/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Ops

/-!
# Auto-Vectorize — Vectorizable pattern alphabet (task #108)

This is the first file of the *auto-vectorize-by-default* pass scaffolded on
top of the new MLIR-style `VectorDialect` (`Types.lean` / `Ops.lean` /
`Denote.lean` / `Lowering.lean`, #183) and the `LoweringChoice` selector
abstraction (#187).

The pass detects *vectorizable shapes* inside the surface Com IR and rewrites
them to `VectorOp` ops directly. Detection itself is unverified glue
(`Option`-typed in `Detection.lean`); the **vectorization** step — turning a
detected pattern into a `VectorOp` whose denotation matches the original
scalar program — is what carries the proof obligation.

## The starter pattern set

| Pattern         | Meaning                                                            |
|-----------------|--------------------------------------------------------------------|
| `lanewiseAdd`   | `n` independent additions: `result i = lhs i + rhs i`              |
| `lanewiseMul`   | `n` independent multiplications: `result i = lhs i * rhs i`        |
| `dotProduct`    | inner product: `result = ∑ i, lhs i * rhs i`                       |
| `broadcast`     | replicate a scalar to `n` lanes: `result i = x`                    |

These four shapes cover the bulk of straight-line SIMD-able code in the
crypto kernels CatCrypt emits today (`#VPADD_*`, `#VPMUL_*`, MAC chains,
`vbroadcastss`-style splats). More shapes (lane-wise FMA, dot-product over
strided memory, reduction folds) follow in Phase-2.

## Carrier polymorphism

Patterns are polymorphic in the lane carrier `α` (matching `VectorOp α n`'s
own carrier polymorphism). The per-lane arithmetic operators are carried
*explicitly* as `α → α → α` fields, in the same style as the `VectorOp.add`
and `VectorOp.mul` constructors: keeps the inductive typeclass-free, so
pattern-matching in `Vectorize.lean` is a single `cases` on the constructor.

## Where this fits in the pipeline

```
Surface Com IR        ─ Detection.lean ─▶  VectorizablePattern
       │                                              │
       │ scalar denotation                            │ vectorize
       ▼                                              ▼
   Fin n → α                                    VectorOp α n
                                                      │
                                                      │ Lowering.lean (#183)
                                                      ▼
                                              ScalarExpansion
                                                      │
                                                      │ Phase-2 → Com
                                                      ▼
                                                LLVM / x86vector / neon
```

The keystone in `Vectorize.lean` is `lanewiseAdd_vectorize_denotation_preserves`,
which composes `laneMap_eq_scalarMap` (`VIR/LaneMap.lean` from #150) with the
abstract denotation `denote_add` (`Denote.lean` from #183).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize

/-- The alphabet of patterns the auto-vectorize pass currently detects.

    Each constructor carries:
    * the lane count `n`,
    * the per-lane operands (as `Fin n → α` functions — the same lane carrier
      `VectorOp` uses), and
    * for binary patterns, the per-lane operator (`α → α → α`).

    Detection turns a surface Com fragment into one of these constructors;
    `Vectorize.lean` turns this into a `VectorOp α n`. The split keeps the
    *recognition* logic (unverified pattern-match on Com structure) separate
    from the *transformation* logic (the proven equivalence step).

    Carrier-polymorphic in `α`: lanes can be `BitVec w` (the SIMD case), `ZMod p`
    (lattice / field arithmetic case), or any element type whatsoever — the
    keystone equivalence theorem holds at every carrier. -/
inductive VectorizablePattern (α : Type) : Type where
  /-- `n` independent additions: lane `i` computes `op (lhs i) (rhs i)`. -/
  | lanewiseAdd (n : Nat) (op : α → α → α) (lhs rhs : Fin n → α)
      : VectorizablePattern α
  /-- `n` independent multiplications: lane `i` computes `op (lhs i) (rhs i)`. -/
  | lanewiseMul (n : Nat) (op : α → α → α) (lhs rhs : Fin n → α)
      : VectorizablePattern α
  /-- Inner product / sum of pairwise products. `mulOp i` is the per-lane
      multiply (`α → α → α`), `addOp` is the reduction binary op, `init` is
      the reduction starting value. Result is a scalar. -/
  | dotProduct (n : Nat) (mulOp addOp : α → α → α) (init : α)
      (lhs rhs : Fin n → α) : VectorizablePattern α
  /-- Replicate a scalar `x` to `n` lanes. -/
  | broadcast (n : Nat) (x : α) : VectorizablePattern α

namespace VectorizablePattern

/-- The lane count of a detected pattern. Used by the dispatch in
    `Vectorize.lean` to type-index the produced `VectorOp α n`. -/
@[reducible] def laneCount {α : Type} : VectorizablePattern α → Nat
  | .lanewiseAdd n _ _ _ => n
  | .lanewiseMul n _ _ _ => n
  | .dotProduct n _ _ _ _ _ => n
  | .broadcast n _ => n

/-- A short tag for the pattern, mostly for debugging / logging.
    The auto-vectorize pass surface logs these when it fires. -/
@[reducible] def name {α : Type} : VectorizablePattern α → String
  | .lanewiseAdd _ _ _ _ => "lanewiseAdd"
  | .lanewiseMul _ _ _ _ => "lanewiseMul"
  | .dotProduct _ _ _ _ _ _ => "dotProduct"
  | .broadcast _ _ => "broadcast"

/-- The *scalar reference* denotation of a pattern. This is what a fully
    expanded per-lane scalar program would compute.

    For vector-result patterns (`lanewiseAdd`/`lanewiseMul`/`broadcast`) the
    denotation is a `Fin n → α` lane function; for `dotProduct` it is a
    single scalar wrapped in the constant lane function (so the shape is
    uniform). Phase-2 will split this into a sum type that mirrors
    `VectorOp.Result`. For the first landing, the constant-lane wrapper is
    enough because the proven equivalence is for `lanewiseAdd` which is
    vector-shaped. -/
def scalarDenote {α : Type} [Add α] [Mul α] :
    (p : VectorizablePattern α) → (Fin p.laneCount → α)
  | .lanewiseAdd _ op lhs rhs => fun i => op (lhs i) (rhs i)
  | .lanewiseMul _ op lhs rhs => fun i => op (lhs i) (rhs i)
  | .dotProduct n mulOp addOp init lhs rhs =>
      -- Wrap the scalar result in a constant lane function for uniformity.
      let reduceAcc : α :=
        (List.finRange n).foldl
          (fun acc i => addOp acc (mulOp (lhs i) (rhs i))) init
      fun _ => reduceAcc
  | .broadcast _ x => fun _ => x

end VectorizablePattern

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize
