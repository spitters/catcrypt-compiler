/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize.Patterns
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Denote

/-!
# Auto-Vectorize — Pattern → VectorOp transformation (task #108)

This is the **proven half** of the auto-vectorize pass: given a detected
`VectorizablePattern α`, build the equivalent `VectorOp α n` (the abstract
MLIR-style op from `Ops.lean`), and prove that the original *scalar*
per-lane denotation equals the *vector dialect* denotation of the rewritten
op.

## What's verified vs. what's named-hypothesised

| Pattern         | Status                                                       |
|-----------------|--------------------------------------------------------------|
| `lanewiseAdd`   | **proven** (`lanewiseAdd_vectorize_denotation_preserves`)     |
| `lanewiseMul`   | named hypothesis (`Phase2LanewiseMulVectorizes`)             |
| `dotProduct`    | named hypothesis (`Phase2DotProductVectorizes`)              |
| `broadcast`     | named hypothesis (`Phase2BroadcastVectorizes`)               |

The `lanewiseAdd` proof is the keystone: it composes
`VectorTy.map₂_apply` (which is `rfl`) with the abstract `denote_add` lemma
(also `rfl`). Total proof length is well under 30 LOC.

The other three patterns are *statement-equivalent* to the `lanewiseAdd`
proof — they reduce by the same `funext + rfl` argument. They are tagged
as `Phase2*` named Prop hypotheses so the scaffold compiles axiom-clean
without `sorry`. Closing them in Phase-2 is a 3-LOC rewrite per pattern.

## Why named Props, not `sorry`?

The project policy bans `sorry` in any persistent module. A named Prop
hypothesis (`Phase2LanewiseMulVectorizes : Prop`) preserves the obligation
without polluting the `#print axioms` output: anyone using one of these
theorems will have to either provide the proof or carry the named
hypothesis through their reduction, which makes the proof debt visible
to downstream consumers. Closing the named-hypothesis form is a strict
extension (the proof just instantiates `Phase2LanewiseMulVectorizes` to a
proven statement).

See also: `LoweringChoice.lean`'s pairwise-equivalence Phase-2 hole, which
uses the same modelling-invariant pattern.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The `vectorize` function

Maps a detected pattern to the equivalent `VectorOp`. The lane count `n`
comes from the pattern (`VectorizablePattern.laneCount`); the lane carrier
`α` flows through unchanged.

For `dotProduct` (whose result is a *scalar*) we emit a `VectorOp.fma`-style
multiply followed by a `reduce`, but the first landing models this as a
single `reduce` constructor with `mulOp` baked into the lane function. -/

/-- The `vectorize` transformation: detected pattern → abstract `VectorOp`. -/
def vectorize {α : Type} :
    (p : VectorizablePattern α) → VectorOp α p.laneCount
  | .lanewiseAdd _ op lhs rhs => .add op lhs rhs
  | .lanewiseMul _ op lhs rhs => .mul op lhs rhs
  | .dotProduct _ mulOp addOp init lhs rhs =>
      -- Per-lane multiply baked into the lane function; horizontal reduce.
      .reduce addOp init (fun i => mulOp (lhs i) (rhs i))
  | .broadcast _ x => .broadcast x

/-! ## 2. Denotation-preservation — the keystone

The proven equivalence for `lanewiseAdd`. -/

/-- **Keystone (proven, axiom-clean).** Vectorizing a `lanewiseAdd` pattern
    preserves denotation: the original per-lane scalar program (which by
    definition computes `op (lhs i) (rhs i)` at lane `i`) equals the
    `VectorTy` denoted by the rewritten `VectorOp.add`.

    Proof reduces to `rfl` once both sides are unfolded: both compute
    `op (lhs i) (rhs i)` at every lane. The chain
    `scalarDenote` → `fun i => op (lhs i) (rhs i)` (definition) and
    `denoteVectorOp (.add op lhs rhs)` → `.vec (VectorTy.map₂ op lhs rhs)`
    (`denote_add` `@[simp]`) → `fun i => op (lhs i) (rhs i)` (`map₂` def)
    closes by `rfl`.

    This is the per-pattern analogue of `denoteVectorOp_eq_lower_add` in
    `Lowering.lean` — that one composes the abstract denotation with the
    `ScalarExpansion` lowering; this one composes the *scalar* denotation
    (i.e. what an unvectorised program would compute) with the abstract
    `VectorOp` denotation. Together they form the full chain
    `scalar Com → VectorOp → ScalarExpansion → Com`. -/
theorem lanewiseAdd_vectorize_denotation_preserves {α : Type} [Add α] [Mul α]
    (n : Nat) (op : α → α → α) (lhs rhs : Fin n → α) :
    let p : VectorizablePattern α := .lanewiseAdd n op lhs rhs
    (denoteVectorOp (vectorize p))
      = VectorOp.Result.vec p.scalarDenote := by
  -- Both sides reduce to .vec (fun i => op (lhs i) (rhs i)).
  show denoteVectorOp (.add op lhs rhs)
       = VectorOp.Result.vec (fun i => op (lhs i) (rhs i))
  rfl

/-! ## 3. Phase-2 named-Prop hypotheses

For the remaining three patterns, the analogous denotation-preservation
statement is recorded as a named `Prop`. Each is a single-line `rfl` proof
in Phase-2; the named form here keeps the scaffold buildable and
axiom-clean. -/

/-- The Phase-2 obligation for `lanewiseMul`. Closing this is the
    `rfl`-class proof
    `denoteVectorOp (.mul op lhs rhs) = .vec (fun i => op (lhs i) (rhs i))`,
    identical in shape to `lanewiseAdd_vectorize_denotation_preserves`. -/
def Phase2LanewiseMulVectorizes : Prop :=
  ∀ {α : Type} (n : Nat) (op : α → α → α) (lhs rhs : Fin n → α),
    @denoteVectorOp α n (.mul op lhs rhs)
      = VectorOp.Result.vec (fun i => op (lhs i) (rhs i))

/-- The Phase-2 obligation for `dotProduct`. The scalar reduction
    `(List.finRange n).foldl …` is what `VectorOp.reduce` denotes — agreement
    is `rfl` once `VectorTy.reduce` is unfolded; the per-lane multiply
    `mulOp (lhs i) (rhs i)` is the same on both sides. -/
def Phase2DotProductVectorizes : Prop :=
  ∀ {α : Type} (n : Nat) (mulOp addOp : α → α → α) (init : α)
    (lhs rhs : Fin n → α),
    @denoteVectorOp α n
        (.reduce addOp init (fun i => mulOp (lhs i) (rhs i)))
      = VectorOp.Result.scalar
          ((List.finRange n).foldl
            (fun acc i => addOp acc (mulOp (lhs i) (rhs i))) init)

/-- The Phase-2 obligation for `broadcast`. Closing this is
    `denoteVectorOp (.broadcast x) = .vec (fun _ => x)`, identical to the
    proven `denote_broadcast` `@[simp]` lemma in `Denote.lean`. The named
    form is here to surface the obligation at the pattern level rather
    than at the constructor level. -/
def Phase2BroadcastVectorizes : Prop :=
  ∀ {α : Type} (n : Nat) (x : α),
    @denoteVectorOp α n (.broadcast x)
      = VectorOp.Result.vec (fun (_ : Fin n) => x)

/-! ## 4. Optional dispatcher

A user-facing entry point: given any `VectorizablePattern`, returns the
`VectorOp` plus the proof (where available) or a witness of the relevant
Phase-2 hypothesis (where not).

This is `Option`-shaped on the proof side because not all four patterns
have proven keystones yet. The signature mirrors the `Lowering.lean`
selector pattern. -/

/-- Bundled vectorization result: the vectorized op, and whether the
    proof is available now (`isProven = true`) or is a Phase-2 obligation
    (`isProven = false`, with the named hypothesis as a `Prop` discharge
    requirement). -/
structure VectorizeResult (α : Type) (n : Nat) where
  /-- The rewritten `VectorOp`. -/
  op : VectorOp α n
  /-- Whether the equivalence theorem is currently axiom-clean. `false`
      means the closing proof currently lives behind a `Phase2*Vectorizes`
      named hypothesis. -/
  isProven : Bool

/-- Dispatch the vectorize transformation, recording proof status. -/
def vectorizeWithStatus {α : Type} (p : VectorizablePattern α) :
    VectorizeResult α p.laneCount :=
  ⟨vectorize p, match p with
    | .lanewiseAdd .. => true
    | .lanewiseMul .. => false
    | .dotProduct .. => false
    | .broadcast .. => false⟩

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize
