/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types

/-!
# MLIR `vector` dialect — Ops

Abstract operation alphabet for the new MLIR-style VectorDialect (task #183).

The constructors mirror MLIR's `vector` / `arith`-at-vector-type alphabet but
remain **carrier-polymorphic** in the element type `α` and length `n`. This is
the deliberate contrast with `VIR/MlirVectorDialect.lean`, which pins lanes to
`BitVec w`. Keeping `α` abstract here means:

* a single op set serves `BitVec`, `ZMod p`, and future field/ring lanes
  without duplicating ops per element type, and
* the eventual progressive-lowering pipeline
  (`VectorOp → CatCrypt Com → x86vector / arm_neon`) can specialise `α` at
  the *lowering* layer, not the *op* layer — same shape as MLIR's design.

## First-landing op subset

We declare a minimal viable set (cf. the task spec):

| op            | per-lane meaning                                          |
|---------------|-----------------------------------------------------------|
| `broadcast`   | `fun _ => x`                                              |
| `extract`     | `v i`                                                     |
| `insert`      | overwrite lane `i` with `x`                               |
| `add`         | pointwise `· + ·` (needs `Add α`)                         |
| `mul`         | pointwise `· * ·` (needs `Mul α`)                         |
| `fma`         | pointwise `a * b + c` (needs `Mul`, `Add`)                |
| `shuffle`     | `fun i => v (π i)`                                        |
| `reduce`      | left fold over lanes                                      |

`fma`, `shuffle`, `reduce` are declared but only `broadcast`, `extract`,
`insert`, `add`, `mul` are exercised in `Lowering.lean` for the first
landing. The remainder ride along for free; their lowerings are Phase-2.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-- Abstract vector op alphabet. Indexed by the carrier element type `α` and
    the lane count `n`. Constructors carry the runtime arguments they need
    (lane indices, scalar literals, permutations) so that `denoteVectorOp`
    is a pure total function with no environment.

    The constructors are **parametric in `α`**: per-lane arithmetic ops require
    only the relevant `Add` / `Mul` typeclass to denote. -/
inductive VectorOp (α : Type) (n : Nat) : Type where
  /-- `vector.broadcast`: build the constant vector `replicate x`. -/
  | broadcast (x : α) : VectorOp α n
  /-- `vector.extract`: read lane `i`. Result type `α`, *not* a vector. -/
  | extract (v : VectorTy α n) (i : Fin n) : VectorOp α n
  /-- `vector.insertelement`: set lane `i` of `v` to `x`. -/
  | insert (v : VectorTy α n) (i : Fin n) (x : α) : VectorOp α n
  /-- `arith.addi : vector<n × α>` — pointwise `add` (the binary op is
      carried explicitly so the inductive is typeclass-free; downstream
      consumers will instantiate it with `(· + ·)` for an `Add α`-bearing
      element type). -/
  | add (add : α → α → α) (v w : VectorTy α n) : VectorOp α n
  /-- `arith.muli : vector<n × α>` — pointwise `mul` (explicit binary op,
      same rationale as `add`). -/
  | mul (mul : α → α → α) (v w : VectorTy α n) : VectorOp α n
  /-- `vector.fma`: pointwise `mul a b ⟶ add (·) c`. -/
  | fma (add mul : α → α → α) (a b c : VectorTy α n) : VectorOp α n
  /-- `vector.shuffle`: permute lanes by `π`. -/
  | shuffle (v : VectorTy α n) (π : Fin n → Fin n) : VectorOp α n
  /-- `vector.reduction`: left fold with `op` starting from `init`. -/
  | reduce (op : α → α → α) (init : α) (v : VectorTy α n) : VectorOp α n
  /-- `arith.shli : vector<n × α>` — pointwise UNARY shift-left-by-immediate
      `m`. The shift function is carried explicitly (so the inductive stays
      typeclass-free) together with the immediate amount `m`. This is the op
      the ARX / NTT / `ρ`-step consumers need that the binary `add`/`mul` ops
      cannot express (it is a *unary* lane op with an immediate operand, not a
      two-vector op). Downstream consumers instantiate `shf` with
      `(· <<< m)` for a `BitVec`-shaped lane. -/
  | shiftL (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) : VectorOp α n
  /-- `arith.shri : vector<n × α>` — pointwise UNARY shift-right-by-immediate
      `m` (logical). Same rationale as `shiftL`. -/
  | shiftR (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) : VectorOp α n
  /-- `x86vector.vpmulh : vector<n × α>` — pointwise BINARY high-half product
      (`VPMULH`/`VPMULHW`). Same carry-the-op convention as `mul`/`add`: the
      lane op `α → α → α` returns the *high* half of the full-width product,
      which is exactly what Montgomery / Barrett reduction needs (the low
      half is `mul`). Distinct constructor from `mul` so a consumer can tag a
      lane multiply as low- vs high-half. Downstream `BitVec 16` lanes
      instantiate `op` with the truncating `mulHi16`. -/
  | mulHi (op : α → α → α) (v w : VectorTy α n) : VectorOp α n
  /-- `arith.shrsi : vector<n × α>` — pointwise UNARY SIGNED (arithmetic)
      shift-right-by-immediate `m` (`VPSRA`/`VPSRAW`/`VPSRAD`). Same shape as
      `shiftR` but the carried lane op is the *arithmetic* shift (sign-
      extending), distinguished from the logical `shiftR` so the lattice
      reduction (which shifts signed coefficients) tags the right intrinsic.
      Downstream `BitVec` lanes instantiate `shf` with `BitVec.sshiftRight`. -/
  | shiftRA (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) : VectorOp α n
  /-- `gfni.affineqb : vector<n × α>` — pointwise per-lane GF(2) affine
      transform `lane ↦ aff (v lane)`. The lane op `aff : α → α` is the
      affine map `x ↦ (M · x) ⊕ b` (for `VGF2P8AFFINEQB`) or
      `x ↦ (M · inv x) ⊕ b` (for `VGF2P8AFFINEINVQB`), with the GF(2) matrix
      `M` and bias `b` CLOSED OVER in `aff` — the matrix/bias are compile-time
      `imm`/quad operands of the GFNI instruction, not per-lane data, so they
      belong baked into the carried function (same convention as `shiftL`'s
      immediate `m`, here the whole affine is the "immediate"). This keeps the
      inductive homogeneous (no extra type parameter). It is a UNARY lane op,
      distinct from `add`/`mul` (binary) — the data vector is the only vector
      operand. Downstream `BitVec 8` lanes instantiate `aff` with
      `fun x => gfniAffine8 M x`. -/
  | affineByte (aff : α → α) (v : VectorTy α n) : VectorOp α n
  /-- `x86vector.aesenc : vector<n × α>` — pointwise per-lane AES round
      step `lane ↦ rnd (state lane) (key lane)` (`VAESENC` / `VAESENCLAST` /
      `VAESDEC` / `VAESDECLAST`). Same carry-the-function convention as `add`:
      one round function `α → α → α` applied lane-wise to a state vector and a
      round-key vector. Distinct constructor (the round function is neither
      `add`/`mul` arithmetic nor a shift). Downstream `BitVec 128` lanes
      instantiate `rnd` with `state,key ↦ aesRound state key`. -/
  | aesRound (rnd : α → α → α) (state key : VectorTy α n) : VectorOp α n

namespace VectorOp

/-- The result type of an op: vector-valued for the lane-shape-preserving ops,
    scalar-valued for `extract` / `reduce`. We surface this as a sum type so
    `denoteVectorOp` can return the right shape per constructor. -/
inductive Result (α : Type) (n : Nat) where
  | vec (v : VectorTy α n)
  | scalar (x : α)

/-- Project the vector component of a `Result`, returning a default zero
    function if it is a scalar. Used by lowering specs that statically know
    the op returns a vector. -/
@[reducible] def Result.getVec? {α : Type} {n : Nat} : Result α n → Option (VectorTy α n)
  | .vec v => some v
  | .scalar _ => none

/-- Project the scalar component. -/
@[reducible] def Result.getScalar? {α : Type} {n : Nat} : Result α n → Option α
  | .vec _ => none
  | .scalar x => some x

end VectorOp

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
