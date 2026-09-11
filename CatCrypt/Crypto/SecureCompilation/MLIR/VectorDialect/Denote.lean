/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Ops

/-!
# MLIR `vector` dialect — Denotation

Total semantic interpreter for the abstract `VectorOp α n` alphabet. Every op
denotes to a `Result α n` (vector- or scalar-shaped, cf. `Ops.lean`).

Constructors that need arithmetic typeclasses (`add`, `mul`, `fma`) carry the
instances at the op level, so `denoteVectorOp` is a single pattern-match with
no extra hypotheses. This is the same pattern the existing `VIR/MlirArithDialect`
uses for its dialect-level denotation.

## What `Lowering.lean` proves against this denotation

For two of the ops (`broadcast` and `add`) we prove a denotation-preservation
equation `denoteVectorOp op = lowerSpec op` where `lowerSpec` is the *pointwise
expansion* into the per-lane scalar `α`-operations — exactly the shape a
progressive `vector → x86vector` lowering needs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

open VectorOp

/-- Pure semantic interpreter for an op. -/
@[reducible] def denoteVectorOp {α : Type} {n : Nat} : VectorOp α n → Result α n
  | .broadcast x => .vec (VectorTy.replicate x)
  | .extract v i => .scalar (v i)
  | .insert v i x => .vec (VectorTy.insert v i x)
  | .add op v w => .vec (VectorTy.map₂ op v w)
  | .mul op v w => .vec (VectorTy.map₂ op v w)
  | .fma addOp mulOp a b c => .vec (fun i => addOp (mulOp (a i) (b i)) (c i))
  | .shuffle v π => .vec (VectorTy.shuffle π v)
  | .reduce op init v => .scalar (VectorTy.reduce op init v)
  | .shiftL shf m v => .vec (VectorTy.map₁imm shf m v)
  | .shiftR shf m v => .vec (VectorTy.map₁imm shf m v)
  | .mulHi op v w => .vec (VectorTy.map₂ op v w)
  | .shiftRA shf m v => .vec (VectorTy.map₁imm shf m v)
  | .affineByte aff v => .vec (VectorTy.map₁ aff v)
  | .aesRound rnd s k => .vec (VectorTy.map₂ rnd s k)

/-! ## Convenience accessors

Per-op vector / scalar projections that bake in the constructor's result shape
(`.vec` / `.scalar`). Avoids pattern-matching `.getVec?` / `.getScalar?` at
every call site. -/

/-- The vector that `broadcast x` denotes to: the constant `replicate x`. -/
@[simp] theorem denote_broadcast {α : Type} {n : Nat} (x : α) :
    (denoteVectorOp (.broadcast x : VectorOp α n))
      = .vec (VectorTy.replicate (n := n) x) := rfl

/-- The vector that `add op v w` denotes to: pointwise `op`. -/
@[simp] theorem denote_add {α : Type} {n : Nat}
    (op : α → α → α) (v w : VectorTy α n) :
    (denoteVectorOp (.add op v w : VectorOp α n))
      = .vec (VectorTy.map₂ op v w) := rfl

/-- The vector that `mul op v w` denotes to: pointwise `op`. -/
@[simp] theorem denote_mul {α : Type} {n : Nat}
    (op : α → α → α) (v w : VectorTy α n) :
    (denoteVectorOp (.mul op v w : VectorOp α n))
      = .vec (VectorTy.map₂ op v w) := rfl

/-- The scalar that `extract v i` denotes to: `v i`. -/
@[simp] theorem denote_extract {α : Type} {n : Nat} (v : VectorTy α n) (i : Fin n) :
    (denoteVectorOp (.extract v i : VectorOp α n)) = .scalar (v i) := rfl

/-- The vector that `insert v i x` denotes to. -/
@[simp] theorem denote_insert {α : Type} {n : Nat}
    (v : VectorTy α n) (i : Fin n) (x : α) :
    (denoteVectorOp (.insert v i x : VectorOp α n))
      = .vec (VectorTy.insert v i x) := rfl

/-- The vector that `shiftL shf m v` denotes to: pointwise `shf · m`. -/
@[simp] theorem denote_shiftL {α : Type} {n : Nat}
    (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (denoteVectorOp (.shiftL shf m v : VectorOp α n))
      = .vec (VectorTy.map₁imm shf m v) := rfl

/-- The vector that `shiftR shf m v` denotes to: pointwise `shf · m`. -/
@[simp] theorem denote_shiftR {α : Type} {n : Nat}
    (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (denoteVectorOp (.shiftR shf m v : VectorOp α n))
      = .vec (VectorTy.map₁imm shf m v) := rfl

/-- The vector that `mulHi op v w` denotes to: pointwise high-half product. -/
@[simp] theorem denote_mulHi {α : Type} {n : Nat}
    (op : α → α → α) (v w : VectorTy α n) :
    (denoteVectorOp (.mulHi op v w : VectorOp α n))
      = .vec (VectorTy.map₂ op v w) := rfl

/-- The vector that `shiftRA shf m v` denotes to: pointwise signed `shf · m`. -/
@[simp] theorem denote_shiftRA {α : Type} {n : Nat}
    (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (denoteVectorOp (.shiftRA shf m v : VectorOp α n))
      = .vec (VectorTy.map₁imm shf m v) := rfl

/-- The vector that `affineByte aff v` denotes to: pointwise affine. -/
@[simp] theorem denote_affineByte {α : Type} {n : Nat}
    (aff : α → α) (v : VectorTy α n) :
    (denoteVectorOp (.affineByte aff v : VectorOp α n))
      = .vec (VectorTy.map₁ aff v) := rfl

/-- The vector that `aesRound rnd s k` denotes to: pointwise round step. -/
@[simp] theorem denote_aesRound {α : Type} {n : Nat}
    (rnd : α → α → α) (s k : VectorTy α n) :
    (denoteVectorOp (.aesRound rnd s k : VectorOp α n))
      = .vec (VectorTy.map₂ rnd s k) := rfl

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
