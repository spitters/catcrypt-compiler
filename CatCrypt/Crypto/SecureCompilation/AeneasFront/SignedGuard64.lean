/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.SignedGuard

/-!
# The overflow guard of the signed checked operations at `i64`

At `i64` the checked `+` and `-` of Aeneas fail exactly when the two's-complement overflow
flag of the `64`-bit wrapping operation is set (`BitVec.saddOverflow`,
`BitVec.ssubOverflow`). For a sum with wrapping value `z` the flag is the conjunction of the
sign bits of `x ^^^ z` and `y ^^^ z`; for a difference, of `x ^^^ y` and `x ^^^ z`. The guard
is its negation, the disjunction of the two unsigned comparisons of those words with the sign
bit `2 ^ 63`. It is read as the calls `wrapping_add#64` (or `wrapping_sub#64`), `BitXor#64`,
`Lt` and `||` of the table (`readWordIWadd`, `readWordBxor`, `readBitCmp`, `readBitDecOr`).

The guard is a disjunction, not one comparison: the reader binds an operand of a top-level
comparison that no variable holds as a literal, which is sound only for closed operands.

## Main results

* `add_guard_iff`, `sub_guard_iff`: the guards are the absence of signed overflow
* `iadd64_guarded`, `isub64_guarded`: the checked operations at `i64` in guarded form
* `reifyRw_iadd64`, `reifyRw_isub64`: the rewrites of the reader
* `readWordBxor`, `readBitDecOr`: the reading of the condition
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-! ## The overflow flags -/

/-- The bounds of `i64` hold of the sum of two values exactly when the signed addition of
    their bit vectors does not overflow. -/
theorem inBounds_add_iff (x y : I64) :
    IScalar.inBounds .I64 (x.val + y.val) ↔ x.bv.saddOverflow y.bv = false := by
  simp only [IScalar.inBounds, IScalar.val, BitVec.saddOverflow, IScalarTy.numBits]
  grind

/-- The bounds of `i64` hold of the difference of two values exactly when the signed
    subtraction of their bit vectors does not overflow. -/
theorem inBounds_sub_iff (x y : I64) :
    IScalar.inBounds .I64 (x.val - y.val) ↔ x.bv.ssubOverflow y.bv = false := by
  simp only [IScalar.inBounds, IScalar.val, BitVec.ssubOverflow, IScalarTy.numBits]
  grind

/-- **The sign-bit guard of the sum**: one of the words `x ^^^ z`, `y ^^^ z` of the wrapping
    sum `z` is below `2 ^ 63` exactly when the signed addition does not overflow. -/
theorem add_guard_iff (x y : I64) :
    (toU x ^^^ toU (IScalar.wrapping_add x y) < sbit64 .I64 ∨
      toU y ^^^ toU (IScalar.wrapping_add x y) < sbit64 .I64) ↔
      x.bv.saddOverflow y.bv = false := by
  rcases x with ⟨a⟩
  rcases y with ⟨b⟩
  simp only [toU, IScalar.wrapping_add, sbit64, UScalar.lt_equiv, BitVec.cast_eq,
    IScalarTy.numBits, Nat.add_one_sub_one, Nat.reducePow]
  simp only [UScalar.val, ↓UScalar.bv_mk_apply, ↓IScalar.bv_mk_apply, UScalar.bv_xor] at *
  revert a b
  simp only [IScalarTy.numBits, ← BitVec.lt_def]
  intro a b
  bv_decide

/-- **The sign-bit guard of the difference**: one of the words `x ^^^ y`, `x ^^^ z` of the
    wrapping difference `z` is below `2 ^ 63` exactly when the signed subtraction does not
    overflow. -/
theorem sub_guard_iff (x y : I64) :
    (toU x ^^^ toU y < sbit64 .I64 ∨
      toU x ^^^ toU (IScalar.wrapping_sub x y) < sbit64 .I64) ↔
      x.bv.ssubOverflow y.bv = false := by
  rcases x with ⟨a⟩
  rcases y with ⟨b⟩
  simp only [toU, IScalar.wrapping_sub, sbit64, UScalar.lt_equiv, BitVec.cast_eq,
    IScalarTy.numBits, Nat.add_one_sub_one, Nat.reducePow]
  simp only [UScalar.val, ↓UScalar.bv_mk_apply, ↓IScalar.bv_mk_apply, UScalar.bv_xor] at *
  revert a b
  simp only [IScalarTy.numBits, ← BitVec.lt_def]
  intro a b
  bv_decide

/-! ## The checked operations in guarded form -/

/-- **The checked signed addition at `i64`**: the assertion of the sign-bit guard, followed by
    the wrapping sum. -/
theorem iadd64_guarded (x y : I64) :
    (x + y : RustM I64) = (do
      massert (toU x ^^^ toU (IScalar.wrapping_add x y) < sbit64 .I64 ∨
        toU y ^^^ toU (IScalar.wrapping_add x y) < sbit64 .I64)
      .ok (IScalar.wrapping_add x y)) :=
  tryMk_eq_massert _ _ (fun h => by
    rw [IScalar.wrapping_add_val_eq]; exact bmod_pow_numBits_eq_of_lt _ _ h.1 h.2) _
    ((add_guard_iff x y).trans (inBounds_add_iff x y).symm)

/-- **The checked signed subtraction at `i64`.** -/
theorem isub64_guarded (x y : I64) :
    (x - y : RustM I64) = (do
      massert (toU x ^^^ toU y < sbit64 .I64 ∨
        toU x ^^^ toU (IScalar.wrapping_sub x y) < sbit64 .I64)
      .ok (IScalar.wrapping_sub x y)) :=
  tryMk_eq_massert _ _ (fun h => by
    rw [IScalar.wrapping_sub_val_eq]; exact bmod_pow_numBits_eq_of_lt _ _ h.1 h.2) _
    ((sub_guard_iff x y).trans (inBounds_sub_iff x y).symm)

/-! ## The rewrites of the reader -/

/-- The checked signed addition at `i64`, read through its guarded form. -/
instance reifyRw_iadd64 (x y : I64) :
    ReifyRw (x + y) (do
      massert (toU x ^^^ toU (IScalar.wrapping_add x y) < sbit64 .I64 ∨
        toU y ^^^ toU (IScalar.wrapping_add x y) < sbit64 .I64)
      .ok (IScalar.wrapping_add x y)) :=
  ⟨iadd64_guarded x y⟩

/-- The checked signed subtraction at `i64`, read through its guarded form. -/
instance reifyRw_isub64 (x y : I64) :
    ReifyRw (x - y) (do
      massert (toU x ^^^ toU y < sbit64 .I64 ∨
        toU x ^^^ toU (IScalar.wrapping_sub x y) < sbit64 .I64)
      .ok (IScalar.wrapping_sub x y)) :=
  ⟨isub64_guarded x y⟩

/-! ## The reading of the condition -/

/-- **The bitwise exclusive or of two words** in a condition: the call `BitXor#w`. -/
instance readWordBxor {Γ Δ₁ Δ₂ : Ctxt nfDialect} {ty : UScalarTy} [h : TableTy ty] [Le64 ty]
    (a b : UScalar ty) {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁}
    {va : Var Δ₁ (.word 64)} [h₁ : ReadWord a V Δ₁ p₁ W₁ va]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {vb : Var Δ₂ (.word 64)}
    [h₂ : ReadWord b W₁ Δ₂ p₂ W₂ vb] :
    ReadWord (a ^^^ b) V (.word 64 :: Δ₂)
      ((p₁.append p₂).append
        (.var (callE2 (opName .bxor ++ uTag ty) (.word 64) (p₂.wk va) vb) .nil))
      (HVector.cons (embW (a ^^^ b)) W₂) .here :=
  readWord_call2 (by simp [wordAt, h.table]) rfl h₁ h₂

/-- **A decided disjunction**: the first disjunct, the second, then the call `Or` of their
    bits. -/
instance readBitDecOr {Γ Δ₁ Δ₂ : Ctxt nfDialect} {P Q : Prop} [i : Decidable P]
    [j : Decidable Q] {k : Decidable (P ∨ Q)} {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁}
    {W₁ : Valuation Δ₁} {v₁ : Var Δ₁ .bit} [h₁ : ReadBit (@decide P i) V Δ₁ p₁ W₁ v₁]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {v₂ : Var Δ₂ .bit}
    [h₂ : ReadBit (@decide Q j) W₁ Δ₂ p₂ W₂ v₂] :
    ReadBit (@decide (P ∨ Q) k) V (.bit :: Δ₂)
      ((p₁.append p₂).append (.var (callB2 BoolOp.or.name (p₂.wk v₁) v₂) .nil))
      (HVector.cons (@decide P i || @decide Q j) W₂) .here := by
  have h := readBitConn (hf := BoolForm.or (@decide P i) (@decide Q j)) (h₁ := h₁) (h₂ := h₂)
  exact ⟨h.reads, h.bit.trans (@bit_of_iff _ _ k (by simp))⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront
