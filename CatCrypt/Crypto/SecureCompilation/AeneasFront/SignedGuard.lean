/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Signed
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete

/-!
# The overflow guard of the signed checked operations at `i8`, `i16`, `i32`

At a signed width `w ≤ 32` the checked `+`, `-`, `*` of Aeneas fail exactly when the exact
result leaves `[-2 ^ (w - 1), 2 ^ (w - 1))`. The exact result is the `64`-bit wrapping
operation of the sign extensions of the operands (`IScalar.cast .I64`), since it lies in
`(-2 ^ 63, 2 ^ 63)`. The checked operation is therefore the assertion `massert` of the two `i64`
comparisons of that result with the bounds `lo64`, `hi64`, followed by the `w`-bit wrapping
operation; both panic outside the bounds (`iadd_guarded`, `isub_guarded`, `imul_guarded`).

The guarded form is the rewrite (`ReifyRw`) the reader applies to a checked operation at these
widths at the head of a bind. Its condition is read as a prefix and a bit:

* the sign extension of a pattern `u < 2 ^ w` is `(u ^^^ s) - s` with `s = 2 ^ (w - 1)`, read as
  the literal `s`, the call `BitXor#64` and the call `wrapping_sub#64` (`readWordCast64`);
* a wrapping operation of two signed words is the call of its tagged word operation on their
  patterns (`readWordIWadd`, `readWordIWsub`, `readWordIWmul`);
* the two signed comparisons are `readBitSCmp`, and their conjunction is the call `And` of the
  two bits (`readBitDecAnd`).

The value is the wrapping operation, read as its call (`reifyE_okIWadd` and its siblings) and
complete by determinism of a value. At `i64` the class `IWiden` has no instance, so no rewrite
applies and the reading of `AeneasFront/Signed.lean` stays.

## Main definitions

* `IWiden`: the signed widths of at most `32` bits, with the sign extension as word operations
* `lo64`, `hi64`: the bounds of a signed width as `i64` words

## Main results

* `iadd_guarded`, `isub_guarded`, `imul_guarded`: the checked operations in guarded form
* `reifyRw_iadd`, `reifyRw_isub`, `reifyRw_imul`: the rewrites of the reader
* `readWordCast64`, `readBitDecAnd`: the reading of the condition
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open HaxLean.Aeneas.Std
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-! ## The sign extension as word operations -/

/-- The sign bit `2 ^ (w - 1)` of the width of `ity`, as a `64`-bit word. -/
def sbit64 (ity : IScalarTy) : U64 := ⟨BitVec.ofNat 64 (2 ^ (ity.numBits - 1))⟩

/-- The bit pattern of a signed word, zero-extended to a `64`-bit word. -/
def zext64 {ity : IScalarTy} (x : IScalar ity) : U64 := ⟨BitVec.ofNat 64 (toU x).val⟩

/-- The signed widths of at most `32` bits, at which the `64`-bit operations of the sign
    extensions of two words are exact, with the sign extension as two word operations on the
    zero-extended pattern. -/
class IWiden (ity : IScalarTy) : Prop where
  /-- The width is at most `32` bits. -/
  bits : ity.numBits ≤ 32
  /-- The sign extension is the pattern offset by the sign bit, less the sign bit. -/
  sext : ∀ x : IScalar ity,
    toU (IScalar.cast .I64 x) = UScalar.wrapping_sub (zext64 x ^^^ sbit64 ity) (sbit64 ity)

instance : IWiden .I8 :=
  ⟨by decide, fun x => by
    rcases x with ⟨b⟩
    simp only [uOf, toU, IScalarTy.numBits, UScalarTy.numBits, IScalar.cast,
      ↓IScalar.bv_mk_apply, BitVec.cast_eq, UScalar.wrapping_sub, zext64, UScalar.val,
      ↓UScalar.bv_mk_apply, BitVec.ofNat_toNat, sbit64, Nat.add_one_sub_one, Nat.reducePow,
      UScalar.bv_xor, UScalar.mk.injEq]
    revert b
    simp only [IScalarTy.numBits]
    intro b
    bv_decide⟩

instance : IWiden .I16 :=
  ⟨by decide, fun x => by
    rcases x with ⟨b⟩
    simp only [uOf, toU, IScalarTy.numBits, UScalarTy.numBits, IScalar.cast,
      ↓IScalar.bv_mk_apply, BitVec.cast_eq, UScalar.wrapping_sub, zext64, UScalar.val,
      ↓UScalar.bv_mk_apply, BitVec.ofNat_toNat, sbit64, Nat.add_one_sub_one, Nat.reducePow,
      UScalar.bv_xor, UScalar.mk.injEq]
    revert b
    simp only [IScalarTy.numBits]
    intro b
    bv_decide⟩

instance : IWiden .I32 :=
  ⟨by decide, fun x => by
    rcases x with ⟨b⟩
    simp only [uOf, toU, IScalarTy.numBits, UScalarTy.numBits, IScalar.cast,
      ↓IScalar.bv_mk_apply, BitVec.cast_eq, UScalar.wrapping_sub, zext64, UScalar.val,
      ↓UScalar.bv_mk_apply, BitVec.ofNat_toNat, sbit64, Nat.add_one_sub_one, Nat.reducePow,
      UScalar.bv_xor, UScalar.mk.injEq]
    revert b
    simp only [IScalarTy.numBits]
    intro b
    bv_decide⟩

/-- The zero-extended pattern is the word of the pattern. -/
theorem embW_zext64 {ity : IScalarTy} [ITableTy ity] (x : IScalar ity) :
    embW (zext64 x) = embW (toU x) := by
  grind [embW, zext64, lt64, UScalar.val, BitVec.toNat_ofNat]

/-! ## The bounds -/

/-- The least value `-2 ^ (w - 1)` of the width of `ity`, as an `i64` word. -/
def lo64 (ity : IScalarTy) : I64 := ⟨BitVec.ofInt 64 (-2 ^ (ity.numBits - 1))⟩

/-- The greatest value `2 ^ (w - 1) - 1` of the width of `ity`, as an `i64` word. -/
def hi64 (ity : IScalarTy) : I64 := ⟨BitVec.ofInt 64 (2 ^ (ity.numBits - 1) - 1)⟩

/-- A signed value of a width of `IWiden` is below `2 ^ 31` in absolute value. -/
theorem val_bounds {ity : IScalarTy} [h : IWiden ity] (x : IScalar ity) :
    -2 ^ 31 ≤ x.val ∧ x.val < 2 ^ 31 := by
  have hb := h.bits
  have h1 := BitVec.toInt_lt (x := x.bv)
  have h2 := BitVec.le_toInt (x := x.bv)
  have h3 : (2 : Int) ^ (ity.numBits - 1) ≤ 2 ^ 31 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  simp only [IScalar.val]
  omega

/-- The power `2 ^ (w - 1)` of a width of `IWiden` is positive and at most `2 ^ 31`. -/
theorem pow_bounds (ity : IScalarTy) [h : IWiden ity] :
    (0 : Int) < 2 ^ (ity.numBits - 1) ∧ (2 : Int) ^ (ity.numBits - 1) ≤ 2 ^ 31 :=
  ⟨by positivity, pow_le_pow_right₀ (by norm_num) (by have := h.bits; omega)⟩

/-- The `i64` word of the least value has that value. -/
theorem lo64_val (ity : IScalarTy) [IWiden ity] : (lo64 ity).val = -2 ^ (ity.numBits - 1) := by
  have := pow_bounds ity
  simp only [lo64, IScalar.val]
  grind [Int.bmod_eq_of_le]

/-- The `i64` word of the greatest value has that value. -/
theorem hi64_val (ity : IScalarTy) [IWiden ity] :
    (hi64 ity).val = 2 ^ (ity.numBits - 1) - 1 := by
  have := pow_bounds ity
  simp only [hi64, IScalar.val]
  grind [Int.bmod_eq_of_le]

/-- The sign extension keeps the value. -/
theorem cast64_val {ity : IScalarTy} [h : IWiden ity] (x : IScalar ity) :
    (IScalar.cast .I64 x).val = x.val := by
  have hb := h.bits
  simp only [IScalar.val, IScalar.cast]
  exact BitVec.toInt_signExtend_of_le (by simp only [IScalarTy.numBits] at *; omega)

/-- **The guard.** An `i64` word of value `v` lies between the bounds of `ity` exactly when `v`
    is in the bounds of `ity`. -/
theorem guard_iff {ity : IScalarTy} [IWiden ity] (S : I64) (v : Int) (hS : S.val = v) :
    (lo64 ity ≤ S ∧ S ≤ hi64 ity) ↔ IScalar.inBounds ity v := by
  change (lo64 ity).val ≤ S.val ∧ S.val ≤ (hi64 ity).val ↔ _
  rw [hS, lo64_val, hi64_val]
  simp only [IScalar.inBounds]
  omega

/-- The checked construction of a value `v` is the assertion of a condition `P` equivalent to
    the bounds followed by a word `z` of value `v`: both panic outside the bounds. -/
theorem tryMk_eq_massert {ity : IScalarTy} (v : Int) (z : IScalar ity)
    (hz : IScalar.inBounds ity v → z.val = v) (P : Prop) [Decidable P]
    (hP : P ↔ IScalar.inBounds ity v) :
    IScalar.tryMk ity v = (do massert P; .ok z) := by
  by_cases h : IScalar.inBounds ity v
  · simp only [IScalar.tryMk, IScalar.tryMkOpt, massert, IScalar.check_bounds,
      decide_eq_true h, dite_true, RustM.ofOption, ite_eq_left (hP.mpr h)]
    exact congrArg _ (IScalar.eq_of_val_eq (by rw [hz h]; simp))
  · simp [IScalar.tryMk, IScalar.tryMkOpt, massert, RustM.ofOption, h, hP]

/-! ## The checked operations in guarded form -/

/-- **The checked signed addition at a width of `IWiden`**: the assertion of the bounds of
    the `64`-bit sum of the sign extensions, followed by the wrapping sum. -/
theorem iadd_guarded {ity : IScalarTy} [IWiden ity] (x y : IScalar ity) :
    (x + y : RustM (IScalar ity)) = (do
      massert (lo64 ity ≤ IScalar.wrapping_add (IScalar.cast .I64 x) (IScalar.cast .I64 y) ∧
        IScalar.wrapping_add (IScalar.cast .I64 x) (IScalar.cast .I64 y) ≤ hi64 ity)
      .ok (IScalar.wrapping_add x y)) := by
  have hb := val_bounds x
  have hc := val_bounds y
  have hS : (IScalar.wrapping_add (IScalar.cast .I64 x) (IScalar.cast .I64 y)).val =
      x.val + y.val := by
    rw [IScalar.wrapping_add_val_eq, cast64_val, cast64_val]
    apply bmod_pow_numBits_eq_of_lt <;> simp [IScalarTy.numBits] <;> omega
  exact tryMk_eq_massert _ _ (fun h => by
    rw [IScalar.wrapping_add_val_eq]; exact bmod_pow_numBits_eq_of_lt _ _ h.1 h.2) _
    (guard_iff _ _ hS)

/-- **The checked signed subtraction at a width of `IWiden`.** -/
theorem isub_guarded {ity : IScalarTy} [IWiden ity] (x y : IScalar ity) :
    (x - y : RustM (IScalar ity)) = (do
      massert (lo64 ity ≤ IScalar.wrapping_sub (IScalar.cast .I64 x) (IScalar.cast .I64 y) ∧
        IScalar.wrapping_sub (IScalar.cast .I64 x) (IScalar.cast .I64 y) ≤ hi64 ity)
      .ok (IScalar.wrapping_sub x y)) := by
  have hb := val_bounds x
  have hc := val_bounds y
  have hS : (IScalar.wrapping_sub (IScalar.cast .I64 x) (IScalar.cast .I64 y)).val =
      x.val - y.val := by
    rw [IScalar.wrapping_sub_val_eq, cast64_val, cast64_val]
    apply bmod_pow_numBits_eq_of_lt <;> simp [IScalarTy.numBits] <;> omega
  exact tryMk_eq_massert _ _ (fun h => by
    rw [IScalar.wrapping_sub_val_eq]; exact bmod_pow_numBits_eq_of_lt _ _ h.1 h.2) _
    (guard_iff _ _ hS)

/-- **The checked signed multiplication at a width of `IWiden`.** -/
theorem imul_guarded {ity : IScalarTy} [IWiden ity] (x y : IScalar ity) :
    (x * y : RustM (IScalar ity)) = (do
      massert (lo64 ity ≤ IScalar.wrapping_mul (IScalar.cast .I64 x) (IScalar.cast .I64 y) ∧
        IScalar.wrapping_mul (IScalar.cast .I64 x) (IScalar.cast .I64 y) ≤ hi64 ity)
      .ok (IScalar.wrapping_mul x y)) := by
  have hS : (IScalar.wrapping_mul (IScalar.cast .I64 x) (IScalar.cast .I64 y)).val =
      x.val * y.val := by
    have hb := val_bounds x
    have hc := val_bounds y
    have m1 : x.val * y.val ≤ 2 ^ 62 := by nlinarith
    have m2 : -2 ^ 62 ≤ x.val * y.val := by nlinarith
    rw [IScalar.wrapping_mul_val_eq, cast64_val, cast64_val]
    apply bmod_pow_numBits_eq_of_lt <;> simp only [IScalarTy.numBits] <;> omega
  exact tryMk_eq_massert _ _ (fun h => by
    rw [IScalar.wrapping_mul_val_eq]; exact bmod_pow_numBits_eq_of_lt _ _ h.1 h.2) _
    (guard_iff _ _ hS)

/-! ## The rewrites of the reader -/

/-- The checked signed addition at `i8`-`i32`, read through its guarded form. -/
instance reifyRw_iadd {ity : IScalarTy} [IWiden ity] (x y : IScalar ity) :
    ReifyRw (x + y) (do
      massert (lo64 ity ≤ IScalar.wrapping_add (IScalar.cast .I64 x) (IScalar.cast .I64 y) ∧
        IScalar.wrapping_add (IScalar.cast .I64 x) (IScalar.cast .I64 y) ≤ hi64 ity)
      .ok (IScalar.wrapping_add x y)) :=
  ⟨iadd_guarded x y⟩

/-- The checked signed subtraction at `i8`-`i32`, read through its guarded form. -/
instance reifyRw_isub {ity : IScalarTy} [IWiden ity] (x y : IScalar ity) :
    ReifyRw (x - y) (do
      massert (lo64 ity ≤ IScalar.wrapping_sub (IScalar.cast .I64 x) (IScalar.cast .I64 y) ∧
        IScalar.wrapping_sub (IScalar.cast .I64 x) (IScalar.cast .I64 y) ≤ hi64 ity)
      .ok (IScalar.wrapping_sub x y)) :=
  ⟨isub_guarded x y⟩

/-- The checked signed multiplication at `i8`-`i32`, read through its guarded form. -/
instance reifyRw_imul {ity : IScalarTy} [IWiden ity] (x y : IScalar ity) :
    ReifyRw (x * y) (do
      massert (lo64 ity ≤ IScalar.wrapping_mul (IScalar.cast .I64 x) (IScalar.cast .I64 y) ∧
        IScalar.wrapping_mul (IScalar.cast .I64 x) (IScalar.cast .I64 y) ≤ hi64 ity)
      .ok (IScalar.wrapping_mul x y)) :=
  ⟨imul_guarded x y⟩

/-! ## The reading of the condition -/

/-- **A word operation of two read words**: the first operand, the second, then the call of
    the tagged operation on their variables. -/
theorem readWord_call2 {Γ Δ₁ Δ₂ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty] {o : WordOp}
    (hw : wordAt ty o = true) {a b z : UScalar ty} (hz : o.aen a b = .ok z) {V : Valuation Γ}
    {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁} {va : Var Δ₁ (.word 64)}
    (h₁ : ReadWord a V Δ₁ p₁ W₁ va) {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂}
    {vb : Var Δ₂ (.word 64)} (h₂ : ReadWord b W₁ Δ₂ p₂ W₂ vb) :
    ReadWord z V (.word 64 :: Δ₂)
      ((p₁.append p₂).append (.var (callE2 (opName o ++ uTag ty) (.word 64) (p₂.wk va) vb) .nil))
      (HVector.cons (embW z) W₂) .here :=
  ⟨preReads_snoc (preReads_append _ _ h₁.reads h₂.reads)
    (aeExpr_callE2 _ _ _ _ W₂ a b ((preReads_wk p₂ va h₂.reads).trans h₁.word) h₂.word
      (by rw [aeCall2_word hw, hz]; rfl) (dec_wordV z)), rfl⟩

/-- **The wrapping sum of two signed words** in a condition: the call `wrapping_add#w` of their
    patterns. -/
instance readWordIWadd {Γ Δ₁ Δ₂ : Ctxt nfDialect} {ity : IScalarTy} [h : ITableTy ity]
    (a b : IScalar ity) {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁}
    {va : Var Δ₁ (.word 64)} [h₁ : ReadWord (toU a) V Δ₁ p₁ W₁ va]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {vb : Var Δ₂ (.word 64)}
    [h₂ : ReadWord (toU b) W₁ Δ₂ p₂ W₂ vb] :
    ReadWord (toU (IScalar.wrapping_add a b)) V (.word 64 :: Δ₂)
      ((p₁.append p₂).append
        (.var (callE2 (opName .wadd ++ uTag (uOf ity)) (.word 64) (p₂.wk va) vb) .nil))
      (HVector.cons (embW (toU (IScalar.wrapping_add a b))) W₂) .here :=
  readWord_call2 (by simp [wordAt, h.table]) (by rw [toU_wrapping_add]; rfl) h₁ h₂

/-- **The wrapping difference of two signed words** in a condition. -/
instance readWordIWsub {Γ Δ₁ Δ₂ : Ctxt nfDialect} {ity : IScalarTy} [h : ITableTy ity]
    (a b : IScalar ity) {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁}
    {va : Var Δ₁ (.word 64)} [h₁ : ReadWord (toU a) V Δ₁ p₁ W₁ va]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {vb : Var Δ₂ (.word 64)}
    [h₂ : ReadWord (toU b) W₁ Δ₂ p₂ W₂ vb] :
    ReadWord (toU (IScalar.wrapping_sub a b)) V (.word 64 :: Δ₂)
      ((p₁.append p₂).append
        (.var (callE2 (opName .wsub ++ uTag (uOf ity)) (.word 64) (p₂.wk va) vb) .nil))
      (HVector.cons (embW (toU (IScalar.wrapping_sub a b))) W₂) .here :=
  readWord_call2 (by simp [wordAt, h.table]) (by rw [toU_wrapping_sub]; rfl) h₁ h₂

/-- **The wrapping product of two signed words** in a condition. -/
instance readWordIWmul {Γ Δ₁ Δ₂ : Ctxt nfDialect} {ity : IScalarTy} [h : ITableTy ity]
    (a b : IScalar ity) {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁}
    {va : Var Δ₁ (.word 64)} [h₁ : ReadWord (toU a) V Δ₁ p₁ W₁ va]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {vb : Var Δ₂ (.word 64)}
    [h₂ : ReadWord (toU b) W₁ Δ₂ p₂ W₂ vb] :
    ReadWord (toU (IScalar.wrapping_mul a b)) V (.word 64 :: Δ₂)
      ((p₁.append p₂).append
        (.var (callE2 (opName .wmul ++ uTag (uOf ity)) (.word 64) (p₂.wk va) vb) .nil))
      (HVector.cons (embW (toU (IScalar.wrapping_mul a b))) W₂) .here :=
  readWord_call2 (by simp [wordAt, h.table]) (by rw [toU_wrapping_mul]; rfl) h₁ h₂

/-- **The sign extension to `64` bits** in a condition, at a width of `IWiden`: the pattern,
    the literal sign bit, the call `BitXor#64` of the two, then the call `wrapping_sub#64` of
    that word and the sign bit. -/
instance readWordCast64 {Γ Δ : Ctxt nfDialect} {ity : IScalarTy} [ITableTy ity] [hw : IWiden ity]
    (x : IScalar ity) {V : Valuation Γ} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ}
    {v : Var Δ (.word 64)} [hx : ReadWord (toU x) V Δ p W v] :
    ReadWord (toU (IScalar.cast .I64 x)) V (.word 64 :: .word 64 :: .word 64 :: Δ)
      ((((p.append (.var (litE (sbit64 ity)) .nil)).append
          (.var (callE2 (opName .bxor ++ uTag .U64) (.word 64)
            ((NFPre.var (litE (sbit64 ity)) .nil).wk v) .here) .nil)).append .nil).append
        (.var (callE2 (opName .wsub ++ uTag .U64) (.word 64) (NFPre.nil.wk .here)
          (.there .here)) .nil))
      (HVector.cons (embW (toU (IScalar.cast .I64 x)))
        (HVector.cons (embW (zext64 x ^^^ sbit64 ity)) (vCons (sbit64 ity) W))) .here :=
  have hz : ReadWord (zext64 x) V Δ p W v := ⟨hx.reads, hx.word.trans (embW_zext64 x).symm⟩
  have ht := readWord_call2 (o := .bxor) (a := zext64 x) (b := sbit64 ity)
    (z := zext64 x ^^^ sbit64 ity) (by decide) rfl hz (readWordLit (sbit64 ity) W)
  have hs : ReadWord (sbit64 ity)
      (HVector.cons (embW (zext64 x ^^^ sbit64 ity)) (vCons (sbit64 ity) W))
      (.word 64 :: .word 64 :: Δ) .nil
      (HVector.cons (embW (zext64 x ^^^ sbit64 ity)) (vCons (sbit64 ity) W))
      (.there .here) := ⟨rfl, rfl⟩
  readWord_call2 (o := .wsub) (a := zext64 x ^^^ sbit64 ity) (b := sbit64 ity)
    (z := toU (IScalar.cast .I64 x)) (by decide) (by rw [hw.sext x]; rfl) ht hs

/-- **A decided conjunction**: the first conjunct, the second, then the call `And` of their
    bits. -/
instance readBitDecAnd {Γ Δ₁ Δ₂ : Ctxt nfDialect} {P Q : Prop} [i : Decidable P]
    [j : Decidable Q] {k : Decidable (P ∧ Q)} {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁}
    {W₁ : Valuation Δ₁} {v₁ : Var Δ₁ .bit} [h₁ : ReadBit (@decide P i) V Δ₁ p₁ W₁ v₁]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {v₂ : Var Δ₂ .bit}
    [h₂ : ReadBit (@decide Q j) W₁ Δ₂ p₂ W₂ v₂] :
    ReadBit (@decide (P ∧ Q) k) V (.bit :: Δ₂)
      ((p₁.append p₂).append (.var (callB2 BoolOp.and.name (p₂.wk v₁) v₂) .nil))
      (HVector.cons (@decide P i && @decide Q j) W₂) .here := by
  have h := readBitConn (hf := BoolForm.and (@decide P i) (@decide Q j)) (h₁ := h₁) (h₂ := h₂)
  exact ⟨h.reads, h.bit.trans (@bit_of_iff _ _ k (by simp))⟩

/-! ## The value of the guarded form -/

/-- The signed wrapping sum as a value, read as the call `wrapping_add#w`. -/
instance reifyE_okIWadd {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (RustM.ok (IScalar.wrapping_add x y)) V
      (callE2 (opName .wadd ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .wadd (by simp [wordAt, h.table]) _ x y
    (fun _ hz => by cases hz; exact congrArg _ (toU_wrapping_add x y).symm) V va vb
    hx.eq hy.eq

/-- The signed wrapping difference as a value, read as the call `wrapping_sub#w`. -/
instance reifyE_okIWsub {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (RustM.ok (IScalar.wrapping_sub x y)) V
      (callE2 (opName .wsub ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .wsub (by simp [wordAt, h.table]) _ x y
    (fun _ hz => by cases hz; exact congrArg _ (toU_wrapping_sub x y).symm) V va vb
    hx.eq hy.eq

/-- The signed wrapping product as a value, read as the call `wrapping_mul#w`. -/
instance reifyE_okIWmul {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (RustM.ok (IScalar.wrapping_mul x y)) V
      (callE2 (opName .wmul ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .wmul (by simp [wordAt, h.table]) _ x y
    (fun _ hz => by cases hz; exact congrArg _ (toU_wrapping_mul x y).symm) V va vb
    hx.eq hy.eq

instance {ity : IScalarTy} (x c : IScalar ity) :
    LitOf (RustM.ok (IScalar.wrapping_add x c)) (uOf ity) (toU c) := ⟨⟩
instance {ity : IScalarTy} (x c : IScalar ity) :
    LitOf (RustM.ok (IScalar.wrapping_sub x c)) (uOf ity) (toU c) := ⟨⟩
instance {ity : IScalarTy} (x c : IScalar ity) :
    LitOf (RustM.ok (IScalar.wrapping_mul x c)) (uOf ity) (toU c) := ⟨⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront
