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

The reader binds a closed operand of a comparison that no variable holds as a literal; a
computed operand such as `x ^^^ z` is read through its word reading (`readWordBxor`).

The checked `*` at `i64` is read through the absolute values of the operands as `u64` words:
the absolute value `absW x` is the lesser of the pattern of `x` and the pattern of its wrapping
negation `(x - x) - x`, chosen by the call `select` on the comparison `Lt` of the two. The
checked unsigned product `Mul#64` of the absolute values panics exactly when their product
reaches `2 ^ 64`, where the signed product overflows as well. Below that bound the guard is that
the product `p` is below `2 ^ 63`, or is `2 ^ 63` with operands of different signs, the sign
bit of `x ^^^ y` set (`mul_guard_iff`).

## Main results

* `add_guard_iff`, `sub_guard_iff`, `mul_guard_iff`: the guards are the absence of signed
  overflow
* `iadd64_guarded`, `isub64_guarded`, `imul64_guarded`: the checked operations at `i64` in
  guarded form
* `reifyRw_iadd64`, `reifyRw_isub64`, `reifyRw_imul64`: the rewrites of the reader
* `readWordBxor`, `readBitDecOr`: the reading of the condition
* `reifyE_okCmp`, `reifyE_okSel`: a comparison and a selection of variables as bound values
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

/-! ## The checked multiplication -/

/-- The wrapping negation of an `i64` word, `(x - x) - x`. -/
def neg64 (x : I64) : I64 := IScalar.wrapping_sub (IScalar.wrapping_sub x x) x

/-- The absolute value of an `i64` word as a `u64` word: the lesser of its pattern and the
    pattern of its negation. -/
def absW (x : I64) : U64 :=
  selW (decide (toU x < toU (neg64 x))) (toU x) (toU (neg64 x))

/-- The absolute value as a bit vector. -/
theorem absW_bv (x : I64) : (absW x).bv = x.bv.abs := by
  have hn : (toU (neg64 x)).bv = -x.bv := by
    change (IScalar.wrapping_sub (IScalar.wrapping_sub x x) x).bv = -x.bv
    rw [IScalar.wrapping_sub_bv_eq, IScalar.wrapping_sub_bv_eq, BitVec.sub_self,
      BitVec.zero_sub]
  have hx : (toU x).bv = x.bv := by simp only [toU, BitVec.cast_eq]
  have key : ∀ b : BitVec 64, (if b.toNat < (-b).toNat then b else -b) = b.abs := by
    intro b
    simp only [← BitVec.lt_def]
    bv_decide
  unfold absW selW
  rw [← key]
  by_cases h : toU x < toU (neg64 x)
  · grind
  · grind

/-- The absolute value of an `i64` word has the absolute value of its value. -/
theorem absW_val (x : I64) : (absW x).val = x.val.natAbs := by
  simp only [UScalar.val, IScalar.val, absW_bv]
  rw [BitVec.toNat_abs, BitVec.toInt_eq_toNat_bmod]
  grind [BitVec.toNat_neg, BitVec.msb_eq_decide, Int.bmod_def]

/-- The bounds of `i64` on a product of integers: the product of the absolute values is below
    `2 ^ 63`, or it is `2 ^ 63` and the factors have different signs. -/
theorem natAbs_mul_bounds_iff (a b : Int) :
    (a.natAbs * b.natAbs < 2 ^ 63 ∨
      (a.natAbs * b.natAbs = 2 ^ 63 ∧ decide (a < 0) ≠ decide (b < 0))) ↔
      (-2 ^ 63 ≤ a * b ∧ a * b < 2 ^ 63) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg a <;> obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg b
  · grind
  · have h0 : m * n ≠ 0 → m ≠ 0 ∧ n ≠ 0 :=
      fun h => ⟨fun hm => h (by simp [hm]), fun hn => h (by simp [hn])⟩
    simp only [Int.natAbs_natCast, Int.natAbs_neg, Int.mul_neg, ← Int.natCast_mul, ne_eq,
      decide_eq_decide]
    generalize m * n = K at *
    omega
  · grind
  · grind

/-- The guard of the product: the product `p` of the absolute values is below `2 ^ 63`, or it
    is `2 ^ 63` and the operands have different signs. -/
theorem mul_guard_iff (x y : I64) (p : U64) (hp : p.val = x.val.natAbs * y.val.natAbs) :
    (p < sbit64 .I64 ∨ (p = sbit64 .I64 ∧ sbit64 .I64 ≤ toU x ^^^ toU y)) ↔
      IScalar.inBounds .I64 (x.val * y.val) := by
  have hs : sbit64 .I64 ≤ toU x ^^^ toU y ↔ x.bv.msb ≠ y.bv.msb := by
    rcases x with ⟨a⟩
    rcases y with ⟨b⟩
    simp only [toU, sbit64, UScalar.le_equiv, BitVec.cast_eq, IScalarTy.numBits,
      Nat.add_one_sub_one, Nat.reducePow]
    simp only [UScalar.val, ↓UScalar.bv_mk_apply, ↓IScalar.bv_mk_apply, UScalar.bv_xor] at *
    revert a b
    simp only [IScalarTy.numBits, ← BitVec.le_def]
    intro a b
    bv_decide
  have hlt : p < sbit64 .I64 ↔ p.val < 2 ^ 63 := by
    simp only [UScalar.lt_equiv, sbit64, UScalar.val]
    grind
  have heq : p = sbit64 .I64 ↔ p.val = 2 ^ 63 := by
    exact beq_eq_beq.mp rfl
  have hx : x.bv.msb = decide (x.val < 0) := by
    grind [BitVec.msb_eq_toInt, IScalar.val]
  have hy : y.bv.msb = decide (y.val < 0) := by
    grind [BitVec.msb_eq_toInt, IScalar.val]
  rw [hs, hlt, heq, hx, hy, hp]
  exact natAbs_mul_bounds_iff x.bv.toInt y.bv.toInt

/-- The checked signed multiplication at `i64` through the checked product of the absolute
    values. -/
theorem imul64_eq (x y : I64) :
    (x * y : RustM I64) = (do
      let p ← (absW x * absW y : RustM U64)
      massert (p < sbit64 .I64 ∨ (p = sbit64 .I64 ∧ sbit64 .I64 ≤ toU x ^^^ toU y))
      .ok (IScalar.wrapping_mul x y)) := by
  have hU := UScalar.mul_equiv (absW x) (absW y)
  have hI := IScalar.mul_equiv x y
  have ha := absW_val x
  have hb := absW_val y
  have hn : (x.val * y.val).natAbs = x.val.natAbs * y.val.natAbs := Int.natAbs_mul _ _
  rw [show (absW x * absW y : RustM U64) = UScalar.mul (absW x) (absW y) from rfl]
  rcases hm : UScalar.mul (absW x) (absW y) with z | e | _
  · rw [hm] at hU
    rw [bind_tc_ok]
    exact tryMk_eq_massert _ _ (fun h => by
      rw [IScalar.wrapping_mul_val_eq]; exact bmod_pow_numBits_eq_of_lt _ _ h.1 h.2) _
      (mul_guard_iff x y z (by rw [hU.2.1, ha, hb]))
  · rw [hm] at hU
    obtain ⟨rfl, hgt⟩ := hU
    change IScalar.mul x y = RustM.fail .panic
    rcases hi : IScalar.mul x y with z | e' | _ <;> rw [hi] at hI
    · exfalso
      obtain ⟨h1, h2, -⟩ := hI
      rw [ha, hb, ← hn] at hgt
      simp only [IScalar.min, IScalar.max, UScalar.max, IScalarTy.numBits,
        UScalarTy.numBits] at *
      omega
    · rw [hI.1]
    · exact hI.elim
  · rw [hm] at hU
    exact hU.elim

/-- **The checked signed multiplication at `i64`**: the absolute values of the operands as the
    selection of the lesser of each pattern and its negation, their checked unsigned product,
    which panics at `2 ^ 64` and above, the assertion of the guard, then the wrapping product. -/
theorem imul64_guarded (x y : I64) :
    (x * y : RustM I64) = (do
      let zx ← RustM.ok (IScalar.wrapping_sub x x)
      let nx ← RustM.ok (IScalar.wrapping_sub zx x)
      let cx ← RustM.ok (decide (toU x < toU nx))
      let ax ← RustM.ok (selW cx (toU x) (toU nx))
      let zy ← RustM.ok (IScalar.wrapping_sub y y)
      let ny ← RustM.ok (IScalar.wrapping_sub zy y)
      let cy ← RustM.ok (decide (toU y < toU ny))
      let ay ← RustM.ok (selW cy (toU y) (toU ny))
      let p ← (ax * ay : RustM U64)
      massert (p < sbit64 .I64 ∨ (p = sbit64 .I64 ∧ sbit64 .I64 ≤ toU x ^^^ toU y))
      .ok (IScalar.wrapping_mul x y)) :=
  imul64_eq x y

/-- The checked signed multiplication at `i64`, read through its guarded form. -/
instance reifyRw_imul64 (x y : I64) :
    ReifyRw (x * y) (do
      let zx ← RustM.ok (IScalar.wrapping_sub x x)
      let nx ← RustM.ok (IScalar.wrapping_sub zx x)
      let cx ← RustM.ok (decide (toU x < toU nx))
      let ax ← RustM.ok (selW cx (toU x) (toU nx))
      let zy ← RustM.ok (IScalar.wrapping_sub y y)
      let ny ← RustM.ok (IScalar.wrapping_sub zy y)
      let cy ← RustM.ok (decide (toU y < toU ny))
      let ay ← RustM.ok (selW cy (toU y) (toU ny))
      let p ← (ax * ay : RustM U64)
      massert (p < sbit64 .I64 ∨ (p = sbit64 .I64 ∧ sbit64 .I64 ≤ toU x ^^^ toU y))
      .ok (IScalar.wrapping_mul x y)) :=
  ⟨imul64_guarded x y⟩

/-- **A comparison of two word variables as a value**: the call of the name of the comparison. -/
instance reifyE_okCmp {Γ : Ctxt nfDialect} {P : Prop} {ty : UScalarTy} {c : CmpOp}
    {a b : UScalar ty} [hp : CmpProp P c a b] [Le64 ty] {i : Decidable P} (V : Valuation Γ)
    {va vb : Var Γ (.word 64)} [hx : Lookup V (embW a) va] [hy : Lookup V (embW b) vb] :
    ReifyE (RustM.ok (@decide P i)) V (callE2 c.name .bit va vb) where
  sound z hz := by
    cases hz
    exact aeExpr_callE2 _ _ va vb V a b hx.eq hy.eq (aeCall2_cmp c a b)
      (by rw [@bit_of_iff _ _ i hp.iff]; rfl)

/-- **A selection of two word variables by a bit variable as a value**: the call `select`. -/
instance reifyE_okSel {Γ : Ctxt nfDialect} (k : Bool) (a b : U64) (V : Valuation Γ)
    {vk : Var Γ .bit} {va vb : Var Γ (.word 64)} [hk : Lookup V (AeVal.emb k) vk]
    [hx : Lookup V (embW a) va] [hy : Lookup V (embW b) vb] :
    ReifyE (RustM.ok (selW k a b)) V (selE vk va vb) where
  sound z hz := by
    cases hz
    exact aeExpr_selE vk va vb V k a b hk.eq hx.eq hy.eq

end CatCrypt.Crypto.SecureCompilation.AeneasFront
