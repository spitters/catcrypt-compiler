/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify

/-!
# The signed scalars of Aeneas in `reifyAeneas%`

The Aeneas signed integer `IScalar ity` is a bit vector of the width of `ity`, read as a
two's-complement integer (`IScalar.val = bv.toInt`). The reader `reifyAeneas%` encodes it as
its bit pattern, an unsigned word of the same width (`toU`), zero-extended to `64` bits: the
encoding the table `hax64WExit` admits (arguments in `[0, 2 ^ 64)`, operands of a tag `w`
below `2 ^ w`). Every signed operation is then read as a call the table has for unsigned
words.

* The checked `+`, `-`, `*` and the wrapping `+`, `-`, `*` are the wrapping calls
  `wrapping_add#w`, `wrapping_sub#w`, `wrapping_mul#w`: the bit pattern of a value of the
  checked operation is the wrapping operation of the patterns (`toU_add_of_ok` and its
  siblings). The reading is sound in the direction of the certificate of the entry (a value of
  Aeneas is a value of the program); where Aeneas panics, the program returns the wrapped word.
* The bitwise `&&&`, `|||`, `^^^` are the calls `BitAnd#w`, `BitOr#w`, `BitXor#w`.
* A comparison of two signed words is the unsigned comparison of their patterns offset by the
  sign bit, `sflip x = toU x + 2 ^ (w - 1)` (mod `2 ^ w`): `slt_iff_flip`, `sle_iff_flip`,
  `seq_iff_flip`. In a condition it is read as a prefix binding the sign bit and the two
  offset words, followed by the unsigned comparison (`readWordFlip`, `readBitSCmp`); no new
  operation of the dialect is involved.
* A literal right operand of a signed `+`, `-`, `*` is bound as the literal of its pattern
  (`LitOf` at `toU c`).

The widths are `i8` to `i64` (`ITableTy`): `isize` is excluded, since the wrapping
operations depend on the width and the tag `size` is read at `64` bits.

## Main definitions

* `uOf`, `toU`, `signBit`, `sflip`: the encoding
* the `AeVal` instance of `IScalar ity`: the word `embW (toU x)`
* `ITableTy`: the signed widths of the table
* `SCmpProp`: the notations of the signed comparisons

## Main results

* `toU_add_of_ok`, `toU_sub_of_ok`, `toU_mul_of_ok`, `toU_wrapping_add`, ...: the bit
  pattern of a signed operation
* `iadd_square`, `isub_square`, `slt_square`: the squares against `hax64WExit`
* `slt_iff_flip`, `sle_iff_flip`, `seq_iff_flip`: the signed order through the offset
* `reifyE_iadd`, `reifyE_isub`, `reifyE_imul`, ...: the `ReifyE` instances
* `readWordFlip`, `readBitSCmp`: the reading of a signed comparison
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-! ## The encoding -/

/-- The unsigned type of the width of a signed type. -/
@[reducible] def uOf : IScalarTy → UScalarTy
  | .Isize => .Usize
  | .I8 => .U8
  | .I16 => .U16
  | .I32 => .U32
  | .I64 => .U64
  | .I128 => .U128

/-- The unsigned type of a signed type has its width. -/
theorem numBits_uOf (ity : IScalarTy) : (uOf ity).numBits = ity.numBits := by
  cases ity <;> rfl

/-- The bit pattern of a signed word, as the unsigned word of its width. -/
def toU {ity : IScalarTy} (x : IScalar ity) : UScalar (uOf ity) :=
  ⟨x.bv.cast (numBits_uOf ity).symm⟩

/-- A signed word is the word of its bit pattern. -/
@[reducible] instance (ity : IScalarTy) : AeVal (IScalar ity) :=
  ⟨.word 64, fun x => embW (toU x)⟩

/-- The signed widths of the table: `i8`, `i16`, `i32`, `i64`. -/
class ITableTy (ity : IScalarTy) : Prop where
  /-- The unsigned width of the type is one of `tableTy`. -/
  table : tableTy (uOf ity) = true

instance : ITableTy .I8 := ⟨rfl⟩
instance : ITableTy .I16 := ⟨rfl⟩
instance : ITableTy .I32 := ⟨rfl⟩
instance : ITableTy .I64 := ⟨rfl⟩

instance {ity : IScalarTy} [h : ITableTy ity] : TableTy (uOf ity) := ⟨h.table⟩

instance {ity : IScalarTy} [h : ITableTy ity] : Le64 (uOf ity) :=
  ⟨tableTy_numBits_le h.table⟩

/-- A signed type has at least one bit. -/
theorem numBits_pos (ity : IScalarTy) : 0 < ity.numBits := by
  cases ity <;> simp [IScalarTy.numBits]

/-! ## The arithmetic and bitwise operations -/

/-- The bit pattern of a value of the checked signed addition is the wrapping sum of the
    patterns. -/
theorem toU_add_of_ok {ity : IScalarTy} {x y z : IScalar ity} (h : x + y = RustM.ok z) :
    toU z = UScalar.wrapping_add (toU x) (toU y) := by
  have e := IScalar.add_equiv x y
  rw [h] at e
  obtain ⟨-, -, hz⟩ := e
  cases ity <;> simp [toU, UScalar.wrapping_add, hz]

/-- The bit pattern of a value of the checked signed subtraction is the wrapping difference of
    the patterns. -/
theorem toU_sub_of_ok {ity : IScalarTy} {x y z : IScalar ity} (h : x - y = RustM.ok z) :
    toU z = UScalar.wrapping_sub (toU x) (toU y) := by
  have e := IScalar.sub_equiv x y
  rw [h] at e
  obtain ⟨-, -, hz⟩ := e
  cases ity <;> simp [toU, UScalar.wrapping_sub, hz]

/-- The bit pattern of a value of the checked signed multiplication is the wrapping product of
    the patterns. -/
theorem toU_mul_of_ok {ity : IScalarTy} {x y z : IScalar ity} (h : x * y = RustM.ok z) :
    toU z = UScalar.wrapping_mul (toU x) (toU y) := by
  have e := IScalar.mul_equiv x y
  rw [show x * y = IScalar.mul x y from rfl] at h
  rw [h] at e
  obtain ⟨-, -, -, hz⟩ := e
  cases ity <;> simp [toU, UScalar.wrapping_mul, hz]

/-- The bit pattern of a signed wrapping sum is the unsigned wrapping sum of the patterns. -/
theorem toU_wrapping_add {ity : IScalarTy} (x y : IScalar ity) :
    toU (IScalar.wrapping_add x y) = UScalar.wrapping_add (toU x) (toU y) := by
  cases ity <;> simp [toU, UScalar.wrapping_add, IScalar.wrapping_add]

/-- The bit pattern of a signed wrapping difference. -/
theorem toU_wrapping_sub {ity : IScalarTy} (x y : IScalar ity) :
    toU (IScalar.wrapping_sub x y) = UScalar.wrapping_sub (toU x) (toU y) := by
  cases ity <;> simp [toU, UScalar.wrapping_sub, IScalar.wrapping_sub]

/-- The bit pattern of a signed wrapping product. -/
theorem toU_wrapping_mul {ity : IScalarTy} (x y : IScalar ity) :
    toU (IScalar.wrapping_mul x y) = UScalar.wrapping_mul (toU x) (toU y) := by
  cases ity <;> simp [toU, UScalar.wrapping_mul, IScalar.wrapping_mul]

/-- The bit pattern of a bitwise conjunction. -/
theorem toU_and {ity : IScalarTy} (x y : IScalar ity) : toU (x &&& y) = toU x &&& toU y := by
  cases ity <;> rfl

/-- The bit pattern of a bitwise disjunction. -/
theorem toU_or {ity : IScalarTy} (x y : IScalar ity) : toU (x ||| y) = toU x ||| toU y := by
  cases ity <;> rfl

/-- The bit pattern of a bitwise exclusive or. -/
theorem toU_xor {ity : IScalarTy} (x y : IScalar ity) : toU (x ^^^ y) = toU x ^^^ toU y := by
  cases ity <;> rfl

/-- **The checked signed addition against the table**: a value of `x + y` is, as a bit
    pattern, the value of the call `wrapping_add#w` on the patterns. -/
theorem iadd_square {ity : IScalarTy} [h : ITableTy ity] {x y z : IScalar ity}
    (hz : x + y = RustM.ok z) :
    hax64WExit (opName .wadd ++ uTag (uOf ity)) [wordV (toU x), wordV (toU y)] =
      some (wordV (toU z)) :=
  word_square (by simp [wordAt, h.table]) _ _ _ (by rw [toU_add_of_ok hz]; rfl)

/-- **The checked signed subtraction against the table.** -/
theorem isub_square {ity : IScalarTy} [h : ITableTy ity] {x y z : IScalar ity}
    (hz : x - y = RustM.ok z) :
    hax64WExit (opName .wsub ++ uTag (uOf ity)) [wordV (toU x), wordV (toU y)] =
      some (wordV (toU z)) :=
  word_square (by simp [wordAt, h.table]) _ _ _ (by rw [toU_sub_of_ok hz]; rfl)

/-! ## The reading of the operations -/

/-- A signed operation `m` whose value is, as a bit pattern, the value of the word operation
    `o` on the patterns of `x` and `y` is read as the call of `o` at the unsigned width. -/
theorem reifyE_icall2 {ity : IScalarTy} [ITableTy ity] {Γ : Ctxt nfDialect} (o : WordOp)
    (hw : wordAt (uOf ity) o = true) (m : RustM (IScalar ity)) (x y : IScalar ity)
    (hm : ∀ z, m = .ok z → o.aen (toU x) (toU y) = .ok (toU z)) (V : Valuation Γ)
    (va vb : Var Γ (.word 64)) (hx : va.lookup V = embW (toU x))
    (hy : vb.lookup V = embW (toU y)) :
    ReifyE m V (callE2 (opName o ++ uTag (uOf ity)) (.word 64) va vb) where
  sound z hz := aeExpr_callE2 _ _ va vb V (toU x) (toU y) hx hy
    (by rw [aeCall2_word hw, hm z hz]; rfl) (dec_wordV (toU z))

/-- The checked signed addition, read as the call `wrapping_add#w`. -/
instance reifyE_iadd {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (x + y) V (callE2 (opName .wadd ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .wadd (by simp [wordAt, h.table]) _ x y
    (fun z hz => by rw [toU_add_of_ok hz]; rfl) V va vb hx.eq hy.eq

/-- The checked signed subtraction, read as the call `wrapping_sub#w`. -/
instance reifyE_isub {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (x - y) V (callE2 (opName .wsub ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .wsub (by simp [wordAt, h.table]) _ x y
    (fun z hz => by rw [toU_sub_of_ok hz]; rfl) V va vb hx.eq hy.eq

/-- The checked signed multiplication, read as the call `wrapping_mul#w`. -/
instance reifyE_imul {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (x * y) V (callE2 (opName .wmul ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .wmul (by simp [wordAt, h.table]) _ x y
    (fun z hz => by rw [toU_mul_of_ok hz]; rfl) V va vb hx.eq hy.eq

instance reifyE_iband {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (lift (x &&& y)) V (callE2 (opName .band ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .band (by simp [wordAt, h.table]) _ x y
    (fun _ hz => by cases hz; rw [toU_and]; rfl) V va vb hx.eq hy.eq

instance reifyE_ibor {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (lift (x ||| y)) V (callE2 (opName .bor ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .bor (by simp [wordAt, h.table]) _ x y
    (fun _ hz => by cases hz; rw [toU_or]; rfl) V va vb hx.eq hy.eq

instance reifyE_ibxor {ity : IScalarTy} [h : ITableTy ity] {Γ : Ctxt nfDialect}
    (x y : IScalar ity) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW (toU x)) va] [hy : Lookup V (embW (toU y)) vb] :
    ReifyE (lift (x ^^^ y)) V (callE2 (opName .bxor ++ uTag (uOf ity)) (.word 64) va vb) :=
  reifyE_icall2 .bxor (by simp [wordAt, h.table]) _ x y
    (fun _ hz => by cases hz; rw [toU_xor]; rfl) V va vb hx.eq hy.eq

/-! ## Literals -/

instance {ity : IScalarTy} (x c : IScalar ity) : LitOf (x + c) (uOf ity) (toU c) := ⟨⟩
instance {ity : IScalarTy} (x c : IScalar ity) : LitOf (x - c) (uOf ity) (toU c) := ⟨⟩
instance {ity : IScalarTy} (x c : IScalar ity) : LitOf (x * c) (uOf ity) (toU c) := ⟨⟩

/-! ## Comparisons -/

/-- The sign bit `2 ^ (w - 1)` of the width of `ity`, as an unsigned word. -/
def signBit (ity : IScalarTy) : UScalar (uOf ity) := ⟨BitVec.ofNat _ (2 ^ (ity.numBits - 1))⟩

/-- The bit pattern offset by the sign bit: the unsigned word whose order is the signed order
    of `x`. -/
def sflip {ity : IScalarTy} (x : IScalar ity) : UScalar (uOf ity) :=
  UScalar.wrapping_add (toU x) (signBit ity)

/-- The value of the offset pattern is the signed value plus `2 ^ (w - 1)`. -/
theorem sflip_val {ity : IScalarTy} (x : IScalar ity) :
    ((sflip x).val : Int) = x.val + 2 ^ (ity.numBits - 1) := by
  have hv : (sflip x).val = (x.bv.toNat + 2 ^ (ity.numBits - 1) % 2 ^ ity.numBits) %
      2 ^ ity.numBits := by
    simp only [sflip, signBit, UScalar.val, UScalar.wrapping_add, toU, BitVec.toNat_add,
      BitVec.toNat_cast, BitVec.toNat_ofNat, numBits_uOf]
  have hp : 2 ^ ity.numBits = 2 * 2 ^ (ity.numBits - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    have := numBits_pos ity
    omega
  have ha := x.bv.isLt
  have hc : ((2 : Int) ^ (ity.numBits - 1)) = ((2 ^ (ity.numBits - 1) : Nat) : Int) := by
    push_cast
    rfl
  rw [hv, IScalar.val, BitVec.toInt_eq_toNat_cond, hc]
  clear hv hc
  generalize x.bv.toNat = a at ha ⊢
  generalize 2 ^ ity.numBits = N at hp ha ⊢
  generalize 2 ^ (ity.numBits - 1) = A at hp ha ⊢
  subst hp
  rw [Nat.mod_eq_of_lt (by omega : A < 2 * A)]
  by_cases h : a + A < 2 * A
  · rw [Nat.mod_eq_of_lt h]
    split <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split <;> omega

/-- **The signed order is the unsigned order of the offset patterns.** -/
theorem slt_iff_flip {ity : IScalarTy} (x y : IScalar ity) :
    x.val < y.val ↔ (sflip x).val < (sflip y).val := by
  have hx := sflip_val x
  have hy := sflip_val y
  omega

/-- The non-strict signed order is the unsigned order of the offset patterns. -/
theorem sle_iff_flip {ity : IScalarTy} (x y : IScalar ity) :
    x.val ≤ y.val ↔ (sflip x).val ≤ (sflip y).val := by
  have hx := sflip_val x
  have hy := sflip_val y
  omega

/-- Two signed words are equal exactly when their offset patterns have equal values. -/
theorem seq_iff_flip {ity : IScalarTy} (x y : IScalar ity) :
    x = y ↔ (sflip x).val = (sflip y).val := by
  have hx := sflip_val x
  have hy := sflip_val y
  constructor
  · rintro rfl
    rfl
  · intro h
    have hv : x.val = y.val := by omega
    cases x
    cases y
    simp only [IScalar.val] at hv
    rw [BitVec.toInt_inj] at hv
    rw [hv]

/-- **The signed comparison against the table**: the call `Lt` on the offset patterns is the
    signed order. -/
theorem slt_square {ity : IScalarTy} [h : ITableTy ity] (x y : IScalar ity) :
    hax64WExit (CmpOp.name .lt) [wordV (sflip x), wordV (sflip y)] =
      some (.bool (decide (x < y))) := by
  rw [cmp_square (tableTy_numBits_le h.table)]
  simp only [CmpOp.aen]
  congr 2
  exact decide_eq_decide.mpr (slt_iff_flip x y).symm

/-- The proposition `P` is the comparison `c` of the offset patterns of `x` and `y`: an entry
    for each notation of a signed comparison the backend prints. -/
class SCmpProp (P : Prop) {ity : outParam IScalarTy} (c : outParam CmpOp)
    (x y : outParam (IScalar ity)) : Prop where
  /-- The comparison of the offset patterns is the truth of the proposition. -/
  iff : c.aen (sflip x) (sflip y) = true ↔ P

instance SCmpProp.lt {ity : IScalarTy} (x y : IScalar ity) : SCmpProp (x < y) .lt x y :=
  ⟨decide_eq_true_iff.trans (slt_iff_flip x y).symm⟩

instance SCmpProp.le {ity : IScalarTy} (x y : IScalar ity) : SCmpProp (x ≤ y) .le x y :=
  ⟨decide_eq_true_iff.trans (sle_iff_flip x y).symm⟩

instance SCmpProp.gt {ity : IScalarTy} (x y : IScalar ity) : SCmpProp (x > y) .gt x y :=
  ⟨decide_eq_true_iff.trans (slt_iff_flip y x).symm⟩

instance SCmpProp.ge {ity : IScalarTy} (x y : IScalar ity) : SCmpProp (x ≥ y) .ge x y :=
  ⟨decide_eq_true_iff.trans (sle_iff_flip y x).symm⟩

instance SCmpProp.eq {ity : IScalarTy} (x y : IScalar ity) : SCmpProp (x = y) .eq x y :=
  ⟨decide_eq_true_iff.trans (seq_iff_flip x y).symm⟩

/-- **The negation of a signed comparison** is the comparison of the opposite truth. -/
instance SCmpProp.not {P : Prop} {ity : IScalarTy} {c : CmpOp} {x y : IScalar ity}
    [h : SCmpProp P c x y] : SCmpProp (¬ P) c.neg x y :=
  ⟨by rw [CmpOp.aen_neg, Bool.not_eq_true', ← h.iff, Bool.not_eq_true]⟩

/-- **The offset pattern of a signed word**: the pattern, the literal sign bit, then the call
    `wrapping_add#w` of the two. -/
instance readWordFlip {Γ Δ : Ctxt nfDialect} {ity : IScalarTy} [h : ITableTy ity]
    (x : IScalar ity) {V : Valuation Γ} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ}
    {v : Var Δ (.word 64)} [hx : ReadWord (toU x) V Δ p W v] :
    ReadWord (sflip x) V (.word 64 :: .word 64 :: Δ)
      ((p.append (.var (litE (signBit ity)) .nil)).append
        (.var (callE2 (opName .wadd ++ uTag (uOf ity)) (.word 64) (.there v) .here) .nil))
      (HVector.cons (embW (sflip x)) (HVector.cons (embW (signBit ity)) W)) .here :=
  ⟨preReads_snoc (preReads_snoc hx.reads (aeExpr_litE _ W))
    (aeExpr_callE2 _ _ (.there v) .here (HVector.cons (embW (signBit ity)) W) (toU x)
      (signBit ity) hx.word rfl
      (by rw [aeCall2_word (o := .wadd) (by simp [wordAt, h.table])]; rfl) (dec_wordV _)), rfl⟩

/-- **A signed comparison of two words**, of every width of `ITableTy` and every notation of
    `SCmpProp`: the offset pattern of the first operand, of the second, then the call of the
    name of the unsigned comparison (the square `slt_square`). -/
instance readBitSCmp {Γ Δ₁ Δ₂ : Ctxt nfDialect} {P : Prop} {ity : IScalarTy} {c : CmpOp}
    {x y : IScalar ity} [hp : SCmpProp P c x y] [ITableTy ity] {i : Decidable P}
    {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁}
    {va : Var Δ₁ (.word 64)} [h₁ : ReadWord (sflip x) V Δ₁ p₁ W₁ va]
    {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂} {vb : Var Δ₂ (.word 64)}
    [h₂ : ReadWord (sflip y) W₁ Δ₂ p₂ W₂ vb] :
    ReadBit (@decide P i) V (.bit :: Δ₂)
      ((p₁.append p₂).append (.var (callE2 c.name .bit (p₂.wk va) vb) .nil))
      (HVector.cons (c.aen (sflip x) (sflip y)) W₂) .here :=
  ⟨preReads_snoc (preReads_append _ _ h₁.reads h₂.reads)
    (aeExpr_callE2 _ _ _ _ W₂ (sflip x) (sflip y)
      ((preReads_wk p₂ va h₂.reads).trans h₁.word) h₂.word (aeCall2_cmp c _ _) rfl),
    bit_of_iff hp.iff⟩

/-- `reify_iwrapping I` registers the wrapping operations `core.num.I.wrapping_add`,
    `wrapping_sub`, `wrapping_mul` of the backend output at the signed width `I` as instances
    of `reifyE_icall2`. -/
local macro "reify_iwrapping " ty:ident : command => do
  let t := ty.getId
  let opI (s : String) := Lean.mkIdent (`core.num ++ t ++ Lean.Name.mkSimple s)
  let nm (s : String) := Lean.mkIdent (Lean.Name.mkSimple ("reifyE_i" ++ s ++ "_" ++ t.toString))
  let tyI := Lean.mkIdent (`IScalarTy ++ t)
  `(
  /-- The signed wrapping addition of the backend output. -/
  @[instance] theorem $(nm "wrapping_add"):ident {Γ : Ctxt nfDialect} (x y : IScalar $tyI)
      (V : Valuation Γ) {va vb : Var Γ (.word 64)} [hx : Lookup V (embW (toU x)) va]
      [hy : Lookup V (embW (toU y)) vb] :
      ReifyE (RustM.ok ($(opI "wrapping_add") x y)) V
        (callE2 (opName .wadd ++ uTag (uOf $tyI)) (.word 64) va vb) :=
    reifyE_icall2 .wadd (by decide) _ x y
      (fun _ hz => by cases hz; exact congrArg _ (toU_wrapping_add x y).symm) V va vb
      hx.eq hy.eq
  /-- The signed wrapping subtraction of the backend output. -/
  @[instance] theorem $(nm "wrapping_sub"):ident {Γ : Ctxt nfDialect} (x y : IScalar $tyI)
      (V : Valuation Γ) {va vb : Var Γ (.word 64)} [hx : Lookup V (embW (toU x)) va]
      [hy : Lookup V (embW (toU y)) vb] :
      ReifyE (RustM.ok ($(opI "wrapping_sub") x y)) V
        (callE2 (opName .wsub ++ uTag (uOf $tyI)) (.word 64) va vb) :=
    reifyE_icall2 .wsub (by decide) _ x y
      (fun _ hz => by cases hz; exact congrArg _ (toU_wrapping_sub x y).symm) V va vb
      hx.eq hy.eq
  /-- The signed wrapping multiplication of the backend output. -/
  @[instance] theorem $(nm "wrapping_mul"):ident {Γ : Ctxt nfDialect} (x y : IScalar $tyI)
      (V : Valuation Γ) {va vb : Var Γ (.word 64)} [hx : Lookup V (embW (toU x)) va]
      [hy : Lookup V (embW (toU y)) vb] :
      ReifyE (RustM.ok ($(opI "wrapping_mul") x y)) V
        (callE2 (opName .wmul ++ uTag (uOf $tyI)) (.word 64) va vb) :=
    reifyE_icall2 .wmul (by decide) _ x y
      (fun _ hz => by cases hz; exact congrArg _ (toU_wrapping_mul x y).symm) V va vb
      hx.eq hy.eq)

reify_iwrapping I8
reify_iwrapping I16
reify_iwrapping I32
reify_iwrapping I64

end CatCrypt.Crypto.SecureCompilation.AeneasFront
