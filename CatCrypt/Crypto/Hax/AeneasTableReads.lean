/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.Hax64Table
public import CatCrypt.Crypto.Hax.HaxRuntimeWordBuiltins
public import HaxAscent.RustSemantics.ToRustMS

/-!
# The compiler's table at the scalar and array calls of the Aeneas reading

The builtin table `hax64WExit` of the compiler returns a value only on 64-bit words and on
array accesses below the length. This module states, for the calls of the `RustM` reading
`appRt` of `HaxAscent.RustSemantics.ToRustMS` that read Aeneas operations, that a value the
reading returns is, encoded, the value of `hax64WExit` on the encoded arguments. The
statements are parametric in the Aeneas width `ty : UScalarTy`; the widths `8`, `16`, `32`,
`64` form `tableTy`, and `usize`, whose width is that of the platform, enters through
`wordAt` for the operations whose value does not depend on the width.

The Aeneas front of the compiler (`AeneasFront/Scalars.lean`, `AeneasFront/Arrays.lean`)
states its squares over these statements, and `CatCrypt.Crypto.Hax.Hax64WReading` builds the
reading `app64` on them.

## Main definitions

* `tableTy`, `widthFree`, `wordAt`, `tableBits`, `narrowOfWord`, `opName`: the widths and
  operations of the tagged word calls the table answers

## Main results

* `hax64Builtins_word64`, `hax64Builtins_wordAt`: the table at the tagged word operations
* `hax64WExit_word_of_builtins`, `hax64WExit_int_of_builtins`: admission of a scalar call
* `hax64WExit_appWord`, `hax64WExit_appNot`, `hax64WExit_appChecked`, `hax64WExit_appNeg`,
  `hax64WExit_appArith`: the scalar calls
* `hax64WExit_appIndex`, `hax64WExit_appUpdate`, `hax64WExit_appLen`,
  `hax64WExit_appArrayLit`, `hax64WExit_appRepeat`: the array calls
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value Builtins hax64Builtins hax64WordOps u64BinOp u64BinOp_natCast)
open CatCrypt.Hax.RustSemantics Aeneas.Std

/-! ## The word operations at width 64 -/

/-- The value of `Hax.hax64Builtins` at a binary word operation tagged `64` on two words
    below `2 ^ 64` is the value of the runtime operation at width `64`; for the shifts,
    when the amount is below `64`. -/
theorem hax64Builtins_word64 {f : String} {o : WordOp} (hf : WordOp.ofName "64" f = some o)
    (n m : Nat) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (hs : o = .shr ∨ o = .shl → m < 64) :
    hax64Builtins f [.int n, .int m] = some (.int (o.rt 64 n m)) := by
  unfold WordOp.ofName at hf
  (repeat' split at hf) <;> cases hf <;> subst f <;> clear * - hn hm hs <;>
    simp only [String.reduceAppend] <;> unfold hax64Builtins
  · rw [_root_.Hax.hax64WordOps_bitAnd, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.bitand_w, Int.toNat_natCast]
    rfl
  · rw [WordOpsSim.hax64WordOps_bitOr64, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.bitor_w, Int.toNat_natCast]
    rfl
  · rw [_root_.Hax.hax64WordOps_bitXor, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.bitxor_w, Int.toNat_natCast]
    rfl
  · rw [_root_.Hax.hax64WordOps_wrapping_add, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.wrapping_add_w, _root_.Hax.mod2w, ← Nat.cast_add,
      Int.toNat_natCast]
    rfl
  · rw [_root_.Hax.hax64WordOps_wrapping_sub, u64BinOp_natCast hn hm]
    have e : ((n : Int) - m + (2 ^ 64 : Int)).toNat = n % 2 ^ 64 + 2 ^ 64 - m % 2 ^ 64 := by
      omega
    simp only [WordOp.rt, _root_.Hax.wrapping_sub_w, _root_.Hax.mod2w]
    rw [e]
    rfl
  · rw [_root_.Hax.hax64WordOps_wrapping_mul, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.wrapping_mul_w, _root_.Hax.mod2w, ← Nat.cast_mul,
      Int.toNat_natCast]
    rfl
  · rw [_root_.Hax.hax64WordOps_shr, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.shr_w, Int.toNat_natCast, ite_eq_left (hs (Or.inl rfl))]
    rfl
  · rw [_root_.Hax.hax64WordOps_shl, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.shl_w, _root_.Hax.mod2w, Int.toNat_natCast,
      ite_eq_left (hs (Or.inr rfl)), Nat.mod_eq_of_lt hn]
    rfl
  · rw [_root_.Hax.hax64WordOps_rotr64, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.rotate_right_w, _root_.Hax.mod2w, _root_.Hax.rotrNat,
      Int.toNat_natCast]
    rfl
  · rw [_root_.Hax.hax64WordOps_rotl64, u64BinOp_natCast hn hm]
    simp only [WordOp.rt, _root_.Hax.rotate_left_w, _root_.Hax.mod2w, _root_.Hax.rotlNat,
      Int.toNat_natCast]
    rfl

/-! ## The word operations at the widths of the table -/

/-- The widths `8`, `16`, `32` and `64`: a word of the reading at one of them is a word of
    the table, and the tagged operations of the table at it are those of the reading. -/
def tableTy : UScalarTy → Bool
  | .U8 | .U16 | .U32 | .U64 => true
  | _ => false

/-- The bitwise operations and the right shift: on operands below `2 ^ w`, their value at
    the width `w` is their value at every greater width. -/
def widthFree : WordOp → Bool
  | .band | .bor | .bxor | .shr => true
  | _ => false

/-- The widths and operations of the tagged word operations `hax64WExit` answers wherever
    the reading returns a value: every operation at a width of `tableTy`, and the
    operations of `widthFree` at `usize`. -/
def wordAt (ty : UScalarTy) (o : WordOp) : Bool :=
  tableTy ty || (match ty with
    | .Usize => widthFree o
    | _ => false)

/-- The width at which the table reads a tag: `64` at `size`, the width of the type at
    every other tag. -/
def tableBits : UScalarTy → Nat
  | .Usize => 64
  | ty => ty.numBits

/-- The operation of the narrow table that a word operation of the reading is. -/
def narrowOfWord : WordOp → NarrowOp
  | .band => .and
  | .bor => .or
  | .bxor => .xor
  | .wadd => .add
  | .wsub => .sub
  | .wmul => .mul
  | .shr => .shr
  | .shl => .shl
  | .rotr => .rotr
  | .rotl => .rotl

/-- A width of `wordAt` is at most `64`. -/
theorem wordAt_numBits_le {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true) :
    ty.numBits ≤ 64 := by
  cases ty
  case Usize => rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  case U128 => simp [wordAt, tableTy] at hw
  all_goals decide

/-- On two words below `2 ^ w`, the narrow operation of a word operation at the width `w`
    is the runtime operation at that width; for the shifts, when the amount is below
    `w`. -/
theorem narrowOfWord_nat (o : WordOp) {w n m : Nat} (hn : n < 2 ^ w) (hm : m < 2 ^ w)
    (hs : o = .shr ∨ o = .shl → m < w) :
    ∃ r : Nat, (narrowOfWord o).nat w n m = some r ∧ (r : Int) = o.rt w n m := by
  cases o <;>
    simp only [narrowOfWord, NarrowOp.nat, WordOp.rt, _root_.Hax.bitand_w,
      _root_.Hax.bitor_w, _root_.Hax.bitxor_w, _root_.Hax.wrapping_add_w,
      _root_.Hax.wrapping_sub_w, _root_.Hax.wrapping_mul_w, _root_.Hax.shr_w,
      _root_.Hax.shl_w, _root_.Hax.rotate_right_w, _root_.Hax.rotate_left_w, _root_.Hax.mod2w,
      _root_.Hax.rotrNat, _root_.Hax.rotlNat, Int.toNat_natCast, ← Nat.cast_add,
      ← Nat.cast_mul]
  case wsub =>
    refine ⟨_, rfl, ?_⟩
    have e : ((n : Int) - m + 2 ^ w).toNat = n % 2 ^ w + 2 ^ w - m % 2 ^ w := by
      have h2 : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by norm_cast
      rw [h2, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm]
      omega
    rw [e]
  case shr =>
    rw [ite_eq_left (hs (Or.inl rfl))]
    exact ⟨_, rfl, rfl⟩
  case shl =>
    rw [ite_eq_left (hs (Or.inr rfl)), Nat.mod_eq_of_lt hn]
    exact ⟨_, rfl, rfl⟩
  all_goals exact ⟨_, rfl, rfl⟩

/-- The value of an operation of `widthFree` on two words below `2 ^ w` is the same at
    every width from `w` on. -/
theorem rt_widthFree {o : WordOp} (ho : widthFree o = true) {w W n m : Nat} (hw : w ≤ W)
    (hn : n < 2 ^ w) (hm : m < 2 ^ w) : o.rt W n m = o.rt w n m := by
  have hn' : n < 2 ^ W := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hw)
  have hm' : m < 2 ^ W := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hw)
  cases o <;> first
    | exact absurd ho (by decide)
    | simp [WordOp.rt, _root_.Hax.bitand_w, _root_.Hax.bitor_w, _root_.Hax.bitxor_w,
        _root_.Hax.shr_w, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn',
        Nat.mod_eq_of_lt hm']

/-- The name of a word operation before its tag. -/
def opName : WordOp → String
  | .band => "BitAnd#"
  | .bor => "BitOr#"
  | .bxor => "BitXor#"
  | .wadd => "wrapping_add#"
  | .wsub => "wrapping_sub#"
  | .wmul => "wrapping_mul#"
  | .shr => "Shr#"
  | .shl => "Shl#"
  | .rotr => "rotate_right#"
  | .rotl => "rotate_left#"

/-- A name `WordOp.ofName` reads at a tag is the name of its operation followed by the
    tag. -/
theorem ofName_opName {tag f : String} {o : WordOp} (hf : WordOp.ofName tag f = some o) :
    f = opName o ++ tag := by
  unfold WordOp.ofName at hf
  (repeat' split at hf) <;> cases hf <;> assumption

/-- A binary word operation name tagged `8`, `16`, `32` or `size` is the name of its
    narrow operation at the width of the table. -/
theorem narrowOpOf_word {ty : UScalarTy}
    (hty : ty = .U8 ∨ ty = .U16 ∨ ty = .U32 ∨ ty = .Usize) {f : String} {o : WordOp}
    (hf : WordOp.ofName (uTag ty) f = some o) :
    narrowOpOf f = some (tableBits ty, narrowOfWord o) := by
  obtain rfl := ofName_opName hf
  rcases hty with rfl | rfl | rfl | rfl <;> cases o <;> rfl

/-- **The table at a tagged word operation.** The value of `Hax.hax64Builtins` at a binary
    word operation of `wordAt` on two words below `2 ^ w`, `w` the width of the tag, is the
    value of the runtime operation at the width `w`; for the shifts, when the amount is
    below `w`. -/
theorem hax64Builtins_wordAt {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true)
    {f : String} (hf : WordOp.ofName (uTag ty) f = some o) (n m : Nat)
    (hn : n < 2 ^ ty.numBits) (hm : m < 2 ^ ty.numBits)
    (hs : o = .shr ∨ o = .shl → m < ty.numBits) :
    hax64Builtins f [.int n, .int m] = some (.int (o.rt ty.numBits n m)) := by
  have hle := wordAt_numBits_le hw
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hle
  cases ty
  case U64 => exact hax64Builtins_word64 hf n m hn hm hs
  case U128 => simp [wordAt, tableTy] at hw
  case Usize =>
    have ho : widthFree o = true := by simpa [wordAt, tableTy] using hw
    obtain ⟨r, hr, hrt⟩ := narrowOfWord_nat o (lt_of_lt_of_le hn h64) (lt_of_lt_of_le hm h64)
      (fun h => lt_of_lt_of_le (hs h) hle)
    rw [← rt_widthFree ho hle hn hm, ← hrt]
    exact WordOpsSim.hax64Builtins_narrowOp f _
      (narrowOpOf_word (Or.inr (Or.inr (Or.inr rfl))) hf) n m r (lt_of_lt_of_le hn h64)
      (lt_of_lt_of_le hm h64) hr
  all_goals
    obtain ⟨r, hr, hrt⟩ := narrowOfWord_nat o hn hm hs
    rw [← hrt]
    exact WordOpsSim.hax64Builtins_narrowOp f _ (narrowOpOf_word (by simp) hf) n m r
      (lt_of_lt_of_le hn h64) (lt_of_lt_of_le hm h64) hr

/-- A tagged binary word operation name is none of the array names. -/
theorem word_ne_array {ty : UScalarTy} {o : WordOp} {f : String}
    (hf : WordOp.ofName (uTag ty) f = some o) :
    f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len" := by
  obtain rfl := ofName_opName hf
  cases ty <;> cases o <;> decide +kernel

/-- The result of a binary word operation, at any tag, is a scalar. -/
theorem word_scalarRes {tag f : String} {o : WordOp} (hf : WordOp.ofName tag f = some o) :
    exitScalarRes f = true := by
  obtain rfl := ofName_opName hf
  have hc : (opName o ++ tag).contains '#' = true := by cases o <;> simp [opName]
  simp [exitScalarRes, exitScalarCall, hc]

/-- A binary word operation name of `wordAt` is a two-operand scalar operation. -/
theorem word_scalarOp {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true) {f : String}
    (hf : WordOp.ofName (uTag ty) f = some o) : hax64ScalarOp f = true := by
  obtain rfl := ofName_opName hf
  cases ty
  case U128 => simp [wordAt, tableTy] at hw
  all_goals
    clear hw
    cases o <;> decide +kernel

/-- The call tower type of a tagged binary word operation name holds a word. -/
theorem word_marshalOk {ty : UScalarTy} {o : WordOp} {f : String}
    (hf : WordOp.ofName (uTag ty) f = some o) :
    exitMarshalOk (towerOfCallName f) = true := by
  obtain rfl := ofName_opName hf
  apply exitMarshalOk_of_arrCtorLen
  cases ty <;> cases o <;> rfl

/-- A binary word operation name of `wordAt` is admitted by `hax64WExit` as a scalar call:
    it is none of the array names, its result is a scalar, it is a two-operand scalar
    operation, and its call tower type holds a word. -/
theorem word_admit {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true) {f : String}
    (hf : WordOp.ofName (uTag ty) f = some o) :
    (f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len") ∧
      exitScalarRes f = true ∧ hax64ScalarOp f = true ∧
      exitMarshalOk (towerOfCallName f) = true := by
  exact ⟨word_ne_array hf, word_scalarRes hf, word_scalarOp hw hf, word_marshalOk hf⟩

/-- A shift of the reading that returns a value has an amount below the width. -/
theorem WordOp.aen_shift_lt {ty : UScalarTy} {o : WordOp} {x y r : UScalar ty}
    (h : o.aen x y = .ok r) (ho : o = .shr ∨ o = .shl) : y.val < ty.numBits := by
  rcases ho with rfl | rfl
  · change UScalar.shiftRight x y.val = _ at h
    unfold UScalar.shiftRight at h
    split at h
    · assumption
    · cases h
  · change UScalar.shiftLeft x y.val = _ at h
    unfold UScalar.shiftLeft at h
    split at h
    · assumption
    · cases h

/-- A name `hax64WExit` admits as a two-operand scalar call returns, on two words below
    `2 ^ 64`, the value of `Hax.hax64Builtins` when that value is a word below `2 ^ 64`. -/
theorem hax64WExit_word_of_builtins {f : String}
    (hadm : (f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len") ∧
      exitScalarRes f = true ∧ hax64ScalarOp f = true ∧
      exitMarshalOk (towerOfCallName f) = true)
    {n m r : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (hr : r < 2 ^ 64)
    (hb : hax64Builtins f [.int n, .int m] = some (.int r)) :
    hax64WExit f [.int (n : Int), .int (m : Int)] = some (.int (r : Int)) := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, hres, hop, hto⟩ := hadm
  rw [hax64WExit_of_ne h1 h2 h3 h4
    (fun hw => by obtain ⟨-, _, h⟩ := hax64Builtins_wideHead hw hb; cases h)
    (ne_select_of_exitScalarRes hres)]
  unfold hax64Exit
  rw [hb]
  simp only [hax64ScalarAdmit, hax64ArgsShape, hop, hres, hto, scalarValNB,
    Value.isControlFlow, List.length_cons, List.length_nil, List.all_cons, List.all_nil,
    Bool.not_false, Bool.true_and, Bool.and_true, ite_true, decide_true,
    beq_self_eq_true, Int.natCast_nonneg]
  rw [ite_eq_left (by simp [h5]; omega)]

/-- **The tagged word operations.** A value the reading of a binary word operation of
    `wordAt` returns is, encoded, the value of `hax64WExit` on the encoded arguments. -/
theorem hax64WExit_appWord {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true)
    {f : String} (hf : WordOp.ofName (uTag ty) f = some o) {a b r : AVal}
    (h : appWord ty o a b = .ok r) :
    hax64WExit f [a.toValue, b.toValue] = some r.toValue := by
  unfold appWord at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  obtain ⟨y, hy, h⟩ := rustM_bind_ok h
  obtain ⟨r', hr', h⟩ := rustM_bind_ok h
  cases h
  have hrt : (r'.val : Int) = o.rt ty.numBits x.val y.val :=
    rcompOk_iff.mp (WordOp.square o x y) r' hr'
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (wordAt_numBits_le hw)
  have hxb : x.val < 2 ^ 64 := lt_of_lt_of_le x.hBounds h64
  have hyb : y.val < 2 ^ 64 := lt_of_lt_of_le y.hBounds h64
  have hrb : r'.val < 2 ^ 64 := lt_of_lt_of_le r'.hBounds h64
  have hb := hax64Builtins_wordAt hw hf x.val y.val x.hBounds y.hBounds
    (fun ho => WordOp.aen_shift_lt hr' ho)
  rw [AVal.asW_ok hx, AVal.asW_ok hy]
  show hax64WExit f [.int (x.val : Int), .int (y.val : Int)] = some (.int (r'.val : Int))
  refine hax64WExit_word_of_builtins (word_admit hw hf) hxb hyb hrb ?_
  rw [hrt]
  exact hb

/-! ## The complement at the widths of the table -/

/-- A complement name `Not#w` at a width of `tableTy` is admitted by `hax64WExit` as a
    scalar call on one integer word: it is none of the array names nor the Boolean `Not`,
    its result is a scalar, it is no two-operand scalar operation, its call tower type
    holds a word, and the narrow table reads it at the width of the type. -/
theorem not_admit {ty : UScalarTy} (hty : tableTy ty = true) {f : String}
    (hf : f = "Not#" ++ uTag ty) :
    (f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len" ∧
        f ≠ "Not") ∧
      exitScalarRes f = true ∧ hax64ScalarOp f = false ∧
      exitMarshalOk (towerOfCallName f) = true ∧ narrowNotOf f = some ty.numBits := by
  subst hf
  cases ty <;> first
    | exact absurd hty (by decide)
    | (simp only [uTag, String.reduceAppend]
       exact ⟨by decide, by simp [exitScalarRes, exitScalarCall], by decide,
         exitMarshalOk_of_arrCtorLen rfl, rfl⟩)

/-- A value `appRt` returns at a complement name `Not#w` is the value of `appNot` at the
    width of the tag on one argument. -/
theorem appRt_notAt {ty : UScalarTy} {f : String}
    (hf : f = "Not#" ++ uTag ty) {vs : List AVal} {r : AVal} (h : appRt f vs = .ok r) :
    ∃ a, vs = [a] ∧ appNot ty a = .ok r := by
  have h1 : tagTyAt? "Not#" f = some ty ∧ wordOpAt? f = none ∧ AOp.ofName f = none ∧
      f ≠ "index" ∧ f ≠ "repeat" ∧ f ≠ "array_update" ∧ f ≠ "array_lit" ∧
      checkedAt? f = none ∧ _root_.Hax.FieldTag.fieldTag? f = none := by
    subst hf
    cases ty <;> decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h1
  have hb : boolRt? f = none := by subst hf; cases ty <;> rfl
  have hc : cmpRt? f = none := by subst hf; cases ty <;> rfl
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp [appRt, h7] at h
  · exact ⟨a, rfl, by simpa only [appRt, h1] using h⟩
  · simp [appRt, h2, h3, h4, h5, h7, h8, h9, appBool2_undef hb hc] at h
  · simp [appRt, h6, h7] at h
  · simp [appRt, h7] at h

/-- A value `appRt` returns at a complement name `Not#w` of a width of `tableTy` is the
    value of `appNot` at that width on one argument. -/
theorem appRt_not {ty : UScalarTy} (_hty : tableTy ty = true) {f : String}
    (hf : f = "Not#" ++ uTag ty) {vs : List AVal} {r : AVal} (h : appRt f vs = .ok r) :
    ∃ a, vs = [a] ∧ appNot ty a = .ok r :=
  appRt_notAt hf h

/-- A name `hax64WExit` admits as a one-operand scalar call that the narrow table reads as
    the complement at a width `w` of at most `64` returns, on a word below `2 ^ w`, its
    complement at the width `w`. -/
theorem hax64WExit_not_of_admit {f : String} {w : Nat} (hw : w ≤ 64)
    (hadm : (f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len" ∧
        f ≠ "Not") ∧
      exitScalarRes f = true ∧ hax64ScalarOp f = false ∧
      exitMarshalOk (towerOfCallName f) = true ∧ narrowNotOf f = some w)
    {n : Nat} (hn : n < 2 ^ w) :
    hax64WExit f [.int (n : Int)] = some (.int (_root_.Hax.bitnot_w w n)) := by
  have h64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hxb : n < 2 ^ 64 := lt_of_lt_of_le hn h64
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hres, hop, hto, hnot⟩ := hadm
  rw [hax64WExit_of_ne h1 h2 h3 h4 (fun hw => by
    obtain ⟨-, _, h⟩ := hax64Builtins_wideHead hw (WordOpsSim.hax64Builtins_narrowNot f hnot n hxb)
    cases h) (ne_select_of_exitScalarRes hres)]
  unfold hax64Exit
  rw [WordOpsSim.hax64Builtins_narrowNot f hnot n hxb]
  have hr : 2 ^ w - 1 - n % 2 ^ w < 2 ^ 64 := by omega
  have hsh : hax64ArgsShape f [Value.int (n : Int)] = true := by
    unfold hax64ArgsShape
    rw [ite_eq_right (by simp [hop]), ite_eq_right h6]
    simp only [hax64IntArgs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    omega
  simp only [_root_.Hax.bitnot_w, Int.toNat_natCast, hax64ScalarAdmit, hres, hto, hsh,
    scalarValNB, Value.isControlFlow, Bool.not_false, Bool.true_and, Bool.and_true,
    decide_true, Int.natCast_nonneg]
  rw [ite_eq_left (by simp [h5]; omega)]

/-- **The complement.** A value the reading of `Not#w` at a width of `tableTy` returns is,
    encoded, the value of `hax64WExit` on the encoded argument. -/
theorem hax64WExit_appNot {ty : UScalarTy} (hty : tableTy ty = true) {f : String}
    (hf : f = "Not#" ++ uTag ty) {a r : AVal} (h : appNot ty a = .ok r) :
    hax64WExit f [a.toValue] = some r.toValue := by
  unfold appNot at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  cases h
  have hv : ((~~~x).val : Int) = _root_.Hax.bitnot_w ty.numBits x.val :=
    rcompOk_iff.mp (bitnot_w_u_square x) _ rfl
  have hle : ty.numBits ≤ 64 := by
    cases ty <;> first
      | exact absurd hty (by decide)
      | decide
  rw [AVal.asW_ok hx]
  show hax64WExit f [.int (x.val : Int)] = some (.int ((~~~x).val : Int))
  rw [hv]
  exact hax64WExit_not_of_admit hle (not_admit hty hf) x.hBounds

/-! ## The checked arithmetic -/

/-- A width of `tableTy` is at most `64`. -/
theorem tableTy_numBits_le {ty : UScalarTy} (hty : tableTy ty = true) : ty.numBits ≤ 64 := by
  cases ty <;> first
    | exact absurd hty (by decide)
    | decide

/-- An untagged checked arithmetic name is admitted by `hax64WExit` as a scalar call: it is
    none of the array names nor the Boolean `Not`, its result is a scalar, and its call tower
    type holds a word. -/
theorem arith_admit {f : String} {o : AOp} (hf : AOp.ofName f = some o) :
    (f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len" ∧
        f ≠ "Not") ∧
      exitScalarRes f = true ∧ exitMarshalOk (towerOfCallName f) = true := by
  unfold AOp.ofName at hf
  (repeat' split at hf) <;> cases hf <;> subst f <;>
    exact ⟨by decide, by simp [exitScalarRes, exitScalarCall, exitScalarCalls],
      exitMarshalOk_of_arrCtorLen rfl⟩

/-- Two words below `2 ^ 64` have the argument shape of an untagged checked arithmetic
    name. -/
theorem arith_argsShape {f : String} {o : AOp} (hf : AOp.ofName f = some o) {n m : Nat}
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) :
    hax64ArgsShape f [.int (n : Int), .int (m : Int)] = true := by
  unfold hax64ArgsShape
  split
  · simp only [scalarValNB, List.length_cons, List.length_nil, List.all_cons, List.all_nil,
      beq_self_eq_true, Bool.and_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [ite_eq_right (arith_admit hf).1.2.2.2.2.2]
    simp only [hax64IntArgs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    omega

/-- A checked division or remainder of the reading that returns a value has a non-zero
    divisor. -/
theorem AOp.aen_div_pos {ty : UScalarTy} {o : AOp} {x y z : UScalar ty}
    (h : o.aen x y = .ok z) (ho : o = .div ∨ o = .rem) : 0 < y.val := by
  have hpos : (y.bv != 0) = true → 0 < y.val := fun hy =>
    Nat.pos_of_ne_zero fun e => by
      have hb : y.bv = 0 := BitVec.eq_of_toNat_eq (by simpa using e)
      simp [hb] at hy
  rcases ho with rfl | rfl
  · simp only [AOp.aen, HDiv.hDiv, UScalar.div] at h
    split at h
    · exact hpos ‹_›
    · cases h
  · simp only [AOp.aen, HMod.hMod, UScalar.rem] at h
    split at h
    · rename_i hy
      exact Nat.pos_of_ne_zero (by simpa using hy)
    · cases h

/-- **The table at an untagged checked arithmetic name.** On two words below `2 ^ 64` whose
    runtime result `r` is below `2 ^ 64`, with a non-zero divisor for `Div` and `Rem`, the
    value of `Hax.hax64Builtins` is `r`. -/
theorem hax64Builtins_arith {f : String} {o : AOp} (hf : AOp.ofName f = some o) (n m r : Nat)
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (hr : r < 2 ^ 64) (hrt : (r : Int) = o.rt n m)
    (hd : o = .div ∨ o = .rem → 0 < m) :
    hax64Builtins f [.int n, .int m] = some (.int r) := by
  unfold AOp.ofName at hf
  (repeat' split at hf) <;> cases hf <;> subst f <;> unfold hax64Builtins <;>
    simp only [AOp.rt, _root_.Hax.add, _root_.Hax.sub, _root_.Hax.mul, _root_.Hax.div,
      _root_.Hax.rem] at hrt
  · have e : r = n + m := by omega
    subst e
    rw [_root_.Hax.hax64WordOps_add, u64BinOp_natCast hn hm, ite_eq_left hr]
    rfl
  · have e : m ≤ n ∧ r = n - m := by omega
    rw [_root_.Hax.hax64WordOps_Sub, u64BinOp_natCast hn hm, ite_eq_left e.1, e.2]
    rfl
  · have e : r = n * m := by exact_mod_cast hrt
    subst e
    rw [_root_.Hax.hax64WordOps_mul]
    simp only [Int.toNat_natCast]
    rw [ite_eq_left ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, by omega⟩]
    rfl
  · have e : r = n / m := by exact_mod_cast hrt
    have hm0 := hd (Or.inl rfl)
    subst e
    rw [_root_.Hax.hax64WordOps_div]
    simp only [Int.toNat_natCast]
    rw [ite_eq_left ⟨by omega, by omega, by omega, by omega⟩]
    rfl
  · have e : r = n % m := by exact_mod_cast hrt
    have hm0 := hd (Or.inr rfl)
    subst e
    rw [_root_.Hax.hax64WordOps_rem]
    simp only [Int.toNat_natCast]
    rw [ite_eq_left ⟨by omega, by omega, by omega, by omega⟩]
    rfl

/-- **The checked arithmetic.** A word of a width of at most `64` bits that the reading of
    `Add`, `Sub`, `Mul`, `Div` or `Rem` returns is, encoded, the value of `hax64WExit` on the
    encoded arguments: the operands are words of that width or literals in its range, and
    the reading returns a value only where the result is in the range of the width. -/
theorem hax64WExit_appArith {f : String} {o : AOp} (hf : AOp.ofName f = some o)
    {ty : UScalarTy} (hty : ty.numBits ≤ 64) {a b : AVal} {z : UScalar ty}
    (h : appArith o a b = .ok (.w ty z)) :
    hax64WExit f [a.toValue, b.toValue] = some (AVal.w ty z).toValue := by
  obtain ⟨ty', x, y, z', ha, hb, hz, hr⟩ := appArith_word h
  cases hr
  have hrt : (z.val : Int) = o.rt x.val y.val := rcompOk_iff.mp (AOp.square o x y) z hz
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hty
  have hxb : x.val < 2 ^ 64 := lt_of_lt_of_le x.hBounds h64
  have hyb : y.val < 2 ^ 64 := lt_of_lt_of_le y.hBounds h64
  have hzb : z.val < 2 ^ 64 := lt_of_lt_of_le z.hBounds h64
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hres, hto⟩ := arith_admit hf
  have hbi := hax64Builtins_arith hf x.val y.val z.val hxb hyb hzb hrt
    (fun ho => AOp.aen_div_pos hz ho)
  have hsh := arith_argsShape hf hxb hyb
  rw [ha, hb]
  show hax64WExit f [.int (x.val : Int), .int (y.val : Int)] = some (.int (z.val : Int))
  rw [hax64WExit_of_ne h1 h2 h3 h4
    (fun hw => by obtain ⟨-, _, h⟩ := hax64Builtins_wideHead hw hbi; cases h)
    (ne_select_of_exitScalarRes hres)]
  unfold hax64Exit
  rw [hbi]
  simp only [hax64ScalarAdmit, hres, hto, hsh, scalarValNB, Value.isControlFlow,
    Bool.not_false, Bool.true_and, Bool.and_true, decide_true, Int.natCast_nonneg]
  rw [ite_eq_left (by simp [h5]; omega)]

/-! ## The array operations -/

/-- **`index`.** A value the reading of `index` returns is, encoded, the value of
    `hax64WExit` on the encoded arguments. -/
theorem hax64WExit_appIndex {a i r : AVal} (h : appIndex a i = .ok r) :
    hax64WExit "index" [a.toValue, i.toValue] = some r.toValue := by
  cases a with
  | arr ty n arr =>
    simp only [appIndex] at h
    obtain ⟨j, hj, h⟩ := rustM_bind_ok h
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    cases h
    unfold Aeneas.Std.Array.index_usize at hx
    rw [Aeneas.Std.Array.getElem?_Usize_eq] at hx
    split at hx
    · cases hx
    · rename_i y hy
      cases hx
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hy
      rw [AVal.asW_ok hj]
      have := arrayOps_hax64WExit.index (arr.val.map fun x => Value.int (x.val : Int)) j.val
        (by simpa using hlt) (by simp [Value.isControlFlow])
      simpa [AVal.toValue, hget] using this
  | _ => simp [appIndex] at h

/-- **`array_update`.** A value the reading of `array_update` returns is, encoded, the
    value of `hax64WExit` on the encoded arguments. -/
theorem hax64WExit_appUpdate {a i v r : AVal} (h : appUpdate a i v = .ok r) :
    hax64WExit "array_update" [a.toValue, i.toValue, v.toValue] = some r.toValue := by
  cases a with
  | arr ty n arr =>
    simp only [appUpdate] at h
    obtain ⟨j, hj, h⟩ := rustM_bind_ok h
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    obtain ⟨arr', harr, h⟩ := rustM_bind_ok h
    cases h
    unfold Aeneas.Std.Array.update at harr
    rw [Aeneas.Std.Array.getElem?_Usize_eq] at harr
    split at harr
    · cases harr
    · rename_i y hy
      cases harr
      have hlt : j.val < arr.val.length := (List.getElem?_eq_some_iff.mp hy).1
      rw [AVal.asW_ok hj, AVal.asW_ok hx]
      have := arrayOps_hax64WExit.update (arr.val.map fun x => Value.int (x.val : Int)) j.val
        (.int (x.val : Int)) (by simpa using hlt)
      simpa [AVal.toValue, List.map_set] using this
  | _ => simp [appUpdate] at h

/-! ## The scalar calls on integer words -/

/-- The width of `usize` is at most `64`. -/
theorem usize_numBits_le : UScalarTy.Usize.numBits ≤ 64 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

/-- The widths of the checked operations `Add#t`, `Sub#t`, `Mul#t` that `hax64WExit` answers
    wherever the reading returns a value: the widths of `tableTy` and `usize`. The table reads
    the tag `size` at `64` bits; a checked value at the `usize` width is a checked value at
    `64` bits (`AOp.checkedRt_mono`). -/
def checkedTy (ty : UScalarTy) : Bool := tableTy ty || ty == .Usize

theorem checkedTy_of_tableTy {ty : UScalarTy} (h : tableTy ty = true) : checkedTy ty = true := by
  simp [checkedTy, h]

/-- A width of `checkedTy` is at most `64`. -/
theorem checkedTy_numBits_le {ty : UScalarTy} (h : checkedTy ty = true) : ty.numBits ≤ 64 := by
  cases ty <;> first
    | exact absurd h (by decide)
    | exact usize_numBits_le
    | decide

/-- **Checked addition, subtraction and multiplication are monotone in the width.** A value of
    the checked operation at the width `w` is its value at every width `W ≥ w`. -/
theorem AOp.checkedRt_mono {w W : Nat} (hw : w ≤ W) {o : AOp}
    (ho : o = .add ∨ o = .sub ∨ o = .mul) {a b : Int} {v : Value}
    (h : o.checkedRt w a b = some v) : o.checkedRt W a b = some v := by
  have hp : (2 : Int) ^ w ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) hw
  rcases ho with rfl | rfl | rfl
  · simp only [AOp.checkedRt, _root_.Hax.uintAddOp] at h ⊢
    split at h
    · rename_i h1
      rw [ite_eq_left ⟨h1.1, h1.2.1, lt_of_lt_of_le h1.2.2 hp⟩]
      exact h
    · cases h
  · simp only [AOp.checkedRt, _root_.Hax.uintSubOp] at h ⊢
    split at h
    · rename_i h1
      rw [ite_eq_left ⟨h1.1, h1.2.1, lt_of_lt_of_le h1.2.2 hp⟩]
      exact h
    · cases h
  · simp only [AOp.checkedRt, _root_.Hax.uintMulOp] at h ⊢
    split at h
    · rename_i h1
      obtain ⟨h1, h2, h3, h4, h5⟩ := h1
      rw [ite_eq_left ⟨h1, lt_of_lt_of_le h2 hp, h3, lt_of_lt_of_le h4 hp, lt_of_lt_of_le h5 hp⟩]
      exact h
    · cases h

/-- A scalar call that is none of the array names nor the Boolean `Not`, whose result is a
    scalar and whose call tower type holds a word, returns under `hax64WExit` the value of
    `Hax.hax64Builtins` on integer words below `2 ^ 64` when that value is a word below
    `2 ^ 64`; for a two-operand scalar operation, on two words. -/
theorem hax64WExit_int_of_builtins {f : String}
    (hne : f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len" ∧
      f ≠ "Not")
    (hres : exitScalarRes f = true) (hto : exitMarshalOk (towerOfCallName f) = true)
    {vals : List Value} (hvals : ∀ v ∈ vals, ∃ n : Nat, v = .int n ∧ n < 2 ^ 64)
    (hlen : hax64ScalarOp f = true → vals.length = 2) {r : Nat} (hr : r < 2 ^ 64)
    (hb : hax64Builtins f vals = some (.int r)) :
    hax64WExit f vals = some (.int r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
  rw [hax64WExit_of_ne h1 h2 h3 h4
    (fun hw => by obtain ⟨-, _, h⟩ := hax64Builtins_wideHead hw hb; cases h)
    (ne_select_of_exitScalarRes hres)]
  refine hax64Exit_of_scalarAdmit hb rfl ?_
  have hall : ∀ v ∈ vals, scalarValNB v = true := fun v hv => by
    obtain ⟨n, rfl, hn⟩ := hvals v hv
    simp [scalarValNB]
    omega
  have hsh : hax64ArgsShape f vals = true := by
    unfold hax64ArgsShape
    split_ifs with hop
    · simp [hlen hop, List.all_eq_true.mpr hall]
    · simp only [hax64IntArgs, List.all_eq_true]
      intro v hv
      obtain ⟨n, rfl, hn⟩ := hvals v hv
      simp
      omega
  simp only [hax64ScalarAdmit, hres, hsh, hto, scalarValNB, Bool.and_true, Bool.true_and]
  simp only [decide_true, Int.natCast_nonneg, Bool.true_and]
  have h5' : (f != "len") = true := bne_iff_ne.mpr h5
  rw [h5', Bool.true_and, decide_eq_true_eq]
  exact_mod_cast hr

/-- A checked width-tagged name `Add#t`, `Sub#t` or `Mul#t` at a width of `checkedTy` is
    admitted by `hax64WExit` as a scalar call: it is none of the array names nor the Boolean
    `Not`, its result is a scalar, and its call tower type holds a word. -/
theorem checked_admit {ty : UScalarTy} {o : AOp} {f : String} (hty : checkedTy ty = true)
    (hf : checkedAt? f = some (ty, o)) :
    (f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len" ∧
        f ≠ "Not") ∧
      exitScalarRes f = true ∧ exitMarshalOk (towerOfCallName f) = true := by
  rcases checkedAt?_spec hf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases ty <;>
    first
    | exact absurd hty (by decide)
    | exact ⟨by decide, by simp [exitScalarRes, exitScalarCall, uTag],
        exitMarshalOk_of_arrCtorLen rfl⟩

/-- The checked operations `Add#t`, `Sub#t`, `Mul#t` at a width of `checkedTy` are, in
    `Hax.hax64Builtins`, the checked operations of `u<w>`, where they return a value: at the
    width of the type, and at `usize` at `64` bits, which the value at the `usize` width is
    (`AOp.checkedRt_mono`). -/
theorem hax64Builtins_checkedRt {ty : UScalarTy} {o : AOp} {f : String}
    (hty : checkedTy ty = true) (hf : checkedAt? f = some (ty, o)) {a b : Int} {v : Value}
    (h : o.checkedRt ty.numBits a b = some v) :
    hax64Builtins f [.int a, .int b] = some v := by
  rcases checkedAt?_spec hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases ty <;>
    first
    | exact absurd hty (by decide)
    | exact (congrArg (· <|> _) h).trans rfl
    | exact (congrArg (· <|> _) (AOp.checkedRt_mono usize_numBits_le (by simp) h)).trans rfl

/-- **The checked operations tagged at the widths of the table and `usize`.** A value the
    reading of `Add#t`, `Sub#t` or `Mul#t` at a width of `checkedTy` returns is, encoded, the
    value of `hax64WExit` on the encoded arguments. -/
theorem hax64WExit_appChecked {ty : UScalarTy} {o : AOp} {f : String}
    (hty : checkedTy ty = true) (hf : checkedAt? f = some (ty, o)) {a b r : AVal}
    (h : appChecked ty o a b = .ok r) :
    hax64WExit f [a.toValue, b.toValue] = some r.toValue := by
  obtain ⟨x, y, hx, hy, hc⟩ := appChecked_ok hf h
  obtain ⟨z, rfl⟩ : ∃ z : UScalar ty, r = .w ty z := by
    unfold appChecked at h
    obtain ⟨_, -, h⟩ := rustM_bind_ok h
    obtain ⟨_, -, h⟩ := rustM_bind_ok h
    obtain ⟨z, -, h⟩ := rustM_bind_ok h
    cases h
    exact ⟨z, rfl⟩
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (checkedTy_numBits_le hty)
  have hb := hax64Builtins_checkedRt hty hf hc
  obtain ⟨hne, hres, hto⟩ := checked_admit hty hf
  rw [hx, hy]
  simp only [AVal.toValue, enc_uscalar] at hb ⊢
  refine hax64WExit_int_of_builtins hne hres hto ?_ (fun _ => rfl)
    (lt_of_lt_of_le z.hBounds h64) hb
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl
  exacts [⟨_, rfl, lt_of_lt_of_le x.hBounds h64⟩, ⟨_, rfl, lt_of_lt_of_le y.hBounds h64⟩]

/-- **`wrapping_neg#64`.** A value the reading of `wrapping_neg#64` returns is, encoded, the
    value of `hax64WExit` on the encoded argument. -/
theorem hax64WExit_appNeg {a r : AVal} (h : appNeg .U64 a = .ok r) :
    hax64WExit "wrapping_neg#64" [a.toValue] = some r.toValue := by
  obtain ⟨x, hx, hr⟩ := appNeg_ok h
  have hxb : x.val < 2 ^ 64 := x.hBounds
  have hval : _root_.Hax.wrapping_neg_w UScalarTy.U64.numBits (enc x) =
      (((2 ^ 64 - x.val % 2 ^ 64) % 2 ^ 64 : Nat) : Int) := by
    simp only [enc_uscalar, _root_.Hax.wrapping_neg_w, _root_.Hax.mod2w]
    rw [show UScalarTy.U64.numBits = 64 from rfl]
    omega
  rw [hx, hr, hval]
  simp only [enc_uscalar]
  refine hax64WExit_int_of_builtins (by decide) (by simp [exitScalarRes, exitScalarCall])
    (exitMarshalOk_of_arrCtorLen rfl) ?_ (fun h => absurd h (by decide +kernel))
    (Nat.mod_lt _ (by decide)) ?_
  · intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    exact ⟨_, hv, hxb⟩
  · show (_root_.Hax.hax64WordOps _ _ <|> _) = _
    rw [_root_.Hax.hax64WordOps_wrappingNeg, _root_.Hax.u64UnOp_natCast hxb]
    rfl

/-- **`len`.** A value the reading of `len` returns is, encoded, the value of `hax64WExit`
    on the encoded argument. -/
theorem hax64WExit_appLen {a r : AVal} (h : appLen a = .ok r) :
    hax64WExit "len" [a.toValue] = some r.toValue := by
  obtain ⟨vs, ha, hr⟩ := appLen_ok h
  rw [ha, hr, hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  exact hax64Exit_of_arrShape (_root_.Hax.hax64Builtins_arrayLen vs) rfl rfl

/-- The arguments of a call of `array_lit` from which the reading returns an array of words
    of at most `64` bits are admitted by `hax64WExit`: fewer than `2 ^ 64` words below
    `2 ^ 64`. -/
theorem hax64LitAdmit_of_appArrayLit {vs : List AVal} {ty : UScalarTy} {n : Usize}
    {arr : Aeneas.Std.Array (UScalar ty) n} (hty : ty.numBits ≤ 64)
    (h : appArrayLit vs = .ok (.arr ty n arr)) : hax64LitAdmit (AVal.toValues vs) = true := by
  have hn64 : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) usize_numBits_le
  unfold appArrayLit at h
  split at h
  · rename_i ty' x as
    obtain ⟨xs, hxs, h⟩ := rustM_bind_ok h
    obtain ⟨n', -, h⟩ := rustM_bind_ok h
    split at h
    · rename_i hlen
      have hty' : ty' = ty := by cases h; rfl
      subst hty'
      have h64 : 2 ^ ty'.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hty
      rw [AVal.asWList_ok _ hxs]
      have hl : xs.length < 2 ^ 64 := by
        rw [hlen]
        exact lt_of_lt_of_le n'.hBounds hn64
      have h1 : (xs.map fun x : UScalar ty' => Value.int (x.val : Int)).all scalarValNB =
          true := by
        rw [List.all_eq_true]
        intro v hv
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
        have hy : y.val < 2 ^ 64 := lt_of_lt_of_le y.hBounds h64
        exact (scalarValNB_iff _).mpr ⟨Int.natCast_nonneg _, by exact_mod_cast hy⟩
      unfold hax64LitAdmit
      rw [h1, Bool.true_or, Bool.true_and, decide_eq_true_iff, List.length_map]
      exact hl
    · cases h
  · cases h

/-- **`array_lit`.** An array of words of at most `64` bits that the reading of
    `array_lit` returns is, encoded, the value of `hax64WExit` on the encoded arguments. -/
theorem hax64WExit_appArrayLit {vs : List AVal} {ty : UScalarTy} {n : Usize}
    {arr : Aeneas.Std.Array (UScalar ty) n} (hty : ty.numBits ≤ 64)
    (h : appArrayLit vs = .ok (.arr ty n arr)) :
    hax64WExit "array_lit" (AVal.toValues vs) = some (AVal.arr ty n arr).toValue := by
  simp only [hax64WExit, ite_true, hax64LitAdmit_of_appArrayLit hty h, ← appArrayLit_ok h]

/-- **`repeat`.** An array of words of at most `64` bits that the reading of `repeat`
    returns is, encoded, the value of `hax64WExit` on the encoded arguments. -/
theorem hax64WExit_appRepeat {v m : AVal} {ty : UScalarTy} {n : Usize}
    {arr : Aeneas.Std.Array (UScalar ty) n} (hty : ty.numBits ≤ 64)
    (h : appRepeat v m = .ok (.arr ty n arr)) :
    hax64WExit "repeat" [v.toValue, m.toValue] = some (AVal.arr ty n arr).toValue := by
  obtain ⟨n0, hm0, hr⟩ := appRepeat_ok h
  cases v with
  | w ty' x =>
    simp only [appRepeat] at h
    obtain ⟨k, hk, h⟩ := rustM_bind_ok h
    have hty' : ty' = ty := by cases h; rfl
    subst hty'
    have hm := AVal.asW_ok hk
    rw [hm0] at hm
    cases hm
    have hxb : x.val < 2 ^ 64 :=
      lt_of_lt_of_le x.hBounds (Nat.pow_le_pow_right (by decide) hty)
    have hkb : k.val < 2 ^ 64 :=
      lt_of_lt_of_le k.hBounds (Nat.pow_le_pow_right (by decide) usize_numBits_le)
    have hadm : hax64RepAdmit [(AVal.w ty' x).toValue, .int (enc k)] = true := by
      have hv : scalarValNB (AVal.w ty' x).toValue = true :=
        (scalarValNB_iff _).mpr ⟨Int.natCast_nonneg _, by exact_mod_cast hxb⟩
      have hs : valueToScalar (.int (enc k)) = some k.val := by
        simp [valueToScalar, enc_uscalar]
      show (scalarValNB (AVal.w ty' x).toValue && match valueToScalar (.int (enc k)) with
        | some k => decide (k < 2 ^ 64)
        | none => false) = true
      rw [hv, Bool.true_and, hs]
      exact decide_eq_true hkb
    rw [hm0, hr, hax64WExit, ite_eq_right (by decide), ite_eq_left rfl, ite_eq_left hadm,
      _root_.Hax.hax64Builtins_of_none (_root_.Hax.hax64WordOps_repeat _),
      show _root_.Hax.widthArrayOps "repeat" [(AVal.w ty' x).toValue, Value.int (enc k)] =
        if 0 ≤ enc k then some (.array (List.replicate (enc k).toNat (AVal.w ty' x).toValue))
        else none from rfl,
      ite_eq_left (by simp [enc_uscalar])]
  | _ => simp [appRepeat] at h


end CatCrypt.Crypto.Hax
