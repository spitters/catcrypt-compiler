/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.AeneasTableReads
public import Transfer.Base.RelatedOn

/-!
# The scalar operations of Aeneas as ParamTransfer squares against `hax64WExit`

The Aeneas front reads the scalar operations of Aeneas output (the vendored model
`HaxLean/Rust/Scalar`, result monad `RustM`) as calls of the compiler's builtin table
`hax64WExit`. This module states, for each operation, the square between the Aeneas
operation and the call, as an instance of the ParamTransfer classes `Related`,
`RelatedBinOp`, `RelatedUnOp` and `RelatedBinOpOn`, along the representation relation that
sends an outcome of `RustM` to an option of a chain value: a value `ok x` to `some` of the
value encoding `x`, a failure and divergence to `none` (`encR`). An unsigned word encodes
as the integer of its value (`wordV`), the encoding `ImpToNF.enc` gives to a word of every
width.

Each square is stated once, for every width `ty : UScalarTy` of the table (`tableTy`: `8`,
`16`, `32`, `64`; the bitwise operations and the right shift also at `usize`, `wordAt`).
A width the table does not answer is no instance; the statements are parametric in it.

The operations that never fail in Aeneas (the bitwise and wrapping operations, the
complement, rotations by a `u32` amount, casts, comparisons, Boolean connectives) give
total squares (`RelatedBinOp`, `RelatedUnOp`, `Related`): the outcome encodings agree on
every pair of outcomes. The operations that fail (checked `+ - *`, the shifts) give guarded
squares (`RelatedBinOpOn`) whose guard is that the Aeneas operation returns a value; there
the table returns the same value.

## Main definitions

* `encR`, `wordV`, `encU`, `encB`: the outcome encodings
* `bindR1`, `bindR2`, `call1`, `call2`: the Kleisli liftings of an Aeneas operation and of a
  call of the table
* `OkR`: an outcome that is a value
* `TableTy`: the widths of the table as a class

## Main results

* `relatedBinOp_of`, `relatedBinOpOn_of`, `relatedUnOp_of`: a pointwise square gives the
  ParamTransfer square
* `word_square`, `not_square`, `checked_square`, `rotl_square`, `rotr_square`,
  `cast_square`, `cmp_square`, `bool_square`, `notBool_square`, `select_square`: the pointwise
  squares
* the instances `bandRelated` ... `boolOrRelated`; `notBoolRelated`, the negation of a
  Boolean; `selectRelated`, the selection of a word by a Boolean
* `wordComposite_related`: a composite of total operations is related to its call tree by
  instance resolution
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std Transfer
open _root_.Hax (Value hax64Builtins hax64WordOps)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax

/-! ## Outcome encodings and Kleisli liftings -/

/-- The chain value of an outcome: `some` of the encoding of a value, `none` for a failure
    and for divergence. -/
def encR {α : Type} (e : α → Value) : RustM α → Option Value
  | .ok x => some (e x)
  | .fail _ => none
  | .div => none

@[simp] theorem encR_ok {α : Type} (e : α → Value) (x : α) : encR e (.ok x) = some (e x) := rfl

@[simp] theorem encR_fail {α : Type} (e : α → Value) (err : Error) :
    encR e (.fail err : RustM α) = none := rfl

@[simp] theorem encR_div {α : Type} (e : α → Value) : encR e (.div : RustM α) = none := rfl

/-- The chain value of an unsigned word: the integer of its value. -/
def wordV {ty : UScalarTy} (x : UScalar ty) : Value := .int (x.val : Int)

/-- The outcome encoding at an unsigned width. -/
abbrev encU (ty : UScalarTy) : RustM (UScalar ty) → Option Value := encR wordV

/-- The outcome encoding of a Boolean. -/
abbrev encB : RustM Bool → Option Value := encR Value.bool

/-- An outcome that is a value. -/
def OkR {α : Type} (r : RustM α) : Prop := ∃ y, r = .ok y

/-- A binary operation of `RustM` lifted to outcomes: both operands are run in order. -/
def bindR2 {α β γ : Type} (op : α → β → RustM γ) (a : RustM α) (b : RustM β) : RustM γ :=
  a >>= fun x => b >>= fun y => op x y

/-- A unary operation of `RustM` lifted to outcomes. -/
def bindR1 {α β : Type} (op : α → RustM β) (a : RustM α) : RustM β := a >>= op

/-- A two-argument call of `hax64WExit` lifted to optional values. -/
def call2 (f : String) (a b : Option Value) : Option Value :=
  a.bind fun x => b.bind fun y => hax64WExit f [x, y]

/-- A one-argument call of `hax64WExit` lifted to optional values. -/
def call1 (f : String) (a : Option Value) : Option Value :=
  a.bind fun x => hax64WExit f [x]

theorem bindR2_ok {α β γ : Type} (op : α → β → RustM γ) (x : α) (y : β) :
    bindR2 op (.ok x) (.ok y) = op x y := rfl

theorem encR_bindR2 {α β γ : Type} (e : γ → Value) (op : α → β → RustM γ) (a : RustM α)
    (b : RustM β) :
    encR e (bindR2 op a b) =
      (match a, b with
        | .ok x, .ok y => encR e (op x y)
        | _, _ => none) := by
  cases a <;> cases b <;> rfl

theorem encR_bindR1 {α β : Type} (e : β → Value) (op : α → RustM β) (a : RustM α) :
    encR e (bindR1 op a) = (match a with | .ok x => encR e (op x) | _ => none) := by
  cases a <;> rfl

/-! ## From pointwise squares to ParamTransfer squares -/

/-- **Guarded binary square.** If the table returns the encoding of every value of the
    Aeneas operation `op`, the lifted call realizes the lifted operation on every pair of
    outcomes on which the operation returns a value. -/
theorem relatedBinOpOn_of {α : Type} {e : α → Value} {op : α → α → RustM α} {f : String}
    (h : ∀ x y z, op x y = .ok z → hax64WExit f [e x, e y] = some (e z)) :
    RelatedBinOpOn (encR e) (fun a b => OkR (bindR2 op a b)) (bindR2 op) (call2 f) where
  comm a b hab := by
    obtain ⟨z, hz⟩ := hab
    cases a with
    | ok x =>
      cases b with
      | ok y =>
        rw [bindR2_ok] at hz
        rw [bindR2_ok, hz, encR_ok]
        exact (h x y z hz).symm
      | fail _ => cases hz
      | div => cases hz
    | fail _ => cases hz
    | div => cases hz

/-- **Total binary square.** If the Aeneas operation `op` returns a value on every pair and
    the table returns its encoding, the lifted call realizes the lifted operation. -/
theorem relatedBinOp_of {α β : Type} {e : α → Value} {e' : β → Value}
    {op : α → α → RustM β} {f : String} (hok : ∀ x y, OkR (op x y))
    (h : ∀ x y z, op x y = .ok z → hax64WExit f [e x, e y] = some (e' z)) :
    ∀ a b, encR e' (bindR2 op a b) = call2 f (encR e a) (encR e b) := by
  intro a b
  cases a with
  | ok x =>
    cases b with
    | ok y =>
      obtain ⟨z, hz⟩ := hok x y
      rw [bindR2_ok, hz, encR_ok, encR_ok, encR_ok]
      exact (h x y z hz).symm
    | fail _ => rfl
    | div => rfl
  | fail _ => rfl
  | div => rfl

/-- **Total unary square.** -/
theorem relatedUnOp_of {α β : Type} {e : α → Value} {e' : β → Value}
    {op : α → RustM β} {f : String} (hok : ∀ x, OkR (op x))
    (h : ∀ x z, op x = .ok z → hax64WExit f [e x] = some (e' z)) :
    ∀ a, encR e' (bindR1 op a) = call1 f (encR e a) := by
  intro a
  cases a with
  | ok x =>
    obtain ⟨z, hz⟩ := hok x
    show encR e' (op x) = _
    rw [hz, encR_ok, encR_ok]
    exact (h x z hz).symm
  | fail _ => rfl
  | div => rfl

/-- **Total unary square into a function of optional values.** -/
theorem relatedR1_of {α β : Type} {e : α → Value} {e' : β → Value}
    {op : α → RustM β} {g : Value → Option Value} (hok : ∀ x, OkR (op x))
    (h : ∀ x z, op x = .ok z → g (e x) = some (e' z)) :
    ∀ a, encR e' (bindR1 op a) = (encR e a).bind g := by
  intro a
  cases a with
  | ok x =>
    obtain ⟨z, hz⟩ := hok x
    show encR e' (op x) = _
    rw [hz, encR_ok, encR_ok, Option.bind_some]
    exact (h x z hz).symm
  | fail _ => rfl
  | div => rfl

/-! ## The widths of the table -/

/-- The widths `8`, `16`, `32`, `64` of the table, as a class for instance resolution. -/
class TableTy (ty : UScalarTy) : Prop where
  /-- The width is one of `tableTy`. -/
  table : tableTy ty = true

instance : TableTy .U8 := ⟨rfl⟩
instance : TableTy .U16 := ⟨rfl⟩
instance : TableTy .U32 := ⟨rfl⟩
instance : TableTy .U64 := ⟨rfl⟩

/-- A width of the table is at most `64` bits. -/
theorem TableTy.le64 (ty : UScalarTy) [h : TableTy ty] : ty.numBits ≤ 64 :=
  tableTy_numBits_le h.table

/-- The word of an Aeneas word, as a value of the reading. -/
theorem asW_w {ty : UScalarTy} (x : UScalar ty) : (AVal.w ty x).asW ty = .ok x := by
  simp [AVal.asW]

/-- The chain value of an Aeneas word as a value of the reading is its encoding. -/
theorem toValue_w {ty : UScalarTy} (x : UScalar ty) : (AVal.w ty x).toValue = wordV x := by
  simp only [AVal.toValue, wordV]

/-! ## The pointwise squares -/

deriving instance DecidableEq for AOp

/-- **Word operations.** At a width and an operation of `wordAt`, a value of the Aeneas
    word operation is, encoded, the value of the table at the tagged name. -/
theorem word_square {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true)
    (x y z : UScalar ty) (h : o.aen x y = .ok z) :
    hax64WExit (opName o ++ uTag ty) [wordV x, wordV y] = some (wordV z) := by
  have hf : WordOp.ofName (uTag ty) (opName o ++ uTag ty) = some o := by
    cases ty <;> cases o <;> decide +kernel
  have hr : appWord ty o (.w ty x) (.w ty y) = .ok (.w ty z) := by
    rw [appWord, asW_w, asW_w]
    simp only [bind_tc_ok, h]
  have h' := hax64WExit_appWord hw hf hr
  rwa [toValue_w, toValue_w, toValue_w] at h'

/-- **Complement.** -/
theorem not_square {ty : UScalarTy} (hty : tableTy ty = true) (x : UScalar ty) :
    hax64WExit ("Not#" ++ uTag ty) [wordV x] = some (wordV (~~~x)) := by
  have hr : appNot ty (.w ty x) = .ok (.w ty (~~~x)) := by
    rw [appNot, asW_w]
    simp only [bind_tc_ok]
  have h' := hax64WExit_appNot hty rfl hr
  rwa [toValue_w, toValue_w] at h'

/-- The checked name of an untagged operation `Add`, `Sub`, `Mul` at a width. -/
def checkedName (o : AOp) (ty : UScalarTy) : String :=
  match o with
  | .add => "Add#" ++ uTag ty
  | .sub => "Sub#" ++ uTag ty
  | .mul => "Mul#" ++ uTag ty
  | .div => "Div"
  | .rem => "Rem"

/-- The checked operations of the table: addition, subtraction and multiplication. -/
def taggedOp : AOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- The widths `8`, `16`, `32`, `64` and `usize` of the checked operations, as a class for
    instance resolution. -/
class CheckedTy (ty : UScalarTy) : Prop where
  /-- The width is one of `checkedTy`. -/
  checked : checkedTy ty = true

instance : CheckedTy .U8 := ⟨rfl⟩
instance : CheckedTy .U16 := ⟨rfl⟩
instance : CheckedTy .U32 := ⟨rfl⟩
instance : CheckedTy .U64 := ⟨rfl⟩
instance : CheckedTy .Usize := ⟨rfl⟩

/-- **Checked arithmetic.** At a width of `checkedTy`, a value of the checked Aeneas
    operation `+`, `-` or `*` is, encoded, the value of the table at the tagged name. -/
theorem checked_square {ty : UScalarTy} (hty : checkedTy ty = true) {o : AOp}
    (ho : taggedOp o = true) (x y z : UScalar ty) (h : o.aen x y = .ok z) :
    hax64WExit (checkedName o ty) [wordV x, wordV y] = some (wordV z) := by
  have hf : checkedAt? (checkedName o ty) = some (ty, o) := by
    cases o <;> simp [taggedOp] at ho <;> cases ty <;> decide +kernel
  have hr : appChecked ty o (.w ty x) (.w ty y) = .ok (.w ty z) := by
    rw [appChecked, asW_w, asW_w]
    simp only [bind_tc_ok, h]
  have h' := hax64WExit_appChecked hty hf hr
  rwa [toValue_w, toValue_w, toValue_w] at h'

/-! ## Rotations by a `u32` amount -/

/-- The rotations of the table at a width: the narrow table reads `rotate_left#t` and
    `rotate_right#t` at the width of the type. -/
theorem narrowOpOf_rot {ty : UScalarTy} (hty : tableTy ty = true) (o : WordOp)
    (ho : o = .rotl ∨ o = .rotr) :
    narrowOpOf (opName o ++ uTag ty) = some (ty.numBits, narrowOfWord o) := by
  rcases ho with rfl | rfl <;> cases ty <;>
    first | exact absurd hty (by decide) | decide +kernel

/-- The `rotate_left` of Aeneas by a `u32` amount is `rotlNat` at the width. -/
theorem rotate_left_val {ty : UScalarTy} (x : UScalar ty) (s : U32) :
    (UScalar.rotate_left x s).val = _root_.Hax.rotlNat ty.numBits x.val s.val := by
  have h := rcompOk_iff.mp (rotate_left_w_u_square x s) _ rfl
  simp only [EncRel, enc_uscalar, _root_.Hax.rotate_left_w, _root_.Hax.mod2w,
    Int.toNat_natCast] at h
  simp only [_root_.Hax.rotlNat]
  exact_mod_cast h

/-- The `rotate_right` of Aeneas by a `u32` amount is `rotrNat` at the width. -/
theorem rotate_right_val {ty : UScalarTy} (x : UScalar ty) (s : U32) :
    (UScalar.rotate_right x s).val = _root_.Hax.rotrNat ty.numBits x.val s.val := by
  have h := rcompOk_iff.mp (rotate_right_w_u_square x s) _ rfl
  simp only [EncRel, enc_uscalar, _root_.Hax.rotate_right_w, _root_.Hax.mod2w,
    Int.toNat_natCast] at h
  simp only [_root_.Hax.rotrNat]
  exact_mod_cast h

/-- **Rotations.** At a width of the table, the Aeneas rotation of a word by a `u32` amount
    is, encoded, the value of the table at the tagged rotation name. -/
theorem rot_square {ty : UScalarTy} (hty : tableTy ty = true) (o : WordOp)
    (ho : o = .rotl ∨ o = .rotr) (x : UScalar ty) (s : U32) :
    hax64WExit (opName o ++ uTag ty) [wordV x, wordV s] =
      some (wordV (if o = .rotl then UScalar.rotate_left x s else UScalar.rotate_right x s)) := by
  have hle := tableTy_numBits_le hty
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hle
  have hx : x.val < 2 ^ 64 := lt_of_lt_of_le x.hBounds h64
  have hs : s.val < 2 ^ 64 := lt_of_lt_of_le s.hBounds (by decide)
  have hw : wordAt ty o = true := by simp [wordAt, hty]
  have hf : WordOp.ofName (uTag ty) (opName o ++ uTag ty) = some o := by
    rcases ho with rfl | rfl <;> cases ty <;> decide +kernel
  set z := (if o = .rotl then UScalar.rotate_left x s else UScalar.rotate_right x s) with hz
  have hr : (narrowOfWord o).nat ty.numBits x.val s.val = some z.val := by
    rcases ho with rfl | rfl
    · simp [hz, narrowOfWord, NarrowOp.nat, rotate_left_val]
    · simp [hz, narrowOfWord, NarrowOp.nat, rotate_right_val]
  have hb := WordOpsSim.hax64Builtins_narrowOp _ _ (narrowOpOf_rot hty o ho) x.val s.val z.val
    hx hs hr
  exact hax64WExit_word_of_builtins (word_admit hw hf) hx hs
    (lt_of_lt_of_le z.hBounds h64) hb

/-! ## Casts -/

/-- **Casts.** A cast of Aeneas from a width of at most `64` bits to a width of the table is,
    encoded, the value of the table at `cast#t`. -/
theorem cast_square {src tgt : UScalarTy} (hsrc : src.numBits ≤ 64)
    (htgt : tableTy tgt = true) (x : UScalar src) :
    hax64WExit ("cast#" ++ uTag tgt) [wordV x] = some (wordV (UScalar.cast tgt x)) := by
  have h64 : 2 ^ src.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hsrc
  have hx : x.val < 2 ^ 64 := lt_of_lt_of_le x.hBounds h64
  have hc : narrowCastOf ("cast#" ++ uTag tgt) = some tgt.numBits := by
    cases tgt <;> first | exact absurd htgt (by decide) | decide +kernel
  have hv : (UScalar.cast tgt x).val = x.val % 2 ^ tgt.numBits := by
    unfold UScalar.cast UScalar.val
    exact BitVec.toNat_setWidth _ _
  have hb := WordOpsSim.hax64Builtins_narrowCast _ hc x.val
  have hne : ("cast#" ++ uTag tgt) ≠ "array_lit" ∧ ("cast#" ++ uTag tgt) ≠ "repeat" ∧
      ("cast#" ++ uTag tgt) ≠ "eq#arr" ∧ ("cast#" ++ uTag tgt) ≠ "ne#arr" ∧
      ("cast#" ++ uTag tgt) ≠ "len" ∧ ("cast#" ++ uTag tgt) ≠ "Not" := by
    cases tgt <;> decide +kernel
  have hres : exitScalarRes ("cast#" ++ uTag tgt) = true := by
    cases tgt <;> simp [exitScalarRes, exitScalarCall, uTag]
  have hto : exitMarshalOk (towerOfCallName ("cast#" ++ uTag tgt)) = true :=
    exitMarshalOk_of_arrCtorLen (by cases tgt <;> rfl)
  have hop : hax64ScalarOp ("cast#" ++ uTag tgt) = false := by
    cases tgt <;> decide +kernel
  unfold wordV
  rw [hv]
  refine hax64WExit_int_of_builtins hne hres hto (vals := [.int (x.val : Int)]) ?_
    (fun h => absurd h (by rw [hop]; decide)) (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by decide) (tableTy_numBits_le htgt))) hb
  intro v hv'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv'
  exact ⟨_, hv', hx⟩

/-! ## Comparisons and Boolean connectives -/

/-- A two-operand scalar call admitted by `hax64WExit` returns, on two scalar words, the
    Boolean value of `Hax.hax64Builtins`. -/
theorem hax64WExit_bool_of_builtins {f : String}
    (hne : f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ f ≠ "len")
    (hres : exitScalarRes f = true) (hto : exitMarshalOk (towerOfCallName f) = true)
    (hop : hax64ScalarOp f = true) {a b : Value} (ha : scalarValNB a = true)
    (hb' : scalarValNB b = true) {r : Bool} (hb : hax64Builtins f [a, b] = some (.bool r)) :
    hax64WExit f [a, b] = some (.bool r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hne
  rw [hax64WExit_of_ne h1 h2 h3 h4
    (fun hw => by obtain ⟨-, _, h⟩ := hax64Builtins_wideHead hw hb; cases h)
    (ne_select_of_exitScalarRes hres)]
  refine hax64Exit_of_scalarAdmit hb rfl ?_
  have h5' : (f != "len") = true := bne_iff_ne.mpr h5
  simp only [hax64ScalarAdmit, hax64ArgsShape, hres, hto, hop, ha, hb', h5', ite_true,
    List.length_cons, List.length_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.true_and, beq_self_eq_true]
  rfl

/-- The comparisons of Aeneas words. -/
inductive CmpOp
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq

/-- The name of a comparison in the table. -/
def CmpOp.name : CmpOp → String
  | .lt => "Lt" | .le => "Le" | .gt => "Gt" | .ge => "Ge" | .eq => "Eq" | .ne => "Ne"

/-- The Aeneas comparison of two words, as a Boolean on their values. -/
def CmpOp.aen {ty : UScalarTy} : CmpOp → UScalar ty → UScalar ty → Bool
  | .lt, x, y => decide (x.val < y.val)
  | .le, x, y => decide (x.val ≤ y.val)
  | .gt, x, y => decide (y.val < x.val)
  | .ge, x, y => decide (y.val ≤ x.val)
  | .eq, x, y => decide (x.val = y.val)
  | .ne, x, y => !decide (x.val = y.val)

/-- The Boolean equality of two natural numbers read as integers. -/
theorem int_beq_natCast (a b : Nat) : ((a : Int) == (b : Int)) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-- **Comparisons.** An Aeneas comparison of two words of at most `64` bits is the value of
    the table at its name. -/
theorem cmp_square {ty : UScalarTy} (hty : ty.numBits ≤ 64) (c : CmpOp) (x y : UScalar ty) :
    hax64WExit c.name [wordV x, wordV y] = some (.bool (c.aen x y)) := by
  have h64 : 2 ^ ty.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hty
  have hx : x.val < 2 ^ 64 := lt_of_lt_of_le x.hBounds h64
  have hy : y.val < 2 ^ 64 := lt_of_lt_of_le y.hBounds h64
  have hvx : scalarValNB (wordV x) = true := by simp [wordV, scalarValNB]; omega
  have hvy : scalarValNB (wordV y) = true := by simp [wordV, scalarValNB]; omega
  have hadm : (c.name ≠ "array_lit" ∧ c.name ≠ "repeat" ∧ c.name ≠ "eq#arr" ∧
      c.name ≠ "ne#arr" ∧ c.name ≠ "len") ∧ exitScalarRes c.name = true ∧
      exitMarshalOk (towerOfCallName c.name) = true ∧ hax64ScalarOp c.name = true := by
    cases c <;> exact ⟨by decide, by decide +kernel, exitMarshalOk_of_arrCtorLen rfl,
      by decide +kernel⟩
  obtain ⟨hne, hres, hto, hop⟩ := hadm
  refine hax64WExit_bool_of_builtins hne hres hto hop hvx hvy ?_
  apply WordOpsSim.hax64Builtins_of_some
  cases c <;> simp only [CmpOp.name, CmpOp.aen, wordV, _root_.Hax.hax64WordOps_Lt,
    _root_.Hax.hax64WordOps_Le, _root_.Hax.hax64WordOps_Gt, _root_.Hax.hax64WordOps_Ge,
    _root_.Hax.hax64WordOps_Eq, _root_.Hax.hax64WordOps_Ne, Nat.cast_lt, Nat.cast_le,
    bne, int_beq_natCast]

/-- The Boolean connectives of two operands. -/
inductive BoolOp
  | and | or
  deriving DecidableEq

/-- The name of a connective in the table. -/
def BoolOp.name : BoolOp → String
  | .and => "&&" | .or => "||"

/-- The value of a connective. -/
def BoolOp.val : BoolOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b

/-- **Boolean connectives.** -/
theorem bool_square (o : BoolOp) (a b : Bool) :
    hax64WExit o.name [.bool a, .bool b] = some (.bool (o.val a b)) := by
  have hadm : (o.name ≠ "array_lit" ∧ o.name ≠ "repeat" ∧ o.name ≠ "eq#arr" ∧
      o.name ≠ "ne#arr" ∧ o.name ≠ "len") ∧ exitScalarRes o.name = true ∧
      exitMarshalOk (towerOfCallName o.name) = true ∧ hax64ScalarOp o.name = true := by
    cases o <;> exact ⟨by decide, by decide +kernel, exitMarshalOk_of_arrCtorLen rfl,
      by decide +kernel⟩
  obtain ⟨hne, hres, hto, hop⟩ := hadm
  refine hax64WExit_bool_of_builtins hne hres hto hop rfl rfl ?_
  apply WordOpsSim.hax64Builtins_of_some
  cases o
  · exact _root_.Hax.hax64WordOps_andand a b
  · exact _root_.Hax.hax64WordOps_oror a b

/-! ## The ParamTransfer instances -/

/-- The total word operations: the bitwise and wrapping operations. -/
def WordOp.total : WordOp → Bool
  | .band | .bor | .bxor | .wadd | .wsub | .wmul => true
  | _ => false

theorem WordOp.aen_ok_of_total {ty : UScalarTy} {o : WordOp} (ho : WordOp.total o = true)
    (x y : UScalar ty) : OkR (o.aen x y) := by
  cases o <;> simp [WordOp.total] at ho <;> exact ⟨_, rfl⟩

/-- **The total word operations as `RelatedBinOp` squares.** -/
theorem wordRelated {ty : UScalarTy} [h : TableTy ty] (o : WordOp)
    (ho : WordOp.total o = true) :
    RelatedBinOp (encU ty) (bindR2 o.aen) (call2 (opName o ++ uTag ty)) :=
  ⟨relatedBinOp_of (WordOp.aen_ok_of_total ho)
    (word_square (by simp [wordAt, h.table]))⟩

instance bandRelated {ty : UScalarTy} [TableTy ty] :
    RelatedBinOp (encU ty) (bindR2 (WordOp.aen .band)) (call2 (opName .band ++ uTag ty)) :=
  wordRelated .band rfl
instance borRelated {ty : UScalarTy} [TableTy ty] :
    RelatedBinOp (encU ty) (bindR2 (WordOp.aen .bor)) (call2 (opName .bor ++ uTag ty)) :=
  wordRelated .bor rfl
instance bxorRelated {ty : UScalarTy} [TableTy ty] :
    RelatedBinOp (encU ty) (bindR2 (WordOp.aen .bxor)) (call2 (opName .bxor ++ uTag ty)) :=
  wordRelated .bxor rfl
instance waddRelated {ty : UScalarTy} [TableTy ty] :
    RelatedBinOp (encU ty) (bindR2 (WordOp.aen .wadd)) (call2 (opName .wadd ++ uTag ty)) :=
  wordRelated .wadd rfl
instance wsubRelated {ty : UScalarTy} [TableTy ty] :
    RelatedBinOp (encU ty) (bindR2 (WordOp.aen .wsub)) (call2 (opName .wsub ++ uTag ty)) :=
  wordRelated .wsub rfl
instance wmulRelated {ty : UScalarTy} [TableTy ty] :
    RelatedBinOp (encU ty) (bindR2 (WordOp.aen .wmul)) (call2 (opName .wmul ++ uTag ty)) :=
  wordRelated .wmul rfl

/-- **The shifts as guarded squares**: where the Aeneas shift returns a value, the table
    returns its encoding. -/
instance shiftRelated {ty : UScalarTy} [h : TableTy ty] (o : WordOp) :
    RelatedBinOpOn (encU ty) (fun a b => OkR (bindR2 o.aen a b)) (bindR2 o.aen)
      (call2 (opName o ++ uTag ty)) :=
  relatedBinOpOn_of (word_square (by simp [wordAt, h.table]))

/-- **The checked operations as guarded squares.** -/
instance checkedRelated {ty : UScalarTy} [h : CheckedTy ty] (o : AOp)
    [ho : Fact (taggedOp o = true)] :
    RelatedBinOpOn (encU ty) (fun a b => OkR (bindR2 o.aen a b)) (bindR2 o.aen)
      (call2 (checkedName o ty)) :=
  relatedBinOpOn_of (checked_square h.checked ho.out)

instance : Fact (taggedOp .add = true) := ⟨rfl⟩
instance : Fact (taggedOp .sub = true) := ⟨rfl⟩
instance : Fact (taggedOp .mul = true) := ⟨rfl⟩

/-- **The complement as a `RelatedUnOp` square.** -/
instance notRelated {ty : UScalarTy} [h : TableTy ty] :
    RelatedUnOp (encU ty) (bindR1 fun x => .ok (~~~x)) (call1 ("Not#" ++ uTag ty)) :=
  ⟨relatedUnOp_of (fun _ => ⟨_, rfl⟩) (fun x z hz => by
    cases hz
    exact not_square h.table x)⟩

/-- **Rotation left by a fixed `u32` amount as a `RelatedUnOp` square.** -/
instance rotlRelated {ty : UScalarTy} [h : TableTy ty] (s : U32) :
    RelatedUnOp (encU ty) (bindR1 fun x => .ok (UScalar.rotate_left x s))
      (fun a => a.bind fun v => hax64WExit (opName .rotl ++ uTag ty) [v, wordV s]) :=
  ⟨fun a => by
    cases a with
    | ok x =>
      have := rot_square h.table .rotl (.inl rfl) x s
      simp only [ite_true] at this
      exact this.symm
    | fail _ => rfl
    | div => rfl⟩

/-- **Rotation right by a fixed `u32` amount as a `RelatedUnOp` square.** -/
instance rotrRelated {ty : UScalarTy} [h : TableTy ty] (s : U32) :
    RelatedUnOp (encU ty) (bindR1 fun x => .ok (UScalar.rotate_right x s))
      (fun a => a.bind fun v => hax64WExit (opName .rotr ++ uTag ty) [v, wordV s]) :=
  ⟨fun a => by
    cases a with
    | ok x =>
      have := rot_square h.table .rotr (.inr rfl) x s
      simp only [show WordOp.rotr ≠ WordOp.rotl by decide, ite_false] at this
      exact this.symm
    | fail _ => rfl
    | div => rfl⟩

/-- **Casts as squares between two widths**: a related operand gives a related cast. -/
instance castRelated {src tgt : UScalarTy} [hs : TableTy src] [ht : TableTy tgt]
    (a : RustM (UScalar src)) (a' : Option Value) [ha : Related (encU src) a a'] :
    Related (encU tgt) (bindR1 (fun x => .ok (UScalar.cast tgt x)) a)
      (call1 ("cast#" ++ uTag tgt) a') where
  rel := by
    rw [← ha.rel]
    exact relatedUnOp_of (fun _ => ⟨_, rfl⟩) (fun x z hz => by
      cases hz
      exact cast_square (TableTy.le64 src) ht.table x) a

/-- **Comparisons as squares from words to Booleans.** -/
instance cmpRelated {ty : UScalarTy} [h : TableTy ty] (c : CmpOp)
    (a b : RustM (UScalar ty)) (a' b' : Option Value) [ha : Related (encU ty) a a']
    [hb : Related (encU ty) b b'] :
    Related encB (bindR2 (fun x y => .ok (c.aen x y)) a b) (call2 c.name a' b') where
  rel := by
    rw [← ha.rel, ← hb.rel]
    exact relatedBinOp_of (fun _ _ => ⟨_, rfl⟩) (fun x y z hz => by
      cases hz
      exact cmp_square (TableTy.le64 ty) c x y) a b

/-- **Boolean connectives as `RelatedBinOp` squares.** -/
instance boolRelated (o : BoolOp) :
    RelatedBinOp encB (bindR2 fun a b => .ok (o.val a b)) (call2 o.name) :=
  ⟨relatedBinOp_of (fun _ _ => ⟨_, rfl⟩) (fun x y z hz => by
    cases hz
    exact bool_square o x y)⟩

/-- **The negation of a Boolean** is the value of the table at `Not`. -/
theorem notBool_square (b : Bool) : hax64WExit "Not" [.bool b] = some (.bool !b) := by
  have hres : exitScalarRes "Not" = true := by decide +kernel
  have hop : hax64ScalarOp "Not" = false := by decide +kernel
  have hto : exitMarshalOk (towerOfCallName "Not") = true := exitMarshalOk_of_arrCtorLen rfl
  have hb : hax64Builtins "Not" [.bool b] = some (.bool !b) :=
    WordOpsSim.hax64Builtins_of_some (_root_.Hax.hax64WordOps_notBool b)
  rw [hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  unfold hax64Exit
  rw [hb]
  simp only [hax64ScalarAdmit, hax64ArgsShape, hres, hop, hto, scalarValNB, Value.isControlFlow,
    Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false, ite_true, Bool.and_true]
  rfl

/-- **The negation of a Boolean as a `RelatedUnOp` square.** -/
instance notBoolRelated :
    RelatedUnOp encB (bindR1 fun b => .ok (!b)) (call1 "Not") :=
  ⟨relatedUnOp_of (fun _ => ⟨_, rfl⟩) (fun x z hz => by
    cases hz
    exact notBool_square x)⟩

/-- The selection of one of two words by a Boolean, as an Aeneas value. -/
def selW {ty : UScalarTy} (k : Bool) (x y : UScalar ty) : UScalar ty := if k then x else y

/-- **Selection.** The selection of one of two words of any width by a Boolean is the value of
    the table at `select`. -/
theorem select_square {ty : UScalarTy} (k : Bool) (x y : UScalar ty) :
    hax64WExit "select" [.bool k, wordV x, wordV y] = some (wordV (selW k x y)) := by
  rw [hax64WExit_select_bool k rfl rfl]
  cases k <;> rfl

/-- A three-argument call of `hax64WExit` lifted to optional values. -/
def call3 (f : String) (a b c : Option Value) : Option Value :=
  a.bind fun x => b.bind fun y => c.bind fun z => hax64WExit f [x, y, z]

/-- **Selection as a square from a Boolean and two words to a word**: related operands give a
    related selection, at every width. -/
instance selectRelated {ty : UScalarTy} (c : RustM Bool) (a b : RustM (UScalar ty))
    (c' a' b' : Option Value) [hc : Related encB c c'] [ha : Related (encU ty) a a']
    [hb : Related (encU ty) b b'] :
    Related (encU ty) (c >>= fun k => bindR2 (fun x y => .ok (selW k x y)) a b)
      (call3 "select" c' a' b') where
  rel := by
    rw [← hc.rel, ← ha.rel, ← hb.rel]
    cases c <;> cases a <;> cases b <;>
      simp only [encR, call3, bindR2, bind_tc_ok, Option.bind_some, Option.bind_none,
        select_square] <;> rfl

/-- **Literals**: a word value encodes as the integer of its value. -/
instance litRelated {ty : UScalarTy} (x : UScalar ty) :
    Related (encU ty) (.ok x) (some (.int (x.val : Int))) := ⟨rfl⟩

/-- **A composite by instance resolution.** The Aeneas expression
    `wrapping_add (a &&& b) (c ^^^ d)` over outcomes is related to the call tree
    `wrapping_add#t (BitAnd#t a b) (BitXor#t c d)` of the table, at every width of the table,
    by the `composeBinOp` closure of ParamTransfer over the registered squares. -/
theorem wordComposite_related {ty : UScalarTy} [TableTy ty] (a b c d : RustM (UScalar ty)) :
    encU ty (bindR2 (WordOp.aen .wadd) (bindR2 (WordOp.aen .band) a b)
        (bindR2 (WordOp.aen .bxor) c d)) =
      call2 (opName .wadd ++ uTag ty) (call2 (opName .band ++ uTag ty) (encU ty a) (encU ty b))
        (call2 (opName .bxor ++ uTag ty) (encU ty c) (encU ty d)) :=
  (inferInstance : Related (encU ty) _ _).rel

end CatCrypt.Crypto.SecureCompilation.AeneasFront
