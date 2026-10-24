/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustM
public import HaxAscent.RustSemantics.Arith
public import HaxAscent.RustSemantics.Casts
public import HaxAscent.Ascent.ExtTable

/-!
# The state-passing `RustM` reading of haxpipe literals

`toRustMS app e ρ` reads the literal `e` as an Aeneas program over `Aeneas.Std.RustM` that
threads an environment, as `Hax.denote'` does: a `letBind` extends the environment for the
rest of the run, a counted loop `forFold` (upwards) or `forFoldRev` (downwards) binds its
index and keeps the bindings its body makes, and a call `.app f args` evaluates its arguments left to right and applies
`app f` to their values, a tuple `.tuple es` of any arity evaluates its components left to
right, and a projection `.proj e i` returns component `i` of the tuple
`e` returns. The values (`AVal`) are integer literals, Booleans, unsigned
words of every Aeneas width, Aeneas arrays `Aeneas.Std.Array (UScalar ty) n` of words,
tuples and the unit value.

`appRt` is the reading of the runtime operations: the width-tagged word operations of
`WordOp` at each of the six unsigned widths, `Not#w`, `cast#w`, `wrapping_neg#w`
(`appNeg`), the checked width-tagged operations `Add#w`, `Sub#w`, `Mul#w` (`checkedAt?`,
`appChecked`: both operands read at the width of the tag, the value of the checked operation
of `u<w>`), the untagged checked operations `Add`, `Sub`, `Mul`, `Div`, `Rem`, the
declassification `declassify` of a word (`appDeclassify`), the array operations `index`,
`array_update`, `repeat`, `len` and `array_lit` on the Aeneas `Array` model (`array_lit` at
every number of arguments, `appArrayLit`), the untagged negation `Not` of a
Boolean, the strict connectives `&&` and `||` and the equality and disequality of two
Booleans, and the comparisons `Lt`, `Le`, `Gt`, `Ge`, `Eq` and `Ne` of two integers or words
(`appBNot`, `appBool2`), and the field heads `<method>#p<modulus>` that `FieldTag.fieldTag?`
reads at a modulus below `2^64`, on `u64` words below the modulus (`appField1`, `appField2`:
the `u64` word of the value `FieldTag.fieldVal` of the method). An untyped integer literal is
read at the width of the operation that consumes it (`AVal.asW`). An untagged checked
operation takes its width from a word operand, fails where the Aeneas operation at that
width fails, and returns no value on two integer literals (`appArith_int_int`), so every
value it returns is a word (`appArith_word`). The loop index is the
`usize` word `⟨BitVec.ofNat _ i⟩`, as in the hax backend's `fold_range`.

## Pasting

`AVal.toValue` encodes a value as a `Hax.Value`: a word by its value, an array by the
list of its entries. `AppOk bi app` states that every value `app f vs` returns is, encoded,
the value the builtin table `bi` returns on the encoded arguments; `appRt_ok` proves it for
`runtimeBuiltins base`, and so for the table `extBuiltins T fns` of every extraction.
The pasting theorem `toRustMS_sim` composes these squares along the literal by
functional induction: when the reading returns `(v, ρ')` from `ρ`, the run of the literal
from `encEnv ρ` returns `(.val v.toValue, encEnv ρ')` at every fuel from some fuel on.

## Calls to the functions of an extraction

`appExt fns` extends `appRt` by the functions of an extraction: a call to `fn` is read by
`callS`, the reading of its literal from the environment binding its parameters over its
constants, under the reading of the functions before it, as `extBuiltins T fns` reads it.
`appExt_ok` proves `AppOk (extBuiltins T fns) (appExt fns)` when the names of `fns` are free
in the runtime table and in `T` (`ExtNamesOk`, a Boolean the kernel decides).

## Composition with the ascent

`fnCorres_toRustMS` composes the pasting theorem with a function correspondence
`FnCorres bi e entry G f` of the ascent: every value the reading returns from an
environment whose encoding is `entry a` encodes `f a`. No equation between the literal and
the surface function is needed. `fragOk` is the syntactic fragment of the reading: the
constructs it reads, and the call names `appRt` or a local function reads.

## Main definitions

* `AVal`, `AVal.toValue`, `AEnv`, `AEnv.upd`, `encEnv`, `AVal.asW`
* `appRt`, `AppOk`, `loopS`, `loopRevS`, `toRustMS`, `callS`, `appExt`, `ExtNamesOk`,
  `fragOk`, `appBNot`, `boolRt?`, `cmpRt?`, `appBool2`, `checkedAt?`, `appChecked`, `appNeg`,
  `appField1`, `appField2`
* `appBNot_ok`, `appBool2_ok`, `appBool2_undef`, `appChecked_ok`, `appNeg_ok`,
  `appField1_rt`, `appField2_rt`, `appRt_checkedAt`, `appRt_negAt`, `appRt_declassify`,
  `appRt_mul_p7`
* `appRt_ok`, `loopS_sim`, `loopRevS_sim`, `toRustMS_sim`, `appExt_ok`, `fnCorres_toRustMS`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std

/-! ## Values and environments -/

deriving instance DecidableEq for UScalarTy

/-- A value of the state-passing reading. -/
inductive AVal where
  /-- An integer literal, not yet read at a width. -/
  | int (n : Int)
  /-- A Boolean. -/
  | bool (b : Bool)
  /-- An unsigned word. -/
  | w (ty : UScalarTy) (x : UScalar ty)
  /-- An Aeneas array of unsigned words. -/
  | arr (ty : UScalarTy) (n : Usize) (a : Aeneas.Std.Array (UScalar ty) n)
  /-- A tuple. -/
  | tup (vs : List AVal)
  /-- The unit value. -/
  | unit

mutual

/-- The runtime value encoding a value of the reading: a word by its value, an array by the
    list of its entries. -/
def AVal.toValue : AVal → Hax.Value
  | .int n => .int n
  | .bool b => .bool b
  | .w _ x => .int (x.val : Int)
  | .arr _ _ a => .array (a.val.map fun x => .int (x.val : Int))
  | .tup vs => .tuple (AVal.toValues vs)
  | .unit => .unit

/-- The encodings of a list of values. -/
def AVal.toValues : List AVal → List Hax.Value
  | [] => []
  | v :: vs => v.toValue :: AVal.toValues vs

end

theorem AVal.toValue_isControlFlow (v : AVal) : v.toValue.isControlFlow = false := by
  cases v <;> rfl

theorem AVal.toValue_ne_break (v : AVal) (w : Hax.Value) : v.toValue ≠ .controlFlow true w := by
  cases v <;> simp [AVal.toValue]

theorem AVal.toValues_eq_map (vs : List AVal) : AVal.toValues vs = vs.map AVal.toValue := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [AVal.toValues, ih]; rfl

/-- An environment of the reading. -/
abbrev AEnv := String → Option AVal

/-- The environment `ρ` with `x` bound to `v`, shadowing as `Hax.Env.extend` does. -/
def AEnv.upd (ρ : AEnv) (x : String) (v : AVal) : AEnv :=
  fun y => if y == x then some v else ρ y

/-- The runtime environment encoding an environment of the reading. -/
def encEnv (ρ : AEnv) : Hax.Env := fun y => (ρ y).map AVal.toValue

theorem encEnv_upd (ρ : AEnv) (x : String) (v : AVal) :
    encEnv (ρ.upd x v) = (encEnv ρ).extend x v.toValue := by
  funext y
  simp only [encEnv, AEnv.upd, Hax.Env.extend]
  split <;> rfl

/-- The word of width `ty` a value stands for: an integer literal in range, or a word of
    that width. -/
def AVal.asW (ty : UScalarTy) : AVal → RustM (UScalar ty)
  | .int n => litA ty n
  | .w ty' x => if h : ty' = ty then .ok (h ▸ x) else .fail .undef
  | _ => .fail .undef

theorem AVal.asW_ok {ty : UScalarTy} {v : AVal} {x : UScalar ty} (h : v.asW ty = .ok x) :
    v.toValue = .int (enc x) := by
  cases v with
  | int n =>
    simp only [AVal.asW] at h
    rw [AVal.toValue, litA_ok h]
  | w ty' y =>
    simp only [AVal.asW] at h
    split at h
    · rename_i hty
      subst hty
      cases h
      rfl
    · cases h
  | _ => cases h

/-- The integer a literal or a word stands for. -/
def AVal.toInt? : AVal → Option Int
  | .int n => some n
  | .w _ x => some (x.val : Int)
  | _ => none

theorem AVal.toValue_of_toInt? {v : AVal} {n : Int} (h : v.toInt? = some n) :
    v.toValue = .int n := by
  cases v <;> simp_all [AVal.toInt?, AVal.toValue]

theorem rustM_bind_ok {α β : Type} {x : RustM α} {f : α → RustM β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => cases h
  | div => cases h

/-! ## The runtime operations -/

/-- The unsigned widths, in the order the tags are tried. -/
def uTys : List UScalarTy := [.U8, .U16, .U32, .U64, .U128, .Usize]

/-- The width and operation of a tagged binary word operation name. -/
def wordOpAt? (f : String) : Option (UScalarTy × WordOp) :=
  uTys.findSome? fun ty => (WordOp.ofName (uTag ty) f).map (ty, ·)

/-- The width of a name `pre ++ tag`. -/
def tagTyAt? (pre f : String) : Option UScalarTy :=
  uTys.find? fun ty => decide (f = pre ++ uTag ty)

theorem wordOpAt?_spec {f : String} {ty : UScalarTy} {o : WordOp}
    (h : wordOpAt? f = some (ty, o)) : WordOp.ofName (uTag ty) f = some o := by
  obtain ⟨ty', _, h'⟩ := List.exists_of_findSome?_eq_some h
  cases h1 : WordOp.ofName (uTag ty') f with
  | none => rw [h1] at h'; cases h'
  | some o' =>
    rw [h1] at h'
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact h1

theorem tagTyAt?_spec {pre f : String} {ty : UScalarTy} (h : tagTyAt? pre f = some ty) :
    f = pre ++ uTag ty := by
  have := List.find?_some h
  simpa using this

/-- The untagged checked arithmetic operations. -/
inductive AOp
  | add | sub | mul | div | rem

/-- The operation an untagged name denotes. -/
def AOp.ofName (f : String) : Option AOp :=
  if f = "Add" then some .add
  else if f = "Sub" then some .sub
  else if f = "Mul" then some .mul
  else if f = "Div" then some .div
  else if f = "Rem" then some .rem
  else none

/-- The Aeneas checked operation. -/
def AOp.aen {ty : UScalarTy} : AOp → UScalar ty → UScalar ty → RustM (UScalar ty)
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .rem, x, y => x % y

/-- The runtime operation on unbounded integers. -/
def AOp.rt : AOp → Int → Int → Int
  | .add => Hax.add
  | .sub => Hax.sub
  | .mul => Hax.mul
  | .div => Hax.div
  | .rem => Hax.rem

theorem AOp.square {ty : UScalarTy} (o : AOp) (x y : UScalar ty) :
    RCompOk EncRel (o.aen x y) (pure (o.rt (enc x) (enc y)) : Id Int) := by
  cases o
  · exact add_u_square x y
  · exact sub_u_square x y
  · exact mul_u_square x y
  · exact div_u_square x y
  · exact rem_u_square x y

/-- The width and operation of a checked width-tagged name `Add#t`, `Sub#t` or `Mul#t`. -/
def checkedAt? (f : String) : Option (UScalarTy × AOp) :=
  match tagTyAt? "Add#" f with
  | some ty => some (ty, .add)
  | none =>
    match tagTyAt? "Sub#" f with
    | some ty => some (ty, .sub)
    | none => (tagTyAt? "Mul#" f).map fun ty => (ty, .mul)

theorem checkedAt?_spec {f : String} {ty : UScalarTy} {o : AOp}
    (h : checkedAt? f = some (ty, o)) :
    (o = .add ∧ f = "Add#" ++ uTag ty) ∨ (o = .sub ∧ f = "Sub#" ++ uTag ty) ∨
      (o = .mul ∧ f = "Mul#" ++ uTag ty) := by
  unfold checkedAt? at h
  split at h
  · rename_i ty' h1
    cases h
    exact .inl ⟨rfl, tagTyAt?_spec h1⟩
  · split at h
    · rename_i ty' h1
      cases h
      exact .inr (.inl ⟨rfl, tagTyAt?_spec h1⟩)
    · rcases h2 : tagTyAt? "Mul#" f with _ | ty'
      · rw [h2] at h; cases h
      · rw [h2] at h
        cases h
        exact .inr (.inr ⟨rfl, tagTyAt?_spec h2⟩)

/-- The checked operation of Rust `u<w>` on integers, `none` where Rust panics. -/
def AOp.checkedRt (w : Nat) : AOp → Int → Int → Option Hax.Value
  | .add => Hax.uintAddOp w
  | .sub => Hax.uintSubOp w
  | .mul => Hax.uintMulOp w
  | .div => Hax.uintDivOp w
  | .rem => Hax.uintRemOp w

/-- A checked width-tagged operation at width `ty`: both operands are read at `ty`, and the
    Aeneas operation fails where Rust panics. -/
def appChecked (ty : UScalarTy) (o : AOp) (a b : AVal) : RustM AVal := do
  let x ← a.asW ty
  let y ← b.asW ty
  let r ← o.aen x y
  .ok (.w ty r)

/-- A tagged binary word operation at width `ty`. -/
def appWord (ty : UScalarTy) (o : WordOp) (a b : AVal) : RustM AVal := do
  let x ← a.asW ty
  let y ← b.asW ty
  let r ← o.aen x y
  .ok (.w ty r)

/-- An untagged checked operation: the Aeneas operation at the width of the word operand,
    which fails where Rust panics. An integer literal beside a word is read at the width of
    the word and must be in its range. Two integer literals have no width in this reading,
    and the operation returns no value on them. -/
def appArith (o : AOp) : AVal → AVal → RustM AVal
  | .w ty x, b => do
    let y ← b.asW ty
    let r ← o.aen x y
    .ok (.w ty r)
  | .int n, .w ty y => do
    let x ← litA ty n
    let r ← o.aen x y
    .ok (.w ty r)
  | _, _ => .fail .undef

/-- `index` on an array of words. -/
def appIndex : AVal → AVal → RustM AVal
  | .arr ty _ a, i => do
    let j ← i.asW .Usize
    let x ← a.index_usize j
    .ok (.w ty x)
  | _, _ => .fail .undef

/-- `array_update` on an array of words. -/
def appUpdate : AVal → AVal → AVal → RustM AVal
  | .arr ty n a, i, v => do
    let j ← i.asW .Usize
    let x ← v.asW ty
    let a' ← a.update j x
    .ok (.arr ty n a')
  | _, _, _ => .fail .undef

/-- `repeat` of a word. -/
def appRepeat : AVal → AVal → RustM AVal
  | .w ty x, n => do
    let m ← n.asW .Usize
    .ok (.arr ty m (Aeneas.Std.Array.repeat m x))
  | _, _ => .fail .undef

/-- `len` of an array: its length, an integer literal. -/
def appLen : AVal → RustM AVal
  | .arr _ _ a => .ok (.int a.val.length)
  | _ => .fail .undef

/-- The words of the width `ty` the values of a list stand for (`AVal.asW`). -/
def AVal.asWList (ty : UScalarTy) : List AVal → RustM (List (UScalar ty))
  | [] => .ok []
  | a :: as => a.asW ty >>= fun x => AVal.asWList ty as >>= fun xs => .ok (x :: xs)

/-- `array_lit` of values: the array of the words they stand for at the width of the first,
    a word, with its length as a `usize` word. -/
def appArrayLit : List AVal → RustM AVal
  | .w ty x :: as => AVal.asWList ty (.w ty x :: as) >>= fun xs =>
    (AVal.int xs.length).asW .Usize >>= fun n =>
      if h : xs.length = n.val then .ok (.arr ty n (Aeneas.Std.Array.make n xs h))
      else .fail .undef
  | _ => .fail .undef

/-- `cast#w` of a word to the width `ty`. -/
def appCast (ty : UScalarTy) : AVal → RustM AVal
  | .w _ x => .ok (.w ty (UScalar.cast ty x))
  | _ => .fail .undef

/-- `Not#w` at the width `ty`. -/
def appNot (ty : UScalarTy) (a : AVal) : RustM AVal := do
  let x ← a.asW ty
  .ok (.w ty (~~~x))

/-- The untagged negation `Not` of a Boolean. -/
def appBNot : AVal → RustM AVal
  | .bool x => .ok (.bool (Hax.Not x))
  | _ => .fail .undef

/-- The declassification `declassify` of a word: the identity on words. -/
def appDeclassify : AVal → RustM AVal
  | .w ty x => .ok (.w ty x)
  | _ => .fail .undef

/-- `wrapping_neg#w` at the width `ty`: the two's complement negation. -/
def appNeg (ty : UScalarTy) (a : AVal) : RustM AVal := do
  let x ← a.asW ty
  .ok (.w ty ⟨-x.bv⟩)

/-- A field head of the method `m` with one argument at a modulus `p` below `2^64`: the operand
    is read as a `u64` word below `p`, and the value is the `u64` word of the value
    `FieldTag.fieldVal` of the method. -/
def appField1 (m : Hax.FieldTag.FieldMethod) (p : Nat) (a : AVal) : RustM AVal := do
  let x ← a.asW .U64
  if p < 2 ^ 64 ∧ m.binary = false ∧ x.val < p then
    .ok (.w .U64 ⟨BitVec.ofNat _ (Hax.FieldTag.fieldVal m p x.val 0)⟩)
  else .fail .undef

/-- A field head of the method `m` with two arguments at a modulus `p` below `2^64`: both
    operands are read as `u64` words below `p`, and the value is the `u64` word of the value
    `FieldTag.fieldVal` of the method. -/
def appField2 (m : Hax.FieldTag.FieldMethod) (p : Nat) (a b : AVal) : RustM AVal := do
  let x ← a.asW .U64
  let y ← b.asW .U64
  if p < 2 ^ 64 ∧ m.binary = true ∧ x.val < p ∧ y.val < p then
    .ok (.w .U64 ⟨BitVec.ofNat _ (Hax.FieldTag.fieldVal m p x.val y.val)⟩)
  else .fail .undef

/-- The comparisons of two integers with a Boolean result, by name. -/
def cmpRt? : String → Option (Int → Int → Bool)
  | "Lt" => some Hax.lt
  | "Le" => some Hax.le
  | "Gt" => some Hax.gt
  | "Ge" => some Hax.ge
  | "Eq" => some Hax.beq
  | "Ne" => some Hax.bne
  | _ => none

/-- The Boolean connectives and comparisons of two Booleans, by name: the strict `&&` and
    `||`, the equality and the disequality. -/
def boolRt? : String → Option (Bool → Bool → Bool)
  | "&&" => some Hax.band
  | "||" => some Hax.bor
  | "Eq" => some Hax.beq
  | "Ne" => some Hax.bne
  | _ => none

/-- A binary operation with a Boolean result: on two Booleans the operation `boolRt?` names,
    on two integer literals or words the comparison `cmpRt?` names of the integers they
    stand for. Both operands are values, so `&&` and `||` are read strictly. -/
def appBool2 (f : String) (a b : AVal) : RustM AVal :=
  match a, b with
  | .bool x, .bool y =>
    match boolRt? f with
    | some g => .ok (.bool (g x y))
    | none => .fail .undef
  | _, _ =>
    match cmpRt? f, a.toInt?, b.toInt? with
    | some g, some x, some y => .ok (.bool (g x y))
    | _, _, _ => .fail .undef

/-- At a name neither `boolRt?` nor `cmpRt?` names, `appBool2` fails. -/
theorem appBool2_undef {f : String} (hb : boolRt? f = none) (hc : cmpRt? f = none)
    (a b : AVal) : appBool2 f a b = .fail .undef := by
  unfold appBool2
  split
  · rw [hb]
  · rw [hc]

/-- **The reading of the runtime operations.** -/
def appRt (f : String) : List AVal → RustM AVal
  | [a] =>
    match tagTyAt? "Not#" f with
    | some ty => appNot ty a
    | none =>
      match tagTyAt? "cast#" f with
      | some ty => appCast ty a
      | none =>
        match tagTyAt? "wrapping_neg#" f with
        | some ty => appNeg ty a
        | none =>
          if f = "range_incl_end" then
            match a.toInt? with
            | some k => .ok (.int (k + 1))
            | none => .fail .undef
          else if f = "Not" then appBNot a
          else if f = "len" then appLen a
          else if f = "array_lit" then appArrayLit [a]
          else if f = "declassify" then appDeclassify a
          else
            match Hax.FieldTag.fieldTag? f with
            | some (m, p) => appField1 m p a
            | none => .fail .undef
  | [a, b] =>
    match wordOpAt? f with
    | some (ty, o) => appWord ty o a b
    | none =>
      match checkedAt? f with
      | some (ty, o) => appChecked ty o a b
      | none =>
        match AOp.ofName f with
        | some o => appArith o a b
        | none =>
          if f = "index" then appIndex a b
          else if f = "repeat" then appRepeat a b
          else if f = "array_lit" then appArrayLit [a, b]
          else
            match Hax.FieldTag.fieldTag? f with
            | some (m, p) => appField2 m p a b
            | none => appBool2 f a b
  | [a, i, v] =>
    if f = "array_update" then appUpdate a i v
    else if f = "array_lit" then appArrayLit [a, i, v]
    else .fail .undef
  | vs => if f = "array_lit" then appArrayLit vs else .fail .undef

/-- The reading of the calls agrees with the builtin table `bi`: every value `app f vs`
    returns is, encoded, the value `bi f` returns on the encoded arguments. -/
def AppOk (bi : Hax.Builtins) (app : String → List AVal → RustM AVal) : Prop :=
  ∀ f vs r, app f vs = .ok r → bi f (AVal.toValues vs) = some r.toValue

/-! ## The runtime table on the reading's names -/

section Leaves

open Hax.Ascent Hax.Ascent.RuntimeOps

variable {base : Hax.Builtins}

/-- A tagged binary word operation name is read by the runtime at the width of its tag. -/
theorem WordOp.leaf {ty : UScalarTy} {o : WordOp} {f : String}
    (hf : WordOp.ofName (uTag ty) f = some o) (x y : Int) :
    runtimeBuiltins base f [.int x, .int y] = some (.int (o.rt ty.numBits x y)) := by
  unfold WordOp.ofName at hf
  (repeat' split at hf) <;> cases hf <;> subst f <;> cases ty <;>
    simp only [uTag, String.reduceAppend]
  all_goals first
    | exact tagged2 (op := "BitAnd") (g := Hax.bitand_w) rfl (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "BitOr") (g := Hax.bitor_w) rfl (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "BitXor") (g := Hax.bitxor_w) rfl (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "wrapping_add") (g := Hax.wrapping_add_w) rfl
        (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "wrapping_sub") (g := Hax.wrapping_sub_w) rfl
        (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "wrapping_mul") (g := Hax.wrapping_mul_w) rfl
        (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "Shr") (g := Hax.shr_w) rfl (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "Shl") (g := Hax.shl_w) rfl (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "rotate_right") (g := Hax.rotate_right_w) rfl
        (by first | decide | rfl) rfl x y
    | exact tagged2 (op := "rotate_left") (g := Hax.rotate_left_w) rfl
        (by first | decide | rfl) rfl x y

/-- `Not#w` is read by the runtime at the width of its tag. -/
theorem not_leaf {ty : UScalarTy} (x : Int) :
    runtimeBuiltins base ("Not#" ++ uTag ty) [.int x] =
      some (.int (Hax.bitnot_w ty.numBits x)) := by
  cases ty <;> simp only [uTag, String.reduceAppend] <;>
    exact tagged1 (op := "Not") (g := Hax.bitnot_w) rfl (by first | decide | rfl) rfl x

/-- `wrapping_neg#w` is read by the runtime at the width of its tag. -/
theorem neg_leaf {ty : UScalarTy} (x : Int) :
    runtimeBuiltins base ("wrapping_neg#" ++ uTag ty) [.int x] =
      some (.int (Hax.wrapping_neg_w ty.numBits x)) := by
  cases ty <;> simp only [uTag, String.reduceAppend] <;>
    exact runtimeBuiltins_negAt base (by first | decide | rfl) x

/-- A checked width-tagged name is read by the runtime as the checked operation of `u<w>` at
    the width of its tag. -/
theorem checked_leaf {ty : UScalarTy} {o : AOp} {f : String} (hf : checkedAt? f = some (ty, o))
    (x y : Int) :
    runtimeBuiltins base f [.int x, .int y] = o.checkedRt ty.numBits x y := by
  rcases checkedAt?_spec hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases ty <;>
    simp only [uTag, String.reduceAppend, AOp.checkedRt]
  all_goals first
    | exact runtimeBuiltins_addAt base (by first | decide | rfl) x y
    | exact runtimeBuiltins_subAt base (by first | decide | rfl) x y
    | exact runtimeBuiltins_mulAt base (by first | decide | rfl) x y

/-- `cast#w` is read by the runtime at the width of its tag. -/
theorem cast_leaf {ty : UScalarTy} (x : Int) :
    runtimeBuiltins base ("cast#" ++ uTag ty) [.int x] =
      some (.int (Hax.castVal_w ty.numBits x)) := by
  cases ty <;> simp only [uTag, String.reduceAppend] <;>
    exact cast_w rfl (by first | decide | rfl) x

/-- An untagged checked operation name is read by the runtime as the integer operation. -/
theorem AOp.leaf {o : AOp} {f : String} (hf : AOp.ofName f = some o) (x y : Int) :
    runtimeBuiltins base f [.int x, .int y] = some (.int (o.rt x y)) := by
  unfold AOp.ofName at hf
  (repeat' split at hf) <;> cases hf <;> subst f
  · exact Add_int x y
  · exact Sub_int x y
  · exact Mul_int x y
  · exact Div_int x y
  · exact Rem_int x y

theorem index_leaf (vs : List Hax.Value) (i : Int) :
    runtimeBuiltins base "index" [.array vs, .int i] = some (indexVals vs i) := by
  rw [runtimeBuiltins_of_lookup (g := indexLeaf) rfl]; unfold indexLeaf; rfl

theorem array_update_leaf (vs : List Hax.Value) (i : Int) (v : Hax.Value) :
    runtimeBuiltins base "array_update" [.array vs, .int i, v] =
      some (.array (if i.toNat < vs.length then vs.set i.toNat v else vs)) := by
  rw [runtimeBuiltins_of_lookup (g := arrayUpdateLeaf) rfl]; unfold arrayUpdateLeaf; rfl

theorem repeat_leaf (v : Hax.Value) (n : Int) :
    runtimeBuiltins base "repeat" [v, .int n] = some (.array (List.replicate n.toNat v)) := by
  rw [runtimeBuiltins_of_lookup (g := repeatLeaf) rfl]; unfold repeatLeaf; rfl

theorem len_leaf (vs : List Hax.Value) :
    runtimeBuiltins base "len" [.array vs] = some (.int vs.length) := by
  rw [runtimeBuiltins_of_lookup (g := lenLeaf) rfl]; unfold lenLeaf; rfl

theorem arrayLit_leaf (vs : List Hax.Value) :
    runtimeBuiltins base "array_lit" vs = some (.array vs) := by
  rw [runtimeBuiltins_of_lookup (g := arrayLitLeaf) rfl]; unfold arrayLitLeaf; rfl

end Leaves

/-! ## The squares of the runtime operations -/

theorem appWord_ok {ty : UScalarTy} {o : WordOp} {a b r : AVal} (h : appWord ty o a b = .ok r) :
    ∃ x y : UScalar ty, a.toValue = .int (enc x) ∧ b.toValue = .int (enc y) ∧
      r.toValue = .int (o.rt ty.numBits (enc x) (enc y)) := by
  unfold appWord at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  obtain ⟨y, hy, h⟩ := rustM_bind_ok h
  obtain ⟨r', hr', h⟩ := rustM_bind_ok h
  cases h
  refine ⟨x, y, AVal.asW_ok hx, AVal.asW_ok hy, ?_⟩
  show Hax.Value.int (enc r') = _
  rw [rcompOk_iff.mp (WordOp.square o x y) r' hr']

/-- **The square of a checked width-tagged operation**: a value of `appChecked` at an
    operation of `checkedAt?` is the value of the checked operation of `u<w>` on the
    operands. -/
theorem appChecked_ok {ty : UScalarTy} {o : AOp} {f : String} (hf : checkedAt? f = some (ty, o))
    {a b r : AVal} (h : appChecked ty o a b = .ok r) :
    ∃ x y : UScalar ty, a.toValue = .int (enc x) ∧ b.toValue = .int (enc y) ∧
      o.checkedRt ty.numBits (enc x) (enc y) = some r.toValue := by
  unfold appChecked at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  obtain ⟨y, hy, h⟩ := rustM_bind_ok h
  obtain ⟨z, hz, h⟩ := rustM_bind_ok h
  cases h
  refine ⟨x, y, AVal.asW_ok hx, AVal.asW_ok hy, ?_⟩
  have hsq := rcompOk_iff.mp (AOp.square o x y) z hz
  have hzb := z.bv.isLt
  have hxb := x.bv.isLt
  have hyb := y.bv.isLt
  show _ = some (Hax.Value.int (enc z))
  have h2 : ((2 : Int) ^ ty.numBits) = ((2 ^ ty.numBits : Nat) : Int) := by push_cast; rfl
  rcases checkedAt?_spec hf with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    simp only [AOp.checkedRt, Hax.uintAddOp, Hax.uintSubOp, Hax.uintMulOp] <;>
    simp only [AOp.rt, Hax.add, Hax.sub, Hax.mul, EncRel, enc_uscalar, UScalar.val] at hsq <;>
    rw [ite_eq_left (by simp only [enc_uscalar, UScalar.val, h2]; omega)] <;>
    simp only [enc_uscalar, UScalar.val, hsq]

/-- **The square of `wrapping_neg#w`**. -/
theorem appNeg_ok {ty : UScalarTy} {a r : AVal} (h : appNeg ty a = .ok r) :
    ∃ x : UScalar ty, a.toValue = .int (enc x) ∧
      r.toValue = .int (Hax.wrapping_neg_w ty.numBits (enc x)) := by
  unfold appNeg at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  cases h
  refine ⟨x, AVal.asW_ok hx, ?_⟩
  show Hax.Value.int (((-x.bv).toNat : Nat) : Int) = _
  have hxb := x.bv.isLt
  simp only [Hax.wrapping_neg_w, Hax.mod2w, BitVec.toNat_neg, enc_uscalar, UScalar.val]
  rw [show ((2 : Int) ^ ty.numBits) = ((2 ^ ty.numBits : Nat) : Int) by push_cast; rfl]
  congr 3
  omega

/-- **The square of a field head with one argument**: a value of `appField1` at the method and
    modulus of a field head is the value the runtime table gives the head on the operand. -/
theorem appField1_rt (base : Hax.Builtins) {f : String} {m : Hax.FieldTag.FieldMethod} {p : Nat}
    (hf : Hax.FieldTag.fieldTag? f = some (m, p)) {a r : AVal} (h : appField1 m p a = .ok r) :
    Hax.Ascent.runtimeBuiltins base f (AVal.toValues [a]) = some r.toValue := by
  unfold appField1 at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  split at h
  · rename_i hc
    obtain ⟨hp, hm, hxp⟩ := hc
    cases h
    rw [show AVal.toValues [a] = [.int (enc x)] from by
      simp only [AVal.toValues, AVal.asW_ok hx],
      Hax.Ascent.runtimeBuiltins_of_fieldTag? base hf]
    have hv := Hax.FieldTag.fieldVal_lt m (Nat.zero_lt_of_lt hxp) x.val 0
    simp [Hax.FieldTag.fieldCall, Hax.FieldTag.fieldArm, enc_uscalar, AVal.toValue, hm, hp, hxp]
    show (_ : Int) = ((BitVec.ofNat 64 _).toNat : Int)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · cases h

/-- **The square of a field head with two arguments**: a value of `appField2` at the method and
    modulus of a field head is the value the runtime table gives the head on the operands. -/
theorem appField2_rt (base : Hax.Builtins) {f : String} {m : Hax.FieldTag.FieldMethod}
    {p : Nat} (hf : Hax.FieldTag.fieldTag? f = some (m, p)) {a b r : AVal}
    (h : appField2 m p a b = .ok r) :
    Hax.Ascent.runtimeBuiltins base f (AVal.toValues [a, b]) = some r.toValue := by
  unfold appField2 at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  obtain ⟨y, hy, h⟩ := rustM_bind_ok h
  split at h
  · rename_i hc
    obtain ⟨hp, hm, hxp, hyp⟩ := hc
    cases h
    rw [show AVal.toValues [a, b] = [.int (enc x), .int (enc y)] from by
      simp only [AVal.toValues, AVal.asW_ok hx, AVal.asW_ok hy],
      Hax.Ascent.runtimeBuiltins_of_fieldTag? base hf]
    have hv := Hax.FieldTag.fieldVal_lt m (Nat.zero_lt_of_lt hxp) x.val y.val
    simp [Hax.FieldTag.fieldCall, Hax.FieldTag.fieldArm, enc_uscalar, AVal.toValue, hm, hp, hxp,
      hyp]
    show (_ : Int) = ((BitVec.ofNat 64 _).toNat : Int)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · cases h

/-- An untagged checked operation returns no value on two integer literals. -/
theorem appArith_int_int (o : AOp) (n m : Int) :
    appArith o (.int n) (.int m) = .fail .undef := rfl

/-- A value of an untagged checked operation is a word: the value of the Aeneas operation
    at one width on two words of that width, which the operands encode. -/
theorem appArith_word {o : AOp} {a b r : AVal} (h : appArith o a b = .ok r) :
    ∃ (ty : UScalarTy) (x y z : UScalar ty), a.toValue = .int (enc x) ∧
      b.toValue = .int (enc y) ∧ o.aen x y = .ok z ∧ r = .w ty z := by
  cases a with
  | int n =>
    cases b with
    | w ty y =>
      simp only [appArith] at h
      obtain ⟨x, hx, h⟩ := rustM_bind_ok h
      obtain ⟨r', hr', h⟩ := rustM_bind_ok h
      cases h
      exact ⟨ty, x, y, r', by rw [AVal.toValue, litA_ok hx], rfl, hr', rfl⟩
    | _ => simp [appArith] at h
  | w ty x =>
    simp only [appArith] at h
    obtain ⟨y, hy, h⟩ := rustM_bind_ok h
    obtain ⟨r', hr', h⟩ := rustM_bind_ok h
    cases h
    exact ⟨ty, x, y, r', rfl, AVal.asW_ok hy, hr', rfl⟩
  | _ => simp [appArith] at h

theorem appArith_ok {o : AOp} {a b r : AVal} (h : appArith o a b = .ok r) :
    ∃ x y : Int, a.toValue = .int x ∧ b.toValue = .int y ∧ r.toValue = .int (o.rt x y) := by
  obtain ⟨ty, x, y, z, ha, hb, hz, rfl⟩ := appArith_word h
  refine ⟨enc x, enc y, ha, hb, ?_⟩
  show Hax.Value.int (enc z) = _
  rw [rcompOk_iff.mp (AOp.square o x y) z hz]

theorem appIndex_ok {a i r : AVal} (h : appIndex a i = .ok r) :
    ∃ vs j, a.toValue = .array vs ∧ i.toValue = .int j ∧
      r.toValue = Hax.Ascent.indexVals vs j := by
  cases a with
  | arr ty n arr =>
    simp only [appIndex] at h
    obtain ⟨j, hj, h⟩ := rustM_bind_ok h
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    cases h
    refine ⟨_, enc j, rfl, AVal.asW_ok hj, ?_⟩
    unfold Aeneas.Std.Array.index_usize at hx
    rw [Aeneas.Std.Array.getElem?_Usize_eq] at hx
    split at hx
    · cases hx
    · rename_i y hy
      cases hx
      simp [Hax.Ascent.indexVals, enc_uscalar, hy, AVal.toValue]
  | _ => simp [appIndex] at h

theorem appUpdate_ok {a i v r : AVal} (h : appUpdate a i v = .ok r) :
    ∃ vs j, a.toValue = .array vs ∧ i.toValue = .int j ∧
      r.toValue = .array (if j.toNat < vs.length then vs.set j.toNat v.toValue else vs) := by
  cases a with
  | arr ty n arr =>
    simp only [appUpdate] at h
    obtain ⟨j, hj, h⟩ := rustM_bind_ok h
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    obtain ⟨arr', harr, h⟩ := rustM_bind_ok h
    cases h
    refine ⟨_, enc j, rfl, AVal.asW_ok hj, ?_⟩
    rw [AVal.asW_ok hx]
    unfold Aeneas.Std.Array.update at harr
    rw [Aeneas.Std.Array.getElem?_Usize_eq] at harr
    split at harr
    · cases harr
    · rename_i y hy
      cases harr
      have hlt : j.val < arr.val.length := (List.getElem?_eq_some_iff.mp hy).1
      simp [AVal.toValue, enc_uscalar, hlt, List.map_set]
  | _ => simp [appUpdate] at h

theorem appRepeat_ok {v m r : AVal} (h : appRepeat v m = .ok r) :
    ∃ n, m.toValue = .int n ∧ r.toValue = .array (List.replicate n.toNat v.toValue) := by
  cases v with
  | w ty x =>
    simp only [appRepeat] at h
    obtain ⟨k, hk, h⟩ := rustM_bind_ok h
    cases h
    refine ⟨enc k, AVal.asW_ok hk, ?_⟩
    simp [AVal.toValue, enc_uscalar, List.map_replicate]
  | _ => simp [appRepeat] at h

theorem appLen_ok {a r : AVal} (h : appLen a = .ok r) :
    ∃ vs, a.toValue = .array vs ∧ r.toValue = .int vs.length := by
  cases a with
  | arr ty n arr =>
    simp only [appLen] at h
    cases h
    exact ⟨_, rfl, by simp [AVal.toValue]⟩
  | _ => simp [appLen] at h

theorem AVal.asWList_ok {ty : UScalarTy} (vs : List AVal) {xs : List (UScalar ty)}
    (h : AVal.asWList ty vs = .ok xs) :
    AVal.toValues vs = xs.map fun x => .int (x.val : Int) := by
  induction vs generalizing xs with
  | nil =>
    simp only [AVal.asWList] at h
    cases h
    rfl
  | cons a as ih =>
    simp only [AVal.asWList] at h
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    obtain ⟨ys, hys, h⟩ := rustM_bind_ok h
    cases h
    simp [AVal.toValues, AVal.asW_ok hx, ih hys, enc_uscalar]

theorem appArrayLit_ok {vs : List AVal} {r : AVal} (h : appArrayLit vs = .ok r) :
    r.toValue = .array (AVal.toValues vs) := by
  unfold appArrayLit at h
  split at h
  · obtain ⟨xs, hxs, h⟩ := rustM_bind_ok h
    obtain ⟨n, -, h⟩ := rustM_bind_ok h
    split at h
    · cases h
      rw [AVal.asWList_ok _ hxs]
      rfl
    · cases h
  · cases h

/-- **The square of `array_lit`**: `appArrayLit` reads the runtime's `array_lit`. -/
theorem appArrayLit_rt (base : Hax.Builtins) {vs : List AVal} {r : AVal}
    (h : appArrayLit vs = .ok r) :
    Hax.Ascent.runtimeBuiltins base "array_lit" (AVal.toValues vs) = some r.toValue := by
  rw [arrayLit_leaf, appArrayLit_ok h]

/-- **The square of `Not` on a Boolean**: the negation `appBNot` reads the runtime's `Not`. -/
theorem appBNot_ok (base : Hax.Builtins) {a r : AVal} (h : appBNot a = .ok r) :
    Hax.Ascent.runtimeBuiltins base "Not" [a.toValue] = some r.toValue := by
  cases a with
  | bool x =>
    cases h
    exact Hax.Ascent.RuntimeOps.Not_bool x
  | _ => cases h

/-- **The square of `declassify`**: on the value `appDeclassify` returns, the identity leaf
    of the runtime returns the same value; the argument is a word. -/
theorem appDeclassify_ok {a r : AVal} (h : appDeclassify a = .ok r) :
    r = a ∧ (∃ ty x, a = .w ty x) ∧ Hax.Ascent.identLeaf [a.toValue] = some r.toValue := by
  cases a with
  | w ty x =>
    cases h
    exact ⟨rfl, ⟨ty, x, rfl⟩, by simp only [Hax.Ascent.identLeaf]⟩
  | _ => cases h

/-- **The squares of the Boolean connectives and the comparisons**: `appBool2` reads the
    runtime's `&&`, `||`, `Eq` and `Ne` on two Booleans and `Lt`, `Le`, `Gt`, `Ge`, `Eq` and
    `Ne` on two integers. -/
theorem appBool2_ok (base : Hax.Builtins) {f : String} {a b r : AVal}
    (h : appBool2 f a b = .ok r) :
    Hax.Ascent.runtimeBuiltins base f [a.toValue, b.toValue] = some r.toValue := by
  unfold appBool2 at h
  split at h
  · rename_i x y
    split at h
    · rename_i g hg
      cases h
      unfold boolRt? at hg
      split at hg <;> cases hg
      · exact Hax.Ascent.RuntimeOps.and_bool x y
      · exact Hax.Ascent.RuntimeOps.or_bool x y
      · exact Hax.Ascent.RuntimeOps.Eq_bool x y
      · exact Hax.Ascent.RuntimeOps.Ne_bool x y
    · cases h
  · split at h
    · rename_i g x y hg hx hy
      cases h
      rw [AVal.toValue_of_toInt? hx, AVal.toValue_of_toInt? hy]
      unfold cmpRt? at hg
      split at hg <;> cases hg
      · exact Hax.Ascent.RuntimeOps.Lt_int x y
      · exact Hax.Ascent.RuntimeOps.Le_int x y
      · exact Hax.Ascent.RuntimeOps.Gt_int x y
      · exact Hax.Ascent.RuntimeOps.Ge_int x y
      · exact Hax.Ascent.RuntimeOps.Eq_int x y
      · exact Hax.Ascent.RuntimeOps.Ne_int x y
    · cases h

/-- **The runtime operations are read by `appRt`**: `appRt` agrees with the runtime table
    over any base table. -/
theorem appRt_ok (base : Hax.Builtins) : AppOk (Hax.Ascent.runtimeBuiltins base) appRt := by
  intro f vs r h
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · rw [show appRt f [] = if f = "array_lit" then appArrayLit [] else .fail .undef from rfl]
      at h
    by_cases hal : f = "array_lit"
    · rw [ite_eq_left hal] at h
      subst hal
      exact appArrayLit_rt base h
    · rw [ite_eq_right hal] at h
      cases h
  · simp only [appRt] at h
    split at h
    · rename_i ty hty
      rw [tagTyAt?_spec hty]
      unfold appNot at h
      obtain ⟨x, hx, h⟩ := rustM_bind_ok h
      cases h
      show _ = some (Hax.Value.int (enc (~~~x)))
      rw [show AVal.toValues [a] = [.int (enc x)] from by
        rw [AVal.toValues, AVal.toValues, AVal.asW_ok hx], not_leaf,
        rcompOk_iff.mp (bitnot_w_u_square x) _ rfl]
    · split at h
      · rename_i ty hty
        rw [tagTyAt?_spec hty]
        unfold appCast at h
        split at h
        · rename_i ty' x
          cases h
          show _ = some (Hax.Value.int (enc (UScalar.cast ty x)))
          rw [show AVal.toValues [AVal.w ty' x] = [.int (enc x)] from rfl, cast_leaf,
            rcompOk_lift.mp (cast_u_square ty x)]
        · cases h
      · split at h
        · rename_i ty hty
          rw [tagTyAt?_spec hty]
          obtain ⟨x, hx, hr⟩ := appNeg_ok h
          rw [show AVal.toValues [a] = [.int (enc x)] from by
            simp only [AVal.toValues, hx], neg_leaf, hr]
        · by_cases hi : f = "range_incl_end"
          · rw [ite_eq_left hi] at h
            subst hi
            split at h
            · rename_i k hk
              cases h
              rw [show AVal.toValues [a] = [.int k] from by
                rw [AVal.toValues, AVal.toValues, AVal.toValue_of_toInt? hk],
                Hax.Ascent.RuntimeOps.range_incl_end_int]
              rfl
            · cases h
          · rw [ite_eq_right hi] at h
            by_cases hn : f = "Not"
            · rw [ite_eq_left hn] at h
              subst hn
              exact appBNot_ok base h
            · rw [ite_eq_right hn] at h
              by_cases hl : f = "len"
              · rw [ite_eq_left hl] at h
                subst hl
                obtain ⟨vs, ha, hr⟩ := appLen_ok h
                rw [show AVal.toValues [a] = [.array vs] from by simp only [AVal.toValues, ha],
                  len_leaf, hr]
              · rw [ite_eq_right hl] at h
                by_cases hal : f = "array_lit"
                · rw [ite_eq_left hal] at h
                  subst hal
                  exact appArrayLit_rt base h
                · rw [ite_eq_right hal] at h
                  by_cases hd : f = "declassify"
                  · rw [ite_eq_left hd] at h
                    subst hd
                    obtain ⟨rfl, -, -⟩ := appDeclassify_ok h
                    exact Hax.Ascent.runtimeBuiltins_declassify base _
                  · rw [ite_eq_right hd] at h
                    split at h
                    · rename_i m p hf
                      exact appField1_rt base hf h
                    · cases h
  · simp only [appRt] at h
    split at h
    · rename_i ty o ho
      obtain ⟨x, y, hx, hy, hr⟩ := appWord_ok h
      rw [show AVal.toValues [a, b] = [.int (enc x), .int (enc y)] from by
        simp only [AVal.toValues, hx, hy], hr]
      exact WordOp.leaf (wordOpAt?_spec ho) _ _
    · split at h
      · rename_i ty o ho
        obtain ⟨x, y, hx, hy, hr⟩ := appChecked_ok ho h
        rw [show AVal.toValues [a, b] = [.int (enc x), .int (enc y)] from by
          simp only [AVal.toValues, hx, hy], checked_leaf ho, hr]
      · split at h
        · rename_i o ho
          obtain ⟨x, y, hx, hy, hr⟩ := appArith_ok h
          rw [show AVal.toValues [a, b] = [.int x, .int y] from by
            simp only [AVal.toValues, hx, hy], hr]
          exact AOp.leaf ho _ _
        · by_cases hi : f = "index"
          · rw [ite_eq_left hi] at h
            subst hi
            obtain ⟨vs, j, ha, hb, hr⟩ := appIndex_ok h
            rw [show AVal.toValues [a, b] = [.array vs, .int j] from by
              simp only [AVal.toValues, ha, hb], index_leaf, hr]
          · rw [ite_eq_right hi] at h
            by_cases hrep : f = "repeat"
            · rw [ite_eq_left hrep] at h
              subst hrep
              obtain ⟨n, hb, hr⟩ := appRepeat_ok h
              rw [show AVal.toValues [a, b] = [a.toValue, .int n] from by
                simp only [AVal.toValues, hb], repeat_leaf, hr]
            · rw [ite_eq_right hrep] at h
              by_cases hal : f = "array_lit"
              · rw [ite_eq_left hal] at h
                subst hal
                exact appArrayLit_rt base h
              · rw [ite_eq_right hal] at h
                split at h
                · rename_i m p hf
                  exact appField2_rt base hf h
                · exact appBool2_ok base h
  · simp only [appRt] at h
    by_cases hu : f = "array_update"
    · rw [ite_eq_left hu] at h
      subst hu
      obtain ⟨vs, j, ha, hb, hr⟩ := appUpdate_ok h
      rw [show AVal.toValues [a, b, c] = [.array vs, .int j, c.toValue] from by
        simp only [AVal.toValues, ha, hb], array_update_leaf, hr]
    · rw [ite_eq_right hu] at h
      by_cases hal : f = "array_lit"
      · rw [ite_eq_left hal] at h
        subst hal
        exact appArrayLit_rt base h
      · rw [ite_eq_right hal] at h
        cases h
  · rw [show appRt f (a :: b :: c :: d :: rest) =
      if f = "array_lit" then appArrayLit (a :: b :: c :: d :: rest) else .fail .undef
      from rfl] at h
    by_cases hal : f = "array_lit"
    · rw [ite_eq_left hal] at h
      subst hal
      exact appArrayLit_rt base h
    · rw [ite_eq_right hal] at h
      cases h

/-- A checked width-tagged name is no tagged binary word operation name. -/
theorem wordOpAt?_of_checkedAt? {f : String} {ty : UScalarTy} {o : AOp}
    (h : checkedAt? f = some (ty, o)) : wordOpAt? f = none := by
  rcases checkedAt?_spec h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases ty <;> decide

/-- **A checked width-tagged name on two words of its width** is the Aeneas checked
    operation at that width. -/
theorem appRt_checkedAt {f : String} {ty : UScalarTy} {o : AOp}
    (h : checkedAt? f = some (ty, o)) (x y : UScalar ty) :
    appRt f [.w ty x, .w ty y] = o.aen x y >>= fun z => .ok (.w ty z) := by
  simp only [appRt, wordOpAt?_of_checkedAt? h, h, appChecked]
  simp [AVal.asW]

/-- `wrapping_neg#t` on a word of the width of its tag is its two's complement negation (an
    unfolding lemma of `appRt`). -/
theorem appRt_negAt (ty : UScalarTy) (x : UScalar ty) :
    appRt ("wrapping_neg#" ++ uTag ty) [.w ty x] = .ok (.w ty ⟨-x.bv⟩) := by
  cases ty <;> rfl

/-- `declassify` on a word is the word (an unfolding lemma of `appRt`). -/
theorem appRt_declassify {ty : UScalarTy} (x : UScalar ty) :
    appRt "declassify" [.w ty x] = .ok (.w ty x) := by
  rfl

/-- The field head `mul#p7` on the `u64` words `3` and `5` is the word `3 * 5 mod 7 = 1`. -/
theorem appRt_mul_p7 :
    appRt "mul#p7" [.w .U64 ⟨BitVec.ofNat 64 3⟩, .w .U64 ⟨BitVec.ofNat 64 5⟩] =
      .ok (.w .U64 ⟨BitVec.ofNat 64 1⟩) := by
  rfl

/-! ## The reading -/

/-- `step` run on `k` successive indices from `i`. -/
def loopS (step : Nat → AEnv → RustM AEnv) : Nat → Nat → AEnv → RustM AEnv
  | 0, _, ρ => .ok ρ
  | k + 1, i, ρ => step i ρ >>= loopS step k (i + 1)

/-- `step` run on `k` successive indices downwards, from `i + k - 1` to `i`. -/
def loopRevS (step : Nat → AEnv → RustM AEnv) : Nat → Nat → AEnv → RustM AEnv
  | 0, _, ρ => .ok ρ
  | k + 1, i, ρ => step (i + k) ρ >>= loopRevS step k i

/-- The loop index `i`, a `usize` word. -/
def ctr (i : Nat) : AVal := .w .Usize ⟨BitVec.ofNat _ i⟩

/-- **The state-passing `RustM` reading of a literal.** -/
def toRustMS (app : String → List AVal → RustM AVal) :
    Hax.ImpExpr → AEnv → RustM (AVal × AEnv)
  | .lit (.int n), ρ => .ok (.int n, ρ)
  | .lit (.bool b), ρ => .ok (.bool b, ρ)
  | .var x, ρ => match ρ x with
    | some v => .ok (v, ρ)
    | none => .fail .undef
  | .letBind x v b, ρ =>
    toRustMS app v ρ >>= fun p => toRustMS app b (p.2.upd x p.1)
  | .unitVal, ρ => .ok (.unit, ρ)
  | .seq a b, ρ => toRustMS app a ρ >>= fun p => toRustMS app b p.2
  | .typeAscription e _, ρ => toRustMS app e ρ
  | .app f [a], ρ =>
    toRustMS app a ρ >>= fun p => app f [p.1] >>= fun r => .ok (r, p.2)
  | .app f [a, b], ρ =>
    toRustMS app a ρ >>= fun p => toRustMS app b p.2 >>= fun q =>
      app f [p.1, q.1] >>= fun r => .ok (r, q.2)
  | .app f [a, b, c], ρ =>
    toRustMS app a ρ >>= fun p => toRustMS app b p.2 >>= fun q =>
      toRustMS app c q.2 >>= fun s => app f [p.1, q.1, s.1] >>= fun r => .ok (r, s.2)
  | .tuple es, ρ => toRustMS.argsS app es ρ >>= fun p => .ok (.tup p.1, p.2)
  | .ifThenElse c t e, ρ =>
    toRustMS app c ρ >>= fun p => match p.1 with
      | .bool true => toRustMS app t p.2
      | .bool false => toRustMS app e p.2
      | _ => .fail .undef
  | .forFold var lo hi body, ρ =>
    toRustMS app lo ρ >>= fun p => toRustMS app hi p.2 >>= fun q =>
      match p.1.toInt?, q.1.toInt? with
      | some a, some b =>
        if 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits then
          loopS (fun i ρ => toRustMS app body (ρ.upd var (ctr i)) >>= fun s => .ok s.2)
            (b - a).toNat a.toNat q.2 >>= fun ρ3 => .ok (.unit, ρ3)
        else .fail .undef
      | _, _ => .fail .undef
  | .forFoldRev var lo hi body, ρ =>
    toRustMS app lo ρ >>= fun p => toRustMS app hi p.2 >>= fun q =>
      match p.1.toInt?, q.1.toInt? with
      | some a, some b =>
        if 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits then
          loopRevS (fun i ρ => toRustMS app body (ρ.upd var (ctr i)) >>= fun s => .ok s.2)
            (b - a).toNat a.toNat q.2 >>= fun ρ3 => .ok (.unit, ρ3)
        else .fail .undef
      | _, _ => .fail .undef
  | .proj e i, ρ =>
    toRustMS app e ρ >>= fun p => match p.1 with
      | .tup vs => match vs[i]? with
        | some v => .ok (v, p.2)
        | none => .fail .undef
      | _ => .fail .undef
  | .app f args, ρ =>
    toRustMS.argsS app args ρ >>= fun p => app f p.1 >>= fun r => .ok (r, p.2)
  | _, _ => .fail .undef
where
  /-- The arguments of a call read left to right: their values and the environment after
      the last of them. -/
  argsS (app : String → List AVal → RustM AVal) :
      List Hax.ImpExpr → AEnv → RustM (List AVal × AEnv)
    | [], ρ => .ok ([], ρ)
    | a :: as, ρ => toRustMS app a ρ >>= fun p => argsS app as p.2 >>= fun q =>
      .ok (p.1 :: q.1, q.2)

/-! ## Pasting -/

/-- The run of `e` from the encoding of `ρ` returns the encoding of `v` and ends in the
    encoding of `ρ'`, at every fuel from some fuel on. -/
def Sim (bi : Hax.Builtins) (e : Hax.ImpExpr) (ρ ρ' : AEnv) (v : AVal) : Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
    Hax.denote' bi fuel e (encEnv ρ) = (.val v.toValue, encEnv ρ')

theorem ctr_toValue {i : Nat} (h : i < 2 ^ UScalarTy.Usize.numBits) :
    (ctr i).toValue = .int i := by
  simp only [ctr, AVal.toValue, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **The loop square.** `k` steps of the reading from the index `i`, each a run of the
    body from the environment with the index bound, are the counted loop of the runtime
    from `i` to `b`. -/
theorem loopS_sim {bi : Hax.Builtins} {var : String} {body : Hax.ImpExpr}
    {step : Nat → AEnv → RustM AEnv}
    (hstep : ∀ i ρ ρ', step i ρ = .ok ρ' → ∃ v, Sim bi body (ρ.upd var (ctr i)) ρ' v) :
    ∀ (k i : Nat) (b : Int) (ρ ρ' : AEnv), (b - i).toNat = k →
      b ≤ 2 ^ UScalarTy.Usize.numBits → loopS step k i ρ = .ok ρ' →
      ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
        Hax.denoteForLoop' bi fuel var i b body (encEnv ρ) = (.val .unit, encEnv ρ')
  | 0, i, b, ρ, ρ', hk, _, h => by
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denoteForLoop'_done bi fuel var body _ (by omega)⟩
  | k + 1, i, b, ρ, ρ', hk, hb, h => by
    obtain ⟨ρ1, h1, h2⟩ := rustM_bind_ok h
    obtain ⟨v, F1, hF1⟩ := hstep i ρ ρ1 h1
    obtain ⟨F2, hF2⟩ := loopS_sim hstep k (i + 1) b ρ1 ρ' (by omega) hb h2
    refine ⟨max F1 (F2 + 1), fun fuel hf => ?_⟩
    have hi' : (i : Int) < 2 ^ UScalarTy.Usize.numBits := by omega
    have hi : i < 2 ^ UScalarTy.Usize.numBits := by exact_mod_cast hi'
    have hbody := hF1 fuel (by omega)
    rw [encEnv_upd, ctr_toValue hi] at hbody
    rw [Hax.Ascent.denoteForLoop'_next bi fuel var (by omega) (by omega) hbody
      (AVal.toValue_ne_break v)]
    have h3 := hF2 (fuel - 1) (by omega)
    rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by push_cast; rfl] at h3
    exact h3

section RevLoop

variable (bi : Hax.Builtins) (fuel : Nat)

theorem denote'_forFoldRev {var : String} {lo hi body : Hax.ImpExpr} {env s1 s2 : Hax.Env}
    {a b : Int} (hlo : Hax.denote' bi fuel lo env = (.val (.int a), s1))
    (hhi : Hax.denote' bi fuel hi s1 = (.val (.int b), s2)) :
    Hax.denote' bi fuel (.forFoldRev var lo hi body) env =
      Hax.denoteForLoopRev' bi fuel var a b body s2 := by
  simp only [Hax.denote', Hax.Ascent.stateM_bind_apply, hlo, hhi]

end RevLoop

/-- **The reverse loop square.** `k` steps of the reading downwards from the index
    `i + k - 1` to `i`, each a run of the body from the environment with the index bound,
    are the reverse counted loop of the runtime over `[i, b)`. -/
theorem loopRevS_sim {bi : Hax.Builtins} {var : String} {body : Hax.ImpExpr}
    {step : Nat → AEnv → RustM AEnv}
    (hstep : ∀ i ρ ρ', step i ρ = .ok ρ' → ∃ v, Sim bi body (ρ.upd var (ctr i)) ρ' v) :
    ∀ (k i : Nat) (b : Int) (ρ ρ' : AEnv), (b - i).toNat = k →
      b ≤ 2 ^ UScalarTy.Usize.numBits → loopRevS step k i ρ = .ok ρ' →
      ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
        Hax.denoteForLoopRev' bi fuel var i b body (encEnv ρ) = (.val .unit, encEnv ρ')
  | 0, i, b, ρ, ρ', hk, _, h => by
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denoteForLoopRev'_done bi fuel var body _ (by omega)⟩
  | k + 1, i, b, ρ, ρ', hk, hb, h => by
    obtain ⟨ρ1, h1, h2⟩ := rustM_bind_ok h
    obtain ⟨v, F1, hF1⟩ := hstep (i + k) ρ ρ1 h1
    obtain ⟨F2, hF2⟩ := loopRevS_sim hstep k i (b - 1) ρ1 ρ' (by omega) (by omega) h2
    refine ⟨max F1 (F2 + 1), fun fuel hf => ?_⟩
    have hik : ((i + k : Nat) : Int) = b - 1 := by omega
    have hi' : ((i + k : Nat) : Int) < 2 ^ UScalarTy.Usize.numBits := by omega
    have hi : i + k < 2 ^ UScalarTy.Usize.numBits := by exact_mod_cast hi'
    have hbody := hF1 fuel (by omega)
    rw [encEnv_upd, ctr_toValue hi, hik] at hbody
    rw [Hax.Ascent.denoteForLoopRev'_next bi fuel var (by omega) (by omega) hbody
      (AVal.toValue_ne_break v)]
    exact hF2 (fuel - 1) (by omega)

/-- The run of the arguments `args` from the encoding of `ρ` returns the encodings of `vs`
    and ends in the encoding of `ρ'`, at every fuel from some fuel on. -/
def SimArgs (bi : Hax.Builtins) (args : List Hax.ImpExpr) (ρ ρ' : AEnv) (vs : List AVal) :
    Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
    Hax.denoteArgs' bi fuel args (encEnv ρ) = (some (AVal.toValues vs), encEnv ρ')

/-- Every value and environment that the computation `r` returns are simulated by the run
    of `e` from `ρ`. -/
def SimOk (bi : Hax.Builtins) (e : Hax.ImpExpr) (ρ : AEnv) (r : RustM (AVal × AEnv)) :
    Prop :=
  ∀ v ρ', r = .ok (v, ρ') → Sim bi e ρ ρ' v

/-- Every list of values and environment that the computation `r` returns are simulated by
    the run of the arguments `args` from `ρ`. -/
def SimArgsOk (bi : Hax.Builtins) (args : List Hax.ImpExpr) (ρ : AEnv)
    (r : RustM (List AVal × AEnv)) : Prop :=
  ∀ vs ρ', r = .ok (vs, ρ') → SimArgs bi args ρ ρ' vs

theorem toRustMS_sim {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) (e : Hax.ImpExpr) (ρ : AEnv) :
    ∀ v ρ', toRustMS app e ρ = .ok (v, ρ') → Sim bi e ρ ρ' v := by
  suffices H : ∀ e ρ, SimOk bi e ρ (toRustMS app e ρ) from H e ρ
  apply toRustMS.induct_unfolding app (SimArgsOk bi) (SimOk bi)
  all_goals intros
  case case1 n ρ =>
    intro v ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denote'_lit bi fuel _ _⟩
  case case2 b ρ =>
    intro v ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denote'_lit bi fuel _ _⟩
  case case3 x ρ w hx =>
    intro v ρ' h
    cases h
    refine ⟨0, fun fuel _ => Hax.Ascent.denote'_var bi fuel ?_⟩
    show (ρ x).map AVal.toValue = _
    rw [hx]
    rfl
  case case4 =>
    intro v ρ' h
    cases h
  case case5 x a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, hb⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih2 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih1 p v ρ' hb
    refine ⟨max F1 F2, fun fuel hf => ?_⟩
    rw [Hax.Ascent.denote'_letBind bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _),
      ← encEnv_upd]
    exact h2 fuel (by omega)
  case case6 ρ =>
    intro v ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denote'_unitVal bi fuel _⟩
  case case7 a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, hb⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih2 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih1 p v ρ' hb
    refine ⟨max F1 F2, fun fuel hf => ?_⟩
    rw [Hax.Ascent.denote'_seq bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _)]
    exact h2 fuel (by omega)
  case case8 a s ρ ih1 =>
    intro v ρ' h
    obtain ⟨F1, h1⟩ := ih1 v ρ' h
    exact ⟨F1, fun fuel hf => by
      rw [Hax.Ascent.denote'_typeAscription]; exact h1 fuel hf⟩
  case case9 f a ρ ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F1, h1⟩ := ih1 p.1 p.2 hp
    refine ⟨F1, fun fuel hf => ?_⟩
    exact Hax.Ascent.denote'_app bi fuel
      (Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel hf) (AVal.toValue_isControlFlow _)
        (Hax.Ascent.denoteArgs'_nil bi fuel _)) (happ f [p.1] _ hr)
  case case10 f a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F1, h1⟩ := ih2 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih1 p q.1 q.2 hq
    refine ⟨max F1 F2, fun fuel hf => ?_⟩
    exact Hax.Ascent.denote'_app bi fuel
      (Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _)
        (Hax.Ascent.denoteArgs'_cons bi fuel (h2 fuel (by omega))
          (AVal.toValue_isControlFlow _) (Hax.Ascent.denoteArgs'_nil bi fuel _)))
      (happ f [p.1, q.1] _ hr)
  case case11 f a b c ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨s, hs, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F1, h1⟩ := ih3 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih2 p q.1 q.2 hq
    obtain ⟨F3, h3⟩ := ih1 q s.1 s.2 hs
    refine ⟨max F1 (max F2 F3), fun fuel hf => ?_⟩
    exact Hax.Ascent.denote'_app bi fuel
      (Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _)
        (Hax.Ascent.denoteArgs'_cons bi fuel (h2 fuel (by omega))
          (AVal.toValue_isControlFlow _)
          (Hax.Ascent.denoteArgs'_cons bi fuel (h3 fuel (by omega))
            (AVal.toValue_isControlFlow _) (Hax.Ascent.denoteArgs'_nil bi fuel _))))
      (happ f [p.1, q.1, s.1] _ hr)
  case case12 es ρ ih =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F, hF⟩ := ih p.1 p.2 hp
    exact ⟨F, fun fuel hf => Hax.Ascent.denote'_tuple bi fuel (hF fuel hf)⟩
  case case13 c t e ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨⟨cv, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih3 cv ρ1 hp
    cases cv with
    | bool b =>
      cases b with
      | true =>
        obtain ⟨F2, h2⟩ := ih2 (.bool true, ρ1) v ρ' h
        refine ⟨max F1 F2, fun fuel hf => ?_⟩
        rw [Hax.Ascent.denote'_ifThenElse bi fuel (h1 fuel (by omega))]
        exact h2 fuel (by omega)
      | false =>
        obtain ⟨F2, h2⟩ := ih1 (.bool false, ρ1) v ρ' h
        refine ⟨max F1 F2, fun fuel hf => ?_⟩
        rw [Hax.Ascent.denote'_ifThenElse bi fuel (h1 fuel (by omega))]
        exact h2 fuel (by omega)
    | _ => cases h
  case case14 var lo hi body ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih3 l ρ1 hp
    obtain ⟨F2, h2⟩ := ih2 (l, ρ1) u ρ2 hq
    cases hl : l.toInt? with
    | none => simp only [hl] at h; cases h
    | some a =>
      cases hu : u.toInt? with
      | none => simp only [hl, hu] at h; cases h
      | some b =>
        simp only [hl, hu] at h
        by_cases hab : 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits
        case neg => rw [ite_eq_right hab] at h; cases h
        rw [ite_eq_left hab] at h
        obtain ⟨ρ3, hloop, h⟩ := rustM_bind_ok h
        cases h
        have hstep : ∀ (i : Nat) (ρ ρ' : AEnv), (toRustMS app body (ρ.upd var (ctr i)) >>=
            fun s => RustM.ok s.2) = .ok ρ' → ∃ w, Sim bi body (ρ.upd var (ctr i)) ρ' w := by
          intro i ρ ρ'' hs
          obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
          cases hfin
          exact ⟨s.1, ih1 i ρ s.1 s.2 hs'⟩
        obtain ⟨F3, h3⟩ := loopS_sim hstep (b - a).toNat a.toNat b ρ2 ρ'
          (by rw [Int.toNat_of_nonneg hab.1]) hab.2 hloop
        refine ⟨max F1 (max F2 F3), fun fuel hf => ?_⟩
        have hlo := h1 fuel (by omega)
        have hhi := h2 fuel (by omega)
        rw [AVal.toValue_of_toInt? hl] at hlo
        rw [AVal.toValue_of_toInt? hu] at hhi
        rw [Hax.Ascent.denote'_forFold bi fuel hlo hhi]
        have h4 := h3 fuel (by omega)
        rw [Int.toNat_of_nonneg hab.1] at h4
        exact h4
  case case15 var lo hi body ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨⟨l, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨⟨u, ρ2⟩, hq, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih3 l ρ1 hp
    obtain ⟨F2, h2⟩ := ih2 (l, ρ1) u ρ2 hq
    cases hl : l.toInt? with
    | none => simp only [hl] at h; cases h
    | some a =>
      cases hu : u.toInt? with
      | none => simp only [hl, hu] at h; cases h
      | some b =>
        simp only [hl, hu] at h
        by_cases hab : 0 ≤ a ∧ b ≤ 2 ^ UScalarTy.Usize.numBits
        case neg => rw [ite_eq_right hab] at h; cases h
        rw [ite_eq_left hab] at h
        obtain ⟨ρ3, hloop, h⟩ := rustM_bind_ok h
        cases h
        have hstep : ∀ (i : Nat) (ρ ρ' : AEnv), (toRustMS app body (ρ.upd var (ctr i)) >>=
            fun s => RustM.ok s.2) = .ok ρ' → ∃ w, Sim bi body (ρ.upd var (ctr i)) ρ' w := by
          intro i ρ ρ'' hs
          obtain ⟨s, hs', hfin⟩ := rustM_bind_ok hs
          cases hfin
          exact ⟨s.1, ih1 i ρ s.1 s.2 hs'⟩
        obtain ⟨F3, h3⟩ := loopRevS_sim hstep (b - a).toNat a.toNat b ρ2 ρ'
          (by rw [Int.toNat_of_nonneg hab.1]) hab.2 hloop
        refine ⟨max F1 (max F2 F3), fun fuel hf => ?_⟩
        have hlo := h1 fuel (by omega)
        have hhi := h2 fuel (by omega)
        rw [AVal.toValue_of_toInt? hl] at hlo
        rw [AVal.toValue_of_toInt? hu] at hhi
        rw [denote'_forFoldRev bi fuel hlo hhi]
        have h4 := h3 fuel (by omega)
        rw [Int.toNat_of_nonneg hab.1] at h4
        exact h4
  case case16 e i ρ ih1 =>
    intro v ρ' h
    obtain ⟨⟨t, ρ1⟩, hp, h⟩ := rustM_bind_ok h
    obtain ⟨F1, h1⟩ := ih1 t ρ1 hp
    cases t with
    | tup vs =>
      cases hvi : vs[i]? with
      | none => simp only [hvi] at h; cases h
      | some w =>
        simp only [hvi] at h
        cases h
        refine ⟨F1, fun fuel hf => ?_⟩
        refine Hax.Ascent.denote'_proj bi fuel (h1 fuel hf) (AVal.toValue_isControlFlow _) ?_
        simp only [AVal.toValue, Hax.Value.projIdx, AVal.toValues_eq_map, List.getElem?_map,
          hvi, Option.map_some]
    | _ => cases h
  case case17 f args ρ _ _ _ ih =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨r, hr, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F, hF⟩ := ih p.1 p.2 hp
    exact ⟨F, fun fuel hf => Hax.Ascent.denote'_app bi fuel (hF fuel hf) (happ f p.1 _ hr)⟩
  case case18 =>
    intro v ρ' h
    cases h
  case case19 ρ =>
    intro vs ρ' h
    cases h
    exact ⟨0, fun fuel _ => Hax.Ascent.denoteArgs'_nil bi fuel _⟩
  case case20 a as ρ ih2 ih1 =>
    intro vs ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F1, h1⟩ := ih2 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih1 p q.1 q.2 hq
    exact ⟨max F1 F2, fun fuel hf => Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel (by omega))
      (AVal.toValue_isControlFlow _) (h2 fuel (by omega))⟩

/-- **The reading of a call of any arity.** The arguments are read left to right by
    `toRustMS.argsS`, then `app f` is applied to their values. -/
theorem toRustMS_app_eq (app : String → List AVal → RustM AVal) (f : String)
    (args : List Hax.ImpExpr) (ρ : AEnv) :
    toRustMS app (.app f args) ρ =
      (toRustMS.argsS app args ρ >>= fun p => app f p.1 >>= fun r => .ok (r, p.2)) := by
  match args with
  | [] => simp only [toRustMS]
  | [_] | [_, _] | [_, _, _] => simp only [toRustMS, toRustMS.argsS, bind_assoc]; rfl
  | _ :: _ :: _ :: _ :: _ => simp only [toRustMS]

/-- **The reading of a tuple of any arity.** The components are read left to right by
    `toRustMS.argsS`, and their values form the tuple. -/
theorem toRustMS_tuple_eq (app : String → List AVal → RustM AVal) (es : List Hax.ImpExpr)
    (ρ : AEnv) :
    toRustMS app (.tuple es) ρ = toRustMS.argsS app es ρ >>= fun p => .ok (.tup p.1, p.2) := by
  simp only [toRustMS]

/-- `appRt` reads the runtime operations of the table of every extraction. -/
theorem appRt_ok_extBuiltins (T : Hax.Ascent.Table) (fns : List Hax.Ascent.ExtFn) :
    AppOk (Hax.Ascent.extBuiltins T fns) appRt :=
  appRt_ok _

/-! ## Calls to the functions of an extraction -/

/-- The environment binding a list of names, the head bound last, as `bindParams`. -/
def bindA : List (String × AVal) → AEnv
  | [] => fun _ => none
  | (x, v) :: ps => (bindA ps).upd x v

theorem encEnv_bindA (l : List (String × AVal)) :
    encEnv (bindA l) = Hax.Ascent.bindParams (l.map fun p => (p.1, p.2.toValue)) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨x, v⟩ := p
    rw [bindA, encEnv_upd, ih]
    rfl

theorem AVal.retVal_toValue (v : AVal) : Hax.Ascent.retVal v.toValue = v.toValue := by
  cases v <;> rfl

/-- The values of the constants a function reads: each read as a call without
    arguments. -/
def globalsS (app : String → List AVal → RustM AVal) :
    List String → RustM (List (String × AVal))
  | [] => .ok []
  | g :: gs => app g [] >>= fun v => globalsS app gs >>= fun rest => .ok ((g, v) :: rest)

/-- A successful reading of the constants `gs` reads, at each constant, a value that `bi`
    defines on no arguments. -/
theorem globalsS_ok {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) : ∀ (gs : List String) (l : List (String × AVal)),
      globalsS app gs = .ok l →
      l.map (fun p => (p.1, some p.2.toValue)) = gs.map fun g => (g, bi g [])
  | [], l, h => by cases h; rfl
  | g :: gs, l, h => by
    obtain ⟨v, hv, h⟩ := rustM_bind_ok h
    obtain ⟨rest, hrest, h⟩ := rustM_bind_ok h
    cases h
    have hb : bi g [] = some v.toValue := happ g [] v hv
    simp only [List.map_cons, hb, globalsS_ok happ gs rest hrest]

private theorem globalsS_ok_getD {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) (gs : List String) (l : List (String × AVal))
    (h : globalsS app gs = .ok l) :
    l.map (fun p => (p.1, p.2.toValue)) = gs.map fun g => (g, (bi g []).getD .unit) := by
  have := congrArg (List.map fun p : String × Option Hax.Value => (p.1, p.2.getD .unit))
    (globalsS_ok happ gs l h)
  simpa only [List.map_map, Function.comp_def, Option.getD_some] using this

/-- **The reading of a call to a function of an extraction**: its literal read from the
    environment binding the parameters to the arguments over its constants. -/
def callS (app : String → List AVal → RustM AVal) (fn : Hax.Ascent.ExtFn)
    (vs : List AVal) : RustM AVal :=
  if vs.length = fn.params.length then
    globalsS app fn.globals >>= fun gs =>
      toRustMS app fn.body (bindA (fn.params.zip vs ++ gs)) >>= fun p => .ok p.1
  else .fail .undef

theorem callS_ok {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) {fn : Hax.Ascent.ExtFn} {vs : List AVal} {r : AVal}
    (h : callS app fn vs = .ok r) : fn.leaf bi (AVal.toValues vs) = some r.toValue := by
  unfold callS at h
  by_cases hlen : vs.length = fn.params.length
  case neg => rw [ite_eq_right hlen] at h; cases h
  rw [ite_eq_left hlen] at h
  obtain ⟨gs, hgs, h⟩ := rustM_bind_ok h
  obtain ⟨p, hp, h⟩ := rustM_bind_ok h
  cases h
  obtain ⟨F, hF⟩ := toRustMS_sim happ fn.body _ p.1 p.2 hp
  have hentry : fn.entry bi (AVal.toValues vs) = encEnv (bindA (fn.params.zip vs ++ gs)) := by
    rw [encEnv_bindA, List.map_append, globalsS_ok_getD happ fn.globals gs hgs, AVal.toValues_eq_map,
      Hax.Ascent.ExtFn.entry, Hax.Ascent.ExtFn.globalVals, List.zip_map_right]
    rfl
  have hlen' : (AVal.toValues vs).length = fn.params.length := by
    rw [AVal.toValues_eq_map, List.length_map, hlen]
  unfold Hax.Ascent.ExtFn.leaf
  rw [ite_eq_left hlen', hentry, Hax.Ascent.haxEval_eq (fuel₀ := F) (fun fuel hf => by
    rw [hF fuel hf])]
  simp only [Option.map_some, AVal.retVal_toValue]

/-- `app` extended by the reading of calls to `fn`. -/
def extStepS (base : String → List AVal → RustM AVal) (fn : Hax.Ascent.ExtFn) :
    String → List AVal → RustM AVal :=
  fun f vs => if f = fn.name then callS base fn vs else base f vs

/-- **The reading of the calls of an extraction**: the runtime operations, and each
    function of `fns` read by `callS` under the reading of the functions before it. -/
def appExt (fns : List Hax.Ascent.ExtFn) : String → List AVal → RustM AVal :=
  fns.foldl extStepS appRt

/-- The names of the functions of an extraction are neither runtime names nor tagged
    names nor names of the table `T`. -/
noncomputable def ExtNamesOk (T : Hax.Ascent.Table) (fns : List Hax.Ascent.ExtFn) : Bool :=
  fns.all fun fn => (Hax.Ascent.runtimeTable.lookup fn.name).isNone &&
    (Hax.Ascent.parseTag fn.name).isNone && (T.lookup fn.name).isNone

theorem appExt_snoc_ok {T : Hax.Ascent.Table} {pre : List Hax.Ascent.ExtFn}
    {fn : Hax.Ascent.ExtFn} (ih : AppOk (Hax.Ascent.extBuiltins T pre) (appExt pre))
    (hrt : Hax.Ascent.runtimeTable.lookup fn.name = none)
    (htag : Hax.Ascent.parseTag fn.name = none) (hT : T.lookup fn.name = none) :
    AppOk (Hax.Ascent.extBuiltins T (pre ++ [fn])) (appExt (pre ++ [fn])) := by
  intro f vs r h
  simp only [appExt, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
  unfold extStepS at h
  by_cases hf : f = fn.name
  · rw [ite_eq_left hf] at h
    subst hf
    rw [Hax.Ascent.extBuiltins_self (post := []) hrt htag hT (by simp)]
    exact callS_ok ih h
  · rw [ite_eq_right hf] at h
    rw [Hax.Ascent.extBuiltins_append_agree (by simpa using hf)]
    exact ih f vs r h

theorem appExt_append_ok (T : Hax.Ascent.Table) :
    ∀ (post pre : List Hax.Ascent.ExtFn), AppOk (Hax.Ascent.extBuiltins T pre) (appExt pre) →
      ExtNamesOk T post = true →
      AppOk (Hax.Ascent.extBuiltins T (pre ++ post)) (appExt (pre ++ post))
  | [], pre, h, _ => by simpa using h
  | fn :: post, pre, h, hn => by
    simp only [ExtNamesOk, List.all_cons, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    obtain ⟨⟨⟨hrt, htag⟩, hT⟩, hpost⟩ := hn
    have h1 := appExt_snoc_ok h hrt htag hT
    have h2 := appExt_append_ok T post (pre ++ [fn]) h1 hpost
    simpa using h2

/-- **`appExt` reads the table of an extraction.** -/
theorem appExt_ok (T : Hax.Ascent.Table) (fns : List Hax.Ascent.ExtFn)
    (hn : ExtNamesOk T fns = true) : AppOk (Hax.Ascent.extBuiltins T fns) (appExt fns) :=
  appExt_append_ok T fns [] (appRt_ok _) hn

/-! ## The syntactic fragment -/

/-- The names of arity `n` that `appRt` reads. -/
def rtNameOk (f : String) : Nat → Bool
  | 1 => (tagTyAt? "Not#" f).isSome || (tagTyAt? "cast#" f).isSome ||
      (tagTyAt? "wrapping_neg#" f).isSome || f == "range_incl_end" || f == "Not" ||
      f == "len" || f == "array_lit" || f == "declassify" || (Hax.FieldTag.fieldTag? f).isSome
  | 2 => (wordOpAt? f).isSome || (checkedAt? f).isSome || (AOp.ofName f).isSome ||
      f == "index" || f == "repeat" || (boolRt? f).isSome || (cmpRt? f).isSome ||
      f == "array_lit" || (Hax.FieldTag.fieldTag? f).isSome
  | 3 => f == "array_update" || f == "array_lit"
  | _ => f == "array_lit"

/-- The constructs `toRustMS` reads, with every call to a runtime operation `appRt` reads
    or to one of the functions `locals`. A literal outside this fragment has no value
    under `toRustMS (appExt fns)`. -/
def fragOk (locals : List String) : Hax.ImpExpr → Bool
  | .lit (.int _) | .lit (.bool _) | .var _ | .unitVal => true
  | .letBind _ v b => fragOk locals v && fragOk locals b
  | .seq a b => fragOk locals a && fragOk locals b
  | .typeAscription e _ => fragOk locals e
  | .app f [a] => (rtNameOk f 1 || locals.contains f) && fragOk locals a
  | .app f [a, b] =>
    (rtNameOk f 2 || locals.contains f) && fragOk locals a && fragOk locals b
  | .app f [a, b, c] =>
    (rtNameOk f 3 || locals.contains f) && fragOk locals a && fragOk locals b &&
      fragOk locals c
  | .tuple es => fragOk.list locals es
  | .ifThenElse c t e => fragOk locals c && fragOk locals t && fragOk locals e
  | .forFold _ lo hi body => fragOk locals lo && fragOk locals hi && fragOk locals body
  | .forFoldRev _ lo hi body => fragOk locals lo && fragOk locals hi && fragOk locals body
  | .proj e _ => fragOk locals e
  | .app f args => (rtNameOk f args.length || locals.contains f) && fragOk.list locals args
  | _ => false
where
  /-- Every expression of the list is in the fragment. -/
  list (locals : List String) : List Hax.ImpExpr → Bool
    | [] => true
    | e :: es => fragOk locals e && list locals es

/-! ## Composition with the ascent -/

/-- **The state-passing reading of a function, composed with its ascent correspondence.**
    Every value `v` the reading of the literal returns from an environment whose encoding
    is the entry environment `entry a` encodes the value `f a` of the surface function. -/
theorem fnCorres_toRustMS {bi : Hax.Builtins} {A β : Type} [Hax.Ascent.HaxEnc β]
    {e : Hax.ImpExpr} {entry : A → Hax.Env} {G : A → Prop} {f : A → β}
    (hF : Hax.Ascent.FnCorres bi e entry G f) {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) (a : A) (hG : G a) (ρ : AEnv) (hρ : entry a = encEnv ρ)
    (v : AVal) (ρ' : AEnv) (hr : toRustMS app e ρ = .ok (v, ρ')) :
    v.toValue = Hax.Ascent.HaxEnc.enc (f a) := by
  obtain ⟨F1, h1⟩ := toRustMS_sim happ e ρ v ρ' hr
  obtain ⟨F2, h2⟩ := hF a hG
  have e2 := h2 (max F1 F2) (by omega)
  rw [hρ, h1 (max F1 F2) (by omega)] at e2
  exact Hax.Outcome.val.inj e2

end CatCrypt.Hax.RustSemantics
