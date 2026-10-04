/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.ToRustM
public import CatCrypt.Hax.RustSemantics.Arith
public import CatCrypt.Hax.RustSemantics.Casts
public import CatCrypt.Hax.Ascent.ExtTable

/-!
# The state-passing `RustM` reading of haxpipe literals

`toRustMS app e ρ` reads the literal `e` as an Aeneas program over `Aeneas.Std.RustM` that
threads an environment, as `Hax.denote'` does: a `letBind` extends the environment for the
rest of the run, a counted loop `forFold` binds its index and keeps the bindings its body
makes, and a call `.app f args` evaluates its arguments left to right and applies
`app f` to their values. The values (`AVal`) are integer literals, Booleans, unsigned
words of every Aeneas width, Aeneas arrays `Aeneas.Std.Array (UScalar ty) n` of words,
tuples and the unit value.

`appRt` is the reading of the runtime operations: the width-tagged word operations of
`WordOp` at each of the six unsigned widths, `Not#w`, `cast#w`, the untagged checked
operations `Add`, `Sub`, `Mul`, `Div`, `Rem`, and the array operations `index`,
`array_update` and `repeat` on the Aeneas `Array` model. An untyped integer literal is
read at the width of the operation that consumes it (`AVal.asW`). The loop index is the
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
* `appRt`, `AppOk`, `loopS`, `toRustMS`, `callS`, `appExt`, `ExtNamesOk`, `fragOk`
* `appRt_ok`, `loopS_sim`, `toRustMS_sim`, `appExt_ok`, `fnCorres_toRustMS`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Transfer.Param

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

/-- A tagged binary word operation at width `ty`. -/
def appWord (ty : UScalarTy) (o : WordOp) (a b : AVal) : RustM AVal := do
  let x ← a.asW ty
  let y ← b.asW ty
  let r ← o.aen x y
  .ok (.w ty r)

/-- An untagged checked operation: on two literals the integer operation, otherwise the
    Aeneas operation at the width of the word operand. -/
def appArith (o : AOp) : AVal → AVal → RustM AVal
  | .int n, .int m => .ok (.int (o.rt n m))
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

/-- `cast#w` of a word to the width `ty`. -/
def appCast (ty : UScalarTy) : AVal → RustM AVal
  | .w _ x => .ok (.w ty (UScalar.cast ty x))
  | _ => .fail .undef

/-- `Not#w` at the width `ty`. -/
def appNot (ty : UScalarTy) (a : AVal) : RustM AVal := do
  let x ← a.asW ty
  .ok (.w ty (~~~x))

/-- **The reading of the runtime operations.** -/
def appRt (f : String) : List AVal → RustM AVal
  | [a] =>
    match tagTyAt? "Not#" f with
    | some ty => appNot ty a
    | none =>
      match tagTyAt? "cast#" f with
      | some ty => appCast ty a
      | none => .fail .undef
  | [a, b] =>
    match wordOpAt? f with
    | some (ty, o) => appWord ty o a b
    | none =>
      match AOp.ofName f with
      | some o => appArith o a b
      | none =>
        if f = "index" then appIndex a b
        else if f = "repeat" then appRepeat a b
        else .fail .undef
  | [a, i, v] => if f = "array_update" then appUpdate a i v else .fail .undef
  | _ => .fail .undef

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
  split_ifs at hf <;> cases hf <;> subst f <;> cases ty <;>
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

/-- `Not#w` is read by the runtime at the width of its tag. -/
theorem not_leaf {ty : UScalarTy} (x : Int) :
    runtimeBuiltins base ("Not#" ++ uTag ty) [.int x] =
      some (.int (Hax.bitnot_w ty.numBits x)) := by
  cases ty <;> simp only [uTag, String.reduceAppend] <;>
    exact tagged1 (op := "Not") (g := Hax.bitnot_w) rfl (by first | decide | rfl) rfl x

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
  split_ifs at hf <;> cases hf <;> subst f
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

theorem appArith_ok {o : AOp} {a b r : AVal} (h : appArith o a b = .ok r) :
    ∃ x y : Int, a.toValue = .int x ∧ b.toValue = .int y ∧ r.toValue = .int (o.rt x y) := by
  cases a with
  | int n =>
    cases b with
    | int m =>
      cases h
      exact ⟨n, m, rfl, rfl, rfl⟩
    | w ty y =>
      simp only [appArith] at h
      obtain ⟨x, hx, h⟩ := rustM_bind_ok h
      obtain ⟨r', hr', h⟩ := rustM_bind_ok h
      cases h
      refine ⟨n, enc y, rfl, rfl, ?_⟩
      show Hax.Value.int (enc r') = _
      rw [rcompOk_iff.mp (AOp.square o x y) r' hr', litA_ok hx]
    | _ => simp [appArith] at h
  | w ty x =>
    simp only [appArith] at h
    obtain ⟨y, hy, h⟩ := rustM_bind_ok h
    obtain ⟨r', hr', h⟩ := rustM_bind_ok h
    cases h
    refine ⟨enc x, enc y, rfl, AVal.asW_ok hy, ?_⟩
    show Hax.Value.int (enc r') = _
    rw [rcompOk_iff.mp (AOp.square o x y) r' hr']
  | _ => simp [appArith] at h

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

/-- **The runtime operations are read by `appRt`**: `appRt` agrees with the runtime table
    over any base table. -/
theorem appRt_ok (base : Hax.Builtins) : AppOk (Hax.Ascent.runtimeBuiltins base) appRt := by
  intro f vs r h
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp [appRt] at h
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
      · cases h
  · simp only [appRt] at h
    split at h
    · rename_i ty o ho
      obtain ⟨x, y, hx, hy, hr⟩ := appWord_ok h
      rw [show AVal.toValues [a, b] = [.int (enc x), .int (enc y)] from by
        simp only [AVal.toValues, hx, hy], hr]
      exact WordOp.leaf (wordOpAt?_spec ho) _ _
    · split at h
      · rename_i o ho
        obtain ⟨x, y, hx, hy, hr⟩ := appArith_ok h
        rw [show AVal.toValues [a, b] = [.int x, .int y] from by
          simp only [AVal.toValues, hx, hy], hr]
        exact AOp.leaf ho _ _
      · split_ifs at h with hi hrep
        · subst hi
          obtain ⟨vs, j, ha, hb, hr⟩ := appIndex_ok h
          rw [show AVal.toValues [a, b] = [.array vs, .int j] from by
            simp only [AVal.toValues, ha, hb], index_leaf, hr]
        · subst hrep
          obtain ⟨n, hb, hr⟩ := appRepeat_ok h
          rw [show AVal.toValues [a, b] = [a.toValue, .int n] from by
            simp only [AVal.toValues, hb], repeat_leaf, hr]
  · simp only [appRt] at h
    split_ifs at h with hu
    · subst hu
      obtain ⟨vs, j, ha, hb, hr⟩ := appUpdate_ok h
      rw [show AVal.toValues [a, b, c] = [.array vs, .int j, c.toValue] from by
        simp only [AVal.toValues, ha, hb], array_update_leaf, hr]
  · simp [appRt] at h

/-! ## The reading -/

/-- `step` run on `k` successive indices from `i`. -/
def loopS (step : Nat → AEnv → RustM AEnv) : Nat → Nat → AEnv → RustM AEnv
  | 0, _, ρ => .ok ρ
  | k + 1, i, ρ => step i ρ >>= loopS step k (i + 1)

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
  | .tuple [a, b], ρ =>
    toRustMS app a ρ >>= fun p => toRustMS app b p.2 >>= fun q =>
      .ok (.tup [p.1, q.1], q.2)
  | .tuple [a, b, c], ρ =>
    toRustMS app a ρ >>= fun p => toRustMS app b p.2 >>= fun q =>
      toRustMS app c q.2 >>= fun s => .ok (.tup [p.1, q.1, s.1], s.2)
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
  | _, _ => .fail .undef

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

theorem toRustMS_sim {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) (e : Hax.ImpExpr) (ρ : AEnv) :
    ∀ v ρ', toRustMS app e ρ = .ok (v, ρ') → Sim bi e ρ ρ' v := by
  fun_induction toRustMS app e ρ
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
  case case12 a b ρ ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F1, h1⟩ := ih2 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih1 p q.1 q.2 hq
    refine ⟨max F1 F2, fun fuel hf => ?_⟩
    exact Hax.Ascent.denote'_tuple bi fuel
      (Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _)
        (Hax.Ascent.denoteArgs'_cons bi fuel (h2 fuel (by omega))
          (AVal.toValue_isControlFlow _) (Hax.Ascent.denoteArgs'_nil bi fuel _)))
  case case13 a b c ρ ih3 ih2 ih1 =>
    intro v ρ' h
    obtain ⟨p, hp, h⟩ := rustM_bind_ok h
    obtain ⟨q, hq, h⟩ := rustM_bind_ok h
    obtain ⟨s, hs, h⟩ := rustM_bind_ok h
    cases h
    obtain ⟨F1, h1⟩ := ih3 p.1 p.2 hp
    obtain ⟨F2, h2⟩ := ih2 p q.1 q.2 hq
    obtain ⟨F3, h3⟩ := ih1 q s.1 s.2 hs
    refine ⟨max F1 (max F2 F3), fun fuel hf => ?_⟩
    exact Hax.Ascent.denote'_tuple bi fuel
      (Hax.Ascent.denoteArgs'_cons bi fuel (h1 fuel (by omega)) (AVal.toValue_isControlFlow _)
        (Hax.Ascent.denoteArgs'_cons bi fuel (h2 fuel (by omega))
          (AVal.toValue_isControlFlow _)
          (Hax.Ascent.denoteArgs'_cons bi fuel (h3 fuel (by omega))
            (AVal.toValue_isControlFlow _) (Hax.Ascent.denoteArgs'_nil bi fuel _))))
  case case14 c t e ρ ih3 ih2 ih1 =>
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
        split_ifs at h with hab
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
  case case16 =>
    intro v ρ' h
    cases h

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

theorem AVal.toValues_eq_map (vs : List AVal) : AVal.toValues vs = vs.map AVal.toValue := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [AVal.toValues, ih]; rfl

theorem AVal.retVal_toValue (v : AVal) : Hax.Ascent.retVal v.toValue = v.toValue := by
  cases v <;> rfl

/-- The values of the constants a function reads: each read as a call without
    arguments. -/
def globalsS (app : String → List AVal → RustM AVal) :
    List String → RustM (List (String × AVal))
  | [] => .ok []
  | g :: gs => app g [] >>= fun v => globalsS app gs >>= fun rest => .ok ((g, v) :: rest)

theorem globalsS_ok {bi : Hax.Builtins} {app : String → List AVal → RustM AVal}
    (happ : AppOk bi app) : ∀ (gs : List String) (l : List (String × AVal)),
      globalsS app gs = .ok l →
      l.map (fun p => (p.1, p.2.toValue)) = gs.map fun g => (g, (bi g []).getD .unit)
  | [], l, h => by cases h; rfl
  | g :: gs, l, h => by
    obtain ⟨v, hv, h⟩ := rustM_bind_ok h
    obtain ⟨rest, hrest, h⟩ := rustM_bind_ok h
    cases h
    have hb : bi g [] = some v.toValue := happ g [] v hv
    simp only [List.map_cons, hb, Option.getD_some, globalsS_ok happ gs rest hrest]

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
  split_ifs at h with hlen
  obtain ⟨gs, hgs, h⟩ := rustM_bind_ok h
  obtain ⟨p, hp, h⟩ := rustM_bind_ok h
  cases h
  obtain ⟨F, hF⟩ := toRustMS_sim happ fn.body _ p.1 p.2 hp
  have hentry : fn.entry bi (AVal.toValues vs) = encEnv (bindA (fn.params.zip vs ++ gs)) := by
    rw [encEnv_bindA, List.map_append, globalsS_ok happ fn.globals gs hgs, AVal.toValues_eq_map,
      Hax.Ascent.ExtFn.entry, Hax.Ascent.ExtFn.globalVals, List.zip_map_right]
    rfl
  have hlen' : (AVal.toValues vs).length = fn.params.length := by
    rw [AVal.toValues_eq_map, List.length_map, hlen]
  unfold Hax.Ascent.ExtFn.leaf
  rw [if_pos hlen', hentry, Hax.Ascent.haxEval_eq (fuel₀ := F) (fun fuel hf => by
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
  split_ifs at h with hf
  · subst hf
    rw [Hax.Ascent.extBuiltins_self (post := []) hrt htag hT (by simp)]
    exact callS_ok ih h
  · rw [Hax.Ascent.extBuiltins_append_agree (by simpa using hf)]
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
  | 1 => (tagTyAt? "Not#" f).isSome || (tagTyAt? "cast#" f).isSome
  | 2 => (wordOpAt? f).isSome || (AOp.ofName f).isSome || f == "index" || f == "repeat"
  | 3 => f == "array_update"
  | _ => false

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
  | .tuple [a, b] => fragOk locals a && fragOk locals b
  | .tuple [a, b, c] => fragOk locals a && fragOk locals b && fragOk locals c
  | .ifThenElse c t e => fragOk locals c && fragOk locals t && fragOk locals e
  | .forFold _ lo hi body => fragOk locals lo && fragOk locals hi && fragOk locals body
  | _ => false

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
