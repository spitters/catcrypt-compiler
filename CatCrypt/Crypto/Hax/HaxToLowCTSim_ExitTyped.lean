/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit

/-!
# The exit-flag lowering with one heap per name

`haxToLowCTK` (`HaxToLowCTExit.lean`) lowers every call other than a scalar
operation to an `RCall` into a tower slot, while literals, loop counters, guards
and indices live in the scalar heap; a name written by a call is then read from
the scalar heap, which the call did not write.  This module gives every name of a
function body one heap, a placement `A : ExitTowers` (a name listed in `A` with a
tower type is held in the tower heap at that type, every other name in the scalar
heap), and lowers the body by `haxToLowCTKT A`, which reads each name from the
heap that holds it:

* a scalar operation on two scalar names (`scalarOpExprT`: hax-lean's comparisons,
  addition and subtraction, the Boolean connectives, and the width-tagged word calls
  `op#w` as masked `SExpr` templates, `WidthOp.sexpr`) is `RScalarSetExpr`;
* a literal bound to a name placed in a tower of at least `8` bytes (`exitMarshalOk`) is
  stored into limb `0` of the zeroed tower slot of the name;
* `index(arr, i)` with `arr` in a tower and `i` scalar is an `RArrLoad` into the
  reserved tower slot `exitCallName`: for an array of words, followed by a copy of its
  limb `0` into the scalar slot of the bound name; for an array of tower values
  (`exitElemTower`: the elements of `TFp2`, `TFp6`, `TFp12` are `TFp`, `TFp2`, `TFp6`, and
  those of `TArr n t` for a non-word `t` are `t`), followed by a copy into the tower slot of
  the bound name;
* `array_update(arr, i, src)` rebinding `arr` is an `RArrStore` into `arr`, of a scalar
  marshalled into limb `0` for an array of words, and of a tower value for an array of
  tower values;
* every other call is an `RCall` into `exitCallName`: its scalar arguments are
  first stored into reserved tower slots `exitMarshalName x` of at least `8` bytes
  (`callMarshal`), its tower arguments are read in place at their tower types, and the
  result is copied into the tower slot of the bound name (`RCopy`) or its limb `0` into the
  scalar slot of the bound name.  A call of `exitScalarRes` (a scalar call, or a leaf of
  `exitTowerScalarNames` whose arguments are held in towers) runs at `towerOfCallName f`
  into a scalar name.  A call whose result type `dr` the placement declares under the
  reserved name `exitCallKey f` (`exitCallTys`) runs at `dr` into a name placed at `dr`,
  or, for the word type `dr = TU64`, into a scalar name.  Any other call runs at
  `towerOfCallName f` into a name placed there.  An `array_lit` runs only into a name
  placed at an array type of as many elements (`exitArrLen`), at that type (`arrLitHeadN`);
  a `repeat(v, l)` with a literal count only into a name placed at an array type of `l`
  elements, reading `v` alone (`repeatHeadT`);
* a counted loop, upward or downward, or a `while` loop in an exit context is lowered to
  the exit-flag loop followed by `breakLoop`, whether its body breaks or not;
* a tail variable held in a tower is copied into the tower slot `exitResName`.

`exitTowers` infers a placement from a body; the simulation holds for every
placement, and the fragment `exitSimOkT A R` checks that the body reads each name
from its placement and that the tail has the result placement `R`.

**Agreement.**  `envAgreesT br A env rs` states that a non-reserved name placed in the
scalar heap holds a scalar word (`ScalarValN`: an unsigned word below `2^64` of any width,
a bool, an integer in `[0, 2^64)` or the unit) whose decoding is its scalar slot, and a
name placed in a tower at `t` holds a value related by the bridge `br` to its tower slot.
Agreement off the reserved names (`envAgreesOff`) is agreement under the empty placement
(`envAgreesT_nil_of_off`).

**Leaf conditions.**  `ExitLeaves bi leafSpec br` collects what the simulation assumes of
the builtin table and the leaves: the scalar operations compute their templates
(`ScalarOpsSoundT`), no builtin returns a control-flow value, the store of a scalar into
limb `0` of a fresh tower slot of at least `8` bytes is related to the scalar
(`ExitMarshal`), a call with a tower result other than the array operations `index`,
`array_update`, `array_lit`, `repeat` satisfies `LeafCallAgreesArgs` at
`towerOfCallName f` and, with a declared result type
`dr` of the parameter `D`, at `dr` (`callD`), a call with the declared word result `TU64`
satisfies `LeafCallScalar` at `TU64` (`wordD`), an array literal of `k` values satisfies
`LeafCallAgreesArgsLen` at every array type of `k` elements (`arrLitN`), a `repeat` with
count `k` satisfies `LeafRepeatAgrees` at every such type (`repeatN`), a
call with a scalar result and the element load from an
array of words return a scalar word whose decoding is limb `0` of the leaf output
(`LeafCallScalar`, `IndexScalarAgrees`), the element load from an array of tower values
is related to the loaded element (`IndexTowerAgrees`), the element stores satisfy
`ArrUpdateWordAgrees` and `ArrUpdateTowerAgrees`.  The range condition of the scalar
calls holds on the table `exitRange bi`, which refuses every result of a call of
`exitScalarRes` outside `ScalarValN` (`leafCallScalar_exitRange`); `exitRange` leaves
`index` unchanged (`indexScalarAgrees_exitRange`, `indexTowerAgrees_exitRange`).

## Main definitions

* `ExitTowers`, `exitCallName`, `exitMarshalName`
* `scalarOpExprT`, `WidthOp`, `widthOpOf`
* `exitWordTower`, `exitElemTower`, `exitContainer`, `exitElem`, `exitMarshalOk`
* `exitCallKey`, `exitCallTys`, `exitArrLen`
* `callMarshal`, `callHeadAt`, `callHeadT`, `arrLitHeadN`, `letHeadT`, `haxToLowCTKT`,
  `haxToLowCTFnT`, `haxToLowCTFnI`
* `exitTowerNames`, `exitTowers`, `exitResultPlace`
* `exitSimOkT`, `exitSimWhyT`
* `envAgreesT`, `envAgreesExitT`, `ExitSimTy`, `ExitLeaves`, `exitRange`

## Main results

* `callMarshal_sim`: the marshalling of call arguments into tower slots
* `head_lit`, `head_var`, `headT_app`, `head_app`: the heads of a `letBind`
* `haxToLowCTKT_simulates`: every expression of `exitSimOkT A R` simulates under `A`
* `haxToLowCTFnT_simulates_exit`: the result slot of `haxToLowCTFnT A e` agrees with the
  returned or final value (`outcomeAgreesT`)
* `haxToLowCTFnT_simulates_exit_scalar`, `haxToLowCTFnT_nil_simulates_exit`: the statement
  of `haxToLowCTFn_simulates_exit` at a scalar result, and at the empty placement from
  `envAgreesOff`
* `exitSimWhyT_eq_none_iff`: `exitSimWhyT` names the first construct outside the fragment
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT Located SExpr RustState RustExec LeafSpec rsSetScalar)

/-! ## §1  Placements and reserved tower slots -/

/-- A placement: the names held in the tower heap, each with its tower type.  A name
    absent from the list is held in the scalar heap. -/
abbrev ExitTowers := List (String × TowerType)

/-- The tower slot a call or an element load writes before its result is copied to
    the bound name. -/
def exitCallName : String := "__exit_call"

/-- The tower slot holding the scalar `x` as a call argument. -/
def exitMarshalName (x : String) : String := "__exit_m" ++ x

/-- The slot of component `i` of a function result that is a tuple:
    `"__exit_rc"` followed by `i` bars. -/
def exitResCompName (i : Nat) : String := "__exit_rc" ++ String.ofList (List.replicate i '|')

/-- The placement of a function result: a scalar in the scalar result slot, a tower value
    of type `t` in the tower result slot, a tuple whose component `i` is held in the
    slot `exitResCompName i`, or an `Option` as a tag and a payload. -/
inductive ExitRes where
  | scalar
  | tower (t : TowerType)
  | tuple
  /-- An `Option` whose payload is held under the placement `p`: the tag in the scalar
      result slot, the payload in the slot `exitResCompName 0`. -/
  | option (p : Option TowerType)
  deriving DecidableEq

/-- The result placement of a value held under the placement `p` of a name. -/
def ExitRes.ofPlace : Option TowerType → ExitRes
  | none => .scalar
  | some t => .tower t

/-- The result placement of two tails: the first, except that a first tail `None` takes the
    payload placement of a second tail that is an `Option`. -/
def ExitRes.optJoin : ExitRes → ExitRes → ExitRes
  | .option none, .option p => .option p
  | r, _ => r

/-- The placement is an `Option`. -/
def ExitRes.isOption : ExitRes → Bool
  | .option _ => true
  | _ => false

/-! ## §2  Scalar operations -/

/-- The two-operand operations of hax-lean's width-tagged word calls `op#w`. -/
inductive WidthOp where
  | add | sub | mul | and | or | xor | shl | shr | rotr | rotl
  deriving DecidableEq, Repr

/-- The width and operation of a width-tagged call name `op#w`: the operations
    `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `BitAnd`, `BitOr`, `BitXor`, `Shl`,
    `Shr`, `rotate_right`, `rotate_left` at the tags `8`, `16`, `32`, `64` and `size`
    (width `64`). -/
def widthOpOf : String → Option (Nat × WidthOp)
  | "wrapping_add#8" => some (8, .add)
  | "wrapping_add#16" => some (16, .add)
  | "wrapping_add#32" => some (32, .add)
  | "wrapping_add#64" => some (64, .add)
  | "wrapping_add#size" => some (64, .add)
  | "wrapping_sub#8" => some (8, .sub)
  | "wrapping_sub#16" => some (16, .sub)
  | "wrapping_sub#32" => some (32, .sub)
  | "wrapping_sub#64" => some (64, .sub)
  | "wrapping_sub#size" => some (64, .sub)
  | "wrapping_mul#8" => some (8, .mul)
  | "wrapping_mul#16" => some (16, .mul)
  | "wrapping_mul#32" => some (32, .mul)
  | "wrapping_mul#64" => some (64, .mul)
  | "wrapping_mul#size" => some (64, .mul)
  | "BitAnd#8" => some (8, .and)
  | "BitAnd#16" => some (16, .and)
  | "BitAnd#32" => some (32, .and)
  | "BitAnd#64" => some (64, .and)
  | "BitAnd#size" => some (64, .and)
  | "BitOr#8" => some (8, .or)
  | "BitOr#16" => some (16, .or)
  | "BitOr#32" => some (32, .or)
  | "BitOr#64" => some (64, .or)
  | "BitOr#size" => some (64, .or)
  | "BitXor#8" => some (8, .xor)
  | "BitXor#16" => some (16, .xor)
  | "BitXor#32" => some (32, .xor)
  | "BitXor#64" => some (64, .xor)
  | "BitXor#size" => some (64, .xor)
  | "Shl#8" => some (8, .shl)
  | "Shl#16" => some (16, .shl)
  | "Shl#32" => some (32, .shl)
  | "Shl#64" => some (64, .shl)
  | "Shl#size" => some (64, .shl)
  | "Shr#8" => some (8, .shr)
  | "Shr#16" => some (16, .shr)
  | "Shr#32" => some (32, .shr)
  | "Shr#64" => some (64, .shr)
  | "Shr#size" => some (64, .shr)
  | "rotate_right#8" => some (8, .rotr)
  | "rotate_right#16" => some (16, .rotr)
  | "rotate_right#32" => some (32, .rotr)
  | "rotate_right#64" => some (64, .rotr)
  | "rotate_right#size" => some (64, .rotr)
  | "rotate_left#8" => some (8, .rotl)
  | "rotate_left#16" => some (16, .rotl)
  | "rotate_left#32" => some (32, .rotl)
  | "rotate_left#64" => some (64, .rotl)
  | "rotate_left#size" => some (64, .rotl)
  | _ => none

/-- `e` masked to its low `w` bits: `e &&& (2^w - 1)`, which over `Nat` is
    `e % 2^w`. -/
def widthMask (w : Nat) (e : SExpr) : SExpr := .SAnd e (.SLit (2 ^ w - 1))

/-- The bitwise disjunction as `(a ^^^ b) ^^^ (a &&& b)`, exact over `Nat`. -/
def orExprN (a b : SExpr) : SExpr := .SXor (.SXor a b) (.SAnd a b)

/-- The rotation amount `b` modulo a width `w` that is a power of two:
    `b &&& (w - 1)`. -/
def widthAmt (w : Nat) (b : SExpr) : SExpr := .SAnd b (.SLit (w - 1))

/-- The scalar expression of the width-tagged operation `op` at width `w` on `a`
    and `b`, with `x % 2^w` written as `widthMask w x`, `n % w` as `widthAmt w n` and
    `|||` as `orExprN`. -/
def WidthOp.sexpr (w : Nat) : WidthOp → SExpr → SExpr → SExpr
  | .add, a, b => widthMask w (.SAdd a b)
  | .sub, a, b => widthMask w (.SSub (.SAdd (widthMask w a) (.SLit (2 ^ w))) (widthMask w b))
  | .mul, a, b => widthMask w (.SMul a b)
  | .and, a, b => .SAnd (widthMask w a) (widthMask w b)
  | .or, a, b => orExprN (widthMask w a) (widthMask w b)
  | .xor, a, b => .SXor (widthMask w a) (widthMask w b)
  | .shl, a, b => widthMask w (.SShl (widthMask w a) b)
  | .shr, a, b => .SShr (widthMask w a) b
  | .rotr, a, b => widthMask w (orExprN (.SShr (widthMask w a) (widthAmt w b))
      (.SShl (widthMask w a) (.SSub (.SLit w) (widthAmt w b))))
  | .rotl, a, b => widthMask w (orExprN (.SShl (widthMask w a) (widthAmt w b))
      (.SShr (widthMask w a) (.SSub (.SLit w) (widthAmt w b))))

/-- The `SExpr` of a scalar operation on the scalars `a` and `b`: the operations of
    `scalarOpExpr`, their capitalised forms, the Boolean connectives `&&`, `and` as
    `SAnd` and `||`, `or` as `orExprN` (exact on the decodings `0` and `1` of two
    Booleans), and the width-tagged calls of `widthOpOf`. -/
def scalarOpExprT (op : String) (a b : SExpr) : Option SExpr :=
  match op with
  | "lt" | "Lt" => some (.SLt a b)
  | "gt" | "Gt" => some (.SLt b a)
  | "le" | "Le" => some (.SSub (.SLit 1) (.SLt b a))
  | "ge" | "Ge" => some (.SSub (.SLit 1) (.SLt a b))
  | "eq" | "Eq" => some (.SSub (.SSub (.SLit 1) (.SLt a b)) (.SLt b a))
  | "ne" | "Ne" => some (.SAdd (.SLt a b) (.SLt b a))
  | "add" | "Add" => some (.SAdd a b)
  | "sub" | "Sub" => some (.SSub a b)
  | "&&" | "and" => some (.SAnd a b)
  | "||" | "or" => some (orExprN a b)
  | _ => (widthOpOf op).map fun p => p.2.sexpr p.1 a b

/-- The call names whose result is a scalar besides the width-tagged ones. -/
def exitScalarCalls : List String :=
  ["len", "lt", "gt", "le", "ge", "eq", "ne", "add", "sub",
   "Lt", "Gt", "Le", "Ge", "Eq", "Ne", "Add", "Sub", "Mul", "Div", "Rem",
   "BitAnd", "BitOr", "BitXor", "Shl", "Shr", "Not", "Neg", "&&", "||", "and", "or"]

/-- A call whose result is held in the scalar heap: a name of `exitScalarCalls` or a
    width-tagged name (containing `#`). -/
def exitScalarCall (f : String) : Bool := exitScalarCalls.contains f || f.contains '#'

/-- The leaf calls whose arguments are held in towers and whose result is a scalar: the
    zero and identity predicates of field elements and curve points and the infinity
    flags `infinity`, `g2_inf` of a point, used as conditions, and the accessors `k`,
    `l`, `ctilde_len` (ML-DSA parameters), `height` and `depth` (a trace and a Merkle
    tree), used as loop bounds.  Each is a leaf whose specification returns a word,
    not an element of the tower. -/
def exitTowerScalarNames : List String :=
  ["is_zero", "fe_is_zero", "fp_is_zero", "fp2_is_zero", "h2c_p256_is_zero",
   "point_is_identity", "g1_proj_is_identity", "g2_proj_is_identity", ".infinity",
   ".g2_inf", ".k", ".l", "ctilde_len", ".height", ".depth"]

/-- A leaf call of `exitTowerScalarNames`. -/
def exitTowerScalarCall (f : String) : Bool := exitTowerScalarNames.contains f

/-- A call whose result the typed lowering copies from limb `0` of the call slot into the
    scalar heap: a scalar call or a leaf call of `exitTowerScalarNames`. -/
def exitScalarRes (f : String) : Bool := exitScalarCall f || exitTowerScalarCall f

theorem exitScalarRes_index : exitScalarRes "index" = false := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall, exitTowerScalarNames]

theorem exitScalarRes_arrayLit : exitScalarRes "array_lit" = false := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall, exitTowerScalarNames]

/-! ## §3  The heads of a `letBind` -/

/-- A tower type holding one scalar word: `TU64`, `TU32`, `TU8`. -/
def exitWordTower : TowerType → Bool
  | .TU64 | .TU32 | .TU8 => true
  | _ => false

/-- The element tower type of a tower type whose elements are tower values: an element of
    `TFp2` is a `TFp`, of `TFp6` a `TFp2`, of `TFp12` a `TFp6`, and of `TArr n t` a `t`
    when `t` is not a word type (`exitWordTower`).  `none` for a tower type whose elements
    are scalar words. -/
def exitElemTower : TowerType → Option TowerType
  | .TFp2 => some .TFp
  | .TFp6 => some .TFp2
  | .TFp12 => some .TFp6
  | .TArr _ t => if exitWordTower t then none else some t
  | _ => none

/-- The tower type of an array whose elements are held at the tower type `t`: the inverse
    of `exitElemTower`. -/
def exitContainer : TowerType → Option TowerType
  | .TFp => some .TFp2
  | .TFp2 => some .TFp6
  | .TFp6 => some .TFp12
  | _ => none

theorem exitElemTower_of_container {t c : TowerType} (h : exitContainer t = some c) :
    exitElemTower c = some t := by
  cases t <;> simp only [exitContainer, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- The type of the elements an element store writes into an array held at `t`: the
    element tower type of `exitElemTower`, and `t.elemType` for an array of words. -/
def exitElem (t : TowerType) : TowerType := (exitElemTower t).getD t.elemType

/-- The marshalling of a scalar word into limb `0` of a tower slot of type `dt` needs a
    slot of at least `8` bytes. -/
def exitMarshalOk (dt : TowerType) : Bool := decide (8 ≤ dt.storageBytes)

/-- The argument slots of a call, and the context storing its scalar arguments: an
    argument held in a tower is read in place at its tower type; a scalar argument `x` is
    stored into limb `0` of the fresh tower slot `exitMarshalName x` of type `dt`, which
    `exitMarshalOk dt` requires to hold a word.  `none` when an argument is not a
    variable. -/
def callMarshal (A : ExitTowers) (dt : TowerType) :
    List ImpExpr → Option ((LowCT → LowCT) × List Located)
  | [] => some (id, [])
  | .var x :: as =>
      match callMarshal A dt as with
      | none => none
      | some (ctx, ls) =>
        match A.lookup x with
        | some t => some (ctx, ⟨x, t⟩ :: ls)
        | none =>
          if exitMarshalOk dt then
            some (fun c => .RLetZero (exitMarshalName x) dt
              (.RSeq (.RLimbStoreExpr ⟨exitMarshalName x, dt⟩ 0 (.SVar x)) (ctx c)),
              ⟨exitMarshalName x, dt⟩ :: ls)
          else none
  | _ :: _ => none

/-- The `SExpr` of a scalar operation `f` on two scalar variables bound to a scalar
    name `n`. -/
def scalarOpHeadT (A : ExitTowers) (n f : String) : List ImpExpr → Option SExpr
  | [.var a, .var b] =>
      if A.lookup n = none ∧ A.lookup a = none ∧ A.lookup b = none then
        scalarOpExprT f (.SVar a) (.SVar b)
      else none
  | _ => none

/-- The head of `let n = index(arr, idx)` with `arr` in a tower at `t` and `idx` scalar.
    For an array of words (`exitElemTower t = none`) and a scalar `n`: load the element
    into `exitCallName` and copy its limb `0` into `n`.  For an array of tower values of
    type `t'` (`exitElemTower t = some t'`) and `n` placed at `t'`: load the element into
    `exitCallName` at `t'` and copy it into the tower slot `n`. -/
def indexHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var arr, .var idx] =>
      match A.lookup arr with
      | some t =>
          if A.lookup idx = none then
            match exitElemTower t with
            | none =>
                if A.lookup n = none then
                  some fun b => .RLetZero exitCallName .TFp
                    (.RSeq (.RArrLoad ⟨exitCallName, .TFp⟩ ⟨arr, t⟩ idx)
                      (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b))
                else none
            | some t' =>
                if A.lookup n = some t' then
                  some fun b => .RLetZero exitCallName t'
                    (.RSeq (.RArrLoad ⟨exitCallName, t'⟩ ⟨arr, t⟩ idx)
                      (.RSeq (.RCopy ⟨n, t'⟩ ⟨exitCallName, t'⟩) b))
                else none
          else none
      | none => none
  | _ => none

/-- The head of `let arr = array_update(arr, idx, src)` with `arr` in a tower of type
    `t` and `idx` scalar: store `src` at element `idx` of `arr`.  For an array of words
    (`exitElemTower t = none`), `src` is scalar and is marshalled at `t.elemType`; for an
    array of tower values of type `t'`, `src` is held at `t'` or is a scalar marshalled at
    `t'`. -/
def updateHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var arr, .var idx, .var src] =>
      match A.lookup arr with
      | some t =>
          if n = arr ∧ A.lookup idx = none ∧
              ((exitElemTower t).isNone → A.lookup src = none) then
            match callMarshal A (exitElem t) [.var src] with
            | some (ctx, [srcLoc]) =>
                if srcLoc.locSrc = exitElem t then
                  some fun b => .RSeq (ctx (.RArrStore ⟨arr, t⟩ idx srcLoc)) b
                else none
            | _ => none
          else none
      | none => none
  | _ => none

/-- The head of `let n = f(args)` for a call lowered to `RCall` whose scalar arguments are
    marshalled at the tower type `dt` and whose result slot has the tower type `dr`: the
    call writes `exitCallName` at `dr` from the slots of `callMarshal A dt`; for a scalar
    `n` its limb `0` is copied into the scalar slot `n`, for `n` placed at `dr` it is
    copied into the tower slot `n`. -/
def callHeadAt (A : ExitTowers) (n f : String) (dt dr : TowerType) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match callMarshal A dt args with
  | none => none
  | some (ctx, ls) =>
    let callC : LowCT := .RLetZero exitCallName dr (ctx (.RCall f ⟨exitCallName, dr⟩ ls))
    match A.lookup n with
    | none => some fun b => .RSeq callC (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)
    | some t =>
      if t = dr then some fun b => .RSeq callC (.RSeq (.RCopy ⟨n, dr⟩ ⟨exitCallName, dr⟩) b)
      else none

/-- The reserved name under which a placement records the declared result type of the
    calls of `f`. -/
def exitCallKey (f : String) : String := "__exit_ty:" ++ f

/-- The reserved name under which a placement records the payload placement of the calls
    of `f` returning an `Option`. -/
def exitOptKey (f : String) : String := "__exit_ty;" ++ f

/-- A name of the form `exitCallKey f` or `exitOptKey f`. -/
def exitIsCallKey (s : String) : Bool := "__exit_ty".toList.isPrefixOf s.toList

/-- The declared result types of the calls recorded in the placement `A`: the type at
    `exitCallKey f`.  A declared result of the word type `TU64` is a scalar word. -/
def exitCallTys (A : ExitTowers) (f : String) : Option TowerType := A.lookup (exitCallKey f)

/-- The declared payload placements of the calls returning an `Option` recorded in the
    placement `A`: the type at `exitOptKey f`, the word type `TU64` for a scalar payload. -/
def exitOptTys (A : ExitTowers) (f : String) : Option TowerType := A.lookup (exitOptKey f)

/-- The reserved name under which a placement records the result type of a linked callee
    `f`. -/
def exitCalleeKey (f : String) : String := "__exit_ty!" ++ f

/-- The reserved name under which a placement records the slot type of argument `i` of a
    linked callee `f`. -/
def exitArgKey (f : String) (i : Nat) : String := "__exit_ty?" ++ (toString i ++ "!" ++ f)

/-- The slot types recorded in `A` for the arguments `i, i + 1, …` of `f`, up to the first
    argument without one, at most `fuel` of them. -/
def exitArgTys (A : ExitTowers) (f : String) : Nat → Nat → List TowerType
  | 0, _ => []
  | fuel + 1, i =>
      match A.lookup (exitArgKey f i) with
      | some t => t :: exitArgTys A f fuel (i + 1)
      | none => []

/-- The largest number of arguments of a linked callee `exitCalleeTys` reads. -/
def exitArgMax : Nat := 64

/-- The argument slot types and the result type of a linked callee `f` recorded in the
    placement `A`: the type at `exitCalleeKey f`, and the types at `exitArgKey f i` for the
    first arguments with one, at most `exitArgMax` of them. -/
def exitCalleeTys (A : ExitTowers) (f : String) : Option (List TowerType × TowerType) :=
  (A.lookup (exitCalleeKey f)).map fun dr => (exitArgTys A f exitArgMax 0, dr)

/-- The head of a call.  A call of `exitScalarRes` bound to a scalar name runs at its tower
    type `towerOfCallName f`.  A call of a linked callee with argument slot types `ts` and
    result type `dr` (`exitCalleeTys A f`), declaring no other type, runs at `dr` when its
    argument slots, the scalar arguments marshalled at `TU64`, have the types `ts`.  A call
    with a declared result type `dr` (`exitCallTys A f`) runs at `dr`, its scalar arguments
    marshalled at `TU64`.  In both cases its result is copied into the tower slot of a name
    placed at `dr`, or, for `dr = TU64`, from limb `0` into the scalar slot of a scalar
    name.  A call without a declared result type runs at `towerOfCallName f` into a name
    placed there. -/
def callHeadT (A : ExitTowers) (n f : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  if exitScalarRes f then
    if A.lookup n = none then callHeadAt A n f (towerOfCallName f) (towerOfCallName f) args
    else none
  else
    match exitCalleeTys A f with
    | some (ts, dr) =>
        if (exitCallTys A f).isSome ∨ (exitOptTys A f).isSome ∨
            (A.lookup n = none ∧ dr ≠ .TU64) ∨
            (callMarshal A .TU64 args).map (fun cl => cl.2.map (·.locDst)) ≠ some ts then none
        else callHeadAt A n f .TU64 dr args
    | none =>
    match exitCallTys A f with
    | some dr =>
        if (exitOptTys A f).isSome ∨ (A.lookup n = none ∧ dr ≠ .TU64) then none
        else callHeadAt A n f .TU64 dr args
    | none =>
        if A.lookup n = some (towerOfCallName f) then
          callHeadAt A n f (towerOfCallName f) (towerOfCallName f) args
        else none

/-- The tower type of the first argument held in a tower. -/
def exitFirstTower (A : ExitTowers) : List ImpExpr → Option TowerType
  | [] => none
  | .var x :: as =>
      match A.lookup x with
      | some t => some t
      | none => exitFirstTower A as
  | _ :: as => exitFirstTower A as

/-- The number of elements of an array type: `n` for `TArr n t`, and `2`, `3`, `2` for the
    containers `TFp2`, `TFp6`, `TFp12` of `exitContainer`. -/
def exitArrLen : TowerType → Option Nat
  | .TArr n _ => some n
  | .TFp2 => some 2
  | .TFp6 => some 3
  | .TFp12 => some 2
  | _ => none

/-- Every argument variable held in a tower is placed at `dt`. -/
def exitArgsAt (A : ExitTowers) (dt : TowerType) (args : List ImpExpr) : Bool :=
  args.all fun a =>
    match a with
    | .var x =>
        match A.lookup x with
        | some t => decide (t = dt)
        | none => true
    | _ => true

/-- The head of `let n = array_lit(args)` with `n` placed at an array type `c` of
    `args.length` elements (`exitArrLen`) whose element type holds a word (`exitMarshalOk`),
    and every argument held in a tower placed at the element type `exitElem c`
    (`exitArgsAt`): the scalar arguments are marshalled at `exitElem c`, the result is held
    at `c`. -/
def arrLitHeadN (A : ExitTowers) (n : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match A.lookup n with
  | some c =>
      -- On the Bls, plonky3, Libcrux_specs and Mldsa extractions every tower argument of
      -- an array literal is placed at `exitElem c`, so `exitArgsAt` refuses no site there.
      if exitArrLen c = some args.length ∧ exitMarshalOk (exitElem c) = true ∧
          exitArgsAt A (exitElem c) args = true then
        callHeadAt A n "array_lit" (exitElem c) c args
      else none
  | none => none

/-- The head of `let n = repeat(v, l)` with a literal count `l` decoding to `k` and `n`
    placed at an array type `c` of `k` elements (`exitArrLen`) whose element type holds a
    word: the call reads only `v`, marshalled at the element type `exitElem c` when
    scalar, and writes its result at `c`. -/
def repeatHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var v, .lit l] =>
      match A.lookup n, valueToScalar (Value.ofLit l) with
      | some c, some k =>
          if exitArrLen c = some k ∧ exitMarshalOk (exitElem c) = true then
            callHeadAt A n "repeat" (exitElem c) c [.var v]
          else none
      | _, _ => none
  | _ => none

/-- The head of `let n = f(args)`: a scalar operation, an element load, an element
    store, an array literal at the placed array type of its bound name (`arrLitHeadN`), a
    `repeat` with a literal count at the placed array type of its bound name
    (`repeatHeadT`), or a call. -/
def appHeadT (A : ExitTowers) (n f : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match scalarOpHeadT A n f args with
  | some se => some fun b => .RSeq (.RScalarSetExpr n se) b
  | none =>
    if f = "index" then indexHeadT A n args
    else if f = "array_update" then updateHeadT A n args
    else if f = "array_lit" then arrLitHeadN A n args
    else if f = "repeat" then repeatHeadT A n args
    else callHeadT A n f args

/-- The head of `let n = val` under the placement `A`: a literal bound to a scalar
    name as in `letHead`; a literal bound to a name placed in a tower at `t` with
    `exitMarshalOk t` as the zero slot of type `t` with the literal's word stored into its
    limb `0`; a copy between two scalar names as in `letHead`, between two tower names of
    one type by `RCopy`; a call by `appHeadT`. -/
def letHeadT (A : ExitTowers) (n : String) : ImpExpr → Option (LowCT → LowCT)
  | .lit l =>
      match A.lookup n with
      | none => letHead n (.lit l)
      | some t =>
          if exitMarshalOk t then
            (valueToScalar (Value.ofLit l)).map fun kk b =>
              .RLetZero n t (.RSeq (.RLimbStoreExpr ⟨n, t⟩ 0 (.SLit kk)) b)
          else none
  | .var s =>
      match A.lookup n, A.lookup s with
      | none, none => letHead n (.var s)
      | some t, some t' =>
          if t = t' then
            if n = s then some id
            else some fun b => .RSeq (.RCopy ⟨n, t⟩ ⟨s, t⟩) b
          else none
      | _, _ => none
  | .app f args => appHeadT A n f args
  | _ => none

/-! ## §4  The translator -/

/-- The stores of the components of a tuple of variables from component `i` on: the
    variable of component `i` copied into the slot `exitResCompName i`, in the scalar heap
    or at its tower type.  `none` when a component is not a variable. -/
def tupleStoreT (A : ExitTowers) : Nat → List ImpExpr → Option LowCT
  | _, [] => some .RSkip
  | i, .var x :: es => (tupleStoreT A (i + 1) es).map fun rest =>
      match A.lookup x with
      | none => .RSeq (.RScalarSetExpr (exitResCompName i) (.SVar x)) rest
      | some t => .RSeq (.RCopy ⟨exitResCompName i, t⟩ ⟨x, t⟩) rest
  | _, _ :: _ => none

/-- The lowered tail value `e`: a scalar value stored into the scalar result slot as
    by `resultStore`, a tower variable copied into the tower slot `exitResName`, a tuple
    of variables stored component by component (`tupleStoreT`). -/
def resultStoreT (A : ExitTowers) : ImpExpr → Option LowCT
  | .var x =>
      match A.lookup x with
      | some t => some (.RCopy ⟨exitResName, t⟩ ⟨x, t⟩)
      | none => resultStore (.var x)
  | .tuple es => tupleStoreT A 0 es
  | .app "None" [] => some (.RScalarSet exitResName 0)
  | .app "Some" [.var x] =>
      some (.RSeq (match A.lookup x with
        | none => .RScalarSetExpr (exitResCompName 0) (.SVar x)
        | some t => .RCopy ⟨exitResCompName 0, t⟩ ⟨x, t⟩) (.RScalarSet exitResName 1))
  | e => resultStore e

/-- The tail stores of `resultStoreT` at a call: `None()`, `Some(x)`, and otherwise the
    store of `resultStore`. -/
theorem resultStoreT_app_cases (A : ExitTowers) {f : String} {args : List ImpExpr}
    {s : LowCT} (h : resultStoreT A (.app f args) = some s) :
    (f = "None" ∧ args = [] ∧ s = .RScalarSet exitResName 0) ∨
      (∃ x, f = "Some" ∧ args = [.var x] ∧
        s = .RSeq (match A.lookup x with
          | none => .RScalarSetExpr (exitResCompName 0) (.SVar x)
          | some t => .RCopy ⟨exitResCompName 0, t⟩ ⟨x, t⟩) (.RScalarSet exitResName 1)) ∨
      resultStore (.app f args) = some s := by
  unfold resultStoreT at h
  split at h
  · simp_all
  · simp_all
  · rename_i heq
    obtain ⟨rfl, rfl⟩ := ImpExpr.app.inj heq
    exact Or.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩
  · rename_i heq
    obtain ⟨rfl, rfl⟩ := ImpExpr.app.inj heq
    exact Or.inr (Or.inl ⟨_, rfl, rfl, (Option.some.inj h).symm⟩)
  · exact Or.inr (Or.inr h)

/-- The reserved tower slot receiving the tag of a call returning an `Option`. -/
def exitOptTagName : String := "__exit_otag"

/-- The reserved tower slot receiving the payload of a call returning an `Option`. -/
def exitOptPayName : String := "__exit_opay"

/-- The reserved scalar slot holding the tag of a call returning an `Option`. -/
def exitOptTagS : String := "__exit_otags"

/-- The call and the payload binding of `match f(args) [Some p => … | None => …]` for a call
    `f` with the declared `Option` payload type `t` (`exitOptTys`): the two-output call
    `RCallN f [tag, payload]` on the slots of `callMarshal A TU64 args`, the tag copied from
    limb `0` into the scalar slot `exitOptTagS`, and the binding of `p` to the payload: from
    limb `0` for a scalar `p` and `t = TU64`, by `RCopy` for `p` placed at `t ≠ TU64`. -/
def optHeadT (A : ExitTowers) (f : String) (args : List ImpExpr) (p : String) :
    Option (LowCT × LowCT) :=
  if exitScalarRes f || f == "index" || f == "array_update" || f == "array_lit" ||
      f == "repeat" then none
  else
  match exitOptTys A f with
  | none => none
  | some t =>
    match callMarshal A .TU64 args with
    | none => none
    | some (ctx, ls) =>
      let callC : LowCT := .RSeq (.RLetZero exitOptTagName .TU64 (.RLetZero exitOptPayName t
        (ctx (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls))))
        (.RScalarSetExpr exitOptTagS (.SLimb exitOptTagName 0))
      match A.lookup p with
      | none =>
          if t = .TU64 then some (callC, .RScalarSetExpr p (.SLimb exitOptPayName 0)) else none
      | some tp =>
          if tp = t ∧ t ≠ .TU64 then some (callC, .RCopy ⟨p, t⟩ ⟨exitOptPayName, t⟩) else none

/-- `x` is held in the scalar heap under `A`. -/
def exitSc (A : ExitTowers) (x : String) : Bool := (A.lookup x).isNone

/-- A variable `e` is held in the scalar heap under `A`; any other expression passes. -/
def exitScE (A : ExitTowers) : ImpExpr → Bool
  | .var x => exitSc A x
  | _ => true

/-- The runtime upper bound of a counted loop (`forBoundsRt lo hi`), if any, is held in
    the scalar heap under `A`. -/
def exitScRt (A : ExitTowers) (lo hi : ImpExpr) : Bool :=
  match forBoundsRt lo hi with
  | some (_, h) => exitSc A h
  | none => true

/-- The statements `haxToLowCTKT` lowers outside tail position by `haxToLowCT`: a
    variable and the unit, both lowered to `RSkip`. -/
def exitStmtOk : ImpExpr → Bool
  | .var _ => true
  | .unitVal => true
  | _ => false

/-- The exit-flag lowering under the placement `A`: `haxToLowCTK true` with the heads
    of `letHeadT A`, the tail store `resultStoreT A`, and, in an exit context, every
    counted loop with the bounds of `forBounds` or `forBoundsRt`, every downward counted
    loop with the bounds of `forBounds`, and every `while` loop on a variable lowered to
    the exit-flag loop followed by `breakLoop`.  Every name the lowering reads from the
    scalar heap is placed there: the guard of a conditional or of a `while` loop, the
    counter and the runtime bound of a counted loop, and a variable `break` payload are
    refused when `A` places them in a tower (`exitSc`, `exitScE`, `exitScRt`); outside
    tail position only a variable or the unit is lowered by `haxToLowCT`
    (`exitStmtOk`). -/
def haxToLowCTKT (A : ExitTowers) : Bool → Option String → ImpExpr → Option (LowCT × Bool)
  | tl, fl, .letBind name val body =>
      match letHeadT A name val, haxToLowCTKT A tl fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none
  | tl, fl, .seq a b =>
      match haxToLowCTKT A false fl a, haxToLowCTKT A tl fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none
  | tl, fl, .ifThenElse (.var v) t e =>
      if exitSc A v then
        match haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
        | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
        | _, _ => none
      else none
  | tl, fl, .typeAscription e _ => haxToLowCTKT A tl fl e
  | tl, fl, .match_ (.app f args) [(.somePat (.varPat p), t), (.nonePat, e)] =>
      match optHeadT A f args p, haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (callC, bindP), some (tC, xt), some (eC, xe) =>
          some (.RSeq callC (.RIfNz exitOptTagS (.RSeq bindP tC) eC), xt || xe)
      | _, _, _ => none
  | tl, fl, .match_ (.app f args) [(.nonePat, e), (.somePat (.varPat p), t)] =>
      match optHeadT A f args p, haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (callC, bindP), some (tC, xt), some (eC, xe) =>
          some (.RSeq callC (.RIfNz exitOptTagS (.RSeq bindP tC) eC), xt || xe)
      | _, _, _ => none
  | false, fl, .whileFoldReturn (.var c) body =>
      if exitSc A c then
        match haxToLowCTKT A false (some (exitRunName fl)) body with
        | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
        | none => none
      else none
  | false, fl, .forFoldReturn i lo hi body =>
      if exitSc A i && exitScRt A lo hi then
        match forBounds lo hi, forBoundsRt lo hi,
            haxToLowCTKT A false (some (exitRunName fl)) body with
        | some (l, h), _, some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
        | none, some (l, h), some (bC, _) =>
            some (exitForLoopRt (exitRunName fl) i l h bC, true)
        | _, _, _ => none
      else none
  | false, fl, .forFoldRevReturn i lo hi body =>
      if exitSc A i then
        match forBounds lo hi, haxToLowCTKT A false (some (exitRunName fl)) body with
        | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
        | _, _ => none
      else none
  | false, some r, .forFold i lo hi body =>
      if exitSc A i && exitScRt A lo hi then
        match forBounds lo hi, forBoundsRt lo hi,
            haxToLowCTKT A false (some (exitRunName (some r))) body with
        | some (l, h), _, some (bC, _) =>
            some (breakLoop (exitForLoop (exitRunName (some r)) i l h bC), false)
        | none, some (l, h), some (bC, _) =>
            some (breakLoop (exitForLoopRt (exitRunName (some r)) i l h bC), false)
        | _, _, _ => none
      else none
  | false, some r, .forFoldRev i lo hi body =>
      if exitSc A i then
        match forBounds lo hi, haxToLowCTKT A false (some (exitRunName (some r))) body with
        | some (l, h), some (bC, _) =>
            some (breakLoop (exitForLoopRev (exitRunName (some r)) i l h bC), false)
        | _, _ => none
      else none
  | false, some r, .whileFold (.var c) body =>
      if exitSc A c then
        match haxToLowCTKT A false (some (exitRunName (some r))) body with
        | some (bC, _) => some (breakLoop (exitLoop (exitRunName (some r)) c bC), false)
        | none => none
      else none
  | _, some _, .cfBreak e =>
      if exitScE A e then (exitStore e).map fun s => (s, true) else none
  | true, _, e => (resultStoreT A e).map fun s => (s, false)
  | false, _, e => if exitStmtOk e then (haxToLowCT e).map fun c => (c, false) else none

/-- The lowering of a function body under the placement `A`: `haxToLowCTKT A` in tail
    position in the function context, inside the frame `exitFunction`. -/
def haxToLowCTFnT (A : ExitTowers) (e : ImpExpr) : Option LowCT :=
  (haxToLowCTKT A true (some exitFnSlot) e).map fun p => exitFunction p.1

/-! ## §5  Placement inference -/

/-- The variables of an argument list. -/
def exitArgNames : List ImpExpr → List String
  | [] => []
  | .var x :: as => x :: exitArgNames as
  | _ :: as => exitArgNames as

/-- The names a body binds by a call with a tower result: a call other than a call of
    `exitScalarRes`, `index`, `array_update` and `len`. -/
def exitTowerBound : ImpExpr → List String
  | .letBind n v b =>
      let here := match v with
        | .app f _ =>
            if exitScalarRes f || f = "index" || f = "array_update" || f = "len" then []
            else [n]
        | _ => []
      here ++ exitTowerBound b
  | .seq a b => exitTowerBound a ++ exitTowerBound b
  | .ifThenElse _ t e => exitTowerBound t ++ exitTowerBound e
  | .typeAscription e _ => exitTowerBound e
  | .whileFoldReturn _ b => exitTowerBound b
  | .forFoldReturn _ _ _ b => exitTowerBound b
  | .forFoldRevReturn _ _ _ b => exitTowerBound b
  | .forFold _ _ _ b => exitTowerBound b
  | .forFoldRev _ _ _ b => exitTowerBound b
  | .whileFold _ b => exitTowerBound b
  | _ => []

/-- The `letBind`s of a body at statement positions and in loop bodies, in order. -/
def exitBinds : ImpExpr → List (String × ImpExpr)
  | .letBind n v b => (n, v) :: exitBinds b
  | .seq a b => exitBinds a ++ exitBinds b
  | .ifThenElse _ t e => exitBinds t ++ exitBinds e
  | .typeAscription e _ => exitBinds e
  | .whileFoldReturn _ b => exitBinds b
  | .forFoldReturn _ _ _ b => exitBinds b
  | .forFoldRevReturn _ _ _ b => exitBinds b
  | .forFold _ _ _ b => exitBinds b
  | .forFoldRev _ _ _ b => exitBinds b
  | .whileFold _ b => exitBinds b
  | _ => []

/-- A call on field elements: a name with the prefix `fp_`, `fp2_`, `fp6_` or `fp12_`,
    whose arguments and result are tower values. -/
def exitFieldCall (f : String) : Bool :=
  f.startsWith "fp_" || f.startsWith "fp2_" || f.startsWith "fp6_" || f.startsWith "fp12_"

/-- The names one binding shows to hold tower values, given the names `T` known to: the
    array argument of `index`, `len` and `array_update` and the result of `array_update`;
    the stored value of `array_update` when it is in `T`; the arguments and the result of
    an `array_lit` with an argument in `T`; the arguments of a leaf of
    `exitTowerScalarNames`; the arguments and the result of a call of `exitFieldCall`;
    both sides of a copy with a side in `T`. -/
def exitTowerUse (T : List String) : String × ImpExpr → List String
  | (n, .app f args) =>
      if f = "index" ∨ f = "len" then
        match args with
        | .var a :: _ => [a]
        | _ => []
      else if f = "array_update" then
        match args with
        | [.var a, _, .var s] => a :: n :: (if T.contains s then [s] else [])
        | _ => []
      else if f = "array_lit" then
        if (exitArgNames args).any T.contains then n :: exitArgNames args else []
      else if exitTowerScalarCall f then exitArgNames args
      else if exitFieldCall f then n :: exitArgNames args
      else []
  | (n, .var s) => if T.contains n || T.contains s then [n, s] else []
  | _ => []

/-- The arrays one binding shows to hold tower values, given the names `T` holding tower
    values: the array of an element load bound to a name in `T`, and the array of an
    element store of a value in `T`. -/
def exitContainerUse (T : List String) : String × ImpExpr → List String
  | (n, .app "index" (.var a :: _)) => if T.contains n then [a] else []
  | (_, .app "array_update" [.var a, _, .var s]) => if T.contains s then [a] else []
  | _ => []

/-- The element loads from an array of `C`. -/
def exitElemUse (C : List String) : String × ImpExpr → List String
  | (n, .app "index" (.var a :: _)) => if C.contains a then [n] else []
  | _ => []

/-- `k` rounds of the closure of the names holding tower values over the bindings `bs`,
    from `T`: `exitTowerUse`, the arrays of `exitContainerUse`, and their element loads. -/
def exitTowerNamesAux (bs : List (String × ImpExpr)) : Nat → List String → List String
  | 0, T => T
  | k + 1, T =>
      let C := bs.flatMap (exitContainerUse T)
      exitTowerNamesAux bs k (T ++ bs.flatMap (exitTowerUse T) ++ C ++ bs.flatMap (exitElemUse C))

/-- The names of a body holding tower values: six rounds of `exitTowerNamesAux`. -/
def exitTowerNames (e : ImpExpr) : List String :=
  let bs := exitBinds e
  exitTowerNamesAux bs 6 (bs.flatMap (exitTowerUse []))

/-- The names a body binds or reads as scalars, given the names `tb` bound by a call with
    a tower result and the names `tu` holding tower values: literal bindings of a name
    outside `tb`, results of calls of `exitScalarRes`, element loads bound to a name
    outside `tu`, loop counters and bounds, and conditions. -/
def exitScalarNames (tb tu : List String) : ImpExpr → List String
  | .letBind n v b =>
      let here := match v with
        | .lit _ => if tb.contains n then [] else [n]
        | .app f _ =>
            if exitScalarRes f then [n] else if f = "index" && !tu.contains n then [n] else []
        | _ => []
      here ++ exitScalarNames tb tu b
  | .seq a b => exitScalarNames tb tu a ++ exitScalarNames tb tu b
  | .ifThenElse (.var c) t e => c :: (exitScalarNames tb tu t ++ exitScalarNames tb tu e)
  | .ifThenElse _ t e => exitScalarNames tb tu t ++ exitScalarNames tb tu e
  | .typeAscription e _ => exitScalarNames tb tu e
  | .whileFoldReturn (.var c) b => c :: exitScalarNames tb tu b
  | .forFoldReturn i _ (.var h) b => i :: h :: exitScalarNames tb tu b
  | .forFoldReturn i _ _ b => i :: exitScalarNames tb tu b
  | .forFoldRevReturn i _ _ b => i :: exitScalarNames tb tu b
  | .forFold i _ (.var h) b => i :: h :: exitScalarNames tb tu b
  | .forFold i _ _ b => i :: exitScalarNames tb tu b
  | .forFoldRev i _ _ b => i :: exitScalarNames tb tu b
  | .whileFold (.var c) b => c :: exitScalarNames tb tu b
  | .whileFold _ b => exitScalarNames tb tu b
  | _ => []

/-- `(x, t) :: A` when `x` is neither placed in `A` nor a scalar name of `sc`. -/
def exitPlaceAt (sc : List String) (A : ExitTowers) (x : String) (t : TowerType) :
    ExitTowers :=
  if (A.lookup x).isNone && !sc.contains x then (x, t) :: A else A

/-- One step of placement inference at a binding, from the scalar names `sc`.  An element
    load placed at `t'` places its array at `exitContainer t'`; an element store of a
    value placed at `t'` places its array at `exitContainer t'`; an `array_lit` with an
    argument placed at `t'` places its arguments at `t'` and its result at
    `exitContainer t'`; the result and the arguments of a call other than a scalar call are
    placed at the call's tower type; a copy between names takes the placement of the placed
    side.  With `dflt`, the arrays of element loads of scalars, element stores of scalars
    and `len`, and an `array_lit` without a placed argument with its arguments, are placed
    at `.TFp`. -/
def exitTowersStep (sc : List String) (dflt : Bool) (A : ExitTowers) :
    String × ImpExpr → ExitTowers
  | (n, .app f args) =>
      if f = "index" then
        match args with
        | .var arr :: _ =>
            match A.lookup n with
            | some t' =>
                match exitContainer t' with
                | some c => exitPlaceAt sc A arr c
                | none => A
            | none => if sc.contains n || dflt then exitPlaceAt sc A arr .TFp else A
        | _ => A
      else if f = "array_update" then
        match args with
        | [.var arr, _, .var src] =>
            match A.lookup src with
            | some t' =>
                match exitContainer t' with
                | some c => exitPlaceAt sc A arr c
                | none => A
            | none => if sc.contains src || dflt then exitPlaceAt sc A arr .TFp else A
        | _ => A
      else if f = "len" then
        match args with
        | .var arr :: _ => if dflt then exitPlaceAt sc A arr .TFp else A
        | _ => A
      else if f = "array_lit" then
        match exitFirstTower A args with
        | some t' =>
            match exitContainer t' with
            | some c =>
                exitPlaceAt sc ((exitArgNames args).foldl (fun A x => exitPlaceAt sc A x t') A) n c
            | none => A
        | none =>
            if dflt then
              exitPlaceAt sc ((exitArgNames args).foldl (fun A x => exitPlaceAt sc A x .TFp) A)
                n .TFp
            else A
      else if exitScalarCall f then A
      else
        let dt := towerOfCallName f
        exitPlaceAt sc ((exitArgNames args).foldl (fun A x => exitPlaceAt sc A x dt) A) n dt
  | (n, .var s) =>
      match A.lookup n, A.lookup s with
      | some t, none => exitPlaceAt sc A s t
      | none, some t => exitPlaceAt sc A n t
      | _, _ => A
  | _ => A

/-- The inferred placement of a body: from its scalar names (`exitScalarNames`, where a
    literal binding of a name that a call with a tower result also binds does not make the
    name scalar, and an element load bound to a name of `exitTowerNames` is not scalar),
    three passes of `exitTowersStep` over its bindings, then two passes with the default
    placements; the names of the form `exitCallKey f` are left out, so that the placement
    declares no call result type (`exitCallTys_exitTowers`). -/
def exitTowers (e : ImpExpr) : ExitTowers :=
  let bs := exitBinds e
  let sc := exitScalarNames (exitTowerBound e) (exitTowerNames e) e
  let pass (dflt : Bool) (A : ExitTowers) : ExitTowers := bs.foldl (exitTowersStep sc dflt) A
  (pass true (pass true (pass false (pass false (pass false []))))).filter
    fun p => !exitIsCallKey p.1

theorem exitIsCallKey_callKey (f : String) : exitIsCallKey (exitCallKey f) = true := by
  simp [exitIsCallKey, exitCallKey, String.toList_append]

theorem exitIsCallKey_optKey (f : String) : exitIsCallKey (exitOptKey f) = true := by
  simp [exitIsCallKey, exitOptKey, String.toList_append]

/-- A placement with the names of `exitIsCallKey` left out declares nothing at such a
    name. -/
theorem lookup_isCallKey_filter (l : ExitTowers) {k : String} (hk : exitIsCallKey k = true) :
    (l.filter fun p => !exitIsCallKey p.1).lookup k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', b⟩ := p
    by_cases hp : exitIsCallKey k' = true
    · simp [hp, ih]
    · have hne : (k == k') = false := by
        simpa using fun h : k = k' => hp (h ▸ hk)
      simp [hp, List.lookup_cons, hne, ih]

/-- A placement with the names of the form `exitCallKey` left out declares no call result
    type. -/
theorem lookup_callKey_filter (l : ExitTowers) (f : String) :
    (l.filter fun p => !exitIsCallKey p.1).lookup (exitCallKey f) = none :=
  lookup_isCallKey_filter l (exitIsCallKey_callKey f)

theorem exitCallTys_exitTowers (e : ImpExpr) (f : String) :
    exitCallTys (exitTowers e) f = none :=
  lookup_callKey_filter _ f

theorem exitOptTys_exitTowers (e : ImpExpr) (f : String) :
    exitOptTys (exitTowers e) f = none :=
  lookup_isCallKey_filter _ (exitIsCallKey_optKey f)

theorem exitCallKey_inj {f g : String} (h : exitCallKey f = exitCallKey g) : f = g := by
  unfold exitCallKey at h
  have := congrArg String.toList h
  simp [String.toList_append] at this
  exact String.toList_inj.mp this

theorem exitOptKey_inj {f g : String} (h : exitOptKey f = exitOptKey g) : f = g := by
  unfold exitOptKey at h
  have := congrArg String.toList h
  simp [String.toList_append] at this
  exact String.toList_inj.mp this

theorem exitOptKey_ne_callKey (f g : String) : exitOptKey f ≠ exitCallKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitOptKey, exitCallKey, String.toList_append] at this

/-- A lookup at `key f` in the entries `key g ↦ d` of the names `fs` with `M g = some d`,
    followed by `rest` declaring nothing at `key f`, finds only `M f`. -/
theorem lookup_keyed {key : String → String} (hinj : ∀ {f g}, key f = key g → f = g)
    (M : String → Option TowerType) (fs : List String) (rest : ExitTowers) {f : String}
    {d : TowerType} (hrest : rest.lookup (key f) = none)
    (h : ((fs.filterMap fun g => (M g).map fun d => (key g, d)) ++ rest).lookup (key f) =
      some d) : M f = some d := by
  induction fs with
  | nil => simp [hrest] at h
  | cons g fs ih =>
    rcases hg : M g with _ | e
    · simp only [List.filterMap_cons, hg, Option.map_none] at h
      exact ih h
    · simp only [List.filterMap_cons, hg, Option.map_some, List.cons_append,
        List.lookup_cons] at h
      by_cases he : key f = key g
      · simp only [he, beq_self_eq_true] at h
        rw [hinj he, hg]
        exact h
      · have : (key f == key g) = false := by simpa using he
        simp only [this] at h
        exact ih h

/-- The entries `key g ↦ d` declare nothing at a name no `key g` equals. -/
theorem lookup_keyed_other {key : String → String} (M : String → Option TowerType)
    (fs : List String) (rest : ExitTowers) {k : String} (hk : ∀ g, key g ≠ k) :
    ((fs.filterMap fun g => (M g).map fun d => (key g, d)) ++ rest).lookup k =
      rest.lookup k := by
  induction fs with
  | nil => rfl
  | cons g fs ih =>
    rcases hg : M g with _ | e
    · simp only [List.filterMap_cons, hg, Option.map_none]
      exact ih
    · simp only [List.filterMap_cons, hg, Option.map_some, List.cons_append,
        List.lookup_cons]
      have : (k == key g) = false := by simpa using fun h : k = key g => hk g h.symm
      simp only [this]
      exact ih

/-- The placement `rest` with the declared result types `D` and the declared payload
    placements `DO` of the call names `fs` recorded under `exitCallKey` and `exitOptKey`,
    and the names of those forms in `rest` left out. -/
def exitWithCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) : ExitTowers :=
  (fs.filterMap fun g => (D g).map fun d => (exitCallKey g, d)) ++
    ((fs.filterMap fun g => (DO g).map fun d => (exitOptKey g, d)) ++
      rest.filter (fun p => !exitIsCallKey p.1))

/-- `exitWithCallKeys D DO fs rest` declares only result types of `D`. -/
theorem exitCallTys_withCallKeys {D DO : String → Option TowerType} {fs : List String}
    {rest : ExitTowers} {f : String} {dr : TowerType}
    (h : exitCallTys (exitWithCallKeys D DO fs rest) f = some dr) : D f = some dr := by
  unfold exitCallTys exitWithCallKeys at h
  refine lookup_keyed exitCallKey_inj D fs _ ?_ h
  rw [lookup_keyed_other DO fs _ (fun g => exitOptKey_ne_callKey g f)]
  exact lookup_callKey_filter _ f

/-- `exitWithCallKeys D DO fs rest` declares only payload placements of `DO`. -/
theorem exitOptTys_withCallKeys {D DO : String → Option TowerType} {fs : List String}
    {rest : ExitTowers} {f : String} {t : TowerType}
    (h : exitOptTys (exitWithCallKeys D DO fs rest) f = some t) : DO f = some t := by
  unfold exitOptTys exitWithCallKeys at h
  rw [lookup_keyed_other D fs _ (fun g => (exitOptKey_ne_callKey f g).symm)] at h
  exact lookup_keyed exitOptKey_inj DO fs _ (lookup_isCallKey_filter _ (exitIsCallKey_optKey f)) h

theorem exitIsCallKey_calleeKey (f : String) : exitIsCallKey (exitCalleeKey f) = true := by
  simp [exitIsCallKey, exitCalleeKey, String.toList_append, List.isPrefixOf]

theorem exitCalleeKey_ne_callKey (f g : String) : exitCalleeKey f ≠ exitCallKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCalleeKey, exitCallKey, String.toList_append] at this

theorem exitCalleeKey_ne_optKey (f g : String) : exitCalleeKey f ≠ exitOptKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCalleeKey, exitOptKey, String.toList_append] at this

/-- The placement `exitTowers e` records no linked callee. -/
theorem exitCalleeTys_exitTowers (e : ImpExpr) (f : String) :
    exitCalleeTys (exitTowers e) f = none := by
  unfold exitCalleeTys
  rw [show (exitTowers e).lookup (exitCalleeKey f) = none from
    lookup_isCallKey_filter _ (exitIsCallKey_calleeKey f)]
  rfl

/-- `exitWithCallKeys D DO fs rest` records no linked callee. -/
theorem exitCalleeTys_withCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) (f : String) :
    exitCalleeTys (exitWithCallKeys D DO fs rest) f = none := by
  unfold exitCalleeTys exitWithCallKeys
  rw [lookup_keyed_other D fs _ (fun g => (exitCalleeKey_ne_callKey f g).symm),
    lookup_keyed_other DO fs _ (fun g => (exitCalleeKey_ne_optKey f g).symm),
    lookup_isCallKey_filter _ (exitIsCallKey_calleeKey f)]
  rfl

theorem exitIsCallKey_argPrefix (x : String) : exitIsCallKey ("__exit_ty?" ++ x) = true := by
  simp [exitIsCallKey, String.toList_append, List.isPrefixOf]

theorem exitIsCallKey_argKey (f : String) (i : Nat) : exitIsCallKey (exitArgKey f i) = true :=
  exitIsCallKey_argPrefix _

theorem argPrefix_ne_callKey (x g : String) : "__exit_ty?" ++ x ≠ exitCallKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCallKey, String.toList_append] at this

theorem argPrefix_ne_optKey (x g : String) : "__exit_ty?" ++ x ≠ exitOptKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitOptKey, String.toList_append] at this

theorem argPrefix_ne_calleeKey (x g : String) : "__exit_ty?" ++ x ≠ exitCalleeKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCalleeKey, String.toList_append] at this

theorem exitArgKey_ne_callKey (f g : String) (i : Nat) : exitArgKey f i ≠ exitCallKey g :=
  argPrefix_ne_callKey _ g

theorem exitArgKey_ne_optKey (f g : String) (i : Nat) : exitArgKey f i ≠ exitOptKey g :=
  argPrefix_ne_optKey _ g

theorem exitArgKey_ne_calleeKey (f g : String) (i : Nat) : exitArgKey f i ≠ exitCalleeKey g :=
  argPrefix_ne_calleeKey _ g

/-- `exitWithCallKeys D DO fs rest` holds nothing at `exitCalleeKey f`. -/
theorem lookup_calleeKey_withCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) (f : String) :
    (exitWithCallKeys D DO fs rest).lookup (exitCalleeKey f) = none := by
  unfold exitWithCallKeys
  rw [lookup_keyed_other D fs _ (fun g => (exitCalleeKey_ne_callKey f g).symm),
    lookup_keyed_other DO fs _ (fun g => (exitCalleeKey_ne_optKey f g).symm)]
  exact lookup_isCallKey_filter _ (exitIsCallKey_calleeKey f)

/-- `exitWithCallKeys D DO fs rest` holds nothing at `exitArgKey f i`. -/
theorem lookup_argKey_withCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) (f : String) (i : Nat) :
    (exitWithCallKeys D DO fs rest).lookup (exitArgKey f i) = none := by
  unfold exitWithCallKeys
  rw [lookup_keyed_other D fs _ (fun g => (exitArgKey_ne_callKey f g i).symm),
    lookup_keyed_other DO fs _ (fun g => (exitArgKey_ne_optKey f g i).symm)]
  exact lookup_isCallKey_filter _ (exitIsCallKey_argKey f i)

theorem lookup_append_of_none {l r : ExitTowers} {k : String} (h : r.lookup k = none) :
    (l ++ r).lookup k = l.lookup k := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    cases hk : (k == k') <;> simp [List.lookup, hk, ih]

theorem exitArgTys_append {l r : ExitTowers} {f : String}
    (h : ∀ i, r.lookup (exitArgKey f i) = none) :
    ∀ fuel i, exitArgTys (l ++ r) f fuel i = exitArgTys l f fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [exitArgTys, lookup_append_of_none (h i), exitArgTys_append h fuel (i + 1)]

/-- The linked callees recorded in `l ++ r` are those of `l` when `r` holds nothing at the
    keys of `f`. -/
theorem exitCalleeTys_append {l r : ExitTowers} {f : String}
    (hc : r.lookup (exitCalleeKey f) = none) (ha : ∀ i, r.lookup (exitArgKey f i) = none) :
    exitCalleeTys (l ++ r) f = exitCalleeTys l f := by
  unfold exitCalleeTys
  rw [lookup_append_of_none hc, exitArgTys_append ha]

/-- The entries of the argument slot types `ts` of `g`, from argument `i` on. -/
def argEntries (g : String) : Nat → List TowerType → ExitTowers
  | _, [] => []
  | i, t :: ts => (exitArgKey g i, t) :: argEntries g (i + 1) ts

/-- The placement `rest` with the linked callees `sig` (name, argument slot types, result
    type) recorded under `exitCalleeKey` and `exitArgKey`. -/
def exitWithCallees (sig : List (String × List TowerType × TowerType)) (rest : ExitTowers) :
    ExitTowers :=
  sig.flatMap (fun s => (exitCalleeKey s.1, s.2.2) :: argEntries s.1 0 s.2.1) ++ rest

/-- The linked callees of `exitWithCallees sig rest` are those `sig` records, when `rest`
    holds nothing at their keys. -/
theorem exitCalleeTys_withCallees (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) (f : String) (hc : rest.lookup (exitCalleeKey f) = none)
    (ha : ∀ i, rest.lookup (exitArgKey f i) = none) :
    exitCalleeTys (exitWithCallees sig rest) f = exitCalleeTys (exitWithCallees sig []) f := by
  unfold exitWithCallees
  rw [exitCalleeTys_append hc ha, List.append_nil]

theorem lookup_append_of_left_none {l r : ExitTowers} {k : String} (h : l.lookup k = none) :
    (l ++ r).lookup k = r.lookup k := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    cases hk : (k == k')
    · simp only [List.cons_append, List.lookup, hk] at h ⊢
      exact ih h
    · simp [List.lookup, hk] at h

theorem lookup_argEntries_other (g : String) {k : String} (hk : ∀ i, exitArgKey g i ≠ k) :
    ∀ i ts, (argEntries g i ts).lookup k = none
  | _, [] => rfl
  | i, t :: ts => by
    have h1 : (k == exitArgKey g i) = false := by
      simpa using fun h : k = exitArgKey g i => hk i h.symm
    simp only [argEntries, List.lookup, h1]
    exact lookup_argEntries_other g hk (i + 1) ts

/-- A lookup in `exitWithCallees sig rest` at a name of neither form `exitCalleeKey g` nor
    `exitArgKey g i` is a lookup in `rest`. -/
theorem lookup_withCallees_other (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) {k : String} (hc : ∀ g, exitCalleeKey g ≠ k)
    (ha : ∀ g i, exitArgKey g i ≠ k) :
    (exitWithCallees sig rest).lookup k = rest.lookup k := by
  unfold exitWithCallees
  induction sig with
  | nil => rfl
  | cons s sig ih =>
    have h1 : (k == exitCalleeKey s.1) = false := by
      simpa using fun h : k = exitCalleeKey s.1 => hc s.1 h.symm
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.lookup, h1]
    rw [lookup_append_of_left_none (lookup_argEntries_other s.1 (fun i => ha s.1 i) 0 s.2.1)]
    exact ih

theorem exitCallTys_withCallees (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) (f : String) :
    exitCallTys (exitWithCallees sig rest) f = exitCallTys rest f :=
  lookup_withCallees_other sig rest (fun g => exitCalleeKey_ne_callKey g f)
    (fun g i => exitArgKey_ne_callKey g f i)

theorem exitOptTys_withCallees (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) (f : String) :
    exitOptTys (exitWithCallees sig rest) f = exitOptTys rest f :=
  lookup_withCallees_other sig rest (fun g => exitCalleeKey_ne_optKey g f)
    (fun g i => exitArgKey_ne_optKey g f i)

theorem exitReserved_calleeKey (g : String) : exitReserved (exitCalleeKey g) = true := by
  simp [exitReserved, exitCalleeKey, String.toList_append, List.isPrefixOf]

theorem exitReserved_argPrefix (x : String) : exitReserved ("__exit_ty?" ++ x) = true := by
  simp [exitReserved, String.toList_append, List.isPrefixOf]

/-- `exitWithCallees sig rest` places a name outside the reserved names as `rest` does. -/
theorem lookup_withCallees_nonreserved (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) {n : String} (hn : exitReserved n = false) :
    (exitWithCallees sig rest).lookup n = rest.lookup n :=
  lookup_withCallees_other sig rest
    (fun g h => by rw [← h, exitReserved_calleeKey] at hn; cases hn)
    (fun g i h => by rw [← h] at hn; rw [exitArgKey, exitReserved_argPrefix] at hn; cases hn)

/-- The placement of the tail value of a body under `A`, read from its first tail: the
    placement of a tail variable, `tuple` for a tail tuple, and `scalar` otherwise. -/
def exitResultPlace (A : ExitTowers) : ImpExpr → ExitRes
  | .letBind _ _ b => exitResultPlace A b
  | .seq _ b => exitResultPlace A b
  | .ifThenElse _ t e => ExitRes.optJoin (exitResultPlace A t) (exitResultPlace A e)
  | .typeAscription e _ => exitResultPlace A e
  | .match_ _ [(_, a), (_, b)] => ExitRes.optJoin (exitResultPlace A a) (exitResultPlace A b)
  | .var x => ExitRes.ofPlace (A.lookup x)
  | .tuple _ => .tuple
  | .app "None" [] => .option none
  | .app "Some" [.var x] => .option (A.lookup x)
  | _ => .scalar

/-- The function lowering under the inferred placement. -/
def haxToLowCTFnI (e : ImpExpr) : Option LowCT := haxToLowCTFnT (exitTowers e) e

/-! ## §6  The fragment -/

/-- Every argument is a non-reserved variable. -/
def exitArgsOk : List ImpExpr → Bool
  | [] => true
  | .var x :: as => !exitReserved x && exitArgsOk as
  | _ :: _ => false

/-- The runtime bounds `forBoundsRt` accepts, with a non-reserved scalar upper-bound
    variable. -/
def forBoundsRtOkT (A : ExitTowers) (lo hi : ImpExpr) : Bool :=
  match forBoundsRt lo hi with
  | some (_, h) => !exitReserved h && exitSc A h
  | none => false

/-- The bounds of a counted loop of the fragment have a scalar runtime bound. -/
theorem exitScRt_of_ok {A : ExitTowers} {lo hi : ImpExpr}
    (h : ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) = true) :
    exitScRt A lo hi = true := by
  unfold exitScRt
  rcases hRt : forBoundsRt lo hi with _ | ⟨l, x⟩
  · rfl
  · obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
    simp only [forBoundsRtOkT, hRt, forBounds, Option.isSome_none, Bool.false_or,
      Bool.and_eq_true] at h
    exact h.2

/-- A literal whose value is a scalar word: an unsigned literal of width at most `64`,
    an integer in `[0, 2^64)`, a bool or the unit. -/
def exitLitOk : ImpLit → Bool
  | .uintLit w _ => w != .w128
  | .int k => decide (0 ≤ k) && decide (k < 2 ^ 64)
  | .bool _ => true
  | .unit => true
  | _ => false

/-- The arguments of `repeat(v, l)`: a non-reserved variable and a literal of `exitLitOk`. -/
def exitRepeatArgsOk : List ImpExpr → Bool
  | [.var v, .lit l] => !exitReserved v && exitLitOk l
  | _ => false

/-- The arguments of a call `f` the fragment admits: non-reserved variables
    (`exitArgsOk`), or, for `repeat`, a variable and a literal count (`exitRepeatArgsOk`). -/
def exitArgsOkT (f : String) (args : List ImpExpr) : Bool :=
  exitArgsOk args || (f == "repeat" && exitRepeatArgsOk args)

/-- A scalar payload of a `cfBreak`: a variable held in the scalar heap, a literal of
    `exitLitOk`, or `unitVal`. -/
def exitPayloadOk (A : ExitTowers) : ImpExpr → Bool
  | .var x => !exitReserved x && exitSc A x
  | .lit l => exitLitOk l
  | .unitVal => true
  | _ => false

theorem exitScE_of_payloadOk {A : ExitTowers} {p : ImpExpr} (h : exitPayloadOk A p = true) :
    exitScE A p = true := by
  cases p <;> simp_all [exitPayloadOk, exitScE]

/-- The fragment the typed simulation covers under the placement `A` with result
    placement `R`, at tail position `tl` and loop context `il`: every name is
    non-reserved; conditions, loop counters, runtime bounds and break payloads are
    scalar; a literal is a scalar word; a copy keeps the placement; a call
    has a head of `appHeadT`; a tail variable has placement `R`, a tail literal or
    `unitVal` needs `R = scalar`, and a tail tuple of non-reserved variables needs
    `R = tuple`. -/
def exitSimOkT (A : ExitTowers) (R : ExitRes) : Bool → Bool → ImpExpr → Bool
  | tl, il, .letBind n (.lit l) body =>
      exitLitOk l && !exitReserved n && exitSimOkT A R tl il body
  | tl, il, .letBind n (.var s) body =>
      !exitReserved n && !exitReserved s && decide (A.lookup n = A.lookup s) &&
        exitSimOkT A R tl il body
  | tl, il, .letBind n (.app f args) body =>
      !exitReserved n && exitArgsOkT f args && (appHeadT A n f args).isSome &&
        exitSimOkT A R tl il body
  | tl, il, .seq a b => exitSimOkT A R false il a && exitSimOkT A R tl il b
  | tl, il, .ifThenElse (.var v) t e =>
      !exitReserved v && exitSc A v && exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | tl, il, .typeAscription e _ => exitSimOkT A R tl il e
  | tl, il, .match_ (.app f args) [(.somePat (.varPat p), t), (.nonePat, e)] =>
      !exitReserved p && exitArgsOk args && (optHeadT A f args p).isSome &&
        exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | tl, il, .match_ (.app f args) [(.nonePat, e), (.somePat (.varPat p), t)] =>
      !exitReserved p && exitArgsOk args && (optHeadT A f args p).isSome &&
        exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | false, _, .whileFoldReturn (.var c) body =>
      !exitReserved c && exitSc A c && exitSimOkT A R false true body
  | false, _, .forFoldReturn i lo hi body =>
      ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) && !exitReserved i &&
        exitSc A i && exitSimOkT A R false true body
  | false, _, .forFoldRevReturn i lo hi body =>
      (forBounds lo hi).isSome && !exitReserved i && exitSc A i &&
        exitSimOkT A R false true body
  | false, true, .forFold i lo hi body =>
      ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) && !exitReserved i &&
        exitSc A i && exitSimOkT A R false true body
  | false, true, .forFoldRev i lo hi body =>
      (forBounds lo hi).isSome && !exitReserved i && exitSc A i &&
        exitSimOkT A R false true body
  | false, true, .whileFold (.var c) body =>
      !exitReserved c && exitSc A c && exitSimOkT A R false true body
  | _, true, .cfBreak p => exitPayloadOk A p
  | tl, _, .var x => !exitReserved x && (!tl || decide (ExitRes.ofPlace (A.lookup x) = R))
  | tl, _, .unitVal => !tl || decide (R = .scalar)
  | true, _, .lit l => exitLitOk l && decide (R = .scalar)
  | true, _, .tuple es => decide (R = .tuple) && exitArgsOk es
  | true, _, .app "None" [] => R.isOption
  | true, _, .app "Some" [.var x] => !exitReserved x && decide (R = .option (A.lookup x))
  | _, _, _ => false

/-- The `match` of the fragment: a call scrutinee with a `Some p` arm and a `None` arm, in
    either order. -/
def exitMatchShape : ImpExpr → List (_root_.Hax.ImpPat × ImpExpr) → Bool
  | .app _ _, [(.somePat (.varPat _), _), (.nonePat, _)] => true
  | .app _ _, [(.nonePat, _), (.somePat (.varPat _), _)] => true
  | _, _ => false

theorem exitMatchShape_cases {s : ImpExpr} {arms : List (_root_.Hax.ImpPat × ImpExpr)}
    (h : exitMatchShape s arms = true) :
    (∃ f args p t e, s = .app f args ∧ arms = [(.somePat (.varPat p), t), (.nonePat, e)]) ∨
      (∃ f args p t e, s = .app f args ∧ arms = [(.nonePat, e), (.somePat (.varPat p), t)]) := by
  unfold exitMatchShape at h
  split at h
  · exact Or.inl ⟨_, _, _, _, _, rfl, rfl⟩
  · exact Or.inr ⟨_, _, _, _, _, rfl, rfl⟩
  · cases h

theorem exitMatchShape_of_ok (A : ExitTowers) (R : ExitRes) {tl il : Bool} {s : ImpExpr}
    {arms : List (_root_.Hax.ImpPat × ImpExpr)}
    (h : exitSimOkT A R tl il (.match_ s arms) = true) : exitMatchShape s arms = true := by
  unfold exitSimOkT at h
  split at h <;> simp_all [exitMatchShape]

/-- The first construct of `e` outside the fragment `exitSimOkT A R tl il`, with the
    reason; `none` when `e` lies in the fragment. -/
def exitSimWhyT (A : ExitTowers) (R : ExitRes) :
    Bool → Bool → ImpExpr → Option String
  | tl, il, .letBind n (.lit l) body =>
      if !exitLitOk l then some "literal not a scalar word"
      else if exitReserved n then some "reserved name" else exitSimWhyT A R tl il body
  | tl, il, .letBind n (.var s) body =>
      if exitReserved n || exitReserved s then some "reserved name"
      else if !decide (A.lookup n = A.lookup s) then some "copy across placements"
      else exitSimWhyT A R tl il body
  | tl, il, .letBind n (.app f args) body =>
      if exitReserved n || !exitArgsOkT f args then
        some "reserved name or non-variable argument"
      else if (appHeadT A n f args).isNone then some s!"letBind app {f}/{args.length} placement"
      else exitSimWhyT A R tl il body
  | tl, il, .seq a b =>
      match exitSimWhyT A R false il a with
      | some r => some r
      | none => exitSimWhyT A R tl il b
  | tl, il, .ifThenElse (.var v) t e =>
      if exitReserved v then some "reserved name"
      else if !exitSc A v then some "condition placed in a tower"
      else
        match exitSimWhyT A R tl il t with
        | some r => some r
        | none => exitSimWhyT A R tl il e
  | tl, il, .typeAscription e _ => exitSimWhyT A R tl il e
  | tl, il, .match_ (.app f args) [(.somePat (.varPat p), t), (.nonePat, e)] =>
      if exitReserved p || !exitArgsOk args then some "reserved name or non-variable argument"
      else if (optHeadT A f args p).isNone then some s!"match {f} option placement"
      else
        match exitSimWhyT A R tl il t with
        | some r => some r
        | none => exitSimWhyT A R tl il e
  | tl, il, .match_ (.app f args) [(.nonePat, e), (.somePat (.varPat p), t)] =>
      if exitReserved p || !exitArgsOk args then some "reserved name or non-variable argument"
      else if (optHeadT A f args p).isNone then some s!"match {f} option placement"
      else
        match exitSimWhyT A R tl il t with
        | some r => some r
        | none => exitSimWhyT A R tl il e
  | false, _, .whileFoldReturn (.var c) body =>
      if exitReserved c then some "reserved name"
      else if !exitSc A c then some "condition placed in a tower"
      else exitSimWhyT A R false true body
  | false, _, .forFoldReturn i lo hi body =>
      if !((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) then some "forFoldReturn bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, _, .forFoldRevReturn i lo hi body =>
      if (forBounds lo hi).isNone then some "forFoldRevReturn bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, true, .forFold i lo hi body =>
      if !((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) then some "forFold bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, true, .forFoldRev i lo hi body =>
      if (forBounds lo hi).isNone then some "forFoldRev bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, true, .whileFold (.var c) body =>
      if exitReserved c then some "reserved name"
      else if !exitSc A c then some "condition placed in a tower"
      else exitSimWhyT A R false true body
  | _, true, .cfBreak p => if exitPayloadOk A p then none else some "break payload not scalar"
  | tl, _, .var x =>
      if exitReserved x then some "reserved name"
      else if tl && !decide (ExitRes.ofPlace (A.lookup x) = R) then some "tail placement"
      else none
  | tl, _, .unitVal => if !tl || decide (R = .scalar) then none else some "tail placement"
  | true, _, .lit l =>
      if exitLitOk l && decide (R = .scalar) then none else some "tail literal"
  | true, _, .tuple es =>
      if decide (R = .tuple) && exitArgsOk es then none else some "tail tuple"
  | true, _, .app "None" [] => if R.isOption then none else some "tail None"
  | true, _, .app "Some" [.var x] =>
      if !exitReserved x && decide (R = .option (A.lookup x)) then none else some "tail Some"
  | _, _, .letBind _ v _ => some s!"letBind {exitWhyHead v}"
  | tl, il, e => some s!"{exitWhyHead e} (tail {tl}, loop {il})"

theorem exitSimWhyT_eq_none_iff (A : ExitTowers) (R : ExitRes) (tl il : Bool)
    (e : ImpExpr) : exitSimWhyT A R tl il e = none ↔ exitSimOkT A R tl il e = true := by
  fun_induction exitSimWhyT A R tl il e <;>
    (try simp_all [exitSimOkT, Option.isSome_iff_ne_none]) <;>
    (try intros) <;> (try first | omega | tauto | simp_all)
  rename_i tl _ x _ h
  cases tl
  · exact Or.inl rfl
  · exact Or.inr (h rfl)

/-! ## §7  Scalar values and agreement under a placement -/

open CatCrypt.Crypto.Jasmin.LowCT (rsSetTower locatedLookup locatedUpdate RustVal towerLimb
  rsTowerLimb)

/-- A scalar value: an unsigned word below `2^64` of any width, a bool, an integer in
    `[0, 2^64)`, or the unit. -/
def ScalarValN : Value → Prop
  | .uint _ n => n < 2 ^ 64
  | .bool _ => True
  | .int n => 0 ≤ n ∧ n < 2 ^ 64
  | .unit => True
  | _ => False

theorem ScalarValN.not_cf {v : Value} (h : ScalarValN v) : v.isControlFlow = false := by
  cases v <;> first | rfl | exact h.elim

/-- The four shapes of a scalar value. -/
theorem ScalarValN.cases {v : Value} (h : ScalarValN v) :
    (∃ w n, v = .uint w n ∧ n < 2 ^ 64) ∨ (∃ b, v = .bool b) ∨
      (∃ n : Int, v = .int n ∧ 0 ≤ n ∧ n < 2 ^ 64) ∨ v = .unit := by
  match v, h with
  | .uint w n, h => exact Or.inl ⟨w, n, rfl, h⟩
  | .bool b, _ => exact Or.inr (Or.inl ⟨b, rfl⟩)
  | .int n, h => exact Or.inr (Or.inr (Or.inl ⟨n, rfl, h⟩))
  | .unit, _ => exact Or.inr (Or.inr (Or.inr rfl))

theorem ScalarValN.of_scalarVal {v : Value} (h : ScalarVal v) : ScalarValN v := by
  match v, h with
  | .uint .w64 _, h => exact h
  | .bool _, _ => trivial
  | .int _, h => exact h

/-- Agreement under the placement `A`: every binding of a non-reserved name placed in
    the scalar heap is a scalar value whose decoding is its scalar slot; every binding
    of a name placed in a tower at `t` is a value without a control-flow tag related by
    `br` to the tower slot of that name, which holds type `t`. -/
def envAgreesT (br : ValueTowerBridge) (A : ExitTowers) (env : Env) (rs : RustState) : Prop :=
  ∀ name v, exitReserved name = false → env name = some v →
    match A.lookup name with
    | none => ScalarValN v ∧ valueToScalar v = some (rs.rsScalar name)
    | some t => v.isControlFlow = false ∧ ∃ val, rs.rsTower name = some ⟨t, val⟩ ∧ br t v val

section Agreement

variable {br : ValueTowerBridge} {A : ExitTowers} {env : Env} {rs : RustState}

theorem envAgreesT_scalar (h : envAgreesT br A env rs) {x : String} {v : Value}
    (hx : exitReserved x = false) (hs : A.lookup x = none) (hv : env x = some v) :
    ScalarValN v ∧ valueToScalar v = some (rs.rsScalar x) := by
  have h' := h x v hx hv
  rw [hs] at h'
  exact h'

theorem envAgreesT_tower (h : envAgreesT br A env rs) {x : String} {v : Value} {t : TowerType}
    (hx : exitReserved x = false) (ht : A.lookup x = some t) (hv : env x = some v) :
    v.isControlFlow = false ∧ ∃ val, rs.rsTower x = some ⟨t, val⟩ ∧ br t v val := by
  have h' := h x v hx hv
  rw [ht] at h'
  exact h'

theorem envAgreesT_not_cf (h : envAgreesT br A env rs) {x : String} {v : Value}
    (hx : exitReserved x = false) (hv : env x = some v) : v.isControlFlow = false := by
  rcases hA : A.lookup x with _ | t
  · exact (envAgreesT_scalar h hx hA hv).1.not_cf
  · exact (envAgreesT_tower h hx hA hv).1

/-- Writing a reserved scalar slot preserves agreement. -/
theorem envAgreesT_set_reserved {x : String} (k : Nat) (hx : exitReserved x = true)
    (h : envAgreesT br A env rs) : envAgreesT br A env (rsSetScalar rs x k) := by
  intro name w hn hw
  have h' := h name w hn hw
  rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
  · rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn hx)]
    exact h'
  · exact h'

/-- Writing a reserved tower slot preserves agreement. -/
theorem envAgreesT_setTower_reserved {x : String} (s : Σ t, RustVal t)
    (hx : exitReserved x = true) (h : envAgreesT br A env rs) :
    envAgreesT br A env (rsSetTower rs x s) := by
  intro name w hn hw
  have h' := h name w hn hw
  rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
  · exact h'
  · rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs x name s (ne_of_reserved hn hx).symm]
    exact h'

/-- Binding a non-reserved scalar name to a scalar value and writing its decoding into
    its scalar slot preserves agreement. -/
theorem envAgreesT_extend {n : String} {v : Value} {k : Nat} (hn : exitReserved n = false)
    (hs : A.lookup n = none) (hv : ScalarValN v) (hk : valueToScalar v = some k)
    (h : envAgreesT br A env rs) : envAgreesT br A (env.extend n v) (rsSetScalar rs n k) := by
  intro name w hname hw
  by_cases he : name = n
  · subst he
    simp only [_root_.Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    rw [hs]
    exact ⟨hv, by simpa using hk⟩
  · simp only [_root_.Hax.Env.extend, beq_iff_eq, he, if_false] at hw
    have h' := h name w hname hw
    rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
    · rw [rsScalar_rsSetScalar, if_neg he]
      exact h'
    · exact h'

/-- Binding a non-reserved tower name to a value related to a tower value, and writing
    that tower value into its slot, preserves agreement. -/
theorem envAgreesT_extend_tower {n : String} {v : Value} {t : TowerType} {val : RustVal t}
    (hn : exitReserved n = false) (ht : A.lookup n = some t) (hcf : v.isControlFlow = false)
    (hbr : br t v val) (h : envAgreesT br A env rs) :
    envAgreesT br A (env.extend n v) (rsSetTower rs n ⟨t, val⟩) := by
  intro name w hname hw
  by_cases he : name = n
  · subst he
    simp only [_root_.Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    rw [ht]
    exact ⟨hcf, val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same rs name _, hbr⟩
  · simp only [_root_.Hax.Env.extend, beq_iff_eq, he, if_false] at hw
    have h' := h name w hname hw
    rcases hA : A.lookup name with _ | u <;> rw [hA] at h'
    · exact h'
    · rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs n name _ (Ne.symm he)]
      exact h'

/-- Agreement off the reserved names is agreement under the empty placement. -/
theorem envAgreesT_nil_of_off (h : envAgreesOff env rs) : envAgreesT br [] env rs := by
  intro name v hn hv
  obtain ⟨hs, hd⟩ := h name v hn hv
  exact ⟨ScalarValN.of_scalarVal hs, hd⟩

end Agreement

/-- The agreement of a component `w` of a tuple result with its slot: a scalar word whose
    decoding is the scalar slot, or a value related by `br` to the tower slot at the type
    the slot holds. -/
def compAgreesT (br : ValueTowerBridge) (slot : String) (w : Value) (rs : RustState) : Prop :=
  (ScalarValN w ∧ valueToScalar w = some (rs.rsScalar slot)) ∨
    ∃ t val, rs.rsTower slot = some ⟨t, val⟩ ∧ br t w val

/-- The agreement of a payload `w` held under the placement `p` with the slot `slot`: a
    scalar word decoding to the scalar slot for `p = none`, and a value related by `br` to
    the tower slot at `t` for `p = some t`. -/
def payloadAgreesT (br : ValueTowerBridge) (p : Option TowerType) (slot : String) (w : Value)
    (rs : RustState) : Prop :=
  match p with
  | none => ScalarValN w ∧ valueToScalar w = some (rs.rsScalar slot)
  | some t => ∃ val, rs.rsTower slot = some ⟨t, val⟩ ∧ br t w val

/-- The result agreement for result placement `R`: the decoding of `v` in the scalar
    result slot, `v` related by `br` to the tower result slot, `v` a tuple whose
    component `i` agrees with the slot `exitResCompName i` (`compAgreesT`), or `v` an
    `Option` whose tag `0` or `1` is the scalar result slot and whose payload agrees with
    the slot `exitResCompName 0` (`payloadAgreesT`). -/
def resultAgreesT (br : ValueTowerBridge) (R : ExitRes) (v : Value) (rs : RustState) :
    Prop :=
  match R with
  | .scalar => valueToScalar v = some (rs.rsScalar exitResName)
  | .tower t => ∃ val, rs.rsTower exitResName = some ⟨t, val⟩ ∧ br t v val
  | .tuple => ∃ vs, v = .tuple vs ∧
      ∀ (i : Nat) (w : Value), vs[i]? = some w → compAgreesT br (exitResCompName i) w rs
  | .option p => (v = .option none ∧ rs.rsScalar exitResName = 0) ∨
      ∃ w, v = .option (some w) ∧ rs.rsScalar exitResName = 1 ∧
        payloadAgreesT br p (exitResCompName 0) w rs

/-- Agreement with the exit component under the placement `A` and result placement
    `R`, for an expression in tail position `tl`. -/
def envAgreesExitT (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (tl : Bool) : Outcome → Env → RustState → Prop
  | .val (.controlFlow true v), env, rs =>
      rs.rsScalar exitRetName = 1 ∧ valueToScalar v = some (rs.rsScalar exitValName) ∧
        envAgreesT br A env rs
  | .val (.controlFlow false _), _, _ => False
  | .val v, env, rs =>
      rs.rsScalar exitRetName = 0 ∧ envAgreesT br A env rs ∧
        (tl = true → resultAgreesT br R v rs)
  | _, _, _ => False

section ExitAgreement

variable {br : ValueTowerBridge} {A : ExitTowers} {R : ExitRes}

theorem envAgreesExitT_val {tl : Bool} {v : Value} {env : Env} {rs : RustState}
    (hv : v.isControlFlow = false) :
    envAgreesExitT br A R tl (.val v) env rs ↔
      (rs.rsScalar exitRetName = 0 ∧ envAgreesT br A env rs ∧
        (tl = true → resultAgreesT br R v rs)) := by
  cases v <;> first | exact Iff.rfl | simp at hv

theorem envAgreesExitT_reset {env : Env} {rs : RustState} {v : Value}
    (hag : envAgreesT br A env rs) (hv : v.isControlFlow = false) :
    envAgreesExitT br A R false (.val v) env (rsSetScalar rs exitRetName 0) :=
  (envAgreesExitT_val hv).mpr ⟨by simp [rsScalar_rsSetScalar],
    envAgreesT_set_reserved _ exitReserved_ret hag, fun h => by cases h⟩

/-- Writing the scalar result slot preserves the exit flag and agreement. -/
theorem res_writeT (rs : RustState) (k : Nat) {env : Env} (h0 : rs.rsScalar exitRetName = 0)
    (hag : envAgreesT br A env rs) :
    (rsSetScalar rs exitResName k).rsScalar exitRetName = 0 ∧
      envAgreesT br A env (rsSetScalar rs exitResName k) ∧
      (rsSetScalar rs exitResName k).rsScalar exitResName = k := by
  refine ⟨?_, envAgreesT_set_reserved k exitReserved_res hag, by simp⟩
  rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_res, h0]

end ExitAgreement

/-- A state with the scalar heap of `rs` and the tower slots of `rs` at every name other
    than the marshalling slots agrees with every environment `rs` agrees with. -/
theorem envAgreesT_of_eqOn {br : ValueTowerBridge} {A : ExitTowers} {env : Env}
    {rs rs1 : RustState} (hS : rs1.rsScalar = rs.rsScalar)
    (hT : ∀ y, exitReserved y = false → rs1.rsTower y = rs.rsTower y)
    (h : envAgreesT br A env rs) : envAgreesT br A env rs1 := by
  intro name w hn hw
  have h' := h name w hn hw
  rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
  · rw [hS]; exact h'
  · rw [hT name hn]; exact h'

/-! ## §8  Scalar operations and leaf conditions -/

/-- hax-lean's scalar operation `op` on scalars, as `LowCT` computes it: the value of
    `scalarOpExprT op` on the literals `a` and `b`, and `0` for an operation outside
    `scalarOpExprT`. -/
def scalarOpNatT (op : String) (a b : Nat) : Nat :=
  match scalarOpExprT op (.SLit a) (.SLit b) with
  | some se => se.eval fun _ => 0
  | none => 0

theorem widthOp_sexpr_congr (w : Nat) (o : WidthOp) {a b a' b' : SExpr} {rs : RustState}
    {σ : String → Nat} (ha : a.evalState rs = a'.eval σ) (hb : b.evalState rs = b'.eval σ) :
    (o.sexpr w a b).evalState rs = (o.sexpr w a' b').eval σ := by
  cases o <;> simp only [WidthOp.sexpr, widthMask, orExprN, widthAmt, SExpr.evalState,
    SExpr.eval, ha, hb]

/-- The value of a scalar operation depends only on the values of its operands. -/
theorem scalarOpExprT_congr (op : String) {a b a' b' : SExpr} {rs : RustState}
    {σ : String → Nat} (ha : a.evalState rs = a'.eval σ) (hb : b.evalState rs = b'.eval σ) :
    (scalarOpExprT op a b).map (·.evalState rs) = (scalarOpExprT op a' b').map (·.eval σ) := by
  unfold scalarOpExprT
  split
  all_goals try simp only [Option.map_some, SExpr.evalState, SExpr.eval, orExprN, ha, hb]
  rcases widthOpOf op with _ | ⟨w, o⟩
  · rfl
  · simp only [Option.map_some, widthOp_sexpr_congr w o ha hb]

/-- The `SExpr` of a scalar operation on two scalar slots evaluates to
    `scalarOpNatT`. -/
theorem scalarOpExprT_evalState (op x y : String) (se : SExpr) (rs : RustState)
    (h : scalarOpExprT op (.SVar x) (.SVar y) = some se) :
    se.evalState rs = scalarOpNatT op (rs.rsScalar x) (rs.rsScalar y) := by
  have hc := scalarOpExprT_congr op (a := .SVar x) (b := .SVar y)
    (a' := .SLit (rs.rsScalar x)) (b' := .SLit (rs.rsScalar y)) (rs := rs) (σ := fun _ => 0)
    rfl rfl
  rw [h] at hc
  unfold scalarOpNatT
  rcases h' : scalarOpExprT op (.SLit (rs.rsScalar x)) (.SLit (rs.rsScalar y)) with _ | se'
  · rw [h'] at hc; cases hc
  · rw [h'] at hc
    simpa using hc

theorem scalarOpExprT_isSome_vars (op x y x' y' : String) :
    (scalarOpExprT op (.SVar x) (.SVar y)).isSome =
      (scalarOpExprT op (.SVar x') (.SVar y')).isSome := by
  unfold scalarOpExprT
  split <;> try rfl
  rcases widthOpOf op with _ | ⟨w, o⟩ <;> rfl

/-- The builtin table computes every operation of `scalarOpExprT` on scalar values as a
    scalar value decoding to `scalarOpNatT`. -/
def ScalarOpsSoundT (bi : Builtins) : Prop :=
  ∀ op va vb r na nb,
    (scalarOpExprT op (.SVar "a") (.SVar "b")).isSome = true →
    ScalarValN va → ScalarValN vb →
    valueToScalar va = some na → valueToScalar vb = some nb →
    bi op [va, vb] = some r →
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT op na nb)

/-- The leaf condition of a call with a scalar result: when every argument value is
    related by `br` to the tower value the call reads, the builtin's result is a scalar
    value whose decoding is limb `0` of the leaf output. -/
def LeafCallScalar (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    ScalarValN vRes ∧
      valueToScalar vRes = some (towerLimb (leafSpec.call f dt (args.map (·.locDst)) oldV argList) 0)

/-- The element load agrees with the builtin `index` on an array of words: for an array
    value related by `br` to a slot of a type `t` whose elements are words
    (`exitElemTower t = none`) and an index decoding to `k`, the builtin's result is a
    scalar value whose decoding is limb `0` of the element the leaf loads. -/
def IndexScalarAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (t : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
    exitElemTower t = none →
    br t vArr arrV → valueToScalar vIdx = some k →
    bi "index" [vArr, vIdx] = some vRes →
    ScalarValN vRes ∧ valueToScalar vRes = some
      (towerLimb (leafSpec.arrLoad { locVar := exitCallName, locSrc := .TFp } default ⟨t, arrV⟩ k) 0)

/-- The element load agrees with the builtin `index` on an array of tower values: for an
    array value related by `br` to a slot of a type `t` whose elements have the tower type
    `t'` (`exitElemTower t = some t'`) and an index decoding to `k`, the builtin's result is
    related by `br` at `t'` to the element the leaf loads. -/
def IndexTowerAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (t t' : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
    exitElemTower t = some t' →
    br t vArr arrV → valueToScalar vIdx = some k →
    bi "index" [vArr, vIdx] = some vRes →
    br t' vRes (leafSpec.arrLoad { locVar := exitCallName, locSrc := t' } default ⟨t, arrV⟩ k)

/-- The element store agrees with the builtin `array_update` on an array of words: for an
    array value related by `br` to a slot of a type `t` whose elements are words
    (`exitElemTower t = none`, so that `exitElem t = t.elemType`), an index decoding to
    `k`, and a scalar word decoding to `m`, the builtin's result is related at `t` to the
    store at element `k` of the word `m` marshalled into limb `0` of a fresh slot of type
    `exitElem t` named `z`. -/
def ArrUpdateWordAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (arr z : String) (t : TowerType) (vArr vIdx vSrc vRes : Value) (arrV : RustVal t)
    (k m : Nat),
    exitElemTower t = none → 8 ≤ (exitElem t).storageBytes →
    br t vArr arrV → valueToScalar vIdx = some k →
    ScalarValN vSrc → valueToScalar vSrc = some m →
    bi "array_update" [vArr, vIdx, vSrc] = some vRes →
    br t vRes (leafSpec.arrStore { locVar := arr, locSrc := t } arrV k
      ⟨exitElem t, leafSpec.limbStore ⟨z, exitElem t⟩ default 0 (BitVec.ofNat 64 m)⟩)

/-- The element store agrees with the builtin `array_update` on an array of tower values:
    for an array value related by `br` to a slot of a type `t` whose elements are tower
    values (`exitElemTower t ≠ none`, of type `exitElem t`), an index decoding to `k`, and a
    value related at `exitElem t` to `srcV`, the builtin's result is related at `t` to the
    store of `srcV` at element `k`. -/
def ArrUpdateTowerAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (arr : String) (t : TowerType) (vArr vIdx vSrc vRes : Value) (arrV : RustVal t)
    (srcV : RustVal (exitElem t)) (k : Nat),
    exitElemTower t ≠ none →
    br t vArr arrV → valueToScalar vIdx = some k →
    br (exitElem t) vSrc srcV →
    bi "array_update" [vArr, vIdx, vSrc] = some vRes →
    br t vRes (leafSpec.arrStore { locVar := arr, locSrc := t } arrV k ⟨exitElem t, srcV⟩)

/-- The marshalling of a scalar word into limb `0` of a fresh tower slot of at least `8`
    bytes is related by `br` to the word. -/
def ExitMarshal (br : ValueTowerBridge) (leafSpec : LeafSpec) : Prop :=
  ∀ (loc : Located) (v : Value) (k : Nat), 8 ≤ loc.locDst.storageBytes →
    ScalarValN v → valueToScalar v = some k →
    br loc.locDst v (leafSpec.limbStore loc default 0 (BitVec.ofNat 64 k))

/-- `LeafCallAgreesArgs` on the argument lists of `k` values: the leaf condition of a call
    whose result has a fixed number `k` of elements. -/
def LeafCallAgreesArgsLen (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (k : Nat) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    vals.length = k → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    br dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

theorem leafCallAgreesArgsLen_of {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (h : LeafCallAgreesArgs bi leafSpec f dt br)
    (k : Nat) : LeafCallAgreesArgsLen bi leafSpec f dt br k :=
  fun args vals argList oldV vRes _ hbi hF => h args vals argList oldV vRes hbi hF

/-- The leaf condition of `repeat(v, cnt)` at an array type `c` of `k` elements: when the
    count decodes to `k` and the value of `v` is related by `br` to the one slot the call
    reads, the builtin's result is related at `c` to the leaf output. -/
def LeafRepeatAgrees (bi : Builtins) (leafSpec : LeafSpec) (c : TowerType)
    (br : ValueTowerBridge) (k : Nat) : Prop :=
  ∀ (args : List Located) (vv vc vRes : Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal c),
    valueToScalar vc = some k → bi "repeat" [vv, vc] = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) [vv] argList →
    br c vRes (leafSpec.call "repeat" c (args.map (·.locDst)) oldV argList)

/-- The relation of a payload `w` of an `Option` held at the payload type `t` to the leaf
    output `out`: a scalar word decoding to limb `0` for `t = TU64`, and `br t` otherwise. -/
def optPayloadRel (br : ValueTowerBridge) (t : TowerType) (w : Value) (out : RustVal t) :
    Prop :=
  if t = .TU64 then ScalarValN w ∧ valueToScalar w = some (towerLimb out 0) else br t w out

/-- The leaf condition of a call `f` returning an `Option` with payload type `t`, run as
    the two-output call `RCallN f [tag, payload]`: when the argument values are related by
    `br` to the slots the call reads, the builtin returns an `Option`, output `0` holds its
    tag `1` or `0` in limb `0`, and output `1` is related to a payload by `optPayloadRel`. -/
def LeafCallOption (bi : Builtins) (leafSpec : LeafSpec) (f : String) (t : TowerType)
    (br : ValueTowerBridge) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldT : RustVal .TU64) (oldP : RustVal t) (vRes : Value),
    bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    ∃ o, vRes = .option o ∧
      towerLimb (leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 0) .TU64
        (args.map (·.locDst)) oldT argList) 0 = (if o.isSome then 1 else 0) ∧
      ∀ w, o = some w → w.isControlFlow = false ∧
        optPayloadRel br t w (leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 1) t
          (args.map (·.locDst)) oldP argList)

/-- A builtin table that does not implement `f` satisfies `LeafCallOption`. -/
theorem leafCallOption_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (t : TowerType) (br : ValueTowerBridge) (h : ∀ vals, bi f vals = none) :
    LeafCallOption bi leafSpec f t br := by
  intro _ vals _ _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-- The builtins `None` and `Some` build `Option` values. -/
def OptCtors (bi : Builtins) : Prop :=
  (∀ vals r, bi "None" vals = some r → vals = [] ∧ r = .option none) ∧
    (∀ vals r, bi "Some" vals = some r → ∃ v, vals = [v] ∧ r = .option (some v))

/-- A builtin table that does not implement `repeat` satisfies `LeafRepeatAgrees`. -/
theorem leafRepeatAgrees_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (c : TowerType)
    (br : ValueTowerBridge) (k : Nat) (h : ∀ vals, bi "repeat" vals = none) :
    LeafRepeatAgrees bi leafSpec c br k := by
  intro _ vv vc _ _ _ _ hBi
  rw [h [vv, vc]] at hBi
  cases hBi

/-- A builtin table that does not implement `f` satisfies `LeafCallAgreesArgsLen`. -/
theorem leafCallAgreesArgsLen_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (dt : TowerType) (br : ValueTowerBridge) (k : Nat) (h : ∀ vals, bi f vals = none) :
    LeafCallAgreesArgsLen bi leafSpec f dt br k := by
  intro _ vals _ _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-- `LeafCallAgreesArgsLen` on argument slots of the type `e`: the leaf condition of a call
    whose result has `k` elements and whose argument slots all have the type `e`. -/
def LeafCallAgreesArgsAt (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (k : Nat) (e : TowerType) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    vals.length = k → (∀ p ∈ argList, p.1 = e) → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    br dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

theorem leafCallAgreesArgsAt_of_len {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} {k : Nat}
    (h : LeafCallAgreesArgsLen bi leafSpec f dt br k) (e : TowerType) :
    LeafCallAgreesArgsAt bi leafSpec f dt br k e :=
  fun args vals argList oldV vRes hl _ hbi hF => h args vals argList oldV vRes hl hbi hF

/-- The leaf condition of `f` on argument slots of the types `ts`: argument `i` read from a
    slot of type `ts[i]`. -/
def LeafCallAgreesArgsTys (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (ts : List TowerType) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    argList.map (·.1) = ts → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    br dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

theorem leafCallAgreesArgsTys_of {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (h : LeafCallAgreesArgs bi leafSpec f dt br)
    (ts : List TowerType) : LeafCallAgreesArgsTys bi leafSpec f dt br ts :=
  fun args vals argList oldV vRes _ hbi hF => h args vals argList oldV vRes hbi hF

/-- `LeafCallScalar` on argument slots of the types `ts`. -/
def LeafCallScalarTys (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (ts : List TowerType) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    argList.map (·.1) = ts → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    ScalarValN vRes ∧
      valueToScalar vRes = some (towerLimb (leafSpec.call f dt (args.map (·.locDst)) oldV argList) 0)

/-- The leaf conditions of the typed simulation, for the declared call result types `D`
    (by default none): the scalar operations, the absence of control-flow results, the
    storage of a scalar into limb `0` of a fresh tower slot of at least `8` bytes, the
    calls with a tower result without a declared type at `towerOfCallName f`
    (`LeafCallAgreesArgs`, for every call other than the array operations `index`,
    `array_update`, `array_lit`, `repeat`) and with a
    scalar result (`LeafCallScalar`, for the scalar calls and for the leaves of
    `exitTowerScalarNames`), the element load and the element store on an array of words
    and on an array of tower values, the array literal of `k` values at each array type of
    `k` elements (`arrLitN`), the `repeat` with count `k` at each such type (`repeatN`),
    the calls other than the array operations with a declared
    result type `dr` at `dr` (`callD`) and, for a declared word result `TU64`, with a scalar
    result (`wordD`), the calls returning an `Option` with a declared payload type
    `t` of `DO` (`optD`), the linked callees of `DA` with argument slot types `ts` and
    result type `dr` on argument slots of the types `ts` (`callA`, and `wordA` for a word
    result), and the `Option` constructors `None` and `Some` (`optCtors`).  `callD`,
    `wordD`, `optD`, `callA` and `wordA` hold for the default `D`, `DO` and `DA`. -/
structure ExitLeaves (bi : Builtins) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (D : String → Option TowerType := fun _ => none)
    (DO : String → Option TowerType := fun _ => none)
    (DA : String → Option (List TowerType × TowerType) := fun _ => none) : Prop where
  ops : ScalarOpsSoundT bi
  plain : _root_.Hax.ContinueFlag.BuiltinsPlain bi
  marshal : ExitMarshal br leafSpec
  callT : ∀ f, exitScalarRes f = false → f ≠ "index" → f ≠ "array_update" →
    f ≠ "array_lit" → f ≠ "repeat" → DA f = none →
    LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) br
  callS : ∀ f, exitScalarCall f = true → LeafCallScalar bi leafSpec f (towerOfCallName f) br
  /-- The leaf calls of `exitTowerScalarNames`, whose arguments are related by `br` to
      tower values and whose result is a scalar word read from limb `0` of the leaf
      output, with no bridge on the result. -/
  callTS : ∀ f, exitTowerScalarCall f = true →
    LeafCallScalar bi leafSpec f (towerOfCallName f) br
  index : IndexScalarAgrees br bi leafSpec
  update : ArrUpdateWordAgrees br bi leafSpec
  indexT : IndexTowerAgrees br bi leafSpec
  updateT : ArrUpdateTowerAgrees br bi leafSpec
  /-- The array literal of `k` values held at an array type `c` of `k` elements whose
      element type holds a word, read from argument slots of the element type
      `exitElem c`. -/
  arrLitN : ∀ c k, exitArrLen c = some k → exitMarshalOk (exitElem c) = true →
    LeafCallAgreesArgsAt bi leafSpec "array_lit" c br k (exitElem c)
  /-- The `repeat` with count `k` held at an array type `c` of `k` elements whose element
      type holds a word. -/
  repeatN : ∀ c k, exitArrLen c = some k → exitMarshalOk (exitElem c) = true →
    LeafRepeatAgrees bi leafSpec c br k
  /-- A call outside `exitScalarRes` and the array operations with the declared result type
      `dr` agrees at `dr`. -/
  callD : ∀ f dr, D f = some dr → DO f = none → DA f = none → exitScalarRes f = false →
    f ≠ "index" → f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallAgreesArgs bi leafSpec f dr br := by
    intro f dr h; simp at h
  /-- A call outside `exitScalarRes` and the array operations with the declared word result
      `TU64` returns a scalar word whose decoding is limb `0` of the leaf output at `TU64`. -/
  wordD : ∀ f, D f = some .TU64 → DA f = none → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallScalar bi leafSpec f .TU64 br := by
    intro f h; simp at h
  /-- A linked callee with argument slot types `ts` and result type `dr` agrees at `dr` on
      argument slots of the types `ts`. -/
  callA : ∀ f ts dr, DA f = some (ts, dr) → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallAgreesArgsTys bi leafSpec f dr br ts := by
    intro f ts dr h; simp at h
  /-- A linked callee with argument slot types `ts` and the word result `TU64` returns, on
      argument slots of the types `ts`, a scalar word whose decoding is limb `0` of the leaf
      output. -/
  wordA : ∀ f ts, DA f = some (ts, .TU64) → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallScalarTys bi leafSpec f .TU64 br ts := by
    intro f ts h; simp at h
  /-- A call outside `exitScalarRes` and the array operations with the declared `Option`
      payload type `t` satisfies `LeafCallOption` at `t`. -/
  optD : ∀ f t, DO f = some t → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallOption bi leafSpec f t br := by
    intro f t h; simp at h
  /-- The builtins `None` and `Some` build `Option` values. -/
  optCtors : OptCtors bi

/-- The leaf conditions for the declared types `D`, `DO` and the linked callees `DA` give
    those for any `D'`, `DO'`, `DA'` declaring fewer, when no name `D'` declares is declared
    by `DO`, and every name without a linked callee in `DA'` has none in `DA`. -/
theorem ExitLeaves.mono {bi : Builtins} {leafSpec : LeafSpec} {br : ValueTowerBridge}
    {D D' DO DO' : String → Option TowerType}
    {DA DA' : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA)
    (h : ∀ f dr, D' f = some dr → D f = some dr)
    (hO : ∀ f t, DO' f = some t → DO f = some t)
    (hdisj : ∀ f dr, D' f = some dr → DO f = none)
    (hA : ∀ f x, DA' f = some x → DA f = some x)
    (hA' : ∀ f, DA' f = none → DA f = none) : ExitLeaves bi leafSpec br D' DO' DA' where
  ops := hL.ops
  plain := hL.plain
  marshal := hL.marshal
  callT f hsc h1 h2 h3 h4 hda := hL.callT f hsc h1 h2 h3 h4 (hA' f hda)
  callS := hL.callS
  callTS := hL.callTS
  index := hL.index
  update := hL.update
  indexT := hL.indexT
  updateT := hL.updateT
  arrLitN := hL.arrLitN
  repeatN := hL.repeatN
  callD f dr hf _ hda := hL.callD f dr (h f dr hf) (hdisj f dr hf) (hA' f hda)
  wordD f hf hda := hL.wordD f (h f _ hf) (hA' f hda)
  optD f t hf := hL.optD f t (hO f t hf)
  callA f ts dr hf := hL.callA f ts dr (hA f _ hf)
  wordA f ts hf := hL.wordA f ts (hA f _ hf)
  optCtors := hL.optCtors

/-- The leaf conditions for the placement `exitTowers e`, which declares no call result
    type and records no linked callee. -/
theorem ExitLeaves.atExitTowers {bi : Builtins} {leafSpec : LeafSpec} {br : ValueTowerBridge}
    (hL : ExitLeaves bi leafSpec br) (e : ImpExpr) :
    ExitLeaves bi leafSpec br (exitCallTys (exitTowers e)) (exitOptTys (exitTowers e))
      (exitCalleeTys (exitTowers e)) :=
  hL.mono (fun f dr h => by rw [exitCallTys_exitTowers] at h; cases h)
    (fun f t h => by rw [exitOptTys_exitTowers] at h; cases h) (fun _ _ _ => rfl)
    (fun f x h => by rw [exitCalleeTys_exitTowers] at h; cases h) (fun _ _ => rfl)

/-- Every call of `exitScalarRes` satisfies `LeafCallScalar`. -/
theorem ExitLeaves.callSR {bi : Builtins} {leafSpec : LeafSpec} {br : ValueTowerBridge}
    {D DO : String → Option TowerType} {DA : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA) {f : String} (hf : exitScalarRes f = true) :
    LeafCallScalar bi leafSpec f (towerOfCallName f) br := by
  unfold exitScalarRes at hf
  rcases Bool.or_eq_true_iff.mp hf with h | h
  · exact hL.callS f h
  · exact hL.callTS f h

/-- A builtin table that does not implement `f` satisfies the scalar leaf condition. -/
theorem leafCallScalar_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (dt : TowerType) (br : ValueTowerBridge) (h : ∀ vals, bi f vals = none) :
    LeafCallScalar bi leafSpec f dt br := by
  intro _ vals _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-- `ScalarValN` as a Boolean test. -/
def scalarValNB : Value → Bool
  | .uint _ n => decide (n < 2 ^ 64)
  | .bool _ => true
  | .int n => decide (0 ≤ n) && decide (n < 2 ^ 64)
  | .unit => true
  | _ => false

theorem scalarValNB_iff (v : Value) : scalarValNB v = true ↔ ScalarValN v := by
  cases v <;> simp [scalarValNB, ScalarValN]

/-- A call whose result the range-refusing table `exitRange` checks: a call of
    `exitScalarRes`.  An element load is not checked: its result is a word or a tower value
    according to the tower type of the array (`IndexScalarAgrees`, `IndexTowerAgrees`). -/
def exitScalarResult (f : String) : Bool := exitScalarRes f

/-- The table `bi` with every scalar result outside `ScalarValN` refused: a call of
    `exitScalarResult` whose result is not a scalar word returns `none`.  A run of `denote'`
    over this table that ends in a value is a run of `bi` whose scalar results are scalar
    words. -/
def exitRange (bi : Builtins) : Builtins := fun f vals =>
  match bi f vals with
  | some r => if exitScalarResult f && !scalarValNB r then none else some r
  | none => none

theorem exitRange_some {bi : Builtins} {f : String} {vals : List Value} {r : Value}
    (h : exitRange bi f vals = some r) :
    bi f vals = some r ∧ (exitScalarResult f = true → ScalarValN r) := by
  unfold exitRange at h
  rcases hb : bi f vals with _ | r'
  · rw [hb] at h; cases h
  · rw [hb] at h
    simp only at h
    split_ifs at h with hc
    cases h
    refine ⟨rfl, fun hs => ?_⟩
    simp only [hs, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    exact (scalarValNB_iff r).mp (by simpa using hc)

theorem exitRange_of_not_scalar {bi : Builtins} {f : String} (hf : exitScalarResult f = false)
    (vals : List Value) : exitRange bi f vals = bi f vals := by
  unfold exitRange
  rcases bi f vals with _ | r
  · rfl
  · simp [hf]

theorem builtinsPlain_exitRange {bi : Builtins} (h : _root_.Hax.ContinueFlag.BuiltinsPlain bi) :
    _root_.Hax.ContinueFlag.BuiltinsPlain (exitRange bi) :=
  fun f args v hv => h f args v (exitRange_some hv).1

/-- A leaf of a call with a tower result agrees on the range-refusing table when it agrees
    on the table. -/
theorem leafCallAgreesArgs_exitRange {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (h : LeafCallAgreesArgs bi leafSpec f dt br) :
    LeafCallAgreesArgs (exitRange bi) leafSpec f dt br :=
  fun args vals argList oldV vRes hbi hF => h args vals argList oldV vRes (exitRange_some hbi).1 hF

/-- A leaf of a call with a scalar result agrees on the range-refusing table when, on
    every scalar-word result of the table, limb `0` of the leaf output is its decoding. -/
theorem leafCallScalar_exitRange {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (hf : exitScalarRes f = true)
    (h : ∀ (args : List Located) (vals : List Value)
      (argList : List (Σ t : TowerType, RustVal t)) (oldV : RustVal dt) (vRes : Value),
      bi f vals = some vRes →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
      ScalarValN vRes →
      valueToScalar vRes = some (towerLimb (leafSpec.call f dt (args.map (·.locDst)) oldV argList) 0)) :
    LeafCallScalar (exitRange bi) leafSpec f dt br := by
  intro args vals argList oldV vRes hbi hF
  obtain ⟨hb, hs⟩ := exitRange_some hbi
  have hsv := hs (by simp [exitScalarResult, hf])
  exact ⟨hsv, h args vals argList oldV vRes hb hF hsv⟩

theorem exitRange_index {bi : Builtins} (vals : List Value) :
    exitRange bi "index" vals = bi "index" vals :=
  exitRange_of_not_scalar exitScalarRes_index vals

/-- The range-refusing table leaves `index` unchanged, so the element loads agree on it when
    they agree on the table. -/
theorem indexScalarAgrees_exitRange {br : ValueTowerBridge} {bi : Builtins}
    {leafSpec : LeafSpec} (h : IndexScalarAgrees br bi leafSpec) :
    IndexScalarAgrees br (exitRange bi) leafSpec := by
  intro t vArr vIdx vRes arrV k ht hbr hk hbi
  rw [exitRange_index] at hbi
  exact h t vArr vIdx vRes arrV k ht hbr hk hbi

theorem indexTowerAgrees_exitRange {br : ValueTowerBridge} {bi : Builtins}
    {leafSpec : LeafSpec} (h : IndexTowerAgrees br bi leafSpec) :
    IndexTowerAgrees br (exitRange bi) leafSpec := by
  intro t t' vArr vIdx vRes arrV k ht hbr hk hbi
  rw [exitRange_index] at hbi
  exact h t t' vArr vIdx vRes arrV k ht hbr hk hbi

/-! ## §9  Source steps -/

section SourceStepsT

variable (bi : Builtins) (fuel : Nat)

/-- A scalar value is a bool, or neither a bool nor tagged by control flow. -/
theorem ScalarValN.bool_or {w : Value} (h : ScalarValN w) :
    (∃ b, w = .bool b) ∨ ((∀ b, w ≠ .bool b) ∧ w.isControlFlow = false) := by
  rcases h.cases with ⟨_, _, rfl, _⟩ | ⟨b, rfl⟩ | ⟨_, rfl, _⟩ | rfl
  · exact Or.inr ⟨fun b h => (by cases h), rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact Or.inr ⟨fun b h => (by cases h), rfl⟩
  · exact Or.inr ⟨fun b h => (by cases h), rfl⟩

theorem denote'_ifThenElse_var_run_nonbool (c : String) (t e : ImpExpr) (env : Env) (w : Value)
    (h : env c = some w) (hb : ∀ b, w ≠ .bool b) (hw : w.isControlFlow = false) :
    (denote' bi fuel (.ifThenElse (.var c) t e)).run env = (.err "if condition not a bool", env) := by
  rw [denote'_ifThenElse_run, denote'_var_run, h]
  cases w <;> first | rfl | exact absurd rfl (hb _) | simp at hw

theorem denoteWhile'Return_succ_nonbool (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (w : Value) (h : env c = some w) (hb : ∀ b, w ≠ .bool b) (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env =
      (.err "while condition not a bool", env) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]
  cases w <;> first | rfl | exact absurd rfl (hb _) | simp at hw

theorem denoteWhile'_succ_nonbool (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (w : Value) (h : env c = some w) (hb : ∀ b, w ≠ .bool b) (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteWhile' bi (n + 1) (.var c) body).run env =
      (.err "while condition not a bool", env) := by
  rw [denoteWhile'_succ_run, denote'_var_run, h]
  cases w <;> first | rfl | exact absurd rfl (hb _) | simp at hw

/-- `denote'_forFoldReturn_var_scalar` for a variable holding a value of `ScalarValN`. -/
theorem denote'_forFoldReturn_var_scalarN (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.var h) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hsv : ∀ v, env h = some v → ScalarValN v) :
    ∃ (v : Value) (H : Nat), env h = some v ∧ valueToScalar v = some H ∧ H < 2 ^ 64 ∧
      (_root_.Hax.denoteForLoop'Return bi fuel i lo H body).run env = (o, env') := by
  obtain ⟨u, rfl⟩ := hval
  rcases hh : env h with _ | w
  · simp only [denote'] at hrun
    simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, hh, Value.ofLit] at hrun
    cases (Prod.mk.inj hrun).1
  · have hs := hsv w hh
    cases w with
    | int n =>
      obtain ⟨h0, h1⟩ := hs
      refine ⟨_, n.toNat, rfl, ?_, by omega, ?_⟩
      · have hd := valueToScalar_int n.toNat
        rwa [Int.toNat_of_nonneg h0] at hd
      · rw [denote'_forFoldReturn_var_run bi fuel i h lo body env n hh] at hrun
        rwa [Int.toNat_of_nonneg h0]
    | uint wd n =>
      refine ⟨_, n, rfl, valueToScalar_uint wd n, hs, ?_⟩
      rw [_root_.Hax.denote'_forFoldReturn_lit_var_uint bi fuel i h lo body env wd n hh] at hrun
      exact hrun
    | bool b =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | unit =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | _ => exact (show False from hs).elim

/-- `denote'_forFold_var_scalar` for a variable holding a value of `ScalarValN`. -/
theorem denote'_forFold_var_scalarN (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.var h) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hsv : ∀ v, env h = some v → ScalarValN v) :
    ∃ (v : Value) (H : Nat), env h = some v ∧ valueToScalar v = some H ∧ H < 2 ^ 64 ∧
      (_root_.Hax.denoteForLoop' bi fuel i lo H body).run env = (o, env') := by
  obtain ⟨u, rfl⟩ := hval
  rcases hh : env h with _ | w
  · simp only [denote'] at hrun
    simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, hh, Value.ofLit] at hrun
    cases (Prod.mk.inj hrun).1
  · have hs := hsv w hh
    cases w with
    | int n =>
      obtain ⟨h0, h1⟩ := hs
      refine ⟨_, n.toNat, rfl, ?_, by omega, ?_⟩
      · have hd := valueToScalar_int n.toNat
        rwa [Int.toNat_of_nonneg h0] at hd
      · rw [denote'_forFold_var_run bi fuel i h lo body env n hh] at hrun
        rwa [Int.toNat_of_nonneg h0]
    | uint wd n =>
      refine ⟨_, n, rfl, valueToScalar_uint wd n, hs, ?_⟩
      rw [_root_.Hax.denote'_forFold_lit_var_uint bi fuel i h lo body env wd n hh] at hrun
      exact hrun
    | bool b =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | unit =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | _ => exact (show False from hs).elim

/-- The arguments of a call on variables evaluate, when they evaluate to values, to the
    values of the variables, and leave the environment unchanged. -/
theorem denoteArgs'_vars_inv (args : List ImpExpr) (hargs : exitArgsOk args = true)
    (env e1 : Env) (o : Option (List Value))
    (h : (_root_.Hax.denoteArgs' bi fuel args).run env = (o, e1)) :
    e1 = env ∧ ∀ vals, o = some vals →
      List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals := by
  induction args generalizing o e1 with
  | nil =>
    rw [denoteArgs'_nil_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, fun vals hv => by cases hv; exact List.Forall₂.nil⟩
  | cons a as ih =>
    cases a with
    | var x =>
      simp only [exitArgsOk, Bool.and_eq_true] at hargs
      rw [denoteArgs'_cons_run, denote'_var_run] at h
      cases hx : env x with
      | none =>
        rw [hx] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨rfl, fun vals hv => by cases hv⟩
      | some v =>
        rw [hx] at h
        rcases hr : (_root_.Hax.denoteArgs' bi fuel as).run env with ⟨o', e1'⟩
        obtain ⟨he, hF⟩ := ih hargs.2 e1' o' hr
        cases v with
        | controlFlow k u =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact ⟨rfl, fun vals hv => by cases hv⟩
        | _ =>
          simp only [hr] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          refine ⟨he, fun vals hv => ?_⟩
          rcases o' with _ | vs
          · cases hv
          · simp only [Option.map_some, Option.some.injEq] at hv
            subst hv
            exact List.Forall₂.cons ⟨x, rfl, hx⟩ (hF vs rfl)
    | _ => simp [exitArgsOk] at hargs

/-- A run of `let n = f(args); body` on variable arguments, over a builtin table
    returning no control-flow value, that ends in a value: the arguments evaluate to the
    values of the variables, the builtin returns `r`, and the body runs from the
    environment extended by `n ↦ r`. -/
theorem letBind_app_inv (hplain : _root_.Hax.ContinueFlag.BuiltinsPlain bi) (n f : String)
    (args : List ImpExpr) (body : ImpExpr) (hargs : exitArgsOk args = true)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.letBind n (.app f args) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    ∃ vals r, List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals ∧
      bi f vals = some r ∧ (denote' bi fuel body).run (env.extend n r) = (o, env') := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel args).run env with ⟨oa, e1⟩
  obtain ⟨rfl, hF⟩ := denoteArgs'_vars_inv bi fuel args hargs env e1 oa hA
  have happ := denote'_app_run bi fuel f args e1
  rw [hA] at happ
  rcases oa with _ | vals
  · rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  · cases hbi : bi f vals with
    | none =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_val bi fuel n _ body e1 e1 r happ (hplain f vals r hbi)] at hrun
      exact ⟨vals, r, hF vals rfl, hbi, hrun⟩

/-- The arguments `[v, l]` of a call on a variable and a literal evaluate, when they
    evaluate to values, to the value of `v` and the value of `l`, and leave the environment
    unchanged. -/
theorem denoteArgs'_varLit_inv (v : String) (l : ImpLit) (env e1 : Env)
    (o : Option (List Value))
    (h : (_root_.Hax.denoteArgs' bi fuel [.var v, .lit l]).run env = (o, e1)) :
    e1 = env ∧ ∀ vals, o = some vals → ∃ vv, env v = some vv ∧ vals = [vv, Value.ofLit l] := by
  rw [denoteArgs'_cons_run, denote'_var_run] at h
  cases hx : env v with
  | none =>
    rw [hx] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, fun vals hv => by cases hv⟩
  | some vv =>
    rw [hx] at h
    have hl : (_root_.Hax.denoteArgs' bi fuel [.lit l]).run env = (some [Value.ofLit l], env) := by
      rw [denoteArgs'_cons_run]
      have h1 : (denote' bi fuel (.lit l)).run env = (.val (Value.ofLit l), env) := by
        simp only [denote']; rfl
      rw [h1]
      cases l <;> simp [denoteArgs'_nil_run, Value.ofLit]
    cases vv with
    | controlFlow k u =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, fun vals hv => by cases hv⟩
    | _ =>
      simp only [hl, Option.map_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, fun vals hv => ⟨_, rfl, (Option.some.inj hv).symm⟩⟩

private theorem stateM_bind_run' {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β)
    (s : σ) : (m >>= f) s = (f (m s).1) (m s).2 := rfl

private theorem stateM_get_run' {σ : Type} (s : σ) : (get : StateM σ σ) s = (s, s) := rfl

/-- A `match` on an `Option` whose scrutinee evaluates to `Some w`: the `Some` arm runs with
    the payload bound. -/
theorem denote'_optMatch_some {s t e : ImpExpr} {p : String} {env env1 : Env} {w : Value}
    (hs : denote' bi fuel s env = (.val (.option (some w)), env1)) :
    denote' bi fuel (.match_ s [(.somePat (.varPat p), t), (.nonePat, e)]) env =
      denote' bi fuel t (env1.extend p w) := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

theorem denote'_optMatch_none {s t e : ImpExpr} {p : String} {env env1 : Env}
    (hs : denote' bi fuel s env = (.val (.option none), env1)) :
    denote' bi fuel (.match_ s [(.somePat (.varPat p), t), (.nonePat, e)]) env =
      denote' bi fuel e env1 := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

theorem denote'_optMatchR_some {s t e : ImpExpr} {p : String} {env env1 : Env} {w : Value}
    (hs : denote' bi fuel s env = (.val (.option (some w)), env1)) :
    denote' bi fuel (.match_ s [(.nonePat, e), (.somePat (.varPat p), t)]) env =
      denote' bi fuel t (env1.extend p w) := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

theorem denote'_optMatchR_none {s t e : ImpExpr} {p : String} {env env1 : Env}
    (hs : denote' bi fuel s env = (.val (.option none), env1)) :
    denote' bi fuel (.match_ s [(.nonePat, e), (.somePat (.varPat p), t)]) env =
      denote' bi fuel e env1 := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

/-- A `match` whose scrutinee does not evaluate to a value ends in that outcome. -/
theorem denote'_match_nonval {s : ImpExpr} {arms : List (_root_.Hax.ImpPat × ImpExpr)}
    {env env1 : Env} {o : Outcome} (hs : denote' bi fuel s env = (o, env1))
    (ho : ∀ v, o ≠ .val v) : denote' bi fuel (.match_ s arms) env = (o, env1) := by
  simp only [denote', stateM_bind_run', hs]
  rcases o with v | _ | _ | _ | _
  · exact absurd rfl (ho v)
  all_goals rfl

/-- A run of `let n = repeat(v, l); body` with a literal count, over a builtin table
    returning no control-flow value, that ends in a value: `v` holds `vv`, the builtin
    returns `r` on `vv` and the value of `l`, and the body runs from the environment
    extended by `n ↦ r`. -/
theorem letBind_repeat_inv (hplain : _root_.Hax.ContinueFlag.BuiltinsPlain bi) (n v : String)
    (l : ImpLit) (body : ImpExpr) (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.letBind n (.app "repeat" [.var v, .lit l]) body)).run env =
      (o, env'))
    (hval : ∃ w, o = .val w) :
    ∃ vv r, env v = some vv ∧ bi "repeat" [vv, Value.ofLit l] = some r ∧
      (denote' bi fuel body).run (env.extend n r) = (o, env') := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel [.var v, .lit l]).run env with ⟨oa, e1⟩
  obtain ⟨rfl, hF⟩ := denoteArgs'_varLit_inv bi fuel v l env e1 oa hA
  have happ := denote'_app_run bi fuel "repeat" [.var v, .lit l] e1
  rw [hA] at happ
  rcases oa with _ | vals
  · rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  · obtain ⟨vv, hvv, rfl⟩ := hF _ rfl
    cases hbi : bi "repeat" [vv, Value.ofLit l] with
    | none =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_val bi fuel n _ body e1 e1 r happ (hplain _ _ r hbi)] at hrun
      exact ⟨vv, r, hvv, hbi, hrun⟩

theorem denote'_forFoldRev_lit_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    (denote' bi fuel (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (_root_.Hax.denoteForLoopRev' bi fuel i lo hi body).run env := by
  simp only [denote']; rfl

theorem denoteForLoopRev'_ge_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) :
    (_root_.Hax.denoteForLoopRev' bi fuel i lo hi body).run env = (.val .unit, env) := by
  rw [_root_.Hax.denoteForLoopRev', if_pos h]; rfl

theorem denoteForLoopRev'_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (_root_.Hax.denoteForLoopRev' bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [_root_.Hax.denoteForLoopRev', if_neg (not_le.mpr h), if_pos rfl]; rfl

theorem denoteForLoopRev'_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : lo < hi) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) with
      | (.val (.controlFlow true v), e2) => (.val v, e2)
      | (.val (.controlFlow false _), e2) =>
          (_root_.Hax.denoteForLoopRev' bi n i lo (hi - 1) body).run e2
      | (.val _, e2) => (_root_.Hax.denoteForLoopRev' bi n i lo (hi - 1) body).run e2
      | (o, e2) => (o, e2) := by
  rw [_root_.Hax.denoteForLoopRev', if_neg (not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int (hi - 1))) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w => cases k <;> rfl
  | _ => rfl

theorem denoteForLoopRev'_succ_break (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) =
      (.val (.controlFlow true w), e2)) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env = (.val w, e2) := by
  rw [denoteForLoopRev'_succ_run bi n i lo hi body env h, hb]

theorem denoteForLoopRev'_succ_iterate (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) = (.val w, e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env =
      (_root_.Hax.denoteForLoopRev' bi n i lo (hi - 1) body).run e2 := by
  rw [denoteForLoopRev'_succ_run bi n i lo hi body env h, hb]
  cases w <;> first | rfl | simp at hw

theorem denoteForLoopRev'_succ_nonval (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (o : Outcome) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) = (o, e2))
    (ho : ∀ v, o ≠ .val v) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env = (o, e2) := by
  rw [denoteForLoopRev'_succ_run bi n i lo hi body env h, hb]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

end SourceStepsT

/-! ## §10  The simulation statement and the translator's equations -/

/-- The simulation of `e` under the placement `A` and result placement `R`: from states
    agreeing under `A` with the exit flag `0`, a run of `denote'` ending in a value is
    matched by a run of `haxToLowCTKT A` ending in states agreeing under `A`; a command
    that cannot exit leaves the flag `0`. -/
def ExitSimTy (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (A : ExitTowers) (R : ExitRes) (e : ImpExpr) : Prop :=
  ∀ (tl : Bool) (fl : Option String) (fuel : Nat) (env env' : Env) (o : Outcome)
    (rs : RustState) (c : LowCT) (x : Bool),
    exitSimOkT A R tl fl.isSome e = true → RunCtx fl →
    haxToLowCTKT A tl fl e = some (c, x) →
    (denote' bi fuel e).run env = (o, env') →
    (∃ v, o = .val v) →
    envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesExitT br A R tl o env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0)

section Equations

variable (A : ExitTowers)

theorem haxToLowCTKT_letBind_eq (tl : Bool) (fl : Option String) (n : String)
    (val body : ImpExpr) :
    haxToLowCTKT A tl fl (.letBind n val body) =
      match letHeadT A n val, haxToLowCTKT A tl fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_seq_eq (tl : Bool) (fl : Option String) (a b : ImpExpr) :
    haxToLowCTKT A tl fl (.seq a b) =
      match haxToLowCTKT A false fl a, haxToLowCTKT A tl fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_ifThenElse_eq (tl : Bool) (fl : Option String) (v : String)
    (t e : ImpExpr) (hv : exitSc A v = true) :
    haxToLowCTKT A tl fl (.ifThenElse (.var v) t e) =
      match haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none := by
  cases tl <;> cases fl <;> exact if_pos hv

theorem haxToLowCTKT_typeAscription_eq (tl : Bool) (fl : Option String) (e : ImpExpr)
    (ty : String) : haxToLowCTKT A tl fl (.typeAscription e ty) = haxToLowCTKT A tl fl e := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_whileFoldReturn_eq (fl : Option String) (c : String) (body : ImpExpr)
    (hc : exitSc A c = true) :
    haxToLowCTKT A false fl (.whileFoldReturn (.var c) body) =
      match haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none := by
  cases fl <;> exact if_pos hc

theorem haxToLowCTKT_forFoldReturn_eq (fl : Option String) (i : String) (lo hi body : ImpExpr)
    (hi' : (exitSc A i && exitScRt A lo hi) = true) :
    haxToLowCTKT A false fl (.forFoldReturn i lo hi body) =
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), _, some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
      | none, some (l, h), some (bC, _) =>
          some (exitForLoopRt (exitRunName fl) i l h bC, true)
      | _, _, _ => none := by
  cases fl <;> exact if_pos hi'

theorem haxToLowCTKT_forFoldRevReturn_eq (fl : Option String) (i : String)
    (lo hi body : ImpExpr) (hi' : exitSc A i = true) :
    haxToLowCTKT A false fl (.forFoldRevReturn i lo hi body) =
      match forBounds lo hi, haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
      | _, _ => none := by
  cases fl <;> exact if_pos hi'

theorem haxToLowCTKT_forFold_some_eq (r i : String) (lo hi body : ImpExpr)
    (hi' : (exitSc A i && exitScRt A lo hi) = true) :
    haxToLowCTKT A false (some r) (.forFold i lo hi body) =
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (l, h), _, some (bC, _) =>
          some (breakLoop (exitForLoop (exitRunName (some r)) i l h bC), false)
      | none, some (l, h), some (bC, _) =>
          some (breakLoop (exitForLoopRt (exitRunName (some r)) i l h bC), false)
      | _, _, _ => none := if_pos hi'

theorem haxToLowCTKT_forFoldRev_some_eq (r i : String) (lo hi body : ImpExpr)
    (hi' : exitSc A i = true) :
    haxToLowCTKT A false (some r) (.forFoldRev i lo hi body) =
      match forBounds lo hi, haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (l, h), some (bC, _) =>
          some (breakLoop (exitForLoopRev (exitRunName (some r)) i l h bC), false)
      | _, _ => none := if_pos hi'

theorem haxToLowCTKT_whileFold_some_eq (r c : String) (body : ImpExpr)
    (hc : exitSc A c = true) :
    haxToLowCTKT A false (some r) (.whileFold (.var c) body) =
      match haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (bC, _) => some (breakLoop (exitLoop (exitRunName (some r)) c bC), false)
      | none => none := if_pos hc

theorem haxToLowCTKT_cfBreak_eq (tl : Bool) (r : String) (p : ImpExpr)
    (hp : exitScE A p = true) :
    haxToLowCTKT A tl (some r) (.cfBreak p) = (exitStore p).map fun s => (s, true) := by
  cases tl <;> exact if_pos hp

end Equations

/-! ## §11  The reserved tower slots and the marshalling of call arguments -/

theorem exitReserved_call : exitReserved exitCallName = true := by decide

theorem exitReserved_marshal (x : String) : exitReserved (exitMarshalName x) = true := by
  unfold exitReserved exitMarshalName
  rw [String.toList_append, List.isPrefixOf_iff_prefix]
  exact List.IsPrefix.trans (by decide) (List.prefix_append _ _)

theorem exitMarshalName_inj {x y : String} (h : exitMarshalName x = exitMarshalName y) :
    x = y := by
  unfold exitMarshalName at h
  have h' := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h'
  exact String.ext (List.append_cancel_left h')

theorem exitCallName_ne_marshal (x : String) : exitCallName ≠ exitMarshalName x := by
  intro h
  have h' := congrArg (fun s => s.toList.take 8) h
  simp only [exitMarshalName, String.toList_append] at h'
  rw [List.take_append_of_le_length (by decide)] at h'
  revert h'; decide

theorem ne_marshal_of_nonreserved {y : String} (hy : exitReserved y = false) (x : String) :
    y ≠ exitMarshalName x := ne_of_reserved hy (exitReserved_marshal x)

theorem rsSetTower_rsSetTower (rs : RustState) (x : String) (v w : Σ t, RustVal t) :
    rsSetTower (rsSetTower rs x v) x w = rsSetTower rs x w := by
  cases rs
  simp only [rsSetTower, RustState.mk.injEq, and_true]
  funext y
  by_cases h : y = x <;> simp [h]

section Marshal

variable (N : Nat) (leafSpec : LeafSpec)

/-- The value `callMarshal` stores for the scalar `k` in the slot of `z`. -/
def marshalVal (dt : TowerType) (z : String) (k : Nat) : RustVal dt :=
  leafSpec.limbStore ⟨exitMarshalName z, dt⟩ default 0 (BitVec.ofNat 64 k)

/-- **The marshalling of call arguments.**  From a state `rs0` with the scalar heap of
    `rs` and the tower slots of `rs` at the non-reserved names, the context of
    `callMarshal` runs to a state `rs1` that keeps the scalar heap and every tower slot
    other than the marshalling slots, holds in each marshalling slot it wrote the value
    `marshalVal` of the scalar, and holds, for each argument, a tower value of the slot's
    type related by `br` to the argument's value in the slot it reads the argument from. -/
theorem callMarshal_sim {br : ValueTowerBridge} {A : ExitTowers} {env : Env} {rs : RustState}
    (hag : envAgreesT br A env rs) (hmar : ExitMarshal br leafSpec) (dt : TowerType) :
    ∀ (args : List ImpExpr) (ctx : LowCT → LowCT) (ls : List Located) (vals : List Value),
      callMarshal A dt args = some (ctx, ls) → exitArgsOk args = true →
      List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals →
      ∀ rs0 : RustState, rs0.rsScalar = rs.rsScalar →
        (∀ y, exitReserved y = false → rs0.rsTower y = rs.rsTower y) →
        ∃ rs1, (∀ c rs', RustExec N leafSpec c rs1 rs' → RustExec N leafSpec (ctx c) rs0 rs') ∧
          rs1.rsScalar = rs.rsScalar ∧
          (∀ y, (∀ z, y ≠ exitMarshalName z) → rs1.rsTower y = rs0.rsTower y) ∧
          (∀ z, rs1.rsTower (exitMarshalName z) = rs0.rsTower (exitMarshalName z) ∨
            rs1.rsTower (exitMarshalName z) =
              some ⟨dt, marshalVal leafSpec dt z (rs.rsScalar z)⟩) ∧
          List.Forall₂ (fun v (a : Located) => ∃ val, rs1.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧
            br a.locDst v val ∧
            ∀ z, a.locVar = exitMarshalName z → val = marshalVal leafSpec a.locDst z (rs.rsScalar z))
            vals ls := by
  intro args
  induction args with
  | nil =>
    intro ctx ls vals h _ hF rs0 hS _
    simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hF
    exact ⟨rs0, fun c rs' hc => hc, hS, fun _ _ => rfl, fun _ => Or.inl rfl, List.Forall₂.nil⟩
  | cons a as ih =>
    intro ctx ls vals h hok hF rs0 hS hT
    cases a with
    | var x =>
      simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hxr, hok⟩ := hok
      rcases hF with _ | ⟨⟨x', hx', hxv⟩, hF⟩
      cases hx'
      rename_i v vs
      rcases hr : callMarshal A dt as with _ | ⟨ctx', ls'⟩
      · simp [callMarshal, hr] at h
      rcases hx : A.lookup x with _ | t
      · -- a scalar argument: store it into its marshalling slot
        simp only [callMarshal, hr, hx] at h
        split_ifs at h with hmo
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h8 : 8 ≤ dt.storageBytes := by simpa [exitMarshalOk] using hmo
        obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hxr hx hxv
        have hSB : (rsSetTower rs0 (exitMarshalName x)
            ⟨dt, marshalVal leafSpec dt x (rs.rsScalar x)⟩).rsScalar = rs.rsScalar := hS
        have hTB : ∀ y, exitReserved y = false → (rsSetTower rs0 (exitMarshalName x)
            ⟨dt, marshalVal leafSpec dt x (rs.rsScalar x)⟩).rsTower y = rs.rsTower y := by
          intro y hy
          rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
            (ne_marshal_of_nonreserved hy x).symm]
          exact hT y hy
        obtain ⟨rs1, hex, hS1, hT1, hM1, hF1⟩ := ih ctx' ls' vs hr hok hF _ hSB hTB
        refine ⟨rs1, fun c rs' hc => ?_, hS1, ?_, ?_, ?_⟩
        · refine RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _
            (RustExec.limbStoreExpr _ _ _ _ default ?_) ?_)
          · exact locatedLookup_of_rsTower _ _ dt default
              (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _)
          · have hev : (SExpr.SVar x).evalState
                (rsSetTower rs0 (exitMarshalName x) ⟨dt, default⟩) = rs.rsScalar x := by
              simp only [SExpr.evalState]
              exact congrFun hS x
            simp only [locatedUpdate, hev, rsSetTower_rsSetTower]
            exact hex c rs' hc
        · intro y hy
          rw [hT1 y hy, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
            (fun h => hy x h.symm)]
        · intro z
          by_cases hz : z = x
          · subst hz
            right
            rcases hM1 z with h1 | h1
            · rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]
            · exact h1
          · have hmz : exitMarshalName x ≠ exitMarshalName z :=
              fun h => hz (exitMarshalName_inj h).symm
            rcases hM1 z with h1 | h1
            · left
              rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ hmz]
            · exact Or.inr h1
        · refine List.Forall₂.cons ⟨marshalVal leafSpec dt x (rs.rsScalar x), ?_, ?_, ?_⟩ hF1
          · rcases hM1 x with h1 | h1
            · rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]
            · exact h1
          · exact hmar ⟨exitMarshalName x, dt⟩ v _ h8 hsv hdv
          · intro z hz
            obtain rfl := exitMarshalName_inj hz
            rfl
      · -- a tower argument, read in place at its tower type
        simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, val, hval, hbr⟩ := envAgreesT_tower hag hxr hx hxv
        obtain ⟨rs1, hex, hS1, hT1, hM1, hF1⟩ := ih ctx' ls' vs hr hok hF rs0 hS hT
        refine ⟨rs1, hex, hS1, hT1, hM1, List.Forall₂.cons ⟨val, ?_, hbr,
          fun z hz => absurd hz (ne_marshal_of_nonreserved hxr z)⟩ hF1⟩
        rw [hT1 x (ne_marshal_of_nonreserved hxr), hT x hxr]
        exact hval
    | _ => simp [callMarshal] at h

end Marshal

/-- The tower values `RCall` reads from slots holding related values are related
    elementwise. -/
theorem forall₂_filterMap_rsTower {br : ValueTowerBridge} {rs : RustState} :
    ∀ {vals : List Value} {ls : List Located},
      List.Forall₂ (fun v (a : Located) => ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧
        br a.locDst v val) vals ls →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals
        (ls.filterMap fun a => rs.rsTower a.locVar)
  | [], [], _ => by simp
  | v :: vs, a :: as, List.Forall₂.cons ⟨val, hv, hb⟩ h => by
    rw [List.filterMap_cons, hv]
    exact List.Forall₂.cons hb (forall₂_filterMap_rsTower h)

/-- Under `exitArgsAt A dt args`, every argument slot of `callMarshal A dt args` has the
    type `dt`. -/
theorem callMarshal_locDst (A : ExitTowers) (dt : TowerType) :
    ∀ (args : List ImpExpr) (ctx : LowCT → LowCT) (ls : List Located),
      callMarshal A dt args = some (ctx, ls) → exitArgsAt A dt args = true →
      ∀ a ∈ ls, a.locDst = dt := by
  intro args
  induction args with
  | nil =>
    intro ctx ls h _ a ha
    simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases ha
  | cons e as ih =>
    intro ctx ls h hat
    cases e with
    | var x =>
      simp only [exitArgsAt, List.all_cons, Bool.and_eq_true] at hat
      rcases hr : callMarshal A dt as with _ | ⟨ctx', ls'⟩
      · simp [callMarshal, hr] at h
      have ih' := ih ctx' ls' hr hat.2
      rcases hx : A.lookup x with _ | t
      · simp only [callMarshal, hr, hx] at h
        split_ifs at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · exact ih' a ha
      · simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have ht : t = dt := by simpa [hx] using hat.1
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ht
        · exact ih' a ha
    | _ => simp [callMarshal] at h

/-- The tower values `RCall` reads from slots each holding a value of its declared type
    have the declared types of the slots. -/
theorem filterMap_rsTower_types {rs : RustState} :
    ∀ {ls : List Located}, (∀ a ∈ ls, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (ls.filterMap fun a => rs.rsTower a.locVar).map (·.1) = ls.map (·.locDst)
  | [], _ => rfl
  | a :: as, h => by
    obtain ⟨v, hv⟩ := h a (by simp)
    simp only [List.filterMap_cons, hv, List.map_cons,
      filterMap_rsTower_types (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem forall₂_rsTower_typed {br : ValueTowerBridge} {rs : RustState}
    {vals : List Value} {ls : List Located}
    (h : List.Forall₂ (fun v (a : Located) => ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧
      br a.locDst v val) vals ls) :
    ∀ a ∈ ls, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hh _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨val, hv, -⟩ := hh
      exact ⟨val, hv⟩
    · exact ih a ha

/-! ## §12  The heads of a `letBind` -/

theorem exitSimOkT_letBind_body (A : ExitTowers) (R : ExitRes) (tl il : Bool)
    (n : String) (val body : ImpExpr) (h : exitSimOkT A R tl il (.letBind n val body) = true) :
    exitSimOkT A R tl il body = true := by
  cases val with
  | lit l => cases tl <;> cases il <;> simp_all [exitSimOkT]
  | var s => cases tl <;> cases il <;> simp_all [exitSimOkT]
  | app f args => cases tl <;> cases il <;> simp_all [exitSimOkT]
  | _ => cases tl <;> cases il <;> simp [exitSimOkT] at h

/-- A run of the head `k` of `let n = val` from agreeing states: the body of the binding
    runs from an environment `env1` agreeing with a state `rs1` with the exit flag `0`,
    and every run of a lowered body from `rs1` extends to a run of `k` applied to it. -/
def HeadSimT (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (A : ExitTowers) (R : ExitRes) (n : String) (val body : ImpExpr) : Prop :=
  ∀ (tl il : Bool) (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (k : LowCT → LowCT),
    exitSimOkT A R tl il (.letBind n val body) = true → letHeadT A n val = some k →
    (denote' bi fuel (.letBind n val body)).run env = (o, env') → (∃ v, o = .val v) →
    envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
    ∃ env1 rs1, (denote' bi fuel body).run env1 = (o, env') ∧ envAgreesT br A env1 rs1 ∧
      rs1.rsScalar exitRetName = 0 ∧
      ∀ bC rs', RustExec N leafSpec bC rs1 rs' → RustExec N leafSpec (k bC) rs rs'

section Heads

variable (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
  (A : ExitTowers) (R : ExitRes)

/-- **The `letBind` arm** from a simulation of the head. -/
theorem exitSimTy_letBind_of_head (n : String) (val body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body)
    (hhead : HeadSimT bi N leafSpec br A R n val body) :
    ExitSimTy bi N leafSpec br A R (.letBind n val body) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [haxToLowCTKT_letBind_eq] at hK
  rcases hk : letHeadT A n val with _ | k
  · rw [hk] at hK; cases hK
  rcases hB : haxToLowCTKT A tl fl body with _ | ⟨bC, x⟩
  · rw [hk, hB] at hK; cases hK
  rw [hk, hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  obtain ⟨env1, rs1, hrun1, hag1, hret1, hexK⟩ :=
    hhead tl fl.isSome fuel env env' o rs k hok hk hrun hval hag hret
  obtain ⟨rs', hex, hagE, hx⟩ :=
    ihb tl fl fuel env1 env' o rs1 bC x (exitSimOkT_letBind_body A R _ _ n val body hok) hfl hB
      hrun1 hval hag1 hret1
  exact ⟨rs', hexK bC rs' hex, hagE, hx⟩

/-- The scalar binding `let n = kk` of a scalar name: a run of the body from the state
    whose slot `n` holds `kk` extends to a run of the lowered binding. -/
theorem exec_letU64_set (n : String) (kk : Nat) (bC : LowCT) (rs rs' : RustState)
    (h : RustExec N leafSpec bC (rsSetScalar rs n kk) rs') :
    RustExec N leafSpec (.RLetU64Zero n (.RSeq (.RScalarSet n kk) bC)) rs rs' :=
  RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSet _ _ _)
    (by rw [rsSetScalar_rsSetScalar]; exact h))

theorem ret_setScalar {rs : RustState} {n : String} (hn : exitReserved n = false) (kk : Nat)
    (h : rs.rsScalar exitRetName = 0) : (rsSetScalar rs n kk).rsScalar exitRetName = 0 := by
  rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, h]

/-- The value of a literal of `exitLitOk` is a scalar word. -/
theorem exitLitOk_scalarValN {l : ImpLit} (hl : exitLitOk l = true) :
    ScalarValN (Value.ofLit l) := by
  cases l with
  | uintLit w m =>
    show m % w.modulus < 2 ^ 64
    cases w <;> simp only [IntWidth.modulus, IntWidth.bits] <;> first
      | omega | (simp only [exitLitOk] at hl; exact absurd hl (by decide))
  | int z =>
    simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    exact hl
  | bool b => trivial
  | unit => trivial
  | _ => simp [exitLitOk] at hl

/-- The head of `let n = l`: on a scalar name, the scalar binding of `letHead`; on a name
    placed in a tower at `t`, the zero slot of type `t` with the literal's word in limb `0`,
    whose value the marshalling condition `hmar` relates to the literal. -/
theorem head_lit (hmar : ExitMarshal br leafSpec) (n : String) (l : ImpLit) (body : ImpExpr) :
    HeadSimT bi N leafSpec br A R n (.lit l) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitLitOk l = true ∧ exitReserved n = false := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1, hok.1.2⟩)
  obtain ⟨hl, hn⟩ := hh
  have hsv := exitLitOk_scalarValN hl
  rw [denote'_letBind_run_val bi fuel n _ body env env _ (denote'_lit_run bi fuel l env)
    hsv.not_cf] at hrun
  rcases hsc' : A.lookup n with _ | t
  · have hk' : letHead n (.lit l) = some k := by simpa [letHeadT, hsc'] using hk
    obtain ⟨kk, hkk, hdk⟩ : ∃ kk, k = (fun bC => .RLetU64Zero n (.RSeq (.RScalarSet n kk) bC)) ∧
        valueToScalar (Value.ofLit l) = some kk := by
      cases l with
      | uintLit w m =>
        simp only [letHead, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, rfl⟩
      | int z =>
        simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
        simp only [letHead, ge_iff_le, hl.1, if_true, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, by simp [valueToScalar, Value.ofLit, hl.1]⟩
      | bool b =>
        simp only [letHead, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, valueToScalar_bool b⟩
      | unit => simp [letHead] at hk'
      | _ => simp [exitLitOk] at hl
    subst hkk
    exact ⟨_, _, hrun, envAgreesT_extend hn hsc' hsv hdk hag, ret_setScalar hn _ hret,
      fun bC rs' h => exec_letU64_set N leafSpec n kk bC rs rs' h⟩
  · simp only [letHeadT, hsc'] at hk
    split_ifs at hk with hmo
    obtain ⟨kk, hdk, rfl⟩ := Option.map_eq_some_iff.mp hk
    have h8 : 8 ≤ t.storageBytes := by simpa [exitMarshalOk] using hmo
    refine ⟨_, rsSetTower rs n ⟨t, leafSpec.limbStore ⟨n, t⟩ default 0 (BitVec.ofNat 64 kk)⟩,
      hrun, envAgreesT_extend_tower hn hsc' hsv.not_cf (hmar ⟨n, t⟩ _ kk h8 hsv hdk) hag, hret,
      fun bC rs' h => ?_⟩
    refine RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _
      (RustExec.limbStoreExpr _ _ _ _ default ?_) ?_)
    · exact locatedLookup_of_rsTower _ _ t default
        (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _)
    · simpa only [locatedUpdate, SExpr.evalState, rsSetTower_rsSetTower] using h

theorem head_var (n s : String) (body : ImpExpr) :
    HeadSimT bi N leafSpec br A R n (.var s) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitReserved n = false ∧ exitReserved s = false ∧ A.lookup n = A.lookup s := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
       exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2⟩)
  obtain ⟨hn, hs, hns⟩ := hh
  cases hw : env s with
  | none =>
    rw [denote'_letBind_run_nonval bi fuel n _ body env env _
      (by rw [denote'_var_run, hw]) (fun _ h => by cases h)] at hrun
    obtain ⟨v, hv⟩ := hval
    cases hrun
    cases hv
  | some w =>
    have hcf := envAgreesT_not_cf hag hs hw
    rw [denote'_letBind_run_val bi fuel n _ body env env w (by rw [denote'_var_run, hw])
      hcf] at hrun
    rcases hA : A.lookup s with _ | t
    · rw [hA] at hns
      simp only [letHeadT, hns, hA, letHead] at hk
      obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hs hA hw
      by_cases hsn : n = s
      · subst hsn
        simp only [if_true, Option.some.injEq] at hk
        subst hk
        rw [Env.extend_self env n w hw] at hrun
        exact ⟨env, rs, hrun, hag, hret, fun bC rs' h => h⟩
      · simp only [hsn, if_false, Option.some.injEq] at hk
        subst hk
        exact ⟨_, _, hrun, envAgreesT_extend hn hns hsv hdv hag, ret_setScalar hn _ hret,
          fun bC rs' h => rustExec_letBind_copy N leafSpec n s bC rs rs' hsn h⟩
    · rw [hA] at hns
      simp only [letHeadT, hns, hA, if_true] at hk
      obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hs hA hw
      by_cases hsn : n = s
      · subst hsn
        simp only [if_true, Option.some.injEq] at hk
        subst hk
        rw [Env.extend_self env n w hw] at hrun
        exact ⟨env, rs, hrun, hag, hret, fun bC rs' h => h⟩
      · simp only [hsn, if_false, Option.some.injEq] at hk
        subst hk
        refine ⟨_, rsSetTower rs n ⟨t, val⟩, hrun,
          envAgreesT_extend_tower hn hns hcf hbr hag, hret, fun bC rs' h => ?_⟩
        exact RustExec.seq _ _ _ _ _
          (RustExec.copy ⟨n, t⟩ ⟨s, t⟩ rs rfl val (locatedLookup_of_rsTower rs s t val hval')) h

/-! ### Inversion of the call heads -/

theorem scalarOpHeadT_some {n f : String} {args : List ImpExpr} {se : SExpr}
    (h : scalarOpHeadT A n f args = some se) :
    ∃ a b, args = [.var a, .var b] ∧ A.lookup n = none ∧ A.lookup a = none ∧
      A.lookup b = none ∧ scalarOpExprT f (.SVar a) (.SVar b) = some se := by
  unfold scalarOpHeadT at h
  split at h
  · rename_i a b
    split_ifs at h with hc
    exact ⟨a, b, rfl, hc.1, hc.2.1, hc.2.2, h⟩
  · cases h

theorem indexHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : indexHeadT A n args = some k) :
    ∃ arr idx t, args = [.var arr, .var idx] ∧ A.lookup arr = some t ∧ A.lookup idx = none ∧
      ((exitElemTower t = none ∧ A.lookup n = none ∧ k = fun b => .RLetZero exitCallName .TFp
          (.RSeq (.RArrLoad ⟨exitCallName, .TFp⟩ ⟨arr, t⟩ idx)
            (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b))) ∨
        ∃ t', exitElemTower t = some t' ∧ A.lookup n = some t' ∧
          k = fun b => .RLetZero exitCallName t'
            (.RSeq (.RArrLoad ⟨exitCallName, t'⟩ ⟨arr, t⟩ idx)
              (.RSeq (.RCopy ⟨n, t'⟩ ⟨exitCallName, t'⟩) b))) := by
  unfold indexHeadT at h
  split at h
  · rename_i arr idx
    rcases ht : A.lookup arr with _ | t <;> rw [ht] at h
    · cases h
    · simp only at h
      rcases he : exitElemTower t with _ | t' <;> simp only [he] at h
      · split_ifs at h with hi hn
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, t, rfl, ht, hi, Or.inl ⟨he, hn, h.symm⟩⟩
      · split_ifs at h with hi hn
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, t, rfl, ht, hi, Or.inr ⟨t', he, hn, h.symm⟩⟩
  · cases h

theorem updateHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : updateHeadT A n args = some k) :
    ∃ arr idx src t ctx srcLoc, args = [.var arr, .var idx, .var src] ∧ n = arr ∧
      A.lookup arr = some t ∧ A.lookup idx = none ∧
      ((exitElemTower t).isNone = true → A.lookup src = none) ∧
      callMarshal A (exitElem t) [.var src] = some (ctx, [srcLoc]) ∧
      srcLoc.locSrc = exitElem t ∧
      k = fun b => .RSeq (ctx (.RArrStore ⟨arr, t⟩ idx srcLoc)) b := by
  unfold updateHeadT at h
  split at h
  · rename_i arr idx src
    rcases ht : A.lookup arr with _ | t <;> rw [ht] at h
    · cases h
    · simp only at h
      split_ifs at h with hc
      rcases hm : callMarshal A (exitElem t) [.var src] with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
      · cases h
      · rcases ls with _ | ⟨srcLoc, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq] at h
        split_ifs at h with hsl
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, src, t, ctx, srcLoc, rfl, hc.1, ht, hc.2.1, hc.2.2, hm, hsl, h.symm⟩
  · cases h

theorem callHeadAt_some {n f : String} {dt dr : TowerType} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : callHeadAt A n f dt dr args = some k) :
    ∃ ctx ls, callMarshal A dt args = some (ctx, ls) ∧
      ((A.lookup n = none ∧
          k = fun b => .RSeq (.RLetZero exitCallName dr
            (ctx (.RCall f ⟨exitCallName, dr⟩ ls)))
            (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)) ∨
        (A.lookup n = some dr ∧
          k = fun b => .RSeq (.RLetZero exitCallName dr
            (ctx (.RCall f ⟨exitCallName, dr⟩ ls)))
            (.RSeq (.RCopy ⟨n, dr⟩ ⟨exitCallName, dr⟩) b))) := by
  unfold callHeadAt at h
  rcases hm : callMarshal A dt args with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
  · cases h
  · simp only at h
    refine ⟨ctx, ls, rfl, ?_⟩
    rcases hn : A.lookup n with _ | t <;> rw [hn] at h
    · simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, h.symm⟩
    · simp only at h
      split_ifs at h with ht
      subst ht
      simp only [Option.some.injEq] at h
      exact Or.inr ⟨rfl, h.symm⟩

/-- The call heads: a call of `exitScalarRes` bound to a scalar name at
    `towerOfCallName f`; a call with the declared result type `dr` at `dr`, bound to a
    scalar name only for `dr = TU64`; a call without a declared result type bound to a name
    placed at `towerOfCallName f` at that type; a linked callee with argument slot types
    `ts` and result type `dr` at `dr`, whose argument slots have the types `ts`, bound to a
    scalar name only for `dr = TU64`. -/
theorem callHeadT_some {n f : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : callHeadT A n f args = some k) :
    ∃ dt dr, callHeadAt A n f dt dr args = some k ∧
      ((exitScalarRes f = true ∧ A.lookup n = none ∧ dr = towerOfCallName f) ∨
        (exitScalarRes f = false ∧ exitCalleeTys A f = none ∧ exitCallTys A f = some dr ∧
          exitOptTys A f = none ∧ (A.lookup n = none → dr = .TU64)) ∨
        (exitScalarRes f = false ∧ exitCalleeTys A f = none ∧ exitCallTys A f = none ∧
          A.lookup n = some dr ∧ dr = towerOfCallName f) ∨
        (∃ ts, exitScalarRes f = false ∧ exitCalleeTys A f = some (ts, dr) ∧ dt = .TU64 ∧
          (callMarshal A .TU64 args).map (fun cl => cl.2.map (·.locDst)) = some ts ∧
          (A.lookup n = none → dr = .TU64))) := by
  unfold callHeadT at h
  by_cases hs : exitScalarRes f = true
  · rw [if_pos hs] at h
    split_ifs at h with hn
    exact ⟨_, _, h, Or.inl ⟨hs, hn, rfl⟩⟩
  · rw [if_neg hs] at h
    have hs' : exitScalarRes f = false := by simpa using hs
    rcases hc : exitCalleeTys A f with _ | ⟨ts, dr⟩ <;> rw [hc] at h
    · simp only at h
      rcases hd : exitCallTys A f with _ | dr <;> rw [hd] at h
      · simp only at h
        split_ifs at h with hn
        exact ⟨_, _, h, Or.inr (Or.inr (Or.inl ⟨hs', rfl, rfl, hn, rfl⟩))⟩
      · simp only at h
        split_ifs at h with hn
        refine ⟨_, _, h, Or.inr (Or.inl ⟨hs', rfl, rfl, ?_, fun h0 => ?_⟩)⟩
        · by_contra hne
          exact hn (Or.inl (Option.isSome_iff_ne_none.mpr hne))
        · by_contra hne
          exact hn (Or.inr ⟨h0, hne⟩)
    · simp only at h
      split_ifs at h with hn
      refine ⟨_, _, h, Or.inr (Or.inr (Or.inr ⟨ts, hs', rfl, rfl, ?_, fun h0 => ?_⟩))⟩
      · by_contra hne
        exact hn (Or.inr (Or.inr (Or.inr hne)))
      · by_contra hne
        exact hn (Or.inr (Or.inr (Or.inl ⟨h0, hne⟩)))

/-- The call of `optHeadT` on the marshalling context `ctx` and the argument slots `ls`. -/
def optCallC (f : String) (t : TowerType) (ctx : LowCT → LowCT) (ls : List Located) : LowCT :=
  .RSeq (.RLetZero exitOptTagName .TU64 (.RLetZero exitOptPayName t
    (ctx (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls))))
    (.RScalarSetExpr exitOptTagS (.SLimb exitOptTagName 0))

theorem optHeadT_some {f : String} {args : List ImpExpr} {p : String} {callC bindP : LowCT}
    (h : optHeadT A f args p = some (callC, bindP)) :
    ∃ t ctx ls, exitScalarRes f = false ∧ f ≠ "index" ∧ f ≠ "array_update" ∧
      f ≠ "array_lit" ∧ f ≠ "repeat" ∧ exitOptTys A f = some t ∧
      callMarshal A .TU64 args = some (ctx, ls) ∧ callC = optCallC f t ctx ls ∧
      ((A.lookup p = none ∧ t = .TU64 ∧
          bindP = .RScalarSetExpr p (.SLimb exitOptPayName 0)) ∨
        (A.lookup p = some t ∧ t ≠ .TU64 ∧ bindP = .RCopy ⟨p, t⟩ ⟨exitOptPayName, t⟩)) := by
  unfold optHeadT at h
  split_ifs at h with hf
  simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hf
  obtain ⟨⟨⟨⟨hs, hi⟩, hu⟩, hl⟩, hr⟩ := hf
  rcases ht : exitOptTys A f with _ | t <;> rw [ht] at h
  · cases h
  simp only at h
  rcases hm : callMarshal A .TU64 args with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
  · cases h
  simp only at h
  rcases hp : A.lookup p with _ | tp <;> rw [hp] at h
  · simp only at h
    split_ifs at h with htu
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨t, ctx, ls, hs, hi, hu, hl, hr, rfl, rfl, rfl, Or.inl ⟨rfl, htu, rfl⟩⟩
  · simp only at h
    split_ifs at h with htp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, htu⟩ := htp
    exact ⟨tp, ctx, ls, hs, hi, hu, hl, hr, rfl, rfl, rfl, Or.inr ⟨rfl, htu, rfl⟩⟩

theorem repeatHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : repeatHeadT A n args = some k) :
    ∃ v l c kN, args = [.var v, .lit l] ∧ A.lookup n = some c ∧
      valueToScalar (Value.ofLit l) = some kN ∧
      (exitArrLen c = some kN ∧ exitMarshalOk (exitElem c) = true) ∧
      callHeadAt A n "repeat" (exitElem c) c [.var v] = some k := by
  unfold repeatHeadT at h
  split at h
  · rename_i v l
    rcases hn : A.lookup n with _ | c <;> rcases hv : valueToScalar (Value.ofLit l) with _ | kN <;>
      simp only [hn, hv] at h
    all_goals first | cases h | skip
    split_ifs at h with hc
    exact ⟨v, l, c, kN, rfl, rfl, hv, hc, h⟩
  · cases h

theorem arrLitHeadN_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : arrLitHeadN A n args = some k) :
    ∃ c, A.lookup n = some c ∧
      (exitArrLen c = some args.length ∧ exitMarshalOk (exitElem c) = true ∧
        exitArgsAt A (exitElem c) args = true) ∧
      callHeadAt A n "array_lit" (exitElem c) c args = some k := by
  unfold arrLitHeadN at h
  rcases hn : A.lookup n with _ | c <;> rw [hn] at h
  · cases h
  · simp only at h
    split_ifs at h with hl
    exact ⟨c, rfl, hl, h⟩


/-! ### Simulation of the call heads -/

variable {bi N leafSpec br A}

/-- The result of a head of `let n = f(args)`: from `rs`, a state agreeing with the
    environment extended by `n ↦ r`, with the exit flag `0`, through which every run of
    the lowered body extends to a run of the head. -/
def HeadResT (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge) (A : ExitTowers)
    (env : Env) (rs : RustState) (n : String) (r : Value) (k : LowCT → LowCT) : Prop :=
  ∃ rs1, envAgreesT br A (env.extend n r) rs1 ∧ rs1.rsScalar exitRetName = 0 ∧
    ∀ bC rs', RustExec N leafSpec bC rs1 rs' → RustExec N leafSpec (k bC) rs rs'

theorem forall₂_var2 {env : Env} {a b : String} {vals : List Value}
    (h : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v)
      [.var a, .var b] vals) : ∃ va vb, vals = [va, vb] ∧ env a = some va ∧ env b = some vb := by
  rcases h with _ | ⟨⟨x, hx, hxa⟩, h⟩
  rcases h with _ | ⟨⟨y, hy, hyb⟩, h⟩
  cases h
  cases hx; cases hy
  exact ⟨_, _, rfl, hxa, hyb⟩

theorem forall₂_var3 {env : Env} {a b c : String} {vals : List Value}
    (h : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v)
      [.var a, .var b, .var c] vals) :
    ∃ va vb vc, vals = [va, vb, vc] ∧ env a = some va ∧ env b = some vb ∧ env c = some vc := by
  rcases h with _ | ⟨⟨x, hx, hxa⟩, h⟩
  rcases h with _ | ⟨⟨y, hy, hyb⟩, h⟩
  rcases h with _ | ⟨⟨z, hz, hzc⟩, h⟩
  cases h
  cases hx; cases hy; cases hz
  exact ⟨_, _, _, rfl, hxa, hyb, hzc⟩

theorem headT_scalarOp {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n f : String} {args : List ImpExpr} {se : SExpr} {vals : List Value} {r : Value}
    (hso : scalarOpHeadT A n f args = some se) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r (fun b => .RSeq (.RScalarSetExpr n se) b) := by
  obtain ⟨a, b, rfl, hnA, haA, hbA, hse⟩ := scalarOpHeadT_some A hso
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
  obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_var2 hF
  obtain ⟨hsa, hda⟩ := envAgreesT_scalar hag hargs.1 haA hva
  obtain ⟨hsb, hdb⟩ := envAgreesT_scalar hag hargs.2.1 hbA hvb
  have hop : (scalarOpExprT f (.SVar "a") (.SVar "b")).isSome = true := by
    rw [scalarOpExprT_isSome_vars f "a" "b" a b, hse]; rfl
  obtain ⟨hsr, hdr⟩ := hL.ops f va vb r _ _ hop hsa hsb hda hdb hbi
  rw [← scalarOpExprT_evalState f a b se rs hse] at hdr
  exact ⟨_, envAgreesT_extend hn hnA hsr hdr hag, ret_setScalar hn _ hret,
    fun bC rs' h => RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) h⟩

theorem rsTowerLimb_rsSetTower_same (rs : RustState) (x : String) (t : TowerType)
    (v : RustVal t) (i : Nat) : rsTowerLimb (rsSetTower rs x ⟨t, v⟩) x i = towerLimb v i := by
  simp [rsTowerLimb, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]

theorem headT_index {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : indexHeadT A n args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi "index" vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨arr, idx, t, rfl, htA, hiA, hcase⟩ := indexHeadT_some A hk
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
  obtain ⟨vArr, vIdx, rfl, hva, hvi⟩ := forall₂_var2 hF
  obtain ⟨-, arrV, harr, hbr⟩ := envAgreesT_tower hag hargs.1 htA hva
  obtain ⟨-, hdi⟩ := envAgreesT_scalar hag hargs.2.1 hiA hvi
  have harrne : exitCallName ≠ arr := (ne_of_reserved hargs.1 exitReserved_call).symm
  rcases hcase with ⟨he, hnA, rfl⟩ | ⟨t', he, hnA, rfl⟩
  swap
  · -- an element of tower type `t'`: load it into the call slot and copy it into `n`
    have hbrR := hL.indexT t t' vArr vIdx r arrV _ he hbr hdi hbi
    let D : Located := ⟨exitCallName, t'⟩
    let lv := leafSpec.arrLoad D default ⟨t, arrV⟩ (rs.rsScalar idx)
    have hload : RustExec N leafSpec (.RArrLoad D ⟨arr, t⟩ idx)
        (rsSetTower rs exitCallName ⟨t', default⟩)
        (rsSetTower (rsSetTower rs exitCallName ⟨t', default⟩) exitCallName ⟨t', lv⟩) :=
      RustExec.arrLoad D ⟨arr, t⟩ idx _ _ default arrV rfl
        (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))
        (locatedLookup_of_rsTower _ _ _ _ (by
          rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ harrne]; exact harr))
    have hagB : envAgreesT br A env
        (rsSetTower (rsSetTower rs exitCallName ⟨t', default⟩) exitCallName ⟨t', lv⟩) :=
      envAgreesT_setTower_reserved _ exitReserved_call
        (envAgreesT_setTower_reserved _ exitReserved_call hag)
    refine ⟨rsSetTower (rsSetTower (rsSetTower rs exitCallName ⟨t', default⟩) exitCallName
        ⟨t', lv⟩) n ⟨t', lv⟩, envAgreesT_extend_tower hn hnA (hL.plain _ _ _ hbi) hbrR hagB,
      hret, fun bC rs' h => ?_⟩
    exact RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _ hload
      (RustExec.seq _ _ _ _ _ (RustExec.copy ⟨n, t'⟩ ⟨exitCallName, t'⟩ _ rfl lv
        (locatedLookup_of_rsTower _ _ _ _
          (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))) h))
  obtain ⟨hsr, hdr⟩ := hL.index t vArr vIdx r arrV _ he hbr hdi hbi
  -- the states: the call slot zeroed, the element loaded, the limb copied
  let D : Located := ⟨exitCallName, .TFp⟩
  let lv := leafSpec.arrLoad D default ⟨t, arrV⟩ (rs.rsScalar idx)
  have hload : RustExec N leafSpec (.RArrLoad D ⟨arr, t⟩ idx)
      (rsSetTower rs exitCallName ⟨.TFp, default⟩)
      (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩) :=
    RustExec.arrLoad D ⟨arr, t⟩ idx _ _ default arrV rfl
      (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))
      (locatedLookup_of_rsTower _ _ _ _ (by
        rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ harrne]; exact harr))
  have hagB : envAgreesT br A env
      (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩) :=
    envAgreesT_setTower_reserved _ exitReserved_call
      (envAgreesT_setTower_reserved _ exitReserved_call hag)
  have hev : (SExpr.SLimb exitCallName 0).evalState
      (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩) =
      towerLimb lv 0 := by
    simp only [SExpr.evalState]
    exact rsTowerLimb_rsSetTower_same _ _ _ _ _
  refine ⟨rsSetScalar (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName
      ⟨.TFp, lv⟩) n (towerLimb lv 0), envAgreesT_extend hn hnA hsr hdr hagB,
    ret_setScalar hn _ hret, fun bC rs' h => ?_⟩
  have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) n
    (.SLimb exitCallName 0)
    (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩)
  rw [hev] at hset
  exact RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _ hload
    (RustExec.seq _ _ _ _ _ hset h))

theorem headT_update {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : updateHeadT A n args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi "array_update" vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨arr, idx, src, t, ctx, srcLoc, rfl, hna, htA, hiA, hsrcA, hm, hsl, rfl⟩ :=
    updateHeadT_some A hk
  subst hna
  have hargs' := hargs
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs'
  obtain ⟨vArr, vIdx, vSrc, rfl, hva, hvi, hvs⟩ := forall₂_var3 hF
  obtain ⟨-, arrV, harr, hbr⟩ := envAgreesT_tower hag hargs'.1 htA hva
  obtain ⟨-, hdi⟩ := envAgreesT_scalar hag hargs'.2.1 hiA hvi
  have hsrcOk : exitArgsOk [.var src] = true := by
    simp [exitArgsOk, hargs'.2.2.1]
  obtain ⟨rs1, hex, hS1, hT1, -, hF1⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal (exitElem t) [.var src] ctx [srcLoc] [vSrc] hm
      hsrcOk (List.Forall₂.cons ⟨src, rfl, hvs⟩ List.Forall₂.nil) rs rfl (fun _ _ => rfl)
  rcases hF1 with _ | ⟨⟨sv, hsv, hbs, hmv⟩, -⟩
  obtain ⟨sName, sTy⟩ := srcLoc
  simp only at hsl
  subst hsl
  have hbrR : br t r (leafSpec.arrStore ⟨n, t⟩ arrV (rs.rsScalar idx) ⟨exitElem t, sv⟩) := by
    rcases he : exitElemTower t with _ | t'
    · -- an array of words: the source is a scalar marshalled into `exitMarshalName src`
      have hsA : A.lookup src = none := hsrcA (by simp [he])
      obtain ⟨hsvs, hdvs⟩ := envAgreesT_scalar hag hargs'.2.2.1 hsA hvs
      simp only [callMarshal, hsA] at hm
      split_ifs at hm with hmo
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Located.mk.injEq,
        and_true] at hm
      obtain ⟨-, hsN⟩ := hm
      have h8 : 8 ≤ (exitElem t).storageBytes := by simpa [exitMarshalOk] using hmo
      rw [hmv src hsN.symm]
      exact hL.update n (exitMarshalName src) t vArr vIdx vSrc r arrV (rs.rsScalar idx)
        (rs.rsScalar src) he h8 hbr hdi hsvs hdvs hbi
    · exact hL.updateT n t vArr vIdx vSrc r arrV sv (rs.rsScalar idx) (by simp [he]) hbr hdi
        hbs hbi
  have harr1 : rs1.rsTower n = some ⟨t, arrV⟩ := by
    rw [hT1 n (ne_marshal_of_nonreserved hargs'.1)]; exact harr
  have hstore : RustExec N leafSpec (.RArrStore ⟨n, t⟩ idx ⟨sName, exitElem t⟩) rs1
      (rsSetTower rs1 n ⟨t, leafSpec.arrStore ⟨n, t⟩ arrV (rs.rsScalar idx)
        ⟨exitElem t, sv⟩⟩) :=
    RustExec.arrStore ⟨n, t⟩ idx ⟨sName, exitElem t⟩ rs1 _ arrV sv (congrFun hS1 idx)
      (locatedLookup_of_rsTower _ _ _ _ harr1) (locatedLookup_of_rsTower _ _ _ _ hsv)
  have hag1 : envAgreesT br A env rs1 :=
    envAgreesT_of_eqOn hS1 (fun y hy => hT1 y (ne_marshal_of_nonreserved hy)) hag
  refine ⟨_, envAgreesT_extend_tower hn htA (hL.plain _ _ _ hbi) hbrR hag1, ?_,
    fun bC rs' h => RustExec.seq _ _ _ _ _ (hex _ _ hstore) h⟩
  show rs1.rsScalar exitRetName = 0
  rw [hS1]; exact hret

/-- The head of a call marshalling its scalar arguments at `dt` into a result slot of type
    `dr`, for a value `r` without a control-flow tag that the leaf output agrees with at the
    placement of the bound name, whenever the argument values are related to the slots the
    call reads. -/
theorem headT_callAtR {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n f : String} {dt dr : TowerType} {args : List ImpExpr} {k : LowCT → LowCT}
    {vals : List Value} {r : Value} (hcf : r.isControlFlow = false)
    (hT : A.lookup n = some dr → ∀ (ls : List Located)
      (argList : List (Σ t : TowerType, RustVal t)) (oldV : RustVal dr),
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
      (exitArgsAt A dt args = true → ∀ p ∈ argList, p.1 = dt) →
      (∃ ctx, callMarshal A dt args = some (ctx, ls)) →
      argList.map (·.1) = ls.map (·.locDst) →
      br dr r (leafSpec.call f dr (ls.map (·.locDst)) oldV argList))
    (hS : A.lookup n = none → ∀ (ls : List Located)
      (argList : List (Σ t : TowerType, RustVal t)) (oldV : RustVal dr),
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
      (∃ ctx, callMarshal A dt args = some (ctx, ls)) →
      argList.map (·.1) = ls.map (·.locDst) →
      ScalarValN r ∧
        valueToScalar r = some (towerLimb (leafSpec.call f dr (ls.map (·.locDst)) oldV argList) 0))
    (hk : callHeadAt A n f dt dr args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨ctx, ls, hm, hcase⟩ := callHeadAt_some A hk
  have hloc := callMarshal_locDst A dt args ctx ls hm
  have hT0 : ∀ y, exitReserved y = false →
      (rsSetTower rs exitCallName ⟨dr, default⟩).rsTower y = rs.rsTower y := fun y hy =>
    CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
      (ne_of_reserved hy exitReserved_call).symm
  obtain ⟨rs1, hex, hS1, hT1, -, hF1'⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal dt args ctx ls vals hm hargs hF
      (rsSetTower rs exitCallName ⟨dr, default⟩) rfl hT0
  have hF1 : List.Forall₂ (fun v (a : Located) => ∃ val,
      rs1.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧ br a.locDst v val) vals ls :=
    hF1'.imp fun _ _ h => by
      obtain ⟨val, h1, h2, -⟩ := h
      exact ⟨val, h1, h2⟩
  have hcall1 : rs1.rsTower exitCallName = some ⟨dr, default⟩ := by
    rw [hT1 exitCallName (fun z => exitCallName_ne_marshal z)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  let argList := ls.filterMap fun a => rs1.rsTower a.locVar
  let resV := leafSpec.call f dr (ls.map (·.locDst)) default argList
  have hcall : RustExec N leafSpec (.RCall f ⟨exitCallName, dr⟩ ls) rs1
      (rsSetTower rs1 exitCallName ⟨dr, resV⟩) :=
    RustExec.call f ⟨exitCallName, dr⟩ ls rs1 default argList
      (locatedLookup_of_rsTower _ _ _ _ hcall1) rfl (forall₂_rsTower_typed hF1)
  have hC : RustExec N leafSpec (.RLetZero exitCallName dr
      (ctx (.RCall f ⟨exitCallName, dr⟩ ls))) rs (rsSetTower rs1 exitCallName ⟨dr, resV⟩) :=
    RustExec.letZero _ _ _ _ _ (hex _ _ hcall)
  have hF2 := forall₂_filterMap_rsTower hF1
  have htys : argList.map (·.1) = ls.map (·.locDst) :=
    filterMap_rsTower_types (forall₂_rsTower_typed hF1)
  have hag2 : envAgreesT br A env (rsSetTower rs1 exitCallName ⟨dr, resV⟩) :=
    envAgreesT_setTower_reserved _ exitReserved_call
      (envAgreesT_of_eqOn hS1 (fun y hy => by
        rw [hT1 y (ne_marshal_of_nonreserved hy), hT0 y hy]) hag)
  have hret2 : (rsSetTower rs1 exitCallName ⟨dr, resV⟩).rsScalar exitRetName = 0 := by
    show rs1.rsScalar exitRetName = 0
    rw [hS1]; exact hret
  rcases hcase with ⟨hnA, rfl⟩ | ⟨hnA, rfl⟩
  · obtain ⟨hsr, hdr⟩ := hS hnA ls argList default hF2 ⟨ctx, hm⟩ htys
    have hev : (SExpr.SLimb exitCallName 0).evalState
        (rsSetTower rs1 exitCallName ⟨dr, resV⟩) = towerLimb resV 0 := by
      simp only [SExpr.evalState]
      exact rsTowerLimb_rsSetTower_same _ _ _ _ _
    refine ⟨rsSetScalar (rsSetTower rs1 exitCallName ⟨dr, resV⟩) n (towerLimb resV 0),
      envAgreesT_extend hn hnA hsr hdr hag2, ret_setScalar hn _ hret2, fun bC rs' h => ?_⟩
    have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) n
      (.SLimb exitCallName 0) (rsSetTower rs1 exitCallName ⟨dr, resV⟩)
    rw [hev] at hset
    exact RustExec.seq _ _ _ _ _ hC (RustExec.seq _ _ _ _ _ hset h)
  · have hty : exitArgsAt A dt args = true → ∀ p ∈ argList, p.1 = dt := by
      intro hat p hp
      obtain ⟨a, ha, hap⟩ := List.mem_filterMap.mp hp
      obtain ⟨v, hv⟩ := forall₂_rsTower_typed hF1 a ha
      rw [hv, Option.some.injEq] at hap
      subst hap
      exact hloc hat a ha
    have hbrR := hT hnA ls argList default hF2 hty ⟨ctx, hm⟩ htys
    refine ⟨rsSetTower (rsSetTower rs1 exitCallName ⟨dr, resV⟩) n ⟨dr, resV⟩,
      envAgreesT_extend_tower hn hnA hcf hbrR hag2, hret2,
      fun bC rs' h => ?_⟩
    refine RustExec.seq _ _ _ _ _ hC (RustExec.seq _ _ _ _ _ ?_ h)
    exact RustExec.copy ⟨n, dr⟩ ⟨exitCallName, dr⟩ _ rfl resV
      (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))

/-- The head of a call marshalling its scalar arguments at `dt` into a result slot of type
    `dr`, under the leaf condition of `f` at `dr` for the placement of the bound name. -/
theorem headT_callAt {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n f : String} {dt dr : TowerType} {args : List ImpExpr} {k : LowCT → LowCT}
    {vals : List Value} {r : Value}
    (hT : A.lookup n = some dr → LeafCallAgreesArgsLen bi leafSpec f dr br vals.length)
    (hS : A.lookup n = none → LeafCallScalar bi leafSpec f dr br)
    (hk : callHeadAt A n f dt dr args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k :=
  headT_callAtR hL (hL.plain _ _ _ hbi)
    (fun h ls argList oldV hF2 _ _ _ => hT h ls vals argList oldV r rfl hbi hF2)
    (fun h ls argList oldV hF2 _ _ => hS h ls vals argList oldV r hbi hF2) hk hn hargs hF hag hret

/-- `headT_callAt` for arguments held in towers at `dt` (`exitArgsAt`), under the leaf
    condition of `f` on argument slots of the type `dt`. -/
theorem headT_callAtTyped {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA) {env : Env} {rs : RustState}
    {n f : String} {dt dr : TowerType} {args : List ImpExpr} {k : LowCT → LowCT}
    {vals : List Value} {r : Value} (hat : exitArgsAt A dt args = true)
    (hT : A.lookup n = some dr → LeafCallAgreesArgsAt bi leafSpec f dr br vals.length dt)
    (hS : A.lookup n = none → LeafCallScalar bi leafSpec f dr br)
    (hk : callHeadAt A n f dt dr args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k :=
  headT_callAtR hL (hL.plain _ _ _ hbi)
    (fun h ls argList oldV hF2 hty _ _ => hT h ls vals argList oldV r rfl (hty hat) hbi hF2)
    (fun h ls argList oldV hF2 _ _ => hS h ls vals argList oldV r hbi hF2) hk hn hargs hF hag hret

/-- Every head of `appHeadT` satisfies `HeadResT` at the builtin's value. -/
theorem headT_app (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) {env : Env}
    {rs : RustState}
    {n f : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : appHeadT A n f args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  unfold appHeadT at hk
  rcases hso : scalarOpHeadT A n f args with _ | se
  · rw [hso] at hk
    simp only at hk
    split_ifs at hk with hfi hfu hfl hfr
    · subst hfi
      exact headT_index hL hk hn hargs hF hbi hag hret
    · subst hfu
      exact headT_update hL hk hn hargs hF hbi hag hret
    · subst hfl
      obtain ⟨c, hnA, ⟨hlen, hmo, hat⟩, hc⟩ := arrLitHeadN_some A hk
      rw [hF.length_eq] at hlen
      exact headT_callAtTyped hL hat (fun _ => hL.arrLitN c _ hlen hmo)
        (fun h => by rw [hnA] at h; cases h) hc hn hargs hF hbi hag hret
    · obtain ⟨v, l, -, -, rfl, -⟩ := repeatHeadT_some A hk
      simp [exitArgsOk] at hargs
    · obtain ⟨dt, dr, hc, hcase⟩ := callHeadT_some A hk
      rcases hcase with ⟨hsc, hnA, rfl⟩ | ⟨hsc, hce, hd, hdo, hnone⟩ | ⟨hsc, hce, -, hnA, rfl⟩ |
          ⟨ts, hsc, hca, rfl, hmts, hnone⟩
      · exact headT_callAt hL (fun h => by rw [hnA] at h; cases h) (fun _ => hL.callSR hsc) hc
          hn hargs hF hbi hag hret
      · refine headT_callAt hL
          (fun _ => leafCallAgreesArgsLen_of (hL.callD f dr hd hdo hce hsc hfi hfu hfl hfr) _)
          (fun h0 => ?_) hc hn hargs hF hbi hag hret
        obtain rfl := hnone h0
        exact hL.wordD f hd hce hsc hfi hfu hfl hfr
      · exact headT_callAt hL
          (fun _ => leafCallAgreesArgsLen_of (hL.callT f hsc hfi hfu hfl hfr hce) _)
          (fun h => by rw [hnA] at h; cases h) hc hn hargs hF hbi hag hret
      · have hts : ∀ (ls : List Located) (argList : List (Σ t : TowerType, RustVal t)),
            (∃ ctx, callMarshal A .TU64 args = some (ctx, ls)) →
            argList.map (·.1) = ls.map (·.locDst) → argList.map (·.1) = ts := by
          intro ls argList ⟨ctx, hm⟩ hty
          rw [hm] at hmts
          simp only [Option.map_some, Option.some.injEq] at hmts
          rw [hty, hmts]
        refine headT_callAtR hL (hL.plain _ _ _ hbi)
          (fun _ ls argList oldV hF2 _ hm hty =>
            hL.callA f ts dr hca hsc hfi hfu hfl hfr ls vals argList oldV r
              (hts ls argList hm hty) hbi hF2)
          (fun h0 ls argList oldV hF2 hm hty => ?_) hc hn hargs hF hag hret
        obtain rfl := hnone h0
        exact hL.wordA f ts hca hsc hfi hfu hfl hfr ls vals argList oldV r
          (hts ls argList hm hty) hbi hF2
  · rw [hso] at hk
    simp only [Option.some.injEq] at hk
    subst hk
    exact headT_scalarOp hL hso hn hargs hF hbi hag hret

/-- The head of `let n = repeat(v, l)` with a literal count: `HeadResT` at the builtin's
    value on the value of `v` and the value of `l`. -/
theorem headT_repeat (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) {env : Env}
    {rs : RustState} {n v : String} {l : ImpLit} {k : LowCT → LowCT} {vv r : Value}
    (hk : repeatHeadT A n [.var v, .lit l] = some k) (hn : exitReserved n = false)
    (hvr : exitReserved v = false) (hv : env v = some vv)
    (hbi : bi "repeat" [vv, Value.ofLit l] = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨v', l', c, kN, hargs, hnA, hkN, ⟨hlen, hmo⟩, hc⟩ := repeatHeadT_some A hk
  simp only [List.cons.injEq, ImpExpr.var.injEq, ImpExpr.lit.injEq, and_true] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  refine headT_callAtR hL (hL.plain _ _ _ hbi)
    (fun _ ls argList oldV hF2 _ _ _ =>
      hL.repeatN c kN hlen hmo ls vv _ r argList oldV hkN hbi hF2)
    (fun h => by rw [hnA] at h; cases h) hc hn (by simp [exitArgsOk, hvr])
    (List.Forall₂.cons ⟨_, rfl, hv⟩ List.Forall₂.nil) hag hret

theorem exitReserved_optTag : exitReserved exitOptTagName = true := by decide
theorem exitReserved_optPay : exitReserved exitOptPayName = true := by decide
theorem exitReserved_optTagS : exitReserved exitOptTagS = true := by decide
theorem exitOptTagS_ne_ret : exitOptTagS ≠ exitRetName := by decide

theorem exitOptTagName_ne_marshal (x : String) : exitOptTagName ≠ exitMarshalName x := by
  intro h
  have h' := congrArg (fun s => s.toList.take 8) h
  simp only [exitMarshalName, String.toList_append] at h'
  rw [List.take_append_of_le_length (by decide)] at h'
  revert h'; decide

theorem exitOptPayName_ne_marshal (x : String) : exitOptPayName ≠ exitMarshalName x := by
  intro h
  have h' := congrArg (fun s => s.toList.take 8) h
  simp only [exitMarshalName, String.toList_append] at h'
  rw [List.take_append_of_le_length (by decide)] at h'
  revert h'; decide

/-- **The call of an `Option` match.** From a state agreeing with `env`, the call
    `optCallC f t ctx ls` of `optHeadT` on argument variables holding `vals` with
    `bi f vals = some vRes`, under `LeafCallOption` of `f` at `t`, runs to a state agreeing
    with `env`, with the exit flag kept, in which the builtin's result is an `Option` whose
    tag is the scalar slot `exitOptTagS` and whose payload agrees with the tower slot
    `exitOptPayName` by `optPayloadRel`. -/
theorem optCall_sim {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState} {f : String} {t : TowerType} {ctx : LowCT → LowCT}
    {ls : List Located} {args : List ImpExpr} {vals : List Value} {vRes : Value}
    (hm : callMarshal A .TU64 args = some (ctx, ls)) (hlc : LeafCallOption bi leafSpec f t br)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some vRes) (hag : envAgreesT br A env rs) :
    ∃ o rs2, vRes = .option o ∧ RustExec N leafSpec (optCallC f t ctx ls) rs rs2 ∧
      envAgreesT br A env rs2 ∧ rs2.rsScalar exitRetName = rs.rsScalar exitRetName ∧
      rs2.rsScalar exitOptTagS = (if o.isSome then 1 else 0) ∧
      ∀ w, o = some w → w.isControlFlow = false ∧
        ∃ payOut, rs2.rsTower exitOptPayName = some ⟨t, payOut⟩ ∧ optPayloadRel br t w payOut := by
  let rs0 := rsSetTower (rsSetTower rs exitOptTagName ⟨.TU64, default⟩) exitOptPayName
    ⟨t, default⟩
  have hT0 : ∀ y, exitReserved y = false → rs0.rsTower y = rs.rsTower y := fun y hy => by
    simp only [rs0]
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
        (ne_of_reserved hy exitReserved_optPay).symm,
      CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
        (ne_of_reserved hy exitReserved_optTag).symm]
  obtain ⟨rs1, hex, hS1, hT1, -, hF1'⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal .TU64 args ctx ls vals hm hargs hF rs0 rfl hT0
  have hF1 : List.Forall₂ (fun v (a : Located) => ∃ val,
      rs1.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧ br a.locDst v val) vals ls :=
    hF1'.imp fun _ _ h => by
      obtain ⟨val, h1, h2, -⟩ := h
      exact ⟨val, h1, h2⟩
  have htag1 : rs1.rsTower exitOptTagName = some ⟨.TU64, default⟩ := by
    rw [hT1 _ (fun z => exitOptTagName_ne_marshal z)]
    simp only [rs0]
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ (by decide)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  have hpay1 : rs1.rsTower exitOptPayName = some ⟨t, default⟩ := by
    rw [hT1 _ (fun z => exitOptPayName_ne_marshal z)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  let argList := ls.filterMap fun a => rs1.rsTower a.locVar
  let dests : List Located := [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩]
  let rs2 := CatCrypt.Crypto.Jasmin.LowCT.callNUpdate leafSpec f (ls.map (·.locDst)) argList 0
    dests rs1
  have hcall : RustExec N leafSpec (.RCallN f dests ls) rs1 rs2 :=
    RustExec.callN f dests ls rs1 argList rfl (forall₂_rsTower_typed hF1) (by
      intro d hd
      simp only [dests, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨_, htag1⟩
      · exact ⟨_, hpay1⟩)
  have hnd : (dests.map (·.locVar)).Nodup := by simp [dests, exitOptTagName, exitOptPayName]
  let tagOut := leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 0) .TU64
    (ls.map (·.locDst)) ((CatCrypt.Crypto.Jasmin.LowCT.locatedLookup rs1
      ⟨exitOptTagName, .TU64⟩).getD default) argList
  let payOut := leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 1) t
    (ls.map (·.locDst)) ((CatCrypt.Crypto.Jasmin.LowCT.locatedLookup rs1
      ⟨exitOptPayName, t⟩).getD default) argList
  have htag2 : rs2.rsTower exitOptTagName = some ⟨.TU64, tagOut⟩ :=
    CatCrypt.Crypto.Jasmin.LowCT.rsTower_callNUpdate_nth leafSpec f _ argList dests 0 0 rs1
      ⟨exitOptTagName, .TU64⟩ hnd rfl
  have hpay2 : rs2.rsTower exitOptPayName = some ⟨t, payOut⟩ :=
    CatCrypt.Crypto.Jasmin.LowCT.rsTower_callNUpdate_nth leafSpec f _ argList dests 0 1 rs1
      ⟨exitOptPayName, t⟩ hnd rfl
  have hS2 : rs2.rsScalar = rs.rsScalar := by
    rw [CatCrypt.Crypto.Jasmin.LowCT.callNUpdate_rsScalar]; exact hS1
  have hT2 : ∀ y, exitReserved y = false → rs2.rsTower y = rs.rsTower y := fun y hy => by
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsTower_callNUpdate_other _ _ _ _ _ _ _ _ (by
        simp only [dests, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        exact ⟨ne_of_reserved hy exitReserved_optTag, ne_of_reserved hy exitReserved_optPay⟩),
      hT1 y (ne_marshal_of_nonreserved hy), hT0 y hy]
  have hag2 : envAgreesT br A env rs2 := envAgreesT_of_eqOn hS2 hT2 hag
  obtain ⟨o, rfl, htag, hpay⟩ := hlc ls vals argList _ _ vRes hbi (forall₂_filterMap_rsTower hF1)
  let rs3 := rsSetScalar rs2 exitOptTagS (towerLimb tagOut 0)
  have hev : (SExpr.SLimb exitOptTagName 0).evalState rs2 = towerLimb tagOut 0 := by
    simp only [SExpr.evalState, CatCrypt.Crypto.Jasmin.LowCT.rsTowerLimb, htag2]
  refine ⟨o, rs3, rfl, ?_, envAgreesT_set_reserved _ exitReserved_optTagS hag2, ?_, ?_,
    fun w hw => ⟨(hpay w hw).1, payOut, hpay2, (hpay w hw).2⟩⟩
  · have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) exitOptTagS
      (.SLimb exitOptTagName 0) rs2
    rw [hev] at hset
    exact RustExec.seq _ _ _ _ _ (RustExec.letZero _ _ _ _ _ (RustExec.letZero _ _ _ _ _
      (hex _ _ hcall))) hset
  · show (rsSetScalar rs2 exitOptTagS _).rsScalar exitRetName = _
    rw [rsScalar_rsSetScalar, if_neg exitOptTagS_ne_ret.symm, hS2]
  · show (rsSetScalar rs2 exitOptTagS _).rsScalar exitOptTagS = _
    rw [rsScalar_rsSetScalar, if_pos rfl]
    exact htag

theorem head_app (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) (n f : String)
    (args : List ImpExpr)
    (body : ImpExpr) : HeadSimT bi N leafSpec br A R n (.app f args) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitReserved n = false ∧ exitArgsOkT f args = true := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1, hok.1.1.2⟩)
  obtain ⟨hn, hargsT⟩ := hh
  have hk' : appHeadT A n f args = some k := hk
  by_cases hargs : exitArgsOk args = true
  · obtain ⟨vals, r, hF, hbi, hrun'⟩ :=
      letBind_app_inv bi fuel hL.plain n f args body hargs env env' o hrun hval
    obtain ⟨rs1, hag1, hret1, hex⟩ := headT_app hL hk' hn hargs hF hbi hag hret
    exact ⟨_, rs1, hrun', hag1, hret1, hex⟩
  · have hrep : f = "repeat" ∧ exitRepeatArgsOk args = true := by
      simpa [exitArgsOkT, hargs] using hargsT
    obtain ⟨rfl, hra⟩ := hrep
    match args, hra with
    | [.var v, .lit l], hra =>
      simp only [exitRepeatArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hra
      obtain ⟨vv, r, hv, hbi, hrun'⟩ :=
        letBind_repeat_inv bi fuel hL.plain n v l body env env' o hrun hval
      have hkr : repeatHeadT A n [.var v, .lit l] = some k := by
        simpa [appHeadT, scalarOpHeadT] using hk'
      obtain ⟨rs1, hag1, hret1, hex⟩ := headT_repeat hL hkr hn hra.1 hv hbi hag hret
      exact ⟨_, rs1, hrun', hag1, hret1, hex⟩

end Heads

/-! ## §13  The arms without a loop -/

section Arms

variable (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
  (A : ExitTowers) (R : ExitRes)

theorem exitSimTy_var (x : String) : ExitSimTy bi N leafSpec br A R (.var x) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hx : exitReserved x = false ∧ (tl = true → ExitRes.ofPlace (A.lookup x) = R) := by
    cases tl <;> cases fl <;> simp_all [exitSimOkT]
  rw [denote'_var_run] at hrun
  cases hv : env x with
  | none =>
    rw [hv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  | some v =>
    rw [hv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    have hcf := envAgreesT_not_cf hag hx.1 hv
    cases tl with
    | false =>
      have hK' : haxToLowCTKT A false fl (.var x) = some (.RSkip, false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      exact ⟨rs, RustExec.skip rs,
        (envAgreesExitT_val hcf).mpr ⟨hret, hag, fun h => by cases h⟩, fun _ => hret⟩
    | true =>
      have hR := hx.2 rfl
      have hK' : haxToLowCTKT A true fl (.var x) =
          (resultStoreT A (.var x)).map fun s => (s, false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      rcases hA : A.lookup x with _ | t
      · rw [hA] at hR
        subst hR
        simp only [resultStoreT, hA, resultStore, storeScalar, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨-, hdec⟩ := envAgreesT_scalar hag hx.1 hA hv
        obtain ⟨h0, hag', hres⟩ := res_writeT rs (rs.rsScalar x) hret hag
        exact ⟨_, RustExec.scalarSetExpr _ _ rs,
          (envAgreesExitT_val hcf).mpr ⟨h0, hag', fun _ => by
            show valueToScalar v = some _
            rw [hdec]; exact congrArg some hres.symm⟩,
          fun _ => h0⟩
      · rw [hA] at hR
        subst hR
        simp only [resultStoreT, hA, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hx.1 hA hv
        refine ⟨rsSetTower rs exitResName ⟨t, val⟩,
          RustExec.copy ⟨exitResName, t⟩ ⟨x, t⟩ rs rfl val (locatedLookup_of_rsTower rs x t val hval'),
          (envAgreesExitT_val hcf).mpr ⟨hret, envAgreesT_setTower_reserved _ exitReserved_res hag,
            fun _ => ⟨val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _, hbr⟩⟩,
          fun _ => hret⟩

theorem exitSimTy_unitVal : ExitSimTy bi N leafSpec br A R .unitVal := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [denote'_unitVal_run] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases tl with
  | false =>
    have hK' : haxToLowCTKT A false fl .unitVal = some (.RSkip, false) := by cases fl <;> rfl
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    exact ⟨rs, RustExec.skip rs,
      (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩, fun _ => hret⟩
  | true =>
    have hR : R = .scalar := by
      cases fl <;> simpa [exitSimOkT, eq_comm] using hok
    subst hR
    have hK' : haxToLowCTKT A true fl .unitVal = some (.RScalarSet exitResName 0, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨h0, hag', hres⟩ := res_writeT rs 0 hret hag
    exact ⟨_, RustExec.scalarSet _ _ rs,
      (envAgreesExitT_val rfl).mpr ⟨h0, hag', fun _ => by
        show valueToScalar Value.unit = some _
        rw [hres]; rfl⟩, fun _ => h0⟩

/-- The value and word of a literal of `exitLitOk` that `storeScalar` stores. -/
theorem storeScalar_lit {slot : String} {l : ImpLit} {s : LowCT} (hl : exitLitOk l = true)
    (hs : storeScalar slot (.lit l) = some s) :
    ∃ k, ScalarValN (Value.ofLit l) ∧ valueToScalar (Value.ofLit l) = some k ∧
      ∀ N leafSpec (rs : RustState), RustExec N leafSpec s rs (rsSetScalar rs slot k) := by
  cases l with
  | uintLit w m =>
    simp only [storeScalar, Option.some.injEq] at hs
    subst hs
    refine ⟨_, ?_, rfl, fun N leafSpec rs => RustExec.scalarSet _ _ _⟩
    show m % w.modulus < 2 ^ 64
    cases w <;> simp only [IntWidth.modulus, IntWidth.bits] <;> first
      | omega | (simp only [exitLitOk] at hl; exact absurd hl (by decide))
  | int z =>
    simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [storeScalar, hl.1, if_true, Option.some.injEq] at hs
    subst hs
    exact ⟨_, hl, by simp [valueToScalar, Value.ofLit, hl.1],
      fun N leafSpec rs => RustExec.scalarSet _ _ _⟩
  | bool b =>
    simp only [storeScalar, Option.some.injEq] at hs
    subst hs
    exact ⟨_, trivial, valueToScalar_bool b, fun N leafSpec rs => RustExec.scalarSet _ _ _⟩
  | _ => simp [storeScalar] at hs

theorem exitSimTy_lit (l : ImpLit) : ExitSimTy bi N leafSpec br A R (.lit l) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [denote'_lit_run] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases tl with
  | false => cases fl <;> simp [exitSimOkT] at hok
  | true =>
    have hh : exitLitOk l = true ∧ R = .scalar := by
      cases fl <;> simpa [exitSimOkT] using hok
    obtain ⟨hl, rfl⟩ := hh
    have hK' : haxToLowCTKT A true fl (.lit l) =
        (resultStore (.lit l)).map fun s => (s, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    rcases hs : resultStore (.lit l) with _ | s
    · rw [hs] at hK; cases hK
    rw [hs] at hK
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨k, hsv, hk, hex⟩ := storeScalar_lit hl hs
    obtain ⟨h0, hag', hres⟩ := res_writeT rs k hret hag
    exact ⟨_, hex N leafSpec rs, (envAgreesExitT_val hsv.not_cf).mpr ⟨h0, hag', fun _ => by
      show valueToScalar _ = some _
      rw [hres]; exact hk⟩, fun _ => h0⟩

theorem exitReserved_resComp (i : Nat) : exitReserved (exitResCompName i) = true := by
  show "__exit_".toList.isPrefixOf (exitResCompName i).toList = true
  simp [exitResCompName]

theorem exitResCompName_inj {i j : Nat} (h : exitResCompName i = exitResCompName j) : i = j := by
  have := congrArg String.length h
  simpa [exitResCompName, String.length_append] using this

theorem exitResCompName_ne_ret (i : Nat) : exitResCompName i ≠ exitRetName := by
  have hp : "__exit_rc".toList.isPrefixOf exitRetName.toList = false := by decide
  rintro h
  rw [← h] at hp
  simp [exitResCompName] at hp

/-- A run of a tuple ends in a value only when its components evaluate to values: the
    value is the tuple of the component values, in the environment the components end in. -/
theorem denote'_tuple_inv (fuel : Nat) (es : List ImpExpr) (env env' : Env) (o : Outcome)
    (h : (denote' bi fuel (.tuple es)).run env = (o, env')) (hval : ∃ v, o = .val v) :
    ∃ vals, (_root_.Hax.denoteArgs' bi fuel es).run env = (some vals, env') ∧
      o = .val (.tuple vals) := by
  simp only [denote', StateT.run, bind, Bind.bind, StateT.bind] at h
  rcases hA : _root_.Hax.denoteArgs' bi fuel es env with ⟨_ | vals, e1⟩
  · rw [hA] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    obtain ⟨_, h'⟩ := hval; cases h'
  · rw [hA] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨vals, hA, rfl⟩

/-- The component stores `tupleStoreT A i es` of a tuple of variables bound to `vals`:
    from a state agreeing with the environment, they run to a state agreeing with it, with
    the exit flag and the slots of the components before `i` unchanged, where component
    `j` of `vals` agrees with the slot `exitResCompName (i + j)`. -/
theorem tupleStoreT_sim {env : Env} :
    ∀ (es : List ImpExpr) (vals : List Value),
      List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) es vals →
      exitArgsOk es = true →
      ∀ (i : Nat) (s : LowCT) (rs : RustState), tupleStoreT A i es = some s →
        envAgreesT br A env rs →
        ∃ rs', RustExec N leafSpec s rs rs' ∧ envAgreesT br A env rs' ∧
          rs'.rsScalar exitRetName = rs.rsScalar exitRetName ∧
          (∀ (j : Nat) (w : Value), vals[j]? = some w →
            compAgreesT br (exitResCompName (i + j)) w rs') ∧
          (∀ k, k < i → rs'.rsScalar (exitResCompName k) = rs.rsScalar (exitResCompName k) ∧
            rs'.rsTower (exitResCompName k) = rs.rsTower (exitResCompName k))
  | [], vals, hF, _, i, s, rs, hs, hag => by
    cases hF
    simp only [tupleStoreT, Option.some.injEq] at hs
    subst hs
    exact ⟨rs, RustExec.skip rs, hag, rfl, fun j w h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
  | a :: es, vals, hF, hargs, i, s, rs, hs, hag => by
    rcases hF with _ | ⟨⟨x, rfl, hv⟩, hF⟩
    rename_i v vals
    simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
    simp only [tupleStoreT] at hs
    rcases hr : tupleStoreT A (i + 1) es with _ | rest
    · rw [hr] at hs; cases hs
    rw [hr] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    have hne : ∀ k, k < i → exitResCompName k ≠ exitResCompName i := fun k hk h =>
      absurd (exitResCompName_inj h) (Nat.ne_of_lt hk)
    rcases hA : A.lookup x with _ | t
    · rw [hA] at hs
      subst hs
      obtain ⟨hsv, hdec⟩ := envAgreesT_scalar hag hargs.1 hA hv
      let rs1 := rsSetScalar rs (exitResCompName i) (rs.rsScalar x)
      have hag1 : envAgreesT br A env rs1 :=
        envAgreesT_set_reserved _ (exitReserved_resComp i) hag
      obtain ⟨rs', hex, hag', hret', hcomp, hframe⟩ :=
        tupleStoreT_sim es vals hF hargs.2 (i + 1) rest rs1 hr hag1
      refine ⟨rs', RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ rs) hex, hag', ?_, ?_, ?_⟩
      · rw [hret']
        simp [rs1, rsScalar_rsSetScalar, Ne.symm (exitResCompName_ne_ret i)]
      · intro j w hw
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          refine Or.inl ⟨hsv, ?_⟩
          rw [Nat.add_zero, (hframe i (Nat.lt_succ_self i)).1]
          simp [rs1, rsScalar_rsSetScalar, hdec]
        | succ j =>
          simp only [List.getElem?_cons_succ] at hw
          have := hcomp j w hw
          rwa [show i + 1 + j = i + (j + 1) by omega] at this
      · intro k hk
        obtain ⟨h1, h2⟩ := hframe k (Nat.lt_succ_of_lt hk)
        refine ⟨?_, h2⟩
        rw [h1]
        simp [rs1, rsScalar_rsSetScalar, hne k hk]
    · rw [hA] at hs
      subst hs
      obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hargs.1 hA hv
      let rs1 := rsSetTower rs (exitResCompName i) ⟨t, val⟩
      have hag1 : envAgreesT br A env rs1 :=
        envAgreesT_setTower_reserved _ (exitReserved_resComp i) hag
      obtain ⟨rs', hex, hag', hret', hcomp, hframe⟩ :=
        tupleStoreT_sim es vals hF hargs.2 (i + 1) rest rs1 hr hag1
      refine ⟨rs', RustExec.seq _ _ _ _ _
        (RustExec.copy ⟨exitResCompName i, t⟩ ⟨x, t⟩ rs rfl val
          (locatedLookup_of_rsTower rs x t val hval')) hex, hag', hret', ?_, ?_⟩
      · intro j w hw
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          subst hw
          refine Or.inr ⟨t, val, ?_, hbr⟩
          rw [Nat.add_zero, (hframe i (Nat.lt_succ_self i)).2]
          exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
        | succ j =>
          simp only [List.getElem?_cons_succ] at hw
          have := hcomp j w hw
          rwa [show i + 1 + j = i + (j + 1) by omega] at this
      · intro k hk
        obtain ⟨h1, h2⟩ := hframe k (Nat.lt_succ_of_lt hk)
        refine ⟨h1, ?_⟩
        rw [h2]
        exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ (hne k hk).symm

theorem exitSimOkT_app_inv {tl il : Bool} {f : String} {args : List ImpExpr}
    (h : exitSimOkT A R tl il (.app f args) = true) :
    tl = true ∧ ((f = "None" ∧ args = [] ∧ R.isOption = true) ∨
      ∃ x, f = "Some" ∧ args = [.var x] ∧ exitReserved x = false ∧ R = .option (A.lookup x)) := by
  unfold exitSimOkT at h
  split at h <;> simp_all

theorem exitResCompName_ne_res (i : Nat) : exitResCompName i ≠ exitResName := by
  have hp : "__exit_rc".toList.isPrefixOf exitResName.toList = false := by decide
  rintro h
  rw [← h] at hp
  simp [exitResCompName] at hp

/-- **The `Option` tails** `None()` and `Some(x)`: the tag `0` or `1` is stored into the
    scalar result slot and the payload of `Some(x)` into the slot `exitResCompName 0`. -/
theorem exitSimTy_app (hC : OptCtors bi) (f : String) (args : List ImpExpr) :
    ExitSimTy bi N leafSpec br A R (.app f args) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  obtain ⟨rfl, hcase⟩ := exitSimOkT_app_inv A R hok
  have hK' : haxToLowCTKT A true fl (.app f args) =
      (resultStoreT A (.app f args)).map fun s => (s, false) := by
    cases fl <;> rfl
  rw [hK'] at hK
  rw [denote'_app_run] at hrun
  rcases hcase with ⟨rfl, rfl, hR⟩ | ⟨x, rfl, rfl, hx, rfl⟩
  · simp only [resultStoreT, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denoteArgs'_nil_run] at hrun
    cases hbi : bi "None" [] with
    | none =>
      simp only [hbi] at hrun
      obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨-, rfl⟩ := hC.1 [] r hbi
      obtain ⟨h0, hag', hres⟩ := res_writeT rs 0 hret hag
      obtain ⟨p, rfl⟩ : ∃ p, R = .option p := by
        cases R <;> simp_all [ExitRes.isOption]
      exact ⟨_, RustExec.scalarSet _ _ rs,
        (envAgreesExitT_val rfl).mpr ⟨h0, hag', fun _ => Or.inl ⟨rfl, hres⟩⟩, fun _ => h0⟩
  · have hargs : exitArgsOk [.var x] = true := by simp [exitArgsOk, hx]
    rcases hA : (_root_.Hax.denoteArgs' bi fuel [.var x]).run env with ⟨oa, e1⟩
    obtain ⟨he1, hF⟩ := denoteArgs'_vars_inv bi fuel [.var x] hargs env e1 oa hA
    subst e1
    rw [hA] at hrun
    rcases oa with _ | vals
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    obtain ⟨v, rfl, hv⟩ : ∃ v, vals = [v] ∧ env x = some v := by
      rcases hF vals rfl with _ | ⟨⟨y, hy, hyv⟩, hrest⟩
      cases hrest
      cases hy
      exact ⟨_, rfl, hyv⟩
    cases hbi : bi "Some" [v] with
    | none =>
      simp only [hbi] at hrun
      obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨v', hv', rfl⟩ := hC.2 [v] r hbi
      cases hv'
      have hne0 : exitResCompName 0 ≠ exitResName := exitResCompName_ne_res 0
      rcases hAx : A.lookup x with _ | t
      · simp only [resultStoreT, hAx, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hx hAx hv
        let rs1 := rsSetScalar rs (exitResCompName 0) (rs.rsScalar x)
        have hag1 : envAgreesT br A env rs1 := envAgreesT_set_reserved _ (exitReserved_resComp 0) hag
        have hret1 : rs1.rsScalar exitRetName = 0 := by
          simp only [rs1, rsScalar_rsSetScalar, if_neg (exitResCompName_ne_ret 0).symm]; exact hret
        obtain ⟨h0, hag2, hres⟩ := res_writeT rs1 1 hret1 hag1
        refine ⟨rsSetScalar rs1 exitResName 1,
          RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ rs) (RustExec.scalarSet _ _ _),
          (envAgreesExitT_val rfl).mpr ⟨h0, hag2, fun _ => Or.inr ⟨v, rfl, hres, hsv, ?_⟩⟩,
          fun _ => h0⟩
        rw [hdv]
        simp [rs1, rsScalar_rsSetScalar, hne0]
      · simp only [resultStoreT, hAx, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        obtain ⟨hvcf, val, hval', hbr⟩ := envAgreesT_tower hag hx hAx hv
        let rs1 := rsSetTower rs (exitResCompName 0) ⟨t, val⟩
        have hag1 : envAgreesT br A env rs1 :=
          envAgreesT_setTower_reserved _ (exitReserved_resComp 0) hag
        have hret1 : rs1.rsScalar exitRetName = 0 := hret
        obtain ⟨h0, hag2, hres⟩ := res_writeT rs1 1 hret1 hag1
        refine ⟨rsSetScalar rs1 exitResName 1, RustExec.seq _ _ _ _ _
            (RustExec.copy ⟨exitResCompName 0, t⟩ ⟨x, t⟩ rs rfl val
              (locatedLookup_of_rsTower rs x t val hval')) (RustExec.scalarSet _ _ _),
          (envAgreesExitT_val rfl).mpr ⟨h0, hag2, fun _ => Or.inr ⟨v, rfl, hres, val,
            (show rs1.rsTower (exitResCompName 0) = some ⟨t, val⟩ from
              CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _), hbr⟩⟩,
          fun _ => h0⟩

theorem exitSimTy_tuple (es : List ImpExpr) : ExitSimTy bi N leafSpec br A R (.tuple es) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  cases tl with
  | false => cases fl <;> simp [exitSimOkT] at hok
  | true =>
    have hh : R = .tuple ∧ exitArgsOk es = true := by
      cases fl <;> simpa [exitSimOkT] using hok
    obtain ⟨rfl, hargs⟩ := hh
    obtain ⟨vals, hA, rfl⟩ := denote'_tuple_inv bi fuel es env env' o hrun hval
    obtain ⟨rfl, hF⟩ := denoteArgs'_vars_inv bi fuel es hargs env env' (some vals) hA
    have hK' : haxToLowCTKT A true fl (.tuple es) =
        (tupleStoreT A 0 es).map fun s => (s, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    rcases hs : tupleStoreT A 0 es with _ | s
    · rw [hs] at hK; cases hK
    rw [hs] at hK
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨rs', hex, hag', hret', hcomp, -⟩ :=
      tupleStoreT_sim N leafSpec br A es vals (hF vals rfl) hargs 0 s rs hs hag
    refine ⟨rs', hex, (envAgreesExitT_val rfl).mpr ⟨hret'.trans hret, hag', fun _ =>
      ⟨vals, rfl, fun j w hw => by simpa using hcomp j w hw⟩⟩, fun _ => hret'.trans hret⟩

theorem exitSimTy_cfBreak (p : ImpExpr) : ExitSimTy bi N leafSpec br A R (.cfBreak p) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  cases fl with
  | none => cases tl <;> simp [exitSimOkT] at hok
  | some r =>
    have hp : exitPayloadOk A p = true := by cases tl <;> simpa [exitSimOkT] using hok
    rw [denote'_cfBreak_run'] at hrun
    obtain ⟨v, k, s, hpay, hsv, hk, hs, hsexec⟩ :
        ∃ v k s, (denote' bi fuel p).run env = (.val v, env) ∧ ScalarValN v ∧
          valueToScalar v = some k ∧ storeScalar exitValName p = some s ∧
          RustExec N leafSpec s rs (rsSetScalar rs exitValName k) := by
      cases p with
      | var x =>
        simp only [exitPayloadOk, Bool.and_eq_true, Bool.not_eq_true'] at hp
        have hsc : A.lookup x = none := by simpa [exitSc] using hp.2
        rw [denote'_var_run] at hrun ⊢
        cases hv : env x with
        | none =>
          rw [hv] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          obtain ⟨_, h⟩ := hval; cases h
        | some v =>
          obtain ⟨hsv, hdec⟩ := envAgreesT_scalar hag hp.1 hsc hv
          exact ⟨v, rs.rsScalar x, _, rfl, hsv, hdec, rfl, RustExec.scalarSetExpr _ _ rs⟩
      | lit l =>
        simp only [exitPayloadOk] at hp
        rcases hs : storeScalar exitValName (.lit l) with _ | s
        · have hK' : haxToLowCTKT A tl (some r) (.cfBreak (.lit l)) = none := by
            rw [haxToLowCTKT_cfBreak_eq _ _ _ _ rfl]; simp [exitStore, hs]
          rw [hK'] at hK; cases hK
        obtain ⟨k, hsv, hk, hex⟩ := storeScalar_lit hp hs
        exact ⟨_, k, s, denote'_lit_run bi fuel l env, hsv, hk, rfl, hex N leafSpec rs⟩
      | unitVal =>
        exact ⟨.unit, 0, _, denote'_unitVal_run bi fuel env, trivial, rfl, rfl,
          RustExec.scalarSet _ _ rs⟩
      | _ => simp [exitPayloadOk] at hp
    rw [hpay] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (Outcome.val (.controlFlow true v), env) = (o, env') by
      rw [← hrun]
      rcases hsv.cases with ⟨_, _, rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ | rfl <;> rfl)
    have hK' : haxToLowCTKT A tl (some r) (.cfBreak p) =
        some (.RSeq s (.RScalarSet exitRetName 1), true) := by
      rw [haxToLowCTKT_cfBreak_eq _ _ _ _ (exitScE_of_payloadOk hp)]; simp [exitStore, hs]
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    refine ⟨_, RustExec.seq _ _ _ _ _ hsexec (RustExec.scalarSet _ _ _), ?_, fun h => by cases h⟩
    refine ⟨by simp, ?_, ?_⟩
    · rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val.symm, rsScalar_rsSetScalar, if_pos rfl]
      exact hk
    · exact envAgreesT_set_reserved 1 exitReserved_ret
        (envAgreesT_set_reserved k exitReserved_val hag)

theorem exitSimTy_seq (a b : ImpExpr) (iha : ExitSimTy bi N leafSpec br A R a)
    (ihb : ExitSimTy bi N leafSpec br A R b) : ExitSimTy bi N leafSpec br A R (.seq a b) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitSimOkT A R false fl.isSome a = true ∧ exitSimOkT A R tl fl.isSome b = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true] using hok
  rw [haxToLowCTKT_seq_eq] at hK
  rcases hA : haxToLowCTKT A false fl a with _ | ⟨aC, xa⟩
  · rw [hA] at hK; cases hK
  rcases hB : haxToLowCTKT A tl fl b with _ | ⟨bC, xb'⟩
  · rw [hA, hB] at hK; cases hK
  rw [hA, hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  rcases hra : (denote' bi fuel a).run env with ⟨oa, e1⟩
  cases oa with
  | val va =>
    obtain ⟨rs1, hexA, hagA, hxA⟩ :=
      iha false fl fuel env e1 (.val va) rs aC xa hok'.1 hfl hA hra ⟨va, rfl⟩ hag hret
    cases hcf : va.isControlFlow with
    | false =>
      obtain ⟨h1, hag1, -⟩ := (envAgreesExitT_val hcf).mp hagA
      rw [denote'_seq_run_val bi fuel a b env e1 va hra hcf] at hrun
      obtain ⟨rs', hexB, hagB, hxB⟩ :=
        ihb tl fl fuel e1 env' o rs1 bC xb' hok'.2 hfl hB hrun hval hag1 h1
      refine ⟨rs', ?_, hagB, fun h => hxB (by simp at h; exact h.2)⟩
      cases xa
      · exact RustExec.seq _ _ _ _ _ hexA hexB
      · exact RustExec.seq _ _ _ _ _ hexA (exitGuard_running _ _ _ _ _ h1 hexB)
    | true =>
      cases va with
      | controlFlow k w =>
        cases k with
        | false => exact (show False from hagA).elim
        | true =>
          obtain ⟨h1, hw, hag1⟩ := hagA
          rw [denote'_seq_run_cf bi fuel a b env e1 true w hra] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          cases xa with
          | false => have h0 := hxA rfl; rw [h1] at h0; cases h0
          | true =>
            exact ⟨rs1, RustExec.seq _ _ _ _ _ hexA (exitGuard_exited _ _ _ _ h1),
              ⟨h1, hw, hag1⟩, fun h => by simp at h⟩
      | _ => simp at hcf
  | _ =>
    rw [denote'_seq_run_nonval bi fuel a b env e1 _ hra (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h

theorem exitSimTy_ifThenElse (v : String) (t e : ImpExpr)
    (iht : ExitSimTy bi N leafSpec br A R t) (ihe : ExitSimTy bi N leafSpec br A R e) :
    ExitSimTy bi N leafSpec br A R (.ifThenElse (.var v) t e) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitReserved v = false ∧ exitSc A v = true ∧
      exitSimOkT A R tl fl.isSome t = true ∧ exitSimOkT A R tl fl.isSome e = true := by
    cases tl <;> cases fl <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2, hok.2⟩)
  have hvsc : A.lookup v = none := by simpa [exitSc] using hok'.2.1
  rw [haxToLowCTKT_ifThenElse_eq _ _ _ _ _ _ hok'.2.1] at hK
  rcases hT' : haxToLowCTKT A tl fl t with _ | ⟨tC, xt⟩
  · rw [hT'] at hK; cases hK
  rcases hE : haxToLowCTKT A tl fl e with _ | ⟨eC, xe⟩
  · rw [hT', hE] at hK; cases hK
  rw [hT', hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  cases hvv : env v with
  | none =>
    rw [denote'_ifThenElse_var_run_none bi fuel v t e env hvv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  | some w =>
    obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hok'.1 hvsc hvv
    rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hwcf⟩
    · rw [denote'_ifThenElse_var_run_bool bi fuel v t e env bb hvv] at hrun
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | true =>
        simp only [if_true] at hrun hdw
        obtain ⟨rs', hex, hag', hx⟩ := iht tl fl fuel env env' o rs tC xt hok'.2.2.1 hfl hT' hrun
          hval hag hret
        exact ⟨rs', RustExec.ifTrue _ _ _ _ _ 1 hdw.symm (by decide) hex, hag',
          fun h => hx (by simp at h; exact h.1)⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at hrun hdw
        obtain ⟨rs', hex, hag', hx⟩ := ihe tl fl fuel env env' o rs eC xe hok'.2.2.2 hfl hE hrun
          hval hag hret
        exact ⟨rs', RustExec.ifFalse _ _ _ _ _ hdw.symm hex, hag',
          fun h => hx (by simp at h; exact h.2)⟩
    · rw [denote'_ifThenElse_var_run_nonbool bi fuel v t e env w hvv hnb hwcf] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h

/-- The scrutinee of a `match` `M` that runs to a value: when a call `f(args)` on argument
    variables that does not run to a value makes `M` end in the same outcome, a run of `M`
    ending in a value has the call on the values `vals` of the arguments return `vRes`,
    leaving the environment unchanged. -/
theorem optMatch_app_inv {M : ImpExpr} {f : String} {args : List ImpExpr} {fuel : Nat}
    {env env' : Env} {o : Outcome} (hargs : exitArgsOk args = true)
    (hnonval : ∀ env1 o, denote' bi fuel (.app f args) env = (o, env1) →
      (∀ v, o ≠ .val v) → denote' bi fuel M env = (o, env1))
    (hrun : denote' bi fuel M env = (o, env')) (hval : ∃ v, o = .val v) :
    ∃ vals vRes, List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals ∧
      bi f vals = some vRes ∧ denote' bi fuel (.app f args) env = (.val vRes, env) := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel args).run env with ⟨oa, e1⟩
  obtain ⟨he1, hF⟩ := denoteArgs'_vars_inv bi fuel args hargs env e1 oa hA
  subst e1
  have happ := denote'_app_run bi fuel f args env
  rw [hA] at happ
  have hbad : ∀ (m : String), denote' bi fuel (.app f args) env = (.err m, env) → False :=
    fun m h => by
      rw [hnonval env _ h (fun v hv => by cases hv)] at hrun
      obtain ⟨rfl, -⟩ := Prod.mk.inj hrun
      obtain ⟨_, h'⟩ := hval; cases h'
  rcases oa with _ | vals
  · exact (hbad _ happ).elim
  cases hbi : bi f vals with
  | none =>
    simp only [hbi] at happ
    exact (hbad _ happ).elim
  | some vRes =>
    simp only [hbi] at happ
    exact ⟨vals, vRes, hF vals rfl, hbi, happ⟩

/-- The payload binding `bindP` of `optHeadT`: from a state holding in the slot
    `exitOptPayName` an output related to the payload `w` by `optPayloadRel`, it runs to a
    state agreeing with the environment extended by `p ↦ w`, with the exit flag `0`. -/
theorem optBind_sim {env : Env} {rs2 : RustState} {p : String} {tty : TowerType}
    {bindP : LowCT} {w : Value} {payOut : RustVal tty} (hpn : exitReserved p = false)
    (hbind : (A.lookup p = none ∧ tty = .TU64 ∧
        bindP = .RScalarSetExpr p (.SLimb exitOptPayName 0)) ∨
      (A.lookup p = some tty ∧ tty ≠ .TU64 ∧ bindP = .RCopy ⟨p, tty⟩ ⟨exitOptPayName, tty⟩))
    (hwcf : w.isControlFlow = false)
    (hpay2 : rs2.rsTower exitOptPayName = some ⟨tty, payOut⟩)
    (hrel : optPayloadRel br tty w payOut) (hag2 : envAgreesT br A env rs2)
    (hret2 : rs2.rsScalar exitRetName = 0) :
    ∃ rs3, RustExec N leafSpec bindP rs2 rs3 ∧
      envAgreesT br A (env.extend p w) rs3 ∧ rs3.rsScalar exitRetName = 0 := by
  rcases hbind with ⟨hpA, rfl, rfl⟩ | ⟨hpA, htu, rfl⟩
  · simp only [optPayloadRel, if_true] at hrel
    have hev : (SExpr.SLimb exitOptPayName 0).evalState rs2 = towerLimb payOut 0 := by
      simp only [SExpr.evalState, CatCrypt.Crypto.Jasmin.LowCT.rsTowerLimb, hpay2]
    have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) p
      (.SLimb exitOptPayName 0) rs2
    rw [hev] at hset
    exact ⟨_, hset, envAgreesT_extend hpn hpA hrel.1 hrel.2 hag2, ret_setScalar hpn _ hret2⟩
  · simp only [optPayloadRel, if_neg htu] at hrel
    exact ⟨rsSetTower rs2 p ⟨tty, payOut⟩,
      RustExec.copy ⟨p, tty⟩ ⟨exitOptPayName, tty⟩ rs2 rfl payOut
        (locatedLookup_of_rsTower rs2 exitOptPayName tty payOut hpay2),
      envAgreesT_extend_tower hpn hpA hwcf hrel hag2, hret2⟩

/-- **A `match` on the `Option` returned by a call**, for either order of its two arms `M`:
    the call of `optHeadT`, then the `Some` arm with the payload bound or the `None` arm by
    the tag. -/
theorem exitSimTy_optMatch (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    (M : ImpExpr) (f : String) (args : List ImpExpr) (p : String) (t e : ImpExpr)
    (hOk : ∀ tl il, exitSimOkT A R tl il M = (!exitReserved p && exitArgsOk args &&
      (optHeadT A f args p).isSome && exitSimOkT A R tl il t && exitSimOkT A R tl il e))
    (hKM : ∀ tl fl, haxToLowCTKT A tl fl M =
      match optHeadT A f args p, haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (callC, bindP), some (tC, xt), some (eC, xe) =>
          some (.RSeq callC (.RIfNz exitOptTagS (.RSeq bindP tC) eC), xt || xe)
      | _, _, _ => none)
    (hsome : ∀ fuel env env1 w, denote' bi fuel (.app f args) env = (.val (.option (some w)), env1) →
      denote' bi fuel M env = denote' bi fuel t (env1.extend p w))
    (hnone : ∀ fuel env env1, denote' bi fuel (.app f args) env = (.val (.option none), env1) →
      denote' bi fuel M env = denote' bi fuel e env1)
    (hnonval : ∀ fuel env env1 o, denote' bi fuel (.app f args) env = (o, env1) →
      (∀ v, o ≠ .val v) → denote' bi fuel M env = (o, env1))
    (iht : ExitSimTy bi N leafSpec br A R t) (ihe : ExitSimTy bi N leafSpec br A R e) :
    ExitSimTy bi N leafSpec br A R M := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  change denote' bi fuel M env = (o, env') at hrun
  rw [hOk] at hok
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hpn, hargs⟩, -⟩, hokt⟩, hoke⟩ := hok
  rw [hKM] at hK
  rcases hk : optHeadT A f args p with _ | ⟨callC, bindP⟩
  · rw [hk] at hK; cases hK
  rcases hT' : haxToLowCTKT A tl fl t with _ | ⟨tC, xt⟩
  · rw [hk, hT'] at hK; cases hK
  rcases hE : haxToLowCTKT A tl fl e with _ | ⟨eC, xe⟩
  · rw [hk, hT', hE] at hK; cases hK
  rw [hk, hT', hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  obtain ⟨tty, ctx, ls, hsf, hfi, hfu, hfl', hfr, hDO, hm, rfl, hbind⟩ := optHeadT_some A hk
  obtain ⟨vals, vRes, hF, hbi, happ⟩ :=
    optMatch_app_inv bi hargs (hnonval fuel env) hrun hval
  obtain ⟨o', rs2, rfl, hexC, hag2, hret2, htagS, hpay⟩ :=
    optCall_sim hL hm (hL.optD f tty hDO hsf hfi hfu hfl' hfr) hargs hF hbi hag
  rw [hret] at hret2
  rcases o' with _ | w
  · rw [hnone fuel env env happ] at hrun
    obtain ⟨rs', hex, hagE, hx⟩ := ihe tl fl fuel env env' o rs2 eC xe hoke hfl hE hrun hval
      hag2 hret2
    exact ⟨rs', RustExec.seq _ _ _ _ _ hexC (RustExec.ifFalse _ _ _ _ _ (by simpa using htagS)
      hex), hagE, fun h => hx (by simp at h; exact h.2)⟩
  · rw [hsome fuel env env w happ] at hrun
    obtain ⟨hwcf, payOut, hpay2, hrel⟩ := hpay w rfl
    obtain ⟨rs3, hexB, hag3, hret3⟩ :=
      optBind_sim N leafSpec br A hpn hbind hwcf hpay2 hrel hag2 hret2
    obtain ⟨rs', hex, hagE, hx⟩ := iht tl fl fuel _ env' o rs3 tC xt hokt hfl hT' hrun hval
      hag3 hret3
    exact ⟨rs', RustExec.seq _ _ _ _ _ hexC (RustExec.ifTrue _ _ _ _ _ 1 (by simpa using htagS)
      (by decide) (RustExec.seq _ _ _ _ _ hexB hex)), hagE,
      fun h => hx (by simp at h; exact h.1)⟩

theorem exitSimTy_typeAscription (e : ImpExpr) (ty : String)
    (ih : ExitSimTy bi N leafSpec br A R e) :
    ExitSimTy bi N leafSpec br A R (.typeAscription e ty) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitSimOkT A R tl fl.isSome e = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOkT] using hok
  rw [haxToLowCTKT_typeAscription_eq] at hK
  have hrun' : (denote' bi fuel e).run env = (o, env') := by
    rw [← hrun]; simp only [StateT.run, denote']
  exact ih tl fl fuel env env' o rs c xb hok' hfl hK hrun' hval hag hret

/-- An expression outside the fragment simulates vacuously. -/
theorem exitSimTy_of_not_ok (e : ImpExpr) (h : ∀ tl il, exitSimOkT A R tl il e = false) :
    ExitSimTy bi N leafSpec br A R e := by
  intro tl fl _ _ _ _ _ _ _ hok
  rw [h] at hok; cases hok

/-! ## §14  The loops -/

/-- **The `whileFoldReturn` loop**, by induction on fuel, as `exitLoop_sim` under the
    placement `A`: the guard is a scalar name. -/
theorem exitLoopT_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hcs : A.lookup c = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      (_root_.Hax.denoteWhile'Return bi fuel (.var c) body).run env = (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      rs.rsScalar run = rs.rsScalar c →
      ∃ rs', RustExec N leafSpec (.RWhileNz run (.RSeq bC (loopTail run c))) rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hcr : c ≠ run := ne_of_reserved hc (exitReserved_of_runSlot hslot)
  have hresv := exitReserved_of_runSlot hslot
  intro fuel
  induction fuel with
  | zero =>
    intro env env' o rs h hval _ _ _
    rw [denoteWhile'Return_zero_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨_, h⟩ := hval; cases h
  | succ n IH =>
    intro env env' o rs h hval hag hret hrc
    cases hvc : env c with
    | none =>
      obtain ⟨msg, h'⟩ := denoteWhile'Return_succ_none bi n c body env hvc
      rw [h'] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hc hcs hvc
      rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hwcf⟩
      swap
      · rw [denoteWhile'Return_succ_nonbool bi n c body env w hvc hnb hwcf] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hdw
        rw [denoteWhile'Return_succ_false bi n c body env hvc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨rs, RustExec.whileFalse _ _ _ (by rw [hrc, ← hdw]),
          (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
      | true =>
        simp only [if_true] at hdw
        have hrun1 : rs.rsScalar run = 1 := by rw [hrc, ← hdw]
        rcases hb : (denote' bi (n + 1) body).run env with ⟨ob, e2⟩
        cases ob with
        | val vb =>
          obtain ⟨rs1, hex1, hag1, -⟩ :=
            ihb false (some run) (n + 1) env e2 (.val vb) rs bC xb hokB hctx hKB hb
              ⟨vb, rfl⟩ hag hret
          cases hcf : vb.isControlFlow with
          | false =>
            obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
            rw [denoteWhile'Return_succ_iterate bi n c body env e2 vb hvc hb hcf] at h
            have htail : RustExec N leafSpec (loopTail run c) rs1
                (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              RustExec.ifFalse _ _ _ _ _ h1 (RustExec.scalarSetExpr _ _ _)
            have hag2 : envAgreesT br A e2 (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              envAgreesT_set_reserved _ hresv hagE
            have hret2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar exitRetName = 0 := by
              rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
            have hrc2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar run =
                (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar c := by
              simp [rsScalar_rsSetScalar, hcr]
            obtain ⟨rs', hexL, hagL⟩ := IH e2 env' o _ h hval hag2 hret2 hrc2
            exact ⟨rs', RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
              (RustExec.seq _ _ _ _ _ hex1 htail) hexL, hagL⟩
          | true =>
            cases vb with
            | controlFlow kk ww =>
              cases kk with
              | false => exact (show False from hag1).elim
              | true =>
                obtain ⟨h1, hw, hagE⟩ := hag1
                have hwcf : ww.isControlFlow = false := by
                  cases ww <;> first | rfl | simp [valueToScalar] at hw
                rw [denoteWhile'Return_succ_exit bi n c body env e2 ww hvc hb hwcf] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                refine ⟨rsSetScalar rs1 run 0,
                  RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
                    (RustExec.seq _ _ _ _ _ hex1
                      (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSet _ _ _)))
                    (RustExec.whileFalse _ _ _ (by simp)), ?_, ?_, ?_⟩
                · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
                · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_val hslot).symm]; exact hw
                · exact envAgreesT_set_reserved _ hresv hagE
            | _ => simp at hcf
        | _ =>
          rw [denoteWhile'Return_succ_nonval bi n c body env e2 _ hvc hb
            (fun v h => by cases h)] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          obtain ⟨_, h⟩ := hval; cases h

theorem exitSimTy_whileFoldReturn (c : String) (body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.whileFoldReturn (.var c) body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : exitReserved c = false ∧ exitSc A c = true ∧
        exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have hcs : A.lookup c = none := by simpa [exitSc] using hok'.2.1
    rw [haxToLowCTKT_whileFoldReturn_eq _ _ _ _ hok'.2.1] at hK
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK; cases hK
    rw [hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_whileFoldReturn_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hresv := exitReserved_of_runSlot hslot
    have hcr : c ≠ exitRunName fl := ne_of_reserved hok'.1 hresv
    let rs0 := rsSetScalar (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0)
      (exitRunName fl) 0
    let rs1 := rsSetScalar rs0 (exitRunName fl) (rs0.rsScalar c)
    have hag1 : envAgreesT br A env rs1 :=
      envAgreesT_set_reserved _ hresv (envAgreesT_set_reserved _ hresv
        (envAgreesT_set_reserved _ exitReserved_val
          (envAgreesT_set_reserved _ exitReserved_ret hag)))
    have hret1 : rs1.rsScalar exitRetName = 0 := by
      simp [rs1, rs0, rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
    have hrc1 : rs1.rsScalar (exitRunName fl) = rs1.rsScalar c := by
      simp [rs1, rsScalar_rsSetScalar, hcr]
    obtain ⟨rs', hexL, hagL⟩ :=
      exitLoopT_sim bi N leafSpec br A R (exitRunName fl) c body bC x ihb hslot hok'.1 hcs
        hok'.2.2 hB fuel env env' o rs1 hrun hval hag1 hret1 hrc1
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) hexL))),
      hagL, fun h => by cases h⟩

/-- After an exit, the guarded trips preserve the exit agreement. -/
theorem exitedTripsT (run : String) (B : LowCT) (hslot : exitRunSlot run = true) :
    ∀ (d k : Nat) (rs : RustState) (w : Value) (env : Env),
      envAgreesExitT br A R false (.val (.controlFlow true w)) env rs →
      ∃ rs', TripsFrom N leafSpec run (exitGuard B) k d rs rs' ∧
        envAgreesExitT br A R false (.val (.controlFlow true w)) env rs' := by
  intro d
  induction d with
  | zero => intro k rs w env hag; exact ⟨rs, rfl, hag⟩
  | succ d IH =>
    intro k rs w env hag
    obtain ⟨h1, hw, hagO⟩ := hag
    have h1' : (rsSetScalar rs run k).rsScalar exitRetName = 1 := by
      rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm]; exact h1
    have hag' : envAgreesExitT br A R false (.val (.controlFlow true w)) env
        (rsSetScalar rs run k) :=
      ⟨h1', by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_val hslot).symm]; exact hw,
        envAgreesT_set_reserved _ (exitReserved_of_runSlot hslot) hagO⟩
    obtain ⟨rs', hT, hagL⟩ := IH (k + 1) (rsSetScalar rs run k) w env hag'
    exact ⟨rs', ⟨rsSetScalar rs run k, exitGuard_exited N leafSpec B _ h1', hT⟩, hagL⟩

/-- The state at the start of trip `j` of a counted loop from `lo`: the trip counter
    `run` holds `j` and the counter `i` holds `lo + j`. -/
theorem tripStart_agree {env : Env} {rs : RustState} {run i : String}
    (hresv : exitReserved run = true) (hi_ : exitReserved i = false) (his : A.lookup i = none)
    (j c : Nat) (hc : c < 2 ^ 64) (hag : envAgreesT br A env rs) :
    envAgreesT br A (env.extend i (.int (c : Int))) (rsSetScalar (rsSetScalar rs run j) i c) :=
  envAgreesT_extend hi_ his ⟨by omega, by omega⟩ (valueToScalar_int _)
    (envAgreesT_set_reserved _ hresv hag)

/-- **The `forFoldReturn` trips**, as `exitForTrips_sim` under the placement `A`. -/
theorem exitForTripsT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop'Return bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTrip run i lo bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoop'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT := tripStart_agree A (br := br) hresv hi_ his j (lo + j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTrip run i lo bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) (.SLit lo)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoop'Return_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop'Return bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'Return_succ_exit bi n i _ hi body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'Return_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

/-- The `forFoldReturn` loop with a variable upper bound, as `exitForLoopRt_sim`. -/
theorem exitForLoopRtT_sim (run i h : String) (lo : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hh_ : exitReserved h = false)
    (hhs : A.lookup h = none) (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.var h) body)).run env =
      (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (exitForLoopRt run i lo h bC) rs rs' ∧
      envAgreesExitT br A R false o env' rs' := by
  obtain ⟨v, H, hhv, hvs, hH, hrun⟩ :=
    denote'_forFoldReturn_var_scalarN bi fuel i h lo body env env' o hrun hval
      (fun v hv => (envAgreesT_scalar hag hh_ hhs hv).1)
  have hdec : H = rs.rsScalar h := by
    have hd := (envAgreesT_scalar hag hh_ hhs hhv).2
    rw [hvs] at hd
    exact Option.some.inj hd
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hH0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar h = H := by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hh_ exitReserved_val), rsScalar_rsSetScalar,
      if_neg (ne_of_reserved hh_ exitReserved_ret), hdec]
  have hrun0 : (_root_.Hax.denoteForLoop'Return bi fuel i ((lo + 0 : Nat) : Int) H body).run env =
      (o, env') := by
    rw [Nat.add_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    exitForTripsT_sim bi N leafSpec br A R run i lo H body bC xb ihb hslot hi_ his (by omega)
      hokB hKB (H - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (H - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  refine ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
    (RustExec.forRuntime _ _ _ _ _ ?_)), hagL⟩
  simpa only [SExpr.evalState, hH0] using hFor

theorem exitSimTy_forFoldReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFoldReturn i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) = true ∧
        exitReserved i = false ∧ exitSc A i = true ∧ exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
    have hslot := runSlot_exitRunName hfl
    rw [haxToLowCTKT_forFoldReturn_eq _ _ _ _ _ _
      (by simp only [hok'.2.2.1, exitScRt_of_ok hok'.1, Bool.and_self])] at hK
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
        rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
    rw [hB] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
      · rw [hFB, hRt] at hK; cases hK
      rw [hFB, hRt] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      have hh : exitReserved h = false ∧ exitSc A h = true := by
        have h1 := hok'.1
        simp only [hFB, forBoundsRtOkT, hRt, Option.isSome_none, Bool.false_or,
          Bool.and_eq_true, Bool.not_eq_true'] at h1
        exact h1
      have hhs : A.lookup h = none := by simpa [exitSc] using hh.2
      obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
      obtain ⟨rs', hex, hagL⟩ :=
        exitForLoopRtT_sim bi N leafSpec br A R (exitRunName fl) i h l body bC x ihb hslot
          hok'.2.1 his hh.1 hhs hok'.2.2.2 hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun h => by cases h⟩
    rw [hFB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rw [denote'_forFoldReturn_lit_run] at hrun
    have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
      envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
    have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
        exitRetName = 0 := by
      rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
    have hrun0 : (_root_.Hax.denoteForLoop'Return bi fuel i ((l + 0 : Nat) : Int) h body).run env =
        (o, env') := by
      rw [Nat.add_zero]; exact hrun
    obtain ⟨rs', hT, hagL⟩ :=
      exitForTripsT_sim bi N leafSpec br A R (exitRunName fl) i l h body bC x ihb hslot
        hok'.2.1 his hh hok'.2.2.2 hB (h - l) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
    have hFor := rustExec_rFor_of_tripsFrom N leafSpec (exitRunName fl) _ (h - l) 0 _ _ rs'
      (RustExec.forZero _ _ _) hT
    rw [Nat.zero_add] at hFor
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor), hagL,
      fun h => by cases h⟩

/-- **The `forFoldRevReturn` trips**, as `exitForTripsRev_sim` under the placement `A`. -/
theorem exitForTripsRevT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoopRev'Return bi fuel i lo ((hi - j : Nat) : Int) body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripRev run i hi bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoopRev'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExitT_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : (lo : Int) < ((hi - j : Nat) : Int) := by omega
    have hc : ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoopRev'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT : envAgreesT br A (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
          (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) := by
        rw [hc]
        exact tripStart_agree br A hresv hi_ his j (hi - 1 - j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) r →
          RustExec N leafSpec (exitForTripRev run i hi bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SSub (.SLit (hi - 1)) (.SVar run)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoopRev'Return_succ_iterate bi n i lo _ body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoopRev'Return bi n i lo ((hi - (j + 1) : Nat) : Int)
              body).run e2 = (o, env') := by
            rw [show ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 by omega]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoopRev'Return_succ_exit bi n i lo _ body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoopRev'Return_succ_nonval bi n i lo _ body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem exitSimTy_forFoldRevReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFoldRevReturn i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
        exitSc A i = true ∧ exitSimOkT A R false true body = true := by
      cases fl <;> simpa only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        using hok
    have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
    rw [haxToLowCTKT_forFoldRevReturn_eq _ _ _ _ _ _ hok'.2.2.1] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rw [hFB] at hok'; cases hok'.1
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rcases hB : haxToLowCTKT A false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hFB, hB] at hK; cases hK
    rw [hFB, hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_forFoldRevReturn_lit_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
      envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
    have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
        exitRetName = 0 := by
      rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
    have hrun0 : (_root_.Hax.denoteForLoopRev'Return bi fuel i l ((h - 0 : Nat) : Int) body).run
        env = (o, env') := by
      rw [Nat.sub_zero]; exact hrun
    obtain ⟨rs', hT, hagL⟩ :=
      exitForTripsRevT_sim bi N leafSpec br A R (exitRunName fl) i l h body bC x ihb hslot
        hok'.2.1 his hh hok'.2.2.2 hB (h - l) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
    have hFor := rustExec_rFor_of_tripsFrom N leafSpec (exitRunName fl) _ (h - l) 0 _ _ rs'
      (RustExec.forZero _ _ _) hT
    rw [Nat.zero_add] at hFor
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor), hagL,
      fun h => by cases h⟩

/-- **The `forFold` trips of a loop that may break**, as `breakForTrips_sim` under the
    placement `A`. -/
theorem breakForTripsT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop' bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTrip run i lo bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoop'_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, envAgreesExitT_reset hag rfl⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT := tripStart_agree br A hresv hi_ his j (lo + j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTrip run i lo bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) (.SLit lo)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoop'_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop' bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'_succ_break bi n i _ hi body env e2 ww hlt hb] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, envAgreesExitT_reset hagL.2.2 hwcf⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem breakForLoopT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoop run i lo hi bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  rw [denote'_forFold_lit_run] at hrun
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i ((lo + 0 : Nat) : Int) hi body).run env =
      (o, env') := by
    rw [Nat.add_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsT_sim bi N leafSpec br A R run i lo hi body bC xb ihb hslot hi_ his hhi hokB hKB
      (hi - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (hi - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  exact ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor))
    (RustExec.scalarSet _ _ _), hagL, by simp [rsScalar_rsSetScalar]⟩

theorem breakForLoopRtT_sim (run i h : String) (lo : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hh_ : exitReserved h = false)
    (hhs : A.lookup h = none) (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.var h) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoopRt run i lo h bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  obtain ⟨v, H, hhv, hvs, hH, hrun⟩ :=
    denote'_forFold_var_scalarN bi fuel i h lo body env env' o hrun hval
      (fun v hv => (envAgreesT_scalar hag hh_ hhs hv).1)
  have hdec : H = rs.rsScalar h := by
    have hd := (envAgreesT_scalar hag hh_ hhs hhv).2
    rw [hvs] at hd
    exact Option.some.inj hd
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hH0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar h = H := by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hh_ exitReserved_val), rsScalar_rsSetScalar,
      if_neg (ne_of_reserved hh_ exitReserved_ret), hdec]
  have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i ((lo + 0 : Nat) : Int) H body).run env =
      (o, env') := by
    rw [Nat.add_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsT_sim bi N leafSpec br A R run i lo H body bC xb ihb hslot hi_ his (by omega)
      hokB hKB (H - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (H - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  refine ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
    (RustExec.forRuntime _ _ _ _ _ ?_))) (RustExec.scalarSet _ _ _), hagL,
    by simp [rsScalar_rsSetScalar]⟩
  simpa only [SExpr.evalState, hH0] using hFor

/-- **The `whileFold` trips of a loop that may break**, as `breakWhileTrips_sim` under the
    placement `A`. -/
theorem breakWhileTripsT_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hcs : A.lookup c = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      (_root_.Hax.denoteWhile' bi fuel (.var c) body).run env = (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      rs.rsScalar run = rs.rsScalar c →
      ∃ rs', RustExec N leafSpec (.RWhileNz run (.RSeq bC (loopTail run c))) rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hcr : c ≠ run := ne_of_reserved hc (exitReserved_of_runSlot hslot)
  have hresv := exitReserved_of_runSlot hslot
  intro fuel
  induction fuel with
  | zero =>
    intro env env' o rs h hval _ _ _
    rw [denoteWhile'_zero_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨_, h⟩ := hval; cases h
  | succ n IH =>
    intro env env' o rs h hval hag hret hrc
    cases hvc : env c with
    | none =>
      obtain ⟨msg, h'⟩ := denoteWhile'_succ_none bi n c body env hvc
      rw [h'] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := envAgreesT_scalar hag hc hcs hvc
      rcases hsw.bool_or with ⟨bb, rfl⟩ | ⟨hnb, hwcf⟩
      swap
      · rw [denoteWhile'_succ_nonbool bi n c body env w hvc hnb hwcf] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hdw
        rw [denoteWhile'_succ_false bi n c body env hvc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨rs, RustExec.whileFalse _ _ _ (by rw [hrc, ← hdw]), envAgreesExitT_reset hag rfl⟩
      | true =>
        simp only [if_true] at hdw
        have hrun1 : rs.rsScalar run = 1 := by rw [hrc, ← hdw]
        rcases hb : (denote' bi (n + 1) body).run env with ⟨ob, e2⟩
        cases ob with
        | val vb =>
          obtain ⟨rs1, hex1, hag1, -⟩ :=
            ihb false (some run) (n + 1) env e2 (.val vb) rs bC xb hokB hctx hKB hb
              ⟨vb, rfl⟩ hag hret
          cases hcf : vb.isControlFlow with
          | false =>
            obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
            rw [denoteWhile'_succ_iterate bi n c body env e2 vb hvc hb hcf] at h
            have htail : RustExec N leafSpec (loopTail run c) rs1
                (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              RustExec.ifFalse _ _ _ _ _ h1 (RustExec.scalarSetExpr _ _ _)
            have hag2 : envAgreesT br A e2 (rsSetScalar rs1 run (rs1.rsScalar c)) :=
              envAgreesT_set_reserved _ hresv hagE
            have hret2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar exitRetName = 0 := by
              rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
            have hrc2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar run =
                (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar c := by
              simp [rsScalar_rsSetScalar, hcr]
            obtain ⟨rs', hexL, hagL⟩ := IH e2 env' o _ h hval hag2 hret2 hrc2
            exact ⟨rs', RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
              (RustExec.seq _ _ _ _ _ hex1 htail) hexL, hagL⟩
          | true =>
            cases vb with
            | controlFlow kk ww =>
              cases kk with
              | false => exact (show False from hag1).elim
              | true =>
                obtain ⟨h1, hw, hagE⟩ := hag1
                have hwcf : ww.isControlFlow = false := by
                  cases ww <;> first | rfl | simp [valueToScalar] at hw
                rw [denoteWhile'_succ_break bi n c body env e2 ww hvc hb] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                exact ⟨rsSetScalar rs1 run 0,
                  RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
                    (RustExec.seq _ _ _ _ _ hex1
                      (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSet _ _ _)))
                    (RustExec.whileFalse _ _ _ (by simp)),
                  envAgreesExitT_reset (envAgreesT_set_reserved _ hresv hagE) hwcf⟩
            | _ => simp at hcf
        | _ =>
          rw [denoteWhile'_succ_nonval bi n c body env e2 _ hvc hb
            (fun v h => by cases h)] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          obtain ⟨_, h⟩ := hval; cases h

theorem breakWhileLoopT_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hcs : A.lookup c = none)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.whileFold (.var c) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitLoop run c bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  rw [denote'_whileFold_run] at hrun
  have hresv := exitReserved_of_runSlot hslot
  have hcr : c ≠ run := ne_of_reserved hc hresv
  let rs0 := rsSetScalar (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) run 0
  let rs1 := rsSetScalar rs0 run (rs0.rsScalar c)
  have hag1 : envAgreesT br A env rs1 :=
    envAgreesT_set_reserved _ hresv (envAgreesT_set_reserved _ hresv
      (envAgreesT_set_reserved _ exitReserved_val
        (envAgreesT_set_reserved _ exitReserved_ret hag)))
  have hret1 : rs1.rsScalar exitRetName = 0 := by
    simp [rs1, rs0, rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
  have hrc1 : rs1.rsScalar run = rs1.rsScalar c := by
    simp [rs1, rsScalar_rsSetScalar, hcr]
  obtain ⟨rs', hexL, hagL⟩ :=
    breakWhileTripsT_sim bi N leafSpec br A R run c body bC xb ihb hslot hc hcs hokB hKB
      fuel env env' o rs1 hrun hval hag1 hret1 hrc1
  exact ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) hexL))))
    (RustExec.scalarSet _ _ _), hagL, by simp [rsScalar_rsSetScalar]⟩

theorem exitSimTy_forFold (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFold i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) = true ∧
          exitReserved i = false ∧ exitSc A i = true ∧
          exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
      have hokB := hok'.2.2.2
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTKT_forFold_some_eq _ _ _ _ _ _
        (by simp only [hok'.2.2.1, exitScRt_of_ok hok'.1, Bool.and_self])] at hK
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK
        rcases hFB : forBounds lo hi with _ | ⟨l, h⟩ <;>
          rcases hRt : forBoundsRt lo hi with _ | ⟨l', h'⟩ <;> rw [hFB, hRt] at hK <;> cases hK
      rw [hB] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rcases hRt : forBoundsRt lo hi with _ | ⟨l, h⟩
        · rw [hFB, hRt] at hK; cases hK
        rw [hFB, hRt] at hK
        simp only [Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        have hh : exitReserved h = false ∧ exitSc A h = true := by
          have h1 := hok'.1
          simp only [hFB, forBoundsRtOkT, hRt, Option.isSome_none, Bool.false_or,
            Bool.and_eq_true, Bool.not_eq_true'] at h1
          exact h1
        have hhs : A.lookup h = none := by simpa [exitSc] using hh.2
        obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
        obtain ⟨rs', hex, hagL, h0⟩ :=
          breakForLoopRtT_sim bi N leafSpec br A R (exitRunName (some r)) i h l body bC x ihb
            hslot hok'.2.1 his hh.1 hhs hokB hB fuel env env' o rs hrun hval hag
        exact ⟨rs', hex, hagL, fun _ => h0⟩
      rw [hFB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      obtain ⟨rs', hex, hagL, h0⟩ :=
        breakForLoopT_sim bi N leafSpec br A R (exitRunName (some r)) i l h body bC x ihb hslot
          hok'.2.1 his hh hokB hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun _ => h0⟩

/-- **The `forFoldRev` trips of a loop that may break**: as `breakForTripsT_sim`, with the
    counter of trip `j` bound to `hi - 1 - j` (`exitForTripRev`). -/
theorem breakForTripsRevT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoopRev' bi fuel i lo ((hi - j : Nat) : Int) body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripRev run i hi bC) j d rs rs' ∧
        envAgreesExitT br A R false o env' (rsSetScalar rs' exitRetName 0) := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoopRev'_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, envAgreesExitT_reset hag rfl⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : (lo : Int) < ((hi - j : Nat) : Int) := by omega
    have hc : ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoopRev'_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT : envAgreesT br A (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
          (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) := by
        rw [hc]
        exact tripStart_agree br A hresv hi_ his j (hi - 1 - j) (by omega) hag
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) r →
          RustExec N leafSpec (exitForTripRev run i hi bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SSub (.SLit (hi - 1)) (.SVar run)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExitT_val hcf).mp hag1
          rw [denoteForLoopRev'_succ_iterate bi n i lo _ body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoopRev' bi n i lo ((hi - (j + 1) : Nat) : Int)
              body).run e2 = (o, env') := by
            rw [show ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 by omega]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoopRev'_succ_break bi n i lo _ body env e2 ww hlt hb] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTripsT N leafSpec br A R run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, envAgreesExitT_reset hagL.2.2 hwcf⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoopRev'_succ_nonval bi n i lo _ body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem breakForLoopRevT_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSimTy bi N leafSpec br A R body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (his : A.lookup i = none) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOkT A R false true body = true)
    (hKB : haxToLowCTKT A false (some run) body = some (bC, xb))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (o, env'))
    (hval : ∃ v, o = .val v) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (breakLoop (exitForLoopRev run i lo hi bC)) rs rs' ∧
      envAgreesExitT br A R false o env' rs' ∧ rs'.rsScalar exitRetName = 0 := by
  rw [denote'_forFoldRev_lit_run] at hrun
  have hag0 : envAgreesT br A env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
    envAgreesT_set_reserved _ exitReserved_val (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
      exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
  have hrun0 : (_root_.Hax.denoteForLoopRev' bi fuel i lo ((hi - 0 : Nat) : Int) body).run env =
      (o, env') := by
    rw [Nat.sub_zero]; exact hrun
  obtain ⟨rs', hT, hagL⟩ :=
    breakForTripsRevT_sim bi N leafSpec br A R run i lo hi body bC xb ihb hslot hi_ his hhi hokB
      hKB (hi - lo) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
  have hFor := rustExec_rFor_of_tripsFrom N leafSpec run _ (hi - lo) 0 _ _ rs'
    (RustExec.forZero _ _ _) hT
  rw [Nat.zero_add] at hFor
  exact ⟨_, RustExec.seq _ _ _ _ _ (RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor))
    (RustExec.scalarSet _ _ _), hagL, by simp [rsScalar_rsSetScalar]⟩

theorem exitSimTy_forFoldRev (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.forFoldRev i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
          exitSc A i = true ∧ exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have his : A.lookup i = none := by simpa [exitSc] using hok'.2.2.1
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTKT_forFoldRev_some_eq _ _ _ _ _ _ hok'.2.2.1] at hK
      rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
      · rw [hFB] at hok'; cases hok'.1
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hFB, hB] at hK; cases hK
      rw [hFB, hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
      obtain ⟨rs', hex, hagL, h0⟩ :=
        breakForLoopRevT_sim bi N leafSpec br A R (exitRunName (some r)) i l h body bC x ihb
          hslot hok'.2.1 his hh hok'.2.2.2 hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun _ => h0⟩

theorem exitSimTy_whileFold (c : String) (body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body) :
    ExitSimTy bi N leafSpec br A R (.whileFold (.var c) body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOkT] at hok
  | false =>
    cases fl with
    | none => simp [exitSimOkT] at hok
    | some r =>
      have hok' : exitReserved c = false ∧ exitSc A c = true ∧
          exitSimOkT A R false true body = true := by
        simpa only [exitSimOkT, Option.isSome_some, Bool.and_eq_true, Bool.not_eq_true',
          and_assoc] using hok
      have hcs : A.lookup c = none := by simpa [exitSc] using hok'.2.1
      have hslot := runSlot_exitRunName hfl
      rw [haxToLowCTKT_whileFold_some_eq _ _ _ _ hok'.2.1] at hK
      rcases hB : haxToLowCTKT A false (some (exitRunName (some r))) body with _ | ⟨bC, x⟩
      · rw [hB] at hK; cases hK
      rw [hB] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨rs', hex, hagL, h0⟩ :=
        breakWhileLoopT_sim bi N leafSpec br A R (exitRunName (some r)) c body bC x ihb hslot
          hok'.1 hcs hok'.2.2 hB fuel env env' o rs hrun hval hag
      exact ⟨rs', hex, hagL, fun _ => h0⟩

end Arms

/-! ## §15  The simulation theorems -/

/-- **Simulation of the typed exit-flag lowering.**  Under the leaf conditions
    `ExitLeaves` at the call result types declared by `A` (`exitCallTys A`), every expression
    of the fragment `exitSimOkT A R` simulates under the placement `A`: the lowered command
    `haxToLowCTKT A` matches every `denote'` run that ends in a value. -/
theorem haxToLowCTKT_simulates (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) (e : ImpExpr) :
    ExitSimTy bi N leafSpec br A R e := by
  have nok : ∀ e : ImpExpr, (∀ tl il, exitSimOkT A R tl il e = false) →
      ExitSimTy bi N leafSpec br A R e :=
    exitSimTy_of_not_ok bi N leafSpec br A R
  induction e using ImpExpr.ind with
  | lit l => exact exitSimTy_lit bi N leafSpec br A R l
  | var x => exact exitSimTy_var bi N leafSpec br A R x
  | unitVal => exact exitSimTy_unitVal bi N leafSpec br A R
  | letBind n val body _ ihb =>
    cases val with
    | lit l =>
      exact exitSimTy_letBind_of_head bi N leafSpec br A R n _ body ihb
        (head_lit bi N leafSpec br A R hL.marshal n l body)
    | var s =>
      exact exitSimTy_letBind_of_head bi N leafSpec br A R n _ body ihb
        (head_var bi N leafSpec br A R n s body)
    | app f args =>
      exact exitSimTy_letBind_of_head bi N leafSpec br A R n _ body ihb
        (head_app R hL n f args body)
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | seq a b iha ihb => exact exitSimTy_seq bi N leafSpec br A R a b iha ihb
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v => exact exitSimTy_ifThenElse bi N leafSpec br A R v t e iht ihe
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | typeAscription e ty ih => exact exitSimTy_typeAscription bi N leafSpec br A R e ty ih
  | whileFoldReturn c body _ ihb =>
    cases c with
    | var v => exact exitSimTy_whileFoldReturn bi N leafSpec br A R v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | forFoldReturn i lo hi body _ _ ihb =>
    exact exitSimTy_forFoldReturn bi N leafSpec br A R i lo hi body ihb
  | forFoldRevReturn i lo hi body _ _ ihb =>
    exact exitSimTy_forFoldRevReturn bi N leafSpec br A R i lo hi body ihb
  | forFold i lo hi body _ _ ihb => exact exitSimTy_forFold bi N leafSpec br A R i lo hi body ihb
  | forFoldRev i lo hi body _ _ ihb =>
    exact exitSimTy_forFoldRev bi N leafSpec br A R i lo hi body ihb
  | whileFold c body _ ihb =>
    cases c with
    | var v => exact exitSimTy_whileFold bi N leafSpec br A R v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | cfBreak p _ => exact exitSimTy_cfBreak bi N leafSpec br A R p
  | tuple es _ => exact exitSimTy_tuple bi N leafSpec br A R es
  | app f args _ => exact exitSimTy_app bi N leafSpec br A R hL.optCtors f args
  | match_ s arms _ iha =>
    by_cases hsh : exitMatchShape s arms = true
    · rcases exitMatchShape_cases hsh with ⟨f, args, p, t, e, rfl, rfl⟩ | ⟨f, args, p, t, e, rfl, rfl⟩
      · exact exitSimTy_optMatch bi N leafSpec br A R hL _ f args p t e
          (fun tl il => by cases tl <;> cases il <;> rfl)
          (fun tl fl => by cases tl <;> cases fl <;> rfl)
          (fun fuel _ _ _ h => denote'_optMatch_some bi fuel h)
          (fun fuel _ _ h => denote'_optMatch_none bi fuel h)
          (fun fuel _ _ _ h ho => denote'_match_nonval bi fuel h ho)
          (iha (.somePat (.varPat p), t) (by simp)) (iha (.nonePat, e) (by simp))
      · exact exitSimTy_optMatch bi N leafSpec br A R hL _ f args p t e
          (fun tl il => by cases tl <;> cases il <;> rfl)
          (fun tl fl => by cases tl <;> cases fl <;> rfl)
          (fun fuel _ _ _ h => denote'_optMatchR_some bi fuel h)
          (fun fuel _ _ h => denote'_optMatchR_none bi fuel h)
          (fun fuel _ _ _ h ho => denote'_match_nonval bi fuel h ho)
          (iha (.somePat (.varPat p), t) (by simp)) (iha (.nonePat, e) (by simp))
    · exact nok _ (fun tl il => by
        cases h : exitSimOkT A R tl il (.match_ s arms)
        · rfl
        · exact absurd (exitMatchShape_of_ok A R h) hsh)
  | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)

/-- The value a function returns under the result placement `R`: the payload of an early
    exit decoded in the scalar result slot or in agreement with the result slots of `R`,
    or the final value in agreement with the result slots of `R` (`resultAgreesT`). -/
def outcomeAgreesT (br : ValueTowerBridge) (R : ExitRes) : Outcome → RustState → Prop
  | .val (.controlFlow true v), rs =>
      valueToScalar v = some (rs.rsScalar exitResName) ∨ resultAgreesT br R v rs
  | .val v, rs => resultAgreesT br R v rs
  | _, _ => False

/-- With a scalar result placement, the result agreement is the decoding of the returned
    or final value in the scalar result slot. -/
theorem outcomeAgreesT_none (br : ValueTowerBridge) (o : Outcome) (rs : RustState) :
    outcomeAgreesT br .scalar o rs ↔ outcomeScalar o = some (rs.rsScalar exitResName) := by
  rcases o with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w =>
      cases k
      · exact Iff.rfl
      · exact or_self_iff
    | _ => exact Iff.rfl
  all_goals simp [outcomeAgreesT, outcomeScalar]

/-- **The function frame under a placement.**  For a function body of the fragment in the
    function context, the frame `exitFunction` around its typed lowering matches every
    `denote'` run that ends in a value, with the result of `outcomeAgreesT`. -/
theorem exitFunctionT_sim (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes) (e : ImpExpr)
    (hT : ExitSimTy bi N leafSpec br A R e) (c0 : LowCT) (x : Bool)
    (hok : exitSimOkT A R true true e = true)
    (hK0 : haxToLowCTKT A true (some exitFnSlot) e = some (c0, x))
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec (exitFunction c0) rs rs' ∧ outcomeAgreesT br R o rs' := by
  have hag0 : envAgreesT br A env
      (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0) :=
    envAgreesT_set_reserved _ exitReserved_res (envAgreesT_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0).rsScalar
      exitRetName = 0 := by
    simp [rsScalar_rsSetScalar]
  obtain ⟨rs1, hex, hagE, -⟩ :=
    hT true (some exitFnSlot) fuel env env' o _ c0 x hok
      (fun r h => Or.inr (Option.some.inj h).symm) hK0 hrun hval hag0 hret0
  obtain ⟨v, rfl⟩ := hval
  cases hcf : v.isControlFlow with
  | false =>
    obtain ⟨h1, -, htail⟩ := (envAgreesExitT_val hcf).mp hagE
    refine ⟨rs1, RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.seq _ _ _ _ _ hex (RustExec.ifFalse _ _ _ _ _ h1 (RustExec.skip _)))), ?_⟩
    have ht := htail rfl
    cases v with
    | controlFlow k w => simp at hcf
    | _ => exact ht
  | true =>
    cases v with
    | controlFlow k w =>
      cases k with
      | false => exact (show False from hagE).elim
      | true =>
        obtain ⟨h1, hw, -⟩ := hagE
        refine ⟨rsSetScalar rs1 exitResName (rs1.rsScalar exitValName),
          RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
            (RustExec.seq _ _ _ _ _ hex
              (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSetExpr _ _ _)))), ?_⟩
        simp only [outcomeAgreesT, rsScalar_rsSetScalar, if_true]
        exact Or.inl hw
    | _ => simp at hcf

/-- **Function-level simulation of the typed lowering.**  For a function body in the
    fragment `exitSimOkT A R` with exits allowed at function level, leaf conditions
    `ExitLeaves` at the call result types declared by `A`, and an entry state agreeing with
    the entry environment under the placement `A`, a `denote'` run ending in a value is
    matched by the lowered function `haxToLowCTFnT A e`, whose result slot agrees with the
    returned or final value (`outcomeAgreesT`). -/
theorem haxToLowCTFnT_simulates_exit (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT A R true true e = true) (hK : haxToLowCTFnT A e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeAgreesT br R o rs' := by
  unfold haxToLowCTFnT at hK
  rcases hK0 : haxToLowCTKT A true (some exitFnSlot) e with _ | ⟨c0, x⟩
  · rw [hK0] at hK; cases hK
  rw [hK0] at hK
  simp only [Option.map_some, Option.some.injEq] at hK
  subst hK
  exact exitFunctionT_sim bi N leafSpec br A R e (haxToLowCTKT_simulates bi N leafSpec br A R hL e)
    c0 x hok hK0 fuel env env' o rs hrun hval hag

/-- **Function-level simulation with a scalar result.**  `haxToLowCTFnT_simulates_exit` at
    the scalar result placement: the result slot of the lowered function holds the decoding
    of the returned or final value. -/
theorem haxToLowCTFnT_simulates_exit_scalar (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT A .scalar true true e = true) (hK : haxToLowCTFnT A e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) := by
  obtain ⟨rs', hex, ho⟩ :=
    haxToLowCTFnT_simulates_exit bi N leafSpec br A .scalar hL e c hok hK fuel env env' o rs hrun
      hval hag
  exact ⟨rs', hex, (outcomeAgreesT_none br o rs').mp ho⟩

/-- **The statement of `haxToLowCTFn_simulates_exit` for the typed lowering** at the empty
    placement: from an entry state agreeing with the entry environment off the reserved
    names (`envAgreesOff`), the result slot of `haxToLowCTFnT [] e` holds the decoding of
    the returned or final value. -/
theorem haxToLowCTFnT_nil_simulates_exit (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (hL : ExitLeaves bi leafSpec br) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT [] .scalar true true e = true) (hK : haxToLowCTFnT [] e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) :=
  haxToLowCTFnT_simulates_exit_scalar bi N leafSpec br []
    (hL.mono (fun _ _ h => by simp [exitCallTys] at h) (fun _ _ h => by simp [exitOptTys] at h)
      (fun _ _ _ => rfl) (fun _ _ h => by simp [exitCalleeTys] at h) (fun _ _ => rfl))
      e c hok hK fuel env env' o rs hrun
    hval (envAgreesT_nil_of_off hag)

/-- Under the empty placement the result placement is scalar or a tuple. -/
theorem exitResultPlace_nil (e : ImpExpr) :
    exitResultPlace [] e = .scalar ∨ exitResultPlace [] e = .tuple ∨
      exitResultPlace [] e = .option none := by
  have hj : ∀ r s : ExitRes, (r = .scalar ∨ r = .tuple ∨ r = .option none) →
      (s = .scalar ∨ s = .tuple ∨ s = .option none) →
      (ExitRes.optJoin r s = .scalar ∨ ExitRes.optJoin r s = .tuple ∨
        ExitRes.optJoin r s = .option none) := by
    rintro r s (rfl | rfl | rfl) (rfl | rfl | rfl) <;> simp [ExitRes.optJoin]
  induction e using ImpExpr.ind with
  | ifThenElse c t e _ iht ihe => exact hj _ _ iht ihe
  | match_ s arms _ iha =>
    match arms, iha with
    | [(pa, a), (pb, b)], iha =>
      exact hj _ _ (iha (pa, a) (by simp)) (iha (pb, b) (by simp))
    | [], _ => simp [exitResultPlace]
    | [_], _ => simp [exitResultPlace]
    | _ :: _ :: _ :: _, _ => simp [exitResultPlace]
  | app f args _ =>
    unfold exitResultPlace
    split <;> simp_all
  | _ => simp_all [exitResultPlace, ExitRes.ofPlace]

/-! ## §16  The scalar operations of hax-lean's `u64` table

`ScalarOpsSoundT Hax.hax64Builtins`: on the `u64` table every operation of
`scalarOpExprT` either computes its template or is undefined.  The width-tagged calls of
`widthOpTable` compute their masked templates (`WidthOp.eval_sexpr`); `Add` and `add`
compute the sum and are undefined when it reaches `2^64`, `Sub` and `sub` the difference and
are undefined when the subtrahend exceeds the minuend, so no refusing table is needed; the
comparisons return a Boolean, whose decoding `1` or `0` is their template. -/

section Hax64Ops

open _root_.Hax (hax64Builtins hax64WordOps widthArrayOps u64BinOp u64BinOp_natCast rotrNat
  rotlNat)

/-- The natural-number value of the width-tagged operation `o` at width `w`: the arms of
    `Hax.hax64WordOps` and `Hax.hax64NarrowOps`, with the shifts total. -/
def WidthOp.nat (w : Nat) : WidthOp → Nat → Nat → Nat
  | .add, a, b => (a + b) % 2 ^ w
  | .sub, a, b => (a % 2 ^ w + 2 ^ w - b % 2 ^ w) % 2 ^ w
  | .mul, a, b => (a * b) % 2 ^ w
  | .and, a, b => (a % 2 ^ w) &&& (b % 2 ^ w)
  | .or, a, b => (a % 2 ^ w) ||| (b % 2 ^ w)
  | .xor, a, b => (a % 2 ^ w) ^^^ (b % 2 ^ w)
  | .shl, a, b => ((a % 2 ^ w) <<< b) % 2 ^ w
  | .shr, a, b => (a % 2 ^ w) >>> b
  | .rotr, a, b => rotrNat w a b
  | .rotl, a, b => rotlNat w a b

theorem xor_xor_and_eq_or (a b : Nat) : (a ^^^ b) ^^^ (a &&& b) = a ||| b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> rfl

/-- At a width that is a power of two, the masked template of a width-tagged operation
    evaluates to `WidthOp.nat`. -/
theorem WidthOp.eval_sexpr (k : Nat) (o : WidthOp) (a b : Nat) (σ : String → Nat) :
    (o.sexpr (2 ^ k) (.SLit a) (.SLit b)).eval σ = o.nat (2 ^ k) a b := by
  cases o <;> simp only [WidthOp.sexpr, WidthOp.nat, widthMask, orExprN, widthAmt, SExpr.eval,
    Nat.and_two_pow_sub_one_eq_mod, xor_xor_and_eq_or, rotrNat, rotlNat]

theorem WidthOp.nat_lt {w : Nat} (hw : w ≤ 64) (o : WidthOp) (a b : Nat) :
    o.nat w a b < 2 ^ 64 := by
  have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hmod : ∀ x, x % 2 ^ w < 2 ^ w := fun x => Nat.mod_lt _ (by positivity)
  suffices o.nat w a b < 2 ^ w by omega
  cases o <;> simp only [WidthOp.nat, rotrNat, rotlNat]
  all_goals first
    | exact hmod _
    | exact Nat.and_lt_two_pow _ (hmod _)
    | exact Nat.or_lt_two_pow (hmod _) (hmod _)
    | exact Nat.xor_lt_two_pow (hmod _) (hmod _)
    | exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (hmod _)

/-- An operation of `scalarOpExprT` is one of its sixteen named operations, one of the four
    Boolean connectives, or a name of `widthOpOf`. -/
theorem scalarOpExprT_isSome_cases {op : String} {a b : SExpr}
    (h : (scalarOpExprT op a b).isSome = true) :
    op ∈ ["lt", "Lt", "gt", "Gt", "le", "Le", "ge", "Ge", "eq", "Eq", "ne", "Ne", "add", "Add",
      "sub", "Sub"] ∨ op ∈ ["&&", "and", "||", "or"] ∨ ∃ p, widthOpOf op = some p := by
  unfold scalarOpExprT at h
  split at h
  all_goals first | (left; simp; done) | (right; left; simp; done) | skip
  right; right
  rcases hw : widthOpOf op with _ | p
  · simp [hw] at h
  · exact ⟨p, rfl⟩

/-- `scalarOpNatT` of a width-tagged name is `WidthOp.nat` at a width of `8`, `16`, `32` or
    `64`. -/
theorem scalarOpNatT_width {f : String} {w : Nat} {o : WidthOp}
    (h : ∀ a b, scalarOpExprT f a b = some (o.sexpr w a b))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (n m : Nat) :
    scalarOpNatT f n m = o.nat w n m := by
  unfold scalarOpNatT
  rw [h]
  rcases hw with rfl | rfl | rfl | rfl
  · exact WidthOp.eval_sexpr 3 o n m _
  · exact WidthOp.eval_sexpr 4 o n m _
  · exact WidthOp.eval_sexpr 5 o n m _
  · exact WidthOp.eval_sexpr 6 o n m _

/-- A two-operand arm `u64BinOp n m g` of `hax64WordOps` whose name `widthArrayOps` does not
    define: a value of `hax64Builtins` is a value of `g`. -/
theorem hax64Builtins_arm {f : String} {g : Nat → Nat → Option Nat} {n m : Nat} {r : Value}
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (harm : hax64WordOps f [.int n, .int m] = u64BinOp n m g)
    (hA : widthArrayOps f [.int n, .int m] = none)
    (h : hax64Builtins f [.int n, .int m] = some r) : ∃ v, g n m = some v ∧ r = .int v := by
  unfold hax64Builtins at h
  rw [harm, u64BinOp_natCast hn hm, hA] at h
  cases hg : g n m with
  | none => rw [hg] at h; cases h
  | some v => rw [hg] at h; cases h; exact ⟨v, rfl, rfl⟩

/-- The arm of `Hax.hax64WordOps` or `Hax.hax64NarrowOps` of the width-tagged operation `o`
    at width `w`: `WidthOp.nat`, the shifts undefined for an amount of `w` or more. -/
def WidthOp.hax (w : Nat) (o : WidthOp) (a b : Nat) : Option Nat :=
  match o with
  | .shl | .shr => if b < w then some (o.nat w a b) else none
  | _ => some (o.nat w a b)

/-- A width-tagged call whose arm in `hax64WordOps` is `WidthOp.hax`: its values on two words
    below `2^64` are the words `WidthOp.nat`, below `2^64`. -/
theorem hax64Builtins_widthOp {f : String} {w : Nat} {o : WidthOp} (hw : w ≤ 64)
    (harm : ∀ a b : Int, hax64WordOps f [.int a, .int b] = u64BinOp a b (o.hax w))
    (hA : ∀ a b : Int, widthArrayOps f [.int a, .int b] = none) {n m : Nat} {r : Value}
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (h : hax64Builtins f [.int n, .int m] = some r) :
    r = .int (o.nat w n m) ∧ o.nat w n m < 2 ^ 64 := by
  obtain ⟨v, hg, rfl⟩ := hax64Builtins_arm hn hm (harm n m) (hA n m) h
  refine ⟨?_, WidthOp.nat_lt hw o n m⟩
  cases o <;> simp only [WidthOp.hax] at hg
  all_goals first
    | (split_ifs at hg; cases hg; rfl)
    | (cases hg; rfl)

/-- The scalar operation `f` on two integer words: when every value of `hax64Builtins f` on
    two words below `2^64` is the word `F n m` below `2^64`, and `scalarOpNatT f` is `F`, the
    condition of `ScalarOpsSoundT` holds at `f` on integer operands. -/
theorem hax64_scalarOp_int {f : String} {F : Nat → Nat → Nat}
    {a b : Int} {na nb : Nat} {r : Value} (hbi : hax64Builtins f [.int a, .int b] = some r)
    (ha0 : 0 ≤ a) (ha : a < 2 ^ 64) (hb0 : 0 ≤ b) (hb : b < 2 ^ 64)
    (hna : valueToScalar (.int a) = some na) (hnb : valueToScalar (.int b) = some nb)
    (hexpr : ∀ n m, scalarOpNatT f n m = F n m)
    (hsem : ∀ (n m : Nat) r, n < 2 ^ 64 → m < 2 ^ 64 →
      hax64Builtins f [.int n, .int m] = some r →
      r = .int (F n m) ∧ F n m < 2 ^ 64) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT f na nb) := by
  simp only [valueToScalar, ha0, hb0, if_true, Option.some.injEq] at hna hnb
  obtain rfl : a = (na : Int) := by omega
  obtain rfl : b = (nb : Int) := by omega
  obtain ⟨rfl, hlt⟩ := hsem na nb r (by omega) (by omega) hbi
  refine ⟨⟨Int.natCast_nonneg _, by exact_mod_cast hlt⟩, ?_⟩
  simp [valueToScalar, hexpr]

/-- `hax64_scalarOp_int` at a width-tagged call whose template is `WidthOp.sexpr w o` and
    whose arm in `hax64WordOps` is `WidthOp.hax w o`. -/
theorem hax64_width_int {f : String} {w : Nat} {o : WidthOp}
    {a b : Int} {na nb : Nat} {r : Value} (hbi : hax64Builtins f [.int a, .int b] = some r)
    (ha0 : 0 ≤ a) (ha : a < 2 ^ 64) (hb0 : 0 ≤ b) (hb : b < 2 ^ 64)
    (hna : valueToScalar (.int a) = some na) (hnb : valueToScalar (.int b) = some nb)
    (hexpr : ∀ a b, scalarOpExprT f a b = some (o.sexpr w a b))
    (harm : ∀ a b : Int, hax64WordOps f [.int a, .int b] = u64BinOp a b (o.hax w))
    (hA : ∀ a b : Int, widthArrayOps f [.int a, .int b] = none)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT f na nb) :=
  hax64_scalarOp_int hbi ha0 ha hb0 hb hna hnb (scalarOpNatT_width hexpr hw)
    (fun _ _ _ hn hm h => hax64Builtins_widthOp (by omega) harm hA hn hm h)

/-- A call of `hax64Builtins` whose value is the Boolean `c`: its result is a scalar value
    decoding to `1` when `c` holds and to `0` otherwise. -/
theorem hax64_bool_result {f : String} {args : List Value} {c : Bool} {r : Value} {n : Nat}
    (hc : hax64Builtins f args = some (.bool c)) (hbi : hax64Builtins f args = some r)
    (hn : n = if c then 1 else 0) : ScalarValN r ∧ valueToScalar r = some n := by
  rw [hc] at hbi
  cases hbi
  subst hn
  cases c <;> exact ⟨trivial, rfl⟩

/-- The checked addition `F n m = n + m` (`Add`, `add`) or subtraction `F n m = n - m`
    (`Sub`, `sub`) of `hax64Builtins`: a value on two words below `2^64` is the word
    `F n m` below `2^64`. -/
theorem hax64Builtins_checked {f : String} {F : Nat → Nat → Nat} {P : Nat → Nat → Prop}
    [∀ n m, Decidable (P n m)]
    (harm : ∀ a b : Int, hax64WordOps f [.int a, .int b] =
      u64BinOp a b fun x y => if P x y then some (F x y) else none)
    (hA : ∀ a b : Int, widthArrayOps f [.int a, .int b] = none)
    (hlt : ∀ n m, n < 2 ^ 64 → m < 2 ^ 64 → P n m → F n m < 2 ^ 64)
    (n m : Nat) (r : Value) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (h : hax64Builtins f [.int n, .int m] = some r) :
    r = .int (F n m) ∧ F n m < 2 ^ 64 := by
  obtain ⟨v, hg, rfl⟩ := hax64Builtins_arm hn hm (harm n m) (hA n m) h
  split_ifs at hg with hP
  cases hg
  exact ⟨rfl, hlt n m hn hm hP⟩

/-- A comparison `f` whose value in `hax64Builtins` on two integers is the Boolean `c a b`
    and whose template value on two naturals is `1` or `0` as `c` holds: the condition of
    `ScalarOpsSoundT` at `f` on two integer words. -/
theorem hax64_cmp_int {f : String} {c : Int → Int → Bool}
    (hc : ∀ a b : Int, hax64Builtins f [.int a, .int b] = some (.bool (c a b)))
    (hexpr : ∀ n m : Nat, scalarOpNatT f n m = if c n m then 1 else 0)
    {a b : Int} {na nb : Nat} {r : Value} (hbi : hax64Builtins f [.int a, .int b] = some r)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hna : valueToScalar (.int a) = some na) (hnb : valueToScalar (.int b) = some nb) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT f na nb) := by
  simp only [valueToScalar, ha0, hb0, if_true, Option.some.injEq] at hna hnb
  obtain rfl : a = (na : Int) := by omega
  obtain rfl : b = (nb : Int) := by omega
  exact hax64_bool_result (hc _ _) hbi (hexpr na nb)

/-- The sixteen named operations of `scalarOpExprT` in `hax64Builtins`: the condition of
    `ScalarOpsSoundT`.  The comparisons are defined on two integers (and `eq`, `Eq`, `ne`,
    `Ne` on two Booleans), `add`, `Add`, `sub`, `Sub` on two integer words. -/
theorem hax64_named_sound {op : String} {va vb r : Value} {na nb : Nat}
    (hl : op ∈ ["lt", "Lt", "gt", "Gt", "le", "Le", "ge", "Ge", "eq", "Eq", "ne", "Ne", "add",
      "Add", "sub", "Sub"])
    (hva : ScalarValN va) (hvb : ScalarValN vb)
    (hna : valueToScalar va = some na) (hnb : valueToScalar vb = some nb)
    (hbi : hax64Builtins op [va, vb] = some r) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT op na nb) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals
    rcases ScalarValN.cases hva with ⟨wa, a, rfl, ha⟩ | ⟨ba, rfl⟩ | ⟨a, rfl, ha0, ha⟩ | rfl <;>
    rcases ScalarValN.cases hvb with ⟨wb, b, rfl, hb⟩ | ⟨bb, rfl⟩ | ⟨b, rfl, hb0, hb⟩ | rfl
  all_goals try exact absurd hbi (by rw [show hax64Builtins _ [_, _] = none from rfl]; exact nofun)
  all_goals first
    | (cases ba <;> cases bb <;> obtain rfl := Option.some.inj hna <;>
        obtain rfl := Option.some.inj hnb <;> exact hax64_bool_result rfl hbi rfl)
    | skip
  -- `lt`, `Lt`
  iterate 2
    refine hax64_cmp_int (c := fun a b => decide (a < b)) (fun _ _ => rfl)
      (fun n m => ?_) hbi ha0 hb0 hna hnb
    change (if n < m then 1 else 0) = _
    simp only [decide_eq_true_eq, Nat.cast_lt]
  -- `gt`, `Gt`
  iterate 2
    refine hax64_cmp_int (c := fun a b => decide (b < a)) (fun _ _ => rfl)
      (fun n m => ?_) hbi ha0 hb0 hna hnb
    change (if m < n then 1 else 0) = _
    simp only [decide_eq_true_eq, Nat.cast_lt]
  -- `le`, `Le`
  iterate 2
    refine hax64_cmp_int (c := fun a b => decide (a ≤ b)) (fun _ _ => rfl)
      (fun n m => ?_) hbi ha0 hb0 hna hnb
    change 1 - (if m < n then 1 else 0) = _
    simp only [decide_eq_true_eq, Nat.cast_le]
    split_ifs <;> omega
  -- `ge`, `Ge`
  iterate 2
    refine hax64_cmp_int (c := fun a b => decide (b ≤ a)) (fun _ _ => rfl)
      (fun n m => ?_) hbi ha0 hb0 hna hnb
    change 1 - (if n < m then 1 else 0) = _
    simp only [decide_eq_true_eq, Nat.cast_le]
    split_ifs <;> omega
  -- `eq`, `Eq`
  iterate 2
    refine hax64_cmp_int (c := fun a b => a == b) (fun _ _ => rfl)
      (fun n m => ?_) hbi ha0 hb0 hna hnb
    change 1 - (if n < m then 1 else 0) - (if m < n then 1 else 0) = _
    simp only [beq_iff_eq, Nat.cast_inj]
    split_ifs <;> omega
  -- `ne`, `Ne`
  iterate 2
    refine hax64_cmp_int (c := fun a b => a != b) (fun _ _ => rfl)
      (fun n m => ?_) hbi ha0 hb0 hna hnb
    change (if n < m then 1 else 0) + (if m < n then 1 else 0) = _
    simp only [bne_iff_ne, ne_eq, Nat.cast_inj]
    split_ifs <;> omega
  -- `add`
  · exact hax64_scalarOp_int (F := fun n m => n + m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => x + y < 2 ^ 64)
        (fun a b => _root_.Hax.hax64WordOps_add_lower a b) (fun _ _ => rfl)
        (fun _ _ _ _ h => h))
  -- `Add`
  · exact hax64_scalarOp_int (F := fun n m => n + m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => x + y < 2 ^ 64)
        (fun a b => _root_.Hax.hax64WordOps_add a b) (fun _ _ => rfl)
        (fun _ _ _ _ h => h))
  -- `sub`
  · exact hax64_scalarOp_int (F := fun n m => n - m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => y ≤ x)
        (fun a b => _root_.Hax.hax64WordOps_sub a b) (fun _ _ => rfl)
        (fun _ _ hn _ _ => by omega))
  -- `Sub`
  · exact hax64_scalarOp_int (F := fun n m => n - m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => y ≤ x)
        (fun a b => _root_.Hax.hax64WordOps_Sub a b) (fun _ _ => rfl)
        (fun _ _ hn _ _ => by omega))

/-- The width-tagged operations of `widthOpOf` in `hax64Builtins`: the condition of
    `ScalarOpsSoundT`. -/
theorem hax64_width_sound {op : String} {p : Nat × WidthOp} {va vb r : Value} {na nb : Nat}
    (hp : widthOpOf op = some p) (hva : ScalarValN va) (hvb : ScalarValN vb)
    (hna : valueToScalar va = some na) (hnb : valueToScalar vb = some nb)
    (hbi : hax64Builtins op [va, vb] = some r) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT op na nb) := by
  unfold widthOpOf at hp
  split at hp
  all_goals cases hp
  all_goals
    obtain ⟨a, rfl, ha0, ha⟩ : ∃ a : Int, va = .int a ∧ 0 ≤ a ∧ a < 2 ^ 64 := by
      rcases ScalarValN.cases hva with ⟨wa, a, rfl, ha⟩ | ⟨ba, rfl⟩ | h | rfl
      all_goals first
        | exact h
        | exact absurd hbi (by rw [show hax64Builtins _ [_, _] = none from rfl]; exact nofun)
    obtain ⟨b, rfl, hb0, hb⟩ : ∃ b : Int, vb = .int b ∧ 0 ≤ b ∧ b < 2 ^ 64 := by
      rcases ScalarValN.cases hvb with ⟨wb, b, rfl, hb⟩ | ⟨bb, rfl⟩ | h | rfl
      all_goals first
        | exact h
        | exact absurd hbi (by rw [show hax64Builtins _ [_, _] = none from rfl]; exact nofun)
    exact hax64_width_int hbi ha0 ha hb0 hb hna hnb (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (by decide)

/-- The Boolean connectives `&&`, `and`, `||`, `or` in `hax64Builtins`: the condition of
    `ScalarOpsSoundT`.  The table defines them on two Booleans, as the Boolean conjunction
    and disjunction, whose decodings are the template values `SAnd` and `orExprN` on `0`
    and `1`; on any other pair of scalar values the table is undefined. -/
theorem hax64_conn_sound {op : String} {va vb r : Value} {na nb : Nat}
    (hl : op ∈ ["&&", "and", "||", "or"]) (hva : ScalarValN va) (hvb : ScalarValN vb)
    (hna : valueToScalar va = some na) (hnb : valueToScalar vb = some nb)
    (hbi : hax64Builtins op [va, vb] = some r) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT op na nb) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals
    rcases ScalarValN.cases hva with ⟨wa, a, rfl, ha⟩ | ⟨ba, rfl⟩ | ⟨a, rfl, ha0, ha⟩ | rfl <;>
    rcases ScalarValN.cases hvb with ⟨wb, b, rfl, hb⟩ | ⟨bb, rfl⟩ | ⟨b, rfl, hb0, hb⟩ | rfl
  all_goals try exact absurd hbi (by rw [show hax64Builtins _ [_, _] = none from rfl]; exact nofun)
  all_goals
    cases ba <;> cases bb <;> obtain rfl := Option.some.inj hna <;>
      obtain rfl := Option.some.inj hnb <;> exact hax64_bool_result rfl hbi (by decide)

/-- **hax-lean's `u64` table computes the scalar operations.**  Every operation of
    `scalarOpExprT` on two scalar words returns, in `Hax.hax64Builtins`, a scalar value whose
    decoding is `scalarOpNatT`: the fifty width-tagged calls of `widthOpTable` (`Shl#w` and
    `Shr#w` undefined for an amount of `w` or more); `Add` and `add` (undefined when the sum
    reaches `2^64`); `Sub` and `sub` (undefined when the subtrahend exceeds the minuend); the
    twelve comparisons on two integer words and `Eq`, `eq`, `Ne`, `ne` on two Booleans, each
    a Boolean decoding to `1` or `0`; the connectives `&&`, `and`, `||`, `or` on two
    Booleans, a Boolean decoding to `1` or `0`. -/
theorem scalarOpsSoundT_hax64Builtins : ScalarOpsSoundT hax64Builtins := by
  intro op va vb r na nb hop hva hvb hna hnb hbi
  rcases scalarOpExprT_isSome_cases hop with hl | hl | ⟨p, hp⟩
  · exact hax64_named_sound hl hva hvb hna hnb hbi
  · exact hax64_conn_sound hl hva hvb hna hnb hbi
  · exact hax64_width_sound hp hva hvb hna hnb hbi

/-- `ScalarOpsSoundT` holds on the range-refusing table of a table satisfying it. -/
theorem scalarOpsSoundT_exitRange {bi : Builtins} (h : ScalarOpsSoundT bi) :
    ScalarOpsSoundT (exitRange bi) :=
  fun op va vb r na nb hop hva hvb hna hnb hbi =>
    h op va vb r na nb hop hva hvb hna hnb (exitRange_some hbi).1

end Hax64Ops

/-! ## Calls of lowered callees

A call `g(args)` of a function whose body is lowered to the program `cg` is read in the
source through `calleeTable` and in the target through `calleeSpec`: the source value is the
value the callee's reading returns from its parameters bound to the argument values
(`calleeRun`), and the leaf output is read from the result slot of the run of `cg` from the
state `calleeEntry` built from the argument slots. `leafCallAgreesArgsTys_callee` is the leaf
condition of `g` on argument slots of the callee's parameter slot types (`calleeArgTys`),
from a function-level simulation of the callee. -/

section Callees

/-- The table `bi` in which the call `g` is the partial function `run`. -/
def calleeTable (bi : Builtins) (g : String) (run : List Value → Option Value) : Builtins :=
  fun f vals => if f = g then run vals else bi f vals

theorem calleeTable_self (bi : Builtins) (g : String) (run : List Value → Option Value)
    (vals : List Value) : calleeTable bi g run g vals = run vals := by
  simp [calleeTable]

theorem calleeTable_of_ne (bi : Builtins) {g f : String} (run : List Value → Option Value)
    (h : f ≠ g) (vals : List Value) : calleeTable bi g run f vals = bi f vals := by
  simp [calleeTable, h]

/-- The leaf semantics `leafSpec` in which the call `g` runs the program `cg` from the state
    `entry args` and returns `out dt r` of the state `r` it reaches, and keeps the
    destination when `cg` has no run; the other calls and the other oracles are those of
    `leafSpec`. -/
noncomputable def calleeSpec (leafSpec : LeafSpec) (N : Nat) (g : String) (cg : LowCT)
    (entry : List (Σ t : TowerType, RustVal t) → RustState)
    (out : (dt : TowerType) → RustState → RustVal dt) : LeafSpec :=
  { leafSpec with
    call := fun f dt ds old args =>
      if f = g then
        open Classical in
        if h : ∃ r, RustExec N leafSpec cg (entry args) r then out dt h.choose else old
      else leafSpec.call f dt ds old args }

theorem calleeSpec_call_of_ne (leafSpec : LeafSpec) (N : Nat) {g f : String} (cg : LowCT)
    (entry : List (Σ t : TowerType, RustVal t) → RustState)
    (out : (dt : TowerType) → RustState → RustVal dt) (h : f ≠ g) :
    (calleeSpec leafSpec N g cg entry out).call f = leafSpec.call f := by
  funext dt ds old args
  simp [calleeSpec, h]

/-- The leaf output of `g` is read from the state of a run of `cg`, when `cg` runs
    deterministically. -/
theorem calleeSpec_call_self (leafSpec : LeafSpec) (N : Nat) (g : String) (cg : LowCT)
    (entry : List (Σ t : TowerType, RustVal t) → RustState)
    (out : (dt : TowerType) → RustState → RustVal dt)
    (hdet : ∀ rs r₁ r₂, RustExec N leafSpec cg rs r₁ → RustExec N leafSpec cg rs r₂ → r₁ = r₂)
    {args : List (Σ t : TowerType, RustVal t)} {r : RustState}
    (hr : RustExec N leafSpec cg (entry args) r) (dt : TowerType) (ds : List TowerType)
    (old : RustVal dt) :
    (calleeSpec leafSpec N g cg entry out).call g dt ds old args = out dt r := by
  have hex : ∃ r, RustExec N leafSpec cg (entry args) r := ⟨r, hr⟩
  simp only [calleeSpec, if_true, dif_pos hex]
  rw [hdet _ _ _ hex.choose_spec hr]

/-- The environment `ρ` with the parameters `ps` bound to the values `vals`, in order. -/
def bindParams (ρ : Env) : List String → List Value → Env
  | p :: ps, v :: vs => bindParams (ρ.extend p v) ps vs
  | _, _ => ρ

/-- The entry state of a callee with parameters `ps` placed by `A`, over the state `rs0`,
    from the argument slots `args`: a parameter placed in the scalar heap holds limb `0` of
    its slot, a parameter placed in a tower holds its slot. -/
def calleeEntry (A : ExitTowers) (rs0 : RustState) :
    List String → List (Σ t : TowerType, RustVal t) → RustState
  | p :: ps, a :: as =>
      calleeEntry A (match A.lookup p with
        | none => rsSetScalar rs0 p (towerLimb a.2 0)
        | some _ => rsSetTower rs0 p a) ps as
  | _, _ => rs0

/-- The argument slot types of a callee with parameters `ps` placed by `A`: the placement of
    a parameter held in a tower, the word type `TU64` for a scalar parameter. -/
def calleeArgTys (A : ExitTowers) (ps : List String) : List TowerType :=
  ps.map fun p => (A.lookup p).getD .TU64

/-- The value of a callee with parameters `ps` placed by `A` and result placement `R` on the
    argument values `vals`, for the reading `read` of its body from `ρ` with the parameters
    bound: the final value of a run ending in a value without a control-flow tag, a scalar
    word for a scalar result, when the argument values are as many as the parameters, carry
    no control-flow tag, and are scalar words at the scalar parameters. -/
def calleeRun (A : ExitTowers) (R : ExitRes) (ps : List String) (read : Env → Outcome)
    (ρ : Env) (vals : List Value) : Option Value :=
  if vals.length = ps.length ∧
      ((ps.zip vals).all fun pv => (A.lookup pv.1).isSome || scalarValNB pv.2) = true ∧
      (vals.all fun v => !v.isControlFlow) = true then
    match read (bindParams ρ ps vals) with
    | .val v =>
        if v.isControlFlow = false ∧ (R = .scalar → scalarValNB v = true) then some v else none
    | _ => none
  else none

/-- The leaf output of a callee with result placement `R` at the destination type `dt`: the
    tower result slot when it holds a value of type `dt`, and for a scalar result the limb
    store of the scalar result slot. -/
def calleeOut (leafSpec : LeafSpec) (R : ExitRes) (dt : TowerType) (r : RustState) :
    RustVal dt :=
  match R with
  | .tower _ =>
      match r.rsTower exitResName with
      | some ⟨t, x⟩ => if h : t = dt then h ▸ x else default
      | none => default
  | _ => leafSpec.limbStore ⟨exitResName, dt⟩ default 0 (BitVec.ofNat 64 (r.rsScalar exitResName))

variable {br : ValueTowerBridge} {A : ExitTowers}

/-- The entry state of a callee agrees with the environment binding its parameters to the
    argument values, when the argument slots have the parameter slot types, a scalar word
    related at `TU64` decodes to limb `0`, and the values bound to scalar parameters are
    scalar words. -/
theorem calleeEntry_agrees
    (hscal : ∀ (v : Value) (x : RustVal .TU64), br .TU64 v x → ScalarValN v →
      valueToScalar v = some (towerLimb x 0)) :
    ∀ (ps : List String) (vals : List Value) (args : List (Σ t : TowerType, RustVal t))
      (ρ : Env) (rs0 : RustState),
      envAgreesT br A ρ rs0 → (∀ p ∈ ps, exitReserved p = false) →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals args →
      args.map (·.1) = calleeArgTys A ps →
      List.Forall₂ (fun p v => (A.lookup p = none → ScalarValN v) ∧ v.isControlFlow = false)
        ps vals →
      envAgreesT br A (bindParams ρ ps vals) (calleeEntry A rs0 ps args) := by
  intro ps
  induction ps with
  | nil =>
    intro vals args ρ rs0 hag _ _ _ hpv
    cases hpv
    exact hag
  | cons p ps ih =>
    intro vals args ρ rs0 hag hres hF hty hpv
    rcases hpv with _ | ⟨⟨hsv, hcf⟩, hpv⟩
    rename_i v vs
    rcases hF with _ | ⟨hbr, hF⟩
    rename_i a as
    simp only [calleeArgTys, List.map_cons, List.cons.injEq] at hty
    obtain ⟨hty1, hty⟩ := hty
    have hp : exitReserved p = false := hres p (by simp)
    have hres' : ∀ q ∈ ps, exitReserved q = false := fun q hq => hres q (by simp [hq])
    obtain ⟨t, x⟩ := a
    dsimp only at hty1 hbr
    simp only [bindParams, calleeEntry]
    rcases hA : A.lookup p with _ | tp
    · rw [hA, Option.getD_none] at hty1
      subst hty1
      have hs := hsv hA
      exact ih vs as _ _ (envAgreesT_extend hp hA hs (hscal v x hbr hs) hag) hres' hF hty hpv
    · rw [hA, Option.getD_some] at hty1
      subst hty1
      exact ih vs as _ _ (envAgreesT_extend_tower hp hA hcf hbr hag) hres' hF hty hpv

/-- **The leaf condition of a lowered callee.**  For a callee with parameters `ps` placed by
    `A` and result placement `R`, scalar or a tower at `dt`, whose lowered program `cg` runs
    deterministically and simulates its reading `read` from every state agreeing with the
    environment (`hF`), the call `g` of `calleeTable bi g (calleeRun A R ps read ρ)` agrees
    with the leaf `calleeSpec` running `cg` from `calleeEntry A rs0`, on argument slots of the
    parameter slot types. -/
theorem leafCallAgreesArgsTys_callee {bi : Builtins} {leafSpec : LeafSpec} {N : Nat}
    {g : String} {cg : LowCT} {R : ExitRes} {ps : List String} {read : Env → Outcome}
    {ρ : Env} {rs0 : RustState} {dt : TowerType}
    (hmar : ExitMarshal br leafSpec)
    (hscal : ∀ (v : Value) (x : RustVal .TU64), br .TU64 v x → ScalarValN v →
      valueToScalar v = some (towerLimb x 0))
    (hdet : ∀ rs r₁ r₂, RustExec N leafSpec cg rs r₁ → RustExec N leafSpec cg rs r₂ → r₁ = r₂)
    (hF : ∀ env rs, envAgreesT br A env rs → (∃ v, read env = .val v) →
      ∃ r, RustExec N leafSpec cg rs r ∧ outcomeAgreesT br R (read env) r)
    (hρ : envAgreesT br A ρ rs0) (hres : ∀ p ∈ ps, exitReserved p = false)
    (hR : (R = .scalar ∧ 8 ≤ dt.storageBytes) ∨ R = .tower dt) :
    LeafCallAgreesArgsTys (calleeTable bi g (calleeRun A R ps read ρ))
      (calleeSpec leafSpec N g cg (calleeEntry A rs0 ps) (calleeOut leafSpec R)) g dt br
      (calleeArgTys A ps) := by
  intro args vals argList oldV vRes hty hbi hFa
  rw [calleeTable_self] at hbi
  unfold calleeRun at hbi
  split_ifs at hbi with hg
  obtain ⟨hlen, hsc, hncf⟩ := hg
  rcases hrd : read (bindParams ρ ps vals) with v | _ | _ | _ | _ <;> rw [hrd] at hbi <;>
    try cases hbi
  simp only at hbi
  split_ifs at hbi with hv
  cases hbi
  obtain ⟨hvcf, hvs⟩ := hv
  have hpv : List.Forall₂ (fun p v => (A.lookup p = none → ScalarValN v) ∧
      v.isControlFlow = false) ps vals := by
    rw [List.forall₂_iff_get]
    refine ⟨hlen.symm, fun i h1 h2 => ⟨fun hA => ?_, ?_⟩⟩
    · have hz : (ps[i], vals[i]) ∈ ps.zip vals := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by simp [h1, h2], by simp⟩
      have := List.all_eq_true.mp hsc _ hz
      simp only [List.get_eq_getElem] at hA ⊢
      simp only [hA, Option.isSome_none, Bool.false_or] at this
      exact (scalarValNB_iff _).mp this
    · have := List.all_eq_true.mp hncf _ (List.getElem_mem h2)
      simpa using this
  have hag := calleeEntry_agrees hscal ps vals argList ρ rs0 hρ hres hFa hty hpv
  obtain ⟨r, hr, hout⟩ := hF _ _ hag ⟨vRes, hrd⟩
  rw [calleeSpec_call_self leafSpec N g cg _ _ hdet hr]
  rw [hrd] at hout
  have hout' : resultAgreesT br R vRes r := by
    cases vRes with
    | controlFlow k w => simp at hvcf
    | _ => exact hout
  rcases hR with ⟨rfl, h8⟩ | rfl
  · have hk : valueToScalar vRes = some (r.rsScalar exitResName) := hout'
    exact hmar ⟨exitResName, dt⟩ vRes _ h8 ((scalarValNB_iff _).mp (hvs rfl)) hk
  · obtain ⟨val, hval, hbr⟩ := hout'
    simp only [calleeOut, hval]
    exact hbr

/-- A value of a callee: as many argument values as parameters, those of the scalar
    parameters scalar words, none a control-flow value, and the reading from the
    parameters bound ending in that value. -/
theorem calleeRun_inv {R : ExitRes} {ps : List String} {read : Env → Outcome} {ρ : Env}
    {vals : List Value} {v : Value} (h : calleeRun A R ps read ρ vals = some v) :
    List.Forall₂ (fun p v => (A.lookup p = none → ScalarValN v) ∧ v.isControlFlow = false)
      ps vals ∧ read (bindParams ρ ps vals) = .val v := by
  unfold calleeRun at h
  split_ifs at h with hg
  obtain ⟨hlen, hsc, hncf⟩ := hg
  rcases hrd : read (bindParams ρ ps vals) with w | _ | _ | _ | _ <;> rw [hrd] at h <;>
    try cases h
  simp only at h
  split_ifs at h with hw
  cases h
  refine ⟨?_, rfl⟩
  rw [List.forall₂_iff_get]
  refine ⟨hlen.symm, fun i h1 h2 => ⟨fun hA => ?_, ?_⟩⟩
  · have hz : (ps[i], vals[i]) ∈ ps.zip vals := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [h1, h2], by simp⟩
    have := List.all_eq_true.mp hsc _ hz
    simp only [List.get_eq_getElem] at hA ⊢
    simp only [hA, Option.isSome_none, Bool.false_or] at this
    exact (scalarValNB_iff _).mp this
  · have := List.all_eq_true.mp hncf _ (List.getElem_mem h2)
    simpa using this

/-- A value of a callee with a scalar result is a scalar word. -/
theorem calleeRun_scalar {R : ExitRes} {ps : List String} {read : Env → Outcome} {ρ : Env}
    {vals : List Value} {v : Value} (hR : R = .scalar) (h : calleeRun A R ps read ρ vals = some v) :
    ScalarValN v := by
  unfold calleeRun at h
  split_ifs at h with hg
  rcases hrd : read (bindParams ρ ps vals) with w | _ | _ | _ | _ <;> rw [hrd] at h <;>
    try cases h
  simp only at h
  split_ifs at h with hw
  cases h
  exact (scalarValNB_iff _).mp (hw.2 hR)

/-- **The scalar leaf condition of a lowered callee with a scalar result**: the call `g`
    returns a scalar word whose decoding is limb `0` of the leaf output at `TU64`. -/
theorem leafCallScalarTys_callee {bi : Builtins} {leafSpec : LeafSpec} {N : Nat}
    {g : String} {cg : LowCT} {ps : List String} {read : Env → Outcome}
    {ρ : Env} {rs0 : RustState}
    (hmar : ExitMarshal br leafSpec)
    (hscal : ∀ (v : Value) (x : RustVal .TU64), br .TU64 v x → ScalarValN v →
      valueToScalar v = some (towerLimb x 0))
    (hdet : ∀ rs r₁ r₂, RustExec N leafSpec cg rs r₁ → RustExec N leafSpec cg rs r₂ → r₁ = r₂)
    (hF : ∀ env rs, envAgreesT br A env rs → (∃ v, read env = .val v) →
      ∃ r, RustExec N leafSpec cg rs r ∧ outcomeAgreesT br .scalar (read env) r)
    (hρ : envAgreesT br A ρ rs0) (hres : ∀ p ∈ ps, exitReserved p = false) :
    LeafCallScalarTys (calleeTable bi g (calleeRun A .scalar ps read ρ))
      (calleeSpec leafSpec N g cg (calleeEntry A rs0 ps) (calleeOut leafSpec .scalar)) g .TU64 br
      (calleeArgTys A ps) := by
  intro args vals argList oldV vRes hty hbi hFa
  have hbr := leafCallAgreesArgsTys_callee (bi := bi) (dt := .TU64) hmar hscal hdet hF hρ hres
    (Or.inl ⟨rfl, by decide⟩) args vals argList oldV vRes hty hbi hFa
  rw [calleeTable_self] at hbi
  have hsv : ScalarValN vRes := calleeRun_scalar rfl hbi
  exact ⟨hsv, hscal _ _ hbr hsv⟩

section Transfer

variable {bi : Builtins} {leafSpec : LeafSpec} {N : Nat} {g : String} {cg : LowCT}
  {entry : List (Σ t : TowerType, RustVal t) → RustState}
  {out : (dt : TowerType) → RustState → RustVal dt} {run : List Value → Option Value}

theorem leafCallAgreesArgs_callee_ne {f : String} {dt : TowerType} (hf : f ≠ g)
    (h : LeafCallAgreesArgs bi leafSpec f dt br) :
    LeafCallAgreesArgs (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out) f dt br := by
  intro args vals argList oldV vRes hbi hF
  rw [calleeTable_of_ne bi run hf] at hbi
  rw [calleeSpec_call_of_ne leafSpec N cg entry out hf]
  exact h args vals argList oldV vRes hbi hF

theorem leafCallScalar_callee_ne {f : String} {dt : TowerType} (hf : f ≠ g)
    (h : LeafCallScalar bi leafSpec f dt br) :
    LeafCallScalar (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out) f dt br := by
  intro args vals argList oldV vRes hbi hF
  rw [calleeTable_of_ne bi run hf] at hbi
  rw [calleeSpec_call_of_ne leafSpec N cg entry out hf]
  exact h args vals argList oldV vRes hbi hF

theorem leafCallAgreesArgsTys_callee_ne {f : String} {dt : TowerType} {ts : List TowerType}
    (hf : f ≠ g) (h : LeafCallAgreesArgsTys bi leafSpec f dt br ts) :
    LeafCallAgreesArgsTys (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out) f dt br
      ts := by
  intro args vals argList oldV vRes hty hbi hF
  rw [calleeTable_of_ne bi run hf] at hbi
  rw [calleeSpec_call_of_ne leafSpec N cg entry out hf]
  exact h args vals argList oldV vRes hty hbi hF

theorem leafCallScalarTys_callee_ne {f : String} {dt : TowerType} {ts : List TowerType}
    (hf : f ≠ g) (h : LeafCallScalarTys bi leafSpec f dt br ts) :
    LeafCallScalarTys (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out) f dt br ts := by
  intro args vals argList oldV vRes hty hbi hF
  rw [calleeTable_of_ne bi run hf] at hbi
  rw [calleeSpec_call_of_ne leafSpec N cg entry out hf]
  exact h args vals argList oldV vRes hty hbi hF

theorem leafCallOption_callee_ne {f : String} {t : TowerType} (hf : f ≠ g)
    (hN : ∀ i, CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f i ≠ g)
    (h : LeafCallOption bi leafSpec f t br) :
    LeafCallOption (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out) f t br := by
  intro args vals argList oldT oldP vRes hbi hF
  rw [calleeTable_of_ne bi run hf] at hbi
  rw [calleeSpec_call_of_ne leafSpec N cg entry out (hN 0),
    calleeSpec_call_of_ne leafSpec N cg entry out (hN 1)]
  exact h args vals argList oldT oldP vRes hbi hF

end Transfer

/-- **The leaf conditions with a linked callee.**  Leaf conditions `ExitLeaves` at `D`, `DO`
    and `DA`, with `DA g = some (ts, dr)`, give those of the table extended by the callee
    `g` (`calleeTable`) and the leaf semantics running its program (`calleeSpec`), when `g`
    is none of the names the table interprets (a scalar operation, a scalar call, the array
    operations, `None`, `Some`, a leaf of a multi-output call), declares no `Option` payload,
    returns no control-flow value, and its own leaf conditions `hA` and `hW` hold. -/
theorem ExitLeaves.withCallee {bi : Builtins} {leafSpec : LeafSpec}
    {D DO : String → Option TowerType} {DA : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA) {N : Nat} {g : String} {cg : LowCT}
    {entry : List (Σ t : TowerType, RustVal t) → RustState}
    {out : (dt : TowerType) → RustState → RustVal dt} {run : List Value → Option Value}
    {ts : List TowerType} {dr : TowerType} (hDAg : DA g = some (ts, dr))
    (hDOg : DO g = none)
    (hop : (scalarOpExprT g (.SVar "a") (.SVar "b")).isSome = false)
    (hSg : exitScalarCall g = false) (hTSg : exitTowerScalarCall g = false)
    (hgi : g ≠ "index") (hgu : g ≠ "array_update") (hgl : g ≠ "array_lit")
    (hgr : g ≠ "repeat") (hgn : g ≠ "None") (hgs : g ≠ "Some")
    (hgN : ∀ f i, CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f i ≠ g)
    (hplain : ∀ vals v, run vals = some v → v.isControlFlow = false)
    (hA : LeafCallAgreesArgsTys (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out)
      g dr br ts)
    (hW : dr = .TU64 → LeafCallScalarTys (calleeTable bi g run)
      (calleeSpec leafSpec N g cg entry out) g .TU64 br ts) :
    ExitLeaves (calleeTable bi g run) (calleeSpec leafSpec N g cg entry out) br D DO DA where
  ops op va vb r na nb hsome hva hvb hna hnb hbi := by
    have hne : op ≠ g := by rintro rfl; rw [hop] at hsome; cases hsome
    rw [calleeTable_of_ne bi run hne] at hbi
    exact hL.ops op va vb r na nb hsome hva hvb hna hnb hbi
  plain f vals v hbi := by
    by_cases hf : f = g
    · subst hf
      rw [calleeTable_self] at hbi
      exact hplain vals v hbi
    · rw [calleeTable_of_ne bi run hf] at hbi
      exact hL.plain f vals v hbi
  marshal := hL.marshal
  callT f hsc h1 h2 h3 h4 hda := by
    have hne : f ≠ g := by rintro rfl; rw [hDAg] at hda; cases hda
    exact leafCallAgreesArgs_callee_ne hne (hL.callT f hsc h1 h2 h3 h4 hda)
  callS f hf := by
    have hne : f ≠ g := by rintro rfl; rw [hSg] at hf; cases hf
    exact leafCallScalar_callee_ne hne (hL.callS f hf)
  callTS f hf := by
    have hne : f ≠ g := by rintro rfl; rw [hTSg] at hf; cases hf
    exact leafCallScalar_callee_ne hne (hL.callTS f hf)
  index t vArr vIdx vRes arrV k h1 h2 h3 hbi := by
    rw [calleeTable_of_ne bi run (Ne.symm hgi)] at hbi
    exact hL.index t vArr vIdx vRes arrV k h1 h2 h3 hbi
  update arr z t vArr vIdx vSrc vRes arrV k m h1 h2 h3 h4 h5 h6 hbi := by
    rw [calleeTable_of_ne bi run (Ne.symm hgu)] at hbi
    exact hL.update arr z t vArr vIdx vSrc vRes arrV k m h1 h2 h3 h4 h5 h6 hbi
  indexT t t' vArr vIdx vRes arrV k h1 h2 h3 hbi := by
    rw [calleeTable_of_ne bi run (Ne.symm hgi)] at hbi
    exact hL.indexT t t' vArr vIdx vRes arrV k h1 h2 h3 hbi
  updateT arr t vArr vIdx vSrc vRes arrV srcV k h1 h2 h3 h4 hbi := by
    rw [calleeTable_of_ne bi run (Ne.symm hgu)] at hbi
    exact hL.updateT arr t vArr vIdx vSrc vRes arrV srcV k h1 h2 h3 h4 hbi
  arrLitN c k hc hm args vals argList oldV vRes hl hty hbi hF := by
    rw [calleeTable_of_ne bi run (Ne.symm hgl)] at hbi
    rw [calleeSpec_call_of_ne leafSpec N cg entry out (Ne.symm hgl)]
    exact hL.arrLitN c k hc hm args vals argList oldV vRes hl hty hbi hF
  repeatN c k hc hm args vv vc vRes argList oldV hk hbi hF := by
    rw [calleeTable_of_ne bi run (Ne.symm hgr)] at hbi
    rw [calleeSpec_call_of_ne leafSpec N cg entry out (Ne.symm hgr)]
    exact hL.repeatN c k hc hm args vv vc vRes argList oldV hk hbi hF
  callD f dr' hd hdo hda hsc h1 h2 h3 h4 := by
    have hne : f ≠ g := by rintro rfl; rw [hDAg] at hda; cases hda
    exact leafCallAgreesArgs_callee_ne hne (hL.callD f dr' hd hdo hda hsc h1 h2 h3 h4)
  wordD f hd hda hsc h1 h2 h3 h4 := by
    have hne : f ≠ g := by rintro rfl; rw [hDAg] at hda; cases hda
    exact leafCallScalar_callee_ne hne (hL.wordD f hd hda hsc h1 h2 h3 h4)
  optD f t hdo hsc h1 h2 h3 h4 := by
    have hne : f ≠ g := by rintro rfl; rw [hDOg] at hdo; cases hdo
    exact leafCallOption_callee_ne hne (hgN f) (hL.optD f t hdo hsc h1 h2 h3 h4)
  callA f ts' dr' hda hsc h1 h2 h3 h4 := by
    by_cases hf : f = g
    · subst hf
      rw [hDAg, Option.some.injEq, Prod.mk.injEq] at hda
      obtain ⟨rfl, rfl⟩ := hda
      exact hA
    · exact leafCallAgreesArgsTys_callee_ne hf (hL.callA f ts' dr' hda hsc h1 h2 h3 h4)
  wordA f ts' hda hsc h1 h2 h3 h4 := by
    by_cases hf : f = g
    · subst hf
      rw [hDAg, Option.some.injEq, Prod.mk.injEq] at hda
      obtain ⟨rfl, rfl⟩ := hda
      exact hW rfl
    · exact leafCallScalarTys_callee_ne hf (hL.wordA f ts' hda hsc h1 h2 h3 h4)
  optCtors := by
    refine ⟨fun vals r h => ?_, fun vals r h => ?_⟩
    · rw [calleeTable_of_ne bi run (Ne.symm hgn)] at h
      exact hL.optCtors.1 vals r h
    · rw [calleeTable_of_ne bi run (Ne.symm hgs)] at h
      exact hL.optCtors.2 vals r h

/-- A name the table does not otherwise interpret: none of a scalar operation, a scalar
    call, the array operations, `None`, `Some`, `len`, a leaf of a multi-output call. -/
def CalleeNameOk (g : String) : Prop :=
  (scalarOpExprT g (.SVar "a") (.SVar "b")).isSome = false ∧ exitScalarCall g = false ∧
    exitTowerScalarCall g = false ∧ g ≠ "index" ∧ g ≠ "array_update" ∧ g ≠ "array_lit" ∧
    g ≠ "repeat" ∧ g ≠ "None" ∧ g ≠ "Some" ∧ g ≠ "len" ∧
    ∀ f i, CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f i ≠ g

theorem callNPrefix (x : String) : "callN:".toList.isPrefixOf ("callN:" ++ x).toList = true := by
  simp [String.toList_append, List.isPrefixOf]

/-- The leaf names of a multi-output call start with `callN:`. -/
theorem callNLeafName_prefix (f : String) (i : Nat) :
    "callN:".toList.isPrefixOf (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f i).toList = true := by
  unfold CatCrypt.Crypto.Jasmin.LowCT.callNLeafName
  rw [String.append_assoc, String.append_assoc]
  exact callNPrefix _

/-- `CalleeNameOk` as a Boolean test. -/
def calleeNameOkB (g : String) : Bool :=
  !(scalarOpExprT g (.SVar "a") (.SVar "b")).isSome && !exitScalarCall g &&
    !exitTowerScalarCall g &&
    !(["index", "array_update", "array_lit", "repeat", "None", "Some", "len"].contains g) &&
    !("callN:".toList.isPrefixOf g.toList)

theorem calleeNameOk_of_B {g : String} (h : calleeNameOkB g = true) : CalleeNameOk g := by
  simp only [calleeNameOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hop, hS⟩, hTS⟩, hn⟩, hN⟩ := h
  refine ⟨hop, hS, hTS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun f i he => ?_⟩
  all_goals first
    | (rintro rfl; simp at hn)
    | (rw [← he, callNLeafName_prefix] at hN; cases hN)

/-- A value of a callee carries no control-flow tag. -/
theorem calleeRun_plain {R : ExitRes} {ps : List String} {read : Env → Outcome} {ρ : Env}
    {vals : List Value} {v : Value} (h : calleeRun A R ps read ρ vals = some v) :
    v.isControlFlow = false := by
  unfold calleeRun at h
  split_ifs at h with hg
  rcases hrd : read (bindParams ρ ps vals) with w | _ | _ | _ | _ <;> rw [hrd] at h <;>
    try cases h
  simp only at h
  split_ifs at h with hw
  cases h
  exact hw.1

/-- The result type of a callee with result placement `R`: the tower type of a tower result,
    the word type `TU64` otherwise. -/
def calleeResTy : ExitRes → TowerType
  | .tower t => t
  | _ => .TU64

/-- A callee lowered by the typed front: its name `g`, the placement `A` and the result
    placement `R` of its lowered body, its parameters `ps`, its reading `read` on a table,
    the environment `ρ` and the state `rs0` its parameters extend, its lowered program `cg`,
    and the declared call result types `D`, payload placements `DO` and linked callees `DA`
    of its own lowering. -/
structure CalleeT where
  g : String
  A : ExitTowers
  R : ExitRes
  ps : List String
  read : Builtins → Env → Outcome
  ρ : Env
  rs0 : RustState
  cg : LowCT
  D : String → Option TowerType
  DO : String → Option TowerType
  DA : String → Option (List TowerType × TowerType)

/-- The argument slot types and the result type at which the callee `c` is linked. -/
def CalleeT.sig (c : CalleeT) : List TowerType × TowerType :=
  (calleeArgTys c.A c.ps, calleeResTy c.R)

/-- The table `bi` extended by the callees `cs`, the last one lowest: each callee is the
    value `calleeRun` of its reading on the table extended by the callees below it. -/
def linkTable (bi : Builtins) : List CalleeT → Builtins
  | [] => bi
  | c :: cs =>
      calleeTable (linkTable bi cs) c.g (calleeRun c.A c.R c.ps (c.read (linkTable bi cs)) c.ρ)

/-- The leaf semantics `leafSpec` extended by the callees `cs`, the last one lowest: each
    callee runs its lowered program on the leaf semantics extended by the callees below
    it. -/
noncomputable def linkSpec (leafSpec : LeafSpec) (N : Nat) : List CalleeT → LeafSpec
  | [] => leafSpec
  | c :: cs =>
      calleeSpec (linkSpec leafSpec N cs) N c.g c.cg (calleeEntry c.A c.rs0 c.ps)
        (calleeOut (linkSpec leafSpec N cs) c.R)

/-- The conditions of the callee `c` above the callees `cs`: a name the table does not
    otherwise interpret, a scalar result or a tower result of a type other than `TU64`,
    parameters outside the reserved names, the environment `ρ` in agreement with the state
    `rs0`, the callees `cs` recorded in its own `DA` and not in its `DO`, and the simulation
    of its reading by its lowered program under the leaf conditions of the callees below it
    at its own declared maps. -/
def CalleeOk (bi : Builtins) (leafSpec : LeafSpec) (N : Nat) (br : ValueTowerBridge)
    (c : CalleeT) (cs : List CalleeT) : Prop :=
  CalleeNameOk c.g ∧ (c.R = .scalar ∨ ∃ t, c.R = .tower t ∧ t ≠ .TU64) ∧
    (∀ p ∈ c.ps, exitReserved p = false) ∧ envAgreesT br c.A c.ρ c.rs0 ∧
    (∀ c' ∈ cs, c.DA c'.g = some c'.sig ∧ c.DO c'.g = none) ∧
    (ExitLeaves (linkTable bi cs) (linkSpec leafSpec N cs) br c.D c.DO c.DA →
      ∀ env rs, envAgreesT br c.A env rs → (∃ v, c.read (linkTable bi cs) env = .val v) →
        ∃ r, RustExec N (linkSpec leafSpec N cs) c.cg rs r ∧
          outcomeAgreesT br c.R (c.read (linkTable bi cs) env) r)

/-- **The leaf conditions with linked callees.**  For a table `bi` and a leaf semantics
    `leafSpec` with leaf conditions at every `D`, `DO`, `DA`, under which a scalar word
    related at `TU64` decodes to limb `0` and programs run deterministically, the table and
    the leaf semantics extended by callees `cs` each satisfying `CalleeOk` above the callees
    below it have leaf conditions at every `D`, `DO`, `DA` recording each callee in `DA` at
    its linked types and not in `DO`. -/
theorem exitLeaves_linkT {bi : Builtins} {leafSpec : LeafSpec} {N : Nat}
    (hbase : ∀ (D DO : String → Option TowerType)
      (DA : String → Option (List TowerType × TowerType)), ExitLeaves bi leafSpec br D DO DA)
    (hscal : ∀ (v : Value) (x : RustVal .TU64), br .TU64 v x → ScalarValN v →
      valueToScalar v = some (towerLimb x 0))
    (hdet : ∀ (ls : LeafSpec) (c : LowCT) rs r₁ r₂, RustExec N ls c rs r₁ →
      RustExec N ls c rs r₂ → r₁ = r₂) :
    ∀ (cs : List CalleeT), (∀ c cs', c :: cs' <:+ cs → CalleeOk bi leafSpec N br c cs') →
      ∀ (D DO : String → Option TowerType) (DA : String → Option (List TowerType × TowerType)),
        (∀ c ∈ cs, DA c.g = some c.sig ∧ DO c.g = none) →
        ExitLeaves (linkTable bi cs) (linkSpec leafSpec N cs) br D DO DA
  | [], _, D, DO, DA, _ => hbase D DO DA
  | c :: cs, hok, D, DO, DA, hD => by
    have hok' : ∀ c' cs', c' :: cs' <:+ cs → CalleeOk bi leafSpec N br c' cs' :=
      fun c' cs' hs => hok c' cs' (hs.trans (List.suffix_cons c cs))
    have ih := exitLeaves_linkT hbase hscal hdet cs hok'
    obtain ⟨⟨hop, hS, hTS, hgi, hgu, hgl, hgr, hgn, hgs, -, hgN⟩, hR, hres, hρ, hsub, hsim⟩ :=
      hok c cs (List.suffix_refl _)
    have hL := ih D DO DA (fun c' hc' => hD c' (List.mem_cons_of_mem _ hc'))
    have hF := hsim (ih c.D c.DO c.DA hsub)
    obtain ⟨hDAg, hDOg⟩ := hD c (List.mem_cons_self ..)
    have hRd : (c.R = .scalar ∧ 8 ≤ (calleeResTy c.R).storageBytes) ∨
        c.R = .tower (calleeResTy c.R) := by
      rcases hR with h | ⟨t, h, -⟩ <;> rw [h]
      · exact Or.inl ⟨rfl, by decide⟩
      · exact Or.inr rfl
    have hA := leafCallAgreesArgsTys_callee (bi := linkTable bi cs) (g := c.g) hL.marshal hscal
      (hdet _ c.cg) hF hρ hres hRd
    refine hL.withCallee hDAg hDOg hop hS hTS hgi hgu hgl hgr hgn hgs hgN
      (fun _ _ h => calleeRun_plain h) hA ?_
    intro hdr
    have hRs : c.R = .scalar := by
      rcases hR with h | ⟨t, h, ht⟩
      · exact h
      · rw [h] at hdr
        exact absurd hdr ht
    rw [hRs] at hF ⊢
    exact leafCallScalarTys_callee hL.marshal hscal (hdet _ c.cg) hF hρ hres

end Callees

end CatCrypt.Crypto.Hax
