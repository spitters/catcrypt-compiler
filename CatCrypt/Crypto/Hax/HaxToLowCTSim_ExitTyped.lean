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
  addition and subtraction, and the width-tagged word calls `op#w` as masked
  `SExpr` templates, `WidthOp.sexpr`) is `RScalarSetExpr`;
* `index(arr, i)` with `arr` in a tower and `i` scalar is an `RArrLoad` into the
  reserved tower slot `exitCallName`, followed by a copy of its limb `0` into the
  scalar slot of the bound name;
* `array_update(arr, i, src)` rebinding `arr` is an `RArrStore` into `arr`;
* every other call is an `RCall` into `exitCallName`: its scalar arguments are
  first stored into reserved tower slots `exitMarshalName x` (`callMarshal`), its
  tower arguments are read in place, and the result is copied into the tower slot
  of the bound name (`RCopy`) or, for a call with a scalar result
  (`exitScalarCall`), its limb `0` into the scalar slot;
* a counted loop or a `while` loop in an exit context is lowered to the exit-flag
  loop followed by `breakLoop`, whether its body breaks or not;
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
limb `0` of a fresh tower slot is related to the scalar, a call with a tower result satisfies
`LeafCallAgreesArgs`, a call with a scalar result and the element load return a scalar word
whose decoding is limb `0` of the leaf output (`LeafCallScalar`, `IndexScalarAgrees`), and
the element store satisfies `ArrUpdateAgrees`.  The range conditions hold on the table
`exitRange bi`, which refuses every scalar result outside `ScalarValN`
(`leafCallScalar_exitRange`, `indexScalarAgrees_exitRange`).

## Main definitions

* `ExitTowers`, `exitCallName`, `exitMarshalName`
* `scalarOpExprT`, `WidthOp`, `widthOpOf`
* `callMarshal`, `letHeadT`, `haxToLowCTKT`, `haxToLowCTFnT`, `haxToLowCTFnI`
* `exitTowers`, `exitResultPlace`
* `exitSimOkT`, `exitSimWhyT`
* `envAgreesT`, `envAgreesExitT`, `ExitSimTy`, `ExitLeaves`, `exitRange`

## Main results

* `callMarshal_sim`: the marshalling of call arguments into tower slots
* `head_lit`, `head_var`, `head_app`: the heads of a `letBind`
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

/-! ## §2  Scalar operations -/

/-- The two-operand operations of hax-lean's width-tagged word calls `op#w`. -/
inductive WidthOp where
  | add | sub | mul | and | or | xor | shl | shr | rotr | rotl
  deriving DecidableEq, Repr

/-- The width of a width tag: `8`, `16`, `32`, `64`, and `size` (width `64`). -/
def widthOfTag : String → Option Nat
  | "8" => some 8
  | "16" => some 16
  | "32" => some 32
  | "64" => some 64
  | "size" => some 64
  | _ => none

/-- The operation of a width-tagged call name before its `#`. -/
def widthOpName : String → Option WidthOp
  | "wrapping_add" => some .add
  | "wrapping_sub" => some .sub
  | "wrapping_mul" => some .mul
  | "BitAnd" => some .and
  | "BitOr" => some .or
  | "BitXor" => some .xor
  | "Shl" => some .shl
  | "Shr" => some .shr
  | "rotate_right" => some .rotr
  | "rotate_left" => some .rotl
  | _ => none

/-- The width and operation of a width-tagged call name `op#w`. -/
def widthOpOf (f : String) : Option (Nat × WidthOp) :=
  match f.splitOn "#" with
  | [op, tag] =>
      match widthOfTag tag, widthOpName op with
      | some w, some o => some (w, o)
      | _, _ => none
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
    `scalarOpExpr`, their capitalised forms, and the width-tagged calls of
    `widthOpOf`. -/
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
  | _ => (widthOpOf op).map fun p => p.2.sexpr p.1 a b

/-- The call names whose result is a scalar besides the width-tagged ones. -/
def exitScalarCalls : List String :=
  ["len", "lt", "gt", "le", "ge", "eq", "ne", "add", "sub",
   "Lt", "Gt", "Le", "Ge", "Eq", "Ne", "Add", "Sub", "Mul", "Div", "Rem",
   "BitAnd", "BitOr", "BitXor", "Shl", "Shr", "Not", "Neg"]

/-- A call whose result is held in the scalar heap: a name of `exitScalarCalls` or a
    width-tagged name (containing `#`). -/
def exitScalarCall (f : String) : Bool := exitScalarCalls.contains f || f.contains '#'

/-! ## §3  The heads of a `letBind` -/

/-- The argument slots of a call reading its arguments at the tower type `dt`, and the
    context storing its scalar arguments: an argument held in a tower at `dt` is read
    in place; a scalar argument `x` is stored into limb `0` of the fresh tower slot
    `exitMarshalName x`.  `none` when an argument is not a variable or is held in a
    tower at another type. -/
def callMarshal (A : ExitTowers) (dt : TowerType) :
    List ImpExpr → Option ((LowCT → LowCT) × List Located)
  | [] => some (id, [])
  | .var x :: as =>
      match callMarshal A dt as with
      | none => none
      | some (ctx, ls) =>
        match A.lookup x with
        | some t => if t = dt then some (ctx, ⟨x, dt⟩ :: ls) else none
        | none => some (fun c => .RLetZero (exitMarshalName x) dt
              (.RSeq (.RLimbStoreExpr ⟨exitMarshalName x, dt⟩ 0 (.SVar x)) (ctx c)),
              ⟨exitMarshalName x, dt⟩ :: ls)
  | _ :: _ => none

/-- The `SExpr` of a scalar operation `f` on two scalar variables bound to a scalar
    name `n`. -/
def scalarOpHeadT (A : ExitTowers) (n f : String) : List ImpExpr → Option SExpr
  | [.var a, .var b] =>
      if A.lookup n = none ∧ A.lookup a = none ∧ A.lookup b = none then
        scalarOpExprT f (.SVar a) (.SVar b)
      else none
  | _ => none

/-- The head of `let n = index(arr, idx)` with `arr` in a tower and `idx`, `n`
    scalar: load the element into `exitCallName` and copy its limb `0` into `n`. -/
def indexHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var arr, .var idx] =>
      match A.lookup arr with
      | some t =>
          if A.lookup idx = none ∧ A.lookup n = none then
            some fun b => .RLetZero exitCallName .TFp
              (.RSeq (.RArrLoad ⟨exitCallName, .TFp⟩ ⟨arr, t⟩ idx)
                (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b))
          else none
      | none => none
  | _ => none

/-- The head of `let arr = array_update(arr, idx, src)` with `arr` in a tower of type
    `t`, `idx` scalar, and `src` scalar or in a tower at `t.elemType`: store `src` at
    element `idx` of `arr`. -/
def updateHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var arr, .var idx, .var src] =>
      match A.lookup arr with
      | some t =>
          if n = arr ∧ A.lookup idx = none then
            match callMarshal A t.elemType [.var src] with
            | some (ctx, [srcLoc]) =>
                some fun b => .RSeq (ctx (.RArrStore ⟨arr, t⟩ idx srcLoc)) b
            | _ => none
          else none
      | none => none
  | _ => none

/-- The head of `let n = f(args)` for a call lowered to `RCall`: the call writes
    `exitCallName` at `towerOfCallName f` from the slots of `callMarshal`; a scalar
    result (`exitScalarCall f`) is copied from limb `0` into the scalar `n`, any other
    result into the tower slot `n`, which must be placed at the call's tower type. -/
def callHeadT (A : ExitTowers) (n f : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  let dt := towerOfCallName f
  match callMarshal A dt args with
  | none => none
  | some (ctx, ls) =>
    let callC : LowCT := .RLetZero exitCallName dt (ctx (.RCall f ⟨exitCallName, dt⟩ ls))
    if exitScalarCall f then
      if A.lookup n = none then
        some fun b => .RSeq callC (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)
      else none
    else if A.lookup n = some dt then
      some fun b => .RSeq callC (.RSeq (.RCopy ⟨n, dt⟩ ⟨exitCallName, dt⟩) b)
    else none

/-- The head of `let n = f(args)`: a scalar operation, an element load, an element
    store, or a call. -/
def appHeadT (A : ExitTowers) (n f : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match scalarOpHeadT A n f args with
  | some se => some fun b => .RSeq (.RScalarSetExpr n se) b
  | none =>
    if f = "index" then indexHeadT A n args
    else if f = "array_update" then updateHeadT A n args
    else callHeadT A n f args

/-- The head of `let n = val` under the placement `A`: a literal bound to a scalar
    name as in `letHead`; a copy between two scalar names as in `letHead`, between two
    tower names of one type by `RCopy`; a call by `appHeadT`. -/
def letHeadT (A : ExitTowers) (n : String) : ImpExpr → Option (LowCT → LowCT)
  | .lit l => if A.lookup n = none then letHead n (.lit l) else none
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

/-- The lowered tail value `e`: a scalar value stored into the scalar result slot as
    by `resultStore`, a tower variable copied into the tower slot `exitResName`. -/
def resultStoreT (A : ExitTowers) : ImpExpr → Option LowCT
  | .var x =>
      match A.lookup x with
      | some t => some (.RCopy ⟨exitResName, t⟩ ⟨x, t⟩)
      | none => resultStore (.var x)
  | e => resultStore e

/-- The exit-flag lowering under the placement `A`: `haxToLowCTK true` with the heads
    of `letHeadT A`, the tail store `resultStoreT A`, and, in an exit context, every
    counted loop with the bounds of `forBounds` or `forBoundsRt` and every `while` loop
    on a variable lowered to the exit-flag loop followed by `breakLoop`. -/
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
      match haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none
  | tl, fl, .typeAscription e _ => haxToLowCTKT A tl fl e
  | false, fl, .whileFoldReturn (.var c) body =>
      match haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none
  | false, fl, .forFoldReturn i lo hi body =>
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), _, some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
      | none, some (l, h), some (bC, _) =>
          some (exitForLoopRt (exitRunName fl) i l h bC, true)
      | _, _, _ => none
  | false, fl, .forFoldRevReturn i lo hi body =>
      match forBounds lo hi, haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
      | _, _ => none
  | false, some r, .forFold i lo hi body =>
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (l, h), _, some (bC, _) =>
          some (breakLoop (exitForLoop (exitRunName (some r)) i l h bC), false)
      | none, some (l, h), some (bC, _) =>
          some (breakLoop (exitForLoopRt (exitRunName (some r)) i l h bC), false)
      | _, _, _ => none
  | false, some r, .whileFold (.var c) body =>
      match haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (bC, _) => some (breakLoop (exitLoop (exitRunName (some r)) c bC), false)
      | none => none
  | _, some _, .cfBreak e => (exitStore e).map fun s => (s, true)
  | true, _, e => (resultStoreT A e).map fun s => (s, false)
  | false, _, e => (haxToLowCT e).map fun c => (c, false)

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

/-- The names a body binds or reads as scalars: literal bindings, results of scalar
    calls and element loads, loop counters and bounds, and conditions. -/
def exitScalarNames : ImpExpr → List String
  | .letBind n v b =>
      let here := match v with
        | .lit _ => [n]
        | .app f _ => if exitScalarCall f || f = "index" then [n] else []
        | _ => []
      here ++ exitScalarNames b
  | .seq a b => exitScalarNames a ++ exitScalarNames b
  | .ifThenElse (.var c) t e => c :: (exitScalarNames t ++ exitScalarNames e)
  | .ifThenElse _ t e => exitScalarNames t ++ exitScalarNames e
  | .typeAscription e _ => exitScalarNames e
  | .whileFoldReturn (.var c) b => c :: exitScalarNames b
  | .forFoldReturn i _ (.var h) b => i :: h :: exitScalarNames b
  | .forFoldReturn i _ _ b => i :: exitScalarNames b
  | .forFoldRevReturn i _ _ b => i :: exitScalarNames b
  | .forFold i _ (.var h) b => i :: h :: exitScalarNames b
  | .forFold i _ _ b => i :: exitScalarNames b
  | .whileFold (.var c) b => c :: exitScalarNames b
  | .whileFold _ b => exitScalarNames b
  | _ => []

/-- `(x, t) :: A` when `x` is neither placed in `A` nor a scalar name of `sc`. -/
def exitPlaceAt (sc : List String) (A : ExitTowers) (x : String) (t : TowerType) :
    ExitTowers :=
  if (A.lookup x).isNone && !sc.contains x then (x, t) :: A else A

/-- One pass of placement inference over a body, from the scalar names `sc`: the
    array argument of `index`, `array_update` and `len` is placed at `.TFp`; the
    result and the arguments of a call with a tower result are placed at the call's
    tower type; a copy between names takes the placement of the placed side. -/
def exitTowersStep (sc : List String) : ExitTowers → ImpExpr → ExitTowers
  | A, .letBind n v b =>
      let A' := match v with
        | .app f args =>
            if f = "index" ∨ f = "array_update" ∨ f = "len" then
              match args with
              | .var arr :: _ => exitPlaceAt sc A arr .TFp
              | _ => A
            else if exitScalarCall f then A
            else
              let dt := towerOfCallName f
              let A1 := (exitArgNames args).foldl (fun A x => exitPlaceAt sc A x dt) A
              exitPlaceAt sc A1 n dt
        | .var s =>
            match A.lookup n, A.lookup s with
            | some t, none => exitPlaceAt sc A s t
            | none, some t => exitPlaceAt sc A n t
            | _, _ => A
        | _ => A
      exitTowersStep sc A' b
  | A, .seq a b => exitTowersStep sc (exitTowersStep sc A a) b
  | A, .ifThenElse _ t e => exitTowersStep sc (exitTowersStep sc A t) e
  | A, .typeAscription e _ => exitTowersStep sc A e
  | A, .whileFoldReturn _ b => exitTowersStep sc A b
  | A, .forFoldReturn _ _ _ b => exitTowersStep sc A b
  | A, .forFoldRevReturn _ _ _ b => exitTowersStep sc A b
  | A, .forFold _ _ _ b => exitTowersStep sc A b
  | A, .whileFold _ b => exitTowersStep sc A b
  | A, _ => A

/-- The inferred placement of a body: three passes of `exitTowersStep`. -/
def exitTowers (e : ImpExpr) : ExitTowers :=
  let sc := exitScalarNames e
  exitTowersStep sc (exitTowersStep sc (exitTowersStep sc [] e) e) e

/-- The placement of the tail value of a body under `A`: the placement of its first
    tail variable, and `none` (scalar) when the tail is not a variable. -/
def exitResultPlace (A : ExitTowers) : ImpExpr → Option TowerType
  | .letBind _ _ b => exitResultPlace A b
  | .seq _ b => exitResultPlace A b
  | .ifThenElse _ t _ => exitResultPlace A t
  | .typeAscription e _ => exitResultPlace A e
  | .var x => A.lookup x
  | _ => none

/-- The function lowering under the inferred placement. -/
def haxToLowCTFnI (e : ImpExpr) : Option LowCT := haxToLowCTFnT (exitTowers e) e

/-! ## §6  The fragment -/

/-- `x` is held in the scalar heap under `A`. -/
def exitSc (A : ExitTowers) (x : String) : Bool := (A.lookup x).isNone

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

/-- A literal whose value is a scalar word: an unsigned literal of width at most `64`,
    an integer in `[0, 2^64)`, a bool or the unit. -/
def exitLitOk : ImpLit → Bool
  | .uintLit w _ => w != .w128
  | .int k => decide (0 ≤ k) && decide (k < 2 ^ 64)
  | .bool _ => true
  | .unit => true
  | _ => false

/-- A scalar payload of a `cfBreak`: a variable held in the scalar heap, a literal of
    `exitLitOk`, or `unitVal`. -/
def exitPayloadOk (A : ExitTowers) : ImpExpr → Bool
  | .var x => !exitReserved x && exitSc A x
  | .lit l => exitLitOk l
  | .unitVal => true
  | _ => false

/-- The fragment the typed simulation covers under the placement `A` with result
    placement `R`, at tail position `tl` and loop context `il`: every name is
    non-reserved; conditions, loop counters, runtime bounds and break payloads are
    scalar; a literal is bound to a scalar name; a copy keeps the placement; a call
    has a head of `appHeadT`; a tail variable has placement `R` and a tail literal or
    `unitVal` needs `R = none`. -/
def exitSimOkT (A : ExitTowers) (R : Option TowerType) : Bool → Bool → ImpExpr → Bool
  | tl, il, .letBind n (.lit l) body =>
      exitLitOk l && exitSc A n && !exitReserved n && exitSimOkT A R tl il body
  | tl, il, .letBind n (.var s) body =>
      !exitReserved n && !exitReserved s && decide (A.lookup n = A.lookup s) &&
        exitSimOkT A R tl il body
  | tl, il, .letBind n (.app f args) body =>
      !exitReserved n && exitArgsOk args && (appHeadT A n f args).isSome &&
        exitSimOkT A R tl il body
  | tl, il, .seq a b => exitSimOkT A R false il a && exitSimOkT A R tl il b
  | tl, il, .ifThenElse (.var v) t e =>
      !exitReserved v && exitSc A v && exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | tl, il, .typeAscription e _ => exitSimOkT A R tl il e
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
  | false, true, .whileFold (.var c) body =>
      !exitReserved c && exitSc A c && exitSimOkT A R false true body
  | _, true, .cfBreak p => exitPayloadOk A p
  | tl, _, .var x => !exitReserved x && (!tl || decide (A.lookup x = R))
  | tl, _, .unitVal => !tl || R.isNone
  | true, _, .lit l => exitLitOk l && R.isNone
  | _, _, _ => false

/-- The first construct of `e` outside the fragment `exitSimOkT A R tl il`, with the
    reason; `none` when `e` lies in the fragment. -/
def exitSimWhyT (A : ExitTowers) (R : Option TowerType) :
    Bool → Bool → ImpExpr → Option String
  | tl, il, .letBind n (.lit l) body =>
      if !exitLitOk l then some "literal not a scalar word"
      else if !exitSc A n then some "literal bound to a tower name"
      else if exitReserved n then some "reserved name" else exitSimWhyT A R tl il body
  | tl, il, .letBind n (.var s) body =>
      if exitReserved n || exitReserved s then some "reserved name"
      else if !decide (A.lookup n = A.lookup s) then some "copy across placements"
      else exitSimWhyT A R tl il body
  | tl, il, .letBind n (.app f args) body =>
      if exitReserved n || !exitArgsOk args then some "reserved name or non-variable argument"
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
  | false, true, .whileFold (.var c) body =>
      if exitReserved c then some "reserved name"
      else if !exitSc A c then some "condition placed in a tower"
      else exitSimWhyT A R false true body
  | _, true, .cfBreak p => if exitPayloadOk A p then none else some "break payload not scalar"
  | tl, _, .var x =>
      if exitReserved x then some "reserved name"
      else if tl && !decide (A.lookup x = R) then some "tail placement" else none
  | tl, _, .unitVal => if !tl || R.isNone then none else some "tail placement"
  | true, _, .lit l =>
      if exitLitOk l && R.isNone then none else some "tail literal"
  | _, _, .letBind _ v _ => some s!"letBind {exitWhyHead v}"
  | tl, il, e => some s!"{exitWhyHead e} (tail {tl}, loop {il})"

theorem exitSimWhyT_eq_none_iff (A : ExitTowers) (R : Option TowerType) (tl il : Bool)
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

/-- The result agreement for result placement `R`: the decoding of `v` in the scalar
    result slot, or `v` related by `br` to the tower result slot. -/
def resultAgreesT (br : ValueTowerBridge) (R : Option TowerType) (v : Value) (rs : RustState) :
    Prop :=
  match R with
  | none => valueToScalar v = some (rs.rsScalar exitResName)
  | some t => ∃ val, rs.rsTower exitResName = some ⟨t, val⟩ ∧ br t v val

/-- Agreement with the exit component under the placement `A` and result placement
    `R`, for an expression in tail position `tl`. -/
def envAgreesExitT (br : ValueTowerBridge) (A : ExitTowers) (R : Option TowerType)
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

variable {br : ValueTowerBridge} {A : ExitTowers} {R : Option TowerType}

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
  all_goals try simp only [Option.map_some, SExpr.evalState, SExpr.eval, ha, hb]
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

/-- The element load agrees with the builtin `index` at a scalar element: for an array
    value related by `br` to a slot of type `t` and an index decoding to `k`, the
    builtin's result is a scalar value whose decoding is limb `0` of the element the leaf
    loads. -/
def IndexScalarAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (t : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
    br t vArr arrV → valueToScalar vIdx = some k →
    bi "index" [vArr, vIdx] = some vRes →
    ScalarValN vRes ∧ valueToScalar vRes = some
      (towerLimb (leafSpec.arrLoad { locVar := exitCallName, locSrc := .TFp } default ⟨t, arrV⟩ k) 0)

/-- The leaf conditions of the typed simulation: the scalar operations, the absence of
    control-flow results, the storage of a scalar into limb `0` of a fresh tower slot,
    the calls with a tower result (`LeafCallAgreesArgs`) and with a scalar result
    (`LeafCallScalar`), the element load and the element store. -/
structure ExitLeaves (bi : Builtins) (leafSpec : LeafSpec) (br : ValueTowerBridge) : Prop where
  ops : ScalarOpsSoundT bi
  plain : _root_.Hax.ContinueFlag.BuiltinsPlain bi
  marshal : ∀ (loc : Located) (v : Value) (k : Nat), ScalarValN v → valueToScalar v = some k →
    br loc.locDst v (leafSpec.limbStore loc default 0 (BitVec.ofNat 64 k))
  callT : ∀ f, exitScalarCall f = false → LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) br
  callS : ∀ f, exitScalarCall f = true → LeafCallScalar bi leafSpec f (towerOfCallName f) br
  index : IndexScalarAgrees br bi leafSpec
  update : ArrUpdateAgrees br bi leafSpec

/-- `ScalarValN` as a Boolean test. -/
def scalarValNB : Value → Bool
  | .uint _ n => decide (n < 2 ^ 64)
  | .bool _ => true
  | .int n => decide (0 ≤ n) && decide (n < 2 ^ 64)
  | .unit => true
  | _ => false

theorem scalarValNB_iff (v : Value) : scalarValNB v = true ↔ ScalarValN v := by
  cases v <;> simp [scalarValNB, ScalarValN]

/-- A call whose result the typed lowering holds in the scalar heap: a scalar call or an
    element load. -/
def exitScalarResult (f : String) : Bool := exitScalarCall f || f == "index"

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
    {dt : TowerType} {br : ValueTowerBridge} (hf : exitScalarCall f = true)
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

/-- The element load agrees on the range-refusing table when, on every scalar-word result
    of `index`, limb `0` of the loaded element is its decoding. -/
theorem indexScalarAgrees_exitRange {br : ValueTowerBridge} {bi : Builtins}
    {leafSpec : LeafSpec}
    (h : ∀ (t : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
      br t vArr arrV → valueToScalar vIdx = some k →
      bi "index" [vArr, vIdx] = some vRes → ScalarValN vRes →
      valueToScalar vRes = some (towerLimb (leafSpec.arrLoad
        { locVar := exitCallName, locSrc := .TFp } default ⟨t, arrV⟩ k) 0)) :
    IndexScalarAgrees br (exitRange bi) leafSpec := by
  intro t vArr vIdx vRes arrV k hbr hk hbi
  obtain ⟨hb, hs⟩ := exitRange_some hbi
  have hsv := hs (by simp [exitScalarResult])
  exact ⟨hsv, h t vArr vIdx vRes arrV k hbr hk hb hsv⟩

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

end SourceStepsT

/-! ## §10  The simulation statement and the translator's equations -/

/-- The simulation of `e` under the placement `A` and result placement `R`: from states
    agreeing under `A` with the exit flag `0`, a run of `denote'` ending in a value is
    matched by a run of `haxToLowCTKT A` ending in states agreeing under `A`; a command
    that cannot exit leaves the flag `0`. -/
def ExitSimTy (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (A : ExitTowers) (R : Option TowerType) (e : ImpExpr) : Prop :=
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
    (t e : ImpExpr) :
    haxToLowCTKT A tl fl (.ifThenElse (.var v) t e) =
      match haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_typeAscription_eq (tl : Bool) (fl : Option String) (e : ImpExpr)
    (ty : String) : haxToLowCTKT A tl fl (.typeAscription e ty) = haxToLowCTKT A tl fl e := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_whileFoldReturn_eq (fl : Option String) (c : String) (body : ImpExpr) :
    haxToLowCTKT A false fl (.whileFoldReturn (.var c) body) =
      match haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none := by
  cases fl <;> rfl

theorem haxToLowCTKT_forFoldReturn_eq (fl : Option String) (i : String) (lo hi body : ImpExpr) :
    haxToLowCTKT A false fl (.forFoldReturn i lo hi body) =
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), _, some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
      | none, some (l, h), some (bC, _) =>
          some (exitForLoopRt (exitRunName fl) i l h bC, true)
      | _, _, _ => none := by
  cases fl <;> rfl

theorem haxToLowCTKT_forFoldRevReturn_eq (fl : Option String) (i : String)
    (lo hi body : ImpExpr) :
    haxToLowCTKT A false fl (.forFoldRevReturn i lo hi body) =
      match forBounds lo hi, haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
      | _, _ => none := by
  cases fl <;> rfl

theorem haxToLowCTKT_forFold_some_eq (r i : String) (lo hi body : ImpExpr) :
    haxToLowCTKT A false (some r) (.forFold i lo hi body) =
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (l, h), _, some (bC, _) =>
          some (breakLoop (exitForLoop (exitRunName (some r)) i l h bC), false)
      | none, some (l, h), some (bC, _) =>
          some (breakLoop (exitForLoopRt (exitRunName (some r)) i l h bC), false)
      | _, _, _ => none := rfl

theorem haxToLowCTKT_whileFold_some_eq (r c : String) (body : ImpExpr) :
    haxToLowCTKT A false (some r) (.whileFold (.var c) body) =
      match haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (bC, _) => some (breakLoop (exitLoop (exitRunName (some r)) c bC), false)
      | none => none := rfl

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

/-- Every slot `callMarshal` reads a call argument from has the call's tower type. -/
theorem callMarshal_locSrc (A : ExitTowers) (dt : TowerType) :
    ∀ (args : List ImpExpr) (ctx : LowCT → LowCT) (ls : List Located),
      callMarshal A dt args = some (ctx, ls) → ∀ a ∈ ls, a.locSrc = dt := by
  intro args
  induction args with
  | nil => intro ctx ls h; simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨-, rfl⟩ := h; simp
  | cons a as ih =>
    intro ctx ls h
    cases a with
    | var x =>
      rcases hr : callMarshal A dt as with _ | ⟨ctx', ls'⟩
      · simp [callMarshal, hr] at h
      rcases hx : A.lookup x with _ | t
      · simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · rfl
        · exact ih ctx' ls' hr b hb
      · simp only [callMarshal, hr, hx] at h
        split_ifs at h with htd
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · rfl
        · exact ih ctx' ls' hr b hb
    | _ => simp [callMarshal] at h

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
    `marshalVal` of the scalar, and holds, for each argument, a tower value related by
    `br` to the argument's value in the slot it reads the argument from. -/
theorem callMarshal_sim {br : ValueTowerBridge} {A : ExitTowers} {env : Env} {rs : RustState}
    (hag : envAgreesT br A env rs)
    (hmar : ∀ (loc : Located) (v : Value) (k : Nat), ScalarValN v → valueToScalar v = some k →
      br loc.locDst v (leafSpec.limbStore loc default 0 (BitVec.ofNat 64 k)))
    (dt : TowerType) :
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
          List.Forall₂ (fun v (a : Located) => ∃ val, rs1.rsTower a.locVar = some ⟨dt, val⟩ ∧
            br dt v val) vals ls := by
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
        simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
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
        · refine List.Forall₂.cons ⟨marshalVal leafSpec dt x (rs.rsScalar x), ?_, ?_⟩ hF1
          · rcases hM1 x with h1 | h1
            · rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]
            · exact h1
          · exact hmar ⟨exitMarshalName x, dt⟩ v _ hsv hdv
      · -- a tower argument at the call's type
        simp only [callMarshal, hr, hx] at h
        split_ifs at h with htd
        subst htd
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, val, hval, hbr⟩ := envAgreesT_tower hag hxr hx hxv
        obtain ⟨rs1, hex, hS1, hT1, hM1, hF1⟩ := ih ctx' ls' vs hr hok hF rs0 hS hT
        refine ⟨rs1, hex, hS1, hT1, hM1, List.Forall₂.cons ⟨val, ?_, hbr⟩ hF1⟩
        rw [hT1 x (ne_marshal_of_nonreserved hxr), hT x hxr]
        exact hval
    | _ => simp [callMarshal] at h

end Marshal

/-- The tower values `RCall` reads from slots holding related values are related
    elementwise. -/
theorem forall₂_filterMap_rsTower {br : ValueTowerBridge} {dt : TowerType} {rs : RustState} :
    ∀ {vals : List Value} {ls : List Located},
      List.Forall₂ (fun v (a : Located) => ∃ val, rs.rsTower a.locVar = some ⟨dt, val⟩ ∧
        br dt v val) vals ls →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals
        (ls.filterMap fun a => rs.rsTower a.locVar)
  | [], [], _ => by simp
  | v :: vs, a :: as, List.Forall₂.cons ⟨val, hv, hb⟩ h => by
    rw [List.filterMap_cons, hv]
    exact List.Forall₂.cons hb (forall₂_filterMap_rsTower h)

theorem forall₂_rsTower_typed {br : ValueTowerBridge} {dt : TowerType} {rs : RustState}
    {vals : List Value} {ls : List Located}
    (h : List.Forall₂ (fun v (a : Located) => ∃ val, rs.rsTower a.locVar = some ⟨dt, val⟩ ∧
      br dt v val) vals ls) (hs : ∀ a ∈ ls, a.locSrc = dt) :
    ∀ a ∈ ls, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hh _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨val, hv, -⟩ := hh
      have hd : a.locDst = dt := hs a (List.mem_cons_self ..)
      rw [hd]; exact ⟨val, hv⟩
    · exact ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) a ha

/-! ## §12  The heads of a `letBind` -/

theorem exitSimOkT_letBind_body (A : ExitTowers) (R : Option TowerType) (tl il : Bool)
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
    (A : ExitTowers) (R : Option TowerType) (n : String) (val body : ImpExpr) : Prop :=
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
  (A : ExitTowers) (R : Option TowerType)

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

theorem head_lit (n : String) (l : ImpLit) (body : ImpExpr) :
    HeadSimT bi N leafSpec br A R n (.lit l) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitLitOk l = true ∧ exitSc A n = true ∧ exitReserved n = false := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2⟩)
  obtain ⟨hl, hsc, hn⟩ := hh
  have hsc' : A.lookup n = none := by simpa [exitSc] using hsc
  have hk' : letHead n (.lit l) = some k := by simpa [letHeadT, hsc'] using hk
  obtain ⟨kk, hkk, hsv, hdk⟩ : ∃ kk, k = (fun bC => .RLetU64Zero n (.RSeq (.RScalarSet n kk) bC)) ∧
      ScalarValN (Value.ofLit l) ∧ valueToScalar (Value.ofLit l) = some kk := by
    cases l with
    | uintLit w m =>
      simp only [letHead, Option.some.injEq] at hk'
      refine ⟨_, hk'.symm, ?_, rfl⟩
      show m % w.modulus < 2 ^ 64
      cases w <;> simp only [IntWidth.modulus, IntWidth.bits] <;> first
        | omega | (simp only [exitLitOk] at hl; exact absurd hl (by decide))
    | int z =>
      simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [letHead, ge_iff_le, hl.1, if_true, Option.some.injEq] at hk'
      exact ⟨_, hk'.symm, hl, by simp [valueToScalar, Value.ofLit, hl.1]⟩
    | bool b =>
      simp only [letHead, Option.some.injEq] at hk'
      exact ⟨_, hk'.symm, trivial, valueToScalar_bool b⟩
    | unit => simp [letHead] at hk'
    | _ => simp [exitLitOk] at hl
  subst hkk
  rw [denote'_letBind_run_val bi fuel n _ body env env _ (denote'_lit_run bi fuel l env)
    hsv.not_cf] at hrun
  exact ⟨_, _, hrun, envAgreesT_extend hn hsc' hsv hdk hag, ret_setScalar hn _ hret,
    fun bC rs' h => exec_letU64_set N leafSpec n kk bC rs rs' h⟩

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
      A.lookup n = none ∧ k = fun b => .RLetZero exitCallName .TFp
        (.RSeq (.RArrLoad ⟨exitCallName, .TFp⟩ ⟨arr, t⟩ idx)
          (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)) := by
  unfold indexHeadT at h
  split at h
  · rename_i arr idx
    rcases ht : A.lookup arr with _ | t <;> rw [ht] at h
    · cases h
    · simp only at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      exact ⟨arr, idx, t, rfl, ht, hc.1, hc.2, h.symm⟩
  · cases h

theorem updateHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : updateHeadT A n args = some k) :
    ∃ arr idx src t ctx srcLoc, args = [.var arr, .var idx, .var src] ∧ n = arr ∧
      A.lookup arr = some t ∧ A.lookup idx = none ∧
      callMarshal A t.elemType [.var src] = some (ctx, [srcLoc]) ∧
      k = fun b => .RSeq (ctx (.RArrStore ⟨arr, t⟩ idx srcLoc)) b := by
  unfold updateHeadT at h
  split at h
  · rename_i arr idx src
    rcases ht : A.lookup arr with _ | t <;> rw [ht] at h
    · cases h
    · simp only at h
      split_ifs at h with hc
      rcases hm : callMarshal A t.elemType [.var src] with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
      · cases h
      · rcases ls with _ | ⟨srcLoc, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq] at h
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, src, t, ctx, srcLoc, rfl, hc.1, ht, hc.2, hm, h.symm⟩
  · cases h

theorem callHeadT_some {n f : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : callHeadT A n f args = some k) :
    ∃ ctx ls, callMarshal A (towerOfCallName f) args = some (ctx, ls) ∧
      ((exitScalarCall f = true ∧ A.lookup n = none ∧
          k = fun b => .RSeq (.RLetZero exitCallName (towerOfCallName f)
            (ctx (.RCall f ⟨exitCallName, towerOfCallName f⟩ ls)))
            (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)) ∨
        (exitScalarCall f = false ∧ A.lookup n = some (towerOfCallName f) ∧
          k = fun b => .RSeq (.RLetZero exitCallName (towerOfCallName f)
            (ctx (.RCall f ⟨exitCallName, towerOfCallName f⟩ ls)))
            (.RSeq (.RCopy ⟨n, towerOfCallName f⟩ ⟨exitCallName, towerOfCallName f⟩) b))) := by
  unfold callHeadT at h
  dsimp only at h
  rcases hm : callMarshal A (towerOfCallName f) args with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
  · cases h
  · simp only at h
    refine ⟨ctx, ls, rfl, ?_⟩
    by_cases hs : exitScalarCall f = true
    · rw [if_pos hs] at h
      split_ifs at h with hn
      simp only [Option.some.injEq] at h
      exact Or.inl ⟨hs, hn, h.symm⟩
    · rw [if_neg hs] at h
      split_ifs at h with hn
      simp only [Option.some.injEq] at h
      exact Or.inr ⟨by simpa using hs, hn, h.symm⟩

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

theorem headT_scalarOp (hL : ExitLeaves bi leafSpec br) {env : Env} {rs : RustState}
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

theorem headT_index (hL : ExitLeaves bi leafSpec br) {env : Env} {rs : RustState}
    {n : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : indexHeadT A n args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi "index" vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨arr, idx, t, rfl, htA, hiA, hnA, rfl⟩ := indexHeadT_some A hk
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
  obtain ⟨vArr, vIdx, rfl, hva, hvi⟩ := forall₂_var2 hF
  obtain ⟨-, arrV, harr, hbr⟩ := envAgreesT_tower hag hargs.1 htA hva
  obtain ⟨-, hdi⟩ := envAgreesT_scalar hag hargs.2.1 hiA hvi
  obtain ⟨hsr, hdr⟩ := hL.index t vArr vIdx r arrV _ hbr hdi hbi
  -- the states: the call slot zeroed, the element loaded, the limb copied
  let D : Located := ⟨exitCallName, .TFp⟩
  let lv := leafSpec.arrLoad D default ⟨t, arrV⟩ (rs.rsScalar idx)
  have harrne : exitCallName ≠ arr := (ne_of_reserved hargs.1 exitReserved_call).symm
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

theorem headT_update (hL : ExitLeaves bi leafSpec br) {env : Env} {rs : RustState}
    {n : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : updateHeadT A n args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi "array_update" vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨arr, idx, src, t, ctx, srcLoc, rfl, hna, htA, hiA, hm, rfl⟩ := updateHeadT_some A hk
  subst hna
  have hargs' := hargs
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs'
  obtain ⟨vArr, vIdx, vSrc, rfl, hva, hvi, hvs⟩ := forall₂_var3 hF
  obtain ⟨-, arrV, harr, hbr⟩ := envAgreesT_tower hag hargs'.1 htA hva
  obtain ⟨-, hdi⟩ := envAgreesT_scalar hag hargs'.2.1 hiA hvi
  have hsrcOk : exitArgsOk [.var src] = true := by
    simp [exitArgsOk, hargs'.2.2.1]
  obtain ⟨rs1, hex, hS1, hT1, -, hF1⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal t.elemType [.var src] ctx [srcLoc] [vSrc] hm hsrcOk
      (List.Forall₂.cons ⟨src, rfl, hvs⟩ List.Forall₂.nil) rs rfl (fun _ _ => rfl)
  have hsl : srcLoc.locSrc = t.elemType :=
    callMarshal_locSrc A t.elemType [.var src] ctx [srcLoc] hm srcLoc (List.mem_singleton_self _)
  rcases hF1 with _ | ⟨⟨sv, hsv, hbs⟩, -⟩
  obtain ⟨sName, sTy⟩ := srcLoc
  simp only at hsl
  subst hsl
  have hbrR := hL.update n t vArr vIdx vSrc r arrV sv (rs.rsScalar idx) hbr
    (fun m hm' => by rw [hdi] at hm'; exact (Option.some.inj hm').symm) hbs hbi
  have harr1 : rs1.rsTower n = some ⟨t, arrV⟩ := by
    rw [hT1 n (ne_marshal_of_nonreserved hargs'.1)]; exact harr
  have hstore : RustExec N leafSpec (.RArrStore ⟨n, t⟩ idx ⟨sName, t.elemType⟩) rs1
      (rsSetTower rs1 n ⟨t, leafSpec.arrStore ⟨n, t⟩ arrV (rs.rsScalar idx)
        ⟨t.elemType, sv⟩⟩) :=
    RustExec.arrStore ⟨n, t⟩ idx ⟨sName, t.elemType⟩ rs1 _ arrV sv (congrFun hS1 idx)
      (locatedLookup_of_rsTower _ _ _ _ harr1) (locatedLookup_of_rsTower _ _ _ _ hsv)
  have hag1 : envAgreesT br A env rs1 :=
    envAgreesT_of_eqOn hS1 (fun y hy => hT1 y (ne_marshal_of_nonreserved hy)) hag
  refine ⟨_, envAgreesT_extend_tower hn htA (hL.plain _ _ _ hbi) hbrR hag1, ?_,
    fun bC rs' h => RustExec.seq _ _ _ _ _ (hex _ _ hstore) h⟩
  show rs1.rsScalar exitRetName = 0
  rw [hS1]; exact hret

theorem headT_call (hL : ExitLeaves bi leafSpec br) {env : Env} {rs : RustState}
    {n f : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : callHeadT A n f args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    (hret : rs.rsScalar exitRetName = 0) :
    HeadResT N leafSpec br A env rs n r k := by
  obtain ⟨ctx, ls, hm, hcase⟩ := callHeadT_some A hk
  let dt := towerOfCallName f
  have hT0 : ∀ y, exitReserved y = false →
      (rsSetTower rs exitCallName ⟨dt, default⟩).rsTower y = rs.rsTower y := fun y hy =>
    CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
      (ne_of_reserved hy exitReserved_call).symm
  obtain ⟨rs1, hex, hS1, hT1, -, hF1⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal dt args ctx ls vals hm hargs hF
      (rsSetTower rs exitCallName ⟨dt, default⟩) rfl hT0
  have hcall1 : rs1.rsTower exitCallName = some ⟨dt, default⟩ := by
    rw [hT1 exitCallName (fun z => exitCallName_ne_marshal z)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  let argList := ls.filterMap fun a => rs1.rsTower a.locVar
  let resV := leafSpec.call f dt (ls.map (·.locDst)) default argList
  have hcall : RustExec N leafSpec (.RCall f ⟨exitCallName, dt⟩ ls) rs1
      (rsSetTower rs1 exitCallName ⟨dt, resV⟩) :=
    RustExec.call f ⟨exitCallName, dt⟩ ls rs1 default argList
      (locatedLookup_of_rsTower _ _ _ _ hcall1) rfl
      (forall₂_rsTower_typed hF1 (callMarshal_locSrc A dt args ctx ls hm))
  have hC : RustExec N leafSpec (.RLetZero exitCallName dt
      (ctx (.RCall f ⟨exitCallName, dt⟩ ls))) rs (rsSetTower rs1 exitCallName ⟨dt, resV⟩) :=
    RustExec.letZero _ _ _ _ _ (hex _ _ hcall)
  have hF2 := forall₂_filterMap_rsTower hF1
  have hag2 : envAgreesT br A env (rsSetTower rs1 exitCallName ⟨dt, resV⟩) :=
    envAgreesT_setTower_reserved _ exitReserved_call
      (envAgreesT_of_eqOn hS1 (fun y hy => by
        rw [hT1 y (ne_marshal_of_nonreserved hy), hT0 y hy]) hag)
  have hret2 : (rsSetTower rs1 exitCallName ⟨dt, resV⟩).rsScalar exitRetName = 0 := by
    show rs1.rsScalar exitRetName = 0
    rw [hS1]; exact hret
  rcases hcase with ⟨hsc, hnA, rfl⟩ | ⟨hsc, hnA, rfl⟩
  · obtain ⟨hsr, hdr⟩ := hL.callS f hsc ls vals argList default r hbi hF2
    have hev : (SExpr.SLimb exitCallName 0).evalState
        (rsSetTower rs1 exitCallName ⟨dt, resV⟩) = towerLimb resV 0 := by
      simp only [SExpr.evalState]
      exact rsTowerLimb_rsSetTower_same _ _ _ _ _
    refine ⟨rsSetScalar (rsSetTower rs1 exitCallName ⟨dt, resV⟩) n (towerLimb resV 0),
      envAgreesT_extend hn hnA hsr hdr hag2, ret_setScalar hn _ hret2, fun bC rs' h => ?_⟩
    have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) n
      (.SLimb exitCallName 0) (rsSetTower rs1 exitCallName ⟨dt, resV⟩)
    rw [hev] at hset
    exact RustExec.seq _ _ _ _ _ hC (RustExec.seq _ _ _ _ _ hset h)
  · have hbrR := hL.callT f hsc ls vals argList default r hbi hF2
    refine ⟨rsSetTower (rsSetTower rs1 exitCallName ⟨dt, resV⟩) n ⟨dt, resV⟩,
      envAgreesT_extend_tower hn hnA (hL.plain _ _ _ hbi) hbrR hag2, hret2,
      fun bC rs' h => ?_⟩
    refine RustExec.seq _ _ _ _ _ hC (RustExec.seq _ _ _ _ _ ?_ h)
    exact RustExec.copy ⟨n, dt⟩ ⟨exitCallName, dt⟩ _ rfl resV
      (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))

theorem head_app (hL : ExitLeaves bi leafSpec br) (n f : String) (args : List ImpExpr)
    (body : ImpExpr) : HeadSimT bi N leafSpec br A R n (.app f args) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitReserved n = false ∧ exitArgsOk args = true := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1, hok.1.1.2⟩)
  obtain ⟨hn, hargs⟩ := hh
  have hk' : appHeadT A n f args = some k := hk
  obtain ⟨vals, r, hF, hbi, hrun'⟩ :=
    letBind_app_inv bi fuel hL.plain n f args body hargs env env' o hrun hval
  suffices hres : HeadResT N leafSpec br A env rs n r k by
    obtain ⟨rs1, hag1, hret1, hex⟩ := hres
    exact ⟨_, rs1, hrun', hag1, hret1, hex⟩
  unfold appHeadT at hk'
  rcases hso : scalarOpHeadT A n f args with _ | se
  · rw [hso] at hk'
    simp only at hk'
    split_ifs at hk' with hfi hfu
    · subst hfi
      exact headT_index hL hk' hn hargs hF hbi hag hret
    · subst hfu
      exact headT_update hL hk' hn hargs hF hbi hag hret
    · exact headT_call hL hk' hn hargs hF hbi hag hret
  · rw [hso] at hk'
    simp only [Option.some.injEq] at hk'
    subst hk'
    exact headT_scalarOp hL hso hn hargs hF hbi hag hret

end Heads

/-! ## §13  The arms without a loop -/

section Arms

variable (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
  (A : ExitTowers) (R : Option TowerType)

theorem exitSimTy_var (x : String) : ExitSimTy bi N leafSpec br A R (.var x) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hx : exitReserved x = false ∧ (tl = true → A.lookup x = R) := by
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
    have hR : R = none := by
      cases fl <;> simpa [exitSimOkT] using hok
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
    have hh : exitLitOk l = true ∧ R = none := by
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
            cases tl <;> simp [haxToLowCTKT, exitStore, hs]
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
      cases tl <;> simp [haxToLowCTKT, exitStore, hs]
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
  rw [haxToLowCTKT_ifThenElse_eq] at hK
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
    rw [haxToLowCTKT_whileFoldReturn_eq] at hK
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
    rw [haxToLowCTKT_forFoldReturn_eq] at hK
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
    rw [haxToLowCTKT_forFoldRevReturn_eq] at hK
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
      rw [haxToLowCTKT_forFold_some_eq] at hK
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
      rw [haxToLowCTKT_whileFold_some_eq] at hK
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
    `ExitLeaves`, every expression of the fragment `exitSimOkT A R` simulates under the
    placement `A`: the lowered command `haxToLowCTKT A` matches every `denote'` run that
    ends in a value. -/
theorem haxToLowCTKT_simulates (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : Option TowerType)
    (hL : ExitLeaves bi leafSpec br) (e : ImpExpr) : ExitSimTy bi N leafSpec br A R e := by
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
        (head_lit bi N leafSpec br A R n l body)
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
  | whileFold c body _ ihb =>
    cases c with
    | var v => exact exitSimTy_whileFold bi N leafSpec br A R v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | cfBreak p _ => exact exitSimTy_cfBreak bi N leafSpec br A R p
  | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)

/-- The value a function returns under the result placement `R`: the payload of an early
    exit decoded in the scalar result slot, or the final value in agreement with the result
    slot of `R` (`resultAgreesT`). -/
def outcomeAgreesT (br : ValueTowerBridge) (R : Option TowerType) : Outcome → RustState → Prop
  | .val (.controlFlow true v), rs => valueToScalar v = some (rs.rsScalar exitResName)
  | .val v, rs => resultAgreesT br R v rs
  | _, _ => False

/-- With a scalar result placement, the result agreement is the decoding of the returned
    or final value in the scalar result slot. -/
theorem outcomeAgreesT_none (br : ValueTowerBridge) (o : Outcome) (rs : RustState) :
    outcomeAgreesT br none o rs ↔ outcomeScalar o = some (rs.rsScalar exitResName) := by
  rcases o with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => cases k <;> exact Iff.rfl
    | _ => exact Iff.rfl
  all_goals simp [outcomeAgreesT, outcomeScalar]

/-- **The function frame under a placement.**  For a function body of the fragment in the
    function context, the frame `exitFunction` around its typed lowering matches every
    `denote'` run that ends in a value, with the result of `outcomeAgreesT`. -/
theorem exitFunctionT_sim (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : Option TowerType) (e : ImpExpr)
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
        exact hw
    | _ => simp at hcf

/-- **Function-level simulation of the typed lowering.**  For a function body in the
    fragment `exitSimOkT A R` with exits allowed at function level, leaf conditions
    `ExitLeaves`, and an entry state agreeing with the entry environment under the
    placement `A`, a `denote'` run ending in a value is matched by the lowered function
    `haxToLowCTFnT A e`, whose result slot agrees with the returned or final value
    (`outcomeAgreesT`). -/
theorem haxToLowCTFnT_simulates_exit (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : Option TowerType)
    (hL : ExitLeaves bi leafSpec br) (e : ImpExpr) (c : LowCT)
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
    (br : ValueTowerBridge) (A : ExitTowers) (hL : ExitLeaves bi leafSpec br)
    (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT A none true true e = true) (hK : haxToLowCTFnT A e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) := by
  obtain ⟨rs', hex, ho⟩ :=
    haxToLowCTFnT_simulates_exit bi N leafSpec br A none hL e c hok hK fuel env env' o rs hrun
      hval hag
  exact ⟨rs', hex, (outcomeAgreesT_none br o rs').mp ho⟩

/-- **The statement of `haxToLowCTFn_simulates_exit` for the typed lowering** at the empty
    placement: from an entry state agreeing with the entry environment off the reserved
    names (`envAgreesOff`), the result slot of `haxToLowCTFnT [] e` holds the decoding of
    the returned or final value. -/
theorem haxToLowCTFnT_nil_simulates_exit (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (hL : ExitLeaves bi leafSpec br) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOkT [] none true true e = true) (hK : haxToLowCTFnT [] e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) :=
  haxToLowCTFnT_simulates_exit_scalar bi N leafSpec br [] hL e c hok hK fuel env env' o rs hrun
    hval (envAgreesT_nil_of_off hag)

end CatCrypt.Crypto.Hax
