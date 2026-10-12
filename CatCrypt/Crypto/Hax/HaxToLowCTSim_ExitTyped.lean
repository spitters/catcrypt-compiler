/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTypedLoops

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
  the exit-flag loop followed by `breakLoop`, whether its body breaks or not; an upward
  loop whose bounds are not literals reads them at run time (`forBoundsV`): the lower
  bound a literal or a scalar variable the body does not bind, the upper bound a scalar
  expression of `boundSE` (literals, scalar variables and the operations of
  `scalarOpExprT`), and the trip count `hi - lo` is read on entry (`exitForLoopV`);
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

## Parts

The development is split into four modules, each importing its predecessor:

* `HaxToLowCTSim_ExitTypedDefs` (§1–§6): placements and reserved tower slots, scalar
  operations, the heads of a `letBind`, the translator, placement inference and the fragment;
* `HaxToLowCTSim_ExitTypedSteps` (§7–§12): agreement under a placement, scalar operations
  and leaf conditions, source steps, the simulation statement and the translator's
  equations, marshalling of call arguments, and the heads of a `letBind`;
* `HaxToLowCTSim_ExitTypedLoops` (§13–§14): the arms without a loop, and the loops;
* this module (§15 onward): the simulation theorems, the scalar operations of hax-lean's
  `u64` table (`hax64_named_sound`), and the calls of lowered callees.

## Main definitions

* `ExitTowers`, `exitCallName`, `exitMarshalName`
* `scalarOpExprT`, `WidthOp`, `widthOpOf`
* `exitWordTower`, `exitElemTower`, `exitContainer`, `exitElem`, `exitMarshalOk`
* `exitCallKey`, `exitCallTys`, `exitArrLen`
* `callMarshal`, `callHeadAt`, `callHeadT`, `arrLitHeadN`, `letHeadT`, `haxToLowCTKT`,
  `haxToLowCTFnT`, `haxToLowCTFnI`
* `boundSE`, `loBoundSE`, `forBoundsV`, `exitForTripV`, `exitForLoopV`, `forBoundsOkT`
* `exitTowerNames`, `exitTowers`, `exitResultPlace`
* `exitSimOkT`, `exitSimWhyT`
* `envAgreesT`, `envAgreesExitT`, `ExitSimTy`, `ExitLeaves`, `exitRange`

## Main results

* `callMarshal_sim`: the marshalling of call arguments into tower slots
* `head_lit`, `head_var`, `headT_app`, `head_app`: the heads of a `letBind`
* `boundSE_sim`: a bound of `boundSE` evaluates, without changing the environment, to a
  scalar word decoding to its scalar expression
* `exitForLoopVT_sim`, `breakForLoopVT_sim`: the counted loops with bounds read at run time
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

open CatCrypt.Crypto.Jasmin.LowCT (rsSetTower locatedLookup locatedUpdate RustVal towerLimb
  rsTowerLimb)

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
    exact exitSimTy_forFoldReturn bi N leafSpec br A R hL.ops i lo hi body ihb
  | forFoldRevReturn i lo hi body _ _ ihb =>
    exact exitSimTy_forFoldRevReturn bi N leafSpec br A R i lo hi body ihb
  | forFold i lo hi body _ _ ihb =>
    exact exitSimTy_forFold bi N leafSpec br A R hL.ops i lo hi body ihb
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
  have hb : b % 2 ^ 2 ^ k < 2 ^ 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
  congr 1
  omega

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

/-- An operation of `scalarOpExprT` is one of its twenty named operations, one of the four
    Boolean connectives, or a name of `widthOpOf`. -/
theorem scalarOpExprT_isSome_cases {op : String} {a b : SExpr}
    (h : (scalarOpExprT op a b).isSome = true) :
    op ∈ ["lt", "Lt", "gt", "Gt", "le", "Le", "ge", "Ge", "eq", "Eq", "ne", "Ne", "add", "Add",
      "Add#64", "Add#size", "sub", "Sub", "Sub#64", "Sub#size"] ∨ op ∈ ["&&", "and", "||", "or"] ∨ ∃ p, widthOpOf op = some p := by
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

/-- The twenty named operations of `scalarOpExprT` in `hax64Builtins`: the condition of
    `ScalarOpsSoundT`.  The comparisons are defined on two integers (and `eq`, `Eq`, `ne`,
    `Ne` on two Booleans), the checked additions `add`, `Add`, `Add#64`, `Add#size` and
    subtractions `sub`, `Sub`, `Sub#64`, `Sub#size` on two integer words. -/
theorem hax64_named_sound {op : String} {va vb r : Value} {na nb : Nat}
    (hl : op ∈ ["lt", "Lt", "gt", "Gt", "le", "Le", "ge", "Ge", "eq", "Eq", "ne", "Ne", "add",
      "Add", "Add#64", "Add#size", "sub", "Sub", "Sub#64", "Sub#size"])
    (hva : ScalarValN va) (hvb : ScalarValN vb)
    (hna : valueToScalar va = some na) (hnb : valueToScalar vb = some nb)
    (hbi : hax64Builtins op [va, vb] = some r) :
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT op na nb) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  -- `Add#64`
  · exact hax64_scalarOp_int (F := fun n m => n + m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => x + y < 2 ^ 64)
        (fun a b => (_root_.Hax.hax64WordOps_add64_eq_Add (a := a) (b := b)).trans
          (_root_.Hax.hax64WordOps_add a b)) (fun _ _ => rfl)
        (fun _ _ _ _ h => h))
  -- `Add#size`
  · exact hax64_scalarOp_int (F := fun n m => n + m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => x + y < 2 ^ 64)
        (fun a b => (_root_.Hax.hax64WordOps_addSize_eq_Add (a := a) (b := b)).trans
          (_root_.Hax.hax64WordOps_add a b)) (fun _ _ => rfl)
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
  -- `Sub#64`
  · exact hax64_scalarOp_int (F := fun n m => n - m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => y ≤ x)
        (fun a b => (_root_.Hax.hax64WordOps_sub64_eq_Sub (a := a) (b := b)).trans
          (_root_.Hax.hax64WordOps_Sub a b)) (fun _ _ => rfl)
        (fun _ _ hn _ _ => by omega))
  -- `Sub#size`
  · exact hax64_scalarOp_int (F := fun n m => n - m) hbi ha0 ha hb0 hb hna hnb
      (fun _ _ => rfl) (hax64Builtins_checked (P := fun x y => y ≤ x)
        (fun a b => (_root_.Hax.hax64WordOps_subSize_eq_Sub (a := a) (b := b)).trans
          (_root_.Hax.hax64WordOps_Sub a b)) (fun _ _ => rfl)
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
    `Shr#w` undefined for an amount of `w` or more); `Add`, `add`, `Add#64`, `Add#size`
    (undefined when the sum reaches `2^64`); `Sub`, `sub`, `Sub#64`, `Sub#size` (undefined
    when the subtrahend exceeds the minuend); the
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
  callS f hf ha := by
    have hne : f ≠ g := by rintro rfl; rw [hSg] at hf; cases hf
    exact leafCallScalar_callee_ne hne (hL.callS f hf ha)
  callTS f hf ha := by
    have hne : f ≠ g := by rintro rfl; rw [hTSg] at hf; cases hf
    exact leafCallScalar_callee_ne hne (hL.callTS f hf ha)
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
