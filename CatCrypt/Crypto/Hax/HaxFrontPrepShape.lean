/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxFrontPrep
public import CatCrypt.Crypto.Hax.HaxFrontOracle
public import CatCrypt.Crypto.Hax.ImpToNF
public import HaxLean.Phase.WhileTrueFlag
public import HaxLean.TExpr

/-!
# The shape of a body on which the candidate preparations of the front are the identity

The front offers an acceptance test several rewritings of a body: `wtFn g` (each
`while true` as a loop on the flag `g`), `ere` (function-level early returns moved into
branches) and `tailSome` (a returned binding `let r = Some(x); r` replaced by `Some(x)`).
`prepShapeB` is a Boolean test on `ImpExpr`, the type on which the three rewritings and the
structured translation `impToNF` act. On a body that passes it each rewriting is the
identity, and a body that `impToNF` translates passes it when the signature table types no
call of `"Some"`.

The test follows the statement positions the rewritings visit: the second component of a
`letBind`, both components of a `seq`, the body of a type ascription, the body of a
`forFold` or `forFoldRev` with an integer literal as lower bound, both arms of an
`ifThenElse` and the body of a `whileFold` on a name. The
bound value of a `letBind`, the arguments of a call, the components of a tuple and the
condition of an `ifThenElse` are not visited by any of the three. An arm of the shape has no
function-level return (`hasRet_of_prepShapeB`), so `ere` leaves a conditional of the shape
in place.

## Main definitions

* `prepShapeB` — the shape test
* `shapeAccepts`, `haxFrontShapeOk` — the shape test as the acceptance tests of the front,
  and the side conditions of the front on an extraction under them

## Main results

* `impToNF_prepShapeB`, `impToNF_isSome_prepShapeB` — a body translated by `impToNF`, over
  a signature table without `"Some"`, passes the test
* `wtFn_of_prepShapeB`, `ere_of_prepShapeB`, `tailSome_of_prepShapeB` — the rewritings are
  the identity on a body that passes the test
* `anfEPick_of_prepShapeB` — `anfEPick ok` is the identity on such a body, for every `ok`
* `anfEPick_of_ok` — `anfEPick ok a = a` when `ok a` holds
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr)
open _root_.Hax.EarlyReturnElim (ere ereSeq hasRet)
open _root_.Hax.WhileTrueFlag (wtFn)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF (impToNF Out NfEnv)

/-- The shape test: at the statement positions, the body is built from variables, literals,
    the unit value, assignments, calls, tuples, tuple projections, type ascriptions, `seq`, `letBind` that is
    not a returned `Some` binding (`isSomeRet`), `forFold` and `forFoldRev` with an integer
    literal or a variable as lower bound, `ifThenElse` with both arms of the shape, and
    `whileFold` on a name with a body of the shape. -/
def prepShapeB : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | .unitVal => true
  | .assign _ _ => true
  | .app _ _ => true
  | .tuple _ => true
  | .proj _ _ => true
  | .typeAscription e _ => prepShapeB e
  | .seq a b => prepShapeB a && prepShapeB b
  | .letBind n v b => !isSomeRet n v b && prepShapeB b
  | .forFold _ (.lit (.int _)) _ b => prepShapeB b
  | .forFold _ (.var _) _ b => prepShapeB b
  | .forFoldRev _ (.lit (.int _)) _ b => prepShapeB b
  | .forFoldRev _ (.var _) _ b => prepShapeB b
  | .ifThenElse _ t e => prepShapeB t && prepShapeB e
  | .whileFold (.var _) b => prepShapeB b
  | _ => false

/-! ## The rewritings on a body of the shape -/

/-- A body of the shape has no function-level return. -/
theorem hasRet_of_prepShapeB (e : ImpExpr) (h : prepShapeB e = true) : hasRet e = false := by
  fun_induction prepShapeB e <;> simp_all [hasRet]

/-- A statement without a function-level return, followed by `k`, is `seq a k`. -/
theorem ereSeq_of_hasRet (a k : ImpExpr) (h : hasRet a = false) : ereSeq a k = .seq a k := by
  cases a <;> simp_all [ereSeq, hasRet]

/-- `wtFn g` is the identity on a body of the shape. -/
theorem wtFn_of_prepShapeB (g : String) (e : ImpExpr) (h : prepShapeB e = true) :
    wtFn g e = e := by
  fun_induction prepShapeB e <;> simp_all [wtFn, _root_.Hax.WhileTrueFlag.wtLoop]

/-- `ere` is the identity on a body of the shape. -/
theorem ere_of_prepShapeB (e : ImpExpr) (h : prepShapeB e = true) : ere e = e := by
  fun_induction prepShapeB e <;> simp_all [ere, ereSeq_of_hasRet, hasRet_of_prepShapeB]

/-- `tailSome` is the identity on a body of the shape. -/
theorem tailSome_of_prepShapeB (e : ImpExpr) (h : prepShapeB e = true) : tailSome e = e := by
  fun_induction prepShapeB e <;> simp_all [tailSome]

/-- `anfEPick ok a` is `a` when `ok a` holds. -/
theorem anfEPick_of_ok (ok : ImpExpr → Bool) (a : ImpExpr) (h : ok a = true) :
    anfEPick ok a = a := by
  simp [anfEPick, h]

/-- `anfEPick ok` is the identity on a body of the shape, for every test `ok`. -/
theorem anfEPick_of_prepShapeB (ok : ImpExpr → Bool) (a : ImpExpr) (h : prepShapeB a = true) :
    anfEPick ok a = a := by
  simp [anfEPick, ere_of_prepShapeB a h, tailSome_of_prepShapeB a h]

/-! ## A translated body has the shape -/

/-- `impToNF` translates no call of a name other than `repeat` the signature table does not
    type. -/
theorem impToNF_app_none (sigOf : String → List NfTy → Option NfTy) (f : String)
    (hf : ∀ as, sigOf f as = none) (hr : f ≠ "repeat") (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (args : List ImpExpr) :
    impToNF sigOf tgt σ (.app f args) = none := by
  simp [ImpToNF.impToNF_app_call sigOf tgt σ hr, hf]

/-- **A translated body has the shape.** Over a signature table that types no call of
    `"Some"`, a body that `impToNF` translates passes `prepShapeB`. -/
theorem impToNF_prepShapeB (sigOf : String → List NfTy → Option NfTy)
    (hS : ∀ as, sigOf "Some" as = none) (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ},
      impToNF sigOf tgt σ e = some o → prepShapeB e = true := by
  induction e using ImpExpr.ind
  case letBind x v b ihv ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ov, hov, ob, hob, rfl⟩ := h
    have hb := ihb _ _ hob
    have hs : isSomeRet x v b = false := by
      cases hr : isSomeRet x v b with
      | false => rfl
      | true =>
        unfold isSomeRet at hr
        split at hr
        · rw [impToNF_app_none sigOf "Some" hS (by simp)] at hov
          cases hov
        · cases hr
    simp [prepShapeB, hs, hb]
  case seq a b iha ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
    simp [prepShapeB, iha _ _ hoa, ihb _ _ hob]
  case typeAscription e s ih =>
    intro tgt Γ σ o h
    simp only [impToNF] at h
    simpa [prepShapeB] using ih _ _ h
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, ImpToNF.loopOut, Option.bind_eq_some_iff] at h
    obtain ⟨eLo, hLo, oHi, _, h⟩ := h
    have hb : prepShapeB body = true := by
      split at h
      · obtain ⟨ob, hob, _⟩ := Option.bind_eq_some_iff.mp h
        exact ihb _ _ hob
      · cases h
    cases lo with
    | lit l =>
      cases l with
      | int n => simpa [prepShapeB] using hb
      | _ => simp [ImpToNF.loOut] at hLo
    | var x => simpa [prepShapeB] using hb
    | _ => simp [ImpToNF.loOut] at hLo
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, ImpToNF.loopOut, Option.bind_eq_some_iff] at h
    obtain ⟨eLo, hLo, oHi, _, h⟩ := h
    have hb : prepShapeB body = true := by
      split at h
      · obtain ⟨ob, hob, _⟩ := Option.bind_eq_some_iff.mp h
        exact ihb _ _ hob
      · cases h
    cases lo with
    | lit l =>
      cases l with
      | int n => simpa [prepShapeB] using hb
      | _ => simp [ImpToNF.loOut] at hLo
    | var x => simpa [prepShapeB] using hb
    | _ => simp [ImpToNF.loOut] at hLo
  case ifThenElse c a b _ iha ihb =>
    intro tgt Γ σ o h
    obtain ⟨oc, oa, ob, -, ha, hb⟩ := ImpToNF.impToNF_cond_arms sigOf tgt c a b σ h
    simp [prepShapeB, iha _ _ ha, ihb _ _ hb]
  case whileFold c body _ ihb =>
    intro tgt Γ σ o h
    cases c with
    | var g =>
      simp only [impToNF] at h
      have hc := ImpToNF.whileOut_whileCarry _ _ _ _ _ _ _ h
      simp only [ImpToNF.whileOut, hc, ite_true, Option.bind_eq_some_iff] at h
      obtain ⟨p, -, h⟩ := h
      split at h
      · obtain ⟨ob, hob, -⟩ := Option.bind_eq_some_iff.mp h
        simpa [prepShapeB] using ihb _ _ hob
      · cases h
    | _ => simp [impToNF] at h
  all_goals
    intro tgt Γ σ o h
    first
      | rfl
      | simp [impToNF] at h

/-- The statement of `impToNF_prepShapeB` on `Option.isSome`. -/
theorem impToNF_isSome_prepShapeB (sigOf : String → List NfTy → Option NfTy)
    (hS : ∀ as, sigOf "Some" as = none) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (e : ImpExpr) (h : (impToNF sigOf tgt σ e).isSome = true) :
    prepShapeB e = true := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
  exact impToNF_prepShapeB sigOf hS e tgt σ ho

/-! ## The shape test as the acceptance tests of the front -/

/-- **The acceptance tests of the shape test**: a normal form is taken as it is when it
    passes `prepShapeB`, and the side condition on a body is `prepShapeB`. -/
def shapeAccepts : FrontOracle where
  plain := prepShapeB
  ok := prepShapeB

/-- The side conditions of the front on an extraction under the shape test: `aNormTDenoteOk`
    of the prepared extraction and `prepShapeB` of the form chosen (`haxFrontOkP` at
    `shapeAccepts`). -/
def haxFrontShapeOk (te : _root_.Hax.TExpr) : Bool :=
  haxFrontOkP shapeAccepts te.erase

/-- The side conditions of the front under the shape test hold on an extraction that passes
    `haxFrontShapeOk`. -/
theorem haxFrontOkP_of_shapeOk {te : _root_.Hax.TExpr} (h : haxFrontShapeOk te = true) :
    haxFrontOkP shapeAccepts te.erase = true :=
  h

end CatCrypt.Crypto.Hax
