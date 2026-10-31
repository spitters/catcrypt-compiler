/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
public import CatCrypt.Crypto.Hax.Hax64Table
public import CatCrypt.Crypto.Hax.HaxFrontOracle
public import CatCrypt.Crypto.Hax.HaxFrontPrepShape
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
public import HaxLean.Secrecy
public import CatCrypt.Crypto.Hax.FrontOps

/-!
# The front of the hax compiler through `NFProg`

The front half of the hax compiler on the direct route, `NFChain.nfFront`, is the source
program `nfSrcProg σ te` followed by the chain of passes `nfChain`. This module holds the
part before the chain: `nfSrcProg σ te` is the body `nfBody te` the front prepares
from `te` (`haxFrontBodyP` under the shape test `shapeAccepts`), translated by `ImpToNF.impToNF` at the call typing
`hax64SigOf` from the parameters `abiEntry σ` of the layout. `outTyB` is the check of a
result type the back half reads back, the first step of the chain. `nfAbiNames fname σ` are
the export names of the route program: the output array the result kind of `σ` names, the
other array parameters, and the registers of the parameters.

`nfSrcProg_sound` is the part of the leg of the front before the chain: from every
environment `σ` reads off an entry state, a run of the source reading of `te` to a value
that is not a control-flow value is matched by a run of the source program at a valuation
of the parameters whose encodings the environment holds.

## Main definitions

* `nfBody`, `nfCtx`, `outTyB` — the body the front prepares, the context of the route
  program, and the check of a result type.
* `nfSrcProg`, `nfAbiNames` — the source program of the front, and its export names.
* `abiResTy`, `crateFnOfAbi`, `crateArrOk`, `nfSrcProgC` — the result type a layout declares,
  a function of a crate as a callee, the check that no callee has an array-operation name, and
  the source program of the front at the call typing with the callees.
* `tailVar` — the variable an expression ends by reading, such as the `&mut` parameter at the
  end of an in-place function.
* `nfCatCom`, `nfLabels`, `nfFrontCT` — the straight-line program of `catCryptDialect` the
  front translates a body to, the labels of its parameters from a secrecy record, and its
  level check `catLevelCheck`.

## Main results

* `haxFrontBodyP_run_rel` — the prepared body runs to a value related to the source outcome
  by `RetRel`.
* `haxFrontBodyP_shapeAccepts`, `haxFrontOkP_shapeAccepts`, `haxFrontShape_of_impToNF` — when
  the body under acceptance tests `O` passes `prepShapeB` (as a body `impToNF` translates
  does), the body and the side conditions under `shapeAccepts` are those under `O`.
* `hax64WExit_subTable` — the table `hax64WExit` agrees with the `u64` table at the calls
  the translation to `catCryptDialect` admits.
* `nfSrcProg_sound` — a source run is matched by a run of the source program.
* `arrayOps_crateBi`, `nfSrcProgC_sound` — the builtins with the callees keep the array
  operations, and a source run with the callees is matched by a run of the source program
  with the callees.
* `nfBody_prepSim`, `nfSrcProgT_sound` — the body of the front keeps the runs of an accepted
  extraction, and the soundness of the source program with the callees holds at every typed
  table with the array operations.
* `tailVar_denote'`, `tailVar_denoteSpine` — the value of a run of an expression ending in a
  variable is the final binding of the variable: the result of an in-place function is the
  final value of its `&mut` parameter.
* `nfFrontCT_sound` — an accepted body translates to a straight-line program that is
  constant time (`catCT`) for the labels of its parameters.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr TExpr Env Outcome Builtins denote')
open _root_.Hax.InlineLocalClosures (denoteSpine IsErr)
open _root_.Hax.InlineMap (ArrayOps)
open _root_.Hax.WhileTrueFlag (wtFn wtOk wtFn_run_same)
open _root_.Hax.EarlyReturnElim (RetRel)

/-- **The body of the front runs, with the outcome relation.** For every pair of acceptance
    tests `O`, under `haxFrontOkP O e`, a run of the source reading `denoteSpine bi fuel e`
    from `env` to a value is matched by a run, at some fuel, of the body `haxFrontBodyP O e`
    from `env` to a value `v₂` related to the source outcome by `RetRel`. -/
theorem haxFrontBodyP_run_rel (O : FrontOracle) (bi : Builtins) (hbi : ArrayOps bi)
    (e : ImpExpr) (hok : haxFrontOkP O e = true) (fuel : Nat) (env env' : Env) (o : Outcome)
    (hrun : (denoteSpine bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v) :
    ∃ fuel' v₂ s₂, (denote' bi fuel' (haxFrontBodyP O e)).run env = (.val v₂, s₂) ∧
      RetRel o (.val v₂) := by
  have ho : ¬ IsErr o := by
    rintro ⟨m, rfl⟩; obtain ⟨v, hv⟩ := hval; cases hv
  unfold haxFrontOkP at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hanfOk, hok⟩ := hok
  have hanf := anfSoundAt_of_aNormTDenoteOk bi (haxFrontPrep e) env hanfOk
  obtain ⟨s, hs'⟩ := haxFrontPrep_refines bi fuel hbi e env env' o hrun ho
  obtain ⟨fuel', env'', ha⟩ := hanf fuel o s hs' hval
  change (denote' bi fuel' (haxFrontAnf e)).run env = (o, env'') at ha
  rw [← repeatCountInline_denote bi fuel' (haxFrontAnf e)] at ha
  obtain ⟨o2, s2, ha2, hrel⟩ :=
    anfEPick_run bi fuel' (haxFrontRouteOkP O) _ env env'' o ha hval
  change (denote' bi fuel' (haxFrontAnfEP O e)).run env = (o2, s2) at ha2
  obtain ⟨v₂, rfl⟩ : ∃ v, o2 = .val v := by
    rcases hrel with rfl | ⟨v, -, -, rfl⟩
    · exact hval
    · exact ⟨v, rfl⟩
  unfold haxFrontRouteOkP at hok
  cases hF : O.plain (haxFrontAnfEP O e) with
  | true =>
    have hB : haxFrontBodyP O e = haxFrontAnfEP O e := by simp [haxFrontBodyP, hF]
    rw [hB]
    exact ⟨fuel', v₂, s2, ha2, hrel⟩
  | false =>
    simp only [hF, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hok
    have hB : haxFrontBodyP O e = wtFn haxFrontFlag (haxFrontAnfEP O e) := by
      simp [haxFrontBodyP, hF]
    rw [hB]
    have hsame := wtFn_run_same (bi := bi) hok.1 fuel' env
    exact ⟨fuel', v₂, ((denote' bi fuel' (wtFn haxFrontFlag (haxFrontAnfEP O e))).run env).2,
      Prod.ext (by rw [hsame, ha2]) rfl, hrel⟩

/-! ## The shape test as the acceptance tests of the front -/

/-- `wtFn g` is the identity on an expression without `whileFold` and `whileFoldReturn`. -/
theorem wtFn_of_whileFoldFree (g : String) (e : ImpExpr)
    (h : ImpToNF.whileFoldFree e = true) : wtFn g e = e := by
  fun_induction wtFn g e <;> simp_all [ImpToNF.whileFoldFree]

/-- `ereSeq a k` has no `whileFold` when `a` and `k` have none. -/
theorem whileFoldFree_ereSeq (a k : ImpExpr) (ha : ImpToNF.whileFoldFree a = true)
    (hk : ImpToNF.whileFoldFree k = true) :
    ImpToNF.whileFoldFree (_root_.Hax.EarlyReturnElim.ereSeq a k) = true := by
  fun_induction _root_.Hax.EarlyReturnElim.ereSeq a k <;> simp_all [ImpToNF.whileFoldFree]

/-- `ere` keeps an expression without `whileFold` without one. -/
theorem whileFoldFree_ere (e : ImpExpr) (h : ImpToNF.whileFoldFree e = true) :
    ImpToNF.whileFoldFree (_root_.Hax.EarlyReturnElim.ere e) = true := by
  fun_induction _root_.Hax.EarlyReturnElim.ere e <;>
    simp_all [ImpToNF.whileFoldFree, whileFoldFree_ereSeq]

/-- `tailSome` keeps an expression without `whileFold` without one. -/
theorem whileFoldFree_tailSome (e : ImpExpr) (h : ImpToNF.whileFoldFree e = true) :
    ImpToNF.whileFoldFree (tailSome e) = true := by
  fun_induction tailSome e <;> simp_all [ImpToNF.whileFoldFree]

/-- The side conditions of step 5 under `shapeAccepts` are `prepShapeB` on a normal form
    without `whileFold`. -/
theorem haxFrontRouteOkP_shapeAccepts (a : ImpExpr) (hw : ImpToNF.whileFoldFree a = true) :
    haxFrontRouteOkP shapeAccepts a = prepShapeB a := by
  unfold haxFrontRouteOkP
  rw [wtFn_of_whileFoldFree _ a hw]
  cases h : prepShapeB a <;> simp [shapeAccepts, h]

/-- On a normal form `c` without `whileFold`, `anfEPick` under the side conditions of step 5
    at `shapeAccepts` is `anfEPick prepShapeB`. -/
theorem anfEPick_routeOk_shapeAccepts (c : ImpExpr) (hw : ImpToNF.whileFoldFree c = true) :
    anfEPick (haxFrontRouteOkP shapeAccepts) c = anfEPick prepShapeB c := by
  have he := whileFoldFree_ere c hw
  unfold anfEPick
  rw [haxFrontRouteOkP_shapeAccepts c hw, haxFrontRouteOkP_shapeAccepts _ he]

/-- Every form `anfEPick` chooses from a normal form without `whileFold` has none. -/
theorem whileFoldFree_anfEPick (ok : ImpExpr → Bool) (c : ImpExpr)
    (hw : ImpToNF.whileFoldFree c = true) : ImpToNF.whileFoldFree (anfEPick ok c) = true := by
  unfold anfEPick
  split
  · exact hw
  · split
    · exact whileFoldFree_ere c hw
    · exact whileFoldFree_tailSome _ (whileFoldFree_ere c hw)

/-- When the form `anfEPick ok` chooses passes `prepShapeB`, `anfEPick prepShapeB` chooses
    the same form. -/
theorem anfEPick_prepShapeB (ok : ImpExpr → Bool) (c : ImpExpr)
    (h : prepShapeB (anfEPick ok c) = true) : anfEPick prepShapeB c = anfEPick ok c := by
  cases hc : prepShapeB c with
  | true => rw [anfEPick_of_prepShapeB _ c hc, anfEPick_of_prepShapeB _ c hc]
  | false =>
    cases he : prepShapeB (_root_.Hax.EarlyReturnElim.ere c) with
    | true =>
      have hl : anfEPick prepShapeB c = _root_.Hax.EarlyReturnElim.ere c := by
        simp [anfEPick, hc, he]
      rw [hl]
      unfold anfEPick at h ⊢
      by_cases h1 : ok c = true
      · rw [ite_eq_left h1, hc] at h; cases h
      · rw [ite_eq_right h1]
        by_cases h2 : ok (_root_.Hax.EarlyReturnElim.ere c) = true
        · rw [ite_eq_left h2]
        · rw [ite_eq_right h2]
          exact (tailSome_of_prepShapeB _ he).symm
    | false =>
      have hl : anfEPick prepShapeB c = tailSome (_root_.Hax.EarlyReturnElim.ere c) := by
        simp [anfEPick, hc, he]
      rw [hl]
      unfold anfEPick at h ⊢
      by_cases h1 : ok c = true
      · rw [ite_eq_left h1, hc] at h; cases h
      · rw [ite_eq_right h1] at h ⊢
        by_cases h2 : ok (_root_.Hax.EarlyReturnElim.ere c) = true
        · rw [ite_eq_left h2, he] at h; cases h
        · rw [ite_eq_right h2]

/-- The body of the front is the form `anfEPick` chooses when that form has the shape,
    whatever `O.plain` answers on it. -/
theorem haxFrontBodyP_of_anfEP_prepShapeB (O : FrontOracle) (e : ImpExpr)
    (h : prepShapeB (haxFrontAnfEP O e) = true) : haxFrontBodyP O e = haxFrontAnfEP O e := by
  unfold haxFrontBodyP
  simp only [wtFn_of_prepShapeB haxFrontFlag _ h, ite_self]

/-- The form `anfEPick` chooses under `O` has no `whileFold` when the normal form has none. -/
theorem whileFoldFree_haxFrontAnfEP (O : FrontOracle) (e : ImpExpr)
    (hc : ImpToNF.whileFoldFree (repeatCountInline (haxFrontAnf e)) = true) :
    ImpToNF.whileFoldFree (haxFrontAnfEP O e) = true :=
  whileFoldFree_anfEPick _ _ hc

/-- When the body of the front under `O` passes `prepShapeB`, so does the form `anfEPick`
    chooses under `O`, on a normal form without `whileFold`. -/
theorem haxFrontAnfEP_prepShapeB_of_body (O : FrontOracle) (e : ImpExpr)
    (hc : ImpToNF.whileFoldFree (repeatCountInline (haxFrontAnf e)) = true)
    (h : prepShapeB (haxFrontBodyP O e) = true) : prepShapeB (haxFrontAnfEP O e) = true := by
  unfold haxFrontBodyP at h
  dsimp only at h
  split at h
  · exact h
  · rwa [wtFn_of_whileFoldFree _ _ (whileFoldFree_haxFrontAnfEP O e hc)] at h

/-- When the body of the front under `O` passes `prepShapeB`, the form chosen under
    `shapeAccepts` is the form chosen under `O`, on a normal form without `whileFold`. -/
theorem haxFrontAnfEP_shapeAccepts (O : FrontOracle) (e : ImpExpr)
    (hc : ImpToNF.whileFoldFree (repeatCountInline (haxFrontAnf e)) = true)
    (h : prepShapeB (haxFrontBodyP O e) = true) :
    haxFrontAnfEP shapeAccepts e = haxFrontAnfEP O e := by
  have ha := haxFrontAnfEP_prepShapeB_of_body O e hc h
  unfold haxFrontAnfEP at ha ⊢
  rw [anfEPick_routeOk_shapeAccepts _ hc]
  exact anfEPick_prepShapeB _ _ ha

/-- **The body under the shape test is the body under any acceptance tests that pass the
    shape test.** When the normal form has no `whileFold` and the body of the front under `O`
    passes `prepShapeB`, the body under `shapeAccepts` is that body. -/
theorem haxFrontBodyP_shapeAccepts (O : FrontOracle) (e : ImpExpr)
    (hc : ImpToNF.whileFoldFree (repeatCountInline (haxFrontAnf e)) = true)
    (h : prepShapeB (haxFrontBodyP O e) = true) :
    haxFrontBodyP shapeAccepts e = haxFrontBodyP O e := by
  have ha := haxFrontAnfEP_prepShapeB_of_body O e hc h
  have hA := haxFrontAnfEP_shapeAccepts O e hc h
  rw [haxFrontBodyP_of_anfEP_prepShapeB O e ha,
    haxFrontBodyP_of_anfEP_prepShapeB shapeAccepts e (by rw [hA]; exact ha), hA]

/-- **The side conditions under the shape test follow from those under any acceptance tests
    whose body passes the shape test**, on a normal form without `whileFold`. -/
theorem haxFrontOkP_shapeAccepts (O : FrontOracle) (e : ImpExpr)
    (hc : ImpToNF.whileFoldFree (repeatCountInline (haxFrontAnf e)) = true)
    (hok : haxFrontOkP O e = true) (h : prepShapeB (haxFrontBodyP O e) = true) :
    haxFrontOkP shapeAccepts e = true := by
  unfold haxFrontOkP at hok ⊢
  simp only [Bool.and_eq_true] at hok ⊢
  refine ⟨hok.1, ?_⟩
  rw [haxFrontAnfEP_shapeAccepts O e hc h,
    haxFrontRouteOkP_shapeAccepts _ (whileFoldFree_haxFrontAnfEP O e hc)]
  exact haxFrontAnfEP_prepShapeB_of_body O e hc h

/-- **A body translated by `impToNF` is the body under the shape test.** For acceptance tests
    `O` with `haxFrontOkP O e`, a normal form without `whileFold`, and a call typing without
    `"Some"` at which `impToNF` translates the body `haxFrontBodyP O e`, the side conditions
    hold under `shapeAccepts` and the body under `shapeAccepts` is `haxFrontBodyP O e`. -/
theorem haxFrontShape_of_impToNF (O : FrontOracle)
    (sigOf : String → List CatCrypt.Crypto.SecureCompilation.VIR.NFDialect.NfTy →
      Option CatCrypt.Crypto.SecureCompilation.VIR.NFDialect.NfTy)
    (hS : ∀ as, sigOf "Some" as = none) (e : ImpExpr) (tgt : Option String)
    {Γ : CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
      CatCrypt.Crypto.SecureCompilation.VIR.NFDialect.nfDialect}
    (σ : ImpToNF.NfEnv Γ) {o : ImpToNF.Out Γ} (hok : haxFrontOkP O e = true)
    (hc : ImpToNF.whileFoldFree (repeatCountInline (haxFrontAnf e)) = true)
    (h : ImpToNF.impToNF sigOf tgt σ (haxFrontBodyP O e) = some o) :
    haxFrontOkP shapeAccepts e = true ∧ haxFrontBodyP shapeAccepts e = haxFrontBodyP O e := by
  have hs := impToNF_prepShapeB sigOf hS _ tgt σ h
  exact ⟨haxFrontOkP_shapeAccepts O e hc hok hs, haxFrontBodyP_shapeAccepts O e hc hs⟩

/-- **The table `hax64WExit` at the calls of the translation.** At the names `CatName` the
    translation to `catCryptDialect` admits, `hax64WExit` returns only values the `u64` table
    returns. -/
theorem hax64WExit_subTable : NFToCat.SubTable hax64WExit := by
  intro f vals v hf hv
  by_cases hl : f = "array_lit"
  · subst hl
    unfold hax64WExit at hv
    rw [ite_eq_left rfl] at hv
    split at hv
    · cases hv
      exact ImpToNF.withSelect_hax64Builtins_of_base rfl
    · cases hv
  have hn : f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" := by
    rcases hf with hm | rfl | rfl | rfl | rfl | rfl
    · exact ImpToNF.hax64NFScalar_ne_arr hm
    all_goals first | decide | exact absurd rfl hl
  by_cases hw : hax64WideHead f
  · rw [hax64WExit_wide hw] at hv
    exact ImpToNF.withSelect_hax64Builtins_of_base hv
  rw [hax64WExit_of_ne hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 hw] at hv
  exact ImpToNF.withSelect_hax64Builtins_of_base (hax64Exit_sub hv)

end CatCrypt.Crypto.Hax

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnv EntryVals EntryTyped impToNF hax64SigOf
  entryVals_of_typed impToNF_sound entryEnv_rel PDenP PDenP_plug_ret tableOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open Ctxt (Var Valuation)
open _root_.Hax (TExpr ImpExpr Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)

/-- The body the front prepares from `te` under the shape test `shapeAccepts`. -/
def nfBody (te : TExpr) : ImpExpr :=
  CatCrypt.Crypto.Hax.haxFrontBodyP CatCrypt.Crypto.Hax.shapeAccepts te.erase

/-- The context of the route program of the direct route under the layout `σ`. -/
abbrev nfCtx (σ : AbiLayout) : Ctxt jasminDialect :=
  mapCtx ((entryCtx (abiEntry σ)).map catTy)

/-- The check of a result type the back half reads back: a word, an integer or an array of
    words. -/
def outTyB : NfTy → Bool
  | .word _ => true
  | .int => true
  | .arr _ (.word _) => true
  | _ => false

theorem outTy_of_outTyB (t : NfTy) (h : outTyB t = true) : OutTy t := by
  cases t with
  | arr n s => cases s <;> first | exact True.intro | simp [outTyB] at h
  | _ => first | exact True.intro | simp [outTyB] at h

/-- **The source program of the front**: the body `nfBody te`, under the side conditions
    `haxFrontShapeOk`, translated to `NFProg nfDialect` by `impToNF` from the parameters
    `abiEntry σ`, with the type of its result. -/
def nfSrcProg (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  if CatCrypt.Crypto.Hax.haxFrontShapeOk te = true then
    (impToNF hax64SigOf none (entryEnv (abiEntry σ)) (nfBody te)).map fun o => ⟨o.t, o.prog⟩
  else none

/-- The slot of the array parameter the result kind of `σ` names. -/
def nfOutIdx (σ : AbiLayout) : Option Nat :=
  match σ.result with
  | .words r k =>
      (σ.args.zipIdx.find? fun q => q.1.reg == r && q.1.kind == .words k).map (·.2)
  | _ => none

/-- **The export names of the direct route**: the function symbol `fname`, the output array
    the result kind of `σ` names, the other array parameters, and the export registers of the
    parameters. -/
def nfAbiNames (fname : String) (σ : AbiLayout) : AbiNames where
  fname := fname
  outArg := ((nfOutIdx σ).map JasminLprogExport.argName).getD ""
  inArgs := σ.args.zipIdx.filterMap fun q =>
    match q.1.kind with
    | .words _ => if nfOutIdx σ = some q.2 then none else some (JasminLprogExport.argName q.2)
    | .scalar => none
  abiArgs := σ.args.map fun a => exportReg a.reg

/-- An environment the layout reads off an entry state is typed at the parameters
    `abiEntry σ`. -/
theorem entryTyped_abiEntry {σ : AbiLayout} {sa : Ascent.AddrMem.AState} {env : Env}
    (h : σ.EnvOf sa env) : EntryTyped env (abiEntry σ) := fun x t hm =>
  entryTyped_of_envOf_arr h x t (List.mem_reverse.mp hm)

/-- **Soundness of the source program of the front.** For `nfSrcProg σ te = some q`, from
    every environment `σ` reads off an entry state, a run of the source reading of `te` to a
    value `v` that is not a control-flow value gives a valuation `V` of the parameters whose
    encodings the environment holds, at which `q.2` denotes, at every fuel from some fuel on,
    a value `y` whose encoding is `v`. -/
theorem nfSrcProg_sound {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProg σ te = some q) {sa : Ascent.AddrMem.AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine CatCrypt.Crypto.Hax.hax64WExit fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote), EntryVals env (abiEntry σ) V ∧
      (∃ N, ∀ tf, N ≤ tf →
        PDenP CatCrypt.Crypto.Hax.hax64WExit tf q.2 V = some (HVector.cons y .nil)) ∧
        v = CatCrypt.Crypto.Hax.ImpToNF.enc q.1 y := by
  unfold nfSrcProg at hq
  split at hq
  · rename_i hok
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨fuel', v₂, s₂, hb, hrel⟩ := CatCrypt.Crypto.Hax.haxFrontBodyP_run_rel
      CatCrypt.Crypto.Hax.shapeAccepts
      CatCrypt.Crypto.Hax.hax64WExit CatCrypt.Crypto.Hax.arrayOps_hax64WExit te.erase
      (CatCrypt.Crypto.Hax.haxFrontOkP_of_shapeOk hok) fuel env env' (.val v) hrun
      ⟨v, rfl⟩
    have hv2 : v₂ = v := by
      rcases hrel with h | ⟨w, -, h, -⟩
      · exact _root_.Hax.Outcome.val.inj h
      · obtain rfl := _root_.Hax.Outcome.val.inj h
        simp [Value.isControlFlow] at hcf
    subst hv2
    obtain ⟨V, hV⟩ := entryVals_of_typed (entryTyped_abiEntry henv)
    obtain ⟨W, ⟨N, hN⟩, -, hvW⟩ := (impToNF_sound CatCrypt.Crypto.Hax.hax64WExit
        hax64SigOf CatCrypt.Crypto.Hax.hax64WExit_typedCalls
        CatCrypt.Crypto.Hax.repeatCalls_hax64WExit (nfBody te) none
        (entryEnv (abiEntry σ)) ho fuel').ev (entryEnv_rel hV) hb
    exact ⟨V, o.res.lookup W, hV, ⟨N, fun tf htf =>
      CatCrypt.Crypto.Hax.ImpToNF.PDenP_plug_ret _ tf o.pre _ V (hN tf htf)⟩, hvW⟩
  · cases hq

/-! ## Calls of the functions of a crate -/

open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf crateBi crateBi_of_find_none
  crateBi_typedCalls paramsEnv dec)
open _root_.Hax (Builtins)
open _root_.Hax.InlineMap (ArrayOps)

/-- The result type a System V layout declares: a `64`-bit word for a result in a register,
    an array of `n` `64`-bit words for `n` words read back at a pointer. -/
def abiResTy (σ : AbiLayout) : Option NfTy :=
  match σ.result with
  | .reg _ => some (.word 64)
  | .words _ n => some (.arr n (.word 64))
  | _ => none

/-- The callee of the function `name` with the layout `σ` and the extraction `te`: the
    parameters `abiParamsArr σ`, in the order of `σ.args` (the declaration order, in which a
    call passes its arguments), the result type `abiResTy σ`, and the body `nfBody te`. -/
def crateFnOfAbi (name : String) (σ : AbiLayout) (te : TExpr) : Option CrateFn :=
  (abiResTy σ).map fun r => ⟨name, abiParamsArr σ, r, nfBody te⟩

/-- The parameter names of the callee `crateFnOfAbi name σ te` are the names of `σ.args`, in
    the order of `σ.args`. -/
theorem crateFnOfAbi_params {name : String} {σ : AbiLayout} {te : TExpr} {c : CrateFn}
    (hc : crateFnOfAbi name σ te = some c) :
    c.params.map (·.1) = σ.args.map (·.name) ∧ c.body = nfBody te := by
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact ⟨by simp [abiParamsArr], rfl⟩

/-- **A call of a callee made from a layout binds the parameters in declaration order.** When
    the function of `fs` named `f` is `crateFnOfAbi name σ te`, a call of `f` at depth `n + 1`
    on the values `vals` runs `nfBody te` from the environment `paramsEnv` binding the names of
    `σ.args` to `vals` position by position. -/
theorem crateBi_crateFnOfAbi {fs : List CrateFn} {f name : String} {σ : AbiLayout}
    {te : TExpr} {c : CrateFn} (hf : fs.find? (·.name == f) = some c)
    (hc : crateFnOfAbi name σ te = some c) (bi : Builtins) (fuel n : Nat) (vals : List Value) :
    crateBi fs bi fuel (n + 1) f vals =
      match ((_root_.Hax.denote' (crateBi fs bi fuel n) fuel (nfBody te)).run
          (paramsEnv (σ.args.map (·.name)) vals)).1 with
      | .val v => if (dec c.res v).isSome then some v else none
      | _ => none := by
  obtain ⟨hp, hb⟩ := crateFnOfAbi_params hc
  simp only [crateBi, hf, hp, hb]
  rfl

/-- The environment of a call binds the first parameter of a layout to the first argument:
    with `crateBi_crateFnOfAbi`, a call `f(x, y)` of a callee made from a layout whose first
    parameter is `a` runs the body with `a` bound to `x`. -/
theorem paramsEnv_abi_head (a : AbiArg) (as : List AbiArg) (v : Value) (vs : List Value) :
    paramsEnv ((a :: as).map (·.name)) (v :: vs) a.name = some v := by
  simp [paramsEnv]

/-- The environment of a call binds the second parameter of a layout to the second argument,
    when its name differs from the name of the first. -/
theorem paramsEnv_abi_snd (a b : AbiArg) (as : List AbiArg) (h : b.name ≠ a.name)
    (v w : Value) (vs : List Value) :
    paramsEnv ((a :: b :: as).map (·.name)) (v :: w :: vs) b.name = some w := by
  simp [paramsEnv, h]

/-- No function of `fs` has the name of an array operation (`len`, `index`, `array_update`,
    `repeat`). -/
def crateArrOk (fs : List CrateFn) : Bool :=
  ["len", "index", "array_update", "repeat"].all fun g => (fs.find? (·.name == g)).isNone

/-- No function of a crate `crateArrOk` accepts is named `repeat`. -/
theorem crateArrOk_find_repeat {fs : List CrateFn} (h : crateArrOk fs = true) :
    fs.find? (·.name == "repeat") = none := by
  simp only [crateArrOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  exact h.2.2.2

/-- The array operations of `bi` are those of the builtins with a crate whose functions have
    no array-operation name. -/
theorem arrayOps_crateBi {fs : List CrateFn} (h : crateArrOk fs = true) {bi : Builtins}
    (hbi : ArrayOps bi) (fuel n : Nat) : ArrayOps (crateBi fs bi fuel n) := by
  simp only [crateArrOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  obtain ⟨hl, hi, hu, -⟩ := h
  exact ⟨fun vs => (hbi.len vs).imp (crateBi_of_find_none fs bi fuel n hl _).trans
      (crateBi_of_find_none fs bi fuel n hl _).trans,
    fun vs j hj hcf => (crateBi_of_find_none fs bi fuel n hi _).trans (hbi.index vs j hj hcf),
    fun vs j v hj => (crateBi_of_find_none fs bi fuel n hu _).trans (hbi.update vs j v hj)⟩

/-- **The source program of the front with the callees `fs`**: `nfSrcProg` at the call
    typing `crateSigOf fs hax64SigOf`, so that a call of a function of `fs`, on arguments of
    any type the parameters of the function declare (words, arrays of words), is a leaf call of
    the program. -/
def nfSrcProgC (fs : List CrateFn) (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  if CatCrypt.Crypto.Hax.haxFrontShapeOk te = true then
    (impToNF (crateSigOf fs hax64SigOf) none (entryEnv (abiEntry σ)) (nfBody te)).map
      fun o => ⟨o.t, o.prog⟩
  else none

/-- **Soundness of the source program of the front with the callees `fs`.** The statement
    of `nfSrcProg_sound` at the builtins `crateBi fs hax64WExit fuelC n`, which answer a call
    of a function of `fs` by the run of its body (to the call depth `n`, at the fuel `fuelC`),
    and the program's leaf calls at the leaf table of the same builtins. -/
theorem nfSrcProgC_sound {fs : List CrateFn} (hfs : crateArrOk fs = true) (fuelC n : Nat)
    {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProgC fs σ te = some q) {sa : Ascent.AddrMem.AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine (crateBi fs CatCrypt.Crypto.Hax.hax64WExit fuelC n) fuel
      te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote), EntryVals env (abiEntry σ) V ∧
      (∃ N, ∀ tf, N ≤ tf → PDenP (crateBi fs CatCrypt.Crypto.Hax.hax64WExit fuelC n) tf q.2 V =
        some (HVector.cons y .nil)) ∧
        v = CatCrypt.Crypto.Hax.ImpToNF.enc q.1 y := by
  unfold nfSrcProgC at hq
  split at hq
  · rename_i hok
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨fuel', v₂, s₂, hb, hrel⟩ := CatCrypt.Crypto.Hax.haxFrontBodyP_run_rel
      CatCrypt.Crypto.Hax.shapeAccepts (crateBi fs CatCrypt.Crypto.Hax.hax64WExit fuelC n)
      (arrayOps_crateBi hfs CatCrypt.Crypto.Hax.arrayOps_hax64WExit fuelC n) te.erase
      (CatCrypt.Crypto.Hax.haxFrontOkP_of_shapeOk hok) fuel
      env env' (.val v) hrun ⟨v, rfl⟩
    have hv2 : v₂ = v := by
      rcases hrel with h | ⟨w, -, h, -⟩
      · exact _root_.Hax.Outcome.val.inj h
      · obtain rfl := _root_.Hax.Outcome.val.inj h
        simp [Value.isControlFlow] at hcf
    subst hv2
    obtain ⟨V, hV⟩ := entryVals_of_typed (entryTyped_abiEntry henv)
    obtain ⟨W, ⟨N, hN⟩, -, hvW⟩ :=
      (impToNF_sound (crateBi fs CatCrypt.Crypto.Hax.hax64WExit fuelC n) (crateSigOf fs hax64SigOf)
        (crateBi_typedCalls fs _ _ CatCrypt.Crypto.Hax.hax64WExit_typedCalls fuelC n)
        (CatCrypt.Crypto.Hax.ImpToNF.crateBi_repeatCalls fs _
          CatCrypt.Crypto.Hax.repeatCalls_hax64WExit (crateArrOk_find_repeat hfs) fuelC n)
        (nfBody te) none (entryEnv (abiEntry σ)) ho fuel').ev (entryEnv_rel hV) hb
    exact ⟨V, o.res.lookup W, hV, ⟨N, fun tf htf =>
      CatCrypt.Crypto.Hax.ImpToNF.PDenP_plug_ret _ tf o.pre _ V (hN tf htf)⟩, hvW⟩
  · cases hq

/-- **The body of the front keeps the runs of an accepted extraction, at every table with the
    array operations.** Under `haxFrontShapeOk te`, a run of the source reading of `te` from
    `env` to a value that is not a control-flow value is matched by a run of `nfBody te`, at
    some fuel, from `env` to the same value. -/
theorem nfBody_prepSim {te : TExpr} (hok : CatCrypt.Crypto.Hax.haxFrontShapeOk te = true)
    {bi : Builtins} (hbi : ArrayOps bi) (fuel : Nat) (env env' : Env) (v : Value)
    (hrun : (denoteSpine bi fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ fuel' s, (_root_.Hax.denote' bi fuel' (nfBody te)).run env = (.val v, s) := by
  obtain ⟨fuel', v₂, s₂, hb, hrel⟩ := CatCrypt.Crypto.Hax.haxFrontBodyP_run_rel
    CatCrypt.Crypto.Hax.shapeAccepts bi hbi te.erase
    (CatCrypt.Crypto.Hax.haxFrontOkP_of_shapeOk hok) fuel env env' (.val v) hrun ⟨v, rfl⟩
  have hv2 : v₂ = v := by
    rcases hrel with h | ⟨w, -, h, -⟩
    · exact _root_.Hax.Outcome.val.inj h
    · obtain rfl := _root_.Hax.Outcome.val.inj h
      simp [Value.isControlFlow] at hcf
  subst hv2
  exact ⟨fuel', s₂, hb⟩

/-- **Soundness of the source program of the front with the callees `fs`, at a table `T`.**
    The statement of `nfSrcProgC_sound` at every table `T` that has the array operations and
    is typed by the call typing `crateSigOf fs hax64SigOf` and satisfies `RepeatCalls`. -/
theorem nfSrcProgT_sound {fs : List CrateFn} {T : Builtins} (hA : ArrayOps T)
    (hT : CatCrypt.Crypto.Hax.ImpToNF.TypedCalls T (crateSigOf fs hax64SigOf))
    (hRep : CatCrypt.Crypto.Hax.ImpToNF.RepeatCalls T)
    {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProgC fs σ te = some q) {sa : Ascent.AddrMem.AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine T fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote), EntryVals env (abiEntry σ) V ∧
      (∃ N, ∀ tf, N ≤ tf → PDenP T tf q.2 V = some (HVector.cons y .nil)) ∧
        v = CatCrypt.Crypto.Hax.ImpToNF.enc q.1 y := by
  unfold nfSrcProgC at hq
  split at hq
  · rename_i hok
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨fuel', s₂, hb⟩ := nfBody_prepSim hok hA fuel env env' v hrun hcf
    obtain ⟨V, hV⟩ := entryVals_of_typed (entryTyped_abiEntry henv)
    obtain ⟨W, ⟨N, hN⟩, -, hvW⟩ := (impToNF_sound T (crateSigOf fs hax64SigOf) hT hRep
        (nfBody te) none (entryEnv (abiEntry σ)) ho fuel').ev (entryEnv_rel hV) hb
    exact ⟨V, o.res.lookup W, hV, ⟨N, fun tf htf =>
      CatCrypt.Crypto.Hax.ImpToNF.PDenP_plug_ret _ tf o.pre _ V (hN tf htf)⟩, hvW⟩
  · cases hq

/-! ## The in-place result of a `&mut` parameter -/

/-- The variable an expression ends by reading: the tail of its spine of bindings and
    sequences, when that tail is a variable. -/
def tailVar : ImpExpr → Option String
  | .var x => some x
  | .letBind _ _ b => tailVar b
  | .seq _ b => tailVar b
  | _ => none

open _root_.Hax (denote') in
/-- **The value of an expression ending in a variable is the final binding of the variable.**
    A run of `denote'` of an expression with `tailVar e = some x` to a value that is not a
    control-flow value leaves `x` bound to that value in the final environment. -/
theorem tailVar_denote' (bi : Builtins) (fuel : Nat) :
    ∀ (e : ImpExpr) (x : String) (env env' : Env) (v : Value), tailVar e = some x →
      (denote' bi fuel e).run env = (.val v, env') → v.isControlFlow = false →
        env' x = some v := by
  intro e x env env' v h hr hcf
  cases e with
  | var y =>
    simp only [tailVar, Option.some.injEq] at h
    subst h
    cases hy : env y <;>
      simp_all [denote', StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure] <;>
      obtain ⟨h1, rfl⟩ := Prod.mk.inj hr <;> cases h1
    exact hy
  | letBind y val b =>
    simp only [tailVar] at h
    simp only [denote', bind, StateT.bind, StateT.run] at hr
    rcases hm : denote' bi fuel val env with ⟨o, s⟩
    rw [hm] at hr
    dsimp only at hr
    split at hr
    · simp only [pure, StateT.pure] at hr
      obtain ⟨h1, -⟩ := Prod.mk.inj hr
      cases h1
      simp [Value.isControlFlow] at hcf
    · exact tailVar_denote' bi fuel b x _ env' v h hr hcf
    · rename_i hne
      simp only [pure, StateT.pure] at hr
      exact absurd (Prod.mk.inj hr).1 (hne v)
  | seq a b =>
    simp only [tailVar] at h
    simp only [denote', bind, StateT.bind, StateT.run] at hr
    rcases hm : denote' bi fuel a env with ⟨o, s⟩
    rw [hm] at hr
    dsimp only at hr
    split at hr
    · simp only [pure, StateT.pure] at hr
      obtain ⟨h1, -⟩ := Prod.mk.inj hr
      cases h1
      simp [Value.isControlFlow] at hcf
    · exact tailVar_denote' bi fuel b x _ env' v h hr hcf
    · rename_i hne
      simp only [pure, StateT.pure] at hr
      exact absurd (Prod.mk.inj hr).1 (hne v)
  | _ => simp [tailVar] at h

/-- **The in-place result.** A run of the source reading `denoteSpine` of an expression with
    `tailVar e = some x` to a value that is not a control-flow value leaves `x` bound to that
    value in the final environment: the result value of a body that ends by reading its
    `&mut` parameter `x` is the final binding of the parameter. -/
theorem tailVar_denoteSpine :
    ∀ (bi : Builtins) (fuel : Nat) (e : ImpExpr) (x : String) (env env' : Env) (v : Value),
      tailVar e = some x → (denoteSpine bi fuel e).run env = (.val v, env') →
        v.isControlFlow = false → env' x = some v := by
  intro bi fuel e x env env' v h hr hcf
  cases e with
  | letBind y val b =>
    simp only [tailVar] at h
    cases val with
    | lam ps body =>
      simp only [denoteSpine] at hr
      split at hr
      · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
          StateT.run] at hr
        exact tailVar_denoteSpine _ fuel b x env env' v h hr hcf
      · exact tailVar_denote' bi fuel _ x env env' v (by simpa [tailVar] using h) hr hcf
    | _ =>
      simp only [denoteSpine, bind, StateT.bind, StateT.run] at hr
      rcases hm : _root_.Hax.denote' bi fuel _ env with ⟨o, s⟩
      rw [hm] at hr
      dsimp only at hr
      split at hr
      · simp only [pure, StateT.pure] at hr
        obtain ⟨h1, -⟩ := Prod.mk.inj hr
        cases h1
        simp [Value.isControlFlow] at hcf
      · exact tailVar_denoteSpine bi fuel b x _ env' v h hr hcf
      · rename_i hne
        simp only [pure, StateT.pure] at hr
        exact absurd (Prod.mk.inj hr).1 (hne v)
  | seq a b =>
    simp only [tailVar] at h
    simp only [denoteSpine, bind, StateT.bind, StateT.run] at hr
    rcases hm : _root_.Hax.denote' bi fuel a env with ⟨o, s⟩
    rw [hm] at hr
    dsimp only at hr
    split at hr
    · simp only [pure, StateT.pure] at hr
      obtain ⟨h1, -⟩ := Prod.mk.inj hr
      cases h1
      simp [Value.isControlFlow] at hcf
    · exact tailVar_denoteSpine bi fuel b x _ env' v h hr hcf
    · rename_i hne
      simp only [pure, StateT.pure] at hr
      exact absurd (Prod.mk.inj hr).1 (hne v)
  | _ => exact tailVar_denote' bi fuel _ x env env' v h hr hcf

/-! ## The level check of the direct front -/

open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams catCT
  catLevelCheck catLevelCheck_sound)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-- The level of a parameter named `x` in the secrecy record `s`: public when the record lists
    it as public, secret otherwise. -/
def paramLevel (s : _root_.Hax.FnSecrecy) (x : String) : SecretLevel :=
  if s.params.lookup x = some .pub then .Public else .Secret

/-- The labels of the mapped context of the parameters `ps` from the secrecy record `s`. -/
def nfLabels (s : _root_.Hax.FnSecrecy) :
    (ps : List (String × NfTy)) → Labels (d := catCryptDialect) ((entryCtx ps).map catTy)
  | [] => .nil
  | (x, _) :: ps => .cons (paramLevel s x) (nfLabels s ps)

/-- The straight-line program of `catCryptDialect` the direct front translates the body of
    `te` to, before the lowering to `jasminDialect`: `none` when the front refuses the body or
    the translated program has a loop. -/
def nfCatCom (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, Com catCryptDialect ((entryCtx (abiEntry σ)).map catTy) (catTy t)) :=
  if CatCrypt.Crypto.Hax.haxFrontShapeOk te = true then
    (impToNF hax64SigOf none (entryEnv (abiEntry σ)) (nfBody te)).bind fun o =>
      (nfToCat (NFProg.dce o.prog) TRd.id).bind fun p' =>
        (NFProg.toCom? p').map fun c => ⟨o.t, c⟩
  else none

/-- **The level check of the direct front**: the straight-line program `nfCatCom σ te`,
    checked by `catLevelCheck P` from the labels of the parameters in the secrecy record
    `s`. -/
def nfFrontCT (P : CatLeakParams) (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr) :
    Bool :=
  match nfCatCom σ te with
  | some c => catLevelCheck P c.2 (nfLabels s (abiEntry σ))
  | none => false

/-- **Soundness of the level check of the direct front.** An accepted body translates to a
    straight-line program of `catCryptDialect` that is constant time (`catCT`) for the labels
    of the parameters in the secrecy record. -/
theorem nfFrontCT_sound (P : CatLeakParams) (s : _root_.Hax.FnSecrecy) (σ : AbiLayout)
    (te : TExpr) (h : nfFrontCT P s σ te = true) :
    ∃ c, nfCatCom σ te = some c ∧ catCT P (nfLabels s (abiEntry σ)) c.2 := by
  unfold nfFrontCT at h
  split at h
  · rename_i c hc
    exact ⟨c, hc, catLevelCheck_sound P c.2 _ h⟩
  · cases h

end CatCrypt.Crypto.SecureCompilation.Haxc
