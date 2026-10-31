/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.Hax.ImpDesugarTable
public import CatCrypt.Hax.TExprTypingSpine

/-!
# The front of the hax compiler with the conditional and remainder desugarings

`desugarAll e` is `ImpDesugarRem.desugarRem` at the empty table of constants after
`ImpDesugarIte.desugarIte` at the renaming `hax64Spec`: a conditional with speculatable arms
is a call of `select`, and a remainder by a constant modulus is a Barrett sequence ending in
a call of `select`. The pass runs on the erased extraction, before the front prepares
the body: the preparation puts the arms of a conditional in A-normal form, which
`desugarIte` does not read as speculatable.

`nfSrcProgDG sig σ te` is the source program of the front on the desugared extraction: the
body `nfBodyD te` the front prepares from `desugarAll te.erase`, translated by
`ImpToNF.impToNF` at the call typing `sig`. `nfSrcProgD` and `nfSrcProgDC fs` are its
instances at `hax64SigOf` and at the call typing with the callees `fs`; `nfFrontD` is
`nfSrcProgD` followed by the chain `nfChain`. The builtin table is `hax64WSel`, the table
`hax64WExit` with `select`.

The denotation lemmas of the two passes relate two successful runs, because a select
evaluates both arms and the Barrett sequence is defined on words below `2^64` only. The
soundness statements therefore take the runs of the two desugared forms as the hypothesis
`DesugarRuns`.

## Main definitions

* `desugarAll` — the two passes in sequence.
* `hax64WSel` — the table `hax64WExit` with `select`.
* `DesugarRuns` — the runs of the two desugared forms of an expression to values that are
  not control-flow values.
* `desugarGate`, `nfBodyD`, `nfSrcProgDG`, `nfSrcProgD`, `nfSrcProgDC` — the check of the
  desugared front, the body it prepares, and its source program at a call typing, at
  `hax64SigOf`, and with callees.
* `crateDesugarOk` — no callee has a name the passes read.
* `nfFrontD` — the front half on the desugared extraction.

## Main results

* `arrayOps_withSelect`, `hax64WSel_typedCalls`, `hax64WSel_subTable`,
  `selectSpec_hax64WSel`, `refines_hax64WSel`, `wordSpec_hax64WSel` — the hypotheses of the
  front, of the chain and of the passes at `hax64WSel`.
* `selectSpec_crateBi`, `refines_crateBi`, `wordSpec_crateBi` — the hypotheses of the passes
  at the builtins with callees.
* `denoteSpine_eq_denote'` — the spine reading of a body whose spine binds no closure.
* `nfSrcProgDG_sound`, `nfSrcProgD_sound`, `nfSrcProgDC_sound` — a source run is matched by
  a run of the source program of the desugared front, under `DesugarRuns`.
* `nfFrontD_sound` — the leg of the desugared front, under `DesugarRuns`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnv EntryVals impToNF hax64SigOf
  entryVals_of_typed impToNF_sound entryEnv_rel PDenP PDenP_plug_ret enc TypedCalls withSelect
  withSelect_of_ne withSelect_typedCalls CrateFn crateSigOf crateBi crateBi_of_find_none
  crateBi_typedCalls RepeatCalls repeatCalls_withSelect crateBi_repeatCalls)
open CatCrypt.Crypto.Hax.ImpDesugarIte (desugarIte hax64Spec Plain SelectSpec Refines
  desugarIte_denote selectName)
open CatCrypt.Crypto.Hax.ImpDesugarRem (desugarRem WordSpec desugarRem_denote)
open CatCrypt.Crypto.Hax.ImpDesugarTable (selectSpec_withSelect refines_hax64Builtins
  refines_mono refines_withSelect hax64Spec_ne_select wordSpec_hax64Builtins wordSpec_mono
  wordSpec_withSelect)
open CatCrypt.Crypto.Hax (hax64WExit haxFrontBodyP haxFrontOkP shapeAccepts spineLamFree
  isLamE)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open Ctxt (Var Valuation)
open _root_.Hax (TExpr ImpExpr Value Env Builtins denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open _root_.Hax.InlineMap (ArrayOps)

/-! ## The pass and its table -/

/-- **The desugaring of the front**: `desugarIte` at the renaming `hax64Spec`, then
    `desugarRem` at the empty table of constants. -/
def desugarAll (e : ImpExpr) : ImpExpr :=
  desugarRem (fun _ => none) (desugarIte hax64Spec e)

/-- The table `hax64WExit` with `select`. -/
abbrev hax64WSel : Builtins := withSelect hax64WExit

/-- The array operations of a table are those of the table with `select`. -/
theorem arrayOps_withSelect {bi : Builtins} (h : ArrayOps bi) : ArrayOps (withSelect bi) where
  len vs := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.len vs
  index vs j hj hcf := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.index vs j hj hcf
  update vs j v hj := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.update vs j v hj

/-- The call typing `hax64SigOf` is sound for `hax64WSel`. -/
theorem hax64WSel_typedCalls : TypedCalls hax64WSel hax64SigOf :=
  withSelect_typedCalls CatCrypt.Crypto.Hax.hax64WExit_typedCalls

/-- `hax64WSel` satisfies `RepeatCalls`. -/
theorem hax64WSel_repeatCalls : RepeatCalls hax64WSel :=
  repeatCalls_withSelect CatCrypt.Crypto.Hax.repeatCalls_hax64WExit

/-- `hax64WSel` agrees with the `u64` table with `select` at the calls the translation to
    `catCryptDialect` admits. -/
theorem hax64WSel_subTable : SubTable hax64WSel :=
  subTable_withSelect_of CatCrypt.Crypto.Hax.hax64WExit_subTable

/-- `hax64WSel` satisfies `SelectSpec`. -/
theorem selectSpec_hax64WSel : SelectSpec hax64WSel := selectSpec_withSelect _

/-- On `hax64WSel`, the checked `Sub` and `Add`, where defined, agree with the wrapping
    operations at `64` bits. -/
theorem refines_hax64WSel : Refines hax64WSel hax64Spec :=
  refines_withSelect
    (refines_mono refines_hax64Builtins fun _ _ _ h => CatCrypt.Crypto.Hax.hax64WExit_sub h)
    hax64Spec_ne_select

/-- `hax64WSel` satisfies `WordSpec`. -/
theorem wordSpec_hax64WSel : WordSpec hax64WSel :=
  wordSpec_withSelect
    (wordSpec_mono wordSpec_hax64Builtins fun _ _ _ h => CatCrypt.Crypto.Hax.hax64WExit_sub h)

/-! ## The table with callees -/

/-- No function of `fs` has a name the desugaring passes read: a name `hax64Spec` admits,
    `select`, `mulhi#64` or `Rem`. -/
def crateDesugarOk (fs : List CrateFn) : Bool :=
  fs.all fun c => (hax64Spec c.name).isNone && !(["select", "mulhi#64", "Rem"].contains c.name)

/-- Under `crateDesugarOk fs`, a name `hax64Spec` admits is the name of no function of
    `fs`. -/
theorem find_none_of_spec {fs : List CrateFn} (h : crateDesugarOk fs = true) {f : String}
    (hf : (hax64Spec f).isSome = true) : fs.find? (·.name == f) = none := by
  rw [List.find?_eq_none]
  intro c hc hcf
  have := List.all_eq_true.mp h c hc
  rw [beq_iff_eq] at hcf
  subst hcf
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  rw [this.1] at hf
  cases hf

/-- Under `crateDesugarOk fs`, `select`, `mulhi#64` and `Rem` are names of no function of
    `fs`. -/
theorem find_none_of_mem {fs : List CrateFn} (h : crateDesugarOk fs = true) {f : String}
    (hf : f ∈ ["select", "mulhi#64", "Rem"]) : fs.find? (·.name == f) = none := by
  rw [List.find?_eq_none]
  intro c hc hcf
  have := List.all_eq_true.mp h c hc
  rw [beq_iff_eq] at hcf
  subst hcf
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at this
  exact this.2 hf

/-- A name `hax64Spec` renames to is a name `hax64Spec` admits. -/
theorem hax64Spec_range {f g : String} (h : hax64Spec f = some g) :
    (hax64Spec g).isSome = true := by
  unfold hax64Spec at h
  split at h
  · cases h
    decide
  · split at h
    · cases h
      decide
    · rename_i hs ha
      split at h
      · rename_i hm
        cases h
        simp [hax64Spec, hs, ha, hm]
      · cases h

/-- The builtins with callees satisfy `SelectSpec` when the builtins do. -/
theorem selectSpec_crateBi {fs : List CrateFn} (h : crateDesugarOk fs = true) {bi : Builtins}
    (hS : SelectSpec bi) (fuel n : Nat) : SelectSpec (crateBi fs bi fuel n) := fun k x y =>
  (crateBi_of_find_none fs bi fuel n
    (find_none_of_mem h (f := selectName) (by decide)) _).trans (hS k x y)

/-- The builtins with callees satisfy `Refines` at `hax64Spec` when the builtins do. -/
theorem refines_crateBi {fs : List CrateFn} (h : crateDesugarOk fs = true) {bi : Builtins}
    (hR : Refines bi hax64Spec) (fuel n : Nat) :
    Refines (crateBi fs bi fuel n) hax64Spec := by
  intro f g hfg vals v w hv hw
  rw [crateBi_of_find_none fs bi fuel n (find_none_of_spec h (by rw [hfg]; rfl))] at hv
  rw [crateBi_of_find_none fs bi fuel n (find_none_of_spec h (hax64Spec_range hfg))] at hw
  exact hR f g hfg vals v w hv hw

/-- The builtins with callees satisfy `WordSpec` when the builtins do. -/
theorem wordSpec_crateBi {fs : List CrateFn} (h : crateDesugarOk fs = true) {bi : Builtins}
    (hW : WordSpec bi) (fuel n : Nat) : WordSpec (crateBi fs bi fuel n) where
  mulhi := fun vals v hv => hW.mulhi vals v (by
    rwa [crateBi_of_find_none fs bi fuel n (find_none_of_mem h (by decide))] at hv)
  wmul := fun vals v hv => hW.wmul vals v (by
    rwa [crateBi_of_find_none fs bi fuel n (find_none_of_spec h (by decide))] at hv)
  wsub := fun vals v hv => hW.wsub vals v (by
    rwa [crateBi_of_find_none fs bi fuel n (find_none_of_spec h (by decide))] at hv)
  lt := fun a b v hv => hW.lt a b v (by
    rwa [crateBi_of_find_none fs bi fuel n (find_none_of_spec h (by decide))] at hv)
  rem := fun a p v ha hp0 hp hv => hW.rem a p v ha hp0 hp (by
    rwa [crateBi_of_find_none fs bi fuel n (find_none_of_mem h (by decide))] at hv)

/-! ## The runs of the desugared forms -/

/-- **The desugared forms run.** From `env`, at the fuel `fuel`, the select form
    `desugarIte hax64Spec e` and the form `desugarAll e` each run to a value that is not a
    control-flow value. -/
def DesugarRuns (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) : Prop :=
  (∃ w e₁, denote' bi fuel (desugarIte hax64Spec e) env = (.val w, e₁) ∧ Plain w) ∧
    ∃ w e₂, denote' bi fuel (desugarAll e) env = (.val w, e₂) ∧ Plain w

/-- On a body whose statement spine binds no closure, the spine reading `denoteSpine` is
    `denote'`. -/
theorem denoteSpine_eq_denote' (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (h : spineLamFree e = true) : denoteSpine bi fuel e = denote' bi fuel e := by
  induction e using _root_.Hax.ImpExpr.ind with
  | letBind x v b _ ihb =>
      simp only [spineLamFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      cases v with
      | lam ps body => simp [isLamE] at h
      | _ =>
          rw [CatCrypt.Hax.TExprTypingSpine.denote'_letBind, ← ihb h.2]
          rfl
  | seq a b _ ihb =>
      rw [CatCrypt.Hax.TExprTypingSpine.denote'_seq, ← ihb h]
      rfl
  | _ => rfl

/-- **The desugared extraction runs to the source value.** Under the hypotheses of the two
    passes on the builtins, a run of `e` to a value `v` that is not a control-flow value
    and `DesugarRuns` give a run of `desugarAll e` to `v`. -/
theorem desugarAll_run {bi : Builtins} (hS : SelectSpec bi) (hR : Refines bi hax64Spec)
    (hW : WordSpec bi) {fuel : Nat} {e : ImpExpr} {env env' : Env} {v : Value}
    (hrun : denote' bi fuel e env = (.val v, env')) (hcf : v.isControlFlow = false)
    (hrunD : DesugarRuns bi fuel e env) :
    ∃ e₂, denote' bi fuel (desugarAll e) env = (.val v, e₂) := by
  obtain ⟨⟨w₁, e₁, h1, hw1⟩, w₂, e₂, h2, hw2⟩ := hrunD
  have hv : Plain v := by
    intro k p hk
    subst hk
    simp [Value.isControlFlow] at hcf
  obtain ⟨rfl, rfl⟩ := desugarIte_denote hS hR e env env' e₁ v w₁ hrun hv h1 hw1
  obtain ⟨rfl, -⟩ := desugarRem_denote hS hW (desugarIte hax64Spec e) (fun _ => none) env
    env' e₂ v w₂ (fun _ _ hk => by cases hk) h1 hv h2 hw2
  exact ⟨e₂, h2⟩

/-! ## The source program of the desugared front -/

/-- **The check of the desugared front**: the statement spines of the extraction and of its
    desugared form bind no closure, the desugared form passes the side conditions of the
    front under the shape test `shapeAccepts`, and the body it prepares has no `whileFold`
    (`ImpToNF.whileFoldFree`). -/
def desugarGate (te : TExpr) : Bool :=
  spineLamFree te.erase && spineLamFree (desugarAll te.erase) &&
    haxFrontOkP shapeAccepts (desugarAll te.erase) &&
    CatCrypt.Crypto.Hax.ImpToNF.whileFoldFree (haxFrontBodyP shapeAccepts (desugarAll te.erase))

/-- The body the front prepares from the desugared extraction under the shape test
    `shapeAccepts`. -/
def nfBodyD (te : TExpr) : ImpExpr :=
  haxFrontBodyP shapeAccepts (desugarAll te.erase)

/-- **The source program of the desugared front** at the call typing `sig`: the body
    `nfBodyD te`, under the check `desugarGate`, translated to `NFProg nfDialect` by
    `impToNF` from the parameters `abiEntry σ`, with the type of its result. -/
def nfSrcProgDG (sig : String → List NfTy → Option NfTy) (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  if desugarGate te = true then
    (impToNF sig none (entryEnv (abiEntry σ)) (nfBodyD te)).map fun o => ⟨o.t, o.prog⟩
  else none

/-- **Soundness of the source program of the desugared front**, at builtins `bi` for which
    `sig` is sound, that satisfy `RepeatCalls`, keep the array operations and satisfy the
    hypotheses of the two passes. For `nfSrcProgDG sig σ te = some q`, from every environment `σ` reads off an
    entry state, a run of the source reading of `te` to a value `v` that is not a
    control-flow value, with the runs `DesugarRuns` of the desugared forms, gives a
    valuation `V` of the parameters whose encodings the environment holds, at which `q.2`
    denotes a value `y` whose encoding is `v`. -/
theorem nfSrcProgDG_sound {bi : Builtins} {sig : String → List NfTy → Option NfTy}
    (hT : TypedCalls bi sig) (hRep : RepeatCalls bi) (hA : ArrayOps bi) (hS : SelectSpec bi)
    (hR : Refines bi hax64Spec) (hW : WordSpec bi) {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProgDG sig σ te = some q) {sa : AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine bi fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) (hrunD : DesugarRuns bi fuel te.erase env) :
    ∃ (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote), EntryVals env (abiEntry σ) V ∧
      PDenP bi 0 q.2 V = some (HVector.cons y .nil) ∧ v = enc q.1 y := by
  unfold nfSrcProgDG at hq
  split at hq
  · rename_i hok
    simp only [desugarGate, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hl, hlD⟩, hok⟩, hwf⟩ := hok
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [denoteSpine_eq_denote' bi fuel _ hl] at hrun
    obtain ⟨e₂, h2⟩ := desugarAll_run hS hR hW hrun hcf hrunD
    have hD : (denoteSpine bi fuel (desugarAll te.erase)).run env = (.val v, e₂) := by
      rw [denoteSpine_eq_denote' bi fuel _ hlD]
      exact h2
    obtain ⟨fuel', v₂, s₂, hb, hrel⟩ := CatCrypt.Crypto.Hax.haxFrontBodyP_run_rel
      shapeAccepts bi hA (desugarAll te.erase) hok fuel env e₂ (.val v) hD ⟨v, rfl⟩
    have hv2 : v₂ = v := by
      rcases hrel with h | ⟨w, -, h, -⟩
      · exact _root_.Hax.Outcome.val.inj h
      · obtain rfl := _root_.Hax.Outcome.val.inj h
        simp [Value.isControlFlow] at hcf
    subst hv2
    obtain ⟨V, hV⟩ := entryVals_of_typed (entryTyped_abiEntry henv)
    obtain ⟨W, hprog, -, hvW⟩ := CatCrypt.Crypto.Hax.ImpToNF.Sound.all_of_whileFree
      (impToNF_sound bi sig hT hRep (nfBodyD te) none (entryEnv (abiEntry σ)) ho fuel')
      (FrontComplete.whileFree_of_opsNB _ (FrontComplete.impToNF_prog_frontOp _ _ none _ o ho
        hwf))
      (entryEnv_rel hV) hb
    exact ⟨V, o.res.lookup W, hV, hprog 0, hvW⟩
  · cases hq

/-- The source program of the desugared front at the call typing `hax64SigOf`. -/
def nfSrcProgD (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  nfSrcProgDG hax64SigOf σ te

/-- **Soundness of `nfSrcProgD`** at the table `hax64WSel`: `nfSrcProgDG_sound` with every
    hypothesis on the builtins discharged. -/
theorem nfSrcProgD_sound {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProgD σ te = some q) {sa : AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine hax64WSel fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) (hrunD : DesugarRuns hax64WSel fuel te.erase env) :
    ∃ (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote), EntryVals env (abiEntry σ) V ∧
      PDenP hax64WSel 0 q.2 V = some (HVector.cons y .nil) ∧ v = enc q.1 y :=
  nfSrcProgDG_sound hax64WSel_typedCalls hax64WSel_repeatCalls
    (arrayOps_withSelect CatCrypt.Crypto.Hax.arrayOps_hax64WExit) selectSpec_hax64WSel
    refines_hax64WSel wordSpec_hax64WSel hq henv hrun hcf hrunD

/-- The source program of the desugared front at the call typing with the callees `fs`. -/
def nfSrcProgDC (fs : List CrateFn) (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  nfSrcProgDG (crateSigOf fs hax64SigOf) σ te

/-- **Soundness of `nfSrcProgDC`** at the builtins `crateBi fs hax64WSel fuelC n`, for
    callees with no array-operation name (`crateArrOk`) and no name the passes read
    (`crateDesugarOk`). -/
theorem nfSrcProgDC_sound {fs : List CrateFn} (hfs : crateArrOk fs = true)
    (hds : crateDesugarOk fs = true) (fuelC n : Nat) {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProgDC fs σ te = some q) {sa : AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine (crateBi fs hax64WSel fuelC n) fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false)
    (hrunD : DesugarRuns (crateBi fs hax64WSel fuelC n) fuel te.erase env) :
    ∃ (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote), EntryVals env (abiEntry σ) V ∧
      PDenP (crateBi fs hax64WSel fuelC n) 0 q.2 V = some (HVector.cons y .nil) ∧
        v = enc q.1 y :=
  nfSrcProgDG_sound (crateBi_typedCalls fs _ _ hax64WSel_typedCalls fuelC n)
    (crateBi_repeatCalls fs _ hax64WSel_repeatCalls (crateArrOk_find_repeat hfs) fuelC n)
    (arrayOps_crateBi hfs (arrayOps_withSelect CatCrypt.Crypto.Hax.arrayOps_hax64WExit) fuelC n)
    (selectSpec_crateBi hds selectSpec_hax64WSel fuelC n)
    (refines_crateBi hds refines_hax64WSel fuelC n)
    (wordSpec_crateBi hds wordSpec_hax64WSel fuelC n) hq henv hrun hcf hrunD

/-! ## The front half on the desugared extraction -/

/-- **The front half of the hax compiler on the desugared extraction**: the source program
    `nfSrcProgD σ te` followed by the chain `nfChain`, with the type of its result. -/
def nfFrontD (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) :=
  (nfSrcProgD σ te).bind fun q => ((nfChain _ q.1).run q.2).map fun rp => ⟨q.1, rp⟩

/-- **The leg of the desugared front.** For a result `⟨t, rp⟩` of `nfFrontD σ te`, from
    every environment `σ` reads off an entry state `sa`, a run of the source reading of `te`
    at the table `hax64WSel` to a value `v` that is not a control-flow value, with the runs
    `DesugarRuns` of the desugared forms, gives a valuation of the route program's context
    that `σ` reads off `sa` at which, at every fuel `cf`, the program denotes a value whose
    source value `denVal` is `v`. It is `nfSrcProgD_sound` followed by `nfChain_entry`. -/
theorem nfFrontD_sound (σ : AbiLayout) (te : TExpr)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFrontD σ te = some p)
    (sa : AState) (env : Env) (henv : σ.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine hax64WSel fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) (hrunD : DesugarRuns hax64WSel fuel te.erase env) :
    ∃ V : Valuation (nfCtx σ), AbiValOf σ sa V ∧
      ∀ cf : Nat, ∃ x, p.2.denoteF cf V = some x ∧ v = denVal _ x := by
  obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨V, y, hV, hp, hv⟩ := nfSrcProgD_sound hq henv hrun hcf hrunD
  refine ⟨_, abiValOf_mapVal henv V hV, fun cf => ?_⟩
  obtain ⟨-, x, hx, hden⟩ := nfChain_entry hax64WSel_subTable 0 cf henv q.2 hrp V hV hp
  exact ⟨x, hx, hv.trans hden.symm⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
