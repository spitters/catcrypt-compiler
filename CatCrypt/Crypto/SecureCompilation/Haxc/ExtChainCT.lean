/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ExtChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCT
public import CatCrypt.Crypto.SecureCompilation.VIR.NFPassLeakMC
public import CatCrypt.Crypto.Hax.ImpToNFLeak

/-!
# Constant time through the chain with declarations

`extChainCTCert` is a constant-time certificate (`PassChain.CTCert`) of the chain `extChain`
at declarations `D` of no name `index` or `array_update` on which the builtin table and
`catEnvOf E'` agree (`ExtAgree`), from the source semantics of the leakage model
`nfLeakModelL D`, in which a call of a tagged field head or of a name that `D` declares is
quiet, with one leaf per step:

0. `flattenTuples`: the identity on the inputs, with the events of the source run
   (`flatSameCTStep`, from `flatSame_leakRunM`), since every tuple operation is quiet in
   `nfLeakModelL D` (`tupleQuiet_nfLeakModelL`);
1. `outTy`: the identity (`outTyCTStep`);
2. `dce`: `dceCTStep`;
3. `nfToCatExt` at the declarations `fieldDeclsFor D p`: `nfToCatExt_leakD`, at valuations in
   range and their mapped valuations; the events of the translation are the source events
   without the variable-time leaf calls of tagged field heads and of the declared names
   (`stripDecl`), at the call environment `catEnvOf (fieldEnv E')`;
4. `aegraph` at `catRules`: `aegraphOptNF_ctRelC` at that call environment;
5. `map?` along `catToJasmin`: `catToJasmin_map?_ctLeakC`, from `catEnvOf (fieldEnv E')` to
   `fieldEnv E'`;
6. the montify step `NFMontify.montifyStep`: `NFMontify.montifyStep_leakRunC` at
   `fieldEnv E'` (`montifyCTStep`); the conversion constants and the reduce-multiply blocks
   bind quiet operations only;
7. the field dialect step `FieldDialectStep.fieldDialectStep` of the tagged calls, at
   leakage parameters with no variable-time operation: two runs at `fieldEnv E'` give two
   runs of its result at `E'`, with equal events from equal events
   (`fieldDialectStep_leakRunC`, `fieldDialectCTStep`);
8. to 10. `lowerSelects`, `rangeNF` and the e-graph pass at `jasminRules`, at `E'`:
   `NFProg.lowerSelects_ctRelC`, `rangeNF_ctRelC` and `aegraphOptNF_ctRelC`.

A call of a declared name emits no event in the translated program; its own constant time is
a property of the callee.

## Main definitions

* `leakSemNFC` — the leakage semantics of structured programs at a call environment: the
  events of `NFProg.leakRunMC`.
* `nfLeakModelL`, `nfLeakRunL` — the leakage model of `nfDialect` with quiet calls of
  tagged field heads and of declared names, and its leakage run.
* `flatSameCTStep` — the constant-time step certificate of tuple flattening.
* `aegraphCTStepC`, `extCallCTStep`, `mapCTStepC`, `montifyCTStep`, `fieldDialectCTStep`,
  `lowerSelectsCTStepC`, `rangeCTStepC` — the constant-time step certificates of the e-graph
  pass, of the translation with declarations, of the conversion `map?`, of the montify step,
  of the field dialect step, of the select lowering and of `rangeNF`.
* `fieldInlineCTStep` — the constant-time step certificate of the inlining `fieldInlineStep`
  of the tagged calls.
* `extChainCTCert` — the constant-time certificate of `extChain`.

## Main results

* `tupleQuiet_nfLeakModel`, `tupleQuiet_nfLeakModelL` — every tuple operation is quiet in
  the leakage models of `nfDialect`.
* `fieldDeclsFor_of_tagged`, `fieldDeclsOf_tagged` — at declarations of tagged heads the
  declarations of the translation are those of the tagged calls of the program, each a
  declaration of a field head.
* `stripDecl_stripField`, `nfLeakRun_of_nfLeakRunQ` — the events of the translation are a
  function of the source events without the leaf calls of tagged field heads.
* `nfLeakRunL_eq`, `stripDecl_fieldDeclsFor` — the run with quiet declared calls is the
  stripped run, and the declared events of the translation are those of `D`.
* `fieldInlineStep_leakRunC` — two leakage runs at `fieldEnv E'` of a program the inlining
  step accepts are two leakage runs at `E'` of its result, with the same results, whose
  events are equal when the source events are.
* `extChain_ctC` — source events of two runs at a fuel that are equal without the leaf calls
  of tagged field heads and of the declared names give two runs at `E'` of the program `extChain` returns at that fuel,
  from the transported valuations, with equal events.
* `extChain_ct` — the same at declarations of tagged heads and the empty call environment,
  for the runs `NFProg.leakRun`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_map?_ctLeakC)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams catLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (RuleSet RulesIndep)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_ctRelC)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules catRules_indep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules jasminRules_indep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF (rangeNFStep rangeNF_ctRelC)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (nfLeakModelQ nfLeakRunQ nfLeakRunQ_eq)
open _root_.Hax.FieldTag (fieldTag?)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep
  fieldDialectStep_leakRunC)
open Ctxt (Var Valuation)
open _root_.Hax (Builtins)

/-! ## The leakage semantics at a call environment -/

section Sems

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- The leakage semantics of structured programs at the leakage model `M`, the call
    environment `E` and the fuel `fuel`: the events of `NFProg.leakRunMC`, in which a `call`
    runs the callee of `E` and emits no event. -/
def leakSemNFC (M : LeakModel d) (E : CallEnv d) (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    LeakSem (NFProg d Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak p V := (NFProg.leakRunMC M E fuel p V).map Prod.snd

variable [DecidableEq d.Ty] [DecidableEq d.Op]

/-- The constant-time step certificate of the e-graph pass at the leakage semantics at the
    call environment `E`, from `aegraphOptNF_ctRelC`. -/
def aegraphCTStepC {M : LeakModel d} (R : RuleSet d) (hI : RulesIndep M R) (E : CallEnv d)
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (aegraphStep R Γ ts).run (leakSemNFC M E fuel Γ ts).twoRun
      (leakSemNFC M E fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, -, hs₁, -⟩ := aegraphOptNF_ctRelC R hI E fuel p V₁ V₁ r₁ r₁ hr₁ hr₁ rfl
    obtain ⟨s₂, -, hs₂, -⟩ := aegraphOptNF_ctRelC R hI E fuel p V₂ V₂ r₂ r₂ hr₂ hr₂ rfl
    refine ⟨s₁.2, s₂.2, by simp only [leakSemNFC, hs₁, Option.map_some],
      by simp only [leakSemNFC, hs₂, Option.map_some], fun he => ?_⟩
    obtain ⟨t₁, t₂, ht₁, ht₂, -, -, het⟩ :=
      aegraphOptNF_ctRelC R hI E fuel p V₁ V₂ r₁ r₂ hr₁ hr₂ he
    rw [hs₁, Option.some.injEq] at ht₁
    rw [hs₂, Option.some.injEq] at ht₂
    rw [ht₁, ht₂, het]

end Sems

/-! ## The translation with declarations -/

/-- **At declarations of tagged heads the declarations of the translation are those of the
    tagged calls of the program**: the filter of `fieldDeclsFor` keeps no declaration. -/
theorem fieldDeclsFor_of_tagged {D : List ExtDecl}
    (hT : ∀ d ∈ D, (fieldTag? d.name).isSome = true) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : fieldDeclsFor D p = fieldDeclsOf p := by
  unfold fieldDeclsFor
  rw [List.filter_eq_nil_iff.mpr (fun d hd => by simp [_root_.Hax.FieldTag.fieldHeadB, hT d hd]),
    List.nil_append]

/-- Every declaration of the tagged calls of a program is a declaration of a field head, a
    canonical or a Montgomery head (`Hax.FieldTag.fieldHeadB`). -/
theorem fieldDeclsOf_tagged {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ d ∈ fieldDeclsOf p, _root_.Hax.FieldTag.fieldHeadB d.name = true := fun _ hd => by
  rcases mem_fieldDeclsOf p hd with ⟨m, q, ht, -⟩ | ⟨m, q, k, hm, -⟩
  · exact _root_.Hax.FieldTag.fieldHeadB_iff.mpr (Or.inl ⟨m, q, ht⟩)
  · exact _root_.Hax.FieldTag.fieldHeadB_iff.mpr (Or.inr ⟨m, q, k, hm⟩)

/-- The declarations of the translation are named neither `index` nor `array_update` when
    the declarations `D` are not: the other declarations are of field heads. -/
theorem fieldDeclsFor_ne_index {D : List ExtDecl}
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update") {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ d ∈ fieldDeclsFor D p, d.name ≠ "index" ∧ d.name ≠ "array_update" := fun d hd => by
  rcases List.mem_append.mp hd with hd | hd
  · exact hN d (List.mem_filter.mp hd).1
  · exact ne_index_of_fieldHeadB (fieldDeclsOf_tagged p d hd)

/-- Removing the variable-time leaf calls of field heads before `stripDecl D` removes
    nothing that `stripDecl D` keeps. -/
theorem stripDecl_stripField (D : List ExtDecl) (l : List CTLeak) :
    stripDecl D (stripField l) = stripDecl D l := by
  unfold stripDecl stripField
  rw [List.filter_filter]
  congr 1
  funext e
  cases e with
  | vtCall f _ =>
      simp only [isFieldEvent, isDeclEvent]
      cases _root_.Hax.FieldTag.fieldHeadB f <;> simp
  | _ => rfl

/-- A run in the leakage model `nfLeakModelQ` with quiet field calls is a run in
    `nfLeakModel` whose events, without the leaf calls of field heads, are its
    events (`nfLeakRunQ_eq`). -/
theorem nfLeakRun_of_nfLeakRunQ {bi : Builtins} {fuel : Nat} {Γ : Ctxt nfDialect}
    {ts : List NfTy} {p : NFProg nfDialect Γ ts} {V : Valuation Γ}
    {r : Valuation (d := nfDialect) ts × List CTLeak}
    (h : nfLeakRunQ bi fuel p V = some r) :
    ∃ r', nfLeakRun bi fuel p V = some r' ∧ r.1 = r'.1 ∧ r.2 = stripField r'.2 := by
  rw [nfLeakRunQ_eq] at h
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r', hr', rfl, rfl⟩

/-! ## The leakage model with quiet declared calls -/

/-- **The leakage model of `nfDialect` with quiet declared calls** at the declarations `D`:
    the class `nfKind` of an operation, except that a call of a field head
    (`Hax.FieldTag.fieldHeadB`) or of a name that `D` declares is quiet. A declared name is
    compiled to a call of a linked function, whose constant time is a property of its code. -/
def nfLeakModelL (D : List ExtDecl) : LeakModel nfDialect where
  kind op := match nfKind op with
    | .vtCall f =>
        if (_root_.Hax.FieldTag.fieldHeadB f || D.any fun d => decide (d.name = f)) = true
        then .quiet
        else .vtCall f
    | k => k
  valNat := nfValNat

/-- The events of an operation under `nfLeakModelL D` are its events under `nfLeakModel`
    without the leaf calls of field heads and of the names that `D` declares. -/
theorem opLeak_nfLeakModelL (D : List ExtDecl) (op : NfOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := nfDialect) op)) :
    opLeak (nfLeakModelL D) op vals = stripDecl D (opLeak nfLeakModel op vals) := by
  have hv : ∀ {tys : List NfTy} (xs : HVector (fun t => ⟦t⟧) tys),
      valsNat (nfLeakModelL D) xs = valsNat nfLeakModel xs := by
    intro tys xs
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg (List.cons _) ih
  unfold opLeak
  rw [hv]
  simp only [nfLeakModelL, nfLeakModel]
  cases nfKind op with
  | vtCall f =>
      cases h : (_root_.Hax.FieldTag.fieldHeadB f || D.any fun d => decide (d.name = f)) <;>
        simp [stripDecl, isDeclEvent, h]
  | _ => simp [stripDecl, isDeclEvent]

/-- The leakage run of a program of `nfDialect` over the leaf table of the builtin table `bi`
    in the leakage model `nfLeakModelL D`. -/
abbrev nfLeakRunL (D : List ExtDecl) (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    Option (Valuation (d := nfDialect) ts × List CTLeak) :=
  @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote (CatCrypt.Crypto.Hax.ImpToNF.tableOf bi))
    (nfLeakModelL D)
    fuel _ _ p V

/-- **The run with quiet declared calls is the stripped run**: the leakage run of a program
    in `nfLeakModelL D` is its run in `nfLeakModel` with the leaf calls of field heads
    and of the names that `D` declares removed from the events (`stripDecl D`). -/
theorem nfLeakRunL_eq (D : List ExtDecl) (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    nfLeakRunL D bi fuel p V = (nfLeakRun bi fuel p V).map fun r => (r.1, stripDecl D r.2) :=
  @CatCrypt.Crypto.SecureCompilation.VIR.NFProg.leakRunM_filter nfDialect _ _ _ _
    (nfDenote (CatCrypt.Crypto.Hax.ImpToNF.tableOf bi)) nfLeakModel (nfLeakModelL D)
    (fun e => !isDeclEvent D e) (fun _ => rfl) (fun _ => rfl) (opLeak_nfLeakModelL D) fuel
    _ _ p V

/-- A run in the leakage model `nfLeakModelL D` is a run in `nfLeakModel` whose events
    without the leaf calls of field heads and of the declared names are its events
    (`nfLeakRunL_eq`). -/
theorem nfLeakRun_of_nfLeakRunL {D : List ExtDecl} {bi : Builtins} {fuel : Nat}
    {Γ : Ctxt nfDialect} {ts : List NfTy} {p : NFProg nfDialect Γ ts} {V : Valuation Γ}
    {r : Valuation (d := nfDialect) ts × List CTLeak}
    (h : nfLeakRunL D bi fuel p V = some r) :
    ∃ r', nfLeakRun bi fuel p V = some r' ∧ r.1 = r'.1 ∧ r.2 = stripDecl D r'.2 := by
  rw [nfLeakRunL_eq] at h
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r', hr', rfl, rfl⟩

/-- At no declaration the stripped events are the events without the field calls. -/
theorem stripDecl_nil_eq (l : List CTLeak) : stripDecl [] l = stripField l := by
  unfold stripDecl stripField
  congr 1
  funext e
  cases e with
  | vtCall f _ => simp [isDeclEvent, isFieldEvent]
  | _ => rfl

/-- The declared events of the translation of a program are the declared events of `D`:
    the declarations `fieldDeclsFor D p` add to `D` the declarations of tagged heads only. -/
theorem isDeclEvent_fieldDeclsFor (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (e : CTLeak) :
    isDeclEvent (fieldDeclsFor D p) e = isDeclEvent D e := by
  cases e with
  | vtCall f _ =>
      simp only [isDeclEvent]
      cases hf0 : _root_.Hax.FieldTag.fieldHeadB f
      · simp only [Bool.false_or, fieldDeclsFor, List.any_append, List.any_filter]
        have h2 : (fieldDeclsOf p).any (fun d => decide (d.name = f)) = false := by
          rw [List.any_eq_false]
          intro d hd hdf
          have := fieldDeclsOf_tagged p d hd
          rw [show d.name = f by simpa using hdf, hf0] at this
          cases this
        rw [h2, Bool.or_false]
        congr 1
        funext d
        by_cases hd : d.name = f
        · rw [hd, hf0]
          simp
        · simp [hd]
      · rfl
  | _ => rfl

/-- Removing the declared events of the translation of a program removes the declared events
    of `D`. -/
theorem stripDecl_fieldDeclsFor (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (l : List CTLeak) :
    stripDecl (fieldDeclsFor D p) l = stripDecl D l := by
  unfold stripDecl
  congr 1
  funext e
  rw [isDeclEvent_fieldDeclsFor]

/-- **The constant-time step certificate of the translation with declarations**, from
    `nfToCatExt_leakD` at the call environment `catEnvOf (fieldEnv E')`, under
    `FieldLevel.FieldCalls bi`, `FieldLevel.FieldCallsWideEq bi`,
    `ExtAgree bi (catEnvOf E') D` and declarations of no name `index` or `array_update`: the
    source semantics is that of the leakage model `nfLeakModelL D`, in which a call of a
    tagged field head or of a declared name is quiet, the input relation relates a valuation
    in range to its mapped valuation `mapVal`, and the events of the translation are the
    source events without the variable-time leaf calls of tagged field heads and of the
    declared names (`stripDecl (fieldDeclsFor D p)`, which is `stripDecl D` by
    `stripDecl_fieldDeclsFor`). -/
def extCallCTStep {P : CatLeakParams} (hP : NoVT P) {bi : Builtins} (hbi : SubTable bi)
    (hF : FieldLevel.FieldCalls bi) (hW : FieldLevel.FieldCallsWideEq bi) {D : List ExtDecl}
    {E' : CallEnv jasminDialect} (hD : ExtAgree bi (catEnvOf E') D)
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update") (fuel : Nat)
    (Γ : Ctxt nfDialect) (ts : List NfTy) :
    StepCert (extCallStep D Γ ts).run (srcLeakSem bi fuel Γ ts (nfLeakModelL D)).twoRun
      (leakSemNFC (catLeakModel P) (catEnvOf (fieldEnv E')) fuel (Γ.map catTy)
        (ts.map catTy)).twoRun :=
  stepCertOfLeak _ _
    (fun V W => W = mapVal V ∧ ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
      obtain ⟨rfl, hin₁⟩ := hV₁
      obtain ⟨rfl, hin₂⟩ := hV₂
      obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨u₁, hu₁, -, hs₁⟩ := nfLeakRun_of_nfLeakRunL hr₁
      obtain ⟨u₂, hu₂, -, hs₂⟩ := nfLeakRun_of_nfLeakRunL hr₂
      have hf' : nfToCatExt (fieldDeclsFor D p) p TRd.id = some q := hf
      have H : NFLeakSoundD P bi _ _ fuel p :=
        nfToCatExt_leakD hP hbi (extAgree_fieldDeclsFor hF hW hD p)
          (fieldDeclsFor_ne_index hN p)
          fuel p
      obtain ⟨c₁, hc₁, e₁, -⟩ := H TRd.id q hf' V₁ (mapVal V₁) u₁ (TRd.agree_id V₁ hin₁) hu₁
      obtain ⟨c₂, hc₂, e₂, -⟩ := H TRd.id q hf' V₂ (mapVal V₂) u₂ (TRd.agree_id V₂ hin₂) hu₂
      exact ⟨c₁.2, c₂.2, by simp only [leakSemNFC, hc₁, Option.map_some],
        by simp only [leakSemNFC, hc₂, Option.map_some], fun he => by
          rw [e₁, e₂, stripDecl_fieldDeclsFor, stripDecl_fieldDeclsFor, ← hs₁, ← hs₂, he]⟩

/-! ## The conversion and the inlining -/

/-- **The constant-time step certificate of `map?` along `catToJasmin` at call
    environments**, from `catToJasmin_map?_ctLeakC` between `catEnvOf E'` and `E'`, which
    agree along the transport at every call (`catEnvOf_transports`): the input relation is
    the graph of `ctMapValD`, and the events are those of the source. -/
def mapCTStepC {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (E' : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt catCryptDialect) (ts : List _) :
    StepCert (mapStep catToJasmin catToJasmin_regionTypes Γ ts).run
      (leakSemNFC (catLeakModel P) (catEnvOf E') fuel Γ ts).twoRun
      (leakSemNFC (jLeakModel Pj) E' fuel (mapCtx Γ) (ts.map mapTy)).twoRun :=
  stepCertOfLeak _ _ (fun V W => W = ctMapValD V)
    fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
      subst hV₁ hV₂
      have hC := fun f as rs x (_ : p.Calls f as rs) => catEnvOf_transports E' f as rs x trivial
      exact ⟨l₁, l₂, (catToJasmin_map?_ctLeakC hc (catEnvOf E') E' fuel p hC q hf V₁).trans h₁,
        (catToJasmin_map?_ctLeakC hc (catEnvOf E') E' fuel p hC q hf V₂).trans h₂, _root_.id⟩

/-- **The constant-time step certificate of the montify step**, from
    `NFMontify.montifyStep_leakRunC`: at the leakage semantics at `fieldEnv E'`, with the
    events of the source, at quiet register arithmetic and register constants. -/
def montifyCTStep {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (hK : ∀ w n, (jLeakModel Pj).kind (.regConst w n) = .quiet) (E' : CallEnv jasminDialect)
    (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (NFMontify.montifyStep Γ ts).run
      (leakSemNFC (jLeakModel Pj) (fieldEnv E') fuel Γ ts).twoRun
      (leakSemNFC (jLeakModel Pj) (fieldEnv E') fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    exact ⟨r₁.2, r₂.2,
      by simp only [leakSemNFC, NFMontify.montifyStep_leakRunC _ hq hK E' fuel hf hr₁,
        Option.map_some],
      by simp only [leakSemNFC, NFMontify.montifyStep_leakRunC _ hq hK E' fuel hf hr₂,
        Option.map_some],
      _root_.id⟩

/-- **Two leakage runs before the inlining of the tagged calls give two runs of its result
    at the remaining calls, with equal events from equal events.** At leakage parameters of
    `jasminDialect` with no variable-time operation, the library of the tagged heads is sound
    for the leakage run at `fieldEnv E'` with a fixed list of events per head
    (`fieldLibJ_leakSound`), so two leakage runs at `fieldEnv E'` of a program that
    `fieldInlineStep` accepts are two runs of the inlined program at the same environment,
    with the same results, whose events are equal when the source events are
    (`NFProg.leakRunMC_inline?_prefix`); the inlined program calls no tagged head, at which
    alone `fieldEnv E'` and `E'` differ, so the runs are its runs at `E'`
    (`NFProg.leakRunMC_congr`). -/
theorem fieldInlineStep_leakRunC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hf : (fieldInlineStep Γ ts).run p = some q)
    {V₁ V₂ : Valuation Γ} {r₁ r₂ : Valuation (d := jasminDialect) ts × List CTLeak}
    (h₁ : NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V₂ = some r₂) :
    ∃ l₁ l₂, NFProg.leakRunMC (jLeakModel Pj) E' fuel q V₁ = some (r₁.1, l₁) ∧
      NFProg.leakRunMC (jLeakModel Pj) E' fuel q V₂ = some (r₂.1, l₂) ∧
      (r₁.2 = r₂.2 → l₁ = l₂) := by
  obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
  split at hif
  · rename_i hff
    have hq : q0 = q := Option.some.inj hif
    subst hq
    obtain ⟨ev, hL⟩ := fieldLibJ_leakSound hV E' fuel
    obtain ⟨l₁, l₂, e₁, e₂, hl⟩ :=
      VIR.NFProg.leakRunMC_inline?_prefix (jLeakModel Pj) (fieldEnv E') hL p hq0 h₁ h₂
    have hc := fun V => NFProg.leakRunMC_congr (jLeakModel Pj) q0 (fieldEnv E') E'
      (fun f as rs x hc => fieldEnv_of_none E' (fieldHeadB_of_fieldFree q0 hff hc) as rs x)
      fuel V
    rw [hc] at e₁ e₂
    exact ⟨l₁, l₂, e₁, e₂, fun he => (hl [] [] (by rw [he])).1⟩
  · cases hif

/-- **Two leakage runs before the inlining of the tagged calls give two runs of its result
    without calls, with equal events from equal events.** `fieldInlineStep_leakRunC` at the
    empty call environment, at which `NFProg.leakRunMC` is `NFProg.leakRun`. -/
theorem fieldInlineStep_leakRun {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hf : (fieldInlineStep Γ ts).run p = some q)
    {V₁ V₂ : Valuation Γ} {r₁ r₂ : Valuation (d := jasminDialect) ts × List CTLeak}
    (h₁ : NFProg.leakRunMC (jLeakModel Pj) (fieldEnv CallEnv.empty) fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC (jLeakModel Pj) (fieldEnv CallEnv.empty) fuel p V₂ = some r₂) :
    ∃ l₁ l₂, NFProg.leakRun (jLeakModel Pj) fuel q V₁ = some (r₁.1, l₁) ∧
      NFProg.leakRun (jLeakModel Pj) fuel q V₂ = some (r₂.1, l₂) ∧
      (r₁.2 = r₂.2 → l₁ = l₂) := by
  obtain ⟨l₁, l₂, e₁, e₂, hl⟩ := fieldInlineStep_leakRunC hV CallEnv.empty fuel hf h₁ h₂
  rw [NFProg.leakRunMC_empty, NFProg.leakRunM_eq_leakRun] at e₁ e₂
  exact ⟨l₁, l₂, e₁, e₂, hl⟩

/-- **The constant-time step certificate of the inlining of the tagged calls**, from
    `fieldInlineStep_leakRunC`: from the leakage semantics at `fieldEnv E'` to the leakage
    semantics at `E'`; equal source events give equal target events. -/
def fieldInlineCTStep {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (fieldInlineStep Γ ts).run
      (leakSemNFC (jLeakModel Pj) (fieldEnv E') fuel Γ ts).twoRun
      (leakSemNFC (jLeakModel Pj) E' fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨l₁, l₂, e₁, e₂, hl⟩ := fieldInlineStep_leakRunC hV E' fuel hf hr₁ hr₂
    exact ⟨l₁, l₂, by simp only [leakSemNFC, e₁, Option.map_some],
      by simp only [leakSemNFC, e₂, Option.map_some], hl⟩

/-- **The constant-time step certificate of the field dialect step**, from
    `fieldDialectStep_leakRunC`: from the leakage semantics at `fieldEnv E'` to the leakage
    semantics at `E'`; equal source events give equal target events. -/
def fieldDialectCTStep {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (fieldDialectStep Γ ts).run
      (leakSemNFC (jLeakModel Pj) (fieldEnv E') fuel Γ ts).twoRun
      (leakSemNFC (jLeakModel Pj) E' fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨l₁, l₂, e₁, e₂, hl⟩ := fieldDialectStep_leakRunC hV E' fuel hf hr₁ hr₂
    exact ⟨l₁, l₂, by simp only [leakSemNFC, e₁, Option.map_some],
      by simp only [leakSemNFC, e₂, Option.map_some], hl⟩

/-- The constant-time step certificate of `lowerSelects` at the leakage semantics at the call
    environment `E'`, from `NFProg.lowerSelects_ctRelC`. -/
def lowerSelectsCTStepC {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (E' : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (lowerSelectsStep Γ ts).run (leakSemNFC (jLeakModel Pj) E' fuel Γ ts).twoRun
      (leakSemNFC (jLeakModel Pj) E' fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, s₂, hs₁, hs₂, -, -, he⟩ := NFProg.lowerSelects_ctRelC (jLeakModel Pj) E'
      (jasminQuiet_opLeak_indep hc hq) (jasminSel_kind hc) fuel p V₁ V₂ r₁ r₂ hr₁ hr₂
    exact ⟨s₁.2, s₂.2, by simp only [leakSemNFC, hs₁, Option.map_some],
      by simp only [leakSemNFC, hs₂, Option.map_some], he⟩

/-- The constant-time step certificate of `rangeNF` at the leakage semantics at the call
    environment `E'`, from `rangeNF_ctRelC` under quiet register arithmetic. -/
def rangeCTStepC {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (E' : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (rangeNFStep Γ ts).run (leakSemNFC (jLeakModel Pj) E' fuel Γ ts).twoRun
      (leakSemNFC (jLeakModel Pj) E' fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, -, hs₁, -⟩ := rangeNF_ctRelC hq E' fuel p V₁ V₁ r₁ r₁ hr₁ hr₁ rfl
    obtain ⟨s₂, -, hs₂, -⟩ := rangeNF_ctRelC hq E' fuel p V₂ V₂ r₂ r₂ hr₂ hr₂ rfl
    refine ⟨s₁.2, s₂.2, by simp only [leakSemNFC, hs₁, Option.map_some],
      by simp only [leakSemNFC, hs₂, Option.map_some], fun he => ?_⟩
    obtain ⟨t₁, t₂, ht₁, ht₂, -, -, het⟩ := rangeNF_ctRelC hq E' fuel p V₁ V₂ r₁ r₂ hr₁ hr₂ he
    rw [hs₁, Option.some.injEq] at ht₁
    rw [hs₂, Option.some.injEq] at ht₂
    rw [ht₁, ht₂, het]

/-! ## The constant-time certificate of the chain -/

/-- Register arithmetic is quiet at leakage parameters of `jasminDialect` with no
    variable-time operation. -/
theorem regArith_quiet_of_opVT {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (bop : JasminBinOp) (w : Nat) : (jLeakModel Pj).kind (.regArith bop w) = .quiet := by
  simp only [jLeakModel, jKind, hV]

/-- Register constants are quiet at leakage parameters of `jasminDialect` with no
    variable-time operation. -/
theorem regConst_quiet_of_opVT {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (w n : Nat) : (jLeakModel Pj).kind (.regConst w n) = .quiet := by
  simp only [jLeakModel, jKind, hV]

/-- Every tuple operation, also under `named`, is quiet in `nfKind`. -/
theorem nfKind_of_opIsTuple (op : NfOp) (h : NFFlattenTuples.opIsTuple op = true) :
    nfKind op = .quiet := by
  induction op <;> simp_all [NFFlattenTuples.opIsTuple, nfKind]

/-- **Every tuple operation is quiet in `nfLeakModel`.** -/
theorem tupleQuiet_nfLeakModel : NFFlattenTuples.TupleQuiet nfLeakModel :=
  nfKind_of_opIsTuple

/-- **Every tuple operation is quiet in `nfLeakModelL D`.** -/
theorem tupleQuiet_nfLeakModelL (D : List ExtDecl) :
    NFFlattenTuples.TupleQuiet (nfLeakModelL D) := fun op h => by
  simp only [nfLeakModelL, nfKind_of_opIsTuple op h]

/-- The constant-time step certificate of tuple flattening `flatSameStep` at a leakage model
    in which every tuple operation is quiet: the identity on the inputs, with the events of
    the source run (`flatSame_leakRunM`). -/
def flatSameCTStep (bi : Builtins) (fuel : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy)
    (M : LeakModel nfDialect) (hM : NFFlattenTuples.TupleQuiet M) :
    StepCert (flatSameStep Γ ts).run (srcLeakSem bi fuel Γ ts M).twoRun
      (srcLeakSem bi fuel Γ ts M).twoRun :=
  stepCertOfLeak _ _ Eq fun {_ _ _ _ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    exact ⟨l₁, l₂,
      (flatSame_leakRunM M hM (CatCrypt.Crypto.Hax.ImpToNF.tableOf bi) fuel hf _).trans h₁,
      (flatSame_leakRunM M hM (CatCrypt.Crypto.Hax.ImpToNF.tableOf bi) fuel hf _).trans h₂,
      _root_.id⟩

/-- **The constant-time certificate of the chain with declarations**, at the leakage
    parameters `P` of `catCryptDialect` with no variable-time operation, the parameters `Pj`
    of `jasminDialect` compatible with them and with no variable-time operation, a builtin
    table `bi` that is a subtable of the `u64` table, answers the tagged heads below `2⁶⁴` by
    their arms and is the `u64` table at the wide tagged heads, declarations `D` of no name
    `index` or `array_update` on which `bi` and `catEnvOf E'` agree, and the fuel `fuel`: one
    leaf per step of `extChain`. The source semantics is that of the leakage model
    `nfLeakModelL D`, in which a call of a tagged field head or of a declared name is
    quiet. The steps up to the
    montify step run at the call environments `catEnvOf (fieldEnv E')` and `fieldEnv E'`,
    the inlining step from `fieldEnv E'` to `E'`, and the later steps at `E'`. -/
def extChainCTCert {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hV : ∀ op, Pj.opVT op = none) {bi : Builtins}
    (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi) (hW : FieldLevel.FieldCallsWideEq bi)
    {D : List ExtDecl}
    (E' : CallEnv jasminDialect) (hD : ExtAgree bi (catEnvOf E') D)
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update") (fuel : Nat)
    (Γ : Ctxt nfDialect) (t : NfTy) :
    CTCert (extChain D Γ t) (srcLeakSem bi fuel Γ [t] (nfLeakModelL D))
      (leakSemNFC (jLeakModel Pj) E' fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) :=
  have hq := regArith_quiet_of_opVT hV
  have hK := regConst_quiet_of_opVT hV
  .cons (flatSameCTStep bi fuel Γ [t] (nfLeakModelL D) (tupleQuiet_nfLeakModelL D))
    (fun _ _ h => h) <|
  .cons (outTyCTStep bi fuel Γ t (nfLeakModelL D)) (fun _ _ h => h) <|
    .cons (dceCTStep bi fuel Γ [t] (nfLeakModelL D)) (fun _ _ h => h) <|
    .cons (extCallCTStep hP hbi hF hW hD hN fuel Γ [t]) (fun _ _ h => h) <|
    .cons (aegraphCTStepC catRules catRules_indep _ fuel (Γ.map catTy) [catTy t])
      (fun _ _ h => h) <|
    .cons (mapCTStepC hc (fieldEnv E') fuel (Γ.map catTy) [catTy t])
      (fun _ _ h => h) <|
    .cons (montifyCTStep hq hK E' fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)])
      (fun _ _ h => h) <|
    .cons (fieldDialectCTStep hV E' fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)])
      (fun _ _ h => h) <|
    .cons (lowerSelectsCTStepC hc hq E' fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)])
      (fun _ _ h => h) <|
    .cons (rangeCTStepC hq E' fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)])
      (fun _ _ h => h) <|
    .cons (aegraphCTStepC jasminRules (jasminRules_indep hq) E' fuel (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]) (fun _ _ h => h) <|
    .nil _

/-- **Constant time through the chain with declarations.** Two runs of the source `p` at the
    fuel `fuel` from valuations in range whose events are equal without the leaf calls of
    tagged field heads and of the names that `D` declares (`stripDecl D`) give two runs
    `NFProg.leakRunMC` at the call environment `E'` of the program `extChain` returns at the
    same fuel, from the transported valuations, with equal events, under
    `ExtAgree bi (catEnvOf E') D` and declarations of no name `index` or `array_update`; this
    is `PassChain.CTCert.ct` at `extChainCTCert`. -/
theorem extChain_ctC {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hV : ∀ op, Pj.opVT op = none) {bi : Builtins}
    (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi) (hW : FieldLevel.FieldCallsWideEq bi)
    {D : List ExtDecl}
    (E' : CallEnv jasminDialect) (hD : ExtAgree bi (catEnvOf E') D)
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update") (fuel : Nat)
    {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t])
    {pj : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChain D Γ t).run p = some pj) (V₁ V₂ : Valuation Γ)
    (hin₁ : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V₁))
    (hin₂ : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V₂))
    {r₁ r₂ : Valuation (d := nfDialect) [t] × List CTLeak}
    (h₁ : nfLeakRun bi fuel p V₁ = some r₁) (h₂ : nfLeakRun bi fuel p V₂ = some r₂)
    (he : stripDecl D r₁.2 = stripDecl D r₂.2) :
    ∃ m, (NFProg.leakRunMC (jLeakModel Pj) E' fuel pj (ctMapValD (mapVal V₁))).map
        Prod.snd = some m ∧
      (NFProg.leakRunMC (jLeakModel Pj) E' fuel pj (ctMapValD (mapVal V₂))).map
        Prod.snd = some m := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ :=
    (extChainCTCert hP hc hV hbi hF hW E' hD hN fuel Γ t).ct
    (W₁ := ctMapValD (mapVal V₁)) (W₂ := ctMapValD (mapVal V₂)) h
    ⟨(V₁, V₂), ⟨rfl, rfl⟩, (V₁, V₂), ⟨rfl, rfl⟩, (V₁, V₂), ⟨rfl, rfl⟩,
      (mapVal V₁, mapVal V₂),
      ⟨⟨rfl, hin₁⟩, ⟨rfl, hin₂⟩⟩, (mapVal V₁, mapVal V₂), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩, rfl⟩
    (show (nfLeakRunL D bi fuel p V₁).map Prod.snd = some (stripDecl D r₁.2) by
      rw [nfLeakRunL_eq, h₁]; rfl)
    (show (nfLeakRunL D bi fuel p V₂).map Prod.snd = some (stripDecl D r₂.2) by
      rw [nfLeakRunL_eq, h₂]; rfl) he
  exact ⟨m₁, hm₁, hm ▸ hm₂⟩

/-- At declarations of tagged heads the chain is the chain at no declarations: the
    declarations of the translation are those of the tagged calls of the program in both
    (`fieldDeclsFor_of_tagged`). -/
theorem extChain_of_tagged {D : List ExtDecl} (hT : ∀ d ∈ D, (fieldTag? d.name).isSome = true)
    (Γ : Ctxt nfDialect) (t : NfTy) : extChain D Γ t = extChain [] Γ t := by
  have hs : extCallStep D Γ [t] = extCallStep [] Γ [t] := by
    unfold extCallStep
    congr 1
    funext p
    rw [fieldDeclsFor_of_tagged hT p,
      fieldDeclsFor_of_tagged (D := []) (fun _ hd => nomatch hd) p]
  unfold extChain extChainCore
  rw [hs]

/-- **Constant time through the chain with declarations of tagged heads.** Two runs of the
    source `p` at the fuel `fuel` from valuations in range whose events are equal without the
    leaf calls of tagged field heads (`stripField`) give two runs
    `NFProg.leakRun` of the program `extChain` returns at the same fuel, from the transported
    valuations, with equal events: `extChain_ctC` at no declarations
    (`extChain_of_tagged`) and the empty call environment. -/
theorem extChain_ct {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hV : ∀ op, Pj.opVT op = none) {bi : Builtins}
    (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi) (hW : FieldLevel.FieldCallsWideEq bi)
    {D : List ExtDecl}
    (hT : ∀ d ∈ D, (fieldTag? d.name).isSome = true) (fuel : Nat) {Γ : Ctxt nfDialect}
    {t : NfTy} (p : NFProg nfDialect Γ [t])
    {pj : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChain D Γ t).run p = some pj) (V₁ V₂ : Valuation Γ)
    (hin₁ : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V₁))
    (hin₂ : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V₂))
    {r₁ r₂ : Valuation (d := nfDialect) [t] × List CTLeak}
    (h₁ : nfLeakRun bi fuel p V₁ = some r₁) (h₂ : nfLeakRun bi fuel p V₂ = some r₂)
    (he : stripField r₁.2 = stripField r₂.2) :
    ∃ m, (NFProg.leakRun (jLeakModel Pj) fuel pj (ctMapValD (mapVal V₁))).map Prod.snd =
        some m ∧
      (NFProg.leakRun (jLeakModel Pj) fuel pj (ctMapValD (mapVal V₂))).map Prod.snd =
        some m := by
  rw [extChain_of_tagged hT] at h
  obtain ⟨m, hm₁, hm₂⟩ := extChain_ctC hP hc hV hbi hF hW CallEnv.empty
    (extAgree_nil bi _) (fun _ hd => nomatch hd) fuel p h V₁ V₂ hin₁ hin₂ h₁ h₂
    (by rw [stripDecl_nil_eq, stripDecl_nil_eq]; exact he)
  rw [NFProg.leakRunMC_empty, NFProg.leakRunM_eq_leakRun] at hm₁ hm₂
  exact ⟨m, hm₁, hm₂⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
