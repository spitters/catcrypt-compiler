/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ExtChainCT
public import CatCrypt.Crypto.Hax.ImpToNFLeak

/-!
# Constant time of the program of the chain from source constant time

The front half of the constant-time statement `haxc_ct_proved_all` of `compileA`. Its
hypothesis is `HaxToNFCT s σ m`: the program of the translation `haxToNF σ m`, in which the
calls of the functions of the module are inlined to the depth of the module, is constant time
in the leakage model `nfLeakModelQ` for the parameter labels of the secrecy record `s`: two
leakage runs from valuations agreeing on the public parameters have equal events once the
leaf calls of tagged field heads are removed (`stripField`). A tagged field call is compiled
to a field body whose constant time is proved separately (`FieldLevel.fieldBody_nfCTRel`),
and the chain removes its events. The composition is:

1. the runs of the translation: the program `impToNF` emits runs at the builtins that answer
   a call of a function of the module by the run of its body (`impToNF_leak`), and the
   inlining keeps the run (`denote_crateInline?`): `haxToNF_leakRun`;
2. the chain `extChain` at no declaration, from events equal without the field calls:
   `extChain_ct`;
3. the transport of the labels: every valuation of the parameters of a layout is the mapped
   valuation of a valuation in range (`mapVal_surj_abi`, `inRange_abi`), and agreement of
   mapped valuations on the public positions of `nfLabels s` is agreement on the public
   positions of `entryLabels (paramLevelOf s)` (`pubEqV_entryLabels_of_mapVal`).

For a module without linked function, callee or depth, a result of `haxToNF` is a result of
`nfSrcProg` (`haxToNF_eq_nfSrcProg`), and `HaxToNFCT` follows from source constant time
`SourceCTNF` of the body `nfBody (bindConsts σ.consts m.entry)` the front reads, for the level table
`levelsOf s`, with one fuel at which the body runs to a value from the environment of every
valuation of the parameters (`haxToNFCT_of_sourceCT`, through `impToNF_nfCTRel_params`). The
tagged field calls are those the `u64` table answers at a modulus below `2⁶⁴`.

## Main results

* `haxModule_eq_single`, `haxToNF_eq_nfSrcProg` — a module without callee, depth or linked
  function is the module of its entry, and its translation is a result of `nfSrcProg`.
* `abiEntry_kinds`, `inRange_abi`, `mapVal_surj_abi`, `pubEqV_entryLabels_of_mapVal` — the
  parameters of a layout and their valuations.
* `HaxToNFCT`, `haxToNFCT_of_sourceCT` — constant time of the translation of a module, and
  its derivation from source constant time for a single function.
* `haxToNFCTB`, `haxToNFCT_of_haxToNFCTB` — the level check of the translation of a module
  in the leakage model `nfLeakModelQ`, and its soundness for `HaxToNFCT`.
* `crateBi_prepared_of_fns_nil`, `haxToNF_leakRun` — the runs of the translation of a module
  without linked function, through the inlining.
* `nfCT_of_haxToNFCT` — the program the chain returns for a constant-time program with runs
  from the valuations of a predicate is constant time for the transported labels of `s` at
  every fuel, on the valuations of that predicate.
* `HaxToNFCTL`, `haxToNFCTBL`, `haxToNFCTL_of_haxToNFCTBL`, `haxToNFCTL_of_linked_nil` —
  constant time of the translation of a module with linked functions in the leakage model
  `nfLeakModelL` at its declared procedures, in which a call of a linked function is quiet,
  its level check, and its derivation from `HaxToNFCT` without linked function.
* `HaxToNFCTLOn`, `haxToNFCTLOn_of_haxToNFCTL` — that constant time on the entry valuations
  of a predicate, and its derivation from `HaxToNFCTL`.
* `HaxToNFCTD`, `haxToNFCTD_of_sourceCTD`, `haxToNFCTLOn_of_haxToNFCTD` — constant time of
  the translation modulo declassification, its derivation from source constant time modulo
  declassification for a single function (`impToNF_nfCTRelD`), and constant time on the
  valuations whose source runs declassify one sequence.
* `haxToNF_leakRunL`, `nfCT_of_haxToNFCTL` — the runs of the translation at the table of the
  linked functions, and constant time of the program of the chain at the declared
  procedures, at a call environment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.CT (levelsOf CTLeak)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnv impToNF hax64SigOf Out SourceCTNF
  entryEnvOf entryEnvOf_rel entryLabels paramLevelOf impToNF_leak impToNF_nfCTRel_params
  nfLeakModelQ nfLeakRunQ nfLeakRunQ_eq crateBi crateBi_typedCalls PDenP tableOf SrcDeclIs
  srcLeakNFD impToNF_nfCTRelD pubEqV_entryLabels_levelsOf)
open CatCrypt.Crypto.Hax (SourceCTDOf)
open CatCrypt.Crypto.Hax.NFInline (denote_crateInline? crateBi_nil)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)
open _root_.Hax (TExpr Value Env denote')
open Ctxt (Var Valuation)

/-! ## The module of the entry function -/

/-- **A module without callee, depth or linked function is the module of its entry
    function.** -/
theorem haxModule_eq_single {m : HaxModule} (hfns : m.fns = []) (hdep : m.depth = 0)
    (hlk : m.linked = []) : m = HaxModule.single m.entry := by
  obtain ⟨e, fns, dep, lk⟩ := m
  simp only at hfns hdep hlk
  subst hfns hdep hlk
  rfl

/-- **A translation of a module without callee, depth or linked function** is a result of the
    source program `nfSrcProg` of its entry with the constants of the layout bound. -/
theorem haxToNF_eq_nfSrcProg (σ : AbiLayout) {m : HaxModule} (hfns : m.fns = [])
    (hdep : m.depth = 0) (hlk : m.linked = [])
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q) : nfSrcProg σ (bindConsts σ.consts m.entry) = some q := by
  obtain ⟨e, fns, dep, lk⟩ := m
  simp only at hfns hdep hlk
  subst hfns hdep hlk
  change haxToNF σ (HaxModule.single e) = some q at hq
  rw [haxToNF_single] at hq
  exact (Option.filter_eq_some_iff.mp hq).1

/-! ## The parameters of a layout -/

/-- The type of every parameter of a layout is the type `abiKindArr` of its kind. -/
theorem abiEntry_kinds (σ : AbiLayout) : ∀ p ∈ abiEntry σ, ∃ k, p.2 = abiKindArr k := by
  intro p hp
  simp only [abiEntry, abiParamsArr, List.mem_reverse, List.mem_map] at hp
  obtain ⟨a, -, rfl⟩ := hp
  exact ⟨a.kind, rfl⟩

/-- A value of the type of a parameter kind is in range. -/
theorem inRange_abiKind (k : ArgKind) (y : (abiKindArr k).denote) : InRange (abiKindArr k) y := by
  cases k with
  | scalar => trivial
  | words n => exact fun i => BitVec.isLt _

/-- Every value of the mapped type of a parameter kind is the mapped value of a value. -/
theorem toCatVal_abi_surj (k : ArgKind) (x : (catTy (abiKindArr k)).denote) :
    ∃ y : (abiKindArr k).denote, toCatVal (abiKindArr k) y = x := by
  cases k with
  | scalar => exact ⟨x, rfl⟩
  | words n =>
      refine ⟨x, ?_⟩
      funext i
      simp [toCatVal, abiKindArr]

/-- The map of values of the type of a parameter kind is injective. -/
theorem toCatVal_abi_inj (k : ArgKind) {y₁ y₂ : (abiKindArr k).denote}
    (h : toCatVal (abiKindArr k) y₁ = toCatVal (abiKindArr k) y₂) : y₁ = y₂ := by
  cases k with
  | scalar => exact h
  | words n =>
      funext i
      have := congrFun h i
      simpa [toCatVal, abiKindArr] using this

/-- **A valuation of parameters of layout kinds is in range.** -/
theorem inRange_abi : ∀ (ps : List (String × NfTy)), (∀ p ∈ ps, ∃ k, p.2 = abiKindArr k) →
    ∀ (V : Valuation (entryCtx ps)) (s : NfTy) (v : Var (entryCtx ps) s),
      InRange s (v.lookup V)
  | [], _, _, _, v => nomatch v
  | (x, t) :: ps, hps, .cons y V, s, v => by
      obtain ⟨k, hk⟩ := hps (x, t) List.mem_cons_self
      simp only at hk
      subst hk
      cases v with
      | here => exact inRange_abiKind k y
      | there v =>
          exact inRange_abi ps (fun p hp => hps p (List.mem_cons_of_mem _ hp)) V s v

/-- **Every valuation of the mapped parameters of layout kinds is the mapped valuation of a
    valuation of the parameters.** -/
theorem mapVal_surj_abi : ∀ (ps : List (String × NfTy)), (∀ p ∈ ps, ∃ k, p.2 = abiKindArr k) →
    ∀ X : Valuation (d := catCryptDialect) ((entryCtx ps).map catTy),
      ∃ V : Valuation (entryCtx ps), mapVal V = X
  | [], _, .nil => ⟨.nil, rfl⟩
  | (x, t) :: ps, hps, .cons z X => by
      obtain ⟨k, hk⟩ := hps (x, t) List.mem_cons_self
      simp only at hk
      subst hk
      obtain ⟨y, hy⟩ := toCatVal_abi_surj k z
      obtain ⟨V, hV⟩ := mapVal_surj_abi ps (fun p hp => hps p (List.mem_cons_of_mem _ hp)) X
      exact ⟨.cons y V, by rw [← hy, ← hV]; rfl⟩

/-- **The labels of a secrecy record through the map of valuations.** For parameters of
    layout kinds, valuations whose mapped valuations agree on the positions `nfLabels s`
    marks public agree on the positions `entryLabels (paramLevelOf s)` marks public: the two
    label lists give each parameter the same level, and the map of values of a parameter
    kind is injective. -/
theorem pubEqV_entryLabels_of_mapVal (s : _root_.Hax.FnSecrecy) :
    ∀ (ps : List (String × NfTy)), (∀ p ∈ ps, ∃ k, p.2 = abiKindArr k) →
    ∀ (V₁ V₂ : Valuation (entryCtx ps)), PubEqV (nfLabels s ps) (mapVal V₁) (mapVal V₂) →
      PubEqV (entryLabels (paramLevelOf s) ps) V₁ V₂
  | [], _, _, _, _ => fun _ v => nomatch v
  | (x, t) :: ps, hps, .cons y₁ V₁, .cons y₂ V₂, h => by
      obtain ⟨k, hk⟩ := hps (x, t) List.mem_cons_self
      simp only at hk
      subst hk
      intro t' v hv
      cases v with
      | here => exact toCatVal_abi_inj k (h _ .here hv)
      | there v =>
          exact pubEqV_entryLabels_of_mapVal s ps
            (fun p hp => hps p (List.mem_cons_of_mem _ hp)) V₁ V₂
            (fun t'' w hw => h t'' (.there w) hw) t' v hv

/-! ## The translation of a module through the inlining -/

/-- **Constant time of the translation of a module**, for the secrecy record `s`: for every
    result `q` of `haxToNF σ m`, the program `q.2`, in which the calls of the functions of the
    module are inlined, is constant time at every fuel in the leakage model `nfLeakModelQ`
    with quiet field calls, at the table `hax64WExit`, relative to the runs that succeed, for
    the labels `entryLabels (paramLevelOf s)` of the parameters of `σ`: two valuations
    agreeing on the public parameters, from which the program runs to results, give equal
    events. -/
def HaxToNFCT (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule) : Prop :=
  ∀ q : (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]), haxToNF σ m = some q →
    ∀ (tf : Nat) (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
      (r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak),
      PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ →
      nfLeakRunQ hax64WExit tf q.2 V₁ = some r₁ → nfLeakRunQ hax64WExit tf q.2 V₂ = some r₂ →
      r₁.2 = r₂.2

/-- **The level check of the translation of a module** for the secrecy record `s`: the
    checker `NFProg.levelCheck'` in the leakage model `nfLeakModelQ`, in which the calls of
    tagged field heads are quiet, on the program of `haxToNF σ m` at the labels
    `entryLabels (paramLevelOf s)` of the parameters of `σ`; `false` when the translation
    refuses the module. -/
def haxToNFCTB (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule) : Bool :=
  match haxToNF σ m with
  | some q =>
      (Dialects.NFLeak.NFProg.levelCheck' nfLeakModelQ q.2
        (entryLabels (paramLevelOf s) (abiEntry σ))).isSome
  | none => false

/-- **The level check of the translation gives its constant time**: when `haxToNFCTB`
    accepts, `HaxToNFCT s σ m` holds, by the soundness of the checker relative to the runs
    that succeed (`NFProg.nfCTRel_of_levelCheck'`) at the leaf table of `hax64WExit`. -/
theorem haxToNFCT_of_haxToNFCTB (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule)
    (h : haxToNFCTB s σ m = true) : HaxToNFCT s σ m := by
  intro q hq tf
  unfold haxToNFCTB at h
  rw [hq] at h
  exact @Dialects.NFLeak.NFProg.nfCTRel_of_levelCheck' nfDialect _ _ _ _
    (nfDenote (tableOf hax64WExit)) nfLeakModelQ tf _ _ q.2 _ h

/-- **Source constant time of a single function gives constant time of its translation.**
    For a module without callee, depth or linked function, every parameter of `σ` listed in
    `s`, the body `nfBody (bindConsts σ.consts m.entry)` the front reads constant time at the
    source for `levelsOf s` modulo the field calls (`SourceCTNF`) and running at the fuel `F`
    to a value from the environment of every valuation of the parameters, the translation is
    constant time (`HaxToNFCT`). A translation is a result of `nfSrcProg`
    (`haxToNF_eq_nfSrcProg`) and
    the statement is `impToNF_nfCTRel_params`. -/
theorem haxToNFCT_of_sourceCT (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) {m : HaxModule}
    (hfns : m.fns = []) (hdep : m.depth = 0) (hlk : m.linked = [])
    (hps : ∀ p ∈ abiEntry σ, ∃ b, (p.1, b) ∈ s.params)
    (hct : SourceCTNF hax64WExit (levelsOf s) (nfBody (bindConsts σ.consts m.entry)))
    (F : Nat)
    (hterm : ∀ V : Valuation (entryCtx (abiEntry σ)), ∃ v env',
      (denote' hax64WExit F (nfBody (bindConsts σ.consts m.entry))).run
        (entryEnvOf (abiEntry σ) V) = (.val v, env')) :
    HaxToNFCT s σ m := by
  rintro ⟨t, qp⟩ hq tf
  replace hq := haxToNF_eq_nfSrcProg σ hfns hdep hlk hq
  unfold nfSrcProg at hq
  split at hq
  · obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hq
    cases he
    exact impToNF_nfCTRel_params hax64WExit hax64SigOf
      CatCrypt.Crypto.Hax.hax64WExit_typedCalls CatCrypt.Crypto.Hax.repeatCalls_hax64WExit s _
      hps hct ho F hterm tf
  · cases hq

/-- The builtins with the prepared callees of a module without callee are the base
    builtins. -/
theorem crateBi_prepared_of_fns_nil {m : HaxModule} (hfns : m.fns = []) (bi : _root_.Hax.Builtins)
    (fuelC n : Nat) : crateBi (m.prepared nfBody) bi fuelC n = bi := by
  rw [HaxModule.prepared, hfns, List.map_nil, crateBi_nil]

/-- **The runs of the translation of a module.** Let the module `m` have no linked function
    and the body `nfBody (bindConsts σ.consts m.entry)` the front reads run at the fuel `F`,
    at the builtins `crateBi (m.prepared nfBody) hax64WExit fuelC m.depth` that answer a call
    of a function of the module by the run of its prepared body, to a value from the
    environment of the valuation `V` of the parameters. Then for every result `q` of
    `haxToNF σ m`, the program `q.2` with the calls inlined has a leakage run at the table
    `hax64WExit` from `V`, at every target fuel from some fuel on. The program `impToNF`
    emits runs at the builtins with the callees from some fuel on (`impToNF_leak`), and the
    inlining keeps that run, at the table `hax64WExit` (`denote_crateInline?`). -/
theorem haxToNF_leakRun (σ : AbiLayout) {m : HaxModule} (hlk : m.linked = []) (F fuelC : Nat)
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]} (hq : haxToNF σ m = some q)
    (V : Valuation (entryCtx (abiEntry σ)))
    (hterm : ∃ v env',
      (denote' (crateBi (m.prepared nfBody) hax64WExit fuelC m.depth) F
        (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
          (.val v, env')) :
    ∃ N, ∀ tf, N ≤ tf → ∃ r, nfLeakRun hax64WExit tf q.2 V = some r := by
  obtain ⟨t, qp⟩ := q
  obtain ⟨hfs, -, -, p, hs, hi⟩ := haxToNF_eq_some hq
  have hfR := crateArrOk_find_repeat hfs
  rw [HaxModule.linkedFns_of_linked_nil hlk, List.append_nil] at hs
  simp only [HaxModule.inline?, HaxModule.linkSig_of_linked_nil hlk] at hi
  unfold nfSrcProgC at hs
  split at hs
  · obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨v, env', hr⟩ := hterm
    obtain ⟨x, ⟨N, hx⟩, -⟩ := impToNF_leak _ _
      (crateBi_typedCalls _ _ _ CatCrypt.Crypto.Hax.hax64WExit_typedCalls fuelC m.depth)
      (CatCrypt.Crypto.Hax.ImpToNF.crateBi_repeatCalls _ _
        CatCrypt.Crypto.Hax.repeatCalls_hax64WExit hfR fuelC m.depth) ho
      (entryEnvOf_rel _ V) hr
    refine ⟨N, fun tf htf => ?_⟩
    have hfst : ∀ (bi : _root_.Hax.Builtins) (p : NFProg nfDialect (entryCtx (abiEntry σ)) [o.t]),
        (nfLeakRun bi tf p V).map Prod.fst = PDenP bi tf p V := fun bi p =>
      @Dialects.NFLeak.NFProg.leakRunM_fst nfDialect _ _ _ _ (nfDenote (tableOf bi))
        nfLeakModel tf _ _ p V
    have hd : PDenP (crateBi (m.prepared nfBody) hax64WExit fuelC m.depth) tf o.prog V =
        some (HVector.cons x .nil) := by
      rw [← hfst, hx tf htf]
      rfl
    have hd' := denote_crateInline? (m.prepared nfBody) hax64WExit
      CatCrypt.Crypto.Hax.hax64WExit_typedCalls CatCrypt.Crypto.Hax.repeatCalls_hax64WExit hfR
      fuelC tf m.depth hi hd
    rw [← hfst] at hd'
    obtain ⟨r, hr', -⟩ := Option.map_eq_some_iff.mp hd'
    exact ⟨r, hr'⟩
  · cases hs

/-! ## Constant time of the program of the chain -/

/-- **Constant time of the program of the chain from constant time of the translation.** Let
    `Q` be a predicate on the valuations of the lowered parameters of `σ`. Let the program
    `p` of `nfDialect` over the parameters of `σ` have a leakage run at the table
    `hax64WExit` at every fuel from every valuation whose lowered valuation
    `ctMapValD (mapVal V)` satisfies `Q`, and be constant time in the leakage model
    `nfLeakModelQ` with quiet field calls for the labels `entryLabels (paramLevelOf s)`, at
    every fuel, relative to the runs that succeed. Then the program the chain `extChain` at
    declarations of tagged heads returns for `p` is constant time at every fuel for the
    transported labels `mapLabels (nfLabels s (abiEntry σ))`, at the owned leakage
    parameters, on the valuations that satisfy `Q`. -/
theorem nfCT_of_haxToNFCT (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) {t : NfTy}
    (p : NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (Q : Valuation (d := jasminDialect) (mapCtx ((entryCtx (abiEntry σ)).map catTy)) → Prop)
    (hrun : ∀ (V : Valuation (entryCtx (abiEntry σ))) (tf : Nat), Q (ctMapValD (mapVal V)) →
      ∃ r, nfLeakRun hax64WExit tf p V = some r)
    (hct : ∀ (tf : Nat) (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
      (r₁ r₂ : Valuation (d := nfDialect) [t] × List CTLeak),
      PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ →
      nfLeakRunQ hax64WExit tf p V₁ = some r₁ → nfLeakRunQ hax64WExit tf p V₂ = some r₂ →
      r₁.2 = r₂.2)
    {D : List ExtDecl} (hT : ∀ d ∈ D, (_root_.Hax.FieldTag.fieldTag? d.name).isSome = true)
    {pj : NFProg jasminDialect (nfCtx σ) [mapTy (catTy t)]}
    (hpj : (extChain D _ t).run p = some pj) (fuel : Nat) :
    ∀ W₁ W₂ : Valuation (d := jasminDialect) (mapCtx ((entryCtx (abiEntry σ)).map catTy)),
      Q W₁ → Q W₂ → PubEqV (mapLabels (nfLabels s (abiEntry σ))) W₁ W₂ →
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) fuel pj W₁).map Prod.snd
        = (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) fuel pj W₂).map
          Prod.snd := by
  intro W₁ W₂ hQ₁ hQ₂ hW
  have hk := abiEntry_kinds σ
  obtain ⟨V₁, hV₁⟩ := mapVal_surj_abi _ hk (ctBackV W₁)
  obtain ⟨V₂, hV₂⟩ := mapVal_surj_abi _ hk (ctBackV W₂)
  have hpub : PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ :=
    pubEqV_entryLabels_of_mapVal s _ hk V₁ V₂ (by rw [hV₁, hV₂]; exact pubEqV_ctBackV hW)
  obtain ⟨r₁, h₁⟩ := hrun V₁ fuel (by rw [hV₁, ctMapValD_ctBackV]; exact hQ₁)
  obtain ⟨r₂, h₂⟩ := hrun V₂ fuel (by rw [hV₂, ctMapValD_ctBackV]; exact hQ₂)
  have he := hct fuel V₁ V₂ _ _ hpub
    ((nfLeakRunQ_eq _ _ _ _).trans (congrArg _ h₁)) ((nfLeakRunQ_eq _ _ _ _).trans (congrArg _ h₂))
  obtain ⟨m, hm₁, hm₂⟩ := extChain_ct noVT_owned leakCompat_owned (fun _ => rfl)
    CatCrypt.Crypto.Hax.hax64WExit_subTable fieldCalls_hax64WExit fieldCallsWideEq_hax64WExit
    hT fuel
    p hpj V₁ V₂ (inRange_abi _ hk V₁) (inRange_abi _ hk V₂) h₁ h₂ he
  rw [← ctMapValD_ctBackV W₁, ← ctMapValD_ctBackV W₂, ← hV₁, ← hV₂, hm₁, hm₂]

/-! ## Modules with linked functions -/

/-- The declared procedures of a module at two tables declare the same names, so their
    declared events are the same. -/
theorem stripDecl_linkedDecls (m : HaxModule) (bi bi' : _root_.Hax.Builtins)
    (l : List CTLeak) : stripDecl (linkedDecls m bi) l = stripDecl (linkedDecls m bi') l := by
  unfold stripDecl
  congr 1
  funext e
  cases e with
  | vtCall f _ =>
      simp only [isDeclEvent, linkedDecls, List.any_flatMap, List.any_map]
      rfl
  | _ => rfl

/-- The declared procedures of a module whose linked functions have names that pass
    `linkNameOk` are named neither `index` nor `array_update`. -/
theorem linkedDecls_ne_index {m : HaxModule} (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true)
    (bi : _root_.Hax.Builtins) :
    ∀ d ∈ linkedDecls m bi, d.name ≠ "index" ∧ d.name ≠ "array_update" := by
  intro d hd
  obtain ⟨l, hl, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨as, -, rfl⟩ := List.mem_map.mp hd
  have h := hlk l (List.mem_filter.mp hl).1
  refine ⟨fun h' => ?_, fun h' => ?_⟩ <;>
    · change l.name = _ at h'
      simp [linkNameOk, h'] at h

/-- **Constant time of the translation of a module with linked functions** for the secrecy
    record `s`: for every result `q` of `haxToNF σ m`, the program `q.2` is constant time at
    every fuel in the leakage model `nfLeakModelL` at the declared procedures of `m`, in
    which a call of a tagged field head or of a linked function of `m` is quiet, at the
    table `m.linkTable hax64WExit` of the linked functions, relative to the runs that
    succeed, for the labels `entryLabels (paramLevelOf s)` of the parameters of `σ`. A call
    of a linked function is compiled to a call of its code, whose constant time is a
    property of that code. -/
def HaxToNFCTL (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule) : Prop :=
  ∀ q : (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]), haxToNF σ m = some q →
    ∀ (tf : Nat) (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
      (r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak),
      PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ →
      nfLeakRunL (linkedDecls m hax64WExit) (m.linkTable hax64WExit) tf q.2 V₁ = some r₁ →
      nfLeakRunL (linkedDecls m hax64WExit) (m.linkTable hax64WExit) tf q.2 V₂ = some r₂ →
      r₁.2 = r₂.2

/-- **Constant time of the translation of a module with linked functions on the valuations
    of a predicate**: `HaxToNFCTL s σ m` restricted to pairs of entry valuations that both
    satisfy `Qv`. -/
def HaxToNFCTLOn (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule)
    (Qv : Valuation (entryCtx (abiEntry σ)) → Prop) : Prop :=
  ∀ q : (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]), haxToNF σ m = some q →
    ∀ (tf : Nat) (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
      (r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak),
      Qv V₁ → Qv V₂ →
      PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ →
      nfLeakRunL (linkedDecls m hax64WExit) (m.linkTable hax64WExit) tf q.2 V₁ = some r₁ →
      nfLeakRunL (linkedDecls m hax64WExit) (m.linkTable hax64WExit) tf q.2 V₂ = some r₂ →
      r₁.2 = r₂.2

/-- Constant time of the translation on all valuations gives it on the valuations of every
    predicate. -/
theorem haxToNFCTLOn_of_haxToNFCTL {s : _root_.Hax.FnSecrecy} {σ : AbiLayout} {m : HaxModule}
    (Qv : Valuation (entryCtx (abiEntry σ)) → Prop) (h : HaxToNFCTL s σ m) :
    HaxToNFCTLOn s σ m Qv :=
  fun q hq tf V₁ V₂ r₁ r₂ _ _ hp h₁ h₂ => h q hq tf V₁ V₂ r₁ r₂ hp h₁ h₂

/-- **The level check of the translation of a module with linked functions**: the checker
    `NFProg.levelCheck'` in the leakage model `nfLeakModelL` at the declared procedures of
    `m` on the program of `haxToNF σ m` at the labels `entryLabels (paramLevelOf s)`;
    `false` when the translation refuses the module. -/
def haxToNFCTBL (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule) : Bool :=
  match haxToNF σ m with
  | some q =>
      (Dialects.NFLeak.NFProg.levelCheck' (nfLeakModelL (linkedDecls m hax64WExit)) q.2
        (entryLabels (paramLevelOf s) (abiEntry σ))).isSome
  | none => false

/-- **The level check of the translation of a module with linked functions gives its
    constant time** (`NFProg.nfCTRel_of_levelCheck'` at the leaf table of
    `m.linkTable hax64WExit`). -/
theorem haxToNFCTL_of_haxToNFCTBL (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule)
    (h : haxToNFCTBL s σ m = true) : HaxToNFCTL s σ m := by
  intro q hq tf
  unfold haxToNFCTBL at h
  rw [hq] at h
  exact @Dialects.NFLeak.NFProg.nfCTRel_of_levelCheck' nfDialect _ _ _ _
    (nfDenote (tableOf (m.linkTable hax64WExit))) (nfLeakModelL (linkedDecls m hax64WExit))
    tf _ _ q.2 _ h

/-- On a module without linked functions, constant time of the translation modulo the field
    calls (`HaxToNFCT`) is its constant time modulo the declared calls (`HaxToNFCTL`): the
    module declares no procedure and its table of linked functions is `hax64WExit`. -/
theorem haxToNFCTL_of_linked_nil {s : _root_.Hax.FnSecrecy} {σ : AbiLayout} {m : HaxModule}
    (hlk : m.linked = []) (h : HaxToNFCT s σ m) : HaxToNFCTL s σ m := by
  intro q hq tf V₁ V₂ r₁ r₂ hp h₁ h₂
  rw [linkedDecls_of_linked_nil hlk, HaxModule.linkTable_of_linked_nil hlk, nfLeakRunL_eq]
    at h₁ h₂
  refine h q hq tf V₁ V₂ r₁ r₂ hp ?_ ?_
  · rw [nfLeakRunQ_eq]
    simpa only [stripDecl_nil_eq] using h₁
  · rw [nfLeakRunQ_eq]
    simpa only [stripDecl_nil_eq] using h₂

/-! ## Constant time modulo declassification -/

/-- **Constant time of the translation of a module modulo declassification**, for the
    secrecy record `s`: `HaxToNFCT` for the pairs of valuations whose source runs declassify
    the same values. For every result `q` of `haxToNF σ m` and every sequence `d` of values,
    two valuations agreeing on the public parameters, from whose entry environments every
    run of the body `nfBody (bindConsts σ.consts m.entry)` under `hax64WExit` that ends in a
    value declassifies `d` (`SrcDeclIs`), and from which the program `q.2` runs to results
    in the leakage model `nfLeakModelQ`, give equal events. -/
def HaxToNFCTD (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (m : HaxModule) : Prop :=
  ∀ q : (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]), haxToNF σ m = some q →
    ∀ (tf : Nat) (ds : List Value) (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
      (r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak),
      PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ →
      SrcDeclIs hax64WExit (nfBody (bindConsts σ.consts m.entry)) ds
        (entryEnvOf (abiEntry σ) V₁) →
      SrcDeclIs hax64WExit (nfBody (bindConsts σ.consts m.entry)) ds
        (entryEnvOf (abiEntry σ) V₂) →
      nfLeakRunQ hax64WExit tf q.2 V₁ = some r₁ → nfLeakRunQ hax64WExit tf q.2 V₂ = some r₂ →
      r₁.2 = r₂.2

/-- **Source constant time modulo declassification of a single function gives constant time
    of its translation modulo declassification.** For a module without callee, depth or
    linked function, every parameter of `σ` listed in `s`, the body
    `nfBody (bindConsts σ.consts m.entry)` the front reads constant time at the source modulo
    declassification for the source leakage `srcLeakNFD` and `levelsOf s` (`SourceCTDOf`),
    and running at the fuel `F` to a value from the environment of every valuation of the
    parameters, the translation is constant time modulo declassification (`HaxToNFCTD`). A
    translation is a result of `nfSrcProg` (`haxToNF_eq_nfSrcProg`) and the statement is
    `impToNF_nfCTRelD`. -/
theorem haxToNFCTD_of_sourceCTD (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) {m : HaxModule}
    (hfns : m.fns = []) (hdep : m.depth = 0) (hlk : m.linked = [])
    (hps : ∀ p ∈ abiEntry σ, ∃ b, (p.1, b) ∈ s.params)
    (hct : SourceCTDOf hax64WExit (srcLeakNFD hax64WExit) (levelsOf s)
      (nfBody (bindConsts σ.consts m.entry)))
    (F : Nat)
    (hterm : ∀ V : Valuation (entryCtx (abiEntry σ)), ∃ v env',
      (denote' hax64WExit F (nfBody (bindConsts σ.consts m.entry))).run
        (entryEnvOf (abiEntry σ) V) = (.val v, env')) :
    HaxToNFCTD s σ m := by
  rintro ⟨t, qp⟩ hq tf ds V₁ V₂ r₁ r₂ hpub hd₁ hd₂ h₁ h₂
  replace hq := haxToNF_eq_nfSrcProg σ hfns hdep hlk hq
  unfold nfSrcProg at hq
  split at hq
  · obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hq
    cases he
    exact impToNF_nfCTRelD hax64WExit hax64SigOf CatCrypt.Crypto.Hax.hax64WExit_typedCalls
      CatCrypt.Crypto.Hax.repeatCalls_hax64WExit (levelsOf s) _ hct ho F hterm tf ds V₁ V₂
      r₁ r₂ (pubEqV_entryLabels_levelsOf s _ hps V₁ V₂ hpub) hd₁ hd₂ h₁ h₂
  · cases hq

/-- **Constant time modulo declassification gives constant time on the valuations that
    declassify one sequence.** On a module without linked functions, let every valuation
    satisfying `Qv` have source runs declassifying `ds`. Then `HaxToNFCTD s σ m` gives
    `HaxToNFCTLOn s σ m Qv`: the module declares no procedure and its table of linked
    functions is `hax64WExit`. -/
theorem haxToNFCTLOn_of_haxToNFCTD {s : _root_.Hax.FnSecrecy} {σ : AbiLayout} {m : HaxModule}
    (hlk : m.linked = []) (ds : List Value) (Qv : Valuation (entryCtx (abiEntry σ)) → Prop)
    (hQ : ∀ V, Qv V → SrcDeclIs hax64WExit (nfBody (bindConsts σ.consts m.entry)) ds
      (entryEnvOf (abiEntry σ) V))
    (h : HaxToNFCTD s σ m) : HaxToNFCTLOn s σ m Qv := by
  intro q hq tf V₁ V₂ r₁ r₂ hQ₁ hQ₂ hp h₁ h₂
  rw [linkedDecls_of_linked_nil hlk, HaxModule.linkTable_of_linked_nil hlk, nfLeakRunL_eq]
    at h₁ h₂
  refine h q hq tf ds V₁ V₂ r₁ r₂ hp (hQ V₁ hQ₁) (hQ V₂ hQ₂) ?_ ?_
  · rw [nfLeakRunQ_eq]
    simpa only [stripDecl_nil_eq] using h₁
  · rw [nfLeakRunQ_eq]
    simpa only [stripDecl_nil_eq] using h₂

/-- **The runs of the translation of a module with linked functions.** Let the body
    `nfBody (bindConsts σ.consts m.entry)` the front reads run at the fuel `F`, at the
    builtins `crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth` that
    answer a call of a function of the module by the run of its prepared body and a call of
    a linked function by its meaning, to a value from the environment of the valuation `V`.
    Then for every result `q` of `haxToNF σ m`, the program `q.2` has a leakage run at the
    table `m.linkTable hax64WExit` from `V`, at every target fuel from some fuel on:
    `impToNF_leak` at the call typing of the prepared callees followed by the linked
    functions, and the inlining
    (`denote_crateInline?`) over the table of the linked functions, which `hax64SigOf` types
    since the names of the linked functions pass `linkNameOk`. -/
theorem haxToNF_leakRunL (σ : AbiLayout) {m : HaxModule} (F fuelC : Nat)
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]} (hq : haxToNF σ m = some q)
    (V : Valuation (entryCtx (abiEntry σ)))
    (hterm : ∃ v env',
      (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth) F
        (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
          (.val v, env')) :
    ∃ N, ∀ tf, N ≤ tf → ∃ r, nfLeakRun (m.linkTable hax64WExit) tf q.2 V = some r := by
  obtain ⟨t, qp⟩ := q
  obtain ⟨hfs, -, hlkn, p, hs, hi⟩ := haxToNF_eq_some hq
  have hfR := crateArrOk_find_repeat hfs
  have hRL := linkTable_repeatCalls hlkn
  have hnc : ∀ l ∈ m.linked, ¬ CatName l.name :=
    fun l hl => not_catName_of_linkNameOk (hlkn l hl)
  have hft : ∀ l ∈ m.linked, _root_.Hax.FieldTag.fieldTag? l.name = none :=
    fun l hl => fieldTag?_of_linkNameOk (hlkn l hl)
  have hTL : CatCrypt.Crypto.Hax.ImpToNF.TypedCalls (m.linkTable hax64WExit) hax64SigOf :=
    typedCalls_linkBi_of_not_catName _ CatCrypt.Crypto.Hax.hax64WExit_typedCalls hnc hft
  have hTC : CatCrypt.Crypto.Hax.ImpToNF.TypedCalls
      (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth)
      (CatCrypt.Crypto.Hax.ImpToNF.crateSigOf (m.prepared nfBody ++ m.linkedFns)
        hax64SigOf) := by
    rw [CatCrypt.Crypto.Hax.NFInline.crateSigOf_append]
    exact crateBi_typedCalls _ _ _
      (CatCrypt.Crypto.Hax.typedCalls_linkBi m.linked
        CatCrypt.Crypto.Hax.hax64WExit_typedCalls) fuelC m.depth
  unfold nfSrcProgC at hs
  split at hs
  · obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨v, env', hr⟩ := hterm
    obtain ⟨x, ⟨N, hx⟩, -⟩ := impToNF_leak _ _ hTC
      (CatCrypt.Crypto.Hax.ImpToNF.crateBi_repeatCalls _ _ hRL hfR fuelC m.depth) ho
      (entryEnvOf_rel _ V) hr
    refine ⟨N, fun tf htf => ?_⟩
    have hfst : ∀ (bi : _root_.Hax.Builtins)
        (p : NFProg nfDialect (entryCtx (abiEntry σ)) [o.t]),
        (nfLeakRun bi tf p V).map Prod.fst = PDenP bi tf p V := fun bi p =>
      @Dialects.NFLeak.NFProg.leakRunM_fst nfDialect _ _ _ _ (nfDenote (tableOf bi))
        nfLeakModel tf _ _ p V
    have hd : PDenP (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth) tf
        o.prog V = some (HVector.cons x .nil) := by
      rw [← hfst, hx tf htf]
      rfl
    have hd' := denote_crateInline? (m.prepared nfBody) (m.linkTable hax64WExit)
      (m.linkTable_typedCalls_linkSig hTL) hRL hfR fuelC tf m.depth hi hd
    rw [← hfst] at hd'
    obtain ⟨r, hr', -⟩ := Option.map_eq_some_iff.mp hd'
    exact ⟨r, hr'⟩
  · cases hs

/-- **Constant time of the program of the chain with declarations.** Let `bi` be a subtable
    of the `u64` table that answers the tagged heads by their arms and is the `u64` table at
    the wide tagged heads, and let `bi` and `catEnvOf E'` agree on declarations `D` of no
    name `index` or `array_update`. Let the program `p` have, from every valuation whose
    lowered valuation satisfies `Q`, a leakage run at `bi` at every fuel from some fuel on,
    and be constant time in the leakage model `nfLeakModelL D` at `bi` for the labels
    `entryLabels (paramLevelOf s)` on the valuations whose lowered valuations satisfy `Q`.
    Then the program the chain `extChain` at `D` returns for `p` is constant time at the
    call environment `E'` for the transported labels `mapLabels (nfLabels s (abiEntry σ))`,
    at the owned leakage parameters: for every two valuations that satisfy `Q`, at every
    fuel from some fuel on. -/
theorem nfCT_of_haxToNFCTL (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) {t : NfTy}
    (p : NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (Q : Valuation (d := jasminDialect) (mapCtx ((entryCtx (abiEntry σ)).map catTy)) → Prop)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi)
    (hW : FieldLevel.FieldCallsWideEq bi)
    (hrun : ∀ V : Valuation (entryCtx (abiEntry σ)), Q (ctMapValD (mapVal V)) →
      ∃ N, ∀ tf, N ≤ tf → ∃ r, nfLeakRun bi tf p V = some r)
    {D : List ExtDecl}
    (hct : ∀ (tf : Nat) (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
      (r₁ r₂ : Valuation (d := nfDialect) [t] × List CTLeak),
      Q (ctMapValD (mapVal V₁)) → Q (ctMapValD (mapVal V₂)) →
      PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ →
      nfLeakRunL D bi tf p V₁ = some r₁ → nfLeakRunL D bi tf p V₂ = some r₂ → r₁.2 = r₂.2)
    (E' : CallEnv jasminDialect) (hD : ExtAgree bi (catEnvOf E') D)
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update")
    {pj : NFProg jasminDialect (nfCtx σ) [mapTy (catTy t)]}
    (hpj : (extChain D _ t).run p = some pj) :
    ∀ W₁ W₂ : Valuation (d := jasminDialect) (mapCtx ((entryCtx (abiEntry σ)).map catTy)),
      Q W₁ → Q W₂ → PubEqV (mapLabels (nfLabels s (abiEntry σ))) W₁ W₂ →
      ∃ N, ∀ fuel, N ≤ fuel →
        (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel JLeakParams.owned) E' fuel pj W₁).map
            Prod.snd
          = (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel JLeakParams.owned) E' fuel pj
            W₂).map Prod.snd := by
  intro W₁ W₂ hQ₁ hQ₂ hW'
  have hk := abiEntry_kinds σ
  obtain ⟨V₁, hV₁⟩ := mapVal_surj_abi _ hk (ctBackV W₁)
  obtain ⟨V₂, hV₂⟩ := mapVal_surj_abi _ hk (ctBackV W₂)
  have hpub : PubEqV (entryLabels (paramLevelOf s) (abiEntry σ)) V₁ V₂ :=
    pubEqV_entryLabels_of_mapVal s _ hk V₁ V₂ (by rw [hV₁, hV₂]; exact pubEqV_ctBackV hW')
  have hQV₁ : Q (ctMapValD (mapVal V₁)) := by rw [hV₁, ctMapValD_ctBackV]; exact hQ₁
  have hQV₂ : Q (ctMapValD (mapVal V₂)) := by rw [hV₂, ctMapValD_ctBackV]; exact hQ₂
  obtain ⟨N₁, hN₁⟩ := hrun V₁ hQV₁
  obtain ⟨N₂, hN₂⟩ := hrun V₂ hQV₂
  refine ⟨max N₁ N₂, fun fuel hf => ?_⟩
  obtain ⟨r₁, h₁⟩ := hN₁ fuel (le_of_max_le_left hf)
  obtain ⟨r₂, h₂⟩ := hN₂ fuel (le_of_max_le_right hf)
  have he := hct fuel V₁ V₂ _ _ hQV₁ hQV₂ hpub
    ((nfLeakRunL_eq _ _ _ _ _).trans (congrArg _ h₁))
    ((nfLeakRunL_eq _ _ _ _ _).trans (congrArg _ h₂))
  obtain ⟨m, hm₁, hm₂⟩ := extChain_ctC noVT_owned leakCompat_owned (fun _ => rfl) hbi hF hW
    E' hD hN fuel p hpj V₁ V₂ (inRange_abi _ hk V₁) (inRange_abi _ hk V₂) h₁ h₂ he
  rw [← ctMapValD_ctBackV W₁, ← ctMapValD_ctBackV W₂, ← hV₁, ← hV₂, hm₁, hm₂]

end CatCrypt.Crypto.SecureCompilation.Haxc
