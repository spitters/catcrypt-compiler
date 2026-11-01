/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightArrLeak
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightArrLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTProved
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTProved
public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeTuple
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTSource
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTSource
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionCallCT

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the bytes of `compileA` from the proved chain

The compiler `compileA` is `haxToNF`, the chain `extChain` and the region back half
`RegionBackend.compileRegion`. This module derives constant time of the decoded bytes of
`compileRegion` (`regionChain_bytes_ct`) and states the headline of `compileA`: every result
is constant time between entry states from the first of which the source has a run, from the
level check of the front and the constant-time check `regionCtB` of the region back half.

`compileRegion` compiles the structured programs that the region export `exportRegion`
accepts. On them constant time follows from the level check of the front and the check
`regionCtB` that `compileRegion` runs on the printed body (`regionChain_bytes_ct`). The gate
conclusion and robust compilation of `compileA` built on these theorems are
`haxc_gate_proved_all` and `haxc_rc_proved_all` of `RCInstance`; their instances on the limb
kernels `mpn_and_n` and `ltu` are in `WorkedKernelCorollaries`.

## Main results

* `regionBytePub_of_pubAgree` — `RegionBytePub` from `σ.PubAgree`, `σ.Regions` and a fuel
  within which the program denotes.
* `regionChain_bytes_ct` — constant time of the bytes of `compileRegion` on a program
  without a `call`, between entry states that satisfy `σ.Regions` and a precondition
  `Pre`, from constant time of its source events on the valuations of such states and the
  check `regionCtB` of `compileRegion`.
* `haxc_ct_proved_all` — constant time of the bytes of `compileA` on a module whose linked
  functions are linked kernels with distinct names, from constant time modulo the
  field calls and the linked calls of the translation with the calls of the module inlined,
  on the valuations of entry states that satisfy `σ.Regions` and a precondition `Pre`
  (`HaxToNFCTLOn`), and termination of the source on those valuations, between such entry
  states from the first of which the module has a source run, and from the second when it
  has linked functions. Its hypothesis `HaxToNFCTLOn` follows from `HaxToNFCTL`
  (`haxToNFCTLOn_of_haxToNFCTL`); on a module without linked functions that follows from
  `HaxToNFCT` (`haxToNFCTL_of_linked_nil`), which follows from the decidable level check
  `haxToNFCTB` of the translation in the leakage model with quiet field calls
  (`haxToNFCT_of_haxToNFCTB`).
* `haxToNFCTBL_of_haxToNFCTB` — on a module without linked functions, the level check
  `haxToNFCTB` gives the level check `haxToNFCTBL` with quiet declared calls.
* `haxc_correct_auto_ct_proved_all` — the joint value and constant-time theorem, on a
  module whose linked functions are linked kernels with distinct names, from the level check
  `haxToNFCTBL` (`haxToNFCTL_of_haxToNFCTBL`) and termination of the source on the entry
  states under the table of the linked functions.
* `ct_of_compileARegion` — constant time of the bytes of the region line
  `compileARegion`; `haxc_ct_proved_all` is that theorem at
  the module and the layout of the pair stage `pairStage` of `compileA`.
* `haxc_correct_auto_tuple_ct_regions` — the joint theorem for `compileA` on a function with
  a pair tail, from a run of the source reading.
-/

/-! ## 1. The compiler -/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime ConstantTimeRel levelsOf)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (optCom)
open CatCrypt.Crypto
open _root_.Hax (TExpr Value Env denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)
open scoped ENNReal


/-- **`RegionBytePub` from the relation of the headline.** For labels that agree with the
    public data of `σ`: two entry states that satisfy `σ.Regions` and the precondition `Pre`
    and agree on the public data of `σ`, with valuations the layout reads off them, are
    related by `RegionBytePub` at every fuel within which the program denotes at the first
    valuation. The equal stack registers and the equal registers of the array parameters are
    the two conjuncts of `σ.PubAgree`, since an array parameter is public under `σ`. -/
theorem regionBytePub_of_pubAgree {σ : AbiLayout} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {L : Labels Γ} {Pre : AState → Prop} (hL : PubLabelsOK σ L)
    {sa₁ sa₂ : AState} {V₁ V₂ : Ctxt.Valuation Γ} (hV₁ : AbiValOf σ sa₁ V₁)
    (hV₂ : AbiValOf σ sa₂ V₂) (hag : σ.PubAgree sa₁ sa₂) (h₁ : σ.Regions sa₁)
    (h₂ : σ.Regions sa₂) (hP₁ : Pre sa₁) (hP₂ : Pre sa₂) {fuel : Nat}
    (hden : (p.denote fuel V₁).isSome = true) :
    RegionBytePub σ fuel p L Pre sa₁ sa₂ :=
  ⟨V₁, V₂, pubEqV_of_pubAgree hL hag hV₁ hV₂, hV₁, hV₂, h₁, h₂, hP₁, hP₂, hag.1,
    fun a ha n hk => hag.2 a ha (by simp [AbiLayout.argPub, hk]), hden⟩

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (regionExportableB_sound) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytesChecked_eq) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (regArrCtxB abiValOf_unique) in
/-- **Constant time of the bytes of the region back half from the proved chain.** Let
    `Pre` be a precondition on machine states. Let `compileRegion` return `(P, bytes)` on a
    program `p` over a context of registers and stack arrays, without a `call`, that is
    constant time at the source events for labels `L` that agree with the public data of
    `σ`, on the valuations the layout reads off machine states that satisfy `σ.Regions` and
    `Pre`: for every two such valuations, at every fuel from some fuel on. Let every entry
    state satisfying `σ.Regions` have a valuation the layout reads off it. Then every
    decoding of `bytes` is constant time under `ctRegime`, with no side condition on the
    steps, between entry states that satisfy `σ.Regions` and `Pre`, agree on the public data
    of `σ`, and at the first of which `p` denotes at some fuel at a valuation the layout
    reads off it. The proof is `regionWide_bytes_ct` at the export and the printed body of
    `compileRegion_spec`, which pass the gate `regionCoB` and the three checks of
    `regionCtB`, for the precondition `Pre` restricted to the two entry states and at a fuel
    above the bounds of the two valuations the layout reads off them, which are unique
    (`abiValOf_unique`). -/
theorem regionChain_bytes_ct (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) (hcf : p.callFree = true) {P : Lprog}
    {bytes : List (BitVec 8)} (hJ : compileRegion σ a p = some (P, bytes)) (L : Labels Γ)
    (Pre : AState → Prop)
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      ∃ N, ∀ fuel, N ≤ fuel →
        (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) fuel p V₁).map Prod.snd
          = (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) fuel p V₂).map
            Prod.snd)
    (hL : PubLabelsOK σ L) (hΓ : regArrCtxB Γ = true)
    (hval : ∀ sa, σ.Regions sa → ∃ V : Ctxt.Valuation Γ, AbiValOf σ sa V)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ ∃ (V : Ctxt.Valuation Γ) (fuel : Nat), AbiValOf σ s₁ V
          ∧ (p.denote fuel V).isSome = true)
      (fun s u => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s u s') := by
  obtain ⟨hB, r, b, cert, hr, hb, hco, hck, -⟩ := compileRegion_spec hJ
  obtain ⟨hlk, hprW, hgW⟩ := regionCtB_spec hck
  rw [encodeLfundefBytesChecked_eq hb] at hd
  rintro sa₁ sa₂ u₁ u₂ ⟨hag, h₁, h₂, hP₁, hP₂, V₁, fuel, hV₁, hden⟩ hb₁ hb₂
  obtain ⟨V₂, hV₂⟩ := hval sa₂ h₂
  have hpub : PubEqV L V₁ V₂ := pubEqV_of_pubAgree hL hag hV₁ hV₂
  obtain ⟨N, hN⟩ := hct V₁ V₂ ⟨sa₁, h₁, hP₁, hV₁⟩ ⟨sa₂, h₂, hP₂, hV₂⟩ hpub
  obtain ⟨N', hN'⟩ := hct V₂ V₁ ⟨sa₂, h₂, hP₂, hV₂⟩ ⟨sa₁, h₁, hP₁, hV₁⟩
    fun t v h => (hpub t v h).symm
  have hW : ∀ sa W, (sa = sa₁ ∨ sa = sa₂) → AbiValOf σ sa W → W = V₁ ∨ W = V₂ := by
    rintro sa W (rfl | rfl) hW
    · exact Or.inl (abiValOf_unique hΓ hW hV₁)
    · exact Or.inr (abiValOf_unique hΓ hW hV₂)
  have hct' : ∀ W₁ W₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ (Pre sa ∧ (sa = sa₁ ∨ sa = sa₂)) ∧ AbiValOf σ sa W₁) →
      (∃ sa, σ.Regions sa ∧ (Pre sa ∧ (sa = sa₁ ∨ sa = sa₂)) ∧ AbiValOf σ sa W₂) →
      PubEqV L W₁ W₂ →
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) (max fuel (max N N'))
          (legalizeRegion p) W₁).map Prod.snd
        = (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) (max fuel (max N N'))
          (legalizeRegion p) W₂).map Prod.snd := by
    rintro W₁ W₂ ⟨s₁, -, ⟨-, e₁⟩, w₁⟩ ⟨s₂, -, ⟨-, e₂⟩, w₂⟩ -
    rw [legalizeRegion_leakRun (fun _ => rfl), legalizeRegion_leakRun (fun _ => rfl)]
    rcases hW s₁ W₁ e₁ w₁ with rfl | rfl <;> rcases hW s₂ W₂ e₂ w₂ with rfl | rfl
    · rfl
    · exact hN _ (by omega)
    · exact hN' _ (by omega)
    · rfl
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hden
  have hden' : (p.denote (max fuel (max N N')) V₁).isSome = true :=
    Option.isSome_iff_exists.mpr
      ⟨out, NFProg.denoteAt_fuel_mono CallEnv.empty (le_max_left _ _) p V₁ out hout⟩
  exact regionWide_bytes_ct JLeakParams.owned a.fname (max fuel (max N N'))
    (regionExportableB_sound hB) (legalizeRegion_callFree hcf) hct' hr hco hlk hprW hgW
    (fun _ _ => True) hd sa₁ sa₂ u₁ u₂
    (by
      rw [regionBytePub_legalizeRegion]
      exact regionBytePub_of_pubAgree hL hV₁ hV₂ hag h₁ h₂ ⟨hP₁, Or.inl rfl⟩
        ⟨hP₂, Or.inr rfl⟩ hden') hb₁ hb₂

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (regArrCtxB) in
/-- The context `nfCtx σ` of the route program under a layout holds registers and stack
    arrays: a scalar parameter is a `64`-bit register and an array parameter of `n` words a
    stack array of `n` words. -/
theorem regArrCtxB_nfCtx (σ : AbiLayout) : regArrCtxB (nfCtx σ) = true := by
  have hk := abiEntry_kinds σ
  simp only [regArrCtxB, nfCtx, mapCtx, entryCtx, List.map_map, List.all_map,
    List.all_eq_true]
  intro p hp
  obtain ⟨k, hk⟩ := hk p hp
  simp only [Function.comp_apply, hk]
  cases k <;> rfl

section Linked

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)

/-- **Constant time of the bytes of the region line from constant time of the translation.**
    Let `compileARegion` return `(P, bytes)` on a module `m` whose linked functions have distinct
    names (`hnd`) and are linked kernels (`hk`, `LinkedKernel`), with a register result or
    an out result. Let the program
    of the translation `haxToNF σ m`, in which the calls of the functions of the module are
    inlined to the depth of the module, be constant time for the parameter labels of the
    secrecy record `s` modulo the field calls and the calls of the linked functions
    (`HaxToNFCTLOn`: a tagged field head is compiled to a field body and a linked function
    to its code, whose constant time is proved separately), on the valuations of the
    parameters whose lowered valuation the layout reads off a machine state satisfying
    `σ.Regions` and a precondition `Pre` on machine states. Let the body
    `nfBody (bindConsts σ.consts m.entry)` the front reads run at one fuel `F`, at the
    builtins that answer a call of a function of the module by the run of its prepared body
    at the fuel `fuelC` and a call of a linked function by its meaning, to a value from the
    environment of every valuation of the parameters whose lowered valuation the layout
    reads off a machine state satisfying `σ.Regions` and `Pre`. Let the labels of `s` agree
    with the public data of `σ` and the names of `σ` be pairwise distinct (`hnds`). Then
    every decoding of `bytes` is constant time under `ctRegime`, with no side condition on
    the steps, between entry states that satisfy
    `σ.Regions` and `Pre`, agree on the public data of `σ`, from the first of which the
    module has a source run, and from the second of which it has one when it has linked
    functions.

    On a module without linked functions, such as a single function, `hnd` and `hk` hold
    vacuously (the default arguments close them when `m.linked` reduces to `[]`), the
    hypothesis `HaxToNFCTLOn` follows from `HaxToNFCT` (`haxToNFCTL_of_linked_nil`,
    `haxToNFCTLOn_of_haxToNFCTL`), the
    table `m.linkTable hax64WExit` is `hax64WExit` (`HaxModule.linkTable_of_linked_nil`),
    and the source run from the second state is not required. For a single function the
    constant time of the translation follows from source constant time `SourceCTNF`
    (`haxToNFCT_of_sourceCT`).

    On a program of the chain without `call` the proof is `nfCT_of_haxToNFCTL` at the
    declared procedures of `m` and `regionChain_bytes_ct`. On a program with a `call` it is
    `AbiLayout.ctCheckRXO_sound_opt` at the interface of the contract
    `l.contractSig c.args c.res.reg?` of the linked function `l` whose data `c`
    `regionCallee` finds (`compileRegion_singleton`, `compileRegion_spec_callee`), whose
    code meets that interface (`LinkedKernel.calleeSpec_code`), whose footprint lies in its
    frame at a register result (`footBelow_contractSig`) and in its frame and the destination
    `c.outDst?` at an out result (`footBelowOut_contractSig`), and whose public relation
    `LinkedFn.pubRegsAgree` is agreement on the stack register and the public argument
    registers, which the check establishes at the call; its premise, the halting of the
    calling body
    under the oracle of the code of `c` guarded by the precondition of that interface from
    both entry states, is `haxEntry_call_halts` at the same `l`. -/
theorem ct_of_compileARegion (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileARegion m σ fname = some (P, bytes))
    (F fuelC : Nat) (Pre : AState → Prop)
    (hct : HaxToNFCTLOn s σ m (fun V => ∃ sa, σ.Regions sa ∧ Pre sa ∧
      AbiValOf σ sa (VIR.DialectToJasminComCorrect.ctMapValD
        (CatCrypt.Crypto.Hax.NFToCat.mapVal V))))
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry σ))), σ.Regions sa →
      Pre sa → AbiValOf σ sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth)
        F (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
          (.val v, env'))
    (hL : PubLabelsOK σ (mapLabels (nfLabels s (abiEntry σ))))
    (hnds : σ.envNames.Nodup) {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  unfold compileARegion at hc
  erw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q, hq, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨pj, hpj, hJ⟩ := Option.bind_eq_some_iff.mp hc
  cases hcf : pj.callFree with
  | true =>
      rw [compileRegion_of_callFree _ _ hcf] at hJ
      have hf0 := NFEntry.frontR_of_compileRegion hq hpj hJ
      have hq' : haxToNF σ m = some q := hq
      obtain ⟨-, -, hlkn, -⟩ := haxToNF_eq_some hq'
      have hnc : ∀ l ∈ m.linked, ¬ CatName l.name :=
        fun l hl => not_catName_of_linkNameOk (hlkn l hl)
      have hpj' : (extChain (linkedDecls m (m.linkTable hax64WExit)) _ q.1).run q.2 =
          some pj := by
        rw [extChain_congr (declared_linkedDecls m (m.linkTable hax64WExit) hax64WExit)]
        exact hpj
      have hLL : ∀ tf V, nfLeakRunL (linkedDecls m (m.linkTable hax64WExit))
          (m.linkTable hax64WExit) tf q.2 V =
          nfLeakRunL (linkedDecls m hax64WExit) (m.linkTable hax64WExit) tf q.2 V := by
        intro tf V
        rw [nfLeakRunL_eq, nfLeakRunL_eq]
        simp only [stripDecl_linkedDecls m (m.linkTable hax64WExit) hax64WExit]
      have hctC := nfCT_of_haxToNFCTL s σ q.2
        (fun W => ∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa W)
        (subTable_linkBi _ CatCrypt.Crypto.Hax.hax64WExit_subTable hnc)
        (haxEntry.fieldCalls σ m q hq 0) (haxEntry.fieldCallsWide σ m q hq 0)
        (fun V hQ => by
          obtain ⟨sa, hR, hP, hV⟩ := hQ
          exact haxToNF_leakRunL σ F fuelC hq' V (hterm sa V hR hP hV))
        (fun tf V₁ V₂ r₁ r₂ hQ₁ hQ₂ hp h₁ h₂ => hct q hq' tf V₁ V₂ r₁ r₂ hQ₁ hQ₂ hp
          ((hLL tf V₁).symm.trans h₁) ((hLL tf V₂).symm.trans h₂))
        (tableEnv (m.linkTable hax64WExit)) (extAgree_linkedDecls m _)
        (linkedDecls_ne_index hlkn _) hpj'
      have hct' : ∀ W₁ W₂ : Ctxt.Valuation (nfCtx σ),
          (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa W₁) →
          (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa W₂) →
          PubEqV (mapLabels (nfLabels s (abiEntry σ))) W₁ W₂ →
          ∃ N, ∀ fuel, N ≤ fuel →
            (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) fuel pj W₁).map
                Prod.snd
              = (Dialects.NFLeak.NFProg.leakRun (jLeakModel JLeakParams.owned) fuel pj W₂).map
                Prod.snd := by
        intro W₁ W₂ h₁ h₂ hW
        obtain ⟨N, hN⟩ := hctC W₁ W₂ h₁ h₂ hW
        refine ⟨N, fun fuel hf => ?_⟩
        have H := hN fuel hf
        rw [Dialects.NFLeak.NFProg.leakRunMC_of_callFree _ _ _ _ hcf,
          Dialects.NFLeak.NFProg.leakRunMC_of_callFree _ _ _ _ hcf,
          Dialects.NFLeak.NFProg.leakRunM_eq_leakRun,
          Dialects.NFLeak.NFProg.leakRunM_eq_leakRun] at H
        exact H
      have H := regionChain_bytes_ct σ (haxEntry.names fname σ) pj hcf hJ _ Pre hct' hL
        (regArrCtxB_nfCtx σ) (fun sa _ => exists_abiValOf σ hnds sa) hd
      rintro sa₁ sa₂ u₁ u₂ ⟨hag, h₁, h₂, hP₁, hP₂, ⟨v, hrun⟩, -⟩ hb₁ hb₂
      obtain ⟨V, fuel, x, hV, hx, -⟩ := haxEntry.toFrontLegOfR.leg σ m _ hf0 sa₁ v h₁ hrun
      rw [RouteProgJ.envDenote_regions_of_callFree _ fuel pj hcf] at hx
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hx
      exact H sa₁ sa₂ u₁ u₂ ⟨hag, h₁, h₂, hP₁, hP₂, V, fuel, hV, by rw [hy]; rfl⟩ hb₁ hb₂
  | false =>
      obtain ⟨c, hcm, h1⟩ := compileRegion_singleton hJ hcf
      obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp hcm
      obtain ⟨qk, hqk, hX⟩ := (hk l hl).calleeSpec_code hlc c.args c.res.reg?
      obtain ⟨c', hc', pr, q', hq', hnc, hdec, hct⟩ := compileRegion_spec_callee h1 hcf
        (fun c'' h'' => by rw [List.mem_singleton.mp h'', hqk]; rfl)
      obtain rfl : c = c' := (List.mem_singleton.mp hc').symm
      rw [hqk, Option.some.injEq] at hq'
      subst hq'
      rw [hd, Option.some.injEq] at hdec
      subst hdec
      obtain ⟨hcres, -, -, hcclob, hcframe, -, -, -, -, -, hcpubRegs, -⟩ :=
        LinkedFn.calleeData_eq hlc
      -- The footprint of the interface: the frame, and the destination of an out result.
      have hfoot : ∀ s x, (l.contractSig c.args c.res.reg?).foot s x →
          X86Backend.Callee.InFrame (s.regs "%rsp") c.frame x
            ∨ ∃ w ∈ c.outDst?, RegionSep.destAt w.1 w.2 s x := by
        rw [hcframe]
        rcases ((hk l hl).code c hlc).1 with ⟨hL, -⟩ | ⟨po, n, hL, -⟩
        · exact fun s x hf =>
            .inl (X86Backend.LinkedFnContract.footBelow_contractSig hL.result _ _ s x hf)
        · obtain ⟨n0, kd, hcr⟩ : ∃ n0 kd, c.res = .out n0 kd := by
            cases h' : c.res with
            | reg r =>
                rw [h'] at hcres
                simp [LinkedFn.calleeRes, hL.result] at hcres
            | out n0 kd => exact ⟨n0, kd, rfl⟩
          obtain ⟨r0, a0, hres0, hak, har, -⟩ := LinkedFn.calleeRes_out (hcr ▸ hcres)
          rw [hL.result] at hres0
          cases hres0
          have hmap : c.args.map phys = l.layout.args.map (·.reg) := by
            have h2 := congrArg (List.map Prod.fst) hL.args
            rw [← CalleeData.ins_map_fst]
            simpa [List.map_map, Function.comp_def] using h2.symm
          have hrd : phys c.resReg = phys po := by
            have h3 := congrArg (·[kd]?) hmap
            simp only [List.getElem?_map, hak, Option.map_some] at h3
            obtain ⟨y, hy, hyp⟩ := Option.map_eq_some_iff.mp h3
            simp only [CalleeData.resReg, hcr, List.getD_eq_getElem?_getD, hy, Option.getD_some]
            rw [hyp, har]
          intro s x hf
          rcases X86Backend.LinkedFnContract.footBelowOut_contractSig hL _ _ s x hf with
            h | ⟨j, hj, hx⟩
          · exact .inl h
          · refine .inr ⟨(phys c.resReg, n), by simp [CalleeData.outDst?, hcr], j, hj, ?_⟩
            rw [hrd]
            exact hx
      rintro sa₁ sa₂ u₁ u₂ ⟨hag, h₁, h₂, -, -, ⟨v₁, hr₁⟩, hr₂⟩ ⟨e₁, hb₁⟩ ⟨e₂, hb₂⟩
      obtain ⟨v₂, hr₂⟩ := hr₂.resolve_left fun h => by simp [h] at hcm
      obtain ⟨pc₁, qk₁, hqk₁, hd₁, -, sa₁', hO₁, -⟩ :=
        haxEntry_call_halts hnd hk hq hpj hcf hl hlc h1 sa₁ h₁ v₁ hr₁
      obtain ⟨pc₂, qk₂, hqk₂, hd₂, -, sa₂', hO₂, -⟩ :=
        haxEntry_call_halts hnd hk hq hpj hcf hl hlc h1 sa₂ h₂ v₂ hr₂
      rw [hqk, Option.some.injEq] at hqk₁ hqk₂
      subst hqk₁ hqk₂
      rw [hd, Option.some.injEq] at hd₁ hd₂
      obtain rfl := eq_of_append_shiftProg hd₁
      obtain rfl := eq_of_append_shiftProg hd₂
      refine AbiLayout.ctCheckRXO_sound_opt hct hnc hX (fun x hx => ?_) hfoot
        (fun s₁ s₂ _ _ hpa => ?_) hag h₁ h₂ hO₁ hO₂ hb₁ hb₂
      · change l.clob.contains x = false
        rw [← hcclob]
        exact hx
      · change l.pubRegsAgree s₁ s₂
        refine ⟨hpa.1 _ List.mem_cons_self, fun a ha hp => hpa.1 _ (List.mem_cons_of_mem _ ?_)⟩
        rw [hcpubRegs]
        exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, hp⟩, rfl⟩

/-- **Constant time of the bytes of `compileA` from constant time of the translation.** Let
    `compileA` return `(P, bytes)` on a module `m` under `σ`. The hypotheses on the
    translation are those of `ct_of_compileARegion` at the module
    `(pairStage m σ).1` and the layout `(pairStage m σ).2` of the pair stage, which
    `compileA` translates; on a module without a pair tail (`pairTailOf`) they are `m` and
    `σ`. Every decoding of `bytes` is constant time under `ctRegime` between entry states
    that satisfy `σ.Regions` and `Pre`, agree on the public data of `σ`, from the first of
    which `m` has a source run, and from the second of which it has one when it has linked
    functions. It is `ct_of_compileARegion` at the pair stage: the layout of the stage has the
    regions and the public data of `σ` (`pairStage_regions`, `pairStage_pubAgree`), and a
    source run of `m` gives one of the stage module (`haxRuns_pairStage`). -/
theorem haxc_ct_proved_all (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (F fuelC : Nat) (Pre : AState → Prop)
    (hct : HaxToNFCTLOn s (pairStage m σ).2 (pairStage m σ).1 (fun V => ∃ sa,
      (pairStage m σ).2.Regions sa ∧ Pre sa ∧
      AbiValOf (pairStage m σ).2 sa (VIR.DialectToJasminComCorrect.ctMapValD
        (CatCrypt.Crypto.Hax.NFToCat.mapVal V))))
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → Pre sa → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth)
        F (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  have hl := pairStage_linked m σ
  have hc' : compileARegion (pairStage m σ).1 (pairStage m σ).2 fname = some (P, bytes) := hc
  have hR := pairStage_regions m σ
  have hA := pairStage_pubAgree m σ
  have hrun : ∀ {sa v}, haxRuns σ m sa v → ∃ x, haxRuns (pairStage m σ).2 (pairStage m σ).1 sa x :=
    fun h => by
      obtain ⟨x, hx, -⟩ := haxRuns_pairStage h
      exact ⟨x, hx⟩
  rintro s₁ s₂ t₁ t₂ ⟨hag, h₁, h₂, hP₁, hP₂, ⟨v, hr⟩, hr₂⟩ hb₁ hb₂
  refine ct_of_compileARegion s _ _ fname P bytes hc' F fuelC Pre hct hterm hL hnds hd
    (hl ▸ hnd) (hl ▸ hk) s₁ s₂ t₁ t₂
    ⟨(hA s₁ s₂).2 hag, (hR s₁).2 h₁, (hR s₂).2 h₂, hP₁, hP₂, hrun hr, ?_⟩ hb₁ hb₂
  rcases hr₂ with h | ⟨v₂, h⟩
  · exact .inl (hl.trans h)
  · exact .inr (hrun h)

/-- **Constant time of the bytes of `compileA` from the level check of the translation.**
    It is `haxc_ct_proved_all` with the decided Boolean level check `haxToNFCTBL` of the
    translation of the pair stage in place of its constant time `HaxToNFCTLOn`
    (`haxToNFCTL_of_haxToNFCTBL`, `haxToNFCTLOn_of_haxToNFCTL`). -/
theorem haxc_ct_proved_all_of_check (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (F fuelC : Nat) (Pre : AState → Prop)
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → Pre sa → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth)
        F (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  haxc_ct_proved_all s m σ fname P bytes hc F fuelC Pre
    (haxToNFCTLOn_of_haxToNFCTL _ (haxToNFCTL_of_haxToNFCTBL s _ _ hck)) hterm hL hnds hd hnd hk

end Linked

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.Hax.ImpToNF (nfLeakModelQ)

/-- On a module without linked functions, the level check of the translation in the leakage
    model with quiet declared calls (`haxToNFCTBL`) is the level check with quiet field calls
    (`haxToNFCTB`): the module declares no procedure, and `nfLeakModelL []` is
    `nfLeakModelQ`. -/
theorem haxToNFCTBL_of_haxToNFCTB {s : _root_.Hax.FnSecrecy} {σ : AbiLayout} {m : HaxModule}
    (hlk : m.linked = []) (h : haxToNFCTB s σ m = true) : haxToNFCTBL s σ m = true := by
  have hQ : nfLeakModelL [] = nfLeakModelQ := by
    unfold nfLeakModelL nfLeakModelQ
    congr 1
    funext op
    cases nfKind op <;> simp
  unfold haxToNFCTBL
  unfold haxToNFCTB at h
  rw [linkedDecls_of_linked_nil hlk, hQ]
  exact h

/-- **The joint value and constant-time theorem for `compileA`, on a module.** The
    hypotheses are those of `haxc_correct_auto` and those of `haxc_ct_proved_all`, with the
    constant time of the translation given by the level check `haxToNFCTBL` in the leakage
    model with quiet declared calls (`haxToNFCTL_of_haxToNFCTBL`), the run hypothesis
    `hterm` at the table `linkTable hax64WExit` of the linked functions, and the linked
    functions of `m` of distinct names (`hnd`) and linked kernels (`hk`), both automatic on a
    module without linked functions. For a result of `compileA`, one decoding of the bytes
    halts from `sa` in a state from which `σ` reads back `v` (both cases of
    `haxc_correct_auto`: `Halts` is the halting run through calls `HaltsC`), and two runs
    of it under `ctRegime` have equal leakage traces from entry states that satisfy
    `σ.Regions` and `Pre`, agree on the public data of `σ`, from the first of which `m` has
    a source run, and from the second of which it has one when it has linked functions. The
    hypotheses on the translation are stated at the module `(pairStage m σ).1` and the
    layout `(pairStage m σ).2` of the pair stage, which are `m` and `σ` on a module without
    a pair tail. The source run `haxRuns σ m sa v` answers a call of a function of the
    module by the run of the source reading of the extraction of the callee under the table
    of the module. -/
theorem haxc_correct_auto_ct_proved_all (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true) (F fuelC : Nat)
    (Pre : AState → Prop)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → Pre sa → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth) F
        (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog
      ∧ (∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
      ∧ ConstantTimeRel
          (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
            ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
          (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  obtain ⟨prog, hd, hv⟩ := haxc_correct_auto m σ fname P bytes hc sa hsep v hrun hnd hk
  refine ⟨prog, hd, ?_, haxc_ct_proved_all_of_check s m σ fname P bytes hc F fuelC Pre hck
    hterm hL hnds hd hnd hk⟩
  rcases hv with ⟨sa', hh, hR, -⟩ | ⟨-, -, -, -, -, -, h, -⟩
  · exact ⟨sa', hh, hR⟩
  · exact h

/-- **The joint value and constant-time theorem on a pair result.** For a result of
    `compileA` on a function `te` with a pair tail at `σ` (`pairTailOf`), whose pair stage
    compiles the stripped body under the array part of the layout: under the hypotheses of
    `haxc_correct_auto_tuple` and those of `haxc_correct_auto_ct_proved_all` at the stripped
    body and `σ.arrPart`, the conclusion of `haxc_correct_auto_tuple` holds for one decoded
    program, and any two runs of it from entry states that satisfy `σ.Regions` and the
    precondition `Pre` and agree on `σ.PubAgree`, from the first of which `te` has a source
    run, have equal leakage traces under `ctRegime`. It is `haxc_correct_auto_ct_proved_all`
    at the single function, with the run of the source from `isControlFlow_false_of_pairTail`. -/
theorem haxc_correct_auto_tuple_ct_regions (s : _root_.Hax.FnSecrecy) (te : TExpr)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes))
    {d : String × String} (hpt : pairTailOf te σ = some d)
    (hck : haxToNFCTB s σ.arrPart (stripArrTailT te) = true) (F fuelC : Nat)
    (Pre : AState → Prop)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry σ.arrPart))),
      σ.arrPart.Regions sa → Pre sa → AbiValOf σ.arrPart sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi ((stripArrTailT te : HaxModule).prepared nfBody) hax64WExit
        fuelC (stripArrTailT te : HaxModule).depth) F
        (nfBody (bindConsts σ.arrPart.consts (stripArrTailT te : HaxModule).entry))).run
          (entryEnvOf (abiEntry σ.arrPart) V) = (.val v, env'))
    (hL : PubLabelsOK σ.arrPart (mapLabels (nfLabels s (abiEntry σ.arrPart))))
    (hnd : σ.arrPart.envNames.Nodup)
    (hres : WordArrResult σ.arrPart (stripArrTailT te))
    (sa : AState) (hsep : σ.Regions sa) (env : Env) (henv : σ.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine hax64WExit fuel te.erase).run env = (.val v, env')) :
    ∃ prog, decodeLprog bytes = some prog
      ∧ (∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
      ∧ ConstantTimeRel
          (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
            ∧ ∃ v, haxRuns σ te s₁ v)
          (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  have hps : pairStage te σ = ((stripArrTailT te : HaxModule), σ.arrPart) := by
    simp only [pairStage, hpt]; rfl
  obtain ⟨prog, hd, hv, hct⟩ := haxc_correct_auto_ct_proved_all s te σ fname P bytes hc
    (by rw [hps]; exact haxToNFCTBL_of_haxToNFCTB rfl hck) F fuelC Pre
    (by rw [hps, HaxModule.linkTable_of_linked_nil rfl]; exact hterm) (by rw [hps]; exact hL)
    (by rw [hps]; exact hnd) sa hsep v ((haxRuns_single σ te sa v).mpr ⟨env, fuel, env', henv,
      hrun, isControlFlow_false_of_pairTail hpt hres hsep henv hrun⟩)
  exact ⟨prog, hd, hv, fun s₁ s₂ t₁ t₂ h => hct s₁ s₂ t₁ t₂ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2, .inl rfl⟩⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
