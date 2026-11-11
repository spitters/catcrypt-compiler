/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3

/-!
# The decoded calling body and the symbol map of a result of `regionBack`

The statement `R3StatementF` asks for a decoding of the bytes of `compileA` into a calling body
`pc` followed by a region `Q`, and a symbol map `sym` of the call targets, under which the target
trees of `pc` are formed. At a result of `regionBack` on a program with a `call`, the calling body
of the relation of the back half (`NFProgCallTreeRegion.ruttF_regionBack_word`) is the calling
body of the decoding of the bytes, at every decoding of the codes of the callees
(`calleeBytes_decode`), and the map `symOf` that sends the entry index of each callee in the region
after `pc` to its symbol meets the condition of the back half on the symbol map, since the entry
indices of distinct callees are distinct (`CalleeTab.entryIdx_inj`).

## Main definitions

* `symOf`: the symbol of the callee of a table whose entry index, raised by an offset, is a given
  index.

## Main results

* `symOf_entry`: at a table with distinct symbols and a decoded region, `symOf` sends the raised
  entry index of each symbol to the symbol.
* `ruttF_regionBack_target`: the relation of the back half at a result of `regionBack`, with the
  decoding of the bytes into its calling body followed by the region of the callees and the
  symbol map `symOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (RegionDecode regionProg)

/-- **The symbol at a raised entry index**: the first symbol of `T` whose entry index raised by
    `n₀` is `n`, and the empty name if there is none. -/
def symOf (T : CalleeTab) (n₀ n : Nat) : String :=
  (T.names.find? fun f => n₀ + T.entryIdx (T.symPos f) == n).getD ""

/-- The position of a symbol of a table is a position of the table, holding the function of the
    symbol. -/
theorem symPos_spec {T : CalleeTab} {f : String} (hf : f ∈ T.names) :
    ∃ c, T.symPos f < T.fns.length ∧ T.fns[T.symPos f]? = some c ∧ c.name = f := by
  obtain ⟨c, hc⟩ := T.lookup_of_mem hf
  have h1 := CalleeTab.lookup_symPos hc
  exact ⟨c, (List.getElem?_eq_some_iff.mp h1).1, h1, (CalleeTab.lookup_spec hc).2⟩

/-- **`symOf` at the raised entry index of a symbol.** In a table with distinct symbols and
    nonempty codes whose code decodes as a region at its entry offsets and indices, `symOf`
    sends the entry index of each symbol, raised by `n₀`, to the symbol. -/
theorem symOf_entry {T : CalleeTab} (hnd : T.names.Nodup) (hne : ∀ c ∈ T.fns, c.bytes ≠ [])
    {Q : List RInstr}
    (hR : RegionDecode T.bytes T.names (fun g => T.entryOff (T.symPos g))
      (fun g => T.entryIdx (T.symPos g)) Q) (n₀ : Nat) :
    ∀ f ∈ T.names, symOf T n₀ (n₀ + T.entryIdx (T.symPos f)) = f := by
  intro f hf
  unfold symOf
  cases hfind : T.names.find? (fun g => n₀ + T.entryIdx (T.symPos g) == n₀ +
      T.entryIdx (T.symPos f)) with
  | none =>
    exact absurd (List.find?_eq_none.mp hfind f hf) (by simp)
  | some g =>
    have hg : g ∈ T.names := List.mem_of_find?_eq_some hfind
    have hidx : T.entryIdx (T.symPos g) = T.entryIdx (T.symPos f) := by
      have := List.find?_some hfind
      simpa using this
    obtain ⟨cg, hgl, hgc, hgn⟩ := symPos_spec hg
    obtain ⟨cf, hfl, hfc, hfn⟩ := symPos_spec hf
    have hpos := T.entryIdx_inj hnd hne hR hgl hfl hidx
    rw [hpos, hfc] at hgc
    obtain rfl := Option.some.inj hgc
    exact hgn.symm.trans hfn

section Back

open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall treeAt pureReader
  eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

/-- **The back half at a result of `regionBack`, with the decoding of the bytes.** The statement
    of `NFProgCallTreeRegion.ruttF_regionBack_word`, where moreover the symbols of the table are
    distinct, and at every decoding `q` of the codes of the callees the bytes decode to the
    calling body `pc` followed by the region of the blocks of `q`, its targets raised by the length
    of `pc`, and `symOf T pc.length` sends the raised entry index of each symbol to the symbol. -/
theorem ruttF_regionBack_target {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ (T : CalleeTab) (b : Lcmd) (pc : List RInstr),
      T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ callsToAny T.names p = true ∧ T.names.Nodup
      ∧ (∀ q : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (q c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries q)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ∀ (kind : String → CalleeKind) (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name)) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        ∀ (sa : AState), σ.Regions sa → ∀ (V : Ctxt.Valuation Γ), AbiValOf σ sa V →
        ∀ (fuel : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (treeAt pureReader eventEnv fuel p V) →
        ∀ (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
          (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₁ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttF h₁ (BackRE T) (BackRA PT X) (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal t
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨T, r0, hr0, hcT, ⟨w, m, rfl⟩, hB, r, b, cert, hwb, hbs, hg, -, -⟩ :=
    regionBack_spec_tab h hcf
  have hp : RegionExportable p := regionExportableB_sound hB
  obtain ⟨-, hneB, ds, pc, -, -, -, hpc, -⟩ := calleeBytes_tab hbs
  have hnd : T.names.Nodup := by
    have hg' := hg
    simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
    obtain ⟨⟨⟨⟨⟨⟨hnd0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
    exact of_decide_eq_true hnd0
  obtain ⟨hpr, hnoc⟩ := regionCoB_callee hg
  have hrs : ∀ i ∈ b, ∀ f, X86Backend.LprogBytes.remoteSym i.li_i = some f → f ∈ T.names := by
    have hg' := hg
    simp only [regionCoB, renImageB, Option.all_some, Bool.and_eq_true] at hg'
    obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
    exact remoteSym_mem_names hpr (calleeBodyBT_spec.mp hb).decode
  have hne := regionCallee_fns_ne_nil hcT
  refine ⟨T, b, pc, regionCallee_sublist hcT, hbs, hpc, callsToAny_of_regionCallee hr0 hcT, hnd,
    fun q hdecq => ?_,
    fun kind X hK PT hTc hword sa hreg V hV fuel G hGT hG h₁ sym rd hsum hsym => ?_⟩
  · have hnoq : ∀ c ∈ T.fns, ∀ tg, RInstr.call tg ∉ q c := fun c hc => hnoc c hc _ (hdecq c hc)
    have hR := T.regionBlocks hne q hdecq hneB hnoq T.names (fun _ h => h)
    obtain ⟨pr', hp', hd⟩ := calleeBytes_decode hbs hpr hrs hR.decode
    rw [hpc, Option.some.injEq] at hp'
    subst hp'
    exact ⟨hd, symOf_entry hnd hneB hR.decode pc.length⟩
  · obtain ⟨pc', ds', hpc', -, hR⟩ := NFProgCallTreeRefBack.ruttF_regionRef_word (a := a) hbs hg
      rfl kind X hK hTc sa hreg hp hr0 hwb hGT V hV fuel hG hword
    rw [hpc] at hpc'
    obtain rfl := Option.some.inj hpc'
    exact hR h₁ sym rd hsum hsym

end Back

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget
