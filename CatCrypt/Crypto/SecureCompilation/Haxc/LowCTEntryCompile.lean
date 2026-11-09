/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.LowCTEntry
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTStraight

@[expose] public section

set_option autoImplicit false

/-!
# The compiler at the scalar fragment of LowCT: correctness and constant time

For an entry `E : NFEntry` the compiler is `E.compileR`: the translation `E.toNF`, the chain
`extChain` and the region back half `compileRegion`. Its correctness is
`NFEntry.compileR_correct` and its constant-time theorem `NFEntry.compileR_ct`, whose source
premise is constant time of the translated program in the leakage model `nfLeakModelL` at
the declared procedures of the entry.

`lowCTEntry_correct` and `lowCTEntry_ct` are the instances at the scalar fragment of LowCT
(`lowCTEntry N L`). The entry declares no procedure and its table is `hax64WExit`; the source
premise of the constant-time theorem is the level check `lowCTToNFCTB` of the program
`lowCTToNF` returns, at the labels `entryLabels (paramLevelOf sec)` of the parameters of the
layout.

## Main definitions

* `lowCTToNFCTB` — the level check of the translation of a LowCT command.

## Main results

* `lowCTToNFCT_of_lowCTToNFCTB` — the level check gives constant time of the translated
  program relative to the runs that succeed.
* `lowCTEntry_correct` — the compiler theorem at the scalar fragment of LowCT.
* `lowCTEntry_ct` — constant time of the bytes compiled from the scalar fragment of LowCT.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel CTLeak)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryLabels paramLevelOf tableOf)
open CatCrypt.Crypto.Hax.LowCTToNF (lowCTToNF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT LeafSpec)
open CatCrypt.Crypto.Hax (hax64WExit)
open _root_.Hax (Value)

/-! ## The level check of the translation -/

/-- **The level check of the translation of a LowCT command** for the secrecy record `sec`:
    the checker `NFProg.levelCheck'` in the leakage model `nfLeakModelL []`, without declared
    procedures, on the program of `lowCTToNF (abiEntry σ) s.1 s.2` at the labels
    `entryLabels (paramLevelOf sec)` of the parameters of `σ`; `false` when the translation
    refuses the command. -/
def lowCTToNFCTB (sec : _root_.Hax.FnSecrecy) (σ : AbiLayout) (s : String × LowCT) : Bool :=
  match lowCTToNF (abiEntry σ) s.1 s.2 with
  | some q =>
      (Dialects.NFLeak.NFProg.levelCheck' (nfLeakModelL []) q.2
        (entryLabels (paramLevelOf sec) (abiEntry σ))).isSome
  | none => false

/-- **The level check gives constant time of the translated program**: when `lowCTToNFCTB`
    accepts, the program `lowCTToNF` returns is constant time in `nfLeakModelL []` at the
    table `hax64WExit` for the labels of `sec`, at every fuel, relative to the runs that
    succeed (`NFProg.nfCTRel_of_levelCheck'`). -/
theorem lowCTToNFCT_of_lowCTToNFCTB (sec : _root_.Hax.FnSecrecy) (σ : AbiLayout)
    (s : String × LowCT) (h : lowCTToNFCTB sec σ s = true)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : lowCTToNF (abiEntry σ) s.1 s.2 = some q) (tf : Nat)
    (V₁ V₂ : Ctxt.Valuation (entryCtx (abiEntry σ)))
    (r₁ r₂ : Ctxt.Valuation (d := nfDialect) [q.1] × List CTLeak)
    (hp : PubEqV (entryLabels (paramLevelOf sec) (abiEntry σ)) V₁ V₂)
    (h₁ : nfLeakRunL [] hax64WExit tf q.2 V₁ = some r₁)
    (h₂ : nfLeakRunL [] hax64WExit tf q.2 V₂ = some r₂) : r₁.2 = r₂.2 := by
  unfold lowCTToNFCTB at h
  rw [hq] at h
  exact @Dialects.NFLeak.NFProg.nfCTRel_of_levelCheck' nfDialect _ _ _ _
    (nfDenote (tableOf hax64WExit)) (nfLeakModelL []) tf _ _ q.2 _ h V₁ V₂ r₁ r₂ hp h₁ h₂

/-! ## The compiler at the scalar fragment of LowCT -/

/-- **The compiler theorem at the scalar fragment of LowCT.** For a result `(P, bytes)` of
    the compiler `compileR` at `lowCTEntry N L` on a result name and a command: from every
    entry state `sa` satisfying `σ.Regions`, every value `v` of an in-range run of the command
    from a state the layout reads off `sa` (`lowCTRuns`) is matched by a halting run of the
    machine on the decoded bytes from which `σ` reads back `v`. -/
theorem lowCTEntry_correct (N : Nat) (L : LeafSpec) (s : String × LowCT) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : (lowCTEntry N L).compileR s σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : lowCTRuns N L σ s sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' v := by
  obtain ⟨prog, sa', hd, hh, hR, -⟩ :=
    (lowCTEntry N L).compileR_correct s σ fname P bytes hc sa hsep v hrun
  exact ⟨prog, sa', hd, hh, hR⟩

/-- **Constant time of the bytes compiled from the scalar fragment of LowCT.** Let the
    compiler `compileR` at `lowCTEntry N L` return `(P, bytes)`, the level check
    `lowCTToNFCTB` accept the command at the labels of the secrecy record `sec`, those labels
    agree with the public data of `σ` and the names of `σ` be pairwise distinct. Let the
    translated program have a leakage run at every fuel from some fuel on, from every
    valuation whose lowered valuation the layout reads off an entry state satisfying
    `σ.Regions` and `Pre` (`hterm`). Then every decoding of `bytes` is constant time under
    `ctRegime` between entry states that satisfy `σ.Regions` and `Pre`, agree on the public
    data of `σ`, and from the first of which the command has an in-range run. -/
theorem lowCTEntry_ct (N : Nat) (L : LeafSpec) (sec : _root_.Hax.FnSecrecy)
    (s : String × LowCT) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : (lowCTEntry N L).compileR s σ fname = some (P, bytes))
    (Pre : AState → Prop) (hsrc : lowCTToNFCTB sec σ s = true)
    (hterm : ∀ q : (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
      lowCTToNF (abiEntry σ) s.1 s.2 = some q →
      ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry σ))), σ.Regions sa → Pre sa →
        AbiValOf σ sa (VIR.DialectToJasminComCorrect.ctMapValD (mapVal V)) →
        ∃ M, ∀ tf, M ≤ tf → ∃ r, nfLeakRun hax64WExit tf q.2 V = some r)
    (hL : PubLabelsOK σ (mapLabels (nfLabels sec (abiEntry σ))))
    (hnds : σ.envNames.Nodup) {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ ∃ v, lowCTRuns N L σ s s₁ v)
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  intro s₁ s₂ t₁ t₂ hpub h₁ h₂
  exact (lowCTEntry N L).compileR_ct sec s σ fname P bytes hc 0 Pre
    (fun _ _ => CatCrypt.Crypto.Hax.hax64WExit_subTable) (fun _ _ _ hd => nomatch hd)
    (fun q hq tf V₁ V₂ r₁ r₂ _ _ hp h₁ h₂ =>
      lowCTToNFCT_of_lowCTToNFCTB sec σ s hsrc q hq tf V₁ V₂ r₁ r₂ hp h₁ h₂)
    hterm hL hnds hd (by exact List.nodup_nil) (fun _ h => nomatch h) s₁ s₂ t₁ t₂
    ⟨hpub.1, hpub.2.1, hpub.2.2.1, hpub.2.2.2.1, hpub.2.2.2.2.1, hpub.2.2.2.2.2, Or.inl rfl⟩
    h₁ h₂

end CatCrypt.Crypto.SecureCompilation.Haxc
