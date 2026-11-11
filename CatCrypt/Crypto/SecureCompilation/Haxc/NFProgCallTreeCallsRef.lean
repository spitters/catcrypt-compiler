/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite

/-!
# A reference body cut at its calls, against the image

A body `B` and its image `B'` related by a simulation of their cut programs (`CutSimI`, the
validation by segments of `LprogCallCut`) are related segment by segment: a halting run of a cut
program of `B` from a state related by `R` is matched by a halting run of the corresponding cut
program of `B'`, and the step of a summary at a shadow instruction of `B` by the step of the
summary at the corresponding shadow instruction of `B'`. A relation between source call trees
and states of `B` at an entry of a segment, carried by the cut programs and the steps of the
summaries of `B` (`RefCarried`), then gives a relation between source call trees and states of
the image at the start of a segment carried by the image (`ImgUp`).

## Main definitions

* `RefCarried`: a relation between source call trees and states of `B` at entries of segments
  carried by the cut programs of `B`, with the conditions of `ImgUp` at the call states of the
  image that the simulation relates to its call states.
* `RefImgUp`: the relation between source call trees and image states that it induces.

## Main results

* `imgUp_of_refCarried`: a relation carried by the cut programs of `B` induces a relation
  carried by the image.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsRef

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (stepA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (RunChain SegTo Glue runChain_of_run)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps Halted atPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
  (RInstr Params ShapeOK Shape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (remoteSym)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (RelocShapeOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave frameSize)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys isRetB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (instrOKB condPrevB frameRsp isCondB LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (ACorrW widenS widenCell lvm_of_getW instrOKWB carryPrevB castPosB SafeWN WideSafeAt CellSafeAt
    NarrowInv CarryReq narrowIn narrowIn_zero narrowIn_succ narrowStep narrowInv_step classifyK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkW
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
  (CutSimI CutRun IsSite IsCut IsCutRev PcFree FnStable entryPos segTo_of_cutRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite (ImgUp)

variable {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
  (RE : E₁.Event → (kSig AState).Event → Prop)
  (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ → (kSig AState).Resp e₂ →
    Prop)
  (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop)
  (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
  (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (E : Nat → List String)
  (X : String → CalleeRun) (pos : Nat → Nat) (tgt : String → Nat) (sym : Nat → String)
  (rd : String → AState → List _root_.Hax.Value) (Fin : LstateMF → AState → Prop)
  {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {outs : List String} {fn : String}
  {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
  (sim : CutSimI I T outs fn B B' cut cut')

/-- **A relation between source call trees and states of `B` carried by its cut programs.** From
    a source tree and a state of `B` at the entry `e` related by `RefUp`: a failed source leaf; a
    source leaf, a halting run of the cut program of `B` from `e` to its end, and `RR` relating
    the value of the leaf to every byte state that `Fin` relates to an image state agreeing with
    the end state on `outs`, the arrays and the memory; a source event, a halting run of the cut
    program from `e` to the shadow instruction at `p` and the step of its summary to `v`, such
    that at every image state at the call `q` that the simulation relates to the call state of
    `B` and every step of the summary of the image from it, the conditions of `ImgUp` hold with
    each source continuation a failed leaf or related to `v` at the entry `some p`; or a source
    event that `B` does not perform. -/
def RefCarried (RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop) : Prop :=
  ∀ t₁ e s, RefUp t₁ e s →
    (∃ r₁, t₁ = .ret r₁ ∧ (Fail r₁ ∨ ∃ t, CutRun I fn (cut e none) s t
      ∧ ∀ t', Obs outs t t' → ∀ sA, Fin t' sA → RR r₁ (some sA)))
    ∨ ∃ e₁ k₁, t₁ = .vis e₁ k₁ ∧
      ((∃ p u v, IsSite T B (some p) ∧ CutRun I fn (cut e (some p)) s u
          ∧ LprogCallCut.Glue T (singletonProgM fn B) p u v ∧
          ∀ u' q v', sim.Q (some p) u u' → sim.site (some p) = some q →
          LprogCallCut.Glue T (singletonProgM fn B') q u' v' →
          ∀ bi ra f l, body[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa sA, ImgRelF frame slotArr base body (E q) (goto u' q) sa → ACorr rsp sA sa →
            sa.reg.lpc = q →
            RE e₁ (callEvent aMachine sym rd (pos q) (tgt f) sA)
            ∧ ∀ a₁ a₂, RA e₁ (callEvent aMachine sym rd (pos q) (tgt f) sA) a₁ a₂ →
              (∃ r, k₁ a₁ = .ret r ∧ Fail r)
              ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (X86Backend.ImageCallProbe.entryOf (pos q + 1) sA) tr sc
                ∧ RefUp (k₁ a₁) (some p) v)
        ∨ RefUp (k₁ (h₁ e₁)) e s)

/-- The relation between source call trees and image states induced by a relation with the
    states of `B`: a state of `B` at an entry `e` related to the source tree and by `R e` to a
    state of the function, both entries sites, the image state being that state at the entry
    position of the site of `e`. -/
def RefImgUp (RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop) (t₁ : CallTree E₁ R₁)
    (s' : LstateMF) : Prop :=
  ∃ e s s₀, RefUp t₁ e s ∧ sim.R e s s₀ ∧ s₀.prog.lfn = fn ∧ IsSite T B e
    ∧ IsSite T B' (sim.site e) ∧ s' = goto s₀ (entryPos (sim.site e))

/-- **A relation carried by the cut programs of `B` induces a relation carried by the image.**
    Let the branch condition of `I` not read the counter, `I` refuse the procedures of `T`, the
    steps of `I` stay in the function, and the cut programs of `B'` be cuts that halt only at
    their exits. Under the simulation `sim`, a relation `RefUp` carried by the cut programs of `B`
    (`RefCarried`) induces the relation `RefImgUp` carried by the image (`ImgUp`). -/
theorem imgUp_of_refCarried {pos' : Option Nat → Option Nat → Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hS : FnStable I)
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x))
    {RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop}
    (hC : RefCarried h₁ RE RA RR Fail frame slotArr base rsp body E X pos tgt sym rd Fin sim
      RefUp) :
    ImgUp h₁ RE RA RR Fail frame slotArr base rsp body E X I T (singletonProgM fn B') pos tgt
      sym rd Fin (RefImgUp sim RefUp) := by
  have hle : ∀ e, IsSite T B' e → entryPos e ≤ B'.length := by
    intro e he
    cases e with
    | none => exact Nat.zero_le _
    | some p =>
        obtain ⟨i, hi, -⟩ := he
        exact (List.getElem?_eq_some_iff.mp hi).1
  rintro t₁ s' ⟨e, s, s₀, hU, hRs, hfn, hB, he, rfl⟩
  rcases hC t₁ e s hU with ⟨r₁, rfl, hf | ⟨t, hrun, hfin⟩⟩ | ⟨e₁, k₁, rfl, hc | hk⟩
  · exact .inl ⟨r₁, rfl, .inl hf⟩
  · obtain ⟨u', hrun', hQ⟩ := sim.seg e none s s₀ t hB trivial hfn hRs hrun
    rw [sim.site_none] at hrun'
    obtain ⟨hc, hv⟩ := hcut' (sim.site e) none he trivial
    obtain ⟨q, hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
    have ho : Obs outs t u' := sim.fin _ _ hQ
    exact .inl ⟨r₁, rfl, .inr ⟨_, hseg, hfin _ ⟨ho.1, ho.2.1, ho.2.2⟩⟩⟩
  · obtain ⟨p, u, v, hp, hrun, hglue, hcall⟩ := hc
    obtain ⟨u', hrun', hQ⟩ := sim.seg e (some p) s s₀ u hB hp hfn hRs hrun
    obtain ⟨q, v', hsite, hglue', hR'⟩ := sim.glue p u u' v hQ hglue
    have hq : IsSite T B' (some q) := by
      obtain ⟨i, pr, dst, srcs, hi, hpq, -⟩ := hglue'
      exact ⟨i, hi, by simp only [LprogCallCut.isProcB, hpq, Option.isSome_some]⟩
    rw [hsite] at hrun'
    obtain ⟨hc, hv⟩ := hcut' (sim.site e) (some q) he hq
    obtain ⟨q', hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
    have hat : Ascent.IsaCfg.atPc (singletonProgM fn B') q (goto u' q') := by
      obtain ⟨_, _, hat, _⟩ := hseg
      exact hat
    have hqq : q' = q := hat.2
    subst hqq
    have hg := hglue'.goto q'
    have hfn' : v'.prog.lfn = fn := (hg.atPc_succ hat).1
    refine .inr ⟨e₁, k₁, rfl, .inl ⟨q', goto u' q', goto v' (q' + 1), hseg, hg,
      fun bi ra f l hb hbi sa sA hIr hA hpc => ?_⟩⟩
    obtain ⟨hRE, hRA⟩ := hcall u' q' v' hQ hsite hglue' bi ra f l hb hbi sa sA hIr hA hpc
    refine ⟨hRE, fun a₁ a₂ ha => ?_⟩
    rcases hRA a₁ a₂ ha with hf | ⟨sc, tr, h1, h2, hU'⟩
    · exact .inl hf
    exact .inr ⟨sc, tr, h1, h2, some p, v, v', hU', hR', hfn', hp, by rw [hsite]; exact hq,
      by rw [hsite]; rfl⟩
  · exact .inr ⟨e₁, k₁, rfl, .inr ⟨e, s, s₀, hk, hRs, hfn, hB, he, rfl⟩⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsRef
