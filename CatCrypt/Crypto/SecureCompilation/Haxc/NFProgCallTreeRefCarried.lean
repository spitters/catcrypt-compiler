/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSeg
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents

/-!
# A relation carried by the cut programs of a reference, from call trees

The calling body of the back half is related to the target trees through a relation between
source call trees and states of its reference `B` at the entries of the cuts of `B`, carried by
the cut programs (`NFProgCallTreeCallsRef.RefCarried`). A call tree with call events related by
`NFProgCallTreeExport.TSim` on the bounds-checked machine to a state at the entry of a cut
(`RefUpT`) gives the segments of `B` to its next call or to its end
(`NFProgCallTreeSeg.segTo_of_tsim_vis`, `LprogCallCut.cutRun_of_segTo`); at the next call the step
of the summary of the procedure table is a state after the call of the source answer, from which
the continuation is again related. What remains at each call of the image is the relation of the
source event with the call event of the image, and of their answers; at the end, the relation of
the source value with the byte states of the end state.

## Main definitions

* `NoneFail`: every event of a call tree fails at the answer `none`.
* `RefUpT`: a call tree related by `TSim` on the bounds-checked machine to a state at the entry of
  a cut of a body.

## Main results

* `noneFail_treeAt`: every call of the call tree with call events fails at the answer `none`.
* `refCarried_of_tsim`: `RefUpT` is carried by the cut programs of the body, under the condition at
  the end and the conditions at the calls of the image.
-/
@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefCarried

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsRef (RefCarried)

/-- **Every event of a call tree fails at the answer `none`**: its continuation at `none` is the
    failed leaf. -/
def NoneFail {α : Type} : CallTree (nfCallSig jasminDialect) (Option α) → Prop
  | .ret _ => True
  | .vis _ c => c none = .ret none ∧ ∀ a, NoneFail (c a)

/-- **A call tree related to a state at the entry of a cut of `B`**: the state is in `fn` at the
    entry position of the site `e` of `PT`, every event of the tree meets `G`, the tree fails at
    every answer `none`, and the tree is related by `TSim` on the bounds-checked machine to the
    state at the end condition `Post`. -/
def RefUpT (PT : LprogIsa.ProcTable) (fn : String) (B : List LinstrRM)
    (G : NFCall jasminDialect → Prop) {α : Type}
    (Post : α → LstateMF → Prop) (t : CallTree (nfCallSig jasminDialect) (Option α))
    (e : Option Nat) (s : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.reg.lpc = entryPos e ∧ IsSite PT B e ∧ entryPos e ≤ B.length
    ∧ NFProgCallTreeEvents.AllEv G t ∧ NoneFail t
    ∧ TSim X86Backend.CheckedIsaCall.x86IsaK (singletonProgM fn B)
      (NFProgCallTreeExport.CallSite (singletonProgM fn B)) (CallRet (singletonProgM fn B)) t s Post



section NoneFail

open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (obind ofoldl owhileIter treeAt
  pureReader eventEnv)

/-- `obind` keeps `NoneFail`. -/
theorem noneFail_obind {α β : Type} {k : α → CallTree (nfCallSig jasminDialect) (Option β)}
    (hk : ∀ a, NoneFail (k a)) :
    ∀ {t : CallTree (nfCallSig jasminDialect) (Option α)}, NoneFail t → NoneFail (obind t k)
  | .ret none, _ => trivial
  | .ret (some a), _ => hk a
  | .vis _ c, ⟨hn, hc⟩ => by
      refine ⟨?_, fun a => noneFail_obind hk (t := c a) (hc a)⟩
      show obind (c none) k = .ret none
      rw [hn]
      rfl

/-- `ofoldl` keeps `NoneFail`. -/
theorem noneFail_ofoldl {α β : Type} {f : β → α → CallTree (nfCallSig jasminDialect) (Option β)}
    (hf : ∀ b a, NoneFail (f b a)) : ∀ (l : List α) (b : β), NoneFail (ofoldl f l b)
  | [], _ => trivial
  | a :: l, b => noneFail_obind (fun b' => noneFail_ofoldl hf l b') (hf b a)

/-- `owhileIter` keeps `NoneFail`. -/
theorem noneFail_owhileIter {cs : List JasminTy}
    {step : Ctxt.Valuation (d := jasminDialect) cs →
      CallTree (nfCallSig jasminDialect)
        (Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs)))}
    (hs : ∀ acc, NoneFail (step acc)) :
    ∀ (n : Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs),
      NoneFail (owhileIter (d := jasminDialect) step n acc)
  | 0, _ => trivial
  | n + 1, acc => noneFail_obind (fun r => by
      dsimp only
      split
      · exact noneFail_owhileIter hs n _
      · trivial) (hs acc)

/-- **Every call of the call tree with call events fails at the answer `none`.** -/
theorem noneFail_treeAt (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ V : Ctxt.Valuation Γ, NoneFail (treeAt pureReader eventEnv fuel p V) := by
  induction p with
  | ret vs => intro V; trivial
  | var e k ih => intro V; exact noneFail_obind (fun x => ih _) trivial
  | forLoop count inits body k ihb ihk =>
      intro V
      exact noneFail_obind (fun acc => ihk _) (noneFail_ofoldl (fun b a => ihb _) _ _)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V
      refine noneFail_obind (fun r => ihk _) ?_
      dsimp only
      split
      · exact iht V
      · exact ihe V
  | whileLoop inits body k ihb ihk =>
      intro V
      exact noneFail_obind (fun acc => ihk _) (noneFail_owhileIter (fun acc => ihb _) _ _)
  | call f args k ih =>
      intro V
      exact noneFail_obind (fun r => ih _) ⟨rfl, fun _ => trivial⟩

end NoneFail

section Carried

open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (cuts_of_calleeCutB)

variable (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
  (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
  (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
    (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
  (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
  (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (E : Nat → List String)
  (X : String → CalleeRun) (pos : Nat → Nat) (tgt : String → Nat) (sym : Nat → String)
  (rd : String → AState → List _root_.Hax.Value) (Fin : LstateMF → AState → Prop)
  {PT : LprogIsa.ProcTable} {outs : List String} {fn : String}
  {A B B' : List LinstrRM} {cut' : Option Nat → Option Nat → List LinstrRM}
  (sim : CutSimI X86Backend.CheckedIsaCall.x86IsaK PT outs fn B B'
    (LprogCallCut.cutAt fn (freshLabel A) B) cut')

/-- **A relation of call trees and states at the entries of the cuts of a body is carried by its
    cut programs.** Let the cut checks of `B` pass at `PT` with the label `freshLabel A` of a list
    `A` holding every instruction of `B`, and every shadow instruction of a call of `B` name a
    symbol of `PT`. At the end condition `Post`, let every state where `Post` holds be past the
    end of `B` in `fn`, with `RR` relating the value to every byte state that `Fin` relates to a
    state agreeing with it on `outs`, the arrays and the memory; at every call site of an event,
    let the summary of `PT` step or the source handler `h₁` fail at the event, and let every image
    state at the corresponding call that the simulation relates to the call state of `B` give
    `RE` of the event and the call event of the image, with every pair of answers that `RA`
    relates the failed answer, or a target answer of the callee run `X` whose source answer the
    step of the summary writes, for every event of `G`. Then `RefUpT` is
    carried by the cut programs of `B`, at the failed leaves `none`. -/
theorem refCarried_of_tsim {α : Type} {RR : Option α → Option AState → Prop}
    {Post : α → LstateMF → Prop}
    (hcut : calleeCutB PT (freshLabel A) B = true) (hsub : ∀ i ∈ B, i ∈ A)
    (hPT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      B[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (PT f).isSome = true)
    (hleaf : ∀ v u, Post v u → u.prog.lfn = fn ∧ B.length ≤ u.prog.base.reg.lpc
      ∧ ∀ t', Obs outs u t' → ∀ sA, Fin t' sA → RR (some v) (some sA))
    {G : NFCall jasminDialect → Prop}
    (hglue : ∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
      NFProgCallTreeExport.CallSite (singletonProgM fn B) ev u →
      atPc (singletonProgM fn B) p u → (∃ v, Glue PT (singletonProgM fn B) p u v) ∨ h₁ ev = none)
    (hsite : ∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
      NFProgCallTreeExport.CallSite (singletonProgM fn B) ev u →
      atPc (singletonProgM fn B) p u →
      ∀ u' q v', sim.Q (some p) u u' → sim.site (some p) = some q →
      Glue PT (singletonProgM fn B') q u' v' →
      ∀ bi ra f l, body[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
      ∀ sa sA, ImgRelF frame slotArr base body (E q) (goto u' q) sa → ACorr rsp sA sa →
        sa.reg.lpc = q →
        RE ev (callEvent aMachine sym rd (pos q) (tgt f) sA)
        ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (pos q) (tgt f) sA) a₁ a₂ →
          a₁ = none ∨ ∃ sc tr, a₂ = some sc
            ∧ X f (X86Backend.ImageCallProbe.entryOf (pos q + 1) sA) tr sc
            ∧ ∀ v, Glue PT (singletonProgM fn B) p u v →
              CallRet (singletonProgM fn B) ev u a₁ v) :
    RefCarried h₁ RE RA RR (fun r => r = none) frame slotArr base rsp body E X pos tgt sym rd
      Fin sim (RefUpT PT fn B G Post) := by
  have hcuts := cuts_of_calleeCutB (fn := fn) hcut hsub
  intro t₁ e s ⟨hfn, hpc, he, hle, hG, hnf, hT⟩
  cases t₁ with
  | ret o =>
      cases o with
      | none => exact Or.inl ⟨none, rfl, Or.inl rfl⟩
      | some v =>
          obtain ⟨k, u, hs, hP⟩ := hT
          obtain ⟨hfu, hlu, hR⟩ := hleaf v u hP
          have hseg : SegTo X86Backend.CheckedIsaCall.x86IsaK PT (singletonProgM fn B) s none u :=
            ⟨k, hs, by
              show (if u.prog.lfn = fn then B[u.prog.base.reg.lpc]? else none) = none
              rw [ite_eq_left hfu]
              exact List.getElem?_eq_none hlu⟩
          exact Or.inl ⟨some v, rfl, Or.inr ⟨u, LprogCallCut.cutRun_of_segTo
            X86Backend.CheckedIsaCall.x86IsaK_pcFree
            (X86Backend.CheckedIsaCall.x86IsaK_refusesProcs PT) (hcuts e none he trivial).1
            ⟨hfn, hpc⟩ hle hseg, hR⟩⟩
  | vis ev c =>
      obtain ⟨k, u, hs, hsi, hc⟩ := hT
      obtain ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩ := hsi
      have hPTs := hPT p dst ev.name srcs tag hf
      have hproc : LprogCallCut.isProcB PT (LprogIsa.callShadow dst ev.name srcs, tag) = true := by
        show (LprogIsa.procCall? PT (LprogIsa.callShadow dst ev.name srcs)).isSome = true
        rw [LprogIsa.procCall?_callShadow, Option.isSome_map]
        exact hPTs
      have hsite' : IsSite PT B (some p) := ⟨_, hf, hproc⟩
      have hseg : SegTo X86Backend.CheckedIsaCall.x86IsaK PT (singletonProgM fn B) s (some p) u :=
        ⟨k, hs, hat, _, hf, hproc⟩
      have hplt : p < B.length := (List.getElem?_eq_some_iff.mp hf).1
      obtain ⟨v, hv⟩ | hnone := hglue ev u p hG.1 ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩ hat
      swap
      · refine Or.inr ⟨ev, c, rfl, Or.inr ?_⟩
        show RefUpT PT fn B G Post (c (h₁ ev)) e s
        rw [hnone, hnf.1]
        exact ⟨hfn, hpc, he, hle, trivial, trivial, trivial⟩
      refine Or.inr ⟨ev, c, rfl, Or.inl ⟨p, u, v, hsite',
        LprogCallCut.cutRun_of_segTo X86Backend.CheckedIsaCall.x86IsaK_pcFree
          (X86Backend.CheckedIsaCall.x86IsaK_refusesProcs PT) (hcuts e (some p) he hsite').1
          ⟨hfn, hpc⟩ hle hseg, hv, ?_⟩⟩
      intro u' q v' hQ hq hg' bi ra f l hbi hcall sa sA hrel hac hpcq
      obtain ⟨hRE, hRA⟩ := hsite ev u p hG.1 ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩ hat u' q v'
        hQ hq hg' bi ra f l hbi hcall sa sA hrel hac hpcq
      refine ⟨hRE, fun a₁ a₂ hra => ?_⟩
      rcases hRA a₁ a₂ hra with rfl | ⟨sc, tr, hsc, hX, hret⟩
      · exact Or.inl ⟨none, hnf.1, rfl⟩
      · refine Or.inr ⟨sc, tr, hsc, hX, ?_⟩
        have hcr := hret v hv
        obtain ⟨i, pr, dst', srcs', hi, -, hstep⟩ := hv
        obtain ⟨x, rfl⟩ := X86Backend.CheckedIsaCall.procStep_retRes hstep
        refine ⟨(LprogIsa.lfn_retRes _ _ _).trans (hat.1.trans rfl), ?_, hsite',
          Nat.succ_le_of_lt hplt, hG.2 a₁, hnf.2 a₁, hc a₁ _ hcr⟩
        show (LprogIsa.retRes dst' x u).prog.base.lpc = p + 1
        rw [LprogIsa.lpc_retRes]
        exact congrArg (· + 1) hat.2

end Carried

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefCarried
