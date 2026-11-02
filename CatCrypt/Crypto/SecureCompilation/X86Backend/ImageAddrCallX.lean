/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW

@[expose] public section

set_option autoImplicit false

/-!
# The linked call to a callee given by its specification

`CheckedIsaCall.haltsC_of_linkedChecksKW` concludes a run through calls of the program that
the bytes of a calling body of the wide class followed by the code of its callee decode to; it
reads the callee as a decoded block `q`, so the callee bytes must decode under the scalar decoder.
This module states the same result for any callee run `X` that meets a callee
specification `CalleeSpec X c`, without a decode of the callee bytes: the bytes of the
caller decode, instruction by instruction, to the layout of its relocated item list; that
layout resolves to the program `prog` in front of every layout whose first instruction
starts at the end of the caller; and a halting run of the image of the calling body is a
run of `prog` under the oracle that answers the call to index `prog.length` by `X`.

## Main results

* `callerPrefix_of_bytes`: the bytes of a relocated body decode to the layout of its item
  list, that layout resolves to `prog` in front of every layout starting at the end of the
  body, `prog` has one instruction per decoded item, and `prog` satisfies
  `LprogBytesLinkReloc.LinkedProg` at the index `prog.length`.
* `haltsO_of_linkedChecksX`: the caller-prefix decode, and a run of `prog` from the index
  of the position of the address state under `oracleAt prog.length X` to a byte state that
  satisfies `Fin` with the end state of the image run, at the bounds-checked instruction
  set `CheckedIsaCall.x86IsaK`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallX

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (layoutAt_start_lt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
  (printedAddrCWB imgGateCBW bitsDeadB liveW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall (x86IsaK x86IsaK_checked
  deadSteps_x86K)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytesReloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave frameSize)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (DShape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO oracleAt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## 1. The decode of the caller prefix -/

/-- **The decode of the bytes of a relocated body, in front of any callee.** Let the body
    have the facts `LinkFacts`, save no register by `push`, and have a nonzero frame below
    `2 ^ 31`, and let its relocated item list satisfy `branchOKReloc` and denote `prog` at
    its own instruction count and byte length `L`. Then:

    * the bytes of the body decode, with fuel the instruction count, to the layout of the
      item list;
    * that layout resolves to `prog` inside the layout of the body followed by any layout
      whose first instruction starts at byte offset `L`;
    * `prog` has one instruction for each item that decodes;
    * `prog` satisfies `LinkedProg` at the index `prog.length`. -/
theorem callerPrefix_of_bytes (symBase : String → Option Int) {body : Lcmd} {ds : List DShape}
    (hF : LinkFacts body ds) (prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hFr : frameSize body < 2 ^ 31)
    (hbr : branchOKReloc (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : expectedReloc (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog) :
    decodeAt (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds)) 0
        (encodeLfundefBytesReloc symBase body)
        = some (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds))
      ∧ (∀ e x tl, resolveAll
          (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds)
            ++ ((encodeLfundefBytesReloc symBase body).length, e, x) :: tl)
          (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds)) = some prog)
      ∧ prog.length = decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      ∧ LinkedProg body ds prog.length (Params.ofBody body).frame prog := by
  have hsh := relocDShapeOK_of_shapes _ hF.shapes
  have hbytes := encodeLfundefBytesReloc_eq_itemBytesL symBase body ds hsaves hsh
  have hok := fundefItemsRelocL_ok symBase (Params.ofBody body) body ds hF0 hFr hsh
  have hlen := expectedReloc_length _ _ _ _ prog hP
  refine ⟨?_, fun e x tl => ?_, hlen, ?_⟩
  · rw [hbytes]
    exact decodeAt_items _ hok _ 0 (by rw [layoutAt_length])
  · have hbr' := hbr
    have hP' := hP
    rw [hbytes] at hbr' hP' ⊢
    rw [resolveAll_layout_reloc _ hok _ _ _ (fun q hq => ?_) _ 0 hbr']
    · exact hP'
    · have hlt : ∀ z ∈ layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds),
          z.1 < (itemBytes (fundefItemsRelocL symBase (Params.ofBody body) body ds)).length :=
        fun z hz => by simpa using layoutAt_start_lt _ hok 0 z hz
      have hnone : (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds)).findIdx?
          (fun z => decide (z.1
            = (itemBytes (fundefItemsRelocL symBase (Params.ofBody body) body ds)).length))
          = none := by
        rw [List.findIdx?_eq_none_iff]
        intro z hz
        have := hlt z hz
        exact decide_eq_false (by omega)
      simp [List.findIdx?_append, hnone, List.findIdx?_cons, hq, layoutAt_length]
  · rw [hlen]
    exact linkedProg_of_itemsMapL symBase hF _ (fun _ => _)
      (fun _ _ _ _ _ _ h => (Prod.mk.inj (Option.some.inj h)).1.symm) prog hP

/-! ## 2. The linked call to a specified callee -/

/-- **A halting run of the image of a calling body of the wide class is a run of its caller
    prefix under the oracle of a specified callee**, from Boolean checks, at the bounds-checked
    instruction set. The callee is any run relation `X` that meets the specification of `c`; its
    bytes are not decoded. Under the hypotheses of `CheckedIsaCall.haltsC_of_linkedChecksKW`
    without those on the callee block, the bytes of the relocated body decode to the layout
    of its item list, which resolves to `prog` in front of every layout starting at the end
    of the body, and `prog` has a run under `oracleAt prog.length X` from the index of the
    position of the address state to a byte state that satisfies `Fin` with the end
    state. -/
theorem haltsO_of_linkedChecksX {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {ds : List DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr}
    (hbr : branchOKReloc (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : expectedReloc (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hdead : callDeadB c (fun _ => (res, c.args)) D.dead body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f (fun _ => (res, c.args))
      (callImg slotArr (fun _ => (res, c.args)) body) = true)
    (hseg : deadSegB D (callImg slotArr (fun _ => (res, c.args)) body) = true)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr (fun _ => (res, c.args)) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    decodeAt (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds)) 0
        (encodeLfundefBytesReloc symBase body)
        = some (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds))
      ∧ (∀ e x tl, resolveAll
          (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds)
            ++ ((encodeLfundefBytesReloc symBase body).length, e, x) :: tl)
          (layoutAt 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds)) = some prog)
      ∧ ∃ sA', HaltsO aMachine (oracleAt prog.length X) prog
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' := by
  have hCF := ImageAddrCallW.callFacts_of_printedAddrCWB hcls hshapes
  obtain ⟨hsaves, hF0, hFr⟩ := ImageAddrCallW.printedAddrCWB_reloc hcls
  obtain ⟨hdec, hres, -, hLk⟩ :=
    callerPrefix_of_bytes symBase hCF.toLinkFacts prog hsaves hF0 hFr hbr hP
  exact ⟨hdec, hres, ImageAddrCallW.haltsO_of_deadChecksS hsep hphys hgate hsites hCF.carry
    (X := fun _ => X) (c := fun _ => c) (tgt := fun _ => prog.length) (fun _ _ => hX)
    (fun _ _ _ tr _ h => ⟨rfl, tr, h⟩) hbits hflags hcond x86IsaK_checked (deadSteps_x86K hseg)
    (ImageAddrCallW.byteSegW_of_linked hCF hLk rsp hfr _) hfin hFin
    (fun _ _ _ hg _ bi ra f l hb hbi => siteStep_word hsep hphys hX hw hS hF hroom hdead
      ⟨bi, ra, (f, l), hb, hbi⟩
      (glue_regArgs (sitesOf_of_siteShapeB hshape hT) hw.wordOnly hw.wordRet hg))
    n hrun hfn hlen hL hI0 hA⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallX
