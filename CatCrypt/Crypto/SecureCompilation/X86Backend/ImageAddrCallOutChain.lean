/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee

@[expose] public section

set_option autoImplicit false

/-!
# The image run chain of a calling body whose calls write a word array

`ImageAddrCall.haltsC_of_linkedChecksS` turns a halting run of the image of a calling body
into a run through calls of its linked bytes, given the step of each call site
(`ImageAddrCall.SiteStep`). This module gives that step for call sites of one out-array
callee: a shadow instruction with the destination `A`, the array of a frame slot of length
`n`, whose summary has no word result and a word-array result of length `n`. The step of the
summary writes the array result to the carrier of `A` (`LprogIsa.retArr`), and
`ImageAddrCallOut.call_reestablishes_out` is the call step at that result. For a linked
function with an out layout (`LinkedFnCallee.OutLayout`) the callee reading is
`LinkedFnCallee.outCallee_of_linkedFn`.

## Main definitions

* `callDeadOutB`: the check of the dead names at the calls of a body whose calls write an
  array: no operand name is dead at a call, and the names dead at the call together with the
  names `exemptC c` are dead after it.

## Main results

* `callDeadOutB_spec`: soundness of `callDeadOutB` at a call instruction.
* `procStep_out`: the step of a summary with a word-array result and no word result writes
  the array of `runOut` to the carrier of the destination.
* `glue_out`: the step `LprogCallCut.Glue` at a shadow instruction of such a summary.
* `siteStep_out`: the step of a call site of an out callee.
* `haltsC_of_linkedChecks_out`: a halting run of the image of a calling body whose call sites
  call one linked function with an out layout is a run through calls of its linked bytes.
* `haltsO_of_linkedChecks_out`: such a run is a run of the program of the relocated item list
  under the oracle of the callee.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOutChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr Params Shape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOut
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
  (OutLayout outSig outSummary readIns outCallee_of_linkedFn footBelowOut_outSig)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (Glue)
open CatCrypt.Crypto.SecureCompilation.Haxc (ArgKind)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax (LinkedFn)

/-! ## 1. The dead names at the calls -/

/-- **The check of the dead names at the calls of a body whose calls write an array**: at
    each call instruction, at position `p`, no name of `args` is dead, and the names dead at
    `p` and the names `exemptC c` are dead at `p + 1`. -/
def callDeadOutB (c : CalleeSig) (args : List String) (E : Nat → List String) (body : Lcmd) :
    Bool :=
  (List.range body.length).all fun p => (body[p]?).all fun bi =>
    !isCallB bi.li_i ||
      (args.all (fun a => !(E p).contains a)
        && (E p ++ exemptC c).all (fun r => (E (p + 1)).contains r))

/-- **Soundness of `callDeadOutB`** at a call instruction. -/
theorem callDeadOutB_spec {c : CalleeSig} {args : List String} {E : Nat → List String}
    {body : Lcmd} (h : callDeadOutB c args E body = true) {p : Nat} {bi : Linstr}
    (hb : body[p]? = some bi) {ra : Option String} {tgt : String × LLabel}
    (hbi : bi.li_i = .Lcall ra tgt) :
    (∀ a ∈ args, a ∉ E p) ∧ ∀ r ∈ E p ++ exemptC c, r ∈ E (p + 1) := by
  simp only [callDeadOutB, List.all_eq_true, List.mem_range] at h
  have hp := h p (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simp only [Option.all_some, hbi, isCallB, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true] at hp
  exact ⟨fun a ha => by simpa using hp.1 a ha, fun r hr => by simpa using hp.2 r hr⟩

/-! ## 2. The step of a summary with a word-array result -/

/-- **The step of a summary with a word-array result of length `n` and no word result**
    writes the array of `runOut n` at the argument words to the carrier of the
    destination. -/
theorem procStep_out {pr : LprogIsa.ProcSummary} {n : Nat} (hout : pr.out = some n)
    (hrun : ∀ vs, pr.run vs = none) {dst : String} {srcs : List LOperand} {u v : LstateMF}
    (h : LprogIsa.procStep pr dst srcs u = some v) :
    ∃ vs arr, LprogIsa.argsRead pr.arrArgs u.prog.base 0 srcs = some vs
      ∧ pr.runOut n vs = some arr ∧ v = LprogIsa.retArr dst arr u := by
  unfold LprogIsa.procStep at h
  split_ifs at h
  obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
  rw [LprogIsa.ProcSummary.result_of_out hout (hrun vs), Option.map_map] at h
  obtain ⟨arr, harr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨vs, arr, hvs, harr, rfl⟩

/-- **The step `Glue` at a shadow instruction of a summary with a word-array result**, for a
    body whose shadow instructions are calls of `pr` on the registers `args` with the
    destination `A`. -/
theorem glue_out {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM}
    {pr : LprogIsa.ProcSummary} {n : Nat} (hout : pr.out = some n)
    (hrun : ∀ vs, pr.run vs = none) {A : String} {args : List String}
    (hsite : SitesOf T B pr A args) {p : Nat} {u v : LstateMF}
    (hg : Glue T (singletonProgM fn B) p u v) :
    ∃ vs arr, LprogIsa.argsRead pr.arrArgs u.prog.base 0 (args.map LOperand.reg) = some vs
      ∧ pr.runOut n vs = some arr ∧ v = LprogIsa.retArr A arr u := by
  obtain ⟨i, pr', dst, srcs, hi, hq, hstep⟩ := hg
  obtain ⟨rfl, rfl, rfl⟩ := hsite p i pr' dst srcs hi hq
  exact procStep_out hout hrun hstep

/-! ## 3. The step of a call site of an out callee -/

/-- **The step of a call site of an out callee.** Let the callee meet its specification and
    have the reading `pr` whose array result is written at the pointer `po`
    (`OutCallee`), the caller be separated (`CallerSep`) for a callee of `FootBelowOut`, and
    `A` be the array of a frame slot of length `n`. Let, at every call of the body, from an
    image state related by `ImgRel` to an address state that corresponds to a byte state,
    the entry state of the call satisfy `room`, the pointer name hold the base of `A` and the
    summary input of the entry state be the argument words of the operands `args`. Under `callDeadOutB` at a call position `p`, a
    step to the image state after the array result at the argument words of `args` is a step
    of the site (`SiteStep`) at the dead names of `p` and `p + 1`. -/
theorem siteStep_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {rd : AState → List (BitVec 64)}
    {po : String} {n : Nat} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : OutCallee c rd po n pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelowOut c G po n)
    (hroom : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ ret, room (entryOf ret sA))
    {qA A : String} (hqA : slotArr qA = some (A, n)) {args : List String}
    (hentry : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      sa.reg.getW po 64 = some (base A)
        ∧ ∀ ret vs, LprogIsa.argsRead pr.arrArgs s.prog.base 0 (args.map LOperand.reg)
            = some vs → rd (entryOf ret sA) = vs)
    {E : Nat → List String} (hdead : callDeadOutB c args E body = true) {p : Nat}
    (hb : ∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) {u v : LstateMF}
    (hv : ∃ vs arr, LprogIsa.argsRead pr.arrArgs u.prog.base 0 (args.map LOperand.reg)
        = some vs ∧ pr.runOut n vs = some arr ∧ v = LprogIsa.retArr A arr u) :
    SiteStep frame slotArr base rsp body X c (E p) (E (p + 1)) u v := by
  obtain ⟨bi, ra, t, hb, hbi⟩ := hb
  obtain ⟨vs, arr, hvs, harr, rfl⟩ := hv
  obtain ⟨hargs, hsub⟩ := callDeadOutB_spec hdead hb hbi
  refine ⟨A, .arr arr, rfl, fun u' hag => ?_, hsub⟩
  have hvs' : LprogIsa.argsRead pr.arrArgs u'.prog.base 0 (args.map LOperand.reg)
      = some vs := by
    rw [LprogIsa.argsRead_regs_congr pr.arrArgs hag.arr.symm 0
      fun x hx => (hag.regs x (hargs x hx)).symm]
    exact hvs
  intro sa zf sA hrel hc hcall ret
  obtain ⟨bi', ra', t', hb', hbi'⟩ := hcall
  obtain ⟨hptr, hrd⟩ := hentry u' sa zf sA hrel hc ⟨bi', ra', t', hb', hbi'⟩
  obtain ⟨hpre, hall⟩ := call_reestablishes_out hsep hphys hX hw hS hF hrel hc hb' hbi' hqA
    hptr ret (hrd ret vs hvs') (hroom u' sa zf sA hrel hc ⟨bi', ra', t', hb', hbi'⟩ ret) harr
  exact ⟨hpre, fun t sc hrun => (hall t sc hrun).2⟩

/-! ## 4. The linked run of a body that calls a linked function with an out layout -/

/-- **A halting run of the image of a calling body whose call sites call one linked function
    with an out layout is a run through calls of the program its linked bytes decode to.**
    Let `l` have the out layout `OutLayout l ins po n` and the code `q` of the callee block
    `cb` meet the out interface `outSig l ins n`; let `T` give the symbol `f` the summary
    `outSummary l ins n`, the image `callImg` at the destination `A` and the operands `args`
    pass `siteShapeB`, `A` be the array of a frame slot of length `n`, and `callDeadOutB`
    accept the table `D`. Let, at every call of the body, from an image state related by
    `ImgRel` to an address state that corresponds to a byte state, the entry state of the
    call satisfy the precondition of `l`, the pointer name `po` hold the base of `A` and the
    summary input `readIns ins` of the entry state be the argument words of `args`. Under the other hypotheses of `haltsC_of_linkedChecksS`, at the frame
    size `l.frame`, the bytes of the relocated body followed by `cb` decode to `prog`
    followed by `q` with its targets raised, and this program has a run through calls from
    the index of the position of the address state to a byte state that satisfies `Fin` with
    the end state. -/
theorem haltsC_of_linkedChecks_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {l : LinkedFn}
    {ins : List (String × ArgKind)} {po : String} {n : Nat} (hL : OutLayout l ins po n)
    (hX : CalleeSpec (Callee.runOf r q) (outSig l ins n)) (hq : ∀ tg, RInstr.call tg ∉ q)
    (hS : CallerSep frame slotArr base rsp l.frame)
    (hroom : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ ret, l.pre (entryOf ret sA))
    {qA A : String} (hqA : slotArr qA = some (A, n)) {args : List String}
    (hentry : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      sa.reg.getW po 64 = some (base A)
        ∧ ∀ ret vs, LprogIsa.argsRead (outSummary l ins n).arrArgs s.prog.base 0
            (args.map LOperand.reg) = some vs → readIns ins (entryOf ret sA) = vs)
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB l.frame body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {cb : List (BitVec 8)} {prog : List RInstr}
    (hcb : LprogBytesDecode.decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadOutB (outSig l ins n) args D.dead body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some (outSummary l ins n))
    (hshape : siteShapeB f A args (callImg slotArr A (args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (k : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)) k s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL0 : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  haltsC_of_linkedChecksS hsep hphys hgate hsites r hX hq hcls hshapes hfr symBase hcb hne hbr
    hP hflags hcond hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_out hsep hphys hX (outCallee_of_linkedFn hL) hS
      (footBelowOut_outSig hL) hroom hqA hentry hdead hb
      (glue_out (pr := outSummary l ins n) rfl (fun _ => rfl)
        (sitesOf_of_siteShapeB hshape hT) hg))
    k hrun hfn hlen hL0 hI0 hA

/-- **A halting run of the image of a calling body whose call sites call one linked function
    with an out layout is a run of the program of its relocated item list under the oracle
    of the callee.** The hypotheses are those of `haltsC_of_linkedChecks_out` with the callee
    an arbitrary run `X` that meets the out interface `outSig l ins n`, and the bytes of the
    callee replaced by the program `prog` of the relocated item list in front of a callee
    block at the index `tgt`. The run starts at the index `DecodePrintedCFG.posOf` of the
    position of the address state and ends in a byte state that satisfies `Fin` with the end
    state. -/
theorem haltsO_of_linkedChecks_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : OutLayout l ins po n) (hX : CalleeSpec X (outSig l ins n))
    (hS : CallerSep frame slotArr base rsp l.frame)
    (hroom : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ ret, l.pre (entryOf ret sA))
    {qA A : String} (hqA : slotArr qA = some (A, n)) {args : List String}
    (hentry : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      sa.reg.getW po 64 = some (base A)
        ∧ ∀ ret vs, LprogIsa.argsRead (outSummary l ins n).arrArgs s.prog.base 0
            (args.map LOperand.reg) = some vs → readIns ins (entryOf ret sA) = vs)
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB l.frame body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr} {tgt L : Nat}
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt L
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadOutB (outSig l ins n) args D.dead body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some (outSummary l ins n))
    (hshape : siteShapeB f A args (callImg slotArr A (args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (k : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)) k s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL0 : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', Callee.HaltsO aMachine (Callee.oracleAt tgt X) prog
        (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' :=
  haltsO_of_linkedChecksS hsep hphys hgate hsites hX hcls hshapes hfr symBase hP hflags hcond
    hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_out hsep hphys hX (outCallee_of_linkedFn hL) hS
      (footBelowOut_outSig hL) hroom hqA hentry hdead hb
      (glue_out (pr := outSummary l ins n) rfl (fun _ => rfl)
        (sitesOf_of_siteShapeB hshape hT) hg))
    k hrun hfn hlen hL0 hI0 hA

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOutChain
