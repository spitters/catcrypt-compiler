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
# The image run chain of a calling body whose calls read word arrays

`ImageAddrCallArr.call_reestablishes_arr` is the call step for a callee whose last argument
is one read-only word array. This module states the call step and the site step for a callee
whose parameters are a list `ins` of scalars and read-only word arrays in any order and whose
result is a word in a register. The summary input at an entry state is
`LinkedFnCallee.readIns ins`, and at the entry of a call it is the argument words of the
operands of the shadow instruction (`LinkedFnCallee.readIns_entry`). For a linked function
whose layout passes the parameters `ins` in registers and returns a word in a register
(`InsLayout`), the callee reading is `insCallee_of_linkedFn`.

## Main definitions

* `InsLayout`: the layout passes the parameters `ins` in the registers of their names and
  returns the result in the register of a result name; the footprint is among the frame
  bytes below the entry stack register.
* `insSummary`, `insSig`: the procedure summary and the interface of a linked function read
  on the parameters `ins` with a word result.
* `InsCallee`: the reading of an interface as a procedure summary at a summary input `rd`
  with a word result in a register.

## Main results

* `insCallee_of_linkedFn`: a linked function with an `InsLayout` is an `InsCallee`.
* `call_reestablishes_ins`: after every run of the callee, the result register holds the
  word of the summary and the relaxed relation holds at the step of the summary.
* `procStep_ins`, `glue_ins`: the step of a summary without a word-array result reads the
  argument words at its array positions and writes the word of `run`.
* `siteStep_ins`: the step of a call site of such a callee.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr Params Shape retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpFacts phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf outOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
  (readIns map_read_eq insVals_readIns run_of_post)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (Glue)
open CatCrypt.Crypto.SecureCompilation.Haxc (ArgKind)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax (LinkedFn insVals insArrArgs)
open CatCrypt.Crypto.Hax.ImpToNF (dec)

/-! ## 1. A linked function on scalars and read-only arrays with a word result -/

/-- **A layout on parameters with a word result**: the parameters of the layout are, in
    order, the parameters `ins`, each a name with its kind, in the registers of the names;
    the result is read back from the register of the general-purpose name `res`, which the
    record clobbers; and the footprint of the record is among the `l.frame` bytes below its
    entry stack register. -/
structure InsLayout (l : LinkedFn) (ins : List (String × ArgKind)) (res : String) : Prop where
  /-- The parameters: the kind of each parameter of `ins` in the register of its name. -/
  args : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2)
  /-- The result is the register of `res`. -/
  result : l.layout.result = .reg (phys res)
  /-- The parameter names are general-purpose names. -/
  ins_gp : ∀ p ∈ ins, gpOk p.1 = true
  /-- The result name is a general-purpose name. -/
  res_gp : gpOk res = true
  /-- The register of the result name is clobbered. -/
  res_clob : l.clob.contains (phys res) = true
  /-- The footprint is among the frame bytes below the entry stack register. -/
  foot : ∀ s x, l.foot s x → InFrame (s.regs "%rsp") l.frame x

/-- **The procedure summary of a linked function on the parameters `ins` with a word
    result**: the array positions of the kinds of `ins`, and as word result the meaning at
    the source values of the argument words under the kinds of `ins`, decoded as a word. The
    array function decodes the same value as an array of words; the summary has no
    word-array result, so the step never reads it. -/
def insSummary (l : LinkedFn) (ins : List (String × ArgKind)) : LprogIsa.ProcSummary where
  arity := l.params.length
  run xs := (l.sem (insVals (ins.map (·.2)) xs)).bind (dec (.word 64))
  arrArgs := insArrArgs (ins.map (·.2))
  runOut m xs := (l.sem (insVals (ins.map (·.2)) xs)).bind (dec (.arr m (.word 64)))

/-- The summary on parameters has no word-array result. -/
theorem insSummary_retWord (l : LinkedFn) (ins : List (String × ArgKind)) :
    (insSummary l ins).RetWord :=
  rfl

/-- **The interface of a linked function on the parameters `ins` with a word result**: the
    parameter names of `ins`, the result name `res`, the clobbered registers, footprint,
    postcondition and public relation of the record, and as precondition the precondition
    of the record at an entry state at whose `readIns ins` the summary `insSummary` is
    defined. -/
def insSig (l : LinkedFn) (ins : List (String × ArgKind)) (res : String) : CalleeSig where
  args := ins.map (·.1)
  res := some res
  clob := fun x => l.clob.contains x
  pre := fun s => l.pre s ∧ ((insSummary l ins).run (readIns ins s)).isSome
  foot := l.foot
  post := l.post
  pub := l.pub

/-- The footprint of the interface on parameters is among the `l.frame` bytes below the
    entry stack register. -/
theorem footBelow_insSig {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hL : InsLayout l ins res) : FootBelow (insSig l ins res) l.frame :=
  hL.foot

/-- Under a layout on parameters, the values the layout reads are the source values of
    `readIns`. -/
theorem read_insLayout {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hL : InsLayout l ins res) (s : AState) :
    l.layout.args.map (·.read s) = insVals (ins.map (·.2)) (readIns ins s) := by
  rw [map_read_eq, hL.args, insVals_readIns, List.map_map]
  rfl

/-- **The reading of an interface as a procedure summary at a summary input with a word
    result.** The summary input at an entry state is `rd`; the result name `res` is a
    general-purpose name whose register is the result register of the interface and in its
    clobber set; the precondition holds at an entry state that satisfies `room` and at whose
    summary input the summary is defined; and the postcondition gives the word of the
    summary in the register of `res` at the return. -/
structure InsCallee (c : CalleeSig) (rd : AState → List (BitVec 64)) (res : String)
    (pr : LprogIsa.ProcSummary) (room : AState → Prop) : Prop where
  /-- The result register of the interface is that of `res`. -/
  res_eq : c.res = some res
  /-- The result name is a general-purpose name. -/
  res_gp : gpOk res = true
  /-- The register of the result name is in the clobber set. -/
  res_clob : c.clob (phys res) = true
  /-- The precondition, from `room` and a defined summary. -/
  pre : ∀ s, room s → (pr.run (rd s)).isSome = true → c.pre s
  /-- The result register at the return holds the word of the summary. -/
  post : ∀ s s', c.pre s → c.post s s' → pr.run (rd s) = some (s'.regs (phys res))

/-- **A linked function with a layout on parameters is a callee on those parameters.** Under
    `InsLayout`, the interface `insSig` has the reading `insSummary` at the summary input
    `readIns ins`, on the precondition of the record. -/
theorem insCallee_of_linkedFn {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hL : InsLayout l ins res) :
    InsCallee (insSig l ins res) (readIns ins) res (insSummary l ins) l.pre where
  res_eq := rfl
  res_gp := hL.res_gp
  res_clob := hL.res_clob
  pre _ h hd := ⟨h, hd⟩
  post _ _ h hpost := run_of_post hL.result (read_insLayout hL _) h.1 hpost h.2

/-! ## 2. The call step -/

/-- **A call on scalars and read-only arrays re-establishes the relaxed relation.** Let
    `ImgRel` and `ACorr` hold at a call instruction of a body of the class `physImgB`, the
    callee meet its specification and have the reading `pr` at the summary input `rd` with
    the word result in the register of `res`, the caller be separated (`CallerSep`) for a
    callee whose footprint is among the `G` bytes below its entry stack register, the summary
    input of the entry state be `vs`, the entry state satisfy `room`, and the summary give
    the word `v` at `vs`. Then the entry state satisfies the precondition, and for every run
    of the callee, after the return: the result register holds `v`, and there is an address
    state at the next position that corresponds to the byte state and is related, up to the
    names `exemptC c` and the flags, to the image state after the step of the summary. -/
theorem call_reestablishes_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {rd : AState → List (BitVec 64)}
    {res : String} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : InsCallee c rd res pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelow c G) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt) (ret : Nat)
    {vs : List (BitVec 64)} (hrd : rd (entryOf ret sA) = vs) (hroom : room (entryOf ret sA))
    {v : BitVec 64} (hv : pr.run vs = some v) :
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      (retOps.foldl aMachine.exec sc).regs (phys res) = v
        ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1
          ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
          ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retWord res v s) sa' := by
  have hpre : c.pre (entryOf ret sA) := hw.pre _ hroom (by rw [hrd, hv]; rfl)
  refine ⟨hpre, fun t sc hrun => ?_⟩
  obtain ⟨hA, hI, hpost⟩ := call_reestablishes hsep hphys hX hrel hc hb hbi ret hpre
    (footClear_of_callerSep hS hF hc.sp ret) hrun ⟨fun _ => 0, false, false, false⟩
  have hres : (retOps.foldl aMachine.exec sc).regs (phys res) = v := by
    have h1 := hw.post _ _ hpre hpost
    rw [hrd, hv] at h1
    rw [(call_return hX ret sA hpre hrun).2.1 _ (gpFacts hw.res_gp).physNe]
    exact (Option.some.inj h1).symm
  exact ⟨hres, _, rfl, hA, _, _,
    agreeOffF_retWord c (outOf (retOps.foldl aMachine.exec sc) _) s hw.res_eq
      (by simp [clobN, hw.res_gp, hw.res_clob]) hres,
    hI⟩

/-! ## 3. The step of a summary with a word result -/

/-- **The step of a summary without a word-array result** reads the argument words at the
    array positions of the summary and writes the word of `run` at them to the
    destination. -/
theorem procStep_ins {pr : LprogIsa.ProcSummary} (hrw : pr.RetWord) {dst : String}
    {srcs : List LOperand} {u v : LstateMF} (h : LprogIsa.procStep pr dst srcs u = some v) :
    ∃ vs w, LprogIsa.argsRead pr.arrArgs u.prog.base 0 srcs = some vs
      ∧ pr.run vs = some w ∧ v = LprogIsa.retWord dst w u := by
  rw [LprogIsa.procStep_of_retWord hrw] at h
  split at h
  · obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨vs, w, hvs, hw, rfl⟩
  · cases h

/-- **The step `Glue` at a shadow instruction of a summary without a word-array result**,
    for a body whose shadow instructions are calls of `pr` on the registers `(site p).2` with
    the destination `(site p).1`. -/
theorem glue_ins {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM}
    {pr : LprogIsa.ProcSummary} (hrw : pr.RetWord) {site : Nat → String × List String}
    (hsite : SitesOf T B (fun _ => pr) site) {p : Nat} {u v : LstateMF}
    (hg : Glue T (singletonProgM fn B) p u v) :
    ∃ vs w, LprogIsa.argsRead pr.arrArgs u.prog.base 0 ((site p).2.map LOperand.reg)
        = some vs
      ∧ pr.run vs = some w ∧ v = LprogIsa.retWord (site p).1 w u := by
  obtain ⟨i, pr', dst, srcs, hi, hq, hstep⟩ := hg
  obtain ⟨rfl, rfl, rfl⟩ := hsite p i pr' dst srcs hi hq
  exact procStep_ins hrw hstep

/-! ## 4. The step of a call site -/

/-- **The step of a call site of a callee on scalars and read-only arrays.** Let the callee
    meet its specification and have the reading `pr` at the summary input `rd` with the word
    result in the register of `res` (`InsCallee`), and the caller be separated (`CallerSep`)
    for a callee of `FootBelow`. Let, at every call of the body, from an image state related
    by `ImgRel` to an address state that corresponds to a byte state, the entry state of the
    call satisfy `room` and the summary input of the entry state be the argument words of the
    operands of the site of the call. Under `callDeadB` at a call position `p` whose site has
    the destination `res`, a step from an image state at the counter `p` to the image state
    after the word of the summary at the argument words of `(site p).2` is a step of the
    site (`SiteStep`) at the dead names of `p` and `p + 1`. -/
theorem siteStep_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {rd : AState → List (BitVec 64)}
    {res : String} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : InsCallee c rd res pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelow c G)
    (hroom : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ ret, room (entryOf ret sA))
    {site : Nat → String × List String}
    (hentry : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ ret vs, LprogIsa.argsRead pr.arrArgs s.prog.base 0
        ((site sa.reg.lpc).2.map LOperand.reg) = some vs → rd (entryOf ret sA) = vs)
    {E : Nat → List String} (hdead : callDeadB c site E body = true) {p : Nat}
    (hb : ∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) (hres : (site p).1 = res)
    {u v : LstateMF} (hpc : u.prog.base.reg.lpc = p)
    (hv : ∃ vs w, LprogIsa.argsRead pr.arrArgs u.prog.base 0 ((site p).2.map LOperand.reg)
        = some vs ∧ pr.run vs = some w ∧ v = LprogIsa.retWord (site p).1 w u) :
    SiteStep frame slotArr base rsp body X c (E p) (E (p + 1)) u v := by
  obtain ⟨bi, ra, t, hb, hbi⟩ := hb
  obtain ⟨vs, w, hvs, hw', rfl⟩ := hv
  obtain ⟨hargs, hsub⟩ := callDeadB_spec hdead hb hbi
  rw [hres] at hsub ⊢
  refine ⟨res, .word w, rfl, fun u' hag => ?_, hsub⟩
  have hvs' : LprogIsa.argsRead pr.arrArgs u'.prog.base 0 ((site p).2.map LOperand.reg)
      = some vs := by
    rw [LprogIsa.argsRead_regs_congr pr.arrArgs hag.arr.symm 0
      fun x hx => (hag.regs x (hargs x hx)).symm]
    exact hvs
  intro sa zf sA hrel hc hcall ret
  have hsp : sa.reg.lpc = p := hrel.pc.trans (hag.pc.symm.trans hpc)
  obtain ⟨bi', ra', t', hb', hbi'⟩ := hcall
  obtain ⟨hpre, hall⟩ := call_reestablishes_ins hsep hphys hX hw hS hF hrel hc hb' hbi' ret
    (hentry u' sa zf sA hrel hc ⟨bi', ra', t', hb', hbi'⟩ ret vs (by rw [hsp]; exact hvs'))
    (hroom u' sa zf sA hrel hc ⟨bi', ra', t', hb', hbi'⟩ ret) hw'
  exact ⟨hpre, fun t sc hrun => (hall t sc hrun).2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain
