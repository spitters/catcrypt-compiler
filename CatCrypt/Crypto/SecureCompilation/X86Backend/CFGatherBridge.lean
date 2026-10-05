/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdToOwnedCF
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdToOwnedCF
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopExporterCTBridge
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopExporterCTBridge
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn
public meta import CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront
public import CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront

/-!
# Speculative leakage across a back-edge and across a call

`GatherImmForms.gatherJBlock6` lowers an `Lcmd` through `lowerCov6`, which has no
arm for `LinstrR.Llabel`, `LinstrR.Lcond` or `LinstrR.Lcall`, so it returns `none`
on any body carrying a control transfer. The speculative statements phrased over
its output — `FrontCTBridge.compileFromHax_cfSpec_state_independent`,
`compileFromHax_cfSpec_mem_addr_in_program`,
`SpeculativeCTReturn.toLprogPhysAbi_gather_callSpec_state_independent` — therefore
say nothing about a loop-exported or call-carrying body.

This module carries them across a back-edge and across a call, using
`LcmdToOwnedCF.lcmdToOwnedCF` and a call-aware companion `lcmdToCallCF` in place
of that gather.

## The back-edge frame

`backEdgeFrame pre top region cc` is the shape every bottom-tested loop exporter
emits: a straight-line prefix whose last instruction seeds the counter, the loop
label, the loop region ending in the counter test, and the conditional back-edge.
`parseLcmdCF_backEdgeFrame` shows the recogniser's parse of such a frame is the
sequence `straight pre ; loop n (straight region) ; straight []`, given a
compile-time-positive counter seed, straight-line prefix and region, and a
condition-code back-edge. `forLoopLcmd`, `forLoopLcmdN` and `forLoopLcmdNCall`
emit that shape (`forLoopLcmd_eq_backEdgeFrame` and its two companions); the
call-aware export carries the `FRAMEADD` scratch declaration of its body's buffer
bindings ahead of the prefix, and walks its body with `loopBodyWalkNSel`. The
single-binder and multi-binder walks emit straight-line instructions only
(`loopBodyWalk_straight`, `loopBodyWalkN_straight`), so the parse of those two
exports is pinned outright; the call-aware export's parse is pinned on a body
walk assumed straight-line, which a body issuing a real `Lcall` does not
satisfy. What remains for the whole recogniser to succeed is that each
leaf lowers through `lowerCov6`; `#guard`s at the end of §10 discharge that on
the deployed `dblLoopBody` export and on a `compileFromHax` output.

## The call frame

`lcmdToCallCF resolve` splits an `Lcmd` at its top-level `LinstrR.Lcall`s: each
maximal call-free run recognises as a `MachineConstantTime.OwnedCF` and each call
becomes a `SpeculativeCTReturn.CallCF.call` node, with the callee supplied by
`resolve` and the continuation the recognised remainder.
`lcmdToCallCF_callAllDirect` carries `AllocCTPreservation.lcmdDirect` of the body
to `CallAllDirect` of the recognised block.

## The two results

`cfSpecExec_state_independent` and `callSpecExec_state_independent` are the
leakage-equality halves: a branch-free index-free block has, under a state-blind
predictor, the same speculative trace from any two machine states, for every
window. The predictor hypothesis is `PubDriven noPub` resp. `RSBPubDriven noPub`
— by `pubDriven_noPub_iff`, exactly "the predictor's decision does not read the
machine state". It is not removable:
`SpeculativeCTControlFlow.secretDrivenPredictor_leaks` and
`SpeculativeCTReturn.secretDrivenRetPredictor_leaks` separate two states with a
secret-reading predictor on blocks that are `CFControlled` resp. `CallControlled`
and index-free.

`compileFromHax_rolledLoop_cfSpec_mem_addr_in_program` and
`lcmdToCallCF_spec_mem` are the predictor-free halves: every memory event of the
speculative trace — transient events across the back-edge or on a mispredicted
return included — names an address the program text contains.

## Scope

`OwnedCF.loop` carries a `Nat` trip count, so the runtime-trip exporters
(`forLoopLcmdNRt`, `whileLcmdNz`, `forLoopLcmdNRtNested`, `blockLoopFrame`,
`forLoopBlockLcmd`) are outside the recogniser: they seed the counter from an
operand, and they wrap the loop in a zero-trip top guard whose guard is a
condition code rather than a general-purpose register.

`CallCF` places a call node at the top of a block, so a call inside a counted loop
— what `forLoopLcmdNCall` emits through `callMarshalHere` — has no `CallCF` image:
splitting at that call leaves the loop label without its back-edge, and the
call-free run does not parse.

Execution agreement between the recognised block's semantics and the emitted
command's own `lsem` is not established here; `LcmdToOwnedCF` states what it
needs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CFGatherBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdToOwnedCF
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
  (OwnedCF IsDirect PubPred agreePub CFControlled CTAddressed MLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
  (CFPredictor PubDriven SLeak cfSpecExec CFAllDirect cfAddrs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (isIndexed lcmdDirect lcmdDirect_iff lcmdDirect_of_mem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn
  (CallCF CallAllDirect CallControlled RSB RSBPredictor RSBPubDriven callSpecExec
   callAddrs)
open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
open CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-! ## 1. Prefix-uniform `takeWhile` / `dropWhile` -/

theorem takeWhile_append_of_all {α : Type} {p : α → Bool} {a b : List α}
    (h : ∀ x ∈ a, p x = true) : (a ++ b).takeWhile p = a ++ b.takeWhile p := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.takeWhile_cons, if_pos (h x (List.mem_cons_self ..)),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy)), List.cons_append]

theorem dropWhile_append_of_all {α : Type} {p : α → Bool} {a b : List α}
    (h : ∀ x ∈ a, p x = true) : (a ++ b).dropWhile p = b.dropWhile p := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.dropWhile_cons, if_pos (h x (List.mem_cons_self ..)),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## 2. The loop-body walks emit straight-line instructions -/

/-- Every op exports to an `Lopn`: no arm of `opToLinstrR` builds a label, a jump
    or a call. -/
theorem opToLinstrR_isStraightR (op : JasminOp) (dst : String)
    (srcs : List LOperand) : isStraightR (opToLinstrR op dst srcs) = true := by
  cases op <;> simp only [opToLinstrR] <;> (try split) <;> (try split) <;> rfl

/-- The single-binder loop-body walk emits straight-line instructions only. -/
theorem loopBodyWalk_straight (d : Nat) (accReg : String) (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat),
      ∀ i ∈ (loopBodyWalk d accReg immSlotMap c curDepth).1, isStraightL i = true
  | _, _, .ret _, _ => by intro i hi; simp [loopBodyWalk] at hi
  | _, _, .var e body, curDepth => by
      intro i hi
      rw [loopBodyWalk] at hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact opToLinstrR_isStraightR _ _ _
      · exact loopBodyWalk_straight d accReg immSlotMap body (curDepth + 1) i hi

/-- The multi-binder loop-body walk emits straight-line instructions only. -/
theorem loopBodyWalkN_straight (d : Nat) (accReg idxReg : String)
    (invRegs : List String) (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
      (curDepth : Nat),
      ∀ i ∈ (loopBodyWalkN d accReg idxReg invRegs immSlotMap c curDepth).1,
        isStraightL i = true
  | _, _, .ret _, _ => by intro i hi; simp [loopBodyWalkN] at hi
  | _, _, .var e body, curDepth => by
      intro i hi
      rw [loopBodyWalkN] at hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact opToLinstrR_isStraightR _ _ _
      · exact loopBodyWalkN_straight d accReg idxReg invRegs immSlotMap body
          (curDepth + 1) i hi

/-- A straight-line instruction is not the return. -/
theorem isLret_of_isStraightL {i : Linstr} (h : isStraightL i = true) :
    isLret i = false := by
  unfold isStraightL isStraightR at h
  unfold isLret
  split at h <;> simp_all

/-! ## 3. The bottom-tested back-edge frame -/

/-- A bottom-tested back-edge frame: a straight-line prefix ending in the counter
    seed, the loop label, the loop region ending in the counter test, and the
    conditional back-edge to the label. -/
def backEdgeFrame (pre : Lcmd) (top : LLabel) (region : Lcmd) (cc : String) : Lcmd :=
  pre ++ (⟨0, .Llabel .internal top⟩ :: (region ++ [⟨0, .Lcond (.reg cc) top⟩]))

/-- A straight-line instruction is not a back-edge. -/
theorem isBackEdge_of_isStraightL {top : LLabel} {i : Linstr}
    (h : isStraightL i = true) : isBackEdge top i = false := by
  unfold isStraightL isStraightR at h
  unfold isBackEdge
  split at h <;> simp_all

/-- **A bottom-tested back-edge frame parses.** The prefix is a straight-line
    leaf, the region between the label and the back-edge is the body of a counted
    loop whose trip count is the immediate the prefix's last instruction seeds the
    counter with, and nothing follows the back-edge. -/
theorem parseLcmdCF_backEdgeFrame {pre region : Lcmd} {top : LLabel}
    {cc ctr : String} {n fuel : Nat} (hfuel : 2 ≤ fuel)
    (hpre : ∀ i ∈ pre, isStraightL i = true)
    (hseed : pre.getLast?.bind counterSeed? = some (ctr, n)) (hn : 0 < n)
    (hregion : ∀ i ∈ region, isStraightL i = true)
    (hok : loopFrameOk ctr region = true) (hcc : isCondCode cc = true) :
    parseLcmdCF fuel (backEdgeFrame pre top region cc)
      = some (.seq (.straight pre)
          (.seq (.loop n (.straight region)) (.straight []))) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
  have hlbl : isStraightL (⟨0, .Llabel .internal top⟩ : Linstr) = false := rfl
  have hdrop : (backEdgeFrame pre top region cc).dropWhile isStraightL
      = ⟨0, .Llabel .internal top⟩ :: (region ++ [⟨0, .Lcond (.reg cc) top⟩]) := by
    rw [backEdgeFrame, dropWhile_append_of_all hpre]
    simp [hlbl]
  have htake : (backEdgeFrame pre top region cc).takeWhile isStraightL = pre := by
    rw [backEdgeFrame, takeWhile_append_of_all hpre]
    simp [hlbl]
  have hnbe : ∀ i ∈ region, (!isBackEdge top i) = true := fun i hi => by
    simp [isBackEdge_of_isStraightL (hregion i hi)]
  have hbe : isBackEdge top (⟨0, .Lcond (.reg cc) top⟩ : Linstr) = true := by
    simp [isBackEdge, hcc]
  have hdrop2 : (region ++ [(⟨0, .Lcond (.reg cc) top⟩ : Linstr)]).dropWhile
      (fun j => !isBackEdge top j) = [⟨0, .Lcond (.reg cc) top⟩] := by
    rw [dropWhile_append_of_all hnbe]
    simp [hbe]
  have htake2 : (region ++ [(⟨0, .Lcond (.reg cc) top⟩ : Linstr)]).takeWhile
      (fun j => !isBackEdge top j) = region := by
    rw [takeWhile_append_of_all hnbe]
    simp [hbe]
  simp only [parseLcmdCF, hdrop, htake, hdrop2, htake2, hseed]
  simp [hn, hok]

/-- No instruction of a back-edge frame is the return. -/
theorem backEdgeFrame_no_lret {pre region : Lcmd} {top : LLabel} {cc : String}
    (hpre : ∀ i ∈ pre, isStraightL i = true)
    (hregion : ∀ i ∈ region, isStraightL i = true) :
    ∀ i ∈ backEdgeFrame pre top region cc, (!isLret i) = true := by
  intro i hi
  rw [backEdgeFrame] at hi
  rcases List.mem_append.mp hi with h | h
  · simp [isLret_of_isStraightL (hpre i h)]
  rcases List.mem_cons.mp h with rfl | h
  · rfl
  rcases List.mem_append.mp h with h' | h'
  · simp [isLret_of_isStraightL (hregion i h')]
  · simp only [List.mem_singleton] at h'; subst h'; rfl

theorem backEdgeFrame_length (pre region : Lcmd) (top : LLabel) (cc : String) :
    2 ≤ (backEdgeFrame pre top region cc).length + 1 := by
  rw [backEdgeFrame]
  simp only [List.length_append, List.length_cons]
  omega

/-! ## 4. The regions of the emitted frames -/

/-- The region a multi-binder loop frame places between its label and its
    back-edge: the body copy `w.1`, the accumulator feedback, the index advance,
    the counter decrement, the invariant-base touches and the counter test. -/
def frameNRegion (accReg idxReg ctr : String) (invRegs : List String)
    (w : Lcmd × String) : Lcmd :=
  w.1
  ++ (if w.2 == accReg then []
      else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg w.2]⟩])
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invRegs.map (fun r =>
       ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩ ]

/-- The region a single-binder loop frame places between its label and its
    back-edge: the body copy `w.1`, the accumulator feedback, the counter
    decrement and the counter test. -/
def frame1Region (accReg ctr : String) (w : Lcmd × String) : Lcmd :=
  w.1
  ++ (if w.2 == accReg then []
      else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg w.2]⟩])
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩ ]

/-- Every instruction of a frame's region is straight-line when the body copy
    is. -/
theorem frameNRegion_straight {accReg idxReg ctr : String} {invRegs : List String}
    {w : Lcmd × String} (hb : ∀ i ∈ w.1, isStraightL i = true) :
    ∀ i ∈ frameNRegion accReg idxReg ctr invRegs w, isStraightL i = true := by
  intro i hi
  rw [frameNRegion] at hi
  simp only [List.mem_append] at hi
  rcases hi with ((((h1 | h2) | h3) | h4) | h5)
  · exact hb i h1
  · split at h2
    · simp at h2
    · simp only [List.mem_singleton] at h2; subst h2; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl <;> rfl
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp h4; rfl
  · simp only [List.mem_singleton] at h5; subst h5; rfl

/-- A frame's region ends with the counter test. -/
theorem frameNRegion_getLast? (accReg idxReg ctr : String) (invRegs : List String)
    (w : Lcmd × String) :
    (frameNRegion accReg idxReg ctr invRegs w).getLast?
      = some ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩ :=
  List.getLast?_concat ..

/-- A frame's region decrements the counter. -/
theorem frameNRegion_counterDec (accReg idxReg ctr : String)
    (invRegs : List String) (w : Lcmd × String) :
    (frameNRegion accReg idxReg ctr invRegs w).any (isCounterDec ctr) = true := by
  have hmem : (⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ : Linstr)
      ∈ frameNRegion accReg idxReg ctr invRegs w := by
    rw [frameNRegion]
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr ?_)))))
    simp
  refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
  simp [isCounterDec, isSubMnem, withWidthTag]

/-- A multi-binder frame's region is a loop body. -/
theorem frameNRegion_loopFrameOk {accReg idxReg ctr : String}
    {invRegs : List String} {w : Lcmd × String}
    (hb : ∀ i ∈ w.1, isStraightL i = true) :
    loopFrameOk ctr (frameNRegion accReg idxReg ctr invRegs w) = true := by
  unfold loopFrameOk
  rw [frameNRegion_getLast?, frameNRegion_counterDec]
  simp [List.all_eq_true.mpr (frameNRegion_straight hb), isCounterTest, isCmpMnem,
    withWidthTag]

/-- Every instruction of a single-binder frame's region is straight-line when the
    body copy is. -/
theorem frame1Region_straight {accReg ctr : String} {w : Lcmd × String}
    (hb : ∀ i ∈ w.1, isStraightL i = true) :
    ∀ i ∈ frame1Region accReg ctr w, isStraightL i = true := by
  intro i hi
  rw [frame1Region] at hi
  simp only [List.mem_append] at hi
  rcases hi with (((h1 | h2) | h3) | h4)
  · exact hb i h1
  · split at h2
    · simp at h2
    · simp only [List.mem_singleton] at h2; subst h2; rfl
  · simp only [List.mem_singleton] at h3; subst h3; rfl
  · simp only [List.mem_singleton] at h4; subst h4; rfl

theorem frame1Region_getLast? (accReg ctr : String) (w : Lcmd × String) :
    (frame1Region accReg ctr w).getLast?
      = some ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩ :=
  List.getLast?_concat ..

theorem frame1Region_counterDec (accReg ctr : String) (w : Lcmd × String) :
    (frame1Region accReg ctr w).any (isCounterDec ctr) = true := by
  have hmem : (⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ : Linstr)
      ∈ frame1Region accReg ctr w := by
    rw [frame1Region]
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
    simp
  refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
  simp [isCounterDec, isSubMnem, withWidthTag]

/-- A single-binder frame's region is a loop body. -/
theorem frame1Region_loopFrameOk {accReg ctr : String} {w : Lcmd × String}
    (hb : ∀ i ∈ w.1, isStraightL i = true) :
    loopFrameOk ctr (frame1Region accReg ctr w) = true := by
  unfold loopFrameOk
  rw [frame1Region_getLast?, frame1Region_counterDec]
  simp [List.all_eq_true.mpr (frame1Region_straight hb), isCounterTest, isCmpMnem,
    withWidthTag]

/-- The scratch-byte declaration a loop frame carries ahead of its prefix: the
    `FRAMEADD` directive for the loop body's buffer bindings, and nothing when
    the body lays no buffer. -/
def frameAddPre (bufs : List (Nat × Nat)) : Lcmd :=
  if bufs.isEmpty then []
  else [⟨0, .Lopn [] "FRAMEADD" [.imm (loopBufTotal bufs)]⟩]

/-- The scratch-byte declaration is straight-line. -/
theorem frameAddPre_straight (bufs : List (Nat × Nat)) :
    ∀ i ∈ frameAddPre bufs, isStraightL i = true := by
  intro i hi
  rw [frameAddPre] at hi
  split at hi
  · simp at hi
  · simp only [List.mem_singleton] at hi; subst hi; rfl

/-- The body walk the call-aware multi-binder loop export selects: the
    buffer-aware walk when the loop body lays scratch buffers or updates its
    accumulator in place, and the call-aware walk otherwise. -/
def loopBodyWalkNSel (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (body : Com jasminDialect Γ t) (startDepth : Nat) : Lcmd × String :=
  if (loopScratchBufBindings body startDepth).isEmpty
      && (loopInPlaceBufSlot body startDepth).isNone then
    loopBodyWalkNCall d accReg idxReg invRegs immSlotMap body startDepth
  else
    loopBodyWalkNBuf d accReg idxReg invRegs
      (loopScratchBufBindings body startDepth)
      (loopInPlaceBufSlot body startDepth) immSlotMap body startDepth

/-- A body walk with its returned name read as the accumulator when the result
    lives in a frame slot (a `mem.`-prefixed name) rather than a register. The
    frame region's feedback move is `MOV accReg, w.2` guarded by `w.2 == accReg`,
    and a frame slot carries no register to move from. -/
def frameFeedbackWalk (accReg : String) (w : Lcmd × String) : Lcmd × String :=
  (w.1, if hasPrefix w.2 "mem." then accReg else w.2)

/-- Reading the returned name as the accumulator keeps the body copy, so a
    straight-line body copy stays straight-line. -/
theorem frameFeedbackWalk_straight (accReg : String) {w : Lcmd × String}
    (hb : ∀ i ∈ w.1, isStraightL i = true) :
    ∀ i ∈ (frameFeedbackWalk accReg w).1, isStraightL i = true := hb

/-- The region of a frame over a slot-aware body walk: the body copy, the
    accumulator feedback under the widened guard, the index advance, the counter
    decrement, the invariant-base touches and the counter test. -/
theorem frameNRegion_frameFeedbackWalk (accReg idxReg ctr : String)
    (invRegs : List String) (w : Lcmd × String) :
    frameNRegion accReg idxReg ctr invRegs (frameFeedbackWalk accReg w)
      = w.1
        ++ (if w.2 == accReg || hasPrefix w.2 "mem." then []
            else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg w.2]⟩])
        ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
           , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
        ++ invRegs.map (fun r =>
             ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
        ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩ ] := by
  rw [frameNRegion, frameFeedbackWalk]
  cases hm : hasPrefix w.2 "mem." <;> simp [hm]

/-! ## 5. The exporters emit back-edge frames -/

/-- The straight-line prefix of a multi-binder loop frame: the accumulator seed,
    the index init and the counter seed. -/
def frameNPre (accReg idxReg ctr : String) (initOp : LOperand) (n : Nat) : Lcmd :=
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm n]⟩ ]

/-- The straight-line prefix of a single-binder loop frame: the accumulator seed
    and the counter seed. -/
def frame1Pre (accReg ctr : String) (initOp : LOperand) (n : Nat) : Lcmd :=
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm n]⟩ ]

theorem frameNPre_straight (accReg idxReg ctr : String) (initOp : LOperand)
    (n : Nat) : ∀ i ∈ frameNPre accReg idxReg ctr initOp n, isStraightL i = true := by
  intro i hi
  simp only [frameNPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem frame1Pre_straight (accReg ctr : String) (initOp : LOperand) (n : Nat) :
    ∀ i ∈ frame1Pre accReg ctr initOp n, isStraightL i = true := by
  intro i hi
  simp only [frame1Pre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem frameNPre_seed (accReg idxReg ctr : String) (initOp : LOperand) (n : Nat) :
    (frameNPre accReg idxReg ctr initOp n).getLast?.bind counterSeed?
      = some (ctr, n) := by
  simp [frameNPre, counterSeed?, isMovMnem, withWidthTag]

theorem frame1Pre_seed (accReg ctr : String) (initOp : LOperand) (n : Nat) :
    (frame1Pre accReg ctr initOp n).getLast?.bind counterSeed? = some (ctr, n) := by
  simp [frame1Pre, counterSeed?, isMovMnem, withWidthTag]

/-- A prefix carrying the scratch-byte declaration ahead of a multi-binder loop
    frame's seeds is straight-line. -/
theorem frameAddPre_frameNPre_straight (bufs : List (Nat × Nat))
    (accReg idxReg ctr : String) (initOp : LOperand) (n : Nat) :
    ∀ i ∈ frameAddPre bufs ++ frameNPre accReg idxReg ctr initOp n,
      isStraightL i = true := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact frameAddPre_straight bufs i h
  · exact frameNPre_straight accReg idxReg ctr initOp n i h

/-- The scratch-byte declaration leaves the counter seed the prefix's last
    instruction. -/
theorem frameAddPre_frameNPre_seed (bufs : List (Nat × Nat))
    (accReg idxReg ctr : String) (initOp : LOperand) (n : Nat) :
    (frameAddPre bufs ++ frameNPre accReg idxReg ctr initOp n).getLast?.bind
        counterSeed? = some (ctr, n) := by
  simp [frameNPre, counterSeed?, isMovMnem, withWidthTag]

/-- `forLoopLcmdN` emits a bottom-tested back-edge frame. -/
theorem forLoopLcmdN_eq_backEdgeFrame (d : Nat) (accReg : String)
    (initOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (p : JLoopBodyN accTy invTys) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) :
    forLoopLcmdN d accReg initOp p invOps immSlotMap
      = backEdgeFrame (frameNPre accReg (loopIdx d) (loopCtr d) initOp p.n) d
          (frameNRegion accReg (loopIdx d) (loopCtr d)
            (invOps.filterMap (fun o => match o with | .reg r => some r | _ => none))
            (loopBodyWalkN d accReg (loopIdx d)
              (invOps.filterMap (fun o => match o with | .reg r => some r | _ => none))
              immSlotMap p.update (2 + invTys.length))) "NZ" := by
  simp only [forLoopLcmdN, backEdgeFrame, frameNPre, frameNRegion, List.append_assoc,
    List.cons_append, List.nil_append]
  rfl

/-- `forLoopLcmdNCall` emits the same frame around the body walk it selects,
    behind the scratch-byte declaration the body's buffer bindings need. -/
theorem forLoopLcmdNCall_eq_backEdgeFrame (d : Nat) (accReg : String)
    (initOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (p : JLoopBodyN accTy invTys) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) :
    forLoopLcmdNCall d accReg initOp p invOps immSlotMap
      = backEdgeFrame
          (frameAddPre (loopScratchBufBindings p.update (2 + invTys.length))
            ++ frameNPre accReg (loopIdx d) (loopCtr d) initOp p.n) d
          (frameNRegion accReg (loopIdx d) (loopCtr d)
            (invOps.filterMap (fun o => match o with | .reg r => some r | _ => none))
            (frameFeedbackWalk accReg
              (loopBodyWalkNSel d accReg (loopIdx d)
                (invOps.filterMap (fun o => match o with | .reg r => some r | _ => none))
                immSlotMap p.update (2 + invTys.length)))) "NZ" := by
  rw [backEdgeFrame, frameNRegion_frameFeedbackWalk]
  simp only [forLoopLcmdNCall, frameAddPre, frameNPre, loopBodyWalkNSel,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- `forLoopLcmd` emits a bottom-tested back-edge frame. -/
theorem forLoopLcmd_eq_backEdgeFrame (d : Nat) (accReg : String)
    (initOp : LOperand) {accTy : JasminTy} (p : JLoopBody accTy)
    (immSlotMap : ImmSlotMap) :
    forLoopLcmd d accReg initOp p immSlotMap
      = backEdgeFrame (frame1Pre accReg (loopCtr d) initOp p.n) d
          (frame1Region accReg (loopCtr d)
            (loopBodyWalk d accReg immSlotMap p.update 1)) "NZ" := by
  simp only [forLoopLcmd, backEdgeFrame, frame1Pre, frame1Region, List.append_assoc,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil]

/-! ## 6. Branch-free blocks -/

/-- The skeleton holds no conditional. -/
def LcmdCFBranchFree : LcmdCF → Prop
  | .straight _ => True
  | .seq a b => LcmdCFBranchFree a ∧ LcmdCFBranchFree b
  | .loop _ b => LcmdCFBranchFree b
  | .ifPub _ _ _ => False

/-- The structured block holds no conditional. -/
def CFBranchFree {w : Nat} : MachineConstantTime.OwnedCF w → Prop
  | .straight _ => True
  | .seq a b => CFBranchFree a ∧ CFBranchFree b
  | .loop _ b => CFBranchFree b
  | .ifPub _ _ _ => False

/-- Gathering the leaves of a conditional-free skeleton gives a conditional-free
    block. -/
theorem lcmdCFToOwnedCF_branchFree {frame spillW qsaveB : Nat} :
    ∀ (k : LcmdCF) (cf : MachineConstantTime.OwnedCF 64), LcmdCFBranchFree k →
      lcmdCFToOwnedCF frame spillW qsaveB k = some cf → CFBranchFree cf := by
  intro k
  induction k with
  | straight seg =>
    intro cf _ h
    simp only [lcmdCFToOwnedCF, Option.map_eq_some_iff] at h
    obtain ⟨g, -, rfl⟩ := h
    exact trivial
  | seq a b iha ihb =>
    intro cf hbf h
    simp only [lcmdCFToOwnedCF] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨iha x hbf.1 hx, ihb y hbf.2 hy⟩
    · exact absurd h (by simp)
  | loop n b ihb =>
    intro cf hbf h
    simp only [lcmdCFToOwnedCF, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ihb x hbf hx
  | ifPub g t e _ _ => intro cf hbf _; exact absurd hbf (by simp [LcmdCFBranchFree])

/-! ## 7. State-independence of a branch-free index-free block -/

/-- The public-register predicate with no public register. -/
def noPub : PubPred := fun _ => false

/-- Any two states agree on the empty set of public registers. -/
theorem agreePub_noPub {w : Nat} (s₁ s₂ : JState w) : agreePub noPub s₁ s₂ := by
  intro r hr
  simp [noPub] at hr

/-- Public-drivenness against the empty public set is state-blindness: the
    predictor's decision does not read the machine state. -/
theorem pubDriven_noPub_iff {w : Nat} (P : CFPredictor w) :
    PubDriven noPub P ↔ ∀ (s₁ s₂ : JState w) (cf : OwnedCF w), P s₁ cf = P s₂ cf :=
  ⟨fun h s₁ s₂ cf => h s₁ s₂ (agreePub_noPub s₁ s₂) cf, fun h s₁ s₂ _ cf => h s₁ s₂ cf⟩

/-- The predictor that never misses is state-blind. -/
theorem pubDriven_noPub_neverMispredict {w : Nat} :
    PubDriven noPub (SpeculativeCTControlFlow.neverMispredict (w := w)) :=
  SpeculativeCTControlFlow.pubDriven_neverMispredict noPub

/-- An index-free instruction reads no memory index register. -/
theorem idxReg_eq_none_of_isDirect {w : Nat} {i : JInstr w} (h : IsDirect i) :
    MachineConstantTime.idxReg i = none := by
  cases i <;> first | rfl | (simp [IsDirect] at h)

/-- An index-free instruction is CT-addressed against the empty public set. -/
theorem ctAddressed_noPub {w : Nat} {i : JInstr w} (h : IsDirect i) :
    CTAddressed noPub i := by
  refine ⟨fun idx hidx => ?_, fun d _ => rfl⟩
  rw [idxReg_eq_none_of_isDirect h] at hidx
  exact absurd hidx (by simp)

/-- **A branch-free index-free block is CT-controlled against the empty public
    set.** `CFControlled` at a conditional demands a public guard, and with no
    public register that demand is unmeetable, so the branch-free blocks are
    exactly the ones this covers. -/
theorem cfControlled_noPub {w : Nat} :
    ∀ (cf : OwnedCF w), CFAllDirect cf → CFBranchFree cf → CFControlled noPub cf
  | .straight _, hd, _ => fun i hi => ctAddressed_noPub (hd i hi)
  | .seq a b, hd, hbf =>
      ⟨cfControlled_noPub a hd.1 hbf.1, cfControlled_noPub b hd.2 hbf.2⟩
  | .loop _ b, hd, hbf => cfControlled_noPub b hd hbf
  | .ifPub _ _ _, _, hbf => absurd hbf (by simp [CFBranchFree])

/-- **Branch-misprediction leakage of a branch-free index-free block is fixed by
    the program text.** Under a state-blind branch predictor, a block with no
    conditional and with index-free straight-line leaves has the same speculative
    leakage trace from any two machine states, for every speculation window. The
    counted loops it contains run a compile-time number of iterations and their
    exit predictions do not read the state, so neither the architectural nor the
    transient events depend on it.

    The predictor hypothesis is not removable:
    `SpeculativeCTControlFlow.secretDrivenPredictor_leaks` exhibits a predictor
    reading a secret register that separates two states on a block that is both
    `CFControlled` and `CFAllDirect`. -/
theorem cfSpecExec_state_independent {w : Nat} (window : Nat) {P : CFPredictor w}
    (hP : PubDriven noPub P) (cf : OwnedCF w) (hd : CFAllDirect cf)
    (hbf : CFBranchFree cf) (s₁ s₂ : JState w) :
    (cfSpecExec window P s₁ cf).1 = (cfSpecExec window P s₂ cf).1 :=
  SpeculativeCTControlFlow.owned_sct_control_flow noPub window hP cf
    (cfControlled_noPub cf hd hbf) s₁ s₂ (agreePub_noPub s₁ s₂)

/-! ## 8. The recogniser on the emitted frame -/

/-- **A bottom-tested back-edge frame recognises to a branch-free block.** The
    recogniser's parse of the frame is pinned by `parseLcmdCF_backEdgeFrame`, so
    the only way the recogniser can fail on such a frame is a leaf that
    `lowerCov6` does not lower; whatever it returns is conditional-free. -/
theorem lcmdToOwnedCF_backEdgeFrame_branchFree {pre region : Lcmd} {top : LLabel}
    {cc ctr : String} {n : Nat} (hpre : ∀ i ∈ pre, isStraightL i = true)
    (hseed : pre.getLast?.bind counterSeed? = some (ctr, n)) (hn : 0 < n)
    (hregion : ∀ i ∈ region, isStraightL i = true)
    (hok : loopFrameOk ctr region = true) (hcc : isCondCode cc = true)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (backEdgeFrame pre top region cc) = some cf) :
    CFBranchFree cf := by
  rw [lcmdToOwnedCF, List.filter_eq_self.mpr (backEdgeFrame_no_lret hpre hregion),
    parseLcmdCF_backEdgeFrame (backEdgeFrame_length pre region top cc) hpre hseed hn
      hregion hok hcc] at hrec
  rw [Option.bind] at hrec
  refine lcmdCFToOwnedCF_branchFree _ cf ?_ hrec
  exact ⟨trivial, trivial, trivial⟩

/-- **The fixed-trip multi-binder loop export recognises to a branch-free
    block.** -/
theorem forLoopLcmdN_branchFree (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (hn : 0 < p.n)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (forLoopLcmdN d accReg initOp p invOps immSlotMap)
      = some cf) : CFBranchFree cf := by
  rw [forLoopLcmdN_eq_backEdgeFrame] at hrec
  exact lcmdToOwnedCF_backEdgeFrame_branchFree (frameNPre_straight _ _ _ _ _)
    (frameNPre_seed _ _ _ _ _) hn
    (frameNRegion_straight (loopBodyWalkN_straight d accReg (loopIdx d) _ immSlotMap
      p.update _))
    (frameNRegion_loopFrameOk (loopBodyWalkN_straight d accReg (loopIdx d) _
      immSlotMap p.update _)) rfl hrec

/-- **The call-aware fixed-trip multi-binder loop export recognises to a
    branch-free block.** -/
theorem forLoopLcmdNCall_branchFree (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (hn : 0 < p.n)
    (hbody : ∀ i ∈ (loopBodyWalkNSel d accReg (loopIdx d)
      (invOps.filterMap (fun o => match o with | .reg r => some r | _ => none))
      immSlotMap p.update (2 + invTys.length)).1, isStraightL i = true)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (forLoopLcmdNCall d accReg initOp p invOps immSlotMap)
      = some cf) : CFBranchFree cf := by
  rw [forLoopLcmdNCall_eq_backEdgeFrame] at hrec
  exact lcmdToOwnedCF_backEdgeFrame_branchFree
    (frameAddPre_frameNPre_straight _ _ _ _ _ _)
    (frameAddPre_frameNPre_seed _ _ _ _ _ _) hn
    (frameNRegion_straight (frameFeedbackWalk_straight accReg hbody))
    (frameNRegion_loopFrameOk (frameFeedbackWalk_straight accReg hbody)) rfl hrec

/-- **The fixed-trip single-binder loop export recognises to a branch-free
    block.** -/
theorem forLoopLcmd_branchFree (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} (p : JLoopBody accTy) (immSlotMap : ImmSlotMap)
    (hn : 0 < p.n) {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (forLoopLcmd d accReg initOp p immSlotMap) = some cf) :
    CFBranchFree cf := by
  rw [forLoopLcmd_eq_backEdgeFrame] at hrec
  exact lcmdToOwnedCF_backEdgeFrame_branchFree (frame1Pre_straight _ _ _ _)
    (frame1Pre_seed _ _ _ _) hn
    (frame1Region_straight (loopBodyWalk_straight d accReg immSlotMap p.update 1))
    (frame1Region_loopFrameOk (loopBodyWalk_straight d accReg immSlotMap p.update 1))
    rfl hrec

/-! ## 9. The rolled loop over a front-compiled body -/

/-- The rolled multi-binder loop over a front-compiled body recognises to an
    index-free block. -/
theorem compileFromHax_forLoopLcmdN_cfAllDirect {k : Nat} {params : List String}
    {e : ImpExpr} {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    (N d : Nat) (accReg : String) (initOp : LOperand) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) (hinit : isIndexed initOp = false) {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (forLoopLcmdN d accReg initOp
      (accTy := rW 64) (invTys := List.replicate k (rW 64)) ⟨N, update⟩ invOps
      immSlotMap) = some cf) :
    CFAllDirect cf :=
  lcmdToOwnedCF_cfAllDirect
    (LoopExporterCTBridge.compileFromHax_forLoopLcmdN_lcmdDirect hc N d accReg initOp
      invOps immSlotMap hinit) hrec

/-- **The branch-misprediction (Spectre-v1) leakage-equality statement for a
    rolled front-compiled loop.** The recognised block of the fixed-trip
    multi-binder loop export over a `compileFromHax` body has the same speculative
    leakage trace from any two machine states, under a state-blind branch
    predictor and for every speculation window.

    The predictor hypothesis is `PubDriven noPub P`, which
    `pubDriven_noPub_iff` reads as: the predictor's decision does not depend on
    the machine state. `SpeculativeCTControlFlow.secretDrivenPredictor_leaks`
    shows it is not removable. -/
theorem compileFromHax_rolledLoop_cfSpec_state_independent {k : Nat}
    {params : List String} {e : ImpExpr}
    {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    {N : Nat} (hN : 0 < N) (d : Nat) (accReg : String) (initOp : LOperand)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hinit : isIndexed initOp = false) {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (forLoopLcmdN d accReg initOp
      (accTy := rW 64) (invTys := List.replicate k (rW 64)) ⟨N, update⟩ invOps
      immSlotMap) = some cf)
    (window : Nat) {P : CFPredictor 64} (hP : PubDriven noPub P)
    (s₁ s₂ : JState 64) :
    (cfSpecExec window P s₁ cf).1 = (cfSpecExec window P s₂ cf).1 :=
  cfSpecExec_state_independent window hP cf
    (compileFromHax_forLoopLcmdN_cfAllDirect hc N d accReg initOp invOps immSlotMap
      hinit hrec)
    (forLoopLcmdN_branchFree d accReg initOp ⟨N, update⟩ invOps immSlotMap hN hrec)
    s₁ s₂

/-- **The predictor-free (Spectre-v1) containment statement for a rolled
    front-compiled loop.** Every memory event of the speculative trace of the
    recognised block — transient events across the back-edge included — names an
    address that occurs in the block's program text, for every branch predictor,
    every window and every state. -/
theorem compileFromHax_rolledLoop_cfSpec_mem_addr_in_program {k : Nat}
    {params : List String} {e : ImpExpr}
    {update : Com jasminDialect (frontCtxt 64 (k + 2) []) (rW 64)}
    (hc : compileFromHax (w := 64) (nIn := k + 2) params e = some update)
    (N d : Nat) (accReg : String) (initOp : LOperand) (invOps : List LOperand)
    (immSlotMap : ImmSlotMap) (hinit : isIndexed initOp = false) {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (forLoopLcmdN d accReg initOp
      (accTy := rW 64) (invTys := List.replicate k (rW 64)) ⟨N, update⟩ invOps
      immSlotMap) = some cf)
    (window : Nat) (P : CFPredictor 64) (s : JState 64) (base : String) (off : Int)
    (hmem : SLeak.arch (MLeak.mem base off) ∈ (cfSpecExec window P s cf).1) :
    MLeak.mem base off ∈ cfAddrs cf :=
  SpeculativeCTControlFlow.cfSpecExec_mem_addr_in_program window P cf
    (compileFromHax_forLoopLcmdN_cfAllDirect hc N d accReg initOp invOps immSlotMap
      hinit hrec) s base off hmem

/-! ## 10. The recogniser on exporter output

`JasminLprogExport.dblLoopBody` is the doubling body of the deployed counted-loop
smoke program `loopSmokeProg`, and `forLoopLcmd` is the exporter `comLToBody`
calls on it. -/

-- The trip count is a positive compile-time literal.
#guard 0 < dblLoopBody.n

-- The single-binder loop export of that body recognises, leaves and all, so the
-- hypothesis `lcmdToOwnedCF … = some cf` of the results above is satisfiable on
-- exporter output.
#guard (lcmdToOwnedCF (forLoopLcmd 1 "Lacc1" (.reg (argName 0)) dblLoopBody
  (fun _ => none))).isSome

-- No operand of that export is register-indexed, so `lcmdToOwnedCF_cfAllDirect`
-- applies to it.
#guard lcmdDirect (forLoopLcmd 1 "Lacc1" (.reg (argName 0)) dblLoopBody
  (fun _ => none))

/-- A two-input front source: the wrapping sum of the accumulator and the loop
    index. -/
def demoLoopSrc : ImpExpr :=
  .letBind "t" (.app "wrapping_add" [.var "acc", .var "i"]) (.var "t")

-- The compile-from-hax front compiles `demoLoopSrc`, and the fixed-trip
-- multi-binder loop export of the compiled body recognises.
#guard ((compileFromHax (w := 64) (nIn := 2) ["acc", "i"] demoLoopSrc).map
    (fun u => (lcmdToOwnedCF (forLoopLcmdN 0 "Lacc0" (.imm 0)
      (accTy := rW 64) (invTys := []) ⟨4, u⟩ [] (fun _ => none))).isSome))
  = some true

/-! ## 11. The call/return layer -/

/-- The `OwnedCF` recogniser with the frame size, spill width and qsave block
    supplied, so that every segment of one body gathers against that body's
    frame layout. -/
def lcmdToOwnedCFAt (frame spillW qsaveB : Nat) (body : Lcmd) : Option (OwnedCF 64) :=
  (parseLcmdCF (body.length + 1) (body.filter (fun i => !isLret i))).bind
    (fun k => lcmdCFToOwnedCF frame spillW qsaveB k)

theorem lcmdToOwnedCF_eq_at (body : Lcmd) :
    lcmdToOwnedCF body
      = lcmdToOwnedCFAt (LprogAsmPrinter.frameSize body)
          (if LprogAsmPrinter.bodyIsU64 body then 64 else 32)
          (LprogAsmPrinter.qsaveBytesFor body) body := rfl

theorem lcmdToOwnedCFAt_cfAllDirect {frame spillW qsaveB : Nat} {body : Lcmd}
    {cf : OwnedCF 64} (hd : lcmdDirect body = true)
    (h : lcmdToOwnedCFAt frame spillW qsaveB body = some cf) : CFAllDirect cf := by
  simp only [lcmdToOwnedCFAt, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, hcf⟩ := h
  refine lcmdCFToOwnedCF_cfAllDirect k cf ?_ hcf
  refine parseLcmdCF_direct _ _ k ?_ hk
  intro i hi
  exact (lcmdDirect_iff body).mp hd i (List.mem_of_mem_filter hi)

theorem lcmdToOwnedCFAt_branchFree {frame spillW qsaveB : Nat} {body : Lcmd}
    {k : LcmdCF}
    {cf : OwnedCF 64} (hk : parseLcmdCF (body.length + 1)
      (body.filter (fun i => !isLret i)) = some k) (hbf : LcmdCFBranchFree k)
    (h : lcmdToOwnedCFAt frame spillW qsaveB body = some cf) : CFBranchFree cf := by
  rw [lcmdToOwnedCFAt, hk, Option.bind] at h
  exact lcmdCFToOwnedCF_branchFree k cf hbf h

theorem lcmdDirect_sublist {c d : Lcmd} (hs : d.Sublist c)
    (hd : lcmdDirect c = true) : lcmdDirect d = true :=
  lcmdDirect_of_mem (direct_sublist hs ((lcmdDirect_iff c).mp hd))

/-- A call instruction. -/
def isLcall : Linstr → Bool
  | ⟨_, .Lcall _ _⟩ => true
  | _ => false

/-- The callee symbol of a call instruction. -/
def callSym? (i : Linstr) : Option String :=
  match i.li_i with
  | .Lcall _ (sym, _) => some sym
  | _ => none

/-- Parse an `Lcmd` into a `CallCF`: each maximal call-free run recognises as an
    owned control-flow block, and each `Lcall` becomes a call node whose callee is
    the block `resolve` supplies for the symbol and whose continuation is the
    recognised remainder. `none` when a run does not recognise or the symbol does
    not resolve. -/
def parseLcmdCall (frame spillW qsaveB : Nat) (resolve : String → Option (CallCF 64)) :
    Nat → Lcmd → Option (CallCF 64)
  | 0, _ => none
  | fuel + 1, c =>
      match c.dropWhile (fun i => !isLcall i) with
      | [] => (lcmdToOwnedCFAt frame spillW qsaveB c).map CallCF.leaf
      | i :: rest =>
          match callSym? i with
          | none => none
          | some sym =>
              match lcmdToOwnedCFAt frame spillW qsaveB
                  (c.takeWhile (fun j => !isLcall j)) with
              | none => none
              | some pre =>
                  match resolve sym with
                  | none => none
                  | some callee =>
                      (parseLcmdCall frame spillW qsaveB resolve fuel rest).map
                        (fun cont => .seq (.leaf pre) (.call callee cont))

/-- **The call-aware recogniser.** Parse an emitted `Lcmd` into the structured
    call/return block it is, gathering each call-free run against the body's own
    frame size and spill width. -/
def lcmdToCallCF (resolve : String → Option (CallCF 64)) (body : Lcmd) :
    Option (CallCF 64) :=
  parseLcmdCall (LprogAsmPrinter.frameSize body)
    (if LprogAsmPrinter.bodyIsU64 body then 64 else 32)
    (LprogAsmPrinter.qsaveBytesFor body) resolve (body.length + 1) body

/-- **The addressing class crosses the call-aware recogniser.** When no operand
    of the emitted command is register-indexed and every resolved callee is
    index-free, the call/return block the recogniser returns is index-free
    throughout — the hypothesis of `SpeculativeCTReturn.callSpecExec_arch_mem`. -/
theorem parseLcmdCall_callAllDirect {frame spillW qsaveB : Nat}
    {resolve : String → Option (CallCF 64)}
    (hres : ∀ (sym : String) (cc : CallCF 64), resolve sym = some cc →
      CallAllDirect cc) :
    ∀ (fuel : Nat) (c : Lcmd) (cc : CallCF 64), lcmdDirect c = true →
      parseLcmdCall frame spillW qsaveB resolve fuel c = some cc → CallAllDirect cc := by
  intro fuel
  induction fuel with
  | zero => intro c cc _ h; exact absurd h (by simp [parseLcmdCall])
  | succ f ih =>
    intro c cc hd h
    rw [parseLcmdCall] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact lcmdToOwnedCFAt_cfAllDirect hd hx
    · rename_i i rest hsplit
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i pre hpre
          split at h
          · exact absurd h (by simp)
          · rename_i callee hcallee
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨cont, hcont, rfl⟩ := h
            refine ⟨lcmdToOwnedCFAt_cfAllDirect
              (lcmdDirect_sublist (List.takeWhile_sublist _) hd) hpre,
              hres _ callee hcallee, ?_⟩
            refine ih rest cont ?_ hcont
            refine lcmdDirect_of_mem (fun z hz => ?_)
            exact (lcmdDirect_iff c).mp hd z
              (mem_of_mem_tail_dropWhile hsplit hz)

theorem lcmdToCallCF_callAllDirect {resolve : String → Option (CallCF 64)}
    (hres : ∀ (sym : String) (cc : CallCF 64), resolve sym = some cc →
      CallAllDirect cc) {body : Lcmd} {cc : CallCF 64} (hd : lcmdDirect body = true)
    (h : lcmdToCallCF resolve body = some cc) : CallAllDirect cc :=
  parseLcmdCall_callAllDirect hres _ body cc hd h

/-- Every owned leaf of the block holds no conditional. -/
def CallBranchFree {w : Nat} : CallCF w → Prop
  | .leaf cf => CFBranchFree cf
  | .seq a b => CallBranchFree a ∧ CallBranchFree b
  | .call callee cont => CallBranchFree callee ∧ CallBranchFree cont

/-- A branch-free index-free call/return block is CT-controlled against the empty
    public set. -/
theorem callControlled_noPub {w : Nat} :
    ∀ (cc : CallCF w), CallAllDirect cc → CallBranchFree cc → CallControlled noPub cc
  | .leaf cf, hd, hbf => cfControlled_noPub cf hd hbf
  | .seq a b, hd, hbf =>
      ⟨callControlled_noPub a hd.1 hbf.1, callControlled_noPub b hd.2 hbf.2⟩
  | .call callee cont, hd, hbf =>
      ⟨callControlled_noPub callee hd.1 hbf.1, callControlled_noPub cont hd.2 hbf.2⟩

/-- **Return-misprediction leakage of a branch-free index-free call/return block
    is fixed by the program text.** Under a state-blind return-target predictor,
    and with every pending return target branch-free and index-free, the block has
    the same speculative leakage trace from any two machine states, for every
    speculation window.

    The predictor hypothesis is not removable:
    `SpeculativeCTReturn.secretDrivenRetPredictor_leaks` exhibits a predictor
    reading a secret register that separates two states on a block that is both
    `CallControlled` and `CallAllDirect`. -/
theorem callSpecExec_state_independent {w : Nat} (window : Nat)
    {P : RSBPredictor w} (hP : RSBPubDriven noPub P) (cc : CallCF w)
    (hd : CallAllDirect cc) (hbf : CallBranchFree cc) (rsb : RSB w)
    (hrsbd : ∀ c ∈ rsb, CallAllDirect c) (hrsbf : ∀ c ∈ rsb, CallBranchFree c)
    (s₁ s₂ : JState w) :
    (callSpecExec window P s₁ rsb cc).1 = (callSpecExec window P s₂ rsb cc).1 :=
  SpeculativeCTReturn.owned_sct_return noPub window hP cc
    (callControlled_noPub cc hd hbf) rsb
    (fun c hc => callControlled_noPub c (hrsbd c hc) (hrsbf c hc)) s₁ s₂
    (agreePub_noPub s₁ s₂)

/-- **A speculative memory event of a recognised call/return block names a
    program-text address.** On an emitted command with no register-indexed operand
    and with index-free resolved callees, every memory access the speculative trace
    records — transient events on a mispredicted return included — is an access the
    block's own program text or a pending return target's contains, for every
    predictor, window, buffer and state. -/
theorem lcmdToCallCF_spec_mem {resolve : String → Option (CallCF 64)}
    (hres : ∀ (sym : String) (c : CallCF 64), resolve sym = some c → CallAllDirect c)
    {body : Lcmd} {cc : CallCF 64} (hd : lcmdDirect body = true)
    (h : lcmdToCallCF resolve body = some cc) (window : Nat) (P : RSBPredictor 64)
    (s : JState 64) (rsb : RSB 64) (hrsb : ∀ c ∈ rsb, CallAllDirect c)
    (e : MLeak) (he : SLeak.arch e ∈ (callSpecExec window P s rsb cc).1) :
    e ∈ callAddrs cc ++ rsb.flatMap callAddrs :=
  SpeculativeCTReturn.callSpecExec_arch_mem window P
    (callAddrs cc ++ rsb.flatMap callAddrs) cc (lcmdToCallCF_callAllDirect hres hd h)
    (fun _ he' => List.mem_append_left _ he') s rsb hrsb
    (fun c hc _ he' =>
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, he'⟩)) e he

/-! ## 12. The call-aware recogniser on front output

`QuerySampleBranchFront.sampleBitsBodyFront` is the front-generated body of the
FRI query-index mask `p3_fs_sample_bits`: a leaf call followed by the word mask.
It carries a top-level `LinstrR.Lcall`, which `GatherImmForms.gatherJBlock6`
rejects. -/

-- The call-aware recogniser accepts it, against a callee map that resolves the
-- sampled symbol to an empty leaf.
#guard (lcmdToCallCF (fun _ => some (.leaf (.straight [])))
  (QuerySampleBranchFront.sampleBitsBodyFront
    QuerySampleBranchFront.demoCfg)).isSome

-- No operand of that body is register-indexed, so `lcmdToCallCF_callAllDirect`
-- applies to it.
#guard lcmdDirect (QuerySampleBranchFront.sampleBitsBodyFront
  QuerySampleBranchFront.demoCfg)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CFGatherBridge
