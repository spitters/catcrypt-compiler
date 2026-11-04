/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkW
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop

/-!
# The wide calling route: carry chains, casts and cell stores between the calls of a body

The image relation across a call (`ImageAddrCall`) is stated at the relation
`ImageAddrSim.ImgRel` and the correspondence `DecodePrintedAddr.ACorr`. This module states the
class and the gate of a calling body, the wide route: between two calls the
simulation runs at `ImageAddrSimW.ImgRelW` and `DecodePrintedAddrW.ACorrW`, over the class
`DecodePrintedAddrW.instrOKWB` of carry chains, casts and one-bit names, with an indexed store
through a cell (`ImageAddrCidx`) as an arm of the gate. A segment starts at the narrow relation and
ends at the wide one; the width analysis `oneBitAt` is dead at each call and at the closing return
(`bitsDeadB`), so that the end state converts to the relaxed relation `ImageAddrCall.ImgRelF` at the
dead names, on the address state with its narrow names widened (`DecodePrintedAddrW.widenS`). The
statement `ImageAddrCall.SegSim` and everything above it (`haltsO_of_runChainS`, the site steps, the
per-symbol chains) apply unchanged.

## Main definitions

* `printedAddrCWB`, `imgGateCBW`: the printed class and the image gate of a calling body; the
  arm of its gate at an indexed store through a cell is `ImageAddrCidx.cidxArmCW`.
* `bitsDeadB`: the width analysis is dead at each call and at the return.
* `liveW`: the positions at which no segment of the wide simulation starts.
* `ByteSegW`: the byte simulation of the segments at `ACorrW`.
* `SegStW`, `SegExactW`: the invariant of a run in a segment, and the simulation of a segment from
  the narrow relation to the wide one.

## Main results

* `printedAddrCWB_reloc`, `printedAddrCWB_remote`, `printedAddrCWB_frameAbove`,
  `callFacts_of_printedAddrCWB`: the facts of the class.
* `instrOKWB_of_instrOKB`: the narrow instruction class `DecodePrintedCFG.instrOKB` is
  contained in the wide one.
* `liveW_zero`, `liveW_succ_call`: the positions where a segment of the wide simulation starts.
* `imgRelF_of_imgRelW`: the conversion from the wide relation to the relaxed one.
* `byteSegW_of_linked`: the byte simulation on a linked decoded program.
* `steps_callImgW`, `segExactW_callImg`, `segSim_of_segExactW`: the run of a segment, its
  simulation and `SegSim` from it.
* `haltsO_of_deadChecksS`, `haltsO_of_linkedChecksS`, `haltsC_of_linkedChecksS`,
  `haltsO_of_linkedChecksOne`, `haltsC_of_linkedChecksOne`: the runs under an oracle and through
  calls of the program of the linked bytes, from Boolean checks.
* `printedAddrCWB_eq_impl`, `imgGateCBW_eq_impl`, `bitsDeadB_eq_impl` (`@[csimp]`): the class and
  the checks are evaluated in one pass, with the width analysis tabulated (`oneBitTab`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW

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

/-! ## 1. The class and the gate -/

/-- **The printed bodies of the wide calling route**: the frame conditions of the relocating
    encoder; the closing return; every other instruction a call of a named symbol or in the
    class `instrOKWB` with carry chains; every conditional branch directly after a compare,
    every carry-out binding directly after its add, every cast keeping the low bits its
    widths give; and, for a body with a call, the frame check `frameNonnegB` at `G` bytes below
    the return word. -/
def printedAddrCWB (G : Nat) (body : Lcmd) : Bool :=
  relocFrameB body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i =>
      remoteCallB i.li_i || instrOKWB body (Params.ofBody body) i.li_i)
    && (List.range body.length).all (fun k =>
      condPrevB body k && carryPrevB body k && castPosB body k)
    && (callFreeB body || frameNonnegB body G)

/-- **The gate of the wide image simulation of a calling body**: every instruction but the
    last is a call of a named symbol or passes the gate `ImageAddrCidx.gateCW` (an indexed
    store through a cell passing `cidxArmCW`, or `instrGateBW`); the last is the return; every
    array-pointer reload follows a save. -/
def imgGateCBW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k => (body[k]?).all fun i =>
      remoteCallB i.li_i || gateCW frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- **The gate of a calling body without the join of forward branches**: `imgGateCBW` with the
    analysis `oneBitAtB` in place of `oneBitAt`, and `instrGateBWB` in place of
    `instrGateBW`. -/
def imgGateCBWB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k => (body[k]?).all fun i =>
      remoteCallB i.li_i
        || (cidxArmAt frame slotArr body k (oneBitAtB frame body (k - 3))
              (oneBitAtB frame body k) i.li_i
            && srcNoCellB i.li_i)
        || instrGateBWB frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- **No calling body the gate accepted without the join of forward branches is refused**: a
    body passing `imgGateCBWB` passes `imgGateCBW`, and its width analysis is `oneBitAtB` at
    every position, so that `bitsDeadB` keeps its value. -/
theorem imgGateCBW_of_back {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateCBWB frame slotArr body = true) :
    imgGateCBW frame slotArr body = true
      ∧ ∀ k, oneBitAt frame body k = oneBitAtB frame body k := by
  simp only [imgGateCBWB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hall, hlast⟩, hrs⟩ := h
  have he : ∀ k, oneBitAt frame body k = oneBitAtB frame body k :=
    oneBitAt_eq_oneBitAtB (fwdIncl_of_instrGateBWB hlast fun q bi c l hlt hq hc => by
      have := hall q hlt
      rw [hq, Option.all_some, hc] at this
      simpa [remoteCallB, srcNoCellB] using this)
  refine ⟨?_, he⟩
  simp only [imgGateCBW, gateCW, ← Bool.or_assoc, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨fun k hk => ?_, hlast⟩, hrs⟩
  have := hall k hk
  cases hb : body[k]? with
  | none => rfl
  | some i =>
      rw [hb, Option.all_some] at this
      rw [Option.all_some, ← instrGateBWB_eq he]
      simp only [cidxArmCW, cidxArmB, he]
      exact this

/-- **The width analysis is dead at each call and at the return**: at the last position and at
    each call position, every name of `oneBitAt` is a dead name of `D`. -/
def bitsDeadB (frame : String → Option (BitVec 64)) (D : DeadTab) (body : Lcmd) : Bool :=
  ((body.length - 1) :: callPos body).all fun p =>
    (oneBitAt frame body p).all (D.dead p).contains

/-- The instruction is a carry-out binding `ADCXHI:64 O, A, S, C`. -/
def carryHiB : LinstrR → Bool
  | .Lopn [.reg _] o [.reg _, .reg _, .reg _] => o == "ADCXHI:64"
  | _ => false

/-- **The positions at which no segment of the wide simulation starts**: a flag of `D` is live
    there, or the instruction there is a carry-out binding, or the position is one of the
    three positions `k' - 2`, `k' - 1`, `k'` of an indexed store through a cell at `k'`, or the
    cast width analysis has an entry there. -/
def liveW (D : DeadTab) (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    Bool :=
  D.live k || (body[k]?).any (fun i => carryHiB i.li_i)
    || (List.range 3).any (fun j => (body[k + j]?).any fun i =>
      (cellIdxStore? slotArr body (k + j) i.li_i).isSome)
    || !(narrowIn body k).isEmpty

/-! ## 2. The facts of the class -/

/-- **The frame facts of the class for the relocating encoder**: no register is saved by
    `push`, and the frame is non-zero and below `2 ^ 31`. -/
theorem printedAddrCWB_reloc {G : Nat} {body : Lcmd} (h : printedAddrCWB G body = true) :
    calleeSavedToSave body = [] ∧ frameSize body ≠ 0 ∧ frameSize body < 2 ^ 31 := by
  simp only [printedAddrCWB, relocFrameB, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2⟩

/-- **A remote transfer of a body of the class is a call.** -/
theorem printedAddrCWB_remote {G : Nat} {body : Lcmd} (h : printedAddrCWB G body = true)
    {i : Linstr} (hi : i ∈ body) {f : String} (hf : remoteSym i.li_i = some f) :
    ∃ ra l, i.li_i = .Lcall ra (f, l) := by
  simp only [printedAddrCWB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hlast⟩, hall⟩, -⟩, -⟩ := h
  rcases List.eq_nil_or_concat body with rfl | ⟨L, b, rfl⟩
  · cases hi
  · simp only [List.concat_eq_append, List.dropLast_concat, List.getLast?_concat,
      Option.any_some, List.all_eq_true] at hlast hall
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have := hall i hi
      cases hc : i.li_i with
      | Lcall ra tg =>
        obtain ⟨f', l⟩ := tg
        rw [hc] at hf
        simp only [remoteSym] at hf
        split at hf
        · cases hf
        · cases hf
          exact ⟨ra, l, rfl⟩
      | _ => simp_all [remoteSym, remoteCallB, instrOKWB]
    · cases hc : i.li_i <;> simp_all [remoteSym, isRetB]

/-- **The shape condition of the relocating encoder from the class.** An instruction of a
    body of the class meets `RelocShapeOK` at a shape `sh` when, being no remote transfer,
    it has the shape `sh`. -/
theorem relocShapeOK_of_printedAddrCWB {G : Nat} {body : Lcmd}
    (h : printedAddrCWB G body = true) {i : Linstr} (hi : i ∈ body) (P : Params) (sh : Shape)
    (hsh : remoteSym i.li_i = none → ShapeOK P i.li_i sh) : RelocShapeOK P i.li_i sh := by
  unfold RelocShapeOK
  cases hr : remoteSym i.li_i with
  | none => exact hsh hr
  | some f => exact printedAddrCWB_remote h hi hr

/-- **The frame of a body of the class with a call lies above the stack register.** -/
theorem printedAddrCWB_frameAbove {G : Nat} {body : Lcmd} (h : printedAddrCWB G body = true)
    (hcall : callFreeB body = false) (sa0 : AState) :
    FrameAbove (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      (frameRsp body sa0) G := by
  simp only [printedAddrCWB, Bool.and_eq_true, hcall, Bool.false_or] at h
  exact frameAbove_of_frameNonnegB h.2 sa0

/-- **The facts of a body of the class** whose shapes are `ds`. -/
theorem callFacts_of_printedAddrCWB {G : Nat} {body : Lcmd} {ds : List PhysAbiShape.DShape}
    (h : printedAddrCWB G body = true)
    (hs : DecodeGen.shapesOf (Params.ofBody body) body = some ds) : CallFactsW body ds := by
  simp only [printedAddrCWB, Bool.and_eq_true, Option.any_eq_true, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨-, r, hlast, hret⟩, hall⟩, hpos⟩, -⟩ := h
  have hlen : 0 < body.length := by
    cases body with
    | nil => simp at hlast
    | cons _ _ => simp
  refine ⟨hs, hlen, ?_, fun k hk => ?_, fun k hk => (hpos k hk).1.1, fun k hk => (hpos k hk).1.2,
    fun k hk => (hpos k hk).2⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    obtain rfl := Option.some.inj hlast
    revert hret
    unfold isRetB
    split <;> simp_all
  · have := hall (body[k]'(by omega)) (by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩)
    simp only [Bool.or_eq_true] at this
    exact this.imp remoteSym_of_remoteCallB id

/-! ## 2a. The class, the gate and the image at a body without a call -/

/-- At a body without a call no instruction is a call of a named symbol. -/
theorem remoteCallB_of_callFree {body : Lcmd} (h : callFreeB body = true) {i : Linstr}
    (hi : i ∈ body) : remoteCallB i.li_i = false := by
  have := List.all_eq_true.mp h i hi
  revert this
  cases i.li_i <;> simp [isCallB, remoteCallB]

/-- **At a body without a call the gate of a calling body is `ImageAddrCidx.imgGateCW`.** -/
theorem imgGateCBW_of_callFree {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} (h : callFreeB body = true) :
    imgGateCBW frame slotArr body = imgGateCW frame slotArr body := by
  have hk : ∀ k, (body[k]?).all (fun i => remoteCallB i.li_i || gateCW frame slotArr body k i.li_i)
      = (body[k]?).all (fun i => gateCW frame slotArr body k i.li_i) := by
    intro k
    cases hb : body[k]? with
    | none => rfl
    | some i => simp [remoteCallB_of_callFree h (List.mem_of_getElem? hb)]
  simp only [imgGateCBW, imgGateCW, hk]

/-- **A body of the wide class without a call is in the wide calling class**: the decodable
    class `decodableLcmd` gives the frame conditions of the relocating encoder (`relocFrameB`),
    and a body without a call needs no frame check below the return word. -/
theorem printedAddrCWB_of_printedAddrWB (G : Nat) {body : Lcmd}
    (h : DecodePrintedAddrW.printedAddrWB body = true) (hcf : callFreeB body = true) :
    printedAddrCWB G body = true := by
  simp only [DecodePrintedAddrW.printedAddrWB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hd, hl⟩, ho⟩, hc⟩, hy⟩, hp⟩ := h
  have hr : relocFrameB body = true := by
    simp only [DecodeLayout.decodableLcmd, Bool.and_eq_true] at hd
    obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, -⟩, -⟩ := hd
    simp only [relocFrameB, h1, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h2, ?_⟩
    have h3' : Int.ofNat (Params.ofBody body).frame < 2 ^ 31 := by
      simp only [SailX86Decoder.dispOk32, decide_eq_true_eq] at h3
      exact h3.2
    have : (Params.ofBody body).frame = frameSize body := rfl
    rw [this, Int.ofNat_eq_natCast] at h3'
    omega
  simp only [printedAddrCWB, hr, hl, hcf, Bool.true_and, Bool.true_or, Bool.and_true,
    Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · simp [List.all_eq_true.mp ho i hi]
  · simp [List.all_eq_true.mp hc k hk, List.all_eq_true.mp hy k hk, List.all_eq_true.mp hp k hk]

/-- **At a body without a call the image of a calling body is the image `virtImg`.** -/
theorem callImg_of_callFree (slotArr : String → Option (String × Nat))
    (site : Nat → String × List String) {body : Lcmd} (h : callFreeB body = true) :
    callImg slotArr site body = virtImg slotArr body := by
  unfold callImg
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [List.getElem_mapIdx]
  split
  · rename_i heq
    have := List.all_eq_true.mp h _ (List.mem_of_getElem? heq)
    simp [isCallB] at this
  · rfl

/-! ## 3. The facts of the gate -/

/-- The positions of a body exempt from `instrGateBW` under `imgGateCBW`: a call of a named symbol
    and an indexed store through a cell passing `cidxArmCW`. -/
def exemptCW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) : Prop :=
  (body[k]?).any (fun i => remoteCallB i.li_i || cidxArmCW frame slotArr body k i.li_i) = true

/-- A body that passes `imgGateCBW` passes the positionwise gate at the exempt positions
    `exemptCW`. -/
theorem imgGateW_of_imgGateCBW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateCBW frame slotArr body = true) :
    ImgGateW frame slotArr body (exemptCW frame slotArr body) := by
  simp only [imgGateCBW, gateCW, ← Bool.or_assoc, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k i hi hk hX => ?_, ?_, h3⟩
  · have := h1 k (by omega)
    rw [hi] at this
    simp only [Option.all_some, Bool.or_eq_true] at this
    simp only [exemptCW, hi, Option.any_some, Bool.or_eq_true] at hX
    rcases this with h | h
    · exact absurd h hX
    · exact h
  · cases hl : body.getLast? with
    | none => rw [hl] at h2; cases h2
    | some r =>
        rw [hl] at h2
        simp only [Option.any_some] at h2
        refine ⟨r, rfl, ?_⟩
        revert h2
        cases r.li_i <;> simp [isRetB]

/-- **A call of a body that passes `imgGateCBW` is not at its last position.** -/
theorem lt_of_call_imgGateCBW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hgate : imgGateCBW frame slotArr body = true) :
    ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length := by
  intro p bi ra t hb hbi
  have hk : p < body.length := (List.getElem?_eq_some_iff.mp hb).1
  by_contra hcn
  have he : p = body.length - 1 := by omega
  obtain ⟨r, hr, hret⟩ := (imgGateW_of_imgGateCBW hgate).last
  rw [List.getLast?_eq_getElem?, ← he, hb] at hr
  cases hr
  rw [hbi] at hret
  cases hret

/-- `bitsDeadB` at a call position. -/
theorem bitsDeadB_call {frame : String → Option (BitVec 64)} {D : DeadTab} {body : Lcmd}
    (h : bitsDeadB frame D body = true) {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    {ra : Option String} {t : String × LLabel} (hbi : bi.li_i = .Lcall ra t) :
    ∀ r ∈ oneBitAt frame body p, r ∈ D.dead p := by
  simp only [bitsDeadB, List.all_cons, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at h
  by_cases hp : p = body.length - 1
  · subst hp
    exact h.1
  · have hl := (List.getElem?_eq_some_iff.mp hb).1
    exact h.2 p (mem_callPos.mpr ⟨by omega, by rw [hb]; simp [hbi, isCallB]⟩)

/-- `bitsDeadB` at the last position. -/
theorem bitsDeadB_last {frame : String → Option (BitVec 64)} {D : DeadTab} {body : Lcmd}
    (h : bitsDeadB frame D body = true) :
    ∀ r ∈ oneBitAt frame body (body.length - 1), r ∈ D.dead (body.length - 1) := by
  simp only [bitsDeadB, List.all_cons, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at h
  exact h.1

/-- What a position with `liveW` false gives: no flag of `D` is live, no carry-out binding stands
    there, no store of a window stands at it or at the next two positions, and the cast width
    analysis has no entry there. -/
theorem liveW_false_spec {D : DeadTab} {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {k : Nat} (h : liveW D slotArr body k = false) :
    D.live k = false ∧ (body[k]?).any (fun i => carryHiB i.li_i) = false
      ∧ (∀ j, j < 3 → ∀ i, body[k + j]? = some i →
          cellIdxStore? slotArr body (k + j) i.li_i = none)
      ∧ narrowIn body k = [] := by
  simp only [liveW, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, List.any_eq_false,
    List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun j hj i hi => ?_, h4⟩
  have := h3 j hj
  rw [hi] at this
  simpa using this

/-- The carry requirement at a position that holds no carry-out binding. -/
theorem carryReq_of_not_carryHi {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    (h : (body[k]?).any (fun i => carryHiB i.li_i) = false) (sA : AState) (sa : LstateA) :
    CarryReq frame body k sA sa := by
  intro ii O A S C hb
  rw [hb] at h
  simp [carryHiB] at h

/-- The cast width analysis invariant at a position where the analysis has no entry. -/
theorem narrowInv_of_nil {body : Lcmd} {sa : LstateA} (h : narrowIn body sa.reg.lpc = []) :
    NarrowInv body sa := by
  intro i _ _ r w hl
  rw [h] at hl
  simp at hl

/-- A position holds no carry-out binding when it is the first one or the instruction before it
    has not the operand shape of an add. -/
theorem carryHiB_false {body : Lcmd} {k : Nat} {i : Linstr} (hb : body[k]? = some i)
    (hk : carryPrevB body k = true)
    (hprev : k = 0 ∨ ∃ j, body[k - 1]? = some j ∧
      ∀ d o a s c, j.li_i ≠ .Lopn [.reg d] o [.reg a, .reg s, .reg c]) :
    carryHiB i.li_i = false := by
  obtain ⟨ii, x⟩ := i
  simp only
  unfold carryHiB
  split
  · rename_i d o a s c
    rw [beq_eq_false_iff_ne]
    rintro rfl
    unfold carryPrevB at hk
    rw [hb] at hk
    simp only [ite_true] at hk
    rcases hprev with rfl | ⟨⟨ii', li⟩, hj, hne⟩
    · simp at hk
    · rw [hj] at hk
      simp only at hne
      grind
  · rfl

/-- **One past a call `liveW` is false**, when no flag is live there: the instruction before a
    carry-out binding is an add, and the three instructions before a store are no calls. -/
theorem liveW_succ_call {D : DeadTab} {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hflags : callFlagsB D body = true) (hcarry : ∀ k, k < body.length → carryPrevB body k = true)
    {p : Nat} {bi : Linstr} (hb : body[p]? = some bi) {ra : Option String}
    {t : String × LLabel} (hbi : bi.li_i = .Lcall ra t) :
    liveW D slotArr body (p + 1) = false := by
  have hL := callFlagsB_spec hflags p bi ra t hb hbi
  simp only [liveW, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, List.any_eq_false,
    List.mem_range]
  refine ⟨⟨⟨hL, ?_⟩, fun j hj => ?_⟩, ?_⟩
  · cases hb1 : body[p + 1]? with
    | none => rfl
    | some i =>
      simp only [Option.any_some]
      exact carryHiB_false hb1 (hcarry (p + 1) (List.getElem?_eq_some_iff.mp hb1).1)
        (Or.inr ⟨bi, hb, fun d o a s c e => by rw [hbi] at e; cases e⟩)
  · cases hi : body[p + 1 + j]? with
    | none => simp
    | some i =>
      simp only [Option.any_some, Option.isSome_iff_ne_none, ne_eq]
      intro hs
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hs
      obtain ⟨A, n, idx, v⟩ := y
      obtain ⟨c, D', B, X', d1, s, l, r, m, hx, hc, h3, hv, hl, hli, hr', hrm, hm, hmm, -⟩ :=
        cellIdxStore?_spec hy
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj' with rfl | rfl | rfl
      · rw [show p + 1 + 0 - 1 = p by omega, hb] at hm
        obtain rfl := Option.some.inj hm
        rw [hbi] at hmm
        simp [cellOpMov?, slotMov?] at hmm
      · rw [show p + 1 + 1 - 2 = p by omega, hb] at hl
        obtain rfl := Option.some.inj hl
        rw [hbi] at hli
        cases hli
      · rw [show p + 1 + 2 - 3 = p by omega, hb] at hr'
        obtain rfl := Option.some.inj hr'
        rw [hbi] at hrm
        simp [cellOpMov?, slotMov?] at hrm
  · rw [narrowIn_succ hb, hbi]
    simp [narrowStep, classifyK]

/-- **At the entry `liveW` is false**, when no flag is live there. -/
theorem liveW_zero {D : DeadTab} {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hL : D.live 0 = false) (hcarry : ∀ k, k < body.length → carryPrevB body k = true) :
    liveW D slotArr body 0 = false := by
  simp only [liveW, Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, List.any_eq_false,
    List.mem_range, narrowIn_zero, and_true]
  refine ⟨⟨hL, ?_⟩, fun j hj => ?_⟩
  · cases hb1 : body[0]? with
    | none => rfl
    | some i =>
      simp only [Option.any_some]
      exact carryHiB_false hb1 (hcarry 0 (List.getElem?_eq_some_iff.mp hb1).1) (Or.inl rfl)
  · cases hi : body[0 + j]? with
    | none => simp
    | some i =>
      simp only [Option.any_some, Option.isSome_iff_ne_none, ne_eq]
      intro hs
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hs
      obtain ⟨A, n, idx, v⟩ := y
      obtain ⟨c, D', B, X', d1, s, l, r, m, hx, hc, h3, -⟩ := cellIdxStore?_spec hy
      omega

/-! ## 4. The conversion to the relaxed relation -/

/-- A cell of width `64`, or of a name that is no general-purpose name, does not widen. -/
theorem widenCell_keep {r : String} {v : BitVec 64} {c : Σ w, BitVec w}
    (h : gpOk r = true → c.1 = 64) : widenCell r v c = c := by
  unfold widenCell
  by_cases hg : gpOk r = true
  · have := h hg
    simp [hg, this, DecodePrintedAddrW.narrowW]
  · simp [hg]

/-- A 64-bit read of the address state survives the widening. -/
theorem getW_widenS {sA : AState} {sa : LstateA} {r : String} {v : BitVec 64}
    (h : sa.reg.getW r 64 = some v) : (widenS sA sa).reg.getW r 64 = some v := by
  rw [getW_eq_some_iff] at h ⊢
  change widenCell r _ (sa.reg.lvm r) = _
  rw [widenCell_keep (by rw [h]; intro; rfl), h]

/-- The image state of the conversion to the relaxed relation: each name of `W` set to its value
    on the widened address state, the frame word for a name with a frame word. -/
def wideWitness (frame : String → Option (BitVec 64)) (W : List String) (sA : AState)
    (sa : LstateA) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := { s.prog.base with reg := { s.prog.base.reg with
      lvm := fun r =>
        if r ∈ W then
          match frame r with
          | some a => ⟨64, frameVal sa.mem r a⟩
          | none => (widenS sA sa).reg.lvm r
        else s.prog.base.reg.lvm r } } } }

/-- **The conversion from the wide relation to the relaxed one.** An image state related by
    `ImgRelW` to an address state that corresponds by `ACorrW` to a byte state, with the width
    analysis at its position inside `E`, is related up to the names of `E` by `ImgRelF` to the
    address state with its narrow names widened, which corresponds to the byte state by `ACorr`. -/
theorem imgRelF_of_imgRelW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {E : List String} {s : LstateMF} {sa : LstateA} {zf : Bool} {sA : AState}
    (hrel : ImgRelW frame slotArr base body s sa zf) (hc : ACorrW rsp sA sa)
    (hE : ∀ r ∈ oneBitAt frame body sa.reg.lpc, r ∈ E) :
    ImgRelF frame slotArr base body E s (widenS sA sa) ∧ ACorr rsp sA (widenS sA sa) := by
  have hA := hc.widen
  refine ⟨⟨wideWitness frame (oneBitAt frame body sa.reg.lpc) sA sa s, zf,
    ⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩, hA⟩
  · have : r ∉ oneBitAt frame body sa.reg.lpc := fun h => hr (hE r h)
    simp [wideWitness, this]
  · refine ⟨hrel.pc, fun r hf => ?_, fun q a hq => ?_, hrel.zf, hrel.cf, hrel.of, fun r hr => ?_,
      hrel.cells, fun k R A n a hS hsl hfr => ?_, fun b q a A n h1 h2 h3 h4 => ?_, hrel.held⟩
    · by_cases hW : r ∈ oneBitAt frame body sa.reg.lpc
      · simp [wideWitness, hW, hf]
      · have h1 := hrel.regsEq hf hW
        simp only [wideWitness, hW, ite_false]
        rw [h1]
        change _ = widenCell r _ (sa.reg.lvm r)
        rw [widenCell_keep fun hg => hrel.wid r hg hW]
    · by_cases hW : q ∈ oneBitAt frame body sa.reg.lpc
      · simp [wideWitness, hW, hq, widenS]
      · simp only [wideWitness, hW, ite_false]
        exact (hrel.slots q a hq).word hW
    · have := lvm_of_getW (hA.regs r hr)
      rw [this]
    · obtain ⟨h1, h2⟩ := hrel.saved k R A n a hS hsl hfr
      exact ⟨h1, fun hle => getW_widenS (h2 hle)⟩
    · have h := hrel.reload b q a A n h1 h2 h3 h4
      change widenCell b _ (sa.reg.lvm b) = _
      rw [widenCell_keep (by rw [h]; intro; rfl), h]
      rfl

/-! ## 5. The byte simulation -/

/-- **The statement of the byte simulation of the segments of a calling body of the wide class**
    by the decoded program `prog` under the oracle `O`, with `pos` the index in `prog` of a
    position of the body: from a safe state, a step of the address machine at the correspondence
    `ACorrW`, the zero flag `CondFlag` and the carry flag `CarryReq` is matched by a run of
    `prog`, and the closing return, at `ACorr`, by the closing `lea` and `ret`. -/
structure ByteSegW (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (body : Lcmd)
    (O : Nat → AState → AState → Prop) (prog : List RInstr) (pos : Nat → Nat)
    (tgt : String → Nat) (FinA : LstateA → AState → Prop) : Prop where
  /-- A step of the address machine. -/
  step : ∀ sa zf sa' zf' sA, SafeWN rsp body sa →
    stepA frame body sa zf = some (sa', zf') → ACorrW rsp sA sa → CondFlag body sA sa zf →
    CarryReq frame body sa.reg.lpc sA sa →
    ∃ sA', ACorrW rsp sA' sa' ∧ sa'.reg.lpc < body.length ∧ CondFlag body sA' sa' zf'
      ∧ CarryReq frame body sa'.reg.lpc sA' sa'
      ∧ ∀ s'', HaltsO aMachine O prog (pos sa'.reg.lpc) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- The closing return. -/
  halt : ∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
    ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA' ∧ FinA sa sA'
  /-- The index of a call. -/
  call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    prog[pos p]? = some (.call (tgt t.1))
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- **The byte simulation `ByteSegW` of a relocated body.** For a body with the facts
    `CallFactsW`, a program `prog` that satisfies `LinkedProgMap` at the target map `K`, and
    a frame that agrees with the frame of the body parameters at the names of the body,
    `ByteSegW` holds under every oracle at the index `DecodePrintedCFG.posOf` and the target
    map `K`, with the end `LprogBytesLinkReloc.FinLea`. -/
theorem byteSegW_of_linked {body : Lcmd} {ds : List PhysAbiShape.DShape}
    (hF : CallFactsW body ds) {K : String → Nat} {prog : List RInstr}
    (hL : LprogBytesLinkReloc.LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (O : Nat → AState → AState → Prop) :
    ByteSegW frame rsp body O prog (DecodePrintedCFG.posOf ds) K
      (LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame) := by
  obtain ⟨h1, h2, h3, h4⟩ := linked_segW hF hL rsp hfr O
  exact ⟨h1, h2, h3, h4⟩

/-! ## 6. The run of a segment -/

/-- At a position that passes `instrGateBW` the instruction is no cell load. -/
theorem cellLd_of_gateAtW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {x : LinstrR} (hg : gateAtW frame slotArr body k W x = true) (D B : String) (off : Nat) :
    cellA? x ≠ some (.ld D B off) := by
  intro hc
  obtain ⟨d, o, n, rfl⟩ : ∃ d o n, x = .Lopn [.reg d] o [.reg n] := by
    unfold cellA? at hc
    split at hc
    · exact ⟨_, _, _, rfl⟩
    · cases hc
  have hu : LprogAsmPrinter.untagCaret o = "LOAD:64" ∨ LprogAsmPrinter.untagCaret o = "MOV:64" := by
    simp only [cellA?] at hc
    split_ifs at hc with h1 h2 h3 h4
    · exact Or.inl h1
    · simp at hc
    · simp at hc
    · exact Or.inr h4
  have hs : slotMov? (.Lopn [.reg d] o [.reg n]) = none := by
    by_cases ho : o = "MOVQ"
    · subst ho
      simp_all
    by_cases ho2 : o = "MOV:64"
    · subst ho2
      have hn : (cellParts? n).isSome = true := by
        simp (config := { decide := true }) only [cellA?, ↓reduceIte] at hc
        cases hd : cellParts? d <;> cases hn0 : cellParts? n <;> simp_all
      simp [slotMov?, hn]
    · simp [slotMov?, ho, ho2]
  have hic : icase frame (.Lopn [.reg d] o [.reg n]) = .reg := by
    unfold icase
    rcases hu with hu | hu <;>
      simp (config := { decide := true }) [hu, hs, JasminLsemAddrRun.normA, slotCmp?,
        JasminLsemAddrRun.castTagW]
  simp only [gateAtW, carryI?, hic, Bool.and_eq_true] at hg
  have h2 := hg.2
  have hnorm : cellA? (JasminLsemAddrRun.normA (.Lopn [.reg d] o [.reg n]))
      = some (.ld D B off) := by
    rw [← hc, ← cellA?_untagCaret]
    rcases hu with hu | hu <;>
      simp (config := { decide := true }) [JasminLsemAddrRun.normA, hu]
  simp [JasminLsemCast.movImmStruct?, bitStore?, sImmB, sCmovB, regGateBW, regOkB, hnorm] at h2

/-- At the program counter of a state related by `ImgRelW`, in a body passing `imgGateCBW`, off
    the calls: the general-purpose names the instruction reads hold a value of width `64`, and the
    instruction is no cell load. -/
theorem safeAt_of_imgGateCBW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hgate : imgGateCBW frame slotArr body = true) {s : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < body.length - 1)
    (hnc : ∀ ra tg, bi.li_i ≠ .Lcall ra tg) :
    WideSafeAt body sa ∧ CellSafeAt rsp body sa := by
  have hG := imgGateW_of_imgGateCBW hgate
  by_cases hX : exemptCW frame slotArr body sa.reg.lpc
  · simp only [exemptCW, hb, Option.any_some, Bool.or_eq_true] at hX
    rcases hX with hr | harm
    · cases hx : bi.li_i with
      | Lcall ra t => exact absurd hx (hnc ra t)
      | _ => rw [hx] at hr; simp [remoteCallB] at hr
    · exact safeAt_of_cidxArmCW hrel harm hb
  · refine ⟨hG.wideSafe_of_gateW hrel hX, fun ii x D' B off p hb' hc _ => ?_⟩
    rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    exact absurd hc (cellLd_of_gateAtW (hG.instr _ _ hb (by omega) hX) D' B off)

/-- At a label of a body the safety conditions `WideSafeAt` and `CellSafeAt` are vacuous. -/
theorem safeAt_label {rsp : BitVec 64} {body : Lcmd} {sa : LstateA} {bp : Linstr} {ii : _}
    {l : LLabel} (hb : body[sa.reg.lpc]? = some bp) (hx : bp.li_i = .Llabel ii l) :
    WideSafeAt body sa ∧ CellSafeAt rsp body sa := by
  obtain ⟨ii0, li⟩ := bp
  simp only at hx
  subst hx
  refine ⟨fun _ _ _ _ hb' => ?_, fun _ x _ _ _ _ hb' hc => ?_⟩
  · rw [hb] at hb'; simp at hb'
  · rw [hb] at hb'
    obtain ⟨-, rfl⟩ := by simpa using hb'
    simp [cellA?] at hc

/-- **One step of the image of a calling body of the wide class, off the calls.** From states
    related by `ImgRelW` with the invariant of the window, a checked step of the image `callImg` at
    an instruction that is no call is matched as in `StepOut`, into `ImgRelW` and the invariant. -/
theorem stepOut_callImgW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (site : Nat → String × List String)
    (fn : String) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base body s sa s.zf)
    (hinv : CidxInv slotArr base body s) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < body.length - 1)
    (hnc : ∀ ra tg, bi.li_i ≠ .Lcall ra tg)
    (hstep : evalInstrPMemFk true (singletonProgM fn (callImg slotArr site body))
      (imgInstr slotArr body sa.reg.lpc bi.li_i) s = some t) :
    StepOut frame rsp body
      (fun t' sa' z => ImgRelW frame slotArr base body t' sa' z ∧ CidxInv slotArr base body t')
      s.zf sa t := by
  have hG := imgGateW_of_imgGateCBW hgate
  by_cases hX : exemptCW frame slotArr body sa.reg.lpc
  · simp only [exemptCW, hb, Option.any_some, Bool.or_eq_true] at hX
    rcases hX with hr | harm
    · cases hx : bi.li_i with
      | Lcall ra t => exact absurd hx (hnc ra t)
      | _ => rw [hx] at hr; simp [remoteCallB] at hr
    · simp only [cidxArmCW, Bool.and_eq_true] at harm
      exact img_stepCW hsep hphys _ hrel hinv hb harm.1 hstep
  · have hstep' : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr body))
        (imgInstr slotArr body sa.reg.lpc bi.li_i) s = some t := by
      rw [← hstep]
      unfold evalInstrPMemFk
      rw [JasminLsemMemFLeakLoop.evalInstrPMemF_congr
        (P := singletonProgM fn (virtImg slotArr body))
        (P' := singletonProgM fn (callImg slotArr site body)) rfl
        (fun l => (findLabelMem_callImg slotArr site body l).symm)]
    have hinv' := cidxInv_step hsep hG fn hrel hinv hb hlt hX hstep'
    exact (ImgGateW.img_stepW' hsep hphys hG fn hrel hb hlt hX hstep').mono
      fun _ _ h => ⟨h, hinv'⟩

/-- **The invariant of a run in a segment of the wide route**, from an image state `s`, an address
    state `sa` and a byte state `sA`: the function name, the relation `ImgRelW` with the invariant
    of the window, the correspondence `ACorrW`, the zero flag of a conditional branch, the carry
    flag of a carry-out binding, and the cast width analysis. -/
structure SegStW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (fn : String) (s : LstateMF)
    (sa : LstateA) (zf : Bool) (sA : AState) : Prop where
  /-- The function name. -/
  lfn : s.prog.lfn = fn
  /-- The relation of the image. -/
  rel : ImgRelW frame slotArr base body s sa zf
  /-- The invariant of a window. -/
  inv : CidxInv slotArr base body s
  /-- The correspondence of the bytes. -/
  corr : ACorrW rsp sA sa
  /-- The zero flag of a conditional branch. -/
  cond : CondFlag body sA sa zf
  /-- The carry flag of a carry-out binding. -/
  carry : CarryReq frame body sa.reg.lpc sA sa
  /-- The cast width analysis. -/
  narrow : NarrowInv body sa

/-- **A run of checked steps of the image of a calling body of the wide class, by the decoded
    program.** Let the body pass `imgGateCBW`, the class `physImgB` and `callSitesB`, the byte
    simulation `ByteSegW` hold, and every step of the instruction set `I` be a checked step of the
    x86 instruction set. From states with the invariant `SegStW`, a run of steps of `I` on the image
    `callImg` reaches states with the invariant, at a position of the body, and every run under `O`
    from the index of the reached position on the reached byte state extends to a run from the
    index of the start. -/
theorem steps_callImgW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {O : Nat → AState → AState → Prop} {prog : List RInstr} {pos : Nat → Nat}
    {tgt : String → Nat} {FinA : LstateA → AState → Prop}
    (hbytes : ByteSegW frame rsp body O prog pos tgt FinA)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (site : Nat → String × List String) (fn : String) :
    ∀ (n : Nat) (s u : LstateMF) (sa : LstateA) (zf : Bool) (sA : AState),
      SegStW frame slotArr base rsp body fn s sa zf sA →
      Steps I (singletonProgM fn (callImg slotArr site body)) n s u →
      ∃ sa' zf' sA', SegStW frame slotArr base rsp body fn u sa' zf' sA'
        ∧ (0 < n → sa'.reg.lpc < body.length)
        ∧ ∀ s'', HaltsO aMachine O prog (pos sa'.reg.lpc) sA' s'' →
            HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  | 0, s, u, sa, zf, sA, hst, h => by
      have hsu : s = u := Option.some.inj h
      subst hsu
      exact ⟨sa, zf, sA, hst, fun h0 => absurd h0 (Nat.lt_irrefl 0), fun _ hr => hr⟩
  | n + 1, s, u, sa, zf, sA, hst, h => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      unfold LprogIsa.Isa.lsemStepPMemF at hc
      cases hf : findInstrMem (singletonProgM fn (callImg slotArr site body)) s.prog with
      | none => rw [hf] at hc; cases hc
      | some i =>
        rw [hf] at hc
        dsimp only at hc
        have hck := hI _ _ _ _ hc
        have hrel := hst.rel
        have hz := hrel.zf
        subst hz
        rw [OwnedLprogTV.findInstrMem_single hst.lfn, ← hrel.pc] at hf
        have hlt : sa.reg.lpc < body.length - 1 := by
          have := (List.getElem?_eq_some_iff.mp hf).1
          rwa [callImg_length] at this
        obtain ⟨bi, hb⟩ : ∃ bi, body[sa.reg.lpc]? = some bi :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hnc : ∀ ra tg, bi.li_i ≠ .Lcall ra tg := by
          intro ra tg e
          obtain rfl := callSitesB_call hsites hb hlt e
          obtain ⟨f, l⟩ := tg
          rw [callImg_getElem?_call slotArr site hb (by omega) e] at hf
          obtain rfl := Option.some.inj hf
          have hn := LprogIsaProcs.evalInstrPMemF_shadowCall
            (singletonProgM fn (callImg slotArr site body))
            (LprogIsa.callShadow (site sa.reg.lpc).1 f
              ((site sa.reg.lpc).2.map LOperand.reg), .reg none) s
            (by rw [LprogIsa.shadowCall?_callShadow]; exact Option.some_ne_none _)
          rw [JasminLsemMemChecked.evalInstrPMemF_of_k hck] at hn
          cases hn
        rw [callImg_getElem?_of_ne slotArr site hb (fun f l => hnc none (f, l)),
          virtImg_getElem?, List.getElem?_dropLast, ite_eq_left hlt, hb, Option.map_some] at hf
        obtain rfl := Option.some.inj hf
        have hfn1 : c.prog.lfn = fn :=
          (AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s c
            (JasminLsemMemChecked.evalInstrPMemF_of_k hck)).1.trans hst.lfn
        obtain ⟨-, hsl, sa1, hst1, hcase⟩ :=
          stepOut_callImgW hsep hphys hgate site fn hrel hst.inv hb hlt hnc hck
        obtain ⟨hw, hcs⟩ := safeAt_of_imgGateCBW (rsp := rsp) hgate hrel hb hlt hnc
        have hn1 : NarrowInv body sa1 := narrowInv_step hst.narrow hst1
        obtain ⟨sA1, hA1, hlen1, hz1, hcy1, hk1⟩ :=
          hbytes.step sa s.zf sa1 c.zf sA ⟨hsl, hw, hcs, hst.narrow⟩ hst1 hst.corr hst.cond
            hst.carry
        rcases hcase with ⟨hrel1, hinv1⟩ | ⟨⟨bp, ii, l, hbp, hlb⟩, -, hsl1, sa2, hst2, hrel2, hinv2⟩
        · obtain ⟨sa', zf', sA', hst', hlen', hk⟩ :=
            steps_callImgW hsep hphys hgate hsites hbytes hI site fn n c u sa1 c.zf sA1
              ⟨hfn1, hrel1, hinv1, hA1, hz1, hcy1, hn1⟩ h
          refine ⟨sa', zf', sA', hst', fun _ => ?_, fun s'' hr => hk1 _ (hk _ hr)⟩
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hcu : c = u := Option.some.inj h
            subst hcu
            rw [hst'.rel.pc, ← hrel1.pc]
            exact hlen1
          · exact hlen' hn
        · obtain ⟨hw1, hcs1⟩ := safeAt_label (rsp := rsp) hbp hlb
          obtain ⟨sA2, hA2, hlen2, hz2, hcy2, hk2⟩ :=
            hbytes.step sa1 c.zf sa2 c.zf sA1 ⟨hsl1, hw1, hcs1, hn1⟩ hst2 hA1 hz1 hcy1
          obtain ⟨sa', zf', sA', hst', hlen', hk⟩ :=
            steps_callImgW hsep hphys hgate hsites hbytes hI site fn n c u sa2 c.zf sA2
              ⟨hfn1, hrel2, hinv2, hA2, hz2, hcy2, narrowInv_step hn1 hst2⟩ h
          refine ⟨sa', zf', sA', hst', fun _ => ?_, fun s'' hr => hk1 _ (hk2 _ (hk _ hr))⟩
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hcu : c = u := Option.some.inj h
            subst hcu
            rw [hst'.rel.pc, ← hrel2.pc]
            exact hlen2
          · exact hlen' hn

/-! ## 7. The simulation of a segment -/

/-- **The statement of the simulation of one segment from the narrow relation to the wide one**:
    from an image state related by `ImgRel` to an address state that corresponds by `ACorr` to a
    byte state, at a position where `L` is false, a segment to a call ends at the position of the
    call, and a segment to an end state ends at the last position, in states related by `ImgRelW`
    and `ACorrW`. -/
structure SegExactW (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (body : Lcmd) (fn : String) (L : Nat → Bool) (O : Nat → AState → AState → Prop)
    (prog : List RInstr) (pos : Nat → Nat) (tgt : String → Nat)
    (Seg : LstateMF → Option Nat → LstateMF → Prop) : Prop where
  /-- A segment to a call. -/
  toCall : ∀ s sa zf sA p u, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa → Seg s (some p) u →
    ∃ sa' zf' sA', ImgRelW frame slotArr base body u sa' zf' ∧ ACorrW rsp sA' sa'
      ∧ (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t
          ∧ prog[pos p]? = some (.call (tgt t.1)))
      ∧ ∀ s'', HaltsO aMachine O prog (pos p) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- A segment to an end state. -/
  toEnd : ∀ s sa zf sA t, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa → Seg s none t →
    ∃ sa' zf' sA', ImgRelW frame slotArr base body t sa' zf' ∧ ACorrW rsp sA' sa'
      ∧ sa'.reg.lpc + 1 = body.length
      ∧ ∀ s'', HaltsO aMachine O prog (pos sa'.reg.lpc) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- The invariant of a run at the start of a segment, at a position where `liveW` is false. -/
theorem segStW_start {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {D : DeadTab} {fn : String} (hcond : condLiveB D body = true) {s : LstateMF}
    {sa : LstateA} {zf : Bool} {sA : AState} (hfn : s.prog.lfn = fn)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hrel : ImgRel frame slotArr base body s sa zf) (hA : ACorr rsp sA sa) :
    SegStW frame slotArr base rsp body fn s sa zf sA := by
  obtain ⟨hD, hcy, hw, hn⟩ := liveW_false_spec hL
  refine ⟨hfn, imgRelW_of hrel, CidxInv.of_outside ?_, DecodePrintedAddrW.ACorr.toW hA,
    fun bi hb hc => ?_,
    carryReq_of_not_carryHi hcy _ _, narrowInv_of_nil hn⟩
  · rw [← hrel.pc]
    exact hw
  · rw [condLiveB_spec hcond _ bi hb hc] at hD
    cases hD

/-- **The simulation `SegExactW` of the segments of the image of a calling body**, from the
    byte simulation `ByteSegW`, at the positions where `liveW` is false. -/
theorem segExactW_callImg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {D : DeadTab} (hcond : condLiveB D body = true)
    {O : Nat → AState → AState → Prop} {prog : List RInstr} {pos : Nat → Nat}
    {tgt : String → Nat} {FinA : LstateA → AState → Prop}
    (hbytes : ByteSegW frame rsp body O prog pos tgt FinA)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (site : Nat → String × List String) (T : LprogIsa.ProcTable) (fn : String) :
    SegExactW frame slotArr base rsp body fn (liveW D slotArr body) O prog pos tgt
      (SegTo I T (singletonProgM fn (callImg slotArr site body))) := by
  refine ⟨fun s sa zf sA p u hfn hlen hL hrel hA hseg => ?_,
    fun s sa zf sA t hfn hlen hL hrel hA hseg => ?_, hbytes.pos_call⟩
  · obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨sa', zf', sA', hst', -, hk⟩ :=
      steps_callImgW hsep hphys hgate hsites hbytes hI site fn n s u sa zf sA
        (segStW_start hcond hfn hL hrel hA) hn
    have hrel' := hst'.rel
    have hpc : sa'.reg.lpc = p := hrel'.pc.trans hat.2
    have hi' : (callImg slotArr site body)[p]? = some i := hi
    have hp : p < body.length - 1 := by
      have := (List.getElem?_eq_some_iff.mp hi').1
      rwa [callImg_length] at this
    obtain ⟨bi, hb⟩ : ∃ bi, body[p]? = some bi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hcallp : ∃ ra t, bi.li_i = .Lcall ra t := by
      by_contra hne
      have hnc : ∀ ra t, bi.li_i ≠ .Lcall ra t := fun ra t e => hne ⟨ra, t, e⟩
      rw [callImg_getElem?_of_ne slotArr site hb (fun f l => hnc none (f, l)),
        virtImg_getElem?, List.getElem?_dropLast, ite_eq_left hp, hb, Option.map_some] at hi'
      obtain rfl := Option.some.inj hi'
      have hsh := callSitesB_other hsites hb hp hnc
      simp [LprogCallCut.isProcB, LprogIsa.procCall?, hsh] at hproc
    obtain ⟨ra, t, hbi⟩ := hcallp
    subst hpc
    exact ⟨sa', zf', sA', hrel', hst'.corr, ⟨bi, ra, t, hb, hbi, hbytes.call _ bi ra t hb hbi⟩, hk⟩
  · obtain ⟨n, hn, hhalt⟩ := hseg
    obtain ⟨sa', zf', sA', hst', hlen', hk⟩ :=
      steps_callImgW hsep hphys hgate hsites hbytes hI site fn n s t sa zf sA
        (segStW_start hcond hfn hL hrel hA) hn
    have hrel' := hst'.rel
    have hlenE : sa'.reg.lpc < body.length := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · have hst : s = t := Option.some.inj hn
        subst hst
        rw [hrel'.pc, ← hrel.pc]
        exact hlen
      · exact hlen' hn0
    have hend : sa'.reg.lpc + 1 = body.length := by
      have hh : findInstrMem (singletonProgM fn (callImg slotArr site body)) t.prog
          = none := hhalt
      rw [OwnedLprogTV.findInstrMem_single hst'.lfn, List.getElem?_eq_none_iff, callImg_length,
        ← hrel'.pc] at hh
      omega
    exact ⟨sa', zf', sA', hrel', hst'.corr, hend, hk⟩

/-- **The simulation `SegSim` of a segment up to dead names, from `SegExactW`.** Let the steps of
    the instruction set `I` on the body keep the agreement of the table `D` (`DeadSteps`), the
    segments have the simulation `SegExactW` at the positions where `L` is false, `L` being true
    where a flag of `D` is live, the width analysis be dead at the calls and the return
    (`bitsDeadB`), the closing return of the byte simulation hold, `Fin` hold of an image state
    related by `ImgRel` to an address state that satisfies `FinA`, and `Fin` be kept by a change of
    the dead names of the position of the end state. Then the segments have the simulation
    `SegSim` at the dead names of `D`. -/
theorem segSim_of_segExactW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {D : DeadTab} {L : Nat → Bool} {O : Nat → AState → AState → Prop}
    {prog : List RInstr} {pos : Nat → Nat} {tgt : String → Nat} {I : LprogIsa.Isa}
    {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM} {FinA : LstateA → AState → Prop}
    {Fin : LstateMF → AState → Prop} (hD : DeadSteps D I (singletonProgM fn B))
    (hLD : ∀ k, L k = false → D.live k = false)
    (hbits : bitsDeadB frame D body = true)
    (hX : SegExactW frame slotArr base rsp body fn L O prog pos tgt
      (SegTo I T (singletonProgM fn B)))
    (hhalt : ∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
      ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA' ∧ FinA sa sA')
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf → FinA sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA) :
    SegSim frame slotArr base rsp body fn D.dead L O prog pos tgt
      (SegTo I T (singletonProgM fn B)) Fin := by
  refine ⟨fun s sa sA p u hfn hlen hL hI hA hseg => ?_,
    fun s sa sA t hfn hlen hL hI hA hseg => ?_, hX.pos_call⟩
  · obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF (hLD _ hL) hI
    obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨u', hn', hagu⟩ := hD n s s' u hag hn
    have hat' : atPc (singletonProgM fn B) p u' :=
      ⟨hagu.off.fn.symm.trans hat.1, hagu.off.pc.symm.trans hat.2⟩
    obtain ⟨sa', zf', sA', hrel', hA', ⟨bi, ra, t', hb, hbi, hprog⟩, hk⟩ :=
      hX.toCall s' sa zf sA p u' (hag.off.fn.symm.trans hfn) hlen hL hrel hA
        ⟨n, hn', hat', i, hi, hproc⟩
    have hpu : u.prog.base.reg.lpc = p := hat.2
    have hpa : sa'.reg.lpc = p := hrel'.pc.trans (hagu.off.pc.symm.trans hpu)
    obtain ⟨⟨u'', zf'', hag2, hrel2⟩, hA2⟩ := imgRelF_of_imgRelW (E := D.dead p) hrel' hA'
      (by rw [hpa]; exact bitsDeadB_call hbits hb hbi)
    refine ⟨widenS sA' sa', sA', ⟨u'', zf'', ?_, hrel2⟩, hA2, hpa,
      ⟨bi, ra, t', hb, hbi, hprog⟩, hk⟩
    have := hagu.off
    rw [hpu] at this
    exact (this.trans hag2).mono fun r hr => by simpa using hr
  · obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF (hLD _ hL) hI
    obtain ⟨n, hn, hhalt0⟩ := hseg
    obtain ⟨t', hn', hagt⟩ := hD n s s' t hag hn
    have hhalt' : Halted (singletonProgM fn B) t' := by
      unfold Halted findInstrMem at hhalt0 ⊢
      rw [← hagt.off.fn]
      exact (congrArg (fun q => if t.prog.lfn = fn then B[q]? else none) hagt.off.pc.symm).trans
        hhalt0
    obtain ⟨sa', zf', sA', hrel', hA', hend, hk⟩ :=
      hX.toEnd s' sa zf sA t' (hag.off.fn.symm.trans hfn) hlen hL hrel hA ⟨n, hn', hhalt'⟩
    have hpe : sa'.reg.lpc = body.length - 1 := by omega
    obtain ⟨⟨t'', zf'', hag2, hrel2⟩, hA2⟩ := imgRelF_of_imgRelW
      (E := D.dead (body.length - 1)) hrel' hA' (by rw [hpe]; exact bitsDeadB_last hbits)
    obtain ⟨sA'', hrun, hfa⟩ := hhalt (widenS sA' sa') sA' hend hA2
    refine ⟨sA'', hk _ hrun, hFin t t'' sA'' ?_ (hfin _ _ _ _ hrel2 hfa)⟩
    have hpt : t.prog.base.reg.lpc = body.length - 1 := by
      rw [hagt.off.pc, ← hrel'.pc, hpe]
    rw [hpt]
    have := hagt.off
    rw [hpt] at this
    exact (this.trans hag2).mono fun r hr => by simpa using hr

/-! ## 8. The runs from Boolean checks -/

/-- **A halting run of the image of a calling body of the wide class at the steps of its call
    sites is a run of the decoded program under an oracle that answers its callees**, from Boolean
    checks and the byte simulation `ByteSegW` of the segments. Let the body pass `physImgB`,
    `imgGateCBW` and `callSitesB`; let every carry-out binding follow its add; let `bitsDeadB`,
    `callFlagsB` and `condLiveB` accept the table `D`; let each callee meet its specification; let
    every step of `I` be a checked step of the x86 instruction set and the steps of `I` on the image
    keep the agreement of `D`; and let each step `Glue` of the image at a call be a step of the site
    (`SiteStep`) of its callee at the dead names of `p` and `p + 1`. Then, under an oracle that
    answers at `tgt f` the runs of the callee of each called symbol, every halting run of
    `I.withProcs T` on the image, from an image state in `fn` at a position where `liveW` is false,
    related up to the dead names of its position to an address state that corresponds to a byte
    state, is matched by a run of `prog` to a byte state that satisfies `Fin` with the end state. -/
theorem haltsO_of_deadChecksS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (hcarry : ∀ k, k < body.length → carryPrevB body k = true)
    {X : String → CalleeRun} {c : String → CalleeSig}
    (hX : ∀ f, CalledIn body f → CalleeSpec (X f) (c f))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : String → Nat}
    {O : Nat → AState → AState → Prop}
    (hCall : ∀ f, CalledIn body f → ∀ s tr s', X f s tr s' → O (tgt f) s s') {D : DeadTab}
    (hbits : bitsDeadB frame D body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {FinA : LstateA → AState → Prop}
    (hbytes : ByteSegW frame rsp body O prog pos tgt FinA)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf → FinA sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (X f) (c f) (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr site body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' :=
  haltsO_of_runChainS (L := liveW D slotArr body) hX hCall
    (fun _ _ _ _ hb hbi => liveW_succ_call hflags hcarry hb hbi) (lt_of_call_imgGateCBW hgate)
    (segSim_of_segExactW hD (fun _ h => (liveW_false_spec h).1) hbits
      (segExactW_callImg hsep hphys hgate hsites hcond hbytes hI site T fn) hbytes.halt hfin hFin)
    hStep (runChain_of_run _ T _ n s t hrun) sa sA hfn hlen hL hI0 hA

/-- **A halting run of the image of a calling body of the wide class at the steps of its call sites
    is a run of the program of its relocated item list under an oracle that answers its callees**,
    from Boolean checks. The hypotheses are those of `haltsO_of_deadChecksS` with the byte
    simulation replaced by: the class `printedAddrCWB`, the shapes `ds` of the body, the program
    `prog` of the relocated item list under an item target map `tgtI` that sends each call of the
    symbol `f` to the index `K f`, and the agreement of `frame` with the frame of the body
    parameters at the names of the body. The run starts at the index `DecodePrintedCFG.posOf` of
    the position of the address state, and the end is `LprogBytesLinkReloc.FinLea`. -/
theorem haltsO_of_linkedChecksS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : String → CalleeRun} {c : String → CalleeSig}
    (hX : ∀ f, CalledIn body f → CalleeSpec (X f) (c f))
    {G : Nat} {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr}
    (tgtI : LprogBytesDecode.Item → Option (Nat × Nat))
    (K : String → Nat)
    (hK : ∀ it f j t, it.target = none → it.sym = some f → tgtI it = some (j, t) → j = K f)
    (hP : LprogBytesLinkReloc.expectedRelocMap
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) tgtI
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {O : Nat → AState → AState → Prop}
    (hCall : ∀ f, CalledIn body f → ∀ s tr s', X f s tr s' → O (K f) s s')
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (X f) (c f) (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr site body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine O prog (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' := by
  have hCF := callFacts_of_printedAddrCWB hcls hshapes
  exact haltsO_of_deadChecksS hsep hphys hgate hsites hCF.carry hX hCall hbits hflags hcond hI hD
    (byteSegW_of_linked hCF
      (LprogBytesLinkReloc.linkedProg_of_itemsMapL symBase hCF.toLinkFacts tgtI K hK prog hP)
      rsp hfr _)
    hfin hFin hStep n hrun hfn hlen hL hI0 hA

/-- **A halting run of the image of a calling body of the wide class at the steps of its call sites,
    all of one callee, is a run of the program of its relocated item list under the oracle of the
    callee**: `haltsO_of_linkedChecksS` at the constant callee `X`, interface `c` and target
    `tgt`, with the program `prog` of the relocated item list in front of a callee block at
    the index `tgt` and the byte length `L`. -/
theorem haltsO_of_linkedChecksOne {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {G : Nat} {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr} {tgt L : Nat}
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt L
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) →
      SiteStep frame slotArr base rsp body X c (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr site body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (Callee.oracleAt tgt X) prog
        (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' :=
  haltsO_of_linkedChecksS hsep hphys hgate hsites (X := fun _ => X) (c := fun _ => c)
    (fun _ _ => hX) hcls hshapes hfr symBase _ (fun _ => tgt)
    (fun _ _ _ _ _ _ h => (Prod.mk.inj (Option.some.inj h)).1.symm) hP
    (fun _ _ _ tr _ h => ⟨rfl, tr, h⟩) hbits hflags hcond hI hD hfin hFin
    (fun p u v hg hpc bi ra f l hb hbi => hStep p u v hg hpc ⟨bi, ra, (f, l), hb, hbi⟩)
    n hrun hfn hlen hL hI0 hA

/-- **A halting run of the image of a calling body of the wide class at the steps of its call sites
    is a run through calls of the program its linked bytes decode to**, from Boolean checks. Let the
    callee region `cb` hold, for each symbol `f` of `fs`, a block `q f` without `call` whose leaky
    runs meet the specification of `c f` (`RegionBlocks`), let every call of the body name a symbol
    of `fs`, and let the relocated item list of the body satisfy `branchOKRelocMap` and denote
    `prog` under the target map of the region placed after the instructions and bytes of the body.
    Under the other hypotheses of `haltsO_of_linkedChecksS`, the bytes of the relocated body
    followed by `cb` decode to `prog` followed by the region program `Q` with its targets raised,
    and this program has a run through calls from the index of the position of the address state
    to a byte state that satisfies `Fin` with the end state. -/
theorem haltsC_of_linkedChecksS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {fs : List String}
    {cb : List (BitVec 8)} {o k : String → Nat} {q : String → List RInstr} {Q : List RInstr}
    (hR : LprogBytesLinkReloc.RegionBlocks cb fs o k q Q) {c : String → CalleeSig}
    (hX : ∀ f, CalledIn body f → CalleeSpec (Callee.runOf r (q f)) (c f))
    (hfs : bodyCallSymsB (fun g => decide (g ∈ fs)) body = true)
    {G : Nat} {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr}
    (hbr : LprogBytesLinkReloc.branchOKRelocMap
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesLinkReloc.symTgt (LprogBytesLinkReloc.regionTgt fs
        (LprogBytesDecode.decCount
          (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
        (LprogBytes.encodeLfundefBytesReloc symBase body).length o k)) 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedRelocMap
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesLinkReloc.symTgt (LprogBytesLinkReloc.regionTgt fs
        (LprogBytesDecode.decCount
          (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
        (LprogBytes.encodeLfundefBytesReloc symBase body).length o k))
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (Callee.runOf r (q f)) (c f) (D.dead p)
        (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr site body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length Q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length Q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' := by
  have hCF := callFacts_of_printedAddrCWB hcls hshapes
  obtain ⟨hsaves, hF0, hFr⟩ := printedAddrCWB_reloc hcls
  obtain ⟨hdec, hLk⟩ := LprogBytesLinkReloc.linkedProg_of_bytesSymL symBase hCF.toLinkFacts cb fs o
    k Q prog hsaves hF0 hFr hR.decode hbr hP
  have hmem : ∀ f, CalledIn body f → f ∈ fs := by
    rintro f ⟨p, bi, ra, l, hb, hbi⟩
    have hp := lt_of_call_imgGateCBW hgate p bi ra _ hb hbi
    simpa using bodyCallSymsB_spec hfs hb (by omega) hbi
  obtain ⟨sA', hrun', hfin'⟩ := haltsO_of_deadChecksS hsep hphys hgate hsites hCF.carry hX
    (tgt := fun f => prog.length + k f)
    (O := Callee.oracleOf fs (fun f => prog.length + k f) (fun f => Callee.runOf r (q f)))
    (fun f hf _ tr _ h => ⟨f, hmem f hf, rfl, tr, h⟩) hbits hflags hcond hI hD
    (byteSegW_of_linked hCF hLk rsp hfr _) hfin hFin hStep n hrun hfn hlen hL hI0 hA
  refine ⟨hdec, sA', Callee.haltsC_of_haltsO_blocks aMachine prog Q (fun t s sc ho => ?_) hrun',
    hfin'⟩
  obtain ⟨f, hf, rfl, tr, hrunf⟩ := ho
  obtain ⟨A, B, hQ, hA⟩ := hR.block f hf
  exact ⟨A, q f, B, hQ, by rw [hA], hR.callFree f hf, DecodedCT.RunL.halts hrunf⟩

/-- **A halting run of the image of a calling body of the wide class at the steps of its call sites,
    all of one callee, is a run through calls of the program its linked bytes decode to**:
    `haltsC_of_linkedChecksS` at the constant interface `c` and the one-block region of the
    callee block `cb`, which decodes to a block `q` without `call` whose leaky runs meet the
    specification of `c`, with the relocated item list of the body satisfying
    `branchOKReloc` and denoting `prog` at its own instruction count and byte length. -/
theorem haltsC_of_linkedChecksOne {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {c : CalleeSig}
    (hX : CalleeSpec (Callee.runOf r q) c) (hq : ∀ tg, RInstr.call tg ∉ q)
    {G : Nat} {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body = some ds)
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
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) →
      SiteStep frame slotArr base rsp body (Callee.runOf r q) c (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr site body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' := by
  have hCF := callFacts_of_printedAddrCWB hcls hshapes
  have hagree : ∀ it ∈ LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds,
      it.target = none → ∀ d, it.dec = some (.call d) →
        (fun _ => some (LprogBytesDecode.decCount
            (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds),
          (LprogBytes.encodeLfundefBytesReloc symBase body).length)) it
        = LprogBytesLinkReloc.symTgt (LprogBytesLinkReloc.regionTgt
            (body.filterMap fun i => remoteSym i.li_i)
            (LprogBytesDecode.decCount
              (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
            (LprogBytes.encodeLfundefBytesReloc symBase body).length
            (fun _ => 0) (fun _ => 0)) it := by
    intro it hit ht d hd
    obtain ⟨f, hf, i, hi, hr⟩ :=
      LprogBytesLinkReloc.fundefItemsRelocL_sym symBase _ body ds it hit ht d hd
    have hmem : f ∈ body.filterMap fun i => remoteSym i.li_i :=
      List.mem_filterMap.mpr ⟨i, hi, hr⟩
    simp [LprogBytesLinkReloc.symTgt, hf, LprogBytesLinkReloc.regionTgt, hmem]
  have hfs : bodyCallSymsB (fun g => decide (g ∈ body.filterMap fun i => remoteSym i.li_i))
      body = true := by
    simp only [bodyCallSymsB, List.all_eq_true, List.mem_range]
    intro p hp
    cases hb : body[p]? with
    | none => rfl
    | some bi =>
      rw [Option.all_some]
      split
      · rename_i ra f l hbi
        have hbk : body[p]'(by omega) = bi := (List.getElem?_eq_some_iff.mp hb).2
        have hrem : remoteSym bi.li_i ≠ none := by
          rcases hCF.instr p (by omega) with h | h
          · rwa [hbk] at h
          · rw [hbk, hbi] at h
            simp [instrOKWB] at h
        rw [hbi] at hrem
        exact decide_eq_true (List.mem_filterMap.mpr
          ⟨bi, List.mem_of_getElem? hb, by rw [hbi]; simpa [remoteSym] using hrem⟩)
      · rfl
  exact haltsC_of_linkedChecksS hsep hphys hgate hsites r
    (LprogBytesLinkReloc.regionBlocks_one cb q _ hcb hne hq) (c := fun _ => c) (fun _ _ => hX)
    hfs hcls hshapes hfr symBase
    (by rw [← LprogBytesLinkReloc.branchOKRelocMap_congr _ _ hagree]; exact hbr)
    (by rw [← LprogBytesLinkReloc.expectedRelocMap_congr _ _ hagree]; exact hP)
    hbits hflags hcond hI hD hfin hFin
    (fun p u v hg hpc bi ra f l hb hbi => hStep p u v hg hpc ⟨bi, ra, (f, l), hb, hbi⟩)
    n hrun hfn hlen hL hI0 hA

/-! ## 9. The narrow instruction class in the wide one -/

section Narrow

open DecodePrintedAddr (AArm classifyA classifyA_instr regArmB plainB cellParts?_gp
  cellParts?_of_spillOff)
open DecodePrinted (Arm isMovM isShI aluArm)
open DecodePrintedAddrW (classifyS classifyC classifyM classifyI classifyL classifyV classifyE
  classifyX classifyEI classifyR)
open JasminLsemCast (movImmStruct?)

/-- The classifiers of `instrOKWB` before `classifyA`, all without an arm at an instruction. -/
def NoWideArm (x : LinstrR) : Prop :=
  classifyK x = none ∧ movImmStruct? x = none ∧ classifyS x = none ∧ classifyC x = none
    ∧ classifyM x = none ∧ classifyI x = none ∧ classifyL x = none ∧ classifyV x = none
    ∧ classifyE x = none ∧ classifyX x = none ∧ classifyEI x = none ∧ classifyR x = none

/-- The names of the two-address arithmetic and logic arm. -/
theorem aluArm_cases {m : String} (h : (aluArm m).isSome = true) :
    m = "ADD:64" ∨ m = "SUB:64" ∨ m = "AND:64" ∨ m = "OR:64" ∨ m = "XOR:64" := by
  unfold aluArm at h
  split at h <;> simp_all

/-- `NoWideArm` of a shape that only `classifyK` and `classifyM` read. -/
theorem noWideArm_one {d m s : String} (hK : JasminLsemAddrRun.castTagW m = none)
    (hM : classifyM (.Lopn [.reg d] m [.reg s]) = none) :
    NoWideArm (.Lopn [.reg d] m [.reg s]) := by
  refine ⟨?_, rfl, rfl, rfl, hM, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [classifyK, hK]

/-- `NoWideArm` of a register source and a second register source, away from the mnemonics of a
    materialised comparison and a register-count shift. -/
theorem noWideArm_two {d a s m : String} (hE : m ≠ "SETE:64" ∧ m ≠ "SETNE:64")
    (hX : m ≠ "SHL:64" ∧ m ≠ "SHR:64") : NoWideArm (.Lopn [.reg d] m [.reg a, .reg s]) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · simp [classifyE, hE.1, hE.2]
  · simp [classifyX, hX.1, hX.2]

/-- `NoWideArm` of a register source and an immediate, away from the mnemonics of a materialised
    comparison and an arithmetic right shift. -/
theorem noWideArm_twoI {d a m : String} {v : Nat} (hE : m ≠ "SETE:64" ∧ m ≠ "SETNE:64")
    (hR : m ≠ "SAR:64") : NoWideArm (.Lopn [.reg d] m [.reg a, .imm v]) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [classifyEI, hE.1, hE.2]
  · simp [classifyR, hR]

/-- A frame-word move meets no classifier of the wide class before `classifyA`. -/
theorem noWideArm_mov {d m s : String} (hm : isMovM m = true) (hd : cellParts? d = none)
    (hs : cellParts? s = none) : NoWideArm (.Lopn [.reg d] m [.reg s]) := by
  simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl <;> refine noWideArm_one (by decide +kernel) ?_ <;>
    simp (config := { decide := true }) [classifyM, hd, hs]

/-- A count-in-mnemonic shift meets no classifier of the wide class before `classifyA`. -/
theorem noWideArm_shift {d m s : String} {e : Nat} (hK : JasminLsemAddrRun.castTagW m = none)
    (hT : (LprogBytes.tagShiftExt (stripWidthTag m) == some e) = true) :
    NoWideArm (.Lopn [.reg d] m [.reg s]) := by
  have hne : ∀ n, LprogBytes.tagShiftExt (stripWidthTag n) = none →
      m ≠ n := by
    rintro n hn rfl
    simp [hn] at hT
  refine noWideArm_one hK ?_
  have h1 := hne "LOAD:64" (by decide +kernel)
  have h2 := hne "STORE:64" (by decide +kernel)
  have h3 := hne "MOV:64" (by decide +kernel)
  simp [classifyM, h1, h2, h3]

/-- **An arm of the narrow class meets no classifier of the wide class before `classifyA`.** -/
theorem noWideArm_of_ok {P : Params} {a : AArm} (h : a.ok P = true) : NoWideArm a.instr := by
  cases a with
  | reg b =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hr, hok⟩, hp⟩ := h
    simp only [AArm.instr]
    cases b with
    | movRR m D S =>
      simp only [Arm.ok, Bool.and_eq_true] at hok
      exact noWideArm_mov hok.1.1 (cellParts?_gp hok.1.2) (cellParts?_gp hok.2)
    | movRI D v =>
      simp only [Arm.ok, Bool.and_eq_true] at hok
      refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · simp [Arm.instr, movImmStruct?, ImageAddrSimW.isMovImmMnem_mov64]
      · simp [Arm.instr, classifyI, (DecodePrinted.gpFacts hok.1.1).notSlot]
      · simp [Arm.instr, classifyL, hok.2]
    | store m q S => simp [regArmB] at hr
    | load m D q => simp [regArmB] at hr
    | alu m D S =>
      simp only [Arm.ok, Bool.and_eq_true] at hok
      rcases aluArm_cases hok.1.1 with rfl | rfl | rfl | rfl | rfl <;>
        exact noWideArm_two (by decide) (by decide)
    | aluI m D v =>
      simp only [Arm.ok, Bool.and_eq_true] at hok
      rcases aluArm_cases hok.1.1 with rfl | rfl | rfl | rfl | rfl <;>
        exact noWideArm_twoI (by decide) (by decide)
    | shr m D S =>
      simp only [Arm.ok, Bool.and_eq_true, Arm.instr, plainB, Option.isNone_iff_eq_none] at hok hp
      exact noWideArm_shift hp.2 hok.1.1.1.1.2
    | shl0 m D S =>
      simp only [Arm.ok, Bool.and_eq_true, Arm.instr, plainB, Option.isNone_iff_eq_none] at hok hp
      exact noWideArm_shift hp.2 hok.1.1.1.2
    | shI m D k =>
      simp only [Arm.ok, Bool.and_eq_true, isShI, Bool.or_eq_true, beq_iff_eq] at hok
      rcases hok.1.1.1 with rfl | rfl <;> exact noWideArm_twoI (by decide) (by decide)
    | lea D B X sc => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | st m q S =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact noWideArm_mov h.2 (cellParts?_of_spillOff h.1.1.2) (cellParts?_gp h.1.1.1.1)
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact noWideArm_mov h.2 (cellParts?_gp h.1.1.1.1.1) (cellParts?_of_spillOff h.1.1.1.2)
  | cmpR c r => exact noWideArm_two (by decide) (by decide)
  | cmpI c k => exact noWideArm_twoI (by decide) (by decide)
  | cmpM c q => exact noWideArm_two (by decide) (by decide)
  | ldx D B I => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | stx d B I V => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | mul D S => exact noWideArm_two (by decide) (by decide)
  | mulxS H S => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | mulx L H S => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | zero B n => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | simm d B V k => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | leaF d q =>
    exact noWideArm_one (by decide +kernel) (by simp (config := { decide := true }) [classifyM])

/-- **The narrow instruction class is in the wide one.** -/
theorem instrOKWB_of_instrOKB {body : Lcmd} {P : Params} {i : LinstrR}
    (h : instrOKB body P i = true) : instrOKWB body P i = true := by
  cases i with
  | Lopn ds o ss =>
    simp only [instrOKB] at h
    cases hA : classifyA (.Lopn ds o ss) with
    | none => simp [hA] at h
    | some a =>
      rw [hA] at h
      have hw := noWideArm_of_ok (P := P) h
      rw [classifyA_instr hA] at hw
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hw
      simp only [instrOKWB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hA]
      exact h
  | Llabel kd l => rfl
  | Lcond c l =>
    cases c with
    | reg cc => simpa [instrOKWB, instrOKB] using h
    | _ => simp [instrOKB] at h
  | _ => simp [instrOKB] at h

/-- No name a symbolic state writes holds a word whose outermost constructor fixes the width `1`. -/
def NoBitWr (ss : OwnedLprogTV.SSt) : Prop :=
  ∀ a ∈ ss.wr, (ss.regs a).wknown ≠ some 1

/-- `regOut` of the empty analysis is empty at an instruction whose symbolic step satisfies
    `NoBitWr`. -/
theorem regOut_nil_of_free {x : LinstrR}
    (h : ∀ ss gs, OwnedLprogTV.symStep (x, .reg none) OwnedLprogTV.SSt.start = .ok ss gs →
      NoBitWr ss) : regOut [] x = [] := by
  unfold regOut
  split
  · rename_i ss gs heq
    have hf := h ss gs heq
    simp only [List.filter_nil, List.nil_append, List.filter_eq_nil_iff, beq_iff_eq]
    exact hf
  · rfl

/-- A symbolic state with the register file and the written names of one write of a term
    other than a one-bit word satisfies `NoBitWr`. -/
theorem noBitWr_set {d : String} {t : OwnedLprogTV.STerm} (ht : t.wknown ≠ some 1)
    (ss : OwnedLprogTV.SSt) (h1 : ss.wr = [d])
    (h2 : ss.rf = (OwnedLprogTV.SSt.start.setR d t).rf) : NoBitWr ss := by
  intro a ha
  rw [h1, List.mem_singleton] at ha
  subst ha
  have : ss.regs a = (OwnedLprogTV.SSt.start.setR a t).regs a := by
    unfold OwnedLprogTV.SSt.regs
    rw [h2]
  rw [this, OwnedLprogTV.SSt.setR_regs, ite_eq_left rfl]
  exact ht

/-- `regOut` of the empty analysis is empty at an instruction with one destination that is no
    compare and no carry or wide form, and whose register moves and `symMC` writes that destination
    with a term other than a one-bit word. -/
theorem regOut_nil_of_mc {d m : String} {ss : List LOperand}
    (hc : cmpArgs? (.Lopn [.reg d] m ss, .reg none) = none)
    (hv : ∀ p, movRegArgs? (.Lopn [.reg d] m ss, .reg none) = some p →
      p.1 = d ∧ (OwnedLprogTV.SSt.start.regs p.2).wknown ≠ some 1)
    (hca : carryArgs? (.Lopn [.reg d] m ss, .reg none) = none)
    (hw : wideArgs? (.Lopn [.reg d] m ss, .reg none) = none)
    (key : ∀ d' t g, OwnedLprogTV.symMC (.Lopn [.reg d] m ss) OwnedLprogTV.SSt.start.regs
      = .set d' t g → d' = d ∧ t.wknown ≠ some 1) :
    regOut [] (.Lopn [.reg d] m ss) = [] := by
  refine regOut_nil_of_free fun s gs h => ?_
  have hcast : OwnedLprogTV.symCast (.Lopn [.reg d] m ss, none) OwnedLprogTV.SSt.start.regs
      = OwnedLprogTV.symMC (.Lopn [.reg d] m ss) OwnedLprogTV.SSt.start.regs := by
    unfold OwnedLprogTV.symCast
    dsimp only
    split
    · cases movImmStruct? (.Lopn [.reg d] m ss) <;> rfl
    · rfl
  unfold OwnedLprogTV.symStep at h
  rw [hc] at h
  dsimp only at h
  cases hmv : movRegArgs? (.Lopn [.reg d] m ss, .reg none) with
  | some p =>
    rw [hmv] at h
    obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj h
    obtain ⟨dst, src⟩ := p
    obtain ⟨rfl, hk⟩ := hv _ hmv
    exact noBitWr_set hk _ rfl rfl
  | none =>
    rw [hmv] at h
    simp only [flagCondCC?, hca, hw, OwnedLprogTV.symMem, hcast] at h
    cases hs : OwnedLprogTV.symMC (.Lopn [.reg d] m ss) OwnedLprogTV.SSt.start.regs with
    | set d' t g =>
      rw [hs] at h
      obtain ⟨rfl, hk⟩ := key d' t g hs
      simp only [OwnedLprogTV.liftR, OwnedLprogTV.aluFl] at h
      obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj h
      exact noBitWr_set hk _ rfl rfl
    | nop =>
      rw [hs] at h
      simp only [OwnedLprogTV.liftR, OwnedLprogTV.aluFl] at h
      obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj h
      intro a ha
      cases ha
    | fail =>
      rw [hs] at h
      simp [OwnedLprogTV.liftR, OwnedLprogTV.aluFl] at h
    | unk =>
      rw [hs] at h
      simp [OwnedLprogTV.liftR, OwnedLprogTV.aluFl] at h

/-- **A move with one register source adds no name to the empty width analysis.** -/
theorem regOut_one (d m s : String) : regOut [] (.Lopn [.reg d] m [.reg s]) = [] := by
  refine regOut_nil_of_mc rfl (fun p hp => ?_) rfl rfl (fun d' t g hs => ?_)
  · simp only [movRegArgs?] at hp
    split_ifs at hp <;> cases hp <;>
      exact ⟨rfl, by simp [OwnedLprogTV.STerm.wknown, OwnedLprogTV.SSt.regs,
        OwnedLprogTV.SSt.start]⟩
  · simp only [OwnedLprogTV.symMC, OwnedLprogTV.symSh, OwnedLprogTV.symN,
      JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
      JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
      JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?] at hs
    repeat' split at hs
    all_goals first
      | (cases hs; exact ⟨rfl, by simp [OwnedLprogTV.STerm.wknown, OwnedLprogTV.SSt.regs,
          OwnedLprogTV.SSt.start]⟩)
      | simp at hs

/-- The last hypothesis of `regOut_nil_of_mc` at a concrete mnemonic, from `hs`. -/
local macro "regout_key" : tactic => `(tactic| (
  rename_i hs
  simp (config := { decide := true }) [OwnedLprogTV.symMC, OwnedLprogTV.symSh,
    OwnedLprogTV.symN, JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
    JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
    JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?] at hs
  obtain ⟨h1, h2, -⟩ := hs
  subst h1 h2
  exact ⟨rfl, by simp (config := { decide := true }) [OwnedLprogTV.STerm.wknown, widthFromTag]⟩))

/-- The proof of `regOut_nil_of_mc` at a concrete mnemonic. -/
local macro "regout_arm" : tactic => `(tactic| (
  refine regOut_nil_of_mc ?_ ?_ ?_ ?_ ?_
  · first | rfl | simp (config := { decide := true }) [cmpArgs?, withWidthTag]
  · intro p hp
    first | cases hp | simp (config := { decide := true }) [movRegArgs?, copyQ, withWidthTag] at hp
  · first | rfl | simp (config := { decide := true }) [carryArgs?, withWidthTag]
  · first | rfl | simp (config := { decide := true }) [wideArgs?, withWidthTag]
  · intro d' t g hs
    simp (config := { decide := true }) [OwnedLprogTV.symMC, OwnedLprogTV.symSh,
      OwnedLprogTV.symN, JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
      JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
      JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?] at hs
    repeat' split at hs
    all_goals first
      | (cases hs; exact ⟨rfl, by simp [OwnedLprogTV.STerm.wknown, OwnedLprogTV.SSt.regs,
          OwnedLprogTV.SSt.start]⟩)
      | simp at hs))

/-- The state of the symbolic step of a widening multiply: its two destinations hold terms other
    than one-bit words. -/
theorem noBitWr_mulx (L H : String) (tx tb : OwnedLprogTV.STerm) :
    NoBitWr ((OwnedLprogTV.SSt.start.setR L (OwnedLprogTV.mulLoT tx tb)).setR H
      (.mulx true tx tb)) := by
  intro a ha
  simp only [OwnedLprogTV.SSt.setR_regs]
  split_ifs
  · simp [OwnedLprogTV.STerm.wknown]
  · simp [OwnedLprogTV.STerm.wknown, OwnedLprogTV.mulLoT]
  · simp only [OwnedLprogTV.SSt.setR, OwnedLprogTV.SSt.start, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    grind

/-- **An arm of the narrow class adds no name to the empty width analysis.** -/
theorem regOut_nil_of_ok {P : Params} {a : AArm} (h : a.ok P = true) :
    regOut [] (JasminLsemAddrRun.normA a.instr) = [] := by
  have hone : ∀ d m s, regOut [] (JasminLsemAddrRun.normA (.Lopn [.reg d] m [.reg s])) = [] :=
    fun _ _ _ => regOut_one _ _ _
  cases a with
  | reg b =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨-, hok⟩, -⟩ := h
    cases b with
    | movRR m D S => exact hone _ _ _
    | movRI D v =>
      simp (config := { decide := true }) only [AArm.instr, Arm.instr, JasminLsemAddrRun.normA,
        LprogAsmPrinter.untagCaret, ↓reduceIte]
      refine regOut_nil_of_mc rfl (fun p hp => by simp [movRegArgs?] at hp) rfl rfl
        (fun d' t g hs => ?_)
      regout_key
    | store m q S => exact hone _ _ _
    | load m D q => exact hone _ _ _
    | alu m D S =>
      simp only [Arm.ok, Bool.and_eq_true] at hok
      rcases aluArm_cases hok.1.1 with rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [AArm.instr, Arm.instr,
          JasminLsemAddrRun.normA, LprogAsmPrinter.untagCaret, ↓reduceIte] <;> regout_arm
    | aluI m D v =>
      simp only [Arm.ok, Bool.and_eq_true] at hok
      rcases aluArm_cases hok.1.1 with rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [AArm.instr, Arm.instr,
          JasminLsemAddrRun.normA, LprogAsmPrinter.untagCaret, ↓reduceIte] <;> regout_arm
    | shr m D S => exact hone _ _ _
    | shl0 m D S => exact hone _ _ _
    | shI m D k =>
      simp only [Arm.ok, Bool.and_eq_true, isShI, Bool.or_eq_true, beq_iff_eq] at hok
      rcases hok.1.1.1 with rfl | rfl <;>
        simp (config := { decide := true }) only [AArm.instr, Arm.instr,
          JasminLsemAddrRun.normA, LprogAsmPrinter.untagCaret, ↓reduceIte] <;> regout_arm
    | lea D B X sc =>
      simp (config := { decide := true }) only [AArm.instr, Arm.instr, JasminLsemAddrRun.normA,
        LprogAsmPrinter.untagCaret, ↓reduceIte]
      refine regOut_nil_of_mc rfl (fun p hp => by simp [movRegArgs?] at hp) rfl rfl
        (fun d' t g hs => ?_)
      regout_key
  | st m q S => exact hone _ _ _
  | ld m D q => exact hone _ _ _
  | leaF d q => exact hone _ _ _
  | ldx D B I =>
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, ↓reduceIte]
    regout_arm
  | stx d B I V =>
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, ↓reduceIte]
    regout_arm
  | simm d B V k =>
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, ↓reduceIte]
    regout_arm
  | mul D S =>
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, ↓reduceIte]
    regout_arm
  | cmpR c r =>
    refine regOut_nil_of_free fun ss gs hs => ?_
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, OwnedLprogTV.symStep, cmpArgs?, ↓reduceIte] at hs
    split at hs
    · obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj hs
      intro a ha
      cases ha
    · cases hs
  | cmpI c k =>
    refine regOut_nil_of_free fun ss gs hs => ?_
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, OwnedLprogTV.symStep, cmpArgs?, ↓reduceIte] at hs
    split at hs
    · obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj hs
      intro a ha
      cases ha
    · cases hs
  | cmpM c q =>
    refine regOut_nil_of_free fun ss gs hs => ?_
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, OwnedLprogTV.symStep, cmpArgs?, ↓reduceIte] at hs
    split at hs
    · obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj hs
      intro a ha
      cases ha
    · cases hs
  | mulxS H S =>
    refine regOut_nil_of_free fun ss gs hs => ?_
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      OwnedLprogTV.symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?,
      OwnedLprogTV.symWide, ↓reduceIte] at hs
    split at hs
    · obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj hs
      exact noBitWr_mulx _ _ _ _
    · cases hs
  | mulx L H S =>
    refine regOut_nil_of_free fun ss gs hs => ?_
    simp (config := { decide := true }) only [AArm.instr, JasminLsemAddrRun.normA,
      OwnedLprogTV.symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?,
      OwnedLprogTV.symWide, ↓reduceIte] at hs
    split at hs
    · obtain ⟨rfl, -⟩ := OwnedLprogTV.SOut.ok.inj hs
      exact noBitWr_mulx _ _ _ _
    · cases hs
  | zero B n =>
    refine regOut_nil_of_free fun ss gs hs => ?_
    simp (config := { decide := true }) [AArm.instr, JasminLsemAddrRun.normA,
      LprogAsmPrinter.untagCaret, OwnedLprogTV.symStep, cmpArgs?, movRegArgs?, flagCondCC?,
      carryArgs?, wideArgs?, OwnedLprogTV.symMem, OwnedLprogTV.symCast, OwnedLprogTV.symMC,
      OwnedLprogTV.symSh, OwnedLprogTV.symN, OwnedLprogTV.liftR, OwnedLprogTV.aluFl,
      JasminLsemCast.castStruct?, JasminLsemCast.movImmStruct?,
      JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
      JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
      JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?] at hs

/-- An instruction of a body of the class `printedAddrB`: the return at the last position, an
    instruction of `instrOKB` at every other position. -/
theorem narrowB_instr {body : Lcmd} (h : DecodePrintedCFG.printedAddrB body = true) {k : Nat}
    {i : Linstr} (hb : body[k]? = some i) :
    isRetB i.li_i = true ∨ instrOKB body (Params.ofBody body) i.li_i = true := by
  simp only [DecodePrintedCFG.printedAddrB, Bool.and_eq_true, Option.any_eq_true] at h
  obtain ⟨⟨⟨-, r, hr, hret⟩, hall⟩, -⟩ := h
  have hk := (List.getElem?_eq_some_iff.mp hb).1
  by_cases hl : k + 1 < body.length
  · have hm : i ∈ body.dropLast := List.mem_of_getElem? (i := k) (by
      rw [List.getElem?_dropLast, ite_eq_left (by omega)]
      exact hb)
    exact Or.inr (List.all_eq_true.mp hall i hm)
  · left
    have he : k = body.length - 1 := by omega
    rw [List.getLast?_eq_getElem?, ← he, hb] at hr
    obtain rfl := Option.some.inj hr
    exact hret

/-- Every instruction of a body of `printedAddrB` meets no classifier of the wide class before
    `classifyA`. -/
theorem noWideArm_of_narrowB {body : Lcmd} (h : DecodePrintedCFG.printedAddrB body = true)
    {k : Nat} {i : Linstr} (hb : body[k]? = some i) : NoWideArm i.li_i := by
  obtain ⟨ii, x⟩ := i
  rcases narrowB_instr h hb with h1 | h1
  · simp only at h1
    cases x <;> first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | simp [isRetB] at h1
  · simp only at h1 ⊢
    cases x with
    | Lopn ds o ss =>
      simp only [instrOKB] at h1
      cases hA : classifyA (.Lopn ds o ss) with
      | none => simp [hA] at h1
      | some a =>
        rw [hA] at h1
        have hw := noWideArm_of_ok (P := Params.ofBody body) h1
        rwa [classifyA_instr hA] at hw
    | Llabel kd l => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | Lcond c l => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | _ => simp [instrOKB] at h1

/-- A body of `printedAddrB` has no carry-out binding, so every position passes `carryPrevB`. -/
theorem carryPrevB_of_narrowB {body : Lcmd} (h : DecodePrintedCFG.printedAddrB body = true)
    (k : Nat) : carryPrevB body k = true := by
  unfold carryPrevB
  split
  · rename_i heq
    rename_i o a s c
    split_ifs with ho
    · have hC := (noWideArm_of_narrowB h heq).2.2.2.1
      simp [classifyC, ho] at hC
    · rfl
  · rfl

/-- A body of `printedAddrB` has no cast, so every position passes `castPosB`. -/
theorem castPosB_of_narrowB {body : Lcmd} (h : DecodePrintedCFG.printedAddrB body = true)
    (k : Nat) : castPosB body k = true := by
  unfold castPosB
  cases hb : body[k]? with
  | none => rfl
  | some i =>
    simp only [Option.all_some]
    rw [(noWideArm_of_narrowB h hb).1]

/-- **The narrow printed class is in the wide one**: `printedAddrB` implies `printedAddrWB`. -/
theorem printedAddrWB_of_printedAddrB {body : Lcmd}
    (h : DecodePrintedCFG.printedAddrB body = true) :
    DecodePrintedAddrW.printedAddrWB body = true := by
  have hc := h
  simp only [DecodePrintedCFG.printedAddrB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  simp only [DecodePrintedAddrW.printedAddrWB, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨h1, h2⟩, fun i hi => instrOKWB_of_instrOKB (h3 i hi)⟩, h4⟩,
    fun k _ => carryPrevB_of_narrowB h k⟩, fun k _ => castPosB_of_narrowB h k⟩

/-- The analysis without a join at the next instruction: one step of `oneBitStepAt0`. -/
theorem oneBitAt0_succ_at {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) :
    oneBitAt0 frame body (k + 1)
      = oneBitStepAt0 frame body k (oneBitAt0 frame body k) bi.li_i := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
  unfold oneBitAt0
  rw [List.take_add_one, hb, Option.toList_some, List.zipIdx_append, List.foldl_append,
    List.length_take, Nat.min_eq_left hk.le]
  simp

/-- An immediate move `MOV:64 d, #n` is a register instruction of the gate. -/
theorem icase_mov64Imm {frame : String → Option (BitVec 64)} {x : LinstrR} {d : String} {n : Nat}
    (hx : x = .Lopn [.reg d] "MOV:64" [.imm n]) : icase frame x = .reg := by
  subst hx
  simp (config := { decide := true }) [icase, slotMov?, slotCmp?, JasminLsemAddrRun.normA,
    LprogAsmPrinter.untagCaret]

/-- At a register instruction of the gate in a body of `printedAddrB`, `regOut` of the empty
    analysis is empty. -/
theorem regOut_nil_of_narrowB {frame : String → Option (BitVec 64)} {body : Lcmd}
    (hcls : DecodePrintedCFG.printedAddrB body = true) {k : Nat} {i : Linstr}
    (hb : body[k]? = some i) (hic : icase frame i.li_i = .reg) :
    regOut [] (JasminLsemAddrRun.normA i.li_i) = [] := by
  obtain ⟨ii, x⟩ := i
  simp only at hic ⊢
  rcases narrowB_instr hcls hb with h1 | h1
  · cases x <;> simp_all [icase, isRetB]
  · simp only at h1
    cases x with
    | Lopn ds o ss =>
      simp only [instrOKB] at h1
      cases hA : classifyA (.Lopn ds o ss) with
      | none => simp [hA] at h1
      | some a =>
        rw [hA] at h1
        rw [← classifyA_instr hA]
        exact regOut_nil_of_ok (P := Params.ofBody body) h1
    | Llabel kd l => simp [icase] at hic
    | Lcond c l => cases c <;> simp [icase] at hic
    | _ => simp [instrOKB] at h1

/-- One step of the analysis without a join at an instruction of a body of `printedAddrB` that
    passes `imgGateB`, from the empty analysis: the return and a gated arm add no name. -/
theorem oneBitStepAt0_nil_of_narrowB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hcls : DecodePrintedCFG.printedAddrB body = true)
    (hgate : imgGateB frame slotArr body = true) {k : Nat}
    {i : Linstr} (hb : body[k]? = some i) : oneBitStepAt0 frame body k [] i.li_i = [] := by
  obtain ⟨hK, hM, hS, hC, -⟩ := noWideArm_of_narrowB hcls hb
  have hstep : oneBitStep frame [] i.li_i = [] := by
    unfold oneBitStep
    cases hci : carryI? i.li_i with
    | some p =>
      obtain ⟨hi, d, a, s, c⟩ := p
      have hx := carryI?_eq hci
      rw [hx] at hC
      cases hi <;> simp [classifyC] at hC
    | none =>
      simp only
      cases hic : icase frame i.li_i
      case reg => simpa [hM] using regOut_nil_of_narrowB hcls hb hic
      all_goals simp [castOut, hK]
  unfold oneBitStepAt0
  cases hbs : bitStore? body k i.li_i with
  | none => exact hstep
  | some p =>
    exfalso
    obtain ⟨d, n⟩ := p
    have hx := (bitStore?_spec hbs).1
    have hg := hgate
    simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hg
    obtain ⟨⟨hall, hlast⟩, -⟩ := hg
    have hk := (List.getElem?_eq_some_iff.mp hb).1
    have hlt : k < body.length - 1 := by
      by_contra hc
      have he : k = body.length - 1 := by omega
      rw [List.getLast?_eq_getElem?, ← he, hb] at hlast
      simp [hx, isRetB] at hlast
    have hgk := hall k hlt
    rw [hb] at hgk
    simp only [Option.all_some] at hgk
    unfold instrGateB at hgk
    rw [icase_mov64Imm hx] at hgk
    simp [bitStoreB, hbs] at hgk

/-- **The width analysis of a body of the narrow gate is empty**: on a body of `printedAddrB`
    that passes `imgGateB`, `oneBitAt` has no name at any position. The analysis without a
    join `oneBitAt0` is empty by induction over the body, each step from the empty analysis
    adding no name (`oneBitStepAt0_nil_of_narrowB`); hence every seed of a label, the names of
    `oneBitAt0` at the branches to it, is empty, and `oneBitAt` is `oneBitAt0`
    (`oneBitAt_eq_oneBitAt0`). -/
theorem oneBitAt_nil_of_narrowB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hcls : DecodePrintedCFG.printedAddrB body = true)
    (hgate : imgGateB frame slotArr body = true) (k : Nat) :
    oneBitAt frame body k = [] := by
  have h0 : ∀ k, oneBitAt0 frame body k = [] := by
    intro k
    induction k with
    | zero => simp [oneBitAt0]
    | succ k ih =>
      cases hb : body[k]? with
      | none =>
        have hl := List.getElem?_eq_none_iff.mp hb
        have e : body.take (k + 1) = body.take k := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le hl]
        unfold oneBitAt0 at ih ⊢
        rw [e]
        exact ih
      | some i =>
        rw [oneBitAt0_succ_at hb, ih]
        exact oneBitStepAt0_nil_of_narrowB hcls hgate hb
  rw [oneBitAt_eq_oneBitAt0 (fun q _ _ _ _ _ => h0 q) k]
  exact h0 k

/-- On a body of `printedAddrB` that passes `imgGateB`, every observed name passes `retOutsB`:
    the width analysis at the last instruction is empty. -/
theorem retOutsB_of_narrowB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hcls : DecodePrintedCFG.printedAddrB body = true)
    (hgate : imgGateB frame slotArr body = true) (outs : List String) :
    retOutsB frame body outs = true := by
  simp [retOutsB, oneBitAt_nil_of_narrowB hcls hgate]

/-- `regGateB` is `regGateBW` at the empty analysis, up to the disjunct of a one-bit write. -/
theorem regGateBW_nil_of_regGateB {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : regGateB frame x = true) : regGateBW frame [] x = true := by
  simp only [regGateB, Bool.and_eq_true] at h
  simp only [regGateBW, Bool.and_eq_true]
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · rename_i ss gs heq
    rw [heq]
    simp only [List.all_eq_true, Bool.or_eq_true] at h2 ⊢
    intro r hr
    refine (h2 r hr).elim (fun hn => Or.inl (Or.inl hn)) fun hw => Or.inl (Or.inr ?_)
    unfold wid64B at hw
    unfold wid64WB
    split at hw <;> simp_all
  · cases h2

/-- The gate of an instruction of the narrow route at the empty analysis gives `gateAtW`, for an
    instruction of the class with no frame-array name. -/
theorem gateAtW_of_instrGateB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {x : LinstrR}
    (hw : NoWideArm x) (hfa : ∀ q ∈ JasminLsemExportRewrites.instrNames x, faB q = false)
    (hg : instrGateB frame slotArr body k x = true) :
    gateAtW frame slotArr body k [] x = true := by
  obtain ⟨-, hM, -, hC, -⟩ := hw
  have hci : carryI? x = none := by
    cases hc : carryI? x with
    | none => rfl
    | some p =>
      obtain ⟨hi, d, a, s, c⟩ := p
      rw [carryI?_eq hc] at hC
      cases hi <;> simp [classifyC] at hC
  have hr : readOkB (gateReadSet frame [] x) x = true := by
    have : gateReadSet frame [] x = [] := by
      unfold gateReadSet
      split <;> simp
    rw [this]
    simp [readOkB]
  unfold gateAtW
  rw [hci, hr]
  simp only [Bool.true_or, Bool.and_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun q hq => by simp [hfa q hq], ?_⟩
  unfold instrGateB at hg
  cases hic : icase frame x with
  | other => rw [hic] at hg; cases hg
  | label => rfl
  | cond cc l =>
    rw [hic] at hg
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hg
    obtain ⟨hp, q, hq⟩ := hg
    simp [hq, Option.isSome_iff_exists.mpr hp]
  | ldx d b idx => rw [hic] at hg; exact hg
  | stx d b idx v => rw [hic] at hg; exact hg
  | sload d q =>
    rw [hic] at hg
    simp only [Bool.and_eq_true] at hg
    simp [hg.1]
  | sstore q S =>
    rw [hic] at hg
    simp only [Bool.and_eq_true] at hg
    simp [hg.1]
  | scmp d y q =>
    rw [hic] at hg
    simp only [Bool.and_eq_true] at hg
    exact hg.1
  | zarr b n w => rw [hic] at hg; exact hg
  | simm d b v j => rw [hic] at hg; exact hg
  | reg =>
    rw [hic] at hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨⟨h1, -⟩, h3⟩ := hg
    have hbs : bitStore? body k x = none := by
      simpa [bitStoreB] using h3
    simp only [hM, hbs, Bool.or_eq_true, Bool.and_eq_true]
    refine Or.inr ⟨regGateBW_nil_of_regGateB h1, ?_⟩
    unfold cmovCondOkB
    split <;> simp

/-- **The narrow image gate is in the wide one**: a body of `printedAddrB` that passes
    `imgGateB` and has no frame-array name passes `imgGateBW`. The width analysis is empty there
    (`oneBitAt_nil_of_narrowB`), and each arm of `gateAtW` at the empty analysis reduces to that
    of `instrGateB`. The hypothesis `hfa` is needed at the destination of an indexed store, which
    `instrGateB` leaves free and the first conjunct of `gateAtW` does not. -/
theorem imgGateBW_of_imgGateB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hcls : DecodePrintedCFG.printedAddrB body = true)
    (hgate : imgGateB frame slotArr body = true)
    (hfa : ∀ i ∈ body, ∀ q ∈ JasminLsemExportRewrites.instrNames i.li_i, faB q = false) :
    imgGateBW frame slotArr body = true := by
  have hg := hgate
  simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨fun k hk => ?_, h2⟩, h3⟩
  have := h1 k hk
  cases hb : body[k]? with
  | none => rfl
  | some i =>
    rw [hb] at this
    simp only [Option.all_some] at this ⊢
    rw [instrGateBW, oneBitAt_nil_of_narrowB hcls hgate]
    exact gateAtW_of_instrGateB (noWideArm_of_narrowB hcls hb)
      (hfa i (List.mem_of_getElem? hb)) this

end Narrow

/-! ## 10. One-pass evaluation of the class and the gate -/

section OnePass

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (condPrevBA condPrevBA_toArray)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (carryPrevBA carryPrevBA_toArray carryPrevB_eq_with castPosBA castPosBA_toArray narrowTable)

/-- `printedAddrCWB` with the body parameters computed once, the position checks read off the
    array of the body and the cast width analyses read off `narrowTable`. -/
def printedAddrCWBImpl (G : Nat) (body : Lcmd) : Bool :=
  let P := Params.ofBody body
  let a := body.toArray
  let nt := narrowTable body
  relocFrameB body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i => remoteCallB i.li_i || instrOKWB body P i.li_i)
    && (List.range a.size).all (fun k =>
      condPrevBA a k && carryPrevBA P a k && castPosBA a nt k)
    && (callFreeB body || frameNonnegB body G)

/-- The class `printedAddrCWB` is evaluated as `printedAddrCWBImpl`. -/
@[csimp] theorem printedAddrCWB_eq_impl : @printedAddrCWB = @printedAddrCWBImpl := by
  funext G body
  simp only [printedAddrCWB, printedAddrCWBImpl, List.size_toArray, carryPrevBA_toArray,
    castPosBA_toArray, carryPrevB_eq_with, condPrevBA_toArray]

/-- The width analysis at each position of a body and one past its end, as an array indexed by
    the position: the first components of the prefix folds of `oneBitStepF` over the body,
    which carry the table of forward branches. -/
def oneBitTab (frame : String → Option (BitVec 64)) (body : Lcmd) : Array (List String) :=
  ((body.zipIdx.scanl (fun S p => oneBitStepF frame body p.2 S p.1.li_i) ([], [])).map
    Prod.fst).toArray

/-- Entry `k` of `oneBitTab`, for `k ≤ body.length`, is the analysis `oneBitAt frame body k`. -/
theorem oneBitTab_getD (frame : String → Option (BitVec 64)) (body : Lcmd) {k : Nat}
    (hk : k ≤ body.length) : (oneBitTab frame body).getD k [] = oneBitAt frame body k := by
  have hz : body.zipIdx.take k = (body.take k).zipIdx := by
    apply List.ext_getElem?
    intro i
    grind
  simp only [oneBitTab, oneBitAt, oneBitSt, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, Option.map_some, List.getElem?_scanl, List.length_zipIdx, hk, ite_true, hz, Option.getD_some]

/-- The instruction gate of `imgGateCBW` at position `k`, read off the table `tab` of the width
    analysis. -/
def gateAtTab (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (tab : Array (List String)) (k : Nat) (x : LinstrR) : Bool :=
  remoteCallB x
    || (cidxArmAt frame slotArr body k (tab.getD (k - 3) []) (tab.getD k []) x
        && srcNoCellB x)
    || gateAtW frame slotArr body k (tab.getD k []) x

/-- At `oneBitTab`, `gateAtTab` is the instruction gate of `imgGateCBW`. -/
theorem gateAtTab_oneBitTab (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) {k : Nat} (hk : k ≤ body.length)
    (x : LinstrR) :
    gateAtTab frame slotArr body (oneBitTab frame body) k x
      = (remoteCallB x || cidxArmCW frame slotArr body k x
          || instrGateBW frame slotArr body k x) := by
  simp only [gateAtTab, oneBitTab_getD frame body hk,
    oneBitTab_getD frame body (show k - 3 ≤ body.length by omega), cidxArmCW, cidxArmB,
    instrGateBW]

/-- `imgGateCBW` with the frame map tabulated over the names of the body and the width analysis
    read off `oneBitTab`. -/
def imgGateCBWImpl (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  let fr := tabFrame frame ((ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q))
  let a := body.toArray
  let tab := oneBitTab fr body
  (List.range (body.length - 1)).all (fun k => (a[k]?).all fun i =>
      gateAtTab fr slotArr body tab k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- The gate `imgGateCBW` is evaluated as `imgGateCBWImpl`. -/
@[csimp] theorem imgGateCBW_eq_impl : @imgGateCBW = @imgGateCBWImpl := by
  funext frame slotArr body
  have hall : (List.range (body.length - 1)).all (fun k => (body[k]?).all fun i =>
        gateAtTab frame slotArr body (oneBitTab frame body) k i.li_i)
      = (List.range (body.length - 1)).all (fun k => (body[k]?).all fun i =>
        remoteCallB i.li_i || cidxArmCW frame slotArr body k i.li_i
          || instrGateBW frame slotArr body k i.li_i) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun k hk => ?_
    have hle : k ≤ body.length := by
      have := List.mem_range.mp hk
      omega
    simp only [gateAtTab_oneBitTab frame slotArr body hle]
  simp only [imgGateCBW, gateCW, ← Bool.or_assoc, imgGateCBWImpl, tabFrame_eq,
    List.getElem?_toArray, hall]

/-- The instruction gate `ImageAddrCidx.gateCW` at position `k`, read off the table `tab` of the
    width analysis. -/
def gateCWTab (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (tab : Array (List String)) (k : Nat) (x : LinstrR) : Bool :=
  (cidxArmAt frame slotArr body k (tab.getD (k - 3) []) (tab.getD k []) x && srcNoCellB x)
    || gateAtW frame slotArr body k (tab.getD k []) x

/-- At `oneBitTab`, `gateCWTab` is `ImageAddrCidx.gateCW`. -/
theorem gateCWTab_oneBitTab (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) {k : Nat} (hk : k ≤ body.length)
    (x : LinstrR) :
    gateCWTab frame slotArr body (oneBitTab frame body) k x = gateCW frame slotArr body k x := by
  simp only [gateCWTab, gateCW, oneBitTab_getD frame body hk,
    oneBitTab_getD frame body (show k - 3 ≤ body.length by omega), cidxArmCW, cidxArmB,
    instrGateBW]

/-- `ImageAddrCidx.imgGateCW` with the frame map tabulated over the names of the body and the
    width analysis read off `oneBitTab`. -/
def imgGateCWImpl (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  let fr := tabFrame frame ((ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q))
  let a := body.toArray
  let tab := oneBitTab fr body
  (List.range (body.length - 1)).all (fun k => (a[k]?).all fun i =>
      gateCWTab fr slotArr body tab k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- The gate `ImageAddrCidx.imgGateCW` is evaluated as `imgGateCWImpl`. -/
@[csimp] theorem imgGateCW_eq_impl : @imgGateCW = @imgGateCWImpl := by
  funext frame slotArr body
  have hall : (List.range (body.length - 1)).all (fun k => (body[k]?).all fun i =>
        gateCWTab frame slotArr body (oneBitTab frame body) k i.li_i)
      = (List.range (body.length - 1)).all (fun k => (body[k]?).all fun i =>
        gateCW frame slotArr body k i.li_i) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun k hk => ?_
    have hle : k ≤ body.length := by
      have := List.mem_range.mp hk
      omega
    simp only [gateCWTab_oneBitTab frame slotArr body hle]
  simp only [imgGateCW, imgGateCWImpl, tabFrame_eq, List.getElem?_toArray, hall]

/-- `bitsDeadB` with the frame map tabulated over the names of the body and the width analysis
    read off `oneBitTab`. -/
def bitsDeadBImpl (frame : String → Option (BitVec 64)) (D : DeadTab) (body : Lcmd) : Bool :=
  let fr := tabFrame frame ((ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q))
  let tab := oneBitTab fr body
  ((body.length - 1) :: callPos body).all fun p => (tab.getD p []).all (D.dead p).contains

/-- The check `bitsDeadB` is evaluated as `bitsDeadBImpl`. -/
@[csimp] theorem bitsDeadB_eq_impl : @bitsDeadB = @bitsDeadBImpl := by
  funext frame D body
  simp only [bitsDeadB, bitsDeadBImpl, tabFrame_eq]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun p hp => ?_
  have hle : p ≤ body.length := by
    rcases List.mem_cons.mp hp with rfl | h
    · omega
    · have := (mem_callPos.mp h).1
      omega
  rw [oneBitTab_getD frame body hle]

end OnePass

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
