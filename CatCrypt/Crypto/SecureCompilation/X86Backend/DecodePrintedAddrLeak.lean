/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of the decoded bytes of a printed body

`DecodePrintedCFG.printedAddr_sim` matches a terminating run of the address machine on a
printed body in `printedAddrB` by a halting run of `aMachine` on the decoded function bytes.
This module adds the leakage: the run with leakage `DecodedCT.RunL` of the decoded bytes, under
the regime `doitm`, has the trace of the address machine (`ImageAddrLeakPhys.runALeak`) with
the red-zone accesses of the widening multiply added, and constant time of the address machine
gives constant time of the decoded bytes.

## The events of an arm

The decoded instructions of an arm `a` of `DecodePrintedAddr.AArm` emit, under `doitm`, no
`vt` event: every machine instruction of an arm is in the DOIT class. Their memory events are
the events `instrLeakA` of the arm on the address machine followed by `redLeak rsp a`: the
widening multiply with coincident destinations stores and reloads its scratch register at the
red-zone word `redW rsp`, two events at an address fixed by the stack register; every other arm
adds nothing. `runALeakX X` is the address machine with the events `X pc` added after each step
from program counter `pc`; `redStep rsp body` is `redLeak` of the arm at each position.

## Constant time

The trace of `runALeakX X` is not a function of the trace of `runALeak` alone. On a covered
body the number of events of a succeeding step is a function of the program counter
(`StepLenDet`, `stepLenDet_of`), and the program counter after a step is a function of the
program counter and the events of the step (`stepA_lpc_det`), so two terminating runs from one
program counter with equal traces visit one sequence of program counters and have equal traces
with any events `X` added (`runALeakX_transfer`).

## Main results

* `runL_det`: a run with leakage of a decoded program is deterministic in its trace and final
  state.
* `runL_ops`: a segment of `op`s runs with the leakage of the block.
* `AArm.leak`: the leakage of the decoded instructions of an arm is `instrLeakA` of the arm
  followed by `redLeak`.
* `run_simL`, `printedAddr_simL`: the traced simulation; every terminating safe run of the
  address machine on a body in `printedAddrB` with trace `ℓ` of `runALeakX (redStep rsp body)`
  is matched by a run with leakage `ℓ` of the decoded bytes.
* `runALeakX_transfer`, `stepLenDet_of`: equal traces of the address machine give equal traces
  with added events.
* `bytes_trace_eq`, `bytes_ct`: constant time of the address machine at the frame below `rsp`
  gives constant time of the decoded bytes between machine states with one frame address that
  correspond at entry to related address states (`BytePub`).
* `instrLeakA_congr`, `runALeak_congr`, `aRun_frameIn`: the traced address machine reads the
  frame only at the names of the body.
* `image_bytes_ct`: for a body in `printedAddrB` without a conditional branch that passes the
  gates of the image simulation, constant time of the image (`MemFCT`) gives constant time of
  the decoded function bytes (`ImgBytePub`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL blockLeakA opLeak resolveEv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (instrLeak MLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel DoitRegime X86Mnem)

/-! ## 1. Runs with leakage of a decoded program -/

/-- **Determinism of the run with leakage**: two halting runs of one program from one index
    and one state, under any side conditions, have one trace and one final state. -/
theorem runL_det {r : DoitRegime} {ok ok' : AState → JInstr 64 → Prop} {prog : List RInstr}
    {pc : Nat} {sa : AState} {t : List CTLeak} {sa₁ : AState}
    (h₁ : RunL r ok prog pc sa t sa₁) :
    ∀ {t' : List CTLeak} {sa₂ : AState}, RunL r ok' prog pc sa t' sa₂ → t = t' ∧ sa₁ = sa₂ := by
  induction h₁ with
  | ret h =>
    intro t' sa₂ h₂
    cases h₂ with
    | ret _ => exact ⟨rfl, rfl⟩
    | op h' _ _ => rw [h] at h'; cases h'
    | jcc h' _ _ => rw [h] at h'; cases h'
    | stack h' hops _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | call h' _ _ _ _ => rw [h] at h'; cases h'
  | op h _ _ ih =>
    intro t' sa₂ h₂
    cases h₂ with
    | ret h' => rw [h] at h'; cases h'
    | op h' _ hr' =>
      rw [h] at h'; cases h'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩
    | jcc h' _ _ => rw [h] at h'; cases h'
    | stack h' hops _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | call h' _ _ _ _ => rw [h] at h'; cases h'
  | jcc h hc _ ih =>
    intro t' sa₂ h₂
    cases h₂ with
    | ret h' => rw [h] at h'; cases h'
    | op h' _ _ => rw [h] at h'; cases h'
    | jcc h' hc' hr' =>
      rw [h] at h'; cases h'
      rw [hc] at hc'; cases hc'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩
    | stack h' hops _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | call h' _ _ _ _ => rw [h] at h'; cases h'
  | stack h hops _ _ ih =>
    intro t' sa₂ h₂
    cases h₂ with
    | ret h' => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | op h' _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | jcc h' _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | stack h' hops' _ hr' =>
      rw [h] at h'; cases h'
      rw [hops] at hops'; cases hops'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩
    | call h' _ _ _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
  | call h _ _ _ _ ihc ihr =>
    intro t' sa₂ h₂
    cases h₂ with
    | ret h' => rw [h] at h'; cases h'
    | op h' _ _ => rw [h] at h'; cases h'
    | jcc h' _ _ => rw [h] at h'; cases h'
    | stack h' hops _ _ => rw [h] at h'; cases h'; simp [RInstr.stackOps?] at hops
    | call h' _ hc' _ hr' =>
      rw [h] at h'; cases h'
      obtain ⟨rfl, rfl⟩ := ihc hc'
      obtain ⟨rfl, rfl⟩ := ihr hr'
      exact ⟨rfl, rfl⟩

/-- A segment of `op`s of a program runs with the leakage of the block. -/
theorem runL_ops {r : DoitRegime} {prog : List RInstr} (B : List RInstr) :
    ∀ (ops : List (JInstr 64)) (A : List RInstr) (sa : AState) {t : List CTLeak} {sa' : AState},
      prog = A ++ ops.map RInstr.op ++ B →
      RunL r (fun _ _ => True) prog (A.length + ops.length) (runBlockA sa ops) t sa' →
      RunL r (fun _ _ => True) prog A.length sa (blockLeakA r sa ops ++ t) sa' := by
  intro ops
  induction ops with
  | nil =>
    intro A sa t sa' _ h
    simpa [blockLeakA] using h
  | cons i is ih =>
    intro A sa t sa' hp h
    have hp' : prog = (A ++ [RInstr.op i]) ++ is.map RInstr.op ++ B := by simp [hp]
    have h' : RunL r (fun _ _ => True) prog ((A ++ [RInstr.op i]).length + is.length)
        (runBlockA (evalInstrA sa i) is) t sa' := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h
    have hr := ih (A ++ [RInstr.op i]) (evalInstrA sa i) hp' h'
    have hi : prog[A.length]? = some (.op i) := by simp [hp]
    have := RunL.op (r := r) (ok := fun _ _ => True) hi trivial (by simpa using hr)
    simpa [blockLeakA, List.append_assoc] using this

/-! ## 2. The leakage of one arm -/

/-- The events of the decoded instructions of an arm beyond those of the address machine: the
    widening multiply with coincident destinations saves and restores its scratch register at
    the red-zone word, two accesses at `redW rsp`. -/
def redLeak (rsp : BitVec 64) : AArm → List CTLeak
  | .mulxS _ _ => [evA (redW rsp), evA (redW rsp)]
  | _ => []

/-- A register instruction that moves no frame word, compares against no frame word and
    accesses no cell, carry chain, immediate slot or slot select has no events on the address
    machine. -/
theorem instrLeakA_nil {frame : String → Option (BitVec 64)} {x : LinstrR} (tag : Option Nat)
    (hmov : ∀ d y, slotMov? x = some (d, y) → frame d = none ∧ frame y = none)
    (hcmp : ∀ d y q, slotCmp? x = some (d, y, q) → frame q = none)
    (hcell : cellA? x = none) (hcar : slotCarry? frame x = none)
    (himm : slotImm? frame x = none) (hsel : slotCmov? frame x = none) (s : LstateA) :
    instrLeakA frame (x, .reg tag) s = [] := by
  cases hm : slotMov? x with
  | some p =>
    obtain ⟨d, y⟩ := p
    obtain ⟨hd, hy⟩ := hmov d y hm
    simp [instrLeakA, hm, hd, hy]
  | none =>
    cases hk : slotCmp? x with
    | some p =>
      obtain ⟨d, y, q⟩ := p
      simp [instrLeakA, hm, hk, hcmp d y q hk]
    | none => simp [instrLeakA, hm, hk, hcell, hcar, himm, hsel]

/-- **The leakage of one arm.** From the correspondence, the leakage of the decoded
    instructions of an arm whose conditions hold, under the regime `doitm`, is its leakage on
    the address machine followed by the red-zone accesses `redLeak`. -/
theorem AArm.leak (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true) (sa : AState)
    (s : LstateA) (hc : ACorr rsp sa s) :
    blockLeakA .doitm sa (a.js P) = instrLeakA (frameP P rsp) a.li s ++ redLeak rsp a := by
  cases a with
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hr, h⟩, -⟩ := h
    obtain ⟨-, hslot, -⟩ := regArm_facts hr h
    have hR : instrLeakA (frameP P rsp) (a.instr, .reg none) s = [] :=
      instrLeakA_nil none
        (fun d y hs => ⟨frameP_gp (hslot d y hs).1, frameP_gp (hslot d y hs).2⟩)
        (fun d y q hk => frameP_gp (regArm_slotCmp h hk)) (regArm_cell hr h)
        (by cases a <;> simp [Arm.instr, slotCarry?]) (regArm_slotImm rsp h)
        (by cases a <;> simp [Arm.instr, slotCmov?]) s
    simp only [AArm.li, AArm.instr, redLeak, List.append_nil]
    rw [hR]
    cases a with
    | alu m D S =>
      simp only [AArm.js, AArm.pieces, Arm.pieces]
      split <;> rename_i hop
      · rename_i op mk
        unfold aluArm at hop
        split at hop <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hop <;>
          obtain ⟨rfl, rfl⟩ := hop <;>
          simp [blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
            X86Mnem.timing]
      · rfl
    | aluI m D v =>
      simp only [AArm.js, AArm.pieces, Arm.pieces]
      split <;> rename_i hop
      · rename_i op mk
        unfold aluArm at hop
        split at hop <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hop <;>
          obtain ⟨rfl, rfl⟩ := hop <;>
          simp [blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
            X86Mnem.timing]
      · rfl
    | shr m D S =>
      by_cases hDS : D = S <;> by_cases hl : tagShl m = true <;>
        simp [AArm.js, AArm.pieces, Arm.pieces, tagShMk, hDS, hl, blockLeakA, opLeak, instrLeak,
          JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]
    | shl0 m D S =>
      by_cases hDS : D = S <;>
        simp [AArm.js, AArm.pieces, Arm.pieces, hDS, blockLeakA, opLeak, instrLeak,
          JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]
    | shI m D k =>
      by_cases hm : m = "SHL:64" <;>
        simp [AArm.js, AArm.pieces, Arm.pieces, shIMk, *, blockLeakA, opLeak, instrLeak,
          JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]
    | store => simp [regArmB] at hr
    | load => simp [regArmB] at hr
    | _ =>
      simp [AArm.js, AArm.pieces, Arm.pieces, blockLeakA, opLeak, instrLeak,
        JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]
  | st m q S =>
    simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hS, -⟩, hsome⟩, -⟩, hm⟩ := h
    have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
      simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm; exact hm.symm
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    rcases hm' with rfl | rfl <;>
      simp [AArm.js, AArm.pieces, Arm.pieces, hso, blockLeakA, opLeak, instrLeak, resolveEv,
        JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, AArm.instr,
        instrLeakA, slotMov?, frameP, (gpFacts hS).off, hoff, hc.sp, evA, redLeak,
        cellParts?_of_spillOff hsome, cellParts?_gp hS]
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hD, -⟩, hsome⟩, -⟩, -⟩, hm⟩ := h
    have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
      simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm; exact hm.symm
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    rcases hm' with rfl | rfl <;>
      simp [AArm.js, AArm.pieces, Arm.pieces, hso, blockLeakA, opLeak, instrLeak, resolveEv,
        JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, AArm.instr,
        instrLeakA, slotMov?, frameP, hoff, hc.sp, evA, redLeak,
        cellParts?_of_spillOff hsome, cellParts?_gp hD]
  | cmpR c r =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    simp [AArm.js, AArm.pieces, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, AArm.instr, instrLeakA, slotMov?,
      slotCmp?, frameP_gp h.2, redLeak]
  | cmpI c k =>
    simp [AArm.js, AArm.pieces, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, AArm.instr, instrLeakA, slotMov?,
      slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?, redLeak]
  | cmpM c q =>
    simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hsome⟩, -⟩, -⟩ := h
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    simp [AArm.js, AArm.pieces, hso, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, AArm.instr, instrLeakA, slotMov?,
      slotCmp?, frameP, hoff, hc.sp, evA, redLeak]
  | ldx D B I =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨-, hB⟩, hI⟩, -⟩ := h
    rw [show (AArm.ldx D B I).li = (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8], .load 64 0)
      from rfl, instrLeakA_ldx _ D B I 8 64 0 (hc.regs B hB) (hc.regs I hI)]
    simp [AArm.js, AArm.pieces, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, evA, redLeak, AState.view, JState.get]
    omega
  | stx d B I V =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hB, hI⟩, -⟩, -⟩ := h
    rw [show (AArm.stx d B I V).li = (.Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V],
      .store 64 0) from rfl, instrLeakA_stx _ d B I V 8 64 0 (hc.regs B hB) (hc.regs I hI)]
    simp [AArm.js, AArm.pieces, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, evA, redLeak, AState.view, JState.get]
    omega
  | mul D S =>
    simp [AArm.js, AArm.pieces, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, AArm.instr, instrLeakA, slotMov?,
      slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?, redLeak]
  | mulxS H S =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨hH, -⟩ := h
    obtain ⟨hlt, -, -, -, hne4⟩ := mulxSameScratch_spec (gpNumU H) (gpNumU S)
    set R := SailX86Decoder.regName (scrOf H S) with hR
    have hRsp : R ≠ "%rsp" := by
      rw [show "%rsp" = SailX86Decoder.regName 4 from rfl]
      exact regName_ne_of_ne hlt (by decide) hne4
    have hHsp : phys H ≠ "%rsp" := (gpFacts hH).physNe
    have hjs : (AArm.mulxS H S).js P = [.storeMem "%rsp" cmovRedZone (.reg R),
        .mulx (phys H) R (.reg "%rdx") (.reg (phys S)), .loadMem R "%rsp" cmovRedZone] := rfl
    obtain ⟨r1, -⟩ := evalInstrA_storeMem_eq sa "%rsp" R cmovRedZone
    set sa1 := evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R))
    set sa2 := evalInstrA sa1 (.mulx (phys H) R (.reg "%rdx") (.reg (phys S)))
    have hsp2 : sa2.regs "%rsp" = rsp := by
      rw [DecodedLsemLoop.evalInstrA_mulx_regs, r1, if_neg hHsp.symm, if_neg hRsp.symm, hc.sp]
    have hsp1 : sa1.regs "%rsp" = rsp := by rw [r1, hc.sp]
    have hA : instrLeakA (frameP P rsp) (AArm.mulxS H S).li s = [] := by
      simp [AArm.li, instrLeakA, slotMov?, slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?]
    rw [hjs, hA]
    simp only [blockLeakA, opLeak, instrLeak, resolveEv, redLeak, List.map, List.nil_append,
      List.append_nil, List.cons_append]
    rw [show evalInstrA sa1 (.mulx (phys H) R (.reg "%rdx") (.reg (phys S))) = sa2 from rfl,
      hsp2]
    rw [hc.sp]
    simp only [JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, Bool.false_eq_true,
      if_false, List.nil_append]
    rfl
  | mulx L H S =>
    simp [AArm.js, AArm.pieces, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, AArm.li, instrLeakA, slotMov?,
      slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?, redLeak]

/-! ## 3. The address machine with added events -/

/-- **The address machine with the events `X` added**: the recursion of `runALeak`, each step
    from a state at program counter `pc` emitting `stepLeakA` followed by `X pc`. -/
def runALeakX (X : Nat → List CTLeak) (frame : String → Option (BitVec 64)) (c : Lcmd) :
    Nat → LstateA → Bool → Option ((LstateA × Bool) × List CTLeak)
  | 0, s, zf => if haltedA c s then some ((s, zf), []) else none
  | fuel + 1, s, zf =>
      if haltedA c s then some ((s, zf), [])
      else (stepA frame c s zf).bind fun bz =>
        (runALeakX X frame c fuel bz.1 bz.2).map fun r =>
          (r.1, stepLeakA frame c s zf ++ X s.reg.lpc ++ r.2)

theorem runALeakX_halt (X : Nat → List CTLeak) (frame : String → Option (BitVec 64))
    (c : Lcmd) (fuel : Nat) (s : LstateA) (zf : Bool) (h : haltedA c s = true) :
    runALeakX X frame c fuel s zf = some ((s, zf), []) := by
  cases fuel <;> simp [runALeakX, h]

theorem runALeakX_step (X : Nat → List CTLeak) (frame : String → Option (BitVec 64))
    (c : Lcmd) (fuel : Nat) (s : LstateA) (zf : Bool) (h : haltedA c s = false) :
    runALeakX X frame c (fuel + 1) s zf
      = (stepA frame c s zf).bind fun bz =>
          (runALeakX X frame c fuel bz.1 bz.2).map fun r =>
            (r.1, stepLeakA frame c s zf ++ X s.reg.lpc ++ r.2) := by
  simp [runALeakX, h]

/-- With no added events the run is `runALeak`. -/
theorem runALeakX_nil (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      runALeakX (fun _ => []) frame c fuel s zf = runALeak frame c fuel s zf := by
  intro fuel
  induction fuel with
  | zero => intro s zf; rfl
  | succ n ih =>
    intro s zf
    cases hh : haltedA c s
    · rw [runALeakX_step _ _ _ _ _ _ hh, runALeak_step _ _ _ _ _ hh]
      simp only [ih, List.append_nil]
    · rw [runALeakX_halt _ _ _ _ _ _ hh, runALeak_halt _ _ _ _ _ hh]

/-- The state component of the run with added events is `runA`. -/
theorem runALeakX_fst (X : Nat → List CTLeak) (frame : String → Option (BitVec 64))
    (c : Lcmd) : ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      (runALeakX X frame c fuel s zf).map Prod.fst = runA frame c fuel s zf := by
  intro fuel
  induction fuel with
  | zero =>
    intro s zf
    cases hh : haltedA c s <;> simp [runALeakX, runA, hh]
  | succ n ih =>
    intro s zf
    cases hh : haltedA c s
    · rw [runALeakX_step X frame c n s zf hh, runA_step frame c n s zf hh]
      cases stepA frame c s zf with
      | none => rfl
      | some bz =>
        simp only [Option.bind_some]
        rw [← ih bz.1 bz.2, Option.map_map]
        rfl
    · rw [runALeakX_halt X frame c _ s zf hh, runA_halt frame c _ s zf hh]
      rfl

/-- A terminating run of the address machine has a trace with added events. -/
theorem runALeakX_of_runA (X : Nat → List CTLeak) {frame : String → Option (BitVec 64)}
    {c : Lcmd} {fuel : Nat} {s : LstateA} {zf : Bool} {t : LstateA × Bool}
    (h : runA frame c fuel s zf = some t) : ∃ ℓ, runALeakX X frame c fuel s zf = some (t, ℓ) := by
  rw [← runALeakX_fst X] at h
  obtain ⟨⟨t', ℓ⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ℓ, h1⟩

/-- The red-zone events of the instruction at position `pc` of `body`: `redLeak` of its arm. -/
def redStep (rsp : BitVec 64) (body : Lcmd) (pc : Nat) : List CTLeak :=
  match body[pc]? with
  | some i =>
      match classifyA i.li_i with
      | some a => redLeak rsp a
      | none => []
  | none => []

/-! ## 4. The traced simulation -/

/-- The machine branch on the zero flag: its condition evaluates to the agreement of the flag
    with the polarity. -/
theorem jcc_pol (sa : AState) {cc : String} {pol : Bool} (hpol : condPol cc = some pol) :
    ∃ c, condtOfNibble (ccNibble cc) = some c
      ∧ sa.view.condB c = (sa.flags.zf.getD false == pol) := by
  have hf : sa.view.flagB (·.zf) = sa.flags.zf.getD false := rfl
  rcases condPol_spec hpol with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
  · rw [hn]
    refine ⟨_, condtOfNibble_four, ?_⟩
    rw [condB_e, hf]
    cases sa.flags.zf.getD false <;> rfl
  · rw [hn]
    refine ⟨_, condtOfNibble_five, ?_⟩
    rw [condB_ne, hf]
    cases sa.flags.zf.getD false <;> rfl

/-- **The run on both machines, with leakage.** From states related by `ACorr` at instruction
    `k` of a covered body, with the machine zero flag equal to the flag at a conditional
    branch, every terminating run of the address machine whose indexed loads avoid the
    red-zone word, with trace `ℓ` of `runALeakX (redStep rsp body)`, is matched by a run with
    leakage `ℓ` of the decoded program from the index of `k`, under the regime `doitm`. -/
theorem run_simL {body : Lcmd} {shs : List DShape} (hF : BodyFacts body shs) (rsp : BitVec 64)
    (a b : JInstr 64) (hb : ∀ sa, opLeak .doitm sa b = []) :
    ∀ (fuel k : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool)
      (ℓ : List CTLeak),
      s.reg.lpc = k → (hk : k < body.length) → ACorr rsp sa s →
      (isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf) →
      runALeakX (redStep rsp body) (frameP (Params.ofBody body) rsp) body fuel s zf
        = some (t, ℓ) →
      RunSafe (frameP (Params.ofBody body) rsp) body (LoadSafeAt rsp body) fuel s zf →
      ∃ sa', RunL .doitm (fun _ _ => True)
        (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])) (posOf shs k) sa ℓ sa' := by
  set P := Params.ofBody body with hP
  set frame := frameP P rsp
  set prog : List RInstr := .op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])
  obtain ⟨hl, hsh⟩ := shapesOf_spec P body shs hF.shapes
  have hskip : shs[shs.length - 1]'(by have := hF.pos; omega) = .one .skip := by
    have hsk := hsh (body.length - 1) (by have := hF.pos; omega) (by have := hF.pos; omega)
    have hlast := hF.last
    revert hsk hlast
    rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
    intro hsk hlast
    simp only at hlast hsk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hsk
    simp only [hl] at hsk ⊢
    exact hsk.symm
  obtain ⟨he1, he2⟩ := prog_end body shs a b (by have := hF.pos; omega) hskip
  rw [hl] at he1 he2
  -- the halt at the return
  have hhalt : ∀ (fuel : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool)
      (ℓ : List CTLeak), s.reg.lpc = body.length - 1 →
      runALeakX (redStep rsp body) frame body fuel s zf = some (t, ℓ) →
      ∃ sa', RunL .doitm (fun _ _ => True) prog (posOf shs (body.length - 1)) sa ℓ sa' := by
    intro fuel sa s zf t ℓ hpc hrun
    have hh : haltedA body s = true := by
      unfold haltedA
      rw [hpc, List.getElem?_eq_getElem (by have := hF.pos; omega)]
      have := hF.last
      revert this
      rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
      intro h
      simp only at h
      subst h
      rfl
    rw [runALeakX_halt _ _ _ _ _ _ hh] at hrun
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrun)
    have := RunL.op (r := .doitm) (ok := fun _ _ => True) (sa := sa) he1 trivial (.ret he2)
    rw [hb, List.append_nil] at this
    exact ⟨_, this⟩
  intro fuel
  induction fuel with
  | zero =>
    intro k sa s zf t ℓ hpc hk _ _ hrun _
    by_cases hkn : k + 1 < body.length
    · simp [runALeakX, haltedA_eq_false hF hpc hkn] at hrun
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt 0 sa s zf t ℓ hpc hrun
  | succ f ih =>
    intro k sa s zf t ℓ hpc hk hc hz hrun hsafe
    by_cases hkn : k + 1 < body.length
    swap
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt (f + 1) sa s zf t ℓ hpc hrun
    rw [runALeakX_step _ _ _ _ _ _ (haltedA_eq_false hF hpc hkn)] at hrun
    have hok := hF.instr k hkn
    have hget : body[s.reg.lpc]? = some (body[k]'hk) := by
      rw [hpc]; exact List.getElem?_eq_getElem hk
    have hks : k < shs.length := by omega
    have hshk := hsh k hk hks
    obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
    rcases hbk : body[k] with ⟨ii, li⟩
    rw [hbk] at hok hget hshk hz
    simp only at hok hshk hz
    cases li with
    | Lopn ds o ss =>
      simp only [instrOKB] at hok
      split at hok
      · rename_i ar hcl
        have hia := classifyA_instr hcl
        have hli := AArm.li_eq hok
        have hsafeA : ar.LoadSafe rsp s := by
          cases ar with
          | ldx D B' I =>
            intro p vi hp hvi
            exact hsafe.1 ii D B' I (by rw [hget, ← hia]; rfl) p vi hp hvi
          | _ => trivial
        obtain ⟨s', zf', hst, hc', hzf'⟩ := AArm.sim P rsp ar hok sa s zf hc hsafeA
        have hstep : stepA frame body s zf = some (s', zf') := by
          simp only [stepA, hget]
          rw [← hia, AArm.tagAt_eq, hli]
          exact hst
        have hleak : stepLeakA frame body s zf = instrLeakA frame ar.li s := by
          simp only [stepLeakA, hget]
          rw [← hia, hli]
        have hred : redStep rsp body s.reg.lpc = redLeak rsp ar := by
          simp only [redStep, hget, hcl]
        rw [hstep, Option.bind_some, hleak, hred] at hrun
        obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
        obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa (ar.js P)).flags.zf.getD false = zf' := by
          intro hcnd
          have hc2 := hF.cond (k + 1) hkn
          unfold condPrevB at hc2
          rw [List.getElem?_eq_getElem hkn] at hc2
          revert hc2 hcnd
          rcases body[k + 1] with ⟨ii', li'⟩
          cases li' <;> simp [isCondB, List.getElem?_eq_getElem hk, hbk, hcl]
          exact hzf'
        obtain ⟨sa', hR⟩ := ih (k + 1) _ s' zf' t' ℓ' hpc' hkn hc' hz' hrun'
          (hsafe.2 s' zf' hstep)
        obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := shs) hshk
        have hops : shs[k].ops' = ar.js P := AArm.shape_ops hok (by rw [hia]; exact hshk)
        have hprog : prog = A ++ (ar.js P).map RInstr.op ++ B := by
          show RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]) = _
          rw [hsplit, hblk, hops]
        have hpos : posOf shs (k + 1) = A.length + (ar.js P).length := by
          rw [posOf_succ shs k hks, hn, hops, hA]
        rw [hpos, aMachine_runBlock] at hR
        have h0 := runL_ops B (ar.js P) A sa hprog hR
        rw [AArm.leak P rsp ar hok sa s hc, hA] at h0
        exact ⟨sa', by simpa [List.append_assoc] using h0⟩
      · cases hok
    | Llabel kd l =>
      have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
        unfold stepA
        rw [hget]
        simp only [hpc]
      have hleak : stepLeakA frame body s zf = [] := by
        simp only [stepLeakA, hget]
      have hred : redStep rsp body s.reg.lpc = [] := by
        simp only [redStep, hget, classifyA_label]
      rw [hstep, Option.bind_some, hleak, hred] at hrun
      obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
      obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
        intro hcnd
        rw [not_cond_after hF hkn (by rw [hbk]; rfl)] at hcnd
        cases hcnd
      obtain ⟨sa', hR⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t' ℓ' rfl hkn (acorr_setLpc hc _)
        hz' hrun' (hsafe.2 _ _ hstep)
      refine ⟨sa', ?_⟩
      rw [posOf_succ shs k hks] at hR
      have hsk : shs[k] = .one .skip := by
        simp [shapeOf] at hshk; exact hshk.symm
      rw [hsk] at hR
      simpa [nOf] using hR
    | Lcond c l =>
      cases c with
      | reg cc =>
        simp only [instrOKB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hok
        obtain ⟨hpl, hlabp, -⟩ := labelAt_spec hp
        have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
          simp [shapeOf] at hshk; exact hshk.symm
        have hj : prog[posOf shs k]? = some (.jcc (ccNibble cc) (posOf shs p)) := by
          show (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs k]? = _
          rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
          simp [blkOf, hp]
        have hzf : sa.flags.zf.getD false = zf := hz rfl
        obtain ⟨cd, hcd, hcb⟩ := jcc_pol sa hpol
        rw [hzf] at hcb
        have hleak : stepLeakA frame body s zf = [.branch (zf == pol)] := by
          simp only [stepLeakA, hget, hpol]
        have hred : redStep rsp body s.reg.lpc = [] := by
          simp only [redStep, hget, classifyA_cond]
        by_cases hzp : zf = pol
        · have hstep : stepA frame body s zf = some (s.setLpc p, zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hp]
          rw [hstep, Option.bind_some, hleak, hred] at hrun
          obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
          obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          have hz' : isCondB (body[p]'hpl).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            revert hlabp hcnd
            rcases body[p] with ⟨ii', li'⟩
            cases li' <;> simp [isCondB, isLabelB]
          obtain ⟨sa', hR⟩ := ih p sa (s.setLpc p) zf t' ℓ' rfl hpl (acorr_setLpc hc _) hz'
            hrun' (hsafe.2 _ _ hstep)
          have hb' : sa.view.condB cd = true := by rw [hcb, hzp]; simp
          refine ⟨sa', ?_⟩
          have := RunL.jcc (r := .doitm) (ok := fun _ _ => True) hj hcd
            (by rw [hb', if_pos rfl]; exact hR)
          rw [hb'] at this
          simpa [hzp] using this
        · have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hpc]
          rw [hstep, Option.bind_some, hleak, hred] at hrun
          obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
          obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            rw [not_cond_after hF hkn (by rw [hbk]; rfl)] at hcnd
            cases hcnd
          obtain ⟨sa', hR⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t' ℓ' rfl hkn
            (acorr_setLpc hc _) hz' hrun' (hsafe.2 _ _ hstep)
          rw [posOf_succ shs k hks, hsk] at hR
          have hb' : sa.view.condB cd = false := by
            rw [hcb]; cases zf <;> cases pol <;> simp_all
          refine ⟨sa', ?_⟩
          have := RunL.jcc (r := .doitm) (ok := fun _ _ => True) hj hcd
            (by rw [hb', if_neg (by simp)]; simpa [nOf] using hR)
          rw [hb'] at this
          have hzb : (zf == pol) = false := by cases zf <;> cases pol <;> simp_all
          simpa [hzb] using this
      | _ => simp [instrOKB] at hok
    | _ => simp [instrOKB] at hok

theorem opLeak_leaFrame (sa : AState) (d : Int) : opLeak .doitm sa (leaFrame d) = [] := by
  simp [opLeak, leaFrame, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]

/-- **The decoded bytes of a covered printed body simulate its run on the address machine,
    with leakage.** For every body in the class `printedAddrB`, from a machine state `sa` and
    an address state `s` at program counter `0` in which every general-purpose name `R` holds
    the value of the machine register `phys R` and the memories are equal, every terminating
    run of the address machine on the body whose indexed loads read outside the red-zone
    word, with trace `ℓ` of `runALeakX (redStep rsp body)` at the frame below the entry
    stack register, is matched by a halting run of the decoded function bytes with leakage
    trace `ℓ` under the regime `doitm`. -/
theorem printedAddr_simL (body : Lcmd) (h : printedAddrB body = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat) (t : LstateA × Bool) (ℓ : List CTLeak)
    (hrun : runALeakX (redStep (frameRsp body sa) body)
      (frameP (Params.ofBody body) (frameRsp body sa)) body fuel s zf = some (t, ℓ))
    (hsafe : RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
      (LoadSafeAt (frameRsp body sa) body) fuel s zf) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ RunL .doitm (fun _ _ => True) prog 0 sa ℓ sa' := by
  obtain ⟨shs, hF⟩ := bodyFacts_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrB, Bool.and_eq_true] at h
    exact h.1.1.1
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  set P := Params.ofBody body
  set F := P.frame
  set rsp := frameRsp body sa with hrsp
  set prog : List RInstr := .op (leaFrame (-(Int.ofNat F)))
    :: (shs.flatMap (blkOf body shs) ++ [.op (leaFrame (Int.ofNat F)), .ret]) with hprog
  have hdecode : decodeLprog (encodeLfundefBytes body) = some prog := by
    rw [decodeLprog_encodeLfundefBytes hdec, fundefLayout, fundefItems,
      show shapesD P body = shs by
        rw [shapesD, show shapesOf P body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_of hF)
  obtain ⟨hl1, hm1⟩ := evalInstrA_leaFrame sa (-(Int.ofNat F))
  set sa1 := evalInstrA sa (leaFrame (-(Int.ofNat F)))
  have hc0 : ACorr rsp sa1 s :=
    { regs := fun R hR => by rw [hent R hR, hl1, if_neg (fun e => (gpFacts hR).physNe e)]
      sp := by rw [hl1, if_pos rfl, hrsp]; rfl
      mem := fun x _ => by rw [hmem, hm1] }
  have hz0 : isCondB (body[0]'hF.pos).li_i = true → sa1.flags.zf.getD false = zf := by
    intro hcnd
    have hc := hF.cond 0 hF.pos
    revert hc hcnd
    unfold condPrevB
    rw [List.getElem?_eq_getElem hF.pos]
    rcases body[0]'hF.pos with ⟨ii, li⟩
    cases li <;> simp [isCondB]
  obtain ⟨sa2, hR⟩ := run_simL hF rsp _ _ (fun sa => opLeak_leaFrame sa _) fuel 0 sa1 s zf t ℓ
    hpc hF.pos hc0 hz0 hrun hsafe
  have hpos0 : posOf shs 0 = 1 := by simp [posOf]
  rw [hpos0] at hR
  have := RunL.op (r := .doitm) (ok := fun _ _ => True) (prog := prog) (pc := 0) (sa := sa)
    (i := leaFrame (-(Int.ofNat F))) rfl trivial hR
  rw [opLeak_leaFrame, List.nil_append] at this
  exact ⟨prog, sa2, hdecode, this⟩

/-! ## 5. Equal traces of the address machine give equal traces with added events -/

/-- The halt of the address machine reads only the program counter. -/
theorem haltedA_congr {c : Lcmd} {s₁ s₂ : LstateA} (h : s₁.reg.lpc = s₂.reg.lpc) :
    haltedA c s₁ = haltedA c s₂ := by
  unfold haltedA; rw [h]

/-- The length of the events of a step of the address machine on `c` is a function of the
    program counter, over steps that succeed. -/
def StepLenDet (frame : String → Option (BitVec 64)) (c : Lcmd) : Prop :=
  ∀ (s₁ s₂ : LstateA) (zf₁ zf₂ : Bool) (b₁ b₂ : LstateA × Bool), s₁.reg.lpc = s₂.reg.lpc →
    stepA frame c s₁ zf₁ = some b₁ → stepA frame c s₂ zf₂ = some b₂ →
    (stepLeakA frame c s₁ zf₁).length = (stepLeakA frame c s₂ zf₂).length

/-- Two steps from one program counter with equal events reach one program counter. -/
theorem stepA_lpc_det {frame : String → Option (BitVec 64)} {c : Lcmd} {s₁ s₂ : LstateA}
    {zf₁ zf₂ : Bool} {b₁ b₂ : LstateA × Bool} (hpc : s₁.reg.lpc = s₂.reg.lpc)
    (h₁ : stepA frame c s₁ zf₁ = some b₁) (h₂ : stepA frame c s₂ zf₂ = some b₂)
    (hl : stepLeakA frame c s₁ zf₁ = stepLeakA frame c s₂ zf₂) :
    b₁.1.reg.lpc = b₂.1.reg.lpc := by
  obtain ⟨u₁, z₁⟩ := b₁
  obtain ⟨u₂, z₂⟩ := b₂
  unfold stepA at h₁ h₂
  unfold stepLeakA at hl
  rw [hpc] at h₁ hl
  cases hb : c[s₂.reg.lpc]? with
  | none => rw [hb] at h₂; cases h₂
  | some i =>
    obtain ⟨ii, li⟩ := i
    rw [hb] at h₁ h₂ hl
    cases li with
    | Lopn ds o ss =>
      simp only at h₁ h₂
      rw [fstepA_lpc _ _ _ _ _ _ h₁, fstepA_lpc _ _ _ _ _ _ h₂, hpc]
    | Llabel _ _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      rw [← h₁.1, ← h₂.1]
      simp [LstateA.setLpc]
    | Lcond cnd l =>
      cases cnd with
      | reg cc =>
        cases hp : condPol cc with
        | none => simp [hp] at h₁
        | some pol =>
          simp only [hp, List.cons.injEq, CTLeak.branch.injEq, and_true] at h₁ h₂ hl
          by_cases e₁ : zf₁ = pol <;> by_cases e₂ : zf₂ = pol
          · rw [if_pos e₁] at h₁
            rw [if_pos e₂] at h₂
            obtain ⟨p, hp1, hq₁⟩ := Option.map_eq_some_iff.mp h₁
            obtain ⟨p', hp2, hq₂⟩ := Option.map_eq_some_iff.mp h₂
            rw [hp1] at hp2
            cases hp2
            simp only [Prod.mk.injEq] at hq₁ hq₂
            rw [← hq₁.1, ← hq₂.1]
            rfl
          · subst e₁; simp at hl; exact absurd hl e₂
          · subst e₂; simp at hl; exact absurd hl e₁
          · rw [if_neg e₁] at h₁
            rw [if_neg e₂] at h₂
            simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
            rw [← h₁.1, ← h₂.1]
            rfl
      | _ => simp at h₁
    | _ => simp at h₁

/-- **Transfer of equal traces.** Over a body whose step event lengths are functions of the
    program counter, two terminating runs of the address machine from one program counter with
    equal traces have equal traces with the events `X` added. -/
theorem runALeakX_transfer {frame : String → Option (BitVec 64)} {c : Lcmd}
    (hlen : StepLenDet frame c) (X : Nat → List CTLeak) :
    ∀ (f₁ f₂ : Nat) (s₁ s₂ : LstateA) (zf₁ zf₂ : Bool) (r₁ r₂ q₁ q₂ : LstateA × Bool)
      (ℓ m₁ m₂ : List CTLeak), s₁.reg.lpc = s₂.reg.lpc →
      runALeak frame c f₁ s₁ zf₁ = some (r₁, ℓ) → runALeak frame c f₂ s₂ zf₂ = some (r₂, ℓ) →
      runALeakX X frame c f₁ s₁ zf₁ = some (q₁, m₁) →
      runALeakX X frame c f₂ s₂ zf₂ = some (q₂, m₂) → m₁ = m₂ := by
  intro f₁
  induction f₁ with
  | zero =>
    intro f₂ s₁ s₂ zf₁ zf₂ r₁ r₂ q₁ q₂ ℓ m₁ m₂ hpc hA₁ hA₂ hX₁ hX₂
    cases hh : haltedA c s₁
    · simp [runALeak, hh] at hA₁
    · have hh₂ : haltedA c s₂ = true := by rw [← haltedA_congr hpc, hh]
      rw [runALeakX_halt _ _ _ _ _ _ hh] at hX₁
      rw [runALeakX_halt _ _ _ _ _ _ hh₂] at hX₂
      cases hX₁; cases hX₂; rfl
  | succ f ih =>
    intro f₂ s₁ s₂ zf₁ zf₂ r₁ r₂ q₁ q₂ ℓ m₁ m₂ hpc hA₁ hA₂ hX₁ hX₂
    cases hh : haltedA c s₁
    · have hh₂ : haltedA c s₂ = false := by rw [← haltedA_congr hpc, hh]
      cases f₂ with
      | zero => simp [runALeak, hh₂] at hA₂
      | succ g =>
        rw [runALeak_step _ _ _ _ _ hh] at hA₁
        rw [runALeak_step _ _ _ _ _ hh₂] at hA₂
        rw [runALeakX_step _ _ _ _ _ _ hh] at hX₁
        rw [runALeakX_step _ _ _ _ _ _ hh₂] at hX₂
        cases hs₁ : stepA frame c s₁ zf₁ with
        | none => rw [hs₁] at hA₁; cases hA₁
        | some b₁ =>
          cases hs₂ : stepA frame c s₂ zf₂ with
          | none => rw [hs₂] at hA₂; cases hA₂
          | some b₂ =>
            rw [hs₁, Option.bind_some] at hA₁ hX₁
            rw [hs₂, Option.bind_some] at hA₂ hX₂
            obtain ⟨⟨r₁', ℓ₁⟩, hA₁', e₁⟩ := Option.map_eq_some_iff.mp hA₁
            obtain ⟨⟨r₂', ℓ₂⟩, hA₂', e₂⟩ := Option.map_eq_some_iff.mp hA₂
            obtain ⟨⟨q₁', m₁'⟩, hX₁', e₃⟩ := Option.map_eq_some_iff.mp hX₁
            obtain ⟨⟨q₂', m₂'⟩, hX₂', e₄⟩ := Option.map_eq_some_iff.mp hX₂
            simp only [Prod.mk.injEq] at e₁ e₂ e₃ e₄
            have happ := e₁.2.trans e₂.2.symm
            obtain ⟨hst, hrest⟩ :=
              List.append_inj happ (hlen s₁ s₂ zf₁ zf₂ b₁ b₂ hpc hs₁ hs₂)
            have hpc' := stepA_lpc_det hpc hs₁ hs₂ hst
            subst hrest
            have hm := ih g b₁.1 b₂.1 b₁.2 b₂.2 r₁' r₂' q₁' q₂' ℓ₁ m₁' m₂' hpc' hA₁' hA₂' hX₁' hX₂'
            rw [← e₃.2, ← e₄.2, hst, hpc, hm]
    · have hh₂ : haltedA c s₂ = true := by rw [← haltedA_congr hpc, hh]
      rw [runALeakX_halt _ _ _ _ _ _ hh] at hX₁
      rw [runALeakX_halt _ _ _ _ _ _ hh₂] at hX₂
      cases hX₁; cases hX₂; rfl

/-- A register-tagged instruction that accesses no cell has events independent of the
    state. -/
theorem instrLeakA_reg_indep {frame : String → Option (BitVec 64)} {x : LinstrR}
    (hcell : cellA? x = none) (tag : Option Nat) (s₁ s₂ : LstateA) :
    instrLeakA frame (x, .reg tag) s₁ = instrLeakA frame (x, .reg tag) s₂ := by
  simp only [instrLeakA, hcell]

/-- Over two succeeding steps of an arm, its events on the address machine have one length. -/
theorem AArm.leak_length {P : Params} {a : AArm} (hok : a.ok P = true)
    {frame : String → Option (BitVec 64)} {s₁ s₂ : LstateA} {zf₁ zf₂ : Bool}
    {b₁ b₂ : LstateA × Bool} (h₁ : fstepA frame a.li s₁ zf₁ = some b₁)
    (h₂ : fstepA frame a.li s₂ zf₂ = some b₂) :
    (instrLeakA frame a.li s₁).length = (instrLeakA frame a.li s₂).length := by
  cases a with
  | ldx D B I =>
    cases hB₁ : s₁.reg.getW B 64 with
    | none => simp [AArm.li, fstepA, loadIdxA?, hB₁] at h₁
    | some p₁ =>
      cases hB₂ : s₂.reg.getW B 64 with
      | none => simp [AArm.li, fstepA, loadIdxA?, hB₂] at h₂
      | some p₂ => simp [AArm.li, instrLeakA, loadIdxA?, hB₁, hB₂]
  | stx d B I V =>
    cases hB₁ : s₁.reg.getW B 64 with
    | none => simp [AArm.li, fstepA, storeIdxA?, hB₁] at h₁
    | some p₁ =>
      cases hB₂ : s₂.reg.getW B 64 with
      | none => simp [AArm.li, fstepA, storeIdxA?, hB₂] at h₂
      | some p₂ => simp [AArm.li, instrLeakA, storeIdxA?, hB₁, hB₂]
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at hok
    simp only [AArm.li, AArm.instr]
    rw [instrLeakA_reg_indep (regArm_cell hok.1.1 hok.1.2) none s₁ s₂]
  | st m q S =>
    simp only [AArm.ok, Bool.and_eq_true] at hok
    have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
      simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hok; exact hok.2.symm
    have hcell : cellA? (AArm.st m q S).instr = none := by
      rcases hm' with rfl | rfl <;>
        simp [AArm.instr, cellA?, cellParts?_of_spillOff hok.1.1.2, cellParts?_gp hok.1.1.1.1]
    simp only [AArm.li]
    rw [instrLeakA_reg_indep hcell none s₁ s₂]
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true] at hok
    have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
      simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hok; exact hok.2.symm
    have hcell : cellA? (AArm.ld m D q).instr = none := by
      rcases hm' with rfl | rfl <;>
        simp [AArm.instr, cellA?, cellParts?_of_spillOff hok.1.1.1.2, cellParts?_gp hok.1.1.1.1.1]
    simp only [AArm.li]
    rw [instrLeakA_reg_indep hcell none s₁ s₂]
  | cmpR c r =>
    simp only [AArm.li]; rw [instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none s₁ s₂]
  | cmpI c k =>
    simp only [AArm.li]; rw [instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none s₁ s₂]
  | cmpM c q =>
    simp only [AArm.li]; rw [instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none s₁ s₂]
  | mul D S =>
    simp only [AArm.li]; rw [instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none s₁ s₂]
  | mulxS H S =>
    simp only [AArm.li]; rw [instrLeakA_reg_indep (by simp [cellA?]) none s₁ s₂]
  | mulx L H S =>
    simp only [AArm.li]; rw [instrLeakA_reg_indep (by simp [cellA?]) none s₁ s₂]

/-- The step event lengths of a covered body are functions of the program counter. -/
theorem stepLenDet_of {body : Lcmd} {shs : List DShape} (hF : BodyFacts body shs)
    (frame : String → Option (BitVec 64)) : StepLenDet frame body := by
  intro s₁ s₂ zf₁ zf₂ b₁ b₂ hpc h₁ h₂
  unfold stepA at h₁ h₂
  unfold stepLeakA
  rw [hpc] at h₁ ⊢
  cases hb : body[s₂.reg.lpc]? with
  | none => rfl
  | some i =>
    obtain ⟨ii, li⟩ := i
    rw [hb] at h₁ h₂
    cases li with
    | Lopn ds o ss =>
      simp only at h₁ h₂ ⊢
      obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
      have hkn : s₂.reg.lpc + 1 < body.length := by
        by_contra hc
        have hlast := hF.last
        have he : s₂.reg.lpc = body.length - 1 := by omega
        simp only [he] at hbk
        rw [hbk] at hlast
        cases hlast
      have hok := hF.instr _ hkn
      rw [hbk] at hok
      simp only [instrOKB] at hok
      split at hok
      · rename_i ar hcl
        have hia := classifyA_instr hcl
        have hli := AArm.li_eq hok
        rw [← hia, AArm.tagAt_eq, hli] at h₁ h₂
        rw [← hia, hli]
        exact AArm.leak_length hok h₁ h₂
      · cases hok
    | Lcond cnd l =>
      cases cnd with
      | reg cc => simp only; cases condPol cc <;> rfl
      | _ => rfl
    | _ => rfl

/-! ## 6. Constant time of the decoded bytes -/

/-- The entry correspondence of an address state `s` to a machine state `sa`: program counter
    `0`, every general-purpose name holding the value of its machine register, equal
    memories. -/
def Entry (sa : AState) (s : LstateA) : Prop :=
  s.reg.lpc = 0 ∧ (∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    ∧ s.mem = sa.mem

/-- A terminating run of the address machine on `body` from `a` whose indexed loads read
    outside the red-zone word at `rsp`. -/
def SafeHalt (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (body : Lcmd)
    (a : LstateA × Bool) : Prop :=
  ∃ fuel t, runA frame body fuel a.1 a.2 = some t
    ∧ RunSafe frame body (LoadSafeAt rsp body) fuel a.1 a.2

/-- **Equal traces of the decoded bytes.** For a body in `printedAddrB` and two machine states
    with one frame address `rsp`, corresponding at entry to address states whose runs
    terminate safely and whose traces of the address machine are equal, every two runs with
    leakage of the decoded bytes from the two machine states have equal traces. -/
theorem bytes_trace_eq {body : Lcmd} (h : printedAddrB body = true) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) {rsp : BitVec 64}
    {sa₁ sa₂ : AState} (hr₁ : frameRsp body sa₁ = rsp) (hr₂ : frameRsp body sa₂ = rsp)
    {a₁ a₂ : LstateA × Bool} (he₁ : Entry sa₁ a₁.1) (he₂ : Entry sa₂ a₂.1)
    (hh₁ : SafeHalt (frameP (Params.ofBody body) rsp) rsp body a₁)
    (hh₂ : SafeHalt (frameP (Params.ofBody body) rsp) rsp body a₂)
    (hℓ : ∀ ℓ₁ ℓ₂, ARun (frameP (Params.ofBody body) rsp) body a₁ ℓ₁ →
      ARun (frameP (Params.ofBody body) rsp) body a₂ ℓ₂ → ℓ₁ = ℓ₂)
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {u₁ u₂ : List CTLeak} {sa₁' sa₂' : AState}
    (hb₁ : RunL .doitm ok₁ prog 0 sa₁ u₁ sa₁') (hb₂ : RunL .doitm ok₂ prog 0 sa₂ u₂ sa₂') :
    u₁ = u₂ := by
  obtain ⟨shs, hF⟩ := bodyFacts_of h
  obtain ⟨f₁, t₁, hrA₁, hs₁⟩ := hh₁
  obtain ⟨f₂, t₂, hrA₂, hs₂⟩ := hh₂
  obtain ⟨hpc₁, hent₁, hmem₁⟩ := he₁
  obtain ⟨hpc₂, hent₂, hmem₂⟩ := he₂
  obtain ⟨m₁, hX₁⟩ := runALeakX_of_runA (redStep rsp body) hrA₁
  obtain ⟨m₂, hX₂⟩ := runALeakX_of_runA (redStep rsp body) hrA₂
  obtain ⟨ℓ₁, hA₁⟩ := runALeakX_of_runA (fun _ => []) hrA₁
  obtain ⟨ℓ₂, hA₂⟩ := runALeakX_of_runA (fun _ => []) hrA₂
  rw [runALeakX_nil] at hA₁ hA₂
  subst hr₁
  obtain ⟨p₁, c₁, hd₁, hL₁⟩ := printedAddr_simL body h sa₁ a₁.1 a₁.2 hpc₁ hent₁ hmem₁ f₁ t₁ m₁
    hX₁ hs₁
  obtain ⟨p₂, c₂, hd₂, hL₂⟩ := printedAddr_simL body h sa₂ a₂.1 a₂.2 hpc₂ hent₂ hmem₂ f₂ t₂ m₂
    (by rw [hr₂]; exact hX₂) (by rw [hr₂]; exact hs₂)
  rw [hdec] at hd₁ hd₂
  cases hd₁; cases hd₂
  have e₁ := (runL_det hb₁ hL₁).1
  have e₂ := (runL_det hb₂ hL₂).1
  have hl : ℓ₁ = ℓ₂ := hℓ ℓ₁ ℓ₂ ⟨f₁, t₁, hA₁⟩ ⟨f₂, t₂, hA₂⟩
  subst hl
  rw [e₁, e₂]
  exact runALeakX_transfer (stepLenDet_of hF _) (redStep _ body) f₁ f₂ a₁.1 a₂.1 a₁.2 a₂.2
    t₁ t₂ t₁ t₂ ℓ₁ m₁ m₂ (by rw [hpc₁, hpc₂]) hA₁ hA₂ hX₁ hX₂

/-- Public-equal machine states for the decoded bytes of `body`: one frame address `rsp`, and
    entry correspondences to address states related by `R` whose runs terminate safely. -/
def BytePub (rsp : BitVec 64) (body : Lcmd) (R : LstateA × Bool → LstateA × Bool → Prop)
    (sa₁ sa₂ : AState) : Prop :=
  frameRsp body sa₁ = rsp ∧ frameRsp body sa₂ = rsp ∧ ∃ a₁ a₂, R a₁ a₂
    ∧ Entry sa₁ a₁.1 ∧ Entry sa₂ a₂.1
    ∧ SafeHalt (frameP (Params.ofBody body) rsp) rsp body a₁
    ∧ SafeHalt (frameP (Params.ofBody body) rsp) rsp body a₂

/-- **Constant time of the decoded bytes from constant time of the address machine.** For a
    body in `printedAddrB`, constant time of the address machine on the body at the frame
    below `rsp`, between address states related by `R`, gives constant time of the decoded
    bytes under the regime `doitm` and any side condition, between machine states that
    correspond at entry to `R`-related address states (`BytePub`). -/
theorem bytes_ct {body : Lcmd} (h : printedAddrB body = true) {rsp : BitVec 64}
    {R : LstateA × Bool → LstateA × Bool → Prop}
    (hct : ConstantTimeRel R (ARun (frameP (Params.ofBody body) rsp) body))
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (BytePub rsp body R) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  rintro sa₁ sa₂ u₁ u₂ ⟨hr₁, hr₂, a₁, a₂, hR, he₁, he₂, hh₁, hh₂⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩
  exact bytes_trace_eq h hdec hr₁ hr₂ he₁ he₂ hh₁ hh₂
    (fun ℓ₁ ℓ₂ h₁ h₂ => hct a₁ a₂ ℓ₁ ℓ₂ hR h₁ h₂) hb₁ hb₂

/-! ## 7. The frame at the names of a body, and the composition with the image -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
  (bodyNamesI frameIn frameIn_eq instrNames_normA slotCarry?_congr slotImm?_congr
    slotCmov?_congr runA_frameIn runSafe_frameIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
  (slotMov?_cases slotCmp?_eq ImgSep ImgRel imgGateB image_addr_sim)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)

/-- The events of an instruction on the address machine read the frame only at the names of
    the instruction. -/
theorem instrLeakA_congr {frame frame' : String → Option (BitVec 64)} {x : LinstrR}
    (h : ∀ q ∈ instrNames x, frame q = frame' q) (tag : MemTag) (sa : LstateA) :
    instrLeakA frame (x, tag) sa = instrLeakA frame' (x, tag) sa := by
  unfold instrLeakA
  cases tag with
  | reg c =>
    simp only
    cases hm : slotMov? x with
    | some ds =>
      obtain ⟨d, s⟩ := ds
      have hd : d ∈ instrNames x ∧ s ∈ instrNames x := by
        rcases slotMov?_cases hm with rfl | rfl <;> simp [instrNames,
          JasminLsemExportRewrites.opNames]
      simp only
      rw [h s hd.2, h d hd.1]
    | none =>
      simp only
      cases hk : slotCmp? x with
      | some dyq =>
        obtain ⟨d, y, q⟩ := dyq
        have hq : q ∈ instrNames x := by
          rw [slotCmp?_eq hk]; simp [instrNames, JasminLsemExportRewrites.opNames]
        simp only
        rw [h q hq]
      | none =>
        simp only
        rw [← slotCarry?_congr h, ← slotImm?_congr h, ← slotCmov?_congr h]
        rcases hsc : slotCarry? frame x with _ | ⟨lo, d, a, s, c⟩
        · rcases hsv : slotCmov? frame x with _ | ⟨d, c, a, b⟩
          · rfl
          · unfold slotCmov? at hsv
            split at hsv
            · split_ifs at hsv
              obtain ⟨rfl, rfl, rfl, rfl⟩ := hsv
              have ha := h a (by simp [instrNames, JasminLsemExportRewrites.opNames])
              have hb := h b (by simp [instrNames, JasminLsemExportRewrites.opNames])
              have hd := h d (by simp [instrNames, JasminLsemExportRewrites.opNames])
              simp only [ha, hb, hd]
            · cases hsv
        · unfold slotCarry? at hsc
          split at hsc
          · split_ifs at hsc
            obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hsc
            have hd := h d (by simp [instrNames, JasminLsemExportRewrites.opNames])
            have ha := h a (by simp [instrNames, JasminLsemExportRewrites.opNames])
            have hs := h s (by simp [instrNames, JasminLsemExportRewrites.opNames])
            have hc := h c (by simp [instrNames, JasminLsemExportRewrites.opNames])
            simp only [hd, ha, hs, hc]
          · cases hsc
  | _ => rfl

theorem stepLeakA_congr {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) (s : LstateA) (zf : Bool) :
    stepLeakA frame body s zf = stepLeakA frame' body s zf := by
  unfold stepLeakA
  cases hb : body[s.reg.lpc]? with
  | none => rfl
  | some i =>
    obtain ⟨ii, li⟩ := i
    cases li with
    | Lopn ds o ss =>
      simp only
      refine instrLeakA_congr (fun q hq => h q ?_) _ s
      rw [instrNames_normA] at hq
      simp only [bodyNamesI, List.mem_flatMap]
      exact ⟨⟨ii, .Lopn ds o ss⟩, List.mem_of_getElem? hb, hq⟩
    | Lcond c l => cases c <;> rfl
    | _ => rfl

theorem runALeak_congr {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      runALeak frame body fuel s zf = runALeak frame' body fuel s zf
  | 0, _, _ => rfl
  | fuel + 1, s, zf => by
      simp only [runALeak, ImageAddrFrame.stepA_congr h s zf, stepLeakA_congr h s zf]
      cases stepA frame' body s zf with
      | none => rfl
      | some bz => simp only [Option.bind_some, runALeak_congr h fuel bz.1 bz.2]

/-- The traced runs of the address machine at the restricted frame are its traced runs at the
    frame. -/
theorem aRun_frameIn (body : Lcmd) (frame : String → Option (BitVec 64)) (a : LstateA × Bool)
    (ℓ : List CTLeak) : ARun (frameIn body frame) body a ℓ ↔ ARun frame body a ℓ := by
  simp only [ARun, runALeak_congr frameIn_eq]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (MemFCT)

/-- Public-equal machine states for the decoded bytes of a body with an image: one frame
    address `rsp`, and entry correspondences to address states public-equal through the image
    (`AddrPub`) at the frame of `body` below `rsp` restricted to its names. -/
def ImgBytePub (rsp : BitVec 64) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (body : Lcmd) (fn : String)
    (pubEq : LstateMF → LstateMF → Prop) (sa₁ sa₂ : AState) : Prop :=
  frameRsp body sa₁ = rsp ∧ frameRsp body sa₂ = rsp ∧ ∃ a₁ a₂,
    AddrPub (frameIn body (frameP (Params.ofBody body) rsp)) slotArr base body fn pubEq a₁ a₂
    ∧ Entry sa₁ a₁.1 ∧ Entry sa₂ a₂.1

/-- **Constant time of the decoded bytes from constant time of the image.** For a printed body
    in `printedAddrB` without a conditional branch that passes the gates of the image
    simulation at its frame below `rsp`, restricted to its names, and is separated there,
    constant time of the image on the flag machine (`MemFCT`) gives constant time of the
    decoded function bytes of the body under the regime `doitm` and any side condition,
    between machine states with the frame address `rsp` that correspond at entry to address
    states public-equal through the image (`ImgBytePub`). -/
theorem image_bytes_ct {slotArr : String → Option (String × Nat)} {base : String → BitVec 64}
    {body : Lcmd} {rsp : BitVec 64} (hpr : printedAddrB body = true)
    (hphys : physImgB slotArr body = true)
    (hgate : imgGateB (frameIn body (frameP (Params.ofBody body) rsp)) slotArr body = true)
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) rsp)) slotArr base rsp)
    (hnc : NoCond body) (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr body)) pubEq)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (ImgBytePub rsp slotArr base body fn pubEq)
      (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  rintro sa₁ sa₂ u₁ u₂ ⟨hr₁, hr₂, a₁, a₂, hpub, he₁, he₂⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩
  have hA := image_addr_ct hsep hphys hgate hnc fn hct
  have hpub' := hpub
  obtain ⟨s₁, s₂, -, -, hfn₁, hfn₂, hR₁, hR₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩ := hpub'
  obtain ⟨g₁, sa₁', zf₁', hrA₁, -, hs₁⟩ :=
    image_addr_sim hsep hphys hgate fn f₁ s₁ t₁ a₁.1 a₁.2 hfn₁ hR₁ hk₁
  obtain ⟨g₂, sa₂', zf₂', hrA₂, -, hs₂⟩ :=
    image_addr_sim hsep hphys hgate fn f₂ s₂ t₂ a₂.1 a₂.2 hfn₂ hR₂ hk₂
  rw [runA_frameIn] at hrA₁ hrA₂
  rw [runSafe_frameIn] at hs₁ hs₂
  exact bytes_trace_eq hpr hdec hr₁ hr₂ he₁ he₂ ⟨g₁, _, hrA₁, hs₁⟩ ⟨g₂, _, hrA₂, hs₂⟩
    (fun ℓ₁ ℓ₂ h₁ h₂ => hA a₁ a₂ ℓ₁ ℓ₂ hpub ((aRun_frameIn body _ a₁ ℓ₁).mpr h₁)
      ((aRun_frameIn body _ a₂ ℓ₂).mpr h₂)) hb₁ hb₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak
