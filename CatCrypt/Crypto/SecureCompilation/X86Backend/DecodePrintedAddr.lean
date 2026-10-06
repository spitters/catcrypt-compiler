/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

@[expose] public section

set_option autoImplicit false

/-!
# The instructions of a physical body on the address machine against their decoded bytes

`VIR.JasminLsemAddrRun.runA` runs a printed physical body on the address machine: a register
file keyed by name and a byte memory. A frame word `qsave.X` or `k.N` is the memory word at
its frame address `frameP P rsp`, and an indexed access `(%B, %I, 8)` reads or writes the
memory word at the address in `B` plus eight times the index. This module relates one
instruction of such a body to the machine instructions its bytes decode to.

## The correspondence

`ACorr rsp sa s` relates a machine state `sa` to an address state `s`: each general-purpose
name `R` holds the value of the machine register `phys R`, the stack register holds `rsp`,
and the two memories agree on every byte outside the eight bytes `redW rsp` at `-128` from
the stack register. The encoder's widening multiply with coincident destinations saves its
scratch register in that red-zone word; no other covered instruction writes it.

## The arms

`AArm` is the covered instructions: the register arms `Arm` of `DecodePrinted` other than
the frame-word moves; the frame-word store and load at `MOVQ` or `MOV:64`; the flag compare
`CMP:64` with a register, a sign-extended `imm8` or a frame word; the indexed load `LOADIDX`
and store `STOREIDX` at scale `8`; the low multiply `MUL:64`; the widening multiply `MULX`
with coincident or with distinct destinations.
`AArm.ok` is the Boolean condition of an arm, read off the instruction.

## Main results

* `ACorr`, `ACorr.read64_eq`: the correspondence and the agreement of a word read outside the
  red-zone word.
* `fstepA_of_reg`, `simA_of_decSim`: a register instruction is stepped by the flag machine on
  the register file, and a `DecodePrinted` simulation of it lifts to the address machine.
* `AArm.bytes`, `AArm.shape_ops`: the encoder lays down the pieces of an arm whose conditions
  hold, and the computed shape of its instruction decodes to the arm's machine instructions.
* `AArm.sim`: the address-machine step of such an arm is simulated by its decoded
  instructions, from `ACorr` to `ACorr`, with the machine zero flag equal to the flag after a
  compare; an indexed load reads outside the red-zone word (`AArm.LoadSafe`).
* `classifyA`, `classifyA_instr`, `AArm.li_eq`: the arm of an instruction, and the tagged
  instruction `VIR.JasminLsemAddrRun.stepA` steps for it.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted

/-! ## 1. The correspondence -/

/-- The frame-slot addresses of a printed body under the body parameters `P`, with the stack
    register at `rsp`: a spill or save name at its frame offset, no address otherwise. -/
def frameP (P : Params) (rsp : BitVec 64) (q : String) : Option (BitVec 64) :=
  (spillQsaveOff P.frame P.spillW q P.qsaveB).map fun o => rsp + BitVec.ofInt 64 o

theorem frameP_gp {P : Params} {rsp : BitVec 64} {r : String} (h : gpOk r = true) :
    frameP P rsp r = none := by
  simp [frameP, (gpFacts h).off]

/-- The red-zone word: the eight bytes at `-128` from the stack register. -/
def redW (rsp : BitVec 64) : BitVec 64 := rsp + BitVec.ofInt 64 cmovRedZone

/-- The flag-machine base state of an address state: its register file and its carry and
    overflow flags. -/
def baseOf (s : LstateA) : LstateM := { reg := s.reg, cf := s.cf, of := s.of }

/-- **The correspondence of a physical body.** Each general-purpose name reads at width `64`
    the value of its machine register, the stack register holds `rsp`, and the memories agree
    outside the red-zone word. -/
structure ACorr (rsp : BitVec 64) (sa : AState) (s : LstateA) : Prop where
  /-- A general-purpose name holds the value of its machine register. -/
  regs : ∀ r, gpOk r = true → s.reg.getW r 64 = some (sa.regs (phys r))
  /-- The stack register holds `rsp`. -/
  sp : sa.regs "%rsp" = rsp
  /-- The memories agree outside the red-zone word. -/
  mem : ∀ x, ¬ InRange8 (redW rsp) x → s.mem x = sa.mem x

/-- Two memories that agree outside the eight bytes at `r` read one word at an address whose
    eight bytes are disjoint from them. -/
theorem read64_eq_of_agree {m m' : AMem} {r a : BitVec 64}
    (h : ∀ x, ¬ InRange8 r x → m x = m' x) (hd : Disjoint8 r a) : read64 m a = read64 m' a := by
  have h0 : ¬ InRange8 r a := by simpa using not_inRange_of_disjoint r a 0 hd (by decide)
  simp only [read64, h a h0, h _ (not_inRange_of_disjoint r a 1 hd (by decide)),
    h _ (not_inRange_of_disjoint r a 2 hd (by decide)),
    h _ (not_inRange_of_disjoint r a 3 hd (by decide)),
    h _ (not_inRange_of_disjoint r a 4 hd (by decide)),
    h _ (not_inRange_of_disjoint r a 5 hd (by decide)),
    h _ (not_inRange_of_disjoint r a 6 hd (by decide)),
    h _ (not_inRange_of_disjoint r a 7 hd (by decide))]

theorem ACorr.read64_eq {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorr rsp sa s)
    {a : BitVec 64} (hd : Disjoint8 (redW rsp) a) : read64 s.mem a = read64 sa.mem a :=
  read64_eq_of_agree h.mem hd

/-- One word written at one address to both memories keeps their agreement. -/
theorem agree_write64 {m m' : AMem} {r : BitVec 64} (h : ∀ x, ¬ InRange8 r x → m x = m' x)
    (a v : BitVec 64) : ∀ x, ¬ InRange8 r x → write64 m a v x = write64 m' a v x := by
  intro x hx
  simp only [write64]
  split
  · rfl
  · exact h x hx

theorem ACorr.pcorr {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorr rsp sa s)
    (zf : Bool) : PCorr [] rsp sa (baseOf s) zf where
  regs := h.regs
  sp := h.sp
  slots p hp := absurd hp (by simp)
  names p hp := absurd hp (by simp)

/-- The machine instructions that write no memory. -/
def noWriteB : JInstr 64 → Bool
  | .storeMem .. => false
  | .addToMem .. => false
  | .storeMemIdx .. => false
  | _ => true

theorem evalInstrA_mem_of_noWriteB (sa : AState) (j : JInstr 64) (h : noWriteB j = true) :
    (evalInstrA sa j).mem = sa.mem := by
  have hw : writeAddr sa j = none := by
    cases j <;> simp_all [noWriteB, writeAddr]
  simp [evalInstrA, hw]

theorem runBlock_mem_of_noWriteB :
    ∀ (js : List (JInstr 64)) (sa : AState), js.all noWriteB = true →
      (aMachine.runBlock sa js).mem = sa.mem := by
  intro js
  induction js with
  | nil => intro _ _; rfl
  | cons j js ih =>
    intro sa h
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [Machine.runBlock_cons, ih _ h.2]
    exact evalInstrA_mem_of_noWriteB sa j h.1

/-! ## 2. Register instructions -/

/-- A register-tagged instruction that moves no frame slot, compares against no frame slot,
    accesses no cell, is no carry-chain instruction with a frame-slot operand, no immediate
    move into a frame slot and no select with a frame-slot value is stepped by the flag machine
    on the register file. -/
theorem fstepA_of_reg (frame : String → Option (BitVec 64)) {i : LinstrRM} {c : Option Nat}
    (ht : i.snd = .reg c)
    (hs : ∀ d s, slotMov? i.fst = some (d, s) → frame s = none ∧ frame d = none)
    (hq : ∀ d x q, slotCmp? i.fst = some (d, x, q) → frame q = none)
    (hcl : cellA? i.fst = none) (hsc : slotCarry? frame i.fst = none)
    (hsi : slotImm? frame i.fst = none) (hsv : slotCmov? frame i.fst = none)
    (s : LstateA) (zf : Bool) : fstepA frame i s zf = regStepA i s zf := by
  obtain ⟨w, t⟩ := i
  simp only at ht hcl hsc hsi hsv
  subst ht
  unfold fstepA
  simp only
  cases h : slotMov? w with
  | none =>
    simp only
    cases hk : slotCmp? w with
    | none => simp only [hcl, hsc, hsi, hsv]
    | some dxq =>
      obtain ⟨d, x, q⟩ := dxq
      simp only [hq d x q hk]
  | some ds =>
    obtain ⟨d, s'⟩ := ds
    obtain ⟨h1, h2⟩ := hs d s' h
    simp only [h1, h2]

/-- **A register instruction.** A `DecodePrinted` simulation of a register instruction that
    the address machine steps on the register file, by machine instructions that write no
    memory, is a simulation from `ACorr` to `ACorr` on the address machine. -/
theorem simA_of_decSim {frame : String → Option (BitVec 64)} {rsp : BitVec 64} {i : LinstrRM}
    {js : List (JInstr 64)} (hf : ∀ s zf, fstepA frame i s zf = regStepA i s zf)
    (hjs : js.all noWriteB = true)
    (hsim : DecSim (PCorr [] rsp) (PCorr [] rsp) [i] js) (sa : AState) (s : LstateA)
    (zf : Bool) (h : ACorr rsp sa s) :
    ∃ s' zf', fstepA frame i s zf = some (s', zf') ∧ ACorr rsp (aMachine.runBlock sa js) s'
      ∧ s'.mem = s.mem := by
  obtain ⟨b', z', hr, hc⟩ := hsim sa (baseOf s) zf (h.pcorr zf)
  rw [runStraightF_singleton] at hr
  refine ⟨{ s with reg := b'.reg, cf := b'.cf, of := b'.of }, z', ?_, ?_, rfl⟩
  · rw [hf]
    show (fstepF i (baseOf s) zf).map _ = _
    rw [hr]
    rfl
  · refine ⟨hc.regs, hc.sp, fun x hx => ?_⟩
    rw [runBlock_mem_of_noWriteB js sa hjs]
    exact h.mem x hx

/-! ## 3. The bytes of the memory, compare and multiply arms -/

/-- The register compare `CMP:64 c, c, r` between general-purpose names. -/
theorem encodeLopn_cmpR (F W : Nat) (c r : String) (qB : Nat) (hc : gpOk c = true)
    (hr : gpOk r = true) :
    encodeLopn F W (.Lopn [.reg c] "CMP:64" [.reg c, .reg r]) qB
      = encAluRRw 1 0x39 (gpNumU c) (gpNumU r) := by
  have fc := gpFacts hc
  have fr := gpFacts hr
  simp (config := { decide := true }) [encodeLopn, fc.isGp, fr.isGp, tagShiftExt,
    aluOpcode, twoByteOpcode, stripWidthTag, adxPrefix, LprogBytes.rexW]

/-- The immediate compare `CMP:64 c, c, #k` with a sign-extended `imm8`. -/
theorem encodeLopn_cmpI (F W : Nat) (c : String) (k qB : Nat) (hc : gpOk c = true)
    (hk : fitsImm8S 1 k = true) :
    encodeLopn F W (.Lopn [.reg c] "CMP:64" [.reg c, .imm k]) qB
      = encAluImm8 1 7 (gpNumU c) k := by
  have fc := gpFacts hc
  simp (config := { decide := true }) [encodeLopn, encImmOp, fc.notSlot, hk, shiftImmExt,
    aluImmDigit, stripWidthTag, adxPrefix, LprogBytes.rexW]

/-- The indexed load `LOADIDX D, (B, I, 8)` between general-purpose names. -/
theorem encodeLopn_ldx (F W : Nat) (D B I : String) (qB : Nat) (hD : gpOk D = true)
    (hB : gpOk B = true) (hI : gpOk I = true) :
    encodeLopn F W (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) qB
      = encMemMovSibw 1 0x8b (gpNumU D) (gpNumU B) (gpNumU I) 8 := by
  have fD := gpFacts hD
  have fB := gpFacts hB
  have fI := gpFacts hI
  simp (config := { decide := true }) [encodeLopn, encLoadIdx, fD.isGp, fB.isGp, fI.isGp,
    tagShiftExt, aluOpcode, twoByteOpcode, stripWidthTag, adxPrefix]

/-- The indexed store `STOREIDX d, (B, I, 8), V` between general-purpose names. -/
theorem encodeLopn_stx (F W : Nat) (d B I V : String) (qB : Nat) (hB : gpOk B = true)
    (hI : gpOk I = true) (hV : gpOk V = true) :
    encodeLopn F W (.Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V]) qB
      = encMemMovSibw 1 0x89 (gpNumU V) (gpNumU B) (gpNumU I) 8 := by
  have fB := gpFacts hB
  have fI := gpFacts hI
  have fV := gpFacts hV
  simp (config := { decide := true }) [encodeLopn, encStoreIdx, fV.isGp, fB.isGp, fI.isGp,
    tagShiftExt, aluOpcode, twoByteOpcode, stripWidthTag, adxPrefix]

/-- The low multiply `MUL:64 D, D, S` between general-purpose names. -/
theorem encodeLopn_mul (F W : Nat) (D S : String) (qB : Nat) :
    encodeLopn F W (.Lopn [.reg D] "MUL:64" [.reg D, .reg S]) qB
      = enc0FRRw 1 0xaf (gpNumU D) (gpNumU S) := by
  simp (config := { decide := true }) [encodeLopn, tagShiftExt, aluOpcode, twoByteOpcode,
    stripWidthTag, adxPrefix, LprogBytes.rexW]

/-- The widening multiply `MULX H, H, S` with coincident destinations. -/
theorem encodeLopn_mulxS (F W : Nat) (H S : String) (qB : Nat) (hH : gpOk H = true)
    (hS : gpOk S = true) :
    encodeLopn F W (.Lopn [.reg H, .reg H] "MULX" [.reg S]) qB
      = encMulxSameDst (gpNumU H) (gpNumU S) := by
  have fH := gpFacts hH
  have fS := gpFacts hS
  simp (config := { decide := true }) [encodeLopn, fH.notSlot, fH.notMem, fS.notSlot,
    mulxSrcMem?_of_isGpName F W qB fS.isGp]

/-- The widening multiply `MULX L, H, S` with distinct destinations. -/
theorem encodeLopn_mulx (F W : Nat) (L H S : String) (qB : Nat) (hne : (L == H) = false)
    (hL : gpOk L = true) (hH : gpOk H = true) (hS : gpOk S = true) :
    encodeLopn F W (.Lopn [.reg L, .reg H] "MULX" [.reg S]) qB
      = ScalarEncoder.encMulxRR (gpNumU H) (gpNumU L) (gpNumU S) := by
  have fL := gpFacts hL
  have fH := gpFacts hH
  have fS := gpFacts hS
  simp (config := { decide := true }) [encodeLopn, hne, fL.notSlot, fL.notMem, fH.notSlot,
    fH.notMem, fS.notSlot, mulxSrcMem?_of_isGpName F W qB fS.isGp]

/-- The frame-word compare `CMP:64 c, c, q` against the word at the frame offset of `q`. -/
theorem encodeLopn_cmpM (F W : Nat) (c q : String) (qB : Nat) (off : Int)
    (hc : gpOk c = true) (hg : isGpName q = false) (hs : isSpillOrQsave q = true)
    (hoff : spillQsaveOff F W q qB = some off) :
    encodeLopn F W (.Lopn [.reg c] "CMP:64" [.reg c, .reg q]) qB
      = encRspMem 1 0x3b (gpNumU c) off := by
  have fc := gpFacts hc
  simp (config := { decide := true }) [encodeLopn, fc.isGp, hg, hs, hoff, tagShiftExt,
    aluOpcode, twoByteOpcode, stripWidthTag, adxPrefix, LprogBytes.rexW]

/-! ## 4. The decoded pieces of the memory, compare and multiply arms -/

theorem pieceDec_cmpR (c r : String) :
    PieceDec (encAluRRw 1 0x39 (gpNumU c) (gpNumU r), .cmp (phys c) (.reg (phys r))) :=
  fun rest => decodeLinstr_cmpRR _ _ rest (gpNumU_lt_16 c) (gpNumU_lt_16 r)

theorem pieceDec_cmpI (c : String) (k : Nat) (hk : fitsImm8S 1 k = true) :
    PieceDec (encAluImm8 1 7 (gpNumU c) k, .cmp (phys c) (.imm k)) :=
  fun rest => decodeLinstr_aluImm8 7 JInstr.cmp _ _ rest (by decide) (gpNumU_lt_16 c) hk rfl

theorem pieceDec_ldx (D B I : String) (hb5 : gpNumU B &&& 7 ≠ 5) (hi4 : gpNumU I ≠ 4) :
    PieceDec (encMemMovSibw 1 0x8b (gpNumU D) (gpNumU B) (gpNumU I) 8,
      .loadMemIdx (phys D) (phys B) (phys I) 8) :=
  fun rest => decodeLinstr_loadIdx8 _ _ _ rest (gpNumU_lt_16 D) (gpNumU_lt_16 B)
    (gpNumU_lt_16 I) hb5 hi4

theorem pieceDec_stx (V B I : String) (hb5 : gpNumU B &&& 7 ≠ 5) (hi4 : gpNumU I ≠ 4) :
    PieceDec (encMemMovSibw 1 0x89 (gpNumU V) (gpNumU B) (gpNumU I) 8,
      .storeMemIdx (phys B) (phys I) 8 (.reg (phys V))) :=
  fun rest => decodeLinstr_storeIdx8 _ _ _ rest (gpNumU_lt_16 V) (gpNumU_lt_16 B)
    (gpNumU_lt_16 I) hb5 hi4

theorem pieceDec_imul (D S : String) (hD : gpOk D = true) (hS : gpOk S = true) :
    PieceDec (enc0FRRw 1 0xaf (gpNumU D) (gpNumU S), .imul (phys D) (.reg (phys S))) := by
  intro rest
  rw [LprogJInstrBytesAgree.enc0FRRw_one]
  apply decodeLinstr_of_decodeJ1
  have h := roundtrip_imulRR [(phys D, phys D), (phys S, phys S)] (phys D) (phys S) rest
  have eD : ScalarEncoder.gpNum (SailX86Decoder.regName (gpNumU D)) = gpNumU D := gpNum_phys hD
  have eS : ScalarEncoder.gpNum (SailX86Decoder.regName (gpNumU S)) = gpNumU S := gpNum_phys hS
  have hl : List.lookup (SailX86Decoder.regName (gpNumU S))
      [(SailX86Decoder.regName (gpNumU D), SailX86Decoder.regName (gpNumU D)),
        (SailX86Decoder.regName (gpNumU S), SailX86Decoder.regName (gpNumU S))]
      = some (SailX86Decoder.regName (gpNumU S)) := by
    by_cases hDS : SailX86Decoder.regName (gpNumU S) = SailX86Decoder.regName (gpNumU D)
    · simp [List.lookup, hDS]
    · simp [List.lookup, beq_eq_false_iff_ne.mpr hDS]
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, AsmPrinter.regOf, eD, eS,
    phys, hl] using h

theorem regOf_canon (n : Nat) (h : n < 16) :
    AsmPrinter.regOf (canonAlloc ()) (SailX86Decoder.regName n) = SailX86Decoder.regName n := by
  interval_cases n <;> decide

theorem gpNum_regName (n : Nat) (h : n < 16) :
    ScalarEncoder.gpNum (SailX86Decoder.regName n) = n := by
  interval_cases n <;> decide

/-- `MULX %s, %l, %h` with the implicit source `%rdx`. -/
theorem pieceDec_mulx (h l s : Nat) (hh : h < 16) (hl : l < 16) (hs : s < 16) :
    PieceDec (ScalarEncoder.encMulxRR h l s, .mulx (SailX86Decoder.regName h)
      (SailX86Decoder.regName l) (.reg "%rdx") (.reg (SailX86Decoder.regName s))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have hrdx : AsmPrinter.regOf (canonAlloc ()) "%rdx" = "%rdx" := by decide
  have hg : SailX86Decoder.regName (ScalarEncoder.gpNum "%rdx") = "%rdx" := by decide
  have e := roundtrip_mulx (canonAlloc ()) (SailX86Decoder.regName h) (SailX86Decoder.regName l)
    "%rdx" (SailX86Decoder.regName s) rest (by simp only [mulxRdxOk, hrdx]; decide)
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon h hh,
    regOf_canon l hl, regOf_canon s hs, gpNum_regName h hh, gpNum_regName l hl,
    gpNum_regName s hs, hrdx, hg] using e

/-- The scratch register of the widening multiply with coincident destinations is a register
    number, neither the destination, the source, `%rdx` nor the stack register. -/
theorem mulxSameScratch_spec (h s : Nat) :
    mulxSameScratch h s < 16 ∧ mulxSameScratch h s ≠ h ∧ mulxSameScratch h s ≠ s
      ∧ mulxSameScratch h s ≠ 2 ∧ mulxSameScratch h s ≠ 4 := by
  unfold mulxSameScratch
  cases hf : List.find? (fun r => r != h && r != s && r != 2) [1, 6, 7, 8, 9, 10, 11, 0, 3] with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    have h1 := hf 1 (by simp)
    have h6 := hf 6 (by simp)
    have h7 := hf 7 (by simp)
    have h8 := hf 8 (by simp)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at h1 h6 h7 h8
    omega
  | some x =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    simp only [Option.getD_some]
    omega

/-! ## 5. The arms -/

/-- A covered instruction of a physical body on the address machine. -/
inductive AArm where
  /-- A register arm of `DecodePrinted` other than the frame-word moves. -/
  | reg (a : Arm)
  /-- The frame-word store `m q, S`, `m` one of `MOVQ` and `MOV:64`. -/
  | st (m q S : String)
  /-- The frame-word load `m D, q`, `m` one of `MOVQ` and `MOV:64`. -/
  | ld (m D q : String)
  /-- The register compare `CMP:64 c, c, r`. -/
  | cmpR (c r : String)
  /-- The immediate compare `CMP:64 c, c, #k`. -/
  | cmpI (c : String) (k : Nat)
  /-- The frame-word compare `CMP:64 c, c, q`. -/
  | cmpM (c q : String)
  /-- The indexed load `LOADIDX D, (B, I, 8)`. -/
  | ldx (D B I : String)
  /-- The indexed store `STOREIDX d, (B, I, 8), V`; the destination `d` names the array and
      is not a machine operand. -/
  | stx (d B I V : String)
  /-- The low multiply `MUL:64 D, D, S`. -/
  | mul (D S : String)
  /-- The widening multiply `MULX H, H, S` with coincident destinations: `H` receives the
      high word of the product of `RDX` and `S`. -/
  | mulxS (H S : String)
  /-- The widening multiply `MULX L, H, S` with distinct destinations: `L` receives the low
      and `H` the high word of the product of `RDX` and `S`. -/
  | mulx (L H S : String)

/-- The instruction of an arm. -/
def AArm.instr : AArm → LinstrR
  | .reg a => a.instr
  | .st m q S => .Lopn [.reg q] m [.reg S]
  | .ld m D q => .Lopn [.reg D] m [.reg q]
  | .cmpR c r => .Lopn [.reg c] "CMP:64" [.reg c, .reg r]
  | .cmpI c k => .Lopn [.reg c] "CMP:64" [.reg c, .imm k]
  | .cmpM c q => .Lopn [.reg c] "CMP:64" [.reg c, .reg q]
  | .ldx D B I => .Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]
  | .stx d B I V => .Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V]
  | .mul D S => .Lopn [.reg D] "MUL:64" [.reg D, .reg S]
  | .mulxS H S => .Lopn [.reg H, .reg H] "MULX" [.reg S]
  | .mulx L H S => .Lopn [.reg L, .reg H] "MULX" [.reg S]

/-- The register arms of `DecodePrinted`: every arm but the frame-word moves. -/
def regArmB : Arm → Bool
  | .store .. => false
  | .load .. => false
  | _ => true

/-- An instruction whose mnemonic is none of those the address machine reads apart:
    `MULX`, `LOADIDX`, `STOREIDX` and the width-carrying casts (`castTagW`). -/
def plainB : LinstrR → Bool
  | .Lopn _ o _ => o != "MULX" && o != "LOADIDX" && o != "STOREIDX" && (castTagW o).isNone
  | _ => true

/-- The scratch register of the widening multiply `MULX H, H, S`. -/
def scrOf (H S : String) : Nat := mulxSameScratch (gpNumU H) (gpNumU S)

/-- The byte pieces of an arm. -/
def AArm.pieces (P : Params) : AArm → List (List (BitVec 8) × JInstr 64)
  | .reg a => a.pieces P
  | .st m q S => Arm.pieces P (.store m q S)
  | .ld m D q => Arm.pieces P (.load m D q)
  | .cmpR c r => [(encAluRRw 1 0x39 (gpNumU c) (gpNumU r), .cmp (phys c) (.reg (phys r)))]
  | .cmpI c k => [(encAluImm8 1 7 (gpNumU c) k, .cmp (phys c) (.imm k))]
  | .cmpM c q => [(encRspMem 1 0x3b (gpNumU c) (slotOff P q),
      .cmpMem (phys c) "%rsp" (slotOff P q))]
  | .ldx D B I => [(encMemMovSibw 1 0x8b (gpNumU D) (gpNumU B) (gpNumU I) 8,
      .loadMemIdx (phys D) (phys B) (phys I) 8)]
  | .stx _ B I V => [(encMemMovSibw 1 0x89 (gpNumU V) (gpNumU B) (gpNumU I) 8,
      .storeMemIdx (phys B) (phys I) 8 (.reg (phys V)))]
  | .mul D S => [(enc0FRRw 1 0xaf (gpNumU D) (gpNumU S), .imul (phys D) (.reg (phys S)))]
  | .mulxS H S =>
      [(encRspMem 1 0x89 (scrOf H S) cmovRedZone,
          .storeMem "%rsp" cmovRedZone (.reg (SailX86Decoder.regName (scrOf H S)))),
        (ScalarEncoder.encMulxRR (gpNumU H) (scrOf H S) (gpNumU S),
          .mulx (phys H) (SailX86Decoder.regName (scrOf H S)) (.reg "%rdx") (.reg (phys S))),
        (encRspMem 1 0x8b (scrOf H S) cmovRedZone,
          .loadMem (SailX86Decoder.regName (scrOf H S)) "%rsp" cmovRedZone)]
  | .mulx L H S => [(ScalarEncoder.encMulxRR (gpNumU H) (gpNumU L) (gpNumU S),
      .mulx (phys H) (phys L) (.reg "%rdx") (.reg (phys S)))]

/-- The machine instructions of an arm. -/
def AArm.js (P : Params) (a : AArm) : List (JInstr 64) := (a.pieces P).map Prod.snd

/-- **The conditions of an arm** under the body parameters `P`: general-purpose operands; a
    frame word with an offset in `rel32` range, whose word a load or compare reads disjoint
    from the red-zone word; a frame-word move at `MOVQ` or `MOV:64`; an immediate compare in
    the sign-extended `imm8` range; an indexed access whose base and index registers have a
    SIB encoding; distinct destinations of the widening multiply `mulx`. -/
def AArm.ok (P : Params) : AArm → Bool
  | .reg a => regArmB a && a.ok P [] && plainB a.instr
  | .st m q S => gpOk S && !gpOk q && (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome
      && dispOk32 (slotOff P q) && isMovM m
  | .ld m D q => gpOk D && !gpOk q && (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome
      && dispOk32 (slotOff P q) && sepB cmovRedZone (slotOff P q) && isMovM m
  | .cmpR c r => gpOk c && gpOk r
  | .cmpI c k => gpOk c && fitsImm8S 1 k
  | .cmpM c q => gpOk c && !isGpName q && isSpillOrQsave q
      && (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome && dispOk32 (slotOff P q)
      && sepB cmovRedZone (slotOff P q)
  | .ldx D B I => gpOk D && gpOk B && gpOk I && (gpNumU B &&& 7 != 5) && (gpNumU I != 4)
  | .stx _ B I V => gpOk B && gpOk I && gpOk V && (gpNumU B &&& 7 != 5) && (gpNumU I != 4)
  | .mul D S => gpOk D && gpOk S
  | .mulxS H S => gpOk H && gpOk S
  | .mulx L H S => gpOk L && gpOk H && gpOk S && L != H

theorem pieceDec_single {q : List (BitVec 8) × JInstr 64} (h : PieceDec q) :
    ∀ p ∈ [q], PieceDec p := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

/-- **The bytes of an arm.** For an arm whose conditions hold, the encoder lays down the
    concatenation of its pieces, and each piece decodes in front of every continuation. -/
theorem AArm.bytes (P : Params) (a : AArm) (h : a.ok P = true) :
    encodeLopn P.frame P.spillW a.instr P.qsaveB = (a.pieces P).flatMap Prod.fst
      ∧ ∀ q ∈ a.pieces P, PieceDec q := by
  cases a with
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact a.bytes P [] h.1.2
  | st m q S =>
    exact Arm.bytes P [] (.store m q S) (by
      simp only [AArm.ok, Bool.and_eq_true] at h
      simp [Arm.ok, h])
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hD, -⟩, hsome⟩, hd⟩, -⟩, hm⟩ := h
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    refine ⟨?_, ?_⟩
    · simp [AArm.instr, AArm.pieces, Arm.pieces, encodeLopn_movM _ _ _ _ _ _ hm,
        encTwoAddr_load _ _ _ _ _ _ _ _ hoff hD, hso, memSrcOp]
    · simp only [AArm.pieces, Arm.pieces, List.mem_singleton]
      rintro p rfl rest
      exact decodeLinstr_rspLoad _ _ rest (gpNumU_lt_16 D) hd
  | cmpR c r =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact ⟨by simp [AArm.instr, AArm.pieces, encodeLopn_cmpR _ _ _ _ _ h.1 h.2],
      pieceDec_single (pieceDec_cmpR c r)⟩
  | cmpI c k =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact ⟨by simp [AArm.instr, AArm.pieces, encodeLopn_cmpI _ _ _ _ _ h.1 h.2],
      pieceDec_single (pieceDec_cmpI c k h.2)⟩
  | cmpM c q =>
    simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hc, hg⟩, hs⟩, hsome⟩, hd⟩, -⟩ := h
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    rw [hso] at hd
    refine ⟨?_, ?_⟩
    · simp [AArm.instr, AArm.pieces, encodeLopn_cmpM _ _ _ _ _ _ hc hg hs hoff, hso]
    · simp only [AArm.pieces, List.mem_singleton]
      rintro p rfl rest
      rw [hso]
      exact decodeLinstr_rspCmp _ _ rest (gpNumU_lt_16 c) hd
  | ldx D B I =>
    simp only [AArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hD, hB⟩, hI⟩, hb5⟩, hi4⟩ := h
    exact ⟨by simp [AArm.instr, AArm.pieces, encodeLopn_ldx _ _ _ _ _ _ hD hB hI],
      pieceDec_single (pieceDec_ldx D B I hb5 hi4)⟩
  | stx d B I V =>
    simp only [AArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hB, hI⟩, hV⟩, hb5⟩, hi4⟩ := h
    exact ⟨by simp [AArm.instr, AArm.pieces, encodeLopn_stx _ _ _ _ _ _ _ hB hI hV],
      pieceDec_single (pieceDec_stx V B I hb5 hi4)⟩
  | mul D S =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact ⟨by simp [AArm.instr, AArm.pieces, encodeLopn_mul],
      pieceDec_single (pieceDec_imul D S h.1 h.2)⟩
  | mulxS H S =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨hlt, -, -, -, -⟩ := mulxSameScratch_spec (gpNumU H) (gpNumU S)
    refine ⟨?_, ?_⟩
    · simp [AArm.instr, AArm.pieces, encodeLopn_mulxS _ _ _ _ _ h.1 h.2, encMulxSameDst,
        scrOf]
    · simp only [AArm.pieces, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl)
      · exact fun rest => decodeLinstr_rspStore (scrOf H S) cmovRedZone rest hlt (by decide)
      · exact pieceDec_mulx _ _ _ (gpNumU_lt_16 H) hlt (gpNumU_lt_16 S)
      · exact fun rest => decodeLinstr_rspLoad (scrOf H S) cmovRedZone rest hlt (by decide)
  | mulx L H S =>
    simp only [AArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨hL, hH⟩, hS⟩, hne⟩ := h
    exact ⟨by simp [AArm.instr, AArm.pieces,
        encodeLopn_mulx _ _ _ _ _ _ (beq_eq_false_iff_ne.mpr hne) hL hH hS],
      pieceDec_single (pieceDec_mulx _ _ _ (gpNumU_lt_16 H) (gpNumU_lt_16 L) (gpNumU_lt_16 S))⟩

/-! ## 6. The simulation of one arm -/

/-- The tagged instruction the address machine steps for an arm: the indexed accesses at the
    load and store tags, the widening multiply at its width `MULX:64`. -/
def AArm.li : AArm → LinstrRM
  | .ldx D B I => (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8], .load 64 0)
  | .stx d B I V => (.Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V], .store 64 0)
  | .mulxS H S => (.Lopn [.reg H, .reg H] (withWidthTag 64 "MULX") [.reg S], .reg none)
  | .mulx L H S => (.Lopn [.reg L, .reg H] (withWidthTag 64 "MULX") [.reg S], .reg none)
  | a => (a.instr, .reg none)

/-- The compare arms. -/
def cmpArmB : AArm → Bool
  | .cmpR .. => true
  | .cmpI .. => true
  | .cmpM .. => true
  | _ => false

theorem fstepA_lpc (frame : String → Option (BitVec 64)) (i : LinstrRM) (s s' : LstateA)
    (zf z' : Bool) (h : fstepA frame i s zf = some (s', z')) : s'.reg.lpc = s.reg.lpc + 1 := by
  have hreg : ∀ j, regStepA j s zf = some (s', z') → s'.reg.lpc = s.reg.lpc + 1 := by
    intro j hj
    unfold regStepA at hj
    cases hf : fstepF j { reg := s.reg, cf := s.cf, of := s.of } zf with
    | none => rw [hf] at hj; cases hj
    | some bz =>
      rw [hf] at hj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
      exact fstepF_lpc_succ j _ bz.1 zf bz.2 hf
  unfold fstepA at h
  repeat' split at h
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl)
    | exact hreg _ h
    | simp at h

theorem aluArm_noWrite {m : String} {op : Nat} {mk : String → JOperand → JInstr 64}
    (h : aluArm m = some (op, mk)) (D : String) (o : JOperand) : noWriteB (mk D o) = true := by
  unfold aluArm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> rfl

/-- The register arms write no memory, move no frame slot, and keep the written frame words. -/
theorem regArm_facts {P : Params} {a : Arm} (hr : regArmB a = true) (h : a.ok P [] = true) :
    (a.js P).all noWriteB = true
      ∧ (∀ d s, slotMov? a.instr = some (d, s) → gpOk d = true ∧ gpOk s = true)
      ∧ a.post P [] = [] := by
  cases a with
  | movRR m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    refine ⟨by simp [Arm.js, Arm.pieces, noWriteB], fun d s hs => ?_, rfl⟩
    simp only [Arm.instr, slotMov?] at hs
    split at hs
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs); exact ⟨h.1.2, h.2⟩
    · cases hs
  | movRI D v => exact ⟨by simp [Arm.js, Arm.pieces, noWriteB], fun d s hs => by
      simp [Arm.instr, slotMov?] at hs, rfl⟩
  | store => simp [regArmB] at hr
  | load => simp [regArmB] at hr
  | alu m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨op, mk⟩, hop⟩ := Option.isSome_iff_exists.mp h.1.1
    exact ⟨by simp [Arm.js, Arm.pieces, hop, aluArm_noWrite hop], fun d s hs => by
      simp [Arm.instr, slotMov?] at hs, rfl⟩
  | aluI m D v =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨op, mk⟩, hop⟩ := Option.isSome_iff_exists.mp h.1.1
    exact ⟨by simp [Arm.js, Arm.pieces, hop, aluArm_noWrite hop], fun d s hs => by
      simp [Arm.instr, slotMov?] at hs, rfl⟩
  | shr m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨?_, fun d s hs => ?_, rfl⟩
    · by_cases hDS : D = S <;> by_cases hl : tagShl m = true <;>
        simp [Arm.js, Arm.pieces, tagShMk, hDS, hl, noWriteB]
    · simp only [Arm.instr, slotMov?] at hs
      split at hs
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs); exact ⟨hD, hS⟩
      · cases hs
  | shl0 m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨?_, fun d s hs => ?_, rfl⟩
    · by_cases hDS : D = S <;> simp [Arm.js, Arm.pieces, hDS, noWriteB]
    · simp only [Arm.instr, slotMov?] at hs
      split at hs
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs); exact ⟨hD, hS⟩
      · cases hs
  | shI m D k =>
    refine ⟨?_, fun d s hs => by simp [Arm.instr, slotMov?] at hs, rfl⟩
    simp only [Arm.js, Arm.pieces, shIMk, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true]
    split_ifs <;> rfl
  | lea D B X sc => exact ⟨by simp [Arm.js, Arm.pieces, noWriteB], fun d s hs => by
      simp [Arm.instr, slotMov?] at hs, rfl⟩

/-- A register arm whose conditions hold compares against a general-purpose name only. -/
theorem regArm_slotCmp {P : Params} {a : Arm} (h : a.ok P [] = true) {d x q : String}
    (hk : slotCmp? a.instr = some (d, x, q)) : gpOk q = true := by
  cases a with
  | alu m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    by_cases hm : m = "CMP:64" <;> simp [Arm.instr, slotCmp?, hm] at hk
    obtain ⟨-, -, rfl⟩ := hk
    exact h.2
  | _ => simp [Arm.instr, slotCmp?] at hk

/-- A general-purpose name is no cell name. -/
theorem cellParts?_gp {r : String} (h : gpOk r = true) : cellParts? r = none := by
  have hm := mem_gpList h
  simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

/-- A register arm of `DecodePrintedAddr` accesses no cell. -/
theorem regArm_cell {P : Params} {a : Arm} (hr : regArmB a = true) (h : a.ok P [] = true) :
    cellA? a.instr = none := by
  cases a with
  | shr m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    simp [Arm.instr, cellA?, cellParts?_gp hD, cellParts?_gp hS]
  | shl0 m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    simp [Arm.instr, cellA?, cellParts?_gp hD, cellParts?_gp hS]
  | movRR m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨-, hD⟩, hS⟩ := h
    simp [Arm.instr, cellA?, cellParts?_gp hD, cellParts?_gp hS]
  | store => simp [regArmB] at hr
  | load => simp [regArmB] at hr
  | _ => simp [Arm.instr, cellA?]

/-- A register arm is no immediate move into a frame slot. -/
theorem regArm_slotImm {P : Params} {a : Arm} (rsp : BitVec 64) (h : a.ok P [] = true) :
    slotImm? (frameP P rsp) a.instr = none := by
  cases a with
  | movRI D v =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    simp [Arm.instr, slotImm?, frameP_gp h.1.1]
  | _ => simp [Arm.instr, slotImm?]

/-- **A register arm.** -/
theorem sim_reg (P : Params) (rsp : BitVec 64) (a : Arm) (hr : regArmB a = true)
    (h : a.ok P [] = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (a.instr, .reg none) s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa (a.js P)) s' := by
  obtain ⟨hjs, hslot, hpost⟩ := regArm_facts hr h
  have hsim := Arm.sim P [] rsp a h
  rw [hpost] at hsim
  obtain ⟨s', zf', h1, h2, -⟩ := simA_of_decSim
    (fun s zf => fstepA_of_reg (frameP P rsp) (i := (a.instr, .reg none)) rfl
      (fun d x hs => ⟨frameP_gp (hslot d x hs).2, frameP_gp (hslot d x hs).1⟩)
      (fun d x q hk => frameP_gp (regArm_slotCmp h hk)) (regArm_cell hr h)
      (by cases a <;> simp [Arm.instr, slotCarry?]) (regArm_slotImm rsp h)
      (by cases a <;> simp [Arm.instr, slotCmov?]) s zf)
    hjs hsim sa s zf hc
  exact ⟨s', zf', h1, h2⟩

/-- A write of `v` to the general-purpose name `D` and to its machine register preserves the
    correspondence when the memories still agree outside the red-zone word. -/
theorem ACorr.write {rsp : BitVec 64} {sa sa' : AState} {s s' : LstateA}
    (h : ACorr rsp sa s) {D : String} (hD : gpOk D = true) (v : BitVec 64)
    (hregs : ∀ r, sa'.regs r = if r = phys D then v else sa.regs r)
    (hmem : ∀ x, ¬ InRange8 (redW rsp) x → s'.mem x = sa'.mem x)
    (hb : ∀ r, r ≠ D → s'.reg.getW r 64 = s.reg.getW r 64)
    (hbD : s'.reg.getW D 64 = some v) : ACorr rsp sa' s' where
  regs r hr := by
    by_cases hrD : r = D
    · subst hrD; rw [hbD, hregs, if_pos rfl]
    · rw [hb r hrD, h.regs r hr, hregs, if_neg (fun e => hrD (phys_inj hr hD e))]
  sp := by rw [hregs, if_neg (fun e => (gpFacts hD).physNe e.symm)]; exact h.sp
  mem := hmem

/-- Registers unchanged on both sides preserve the correspondence when the memories still
    agree outside the red-zone word. -/
theorem ACorr.keep {rsp : BitVec 64} {sa sa' : AState} {s s' : LstateA}
    (h : ACorr rsp sa s) (hregs : sa'.regs = sa.regs)
    (hb : ∀ r, s'.reg.getW r 64 = s.reg.getW r 64)
    (hmem : ∀ x, ¬ InRange8 (redW rsp) x → s'.mem x = sa'.mem x) : ACorr rsp sa' s' where
  regs r hr := by rw [hb, hregs]; exact h.regs r hr
  sp := by rw [hregs]; exact h.sp
  mem := hmem

theorem getW_setReg_nextPcN (b : LstateN) (D r : String) (v : BitVec 64) :
    (b.setReg D v).nextPc.getW r 64 = if r = D then some v else b.getW r 64 := by
  rw [LstateN.getW_nextPc]
  split
  · rename_i h; subst h; exact LstateN.getW_setReg_same _ _ _
  · rename_i h; exact LstateN.getW_setReg_other _ _ _ _ _ h

/-- **The frame-word store.** -/
theorem sim_st (P : Params) (rsp : BitVec 64) (m q S : String)
    (h : (AArm.st m q S).ok P = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.st m q S).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.st m q S).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hS, -⟩, hsome⟩, -⟩, hm⟩ := h
  have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
    simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm; exact hm.symm
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
  have hso : slotOff P q = off := by simp [slotOff, hoff]
  have hjs : (AArm.st m q S).js P = [.storeMem "%rsp" off (.reg (phys S))] := by
    simp [AArm.js, AArm.pieces, Arm.pieces, hso]
  rw [hjs]
  obtain ⟨hregs, hmem⟩ := evalInstrA_storeMem_eq sa "%rsp" (phys S) off
  refine ⟨⟨s.reg.nextPc, write64 s.mem (rsp + BitVec.ofInt 64 off) (sa.regs (phys S)), s.cf,
      s.of⟩, zf, ?_,
    hc.keep (sa' := evalInstrA sa _) hregs (fun r => LstateN.getW_nextPc _ _ _)
    (fun x hx => ?_)⟩
  · simp [AArm.li, AArm.instr, fstepA, slotMov?, hm', frameP, (gpFacts hS).off, hoff,
      hc.regs S hS]
  · show write64 s.mem (rsp + BitVec.ofInt 64 off) (sa.regs (phys S)) x = _
    rw [hmem, hc.sp]
    exact agree_write64 hc.mem _ _ x hx

/-- **The frame-word load.** -/
theorem sim_ld (P : Params) (rsp : BitVec 64) (m D q : String)
    (h : (AArm.ld m D q).ok P = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.ld m D q).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.ld m D q).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hD, -⟩, hsome⟩, -⟩, hsep⟩, hm⟩ := h
  have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
    simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm; exact hm.symm
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
  have hso : slotOff P q = off := by simp [slotOff, hoff]
  rw [hso] at hsep
  have hjs : (AArm.ld m D q).js P = [.loadMem (phys D) "%rsp" off] := by
    simp [AArm.js, AArm.pieces, Arm.pieces, hso]
  rw [hjs]
  obtain ⟨hregs, hmem⟩ := evalInstrA_loadMem_eq sa (phys D) "%rsp" off
  have hdis : Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 off) := by
    simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsep
    exact disjoint8_add_ofInt rsp cmovRedZone off hsep.1 hsep.2
  have hrd := hc.read64_eq hdis
  refine ⟨⟨(s.reg.setReg D (read64 s.mem (rsp + BitVec.ofInt 64 off))).nextPc, s.mem, s.cf,
      s.of⟩, zf, ?_, hc.write (sa' := evalInstrA sa _) hD _
      (fun r => by rw [hregs, hc.sp]) (fun x hx => by rw [hmem]; exact hc.mem x hx)
      (fun r hr => by rw [getW_setReg_nextPcN, if_neg hr])
      (by rw [getW_setReg_nextPcN, if_pos rfl, hrd])⟩
  simp [AArm.li, AArm.instr, fstepA, slotMov?, hm', frameP, hoff]

/-- The machine compare writes no register and no memory, and sets the zero flag to the
    equality of its operands. -/
theorem evalInstrA_cmp (sa : AState) (X : String) (o : JOperand) :
    (evalInstrA sa (.cmp X o)).regs = sa.regs ∧ (evalInstrA sa (.cmp X o)).mem = sa.mem
      ∧ (evalInstrA sa (.cmp X o)).flags.zf.getD false = (sa.regs X == o.eval sa.view) := by
  refine ⟨rfl, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩
  show (some (ZF_of_word (sa.regs X - o.eval sa.view))).getD false = _
  rw [ZF_of_word_sub]
  rfl

/-- **The compare.** The flag compare `CMP:64 c, c, o` of an operand `o` that reads `vo`,
    against the machine compare of `phys c` with an operand that evaluates to `vo`. -/
theorem sim_cmp (P : Params) (rsp : BitVec 64) (c : String) (o : LOperand) (o' : JOperand)
    (hcg : gpOk c = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorr rsp sa s)
    (ho : evalOperandN s.reg 64 o = some (o'.eval sa.view))
    (hq : ∀ q, o = .reg q → frameP P rsp q = none) :
    ∃ s' zf', fstepA (frameP P rsp) (.Lopn [.reg c] "CMP:64" [.reg c, o], .reg none) s zf
        = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa [.cmp (phys c) o']) s'
      ∧ (aMachine.runBlock sa [.cmp (phys c) o']).flags.zf.getD false = zf' := by
  have hw : withWidthTag 64 "CMP" = "CMP:64" := by decide
  have hi : (LinstrR.Lopn [.reg c] "CMP:64" [.reg c, o], MemTag.reg none) = cmpRI c o := by
    simp only [cmpRI, hw]
  rw [hi, fstepA_of_reg (frameP P rsp) (i := cmpRI c o) rfl (fun d x hs => by
    cases o <;> simp [cmpRI, slotMov?] at hs) (fun d x q hk => by
    cases o with
    | reg r =>
      simp only [cmpRI, hw, slotCmp?, if_true, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨-, -, rfl⟩ := hk
      exact hq r rfl
    | _ => simp [cmpRI, slotCmp?] at hk) (by cases o <;> simp [cmpRI, cellA?, hw])
    (by cases o <;> simp [cmpRI, slotCarry?]) (by cases o <;> simp [cmpRI, slotImm?])
    (by cases o <;> simp [cmpRI, slotCmov?]) s zf]
  have hf := fstepF_cmpRI c o (baseOf s) zf _ _ (hc.regs c hcg) ho
  obtain ⟨e1, e2, e3⟩ := evalInstrA_cmp sa (phys c) o'
  refine ⟨⟨s.reg.nextPc, s.mem, s.cf, s.of⟩, sa.regs (phys c) == o'.eval sa.view, ?_, ?_, ?_⟩
  · show (fstepF (cmpRI c o) (baseOf s) zf).map _ = _
    rw [hf]
    rfl
  · exact hc.keep e1 (fun r => LstateN.getW_nextPc _ _ _) (fun x hx => by
      show s.mem x = (evalInstrA sa _).mem x
      rw [e2]; exact hc.mem x hx)
  · exact e3

/-- **The frame-word compare.** The flag compare `CMP:64 c, c, q`, which the address machine
    takes against the memory word at the frame address of `q`, against the machine compare of
    `phys c` with the word at the frame offset of `q`. -/
theorem sim_cmpM (P : Params) (rsp : BitVec 64) (c q : String)
    (h : (AArm.cmpM c q).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.cmpM c q).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.cmpM c q).js P)) s'
      ∧ (aMachine.runBlock sa ((AArm.cmpM c q).js P)).flags.zf.getD false = zf' := by
  simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hcg, -⟩, -⟩, hsome⟩, -⟩, hsep⟩ := h
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
  have hso : slotOff P q = off := by simp [slotOff, hoff]
  rw [hso] at hsep
  have hdis : Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 off) := by
    simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsep
    exact disjoint8_add_ofInt rsp cmovRedZone off hsep.1 hsep.2
  have hrd := hc.read64_eq hdis
  set v := read64 s.mem (rsp + BitVec.ofInt 64 off) with hv
  have hjs : (AArm.cmpM c q).js P = [.cmpMem (phys c) "%rsp" off] := by
    simp [AArm.js, AArm.pieces, hso]
  rw [hjs]
  -- the machine compare against the frame word
  have e1 : (evalInstrA sa (.cmpMem (phys c) "%rsp" off)).regs = sa.regs := by
    simp [evalInstrA, evalInstr, JState.writeB5, AState.view]
  have e2 : (evalInstrA sa (.cmpMem (phys c) "%rsp" off)).mem = sa.mem := rfl
  have e3 : (evalInstrA sa (.cmpMem (phys c) "%rsp" off)).flags.zf.getD false
      = (sa.regs (phys c) == v) := by
    show (some (ZF_of_word (sa.regs (phys c)
      - read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 off)))).getD false = _
    rw [ZF_of_word_sub, hc.sp, ← hrd]
    rfl
  -- the address machine compare against the frame word
  have hstep : fstepA (frameP P rsp) (AArm.cmpM c q).li s zf
      = regStepA (cmpRI c (.imm v.toNat)) s zf := by
    simp [AArm.li, AArm.instr, fstepA, slotMov?, slotCmp?, frameP, hoff, cmpRI, hv,
      show withWidthTag 64 "CMP" = "CMP:64" by decide]
  have hf := fstepF_cmpRI c (.imm v.toNat) (baseOf s) zf _ v (hc.regs c hcg)
    (by simp [evalOperandN])
  refine ⟨⟨s.reg.nextPc, s.mem, s.cf, s.of⟩, sa.regs (phys c) == v, ?_, ?_, ?_⟩
  · rw [hstep]
    show (fstepF (cmpRI c (.imm v.toNat)) (baseOf s) zf).map _ = _
    rw [hf]
    rfl
  · exact hc.keep e1 (fun r => LstateN.getW_nextPc _ _ _) (fun x hx => by
      show s.mem x = (evalInstrA sa _).mem x
      rw [e2]; exact hc.mem x hx)
  · exact e3

theorem ofInt_eight_mul (n : Nat) :
    BitVec.ofInt 64 (8 * (n : Int)) = BitVec.ofNat 64 (8 * n) := by
  rw [show (8 * (n : Int)) = ((8 * n : Nat) : Int) by push_cast; ring, BitVec.ofInt_natCast]

theorem evalInstrA_loadMemIdx_eq (sa : AState) (D B I : String) :
    (∀ r, (evalInstrA sa (.loadMemIdx D B I 8)).regs r = if r = D then
        read64 sa.mem (sa.regs B + BitVec.ofNat 64 (8 * (sa.regs I).toNat)) else sa.regs r)
      ∧ (evalInstrA sa (.loadMemIdx D B I 8)).mem = sa.mem := by
  refine ⟨fun r => ?_, evalInstrA_mem_of_noWriteB sa _ rfl⟩
  by_cases hr : r = D <;>
    simp [evalInstrA, evalInstr, JState.setReg, AState.view, JState.loadIdx, JState.load, hr,
      x86_MOV, ofInt_eight_mul]

theorem evalInstrA_storeMemIdx_eq (sa : AState) (B I V : String) :
    (evalInstrA sa (.storeMemIdx B I 8 (.reg V))).regs = sa.regs
      ∧ (evalInstrA sa (.storeMemIdx B I 8 (.reg V))).mem
        = write64 sa.mem (sa.regs B + BitVec.ofNat 64 (8 * (sa.regs I).toNat)) (sa.regs V) := by
  refine ⟨?_, ?_⟩ <;>
    simp [evalInstrA, evalInstr, JState.storeIdx, JState.store, AState.view, writeAddr,
      writeVal, JOperand.eval, ofInt_eight_mul, x86_MOV]

/-- **The indexed load**, at an address whose eight bytes are disjoint from the red-zone
    word. -/
theorem sim_ldx (P : Params) (rsp : BitVec 64) (D B I : String)
    (h : (AArm.ldx D B I).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorr rsp sa s)
    (hsafe : ∀ p vi, s.reg.getW B 64 = some p → s.reg.getW I 64 = some vi →
      Disjoint8 (redW rsp) (p + BitVec.ofNat 64 (8 * vi.toNat))) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.ldx D B I).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.ldx D B I).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hD, hB⟩, hI⟩, -⟩, -⟩ := h
  have hjs : (AArm.ldx D B I).js P = [.loadMemIdx (phys D) (phys B) (phys I) 8] := rfl
  rw [hjs]
  obtain ⟨hregs, hmem⟩ := evalInstrA_loadMemIdx_eq sa (phys D) (phys B) (phys I)
  set a := sa.regs (phys B) + BitVec.ofNat 64 (8 * (sa.regs (phys I)).toNat) with ha
  have hrd := hc.read64_eq (hsafe _ _ (hc.regs B hB) (hc.regs I hI))
  refine ⟨⟨(s.reg.setReg D (read64 s.mem a)).nextPc, s.mem, s.cf, s.of⟩, zf, ?_,
    hc.write (sa' := evalInstrA sa _) hD _ (fun r => hregs r)
      (fun x hx => by rw [hmem]; exact hc.mem x hx)
      (fun r hr => by rw [getW_setReg_nextPcN, if_neg hr])
      (by rw [getW_setReg_nextPcN, if_pos rfl, hrd])⟩
  simp [AArm.li, fstepA, loadIdxA?, hc.regs B hB, hc.regs I hI, ha]

/-- **The indexed store.** -/
theorem sim_stx (P : Params) (rsp : BitVec 64) (d B I V : String)
    (h : (AArm.stx d B I V).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.stx d B I V).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.stx d B I V).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hB, hI⟩, hV⟩, -⟩, -⟩ := h
  have hjs : (AArm.stx d B I V).js P = [.storeMemIdx (phys B) (phys I) 8 (.reg (phys V))] := rfl
  rw [hjs]
  obtain ⟨hregs, hmem⟩ := evalInstrA_storeMemIdx_eq sa (phys B) (phys I) (phys V)
  set a := sa.regs (phys B) + BitVec.ofNat 64 (8 * (sa.regs (phys I)).toNat) with ha
  refine ⟨⟨s.reg.nextPc, write64 s.mem a (sa.regs (phys V)), s.cf, s.of⟩, zf, ?_,
    hc.keep (sa' := evalInstrA sa _) hregs (fun r => LstateN.getW_nextPc _ _ _)
      (fun x hx => ?_)⟩
  · simp [AArm.li, fstepA, storeIdxA?, hc.regs B hB, hc.regs I hI, hc.regs V hV, ha]
  · show write64 s.mem a (sa.regs (phys V)) x = (evalInstrA sa _).mem x
    rw [hmem]
    exact agree_write64 hc.mem _ _ x hx

/-- The low multiply `MUL:64 D, D, S` against `imul %S, %D`, on the identity
    correspondence. -/
theorem decSim_mulP (rsp : BitVec 64) (D S : String) (hD : gpOk D = true)
    (hS : gpOk S = true) :
    DecSim (PCorr [] rsp) (PCorr [] rsp) [binRegI "MUL:64" D D S]
      [.imul (phys D) (.reg (phys S))] :=
  DecSim.single fun sa b zf hc =>
    ⟨withALUFlags (binRegI "MUL:64" D D S) b
        ((b.setReg D (sa.regs (phys D) * sa.regs (phys S))).nextPc), zf, by
      rw [fstepF_binRegI "MUL:64" "MUL" D D S stripWidthTag_MUL64 (by decide +kernel)
        (by decide) (by decide) (by decide) b zf _ (hc.regs D hD), hc.regs S hS,
        Option.bind_some]
      rfl,
      hc.write hD (sa.regs (phys D) * sa.regs (phys S)) (fun _ => rfl) rfl
        (fun r hr => by rw [withALUFlags_reg, getW_setReg_nextPc, if_neg hr])
        (by rw [withALUFlags_reg, getW_setReg_nextPc, if_pos rfl])⟩

/-- **The low multiply.** -/
theorem sim_mul (P : Params) (rsp : BitVec 64) (D S : String)
    (h : (AArm.mul D S).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.mul D S).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.mul D S).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true] at h
  obtain ⟨s', zf', h1, h2, -⟩ := simA_of_decSim (frame := frameP P rsp)
    (i := binRegI "MUL:64" D D S)
    (fun s zf => fstepA_of_reg (frameP P rsp) rfl (fun d x hs => by
      simp [binRegI, slotMov?] at hs) (fun d x q hk => by simp [binRegI, slotCmp?] at hk)
      (by simp [binRegI, cellA?]) (by simp [binRegI, slotCarry?]) (by simp [binRegI, slotImm?])
      (by simp [binRegI, slotCmov?]) s zf)
    rfl (decSim_mulP rsp D S h.1 h.2) sa s zf hc
  exact ⟨s', zf', h1, h2⟩

/-- The flag machine steps the widening multiply `MULX:64 L, H, S` by `wideStep`. -/
theorem fstepF_mulx (L H S : String) (b : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg L, .reg H] (withWidthTag 64 "MULX") [.reg S], .reg none) b zf
      = (wideStep (.mulx L H (.reg S)) b).map (fun t => (t, zf)) := by
  have hw : wideArgs? ((.Lopn [.reg L, .reg H] (withWidthTag 64 "MULX") [.reg S] : LinstrR),
      MemTag.reg none) = some (.mulx L H (.reg S)) := by
    simp only [wideArgs?, true_or, if_true]
  unfold fstepF stepMemF
  simp only [cmpArgs?, movRegArgs?,
    JasminLsemExportRewrites.lsemStepMem_of_wideArgs hw]
  rw [show carryArgs? ((.Lopn [.reg L, .reg H] (withWidthTag 64 "MULX") [.reg S] : LinstrR),
      MemTag.reg none) = none from rfl, hw]

/-- The flag machine steps the widening multiply `MULX:64 H, H, S` by `wideStep`. -/
theorem fstepF_mulxS (H S : String) (b : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg H, .reg H] (withWidthTag 64 "MULX") [.reg S], .reg none) b zf
      = (wideStep (.mulx H H (.reg S)) b).map (fun t => (t, zf)) :=
  fstepF_mulx H H S b zf

theorem regName_ne_of_ne {m n : Nat} (hm : m < 16) (hn : n < 16) (h : m ≠ n) :
    SailX86Decoder.regName m ≠ SailX86Decoder.regName n := fun e =>
  h (by rw [← gpNum_regName m hm, ← gpNum_regName n hn, e])

/-- **The widening multiply with coincident destinations.** The machine saves the scratch
    register in the red-zone word, multiplies, and restores the scratch register: the
    registers end as the flag machine's, and the memories still agree outside the red-zone
    word. -/
theorem sim_mulxS (P : Params) (rsp : BitVec 64) (H S : String)
    (h : (AArm.mulxS H S).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.mulxS H S).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.mulxS H S).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true] at h
  obtain ⟨hH, hS⟩ := h
  obtain ⟨hlt, hneH, -, hne2, hne4⟩ := mulxSameScratch_spec (gpNumU H) (gpNumU S)
  set R := SailX86Decoder.regName (scrOf H S) with hR
  have hRH : R ≠ phys H :=
    regName_ne_of_ne hlt (gpNumU_lt_16 H) hneH
  have hRsp : R ≠ "%rsp" := by
    rw [show "%rsp" = SailX86Decoder.regName 4 from rfl]
    exact regName_ne_of_ne hlt (by decide) hne4
  have hRdx : R ≠ "%rdx" := by
    rw [show "%rdx" = SailX86Decoder.regName 2 from rfl]
    exact regName_ne_of_ne hlt (by decide) hne2
  have hHsp : phys H ≠ "%rsp" := (gpFacts hH).physNe
  have hrdx : phys "RDX" = "%rdx" := by decide
  have hgRDX : gpOk "RDX" = true := by decide
  set x := sa.regs "%rdx" with hx
  set y := sa.regs (phys S) with hy
  set hi := (x86_MULX_lo_hi x y).2 with hhi
  set lo := (x86_MULX_lo_hi x y).1 with hlo
  -- the machine run
  have hjs : (AArm.mulxS H S).js P = [.storeMem "%rsp" cmovRedZone (.reg R),
      .mulx (phys H) R (.reg "%rdx") (.reg (phys S)), .loadMem R "%rsp" cmovRedZone] := rfl
  rw [hjs]
  obtain ⟨r1, m1⟩ := evalInstrA_storeMem_eq sa "%rsp" R cmovRedZone
  set sa1 := evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R))
  set sa2 := evalInstrA sa1 (.mulx (phys H) R (.reg "%rdx") (.reg (phys S)))
  have r2 : ∀ r, sa2.regs r = if r = phys H then hi else if r = R then lo else sa.regs r := by
    intro r
    rw [DecodedLsemLoop.evalInstrA_mulx_regs, r1]
  have m2 : sa2.mem = sa1.mem := evalInstrA_mem_of_noWriteB sa1 _ rfl
  obtain ⟨r3, m3⟩ := evalInstrA_loadMem_eq sa2 R "%rsp" cmovRedZone
  have hsp2 : sa2.regs "%rsp" = rsp := by
    rw [r2, if_neg hHsp.symm, if_neg hRsp.symm, hc.sp]
  have hfin : ∀ r, (aMachine.runBlock sa [.storeMem "%rsp" cmovRedZone (.reg R),
      .mulx (phys H) R (.reg "%rdx") (.reg (phys S)), .loadMem R "%rsp" cmovRedZone]).regs r
      = if r = phys H then hi else sa.regs r := by
    intro r
    show (evalInstrA sa2 (.loadMem R "%rsp" cmovRedZone)).regs r = _
    rw [r3, hsp2, m2, m1, hc.sp]
    by_cases hrR : r = R
    · subst hrR
      rw [if_pos rfl, if_neg hRH]
      exact read64_write64_same _ _ _
    · rw [if_neg hrR, r2, if_neg hrR]
  have hmemf : (aMachine.runBlock sa [.storeMem "%rsp" cmovRedZone (.reg R),
      .mulx (phys H) R (.reg "%rdx") (.reg (phys S)), .loadMem R "%rsp" cmovRedZone]).mem
      = write64 sa.mem (redW rsp) (sa.regs R) := by
    show (evalInstrA sa2 (.loadMem R "%rsp" cmovRedZone)).mem = _
    rw [m3, m2, m1, hc.sp]
    rfl
  -- the address machine step
  have hxs : s.reg.getW "RDX" 64 = some x := by rw [hc.regs "RDX" hgRDX, hrdx]
  have hys : s.reg.getW S 64 = some y := hc.regs S hS
  refine ⟨⟨((s.reg.setReg H lo).setReg H hi).nextPc, s.mem, s.cf, s.of⟩, zf, ?_,
    hc.write hH hi hfin (fun z hz => ?_) (fun r hr => ?_) ?_⟩
  · rw [show (AArm.mulxS H S).li
        = (.Lopn [.reg H, .reg H] (withWidthTag 64 "MULX") [.reg S], .reg none) from rfl,
      fstepA_of_reg (frameP P rsp) rfl (fun d x hs => by simp [slotMov?] at hs)
        (fun d x q hk => by simp [slotCmp?] at hk) (by simp [cellA?]) (by simp [slotCarry?])
        (by simp [slotImm?]) (by simp [slotCmov?]) s zf]
    show (fstepF _ (baseOf s) zf).map _ = _
    rw [fstepF_mulxS]
    simp [wideStep, evalOperandN, mulxSrc, baseOf, hxs, hys, ← hhi, ← hlo, LstateM.setReg,
      LstateM.nextPc]
  · rw [hmemf, write64_of_not_inRange _ _ _ _ hz]
    exact hc.mem z hz
  · show ((s.reg.setReg H lo).setReg H hi).nextPc.getW r 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hr,
      LstateN.getW_setReg_other _ _ _ _ _ hr]
  · show ((s.reg.setReg H lo).setReg H hi).nextPc.getW H 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same]

/-- **The widening multiply with distinct destinations.** The machine writes the high word
    to `phys H` and the low word to `phys L`, as the flag machine writes them to `H` and `L`;
    the memory is unchanged. -/
theorem sim_mulx (P : Params) (rsp : BitVec 64) (L H S : String)
    (h : (AArm.mulx L H S).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorr rsp sa s) :
    ∃ s' zf', fstepA (frameP P rsp) (AArm.mulx L H S).li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa ((AArm.mulx L H S).js P)) s' := by
  simp only [AArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hL, hH⟩, hS⟩, hne⟩ := h
  have hrdx : phys "RDX" = "%rdx" := by decide
  have hgRDX : gpOk "RDX" = true := by decide
  set x := sa.regs "%rdx" with hx
  set y := sa.regs (phys S) with hy
  set hi := (x86_MULX_lo_hi x y).2 with hhi
  set lo := (x86_MULX_lo_hi x y).1 with hlo
  have hjs : (AArm.mulx L H S).js P
      = [.mulx (phys H) (phys L) (.reg "%rdx") (.reg (phys S))] := rfl
  rw [hjs]
  set sa' := aMachine.runBlock sa [.mulx (phys H) (phys L) (.reg "%rdx") (.reg (phys S))]
    with hsa'
  have r1 : ∀ r, sa'.regs r = if r = phys H then hi else if r = phys L then lo else sa.regs r :=
    fun r => DecodedLsemLoop.evalInstrA_mulx_regs sa _ _ _ _ r
  have m1 : sa'.mem = sa.mem := evalInstrA_mem_of_noWriteB sa _ rfl
  have hxs : s.reg.getW "RDX" 64 = some x := by rw [hc.regs "RDX" hgRDX, hrdx]
  have hys : s.reg.getW S 64 = some y := hc.regs S hS
  refine ⟨⟨((s.reg.setReg L lo).setReg H hi).nextPc, s.mem, s.cf, s.of⟩, zf, ?_,
    ⟨fun r hr => ?_, ?_, fun z hz => ?_⟩⟩
  · rw [show (AArm.mulx L H S).li
        = (.Lopn [.reg L, .reg H] (withWidthTag 64 "MULX") [.reg S], .reg none) from rfl,
      fstepA_of_reg (frameP P rsp) rfl (fun _ _ hs => by simp [slotMov?] at hs)
        (fun _ _ _ hk => by simp [slotCmp?] at hk) (by simp [cellA?]) (by simp [slotCarry?])
        (by simp [slotImm?]) (by simp [slotCmov?]) s zf]
    show (fstepF _ (baseOf s) zf).map _ = _
    rw [fstepF_mulx]
    simp [wideStep, evalOperandN, mulxSrc, baseOf, hxs, hys, ← hhi, ← hlo, LstateM.setReg,
      LstateM.nextPc]
  · show ((s.reg.setReg L lo).setReg H hi).nextPc.getW r 64 = _
    rw [r1, LstateN.getW_nextPc]
    by_cases hrH : r = H
    · subst hrH
      rw [LstateN.getW_setReg_same, if_pos rfl]
    · rw [LstateN.getW_setReg_other _ _ _ _ _ hrH, if_neg (fun e => hrH (phys_inj hr hH e))]
      by_cases hrL : r = L
      · subst hrL
        rw [LstateN.getW_setReg_same, if_pos rfl]
      · rw [LstateN.getW_setReg_other _ _ _ _ _ hrL, if_neg (fun e => hrL (phys_inj hr hL e)),
          hc.regs r hr]
  · rw [r1, if_neg (fun e => (gpFacts hH).physNe e.symm),
      if_neg (fun e => (gpFacts hL).physNe e.symm)]
    exact hc.sp
  · show s.mem z = sa'.mem z
    rw [m1]
    exact hc.mem z hz

/-- The address an indexed load of the arm `a` reads from the address state `s` is disjoint
    from the red-zone word. -/
def AArm.LoadSafe (rsp : BitVec 64) (s : LstateA) : AArm → Prop
  | .ldx _ B I => ∀ p vi, s.reg.getW B 64 = some p → s.reg.getW I 64 = some vi →
      Disjoint8 (redW rsp) (p + BitVec.ofNat 64 (8 * vi.toNat))
  | _ => True

/-- **One arm.** From the correspondence, the address-machine step of an arm whose
    conditions hold, at a safe indexed load, succeeds; its result corresponds to the machine
    run of the decoded instructions of the arm, and after a compare the machine zero flag is
    the flag of the address machine. -/
theorem AArm.sim (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hc : ACorr rsp sa s) (hsafe : a.LoadSafe rsp s) :
    ∃ s' zf', fstepA (frameP P rsp) a.li s zf = some (s', zf')
      ∧ ACorr rsp (aMachine.runBlock sa (a.js P)) s'
      ∧ (cmpArmB a = true → (aMachine.runBlock sa (a.js P)).flags.zf.getD false = zf') := by
  cases a with
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨s', zf', h1, h2⟩ := sim_reg P rsp a h.1.1 h.1.2 sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | st m q S =>
    obtain ⟨s', zf', h1, h2⟩ := sim_st P rsp m q S h sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | ld m D q =>
    obtain ⟨s', zf', h1, h2⟩ := sim_ld P rsp m D q h sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | cmpR c r =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨s', zf', h1, h2, h3⟩ := sim_cmp P rsp c (.reg r) (.reg (phys r)) h.1 sa s zf hc
      (hc.regs r h.2) (fun q hq => by cases hq; exact frameP_gp h.2)
    exact ⟨s', zf', h1, h2, fun _ => h3⟩
  | cmpI c k =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨s', zf', h1, h2, h3⟩ := sim_cmp P rsp c (.imm k) (.imm k) h.1 sa s zf hc rfl
      (fun q hq => by cases hq)
    exact ⟨s', zf', h1, h2, fun _ => h3⟩
  | cmpM c q =>
    obtain ⟨s', zf', h1, h2, h3⟩ := sim_cmpM P rsp c q h sa s zf hc
    exact ⟨s', zf', h1, h2, fun _ => h3⟩
  | ldx D B I =>
    obtain ⟨s', zf', h1, h2⟩ := sim_ldx P rsp D B I h sa s zf hc hsafe
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | stx d B I V =>
    obtain ⟨s', zf', h1, h2⟩ := sim_stx P rsp d B I V h sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | mul D S =>
    obtain ⟨s', zf', h1, h2⟩ := sim_mul P rsp D S h sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | mulxS H S =>
    obtain ⟨s', zf', h1, h2⟩ := sim_mulxS P rsp H S h sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩
  | mulx L H S =>
    obtain ⟨s', zf', h1, h2⟩ := sim_mulx P rsp L H S h sa s zf hc
    exact ⟨s', zf', h1, h2, fun hb => by simp [cmpArmB] at hb⟩

/-! ## 7. Reading an instruction into an arm -/

/-- The arm of an instruction, read off its operand shape and mnemonic; `none` outside the
    covered shapes. -/
def classifyA : LinstrR → Option AArm
  | .Lopn [.reg d] m [.reg s] =>
      if isMovM m && !gpOk d then some (.st m d s)
      else if isMovM m && !gpOk s then some (.ld m d s)
      else (classify (.Lopn [.reg d] m [.reg s])).map .reg
  | .Lopn [.reg d] m [.arrIdx b i sc] =>
      if m == "LOADIDX" && sc == 8 then some (.ldx d b i) else none
  | .Lopn [.reg d] m [.arrIdx b i sc, .reg v] =>
      if m == "STOREIDX" && sc == 8 then some (.stx d b i v) else none
  | .Lopn [.reg d] m [.reg a, .reg s] =>
      if m == "CMP:64" && d == a && gpOk s then some (.cmpR d s)
      else if m == "CMP:64" && d == a then some (.cmpM d s)
      else if m == "MUL:64" && d == a then some (.mul d s)
      else (classify (.Lopn [.reg d] m [.reg a, .reg s])).map .reg
  | .Lopn [.reg d] m [.reg a, .imm k] =>
      if m == "CMP:64" && d == a then some (.cmpI d k)
      else (classify (.Lopn [.reg d] m [.reg a, .imm k])).map .reg
  | .Lopn [.reg h, .reg h'] m [.reg s] =>
      if m == "MULX" && h == h' then some (.mulxS h s)
      else if m == "MULX" then some (.mulx h h' s)
      else none
  | i => (classify i).map .reg

theorem classifyA_instr {i : LinstrR} {a : AArm} (h : classifyA i = some a) : a.instr = i := by
  have hm : ∀ {j : LinstrR}, (classify j).map AArm.reg = some a → a.instr = j := by
    intro j hj
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hj
    exact classify_instr hb
  unfold classifyA at h
  split at h
  · split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h; rfl
    · obtain rfl := Option.some.inj h; rfl
    · exact hm h
  · split_ifs at h with h1
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1; rfl
  · split_ifs at h with h1
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1; rfl
  · split_ifs at h with h1 h2 h3
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h1; rfl
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨rfl, rfl⟩ := h2; rfl
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h3
      obtain ⟨rfl, rfl⟩ := h3; rfl
    · exact hm h
  · split_ifs at h with h1
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1; rfl
    · exact hm h
  · split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1; rfl
    · obtain rfl := Option.some.inj h
      simp only [beq_iff_eq] at h2
      subst h2; rfl
  · exact hm h

/-- The address machine steps an arm whose conditions hold as the tagged instruction
    `AArm.li`. -/
theorem AArm.li_eq {P : Params} {a : AArm} (h : a.ok P = true) :
    (normA a.instr, tagA a.instr) = a.li := by
  cases a with
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨ds, o, ss, he⟩ := a.instr_lopn
    have hp := h.2
    simp only [AArm.instr, he, plainB, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.isNone_iff_eq_none] at hp ⊢
    have ht : tagA (.Lopn ds o ss) = .reg none :=
      (tagA_lopn hp.1.1.2 hp.1.2).trans (congrArg MemTag.reg hp.2)
    simp [AArm.li, AArm.instr, he, normA, ht, hp.1.1.1]
  | st m q S =>
    simp only [AArm.ok, Bool.and_eq_true, isMovM, Bool.or_eq_true, beq_iff_eq] at h
    rcases h.2 with rfl | rfl <;>
      simp (config := { decide := true }) [AArm.li, AArm.instr, normA, tagA]
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true, isMovM, Bool.or_eq_true, beq_iff_eq] at h
    rcases h.2 with rfl | rfl <;>
      simp (config := { decide := true }) [AArm.li, AArm.instr, normA, tagA]
  | _ => simp (config := { decide := true }) [AArm.li, AArm.instr, normA, tagA]

theorem AArm.instr_lopn (a : AArm) : ∃ ds o ss, a.instr = .Lopn ds o ss := by
  cases a with
  | reg a => exact a.instr_lopn
  | _ => exact ⟨_, _, _, rfl⟩

/-- The instruction of an arm is no untagged immediate move, so its tag at any position is
    `tagA`. -/
theorem AArm.tagAt_eq (body : Lcmd) (k : Nat) (a : AArm) :
    tagAt body k a.instr = tagA a.instr := by
  apply tagAt_of_ne
  cases a with
  | reg a => cases a <;> simp [AArm.instr, Arm.instr, JasminLsemCast.movImmStruct?]
  | _ => simp [AArm.instr, JasminLsemCast.movImmStruct?]

/-- The computed shape of an arm's instruction decodes to the arm's machine instructions. -/
theorem AArm.shape_ops {P : Params} {a : AArm} (h : a.ok P = true) {sh : DShape}
    (hs : shapeOf P a.instr = some sh) : sh.ops' = a.js P := by
  obtain ⟨hb, hp⟩ := a.bytes P h
  obtain ⟨ds, o, ss, he⟩ := a.instr_lopn
  rw [he] at hb hs
  exact shapeOf_lopn_ops _ hb hp hs

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
