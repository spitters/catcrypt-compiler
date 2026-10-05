/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaSubset
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
public import CatCrypt.Crypto.SecureCompilation.CT.ArmTiming

@[expose] public section

set_option autoImplicit false

/-!
# The AArch64 instance of the `Lprog` instruction-set record

`armIsa` is the `LprogIsa.Isa` of AArch64. Its data are the AAPCS64 register file and calling
convention (allocatable `x0`–`x15`, scratch `x16`/`x17`, arguments `x0`–`x7`, callee-saved
`x19`–`x28`), the three-address legaliser data (no tied form) and the leakage regime of the
FEAT_DIT table `CT.ArmMnem` (`armLeaksOperands`). Its step is
`LprogIsa.subsetStep` over the alphabet `armBases`: a 64-bit `CMP` writes the zero flag `zf`
(`Z`) and the carry flag `cf` (`C`, set when no borrow occurs), every other instruction of
the alphabet is the core step, and the branch condition `armCond` reads `zf` for the
condition codes `Z`/`NZ` (`B.EQ`/`B.NE`) and tests a register for non-zero otherwise
(`CBNZ`).

The instruction selection `armSel` maps the register fragment of the alphabet (64-bit
`ADD`, `SUB`, `AND`, `OR`, `XOR` with three register operands, and the register `MOV`) on
the registers `armRegs` (`x0`–`x17`, the range of the decoder round trip) to `BInst`. The
encoder `ArmEncoder.encodeBBlock` with the identity assignment `armAlloc` writes its bytes,
and `decodeBBlock` reads them back through `SailArmDecoder.decodeB64` and `rebuildB`.

`arm_asm` is the Asm lemma of the register fragment: for a selected block, the encoded bytes
decode to the selected instructions, and the `BInst` run of those instructions agrees with
the `armIsa` run of the `Lprog` block on every register of `armRegs`, with memory, flags,
function and the counter advance of the `Lprog` run stated.

## Main results

* `armIsa`: the AArch64 instruction set.
* `armLeaksOperands`, `armIsa_leaksOperands_bases`: the leakage regime with `PSTATE.DIT = 1`
  and the absence of an operand-leaking base in the alphabet.
* `armSel`, `armSel_decode`, `armSel_step`: the selection, its byte round trip and its
  one-step simulation.
* `decodeBBlock`, `arm_asm`: the block decoder and the Asm lemma of the register fragment.
* `armSelM`, `armSelM_decode`, `armSelM_step`: the selection of the memory fragment (array
  loads and stores, `ADD`/`SUB` immediate), its byte round trip and its one-step simulation
  under the memory relation `ArmMemRel` and the array layout `ArmArrsSep`.
* `decodeBMBlock`, `arm_asm_mem`: the block decoder and the Asm lemma of the memory fragment.
* `armCond_cbnz`, `armCond_bne`: the branch conditions of `Lcond` as the `CBNZ` and `B.NE`
  tests of a related machine state.
* `armIsa_step_cmp`: the compare `CMP:64` as the flag result of the A64 `CMP`.
* `armSelX`, `armSelX_decode`, `armSelX_step`, `arm_asm_x`: the selection with the compare
  and the immediate-offset `LDR`/`STR` of the word memory, its byte round trip, its one-step
  simulation under the word relation `ArmWordRel`, the flag relation `ArmFlagRel` and the
  cell layout `ArmCellsSep`, and its Asm lemma.
* `armAndBody`, `arm_and_body`: the `mpn_and_n` body at AArch64 bytes.
-/

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder

/-! ## The instruction-set data -/

/-- The registers `x0`–`x17`, the range of the decoder round trip `xRegName_xNum`. -/
def armRegs : List String := (List.range 18).map (fun i => "x" ++ toString i)

/-- The allocatable registers: the AAPCS64 argument and temporary registers `x0`–`x15`. -/
def armAllocPool : List String :=
  ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13",
   "x14", "x15"]

/-- The AAPCS64 integer argument registers. -/
def armArgRegs : List String := ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]

/-- The AAPCS64 callee-saved registers `x19`–`x28`. -/
def armCalleeSaved : List String :=
  ["x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28"]

/-- The A64 mnemonic of a mnemonic base of the AArch64 alphabet `armBases`: the register
    operations as `armSel` selects them, `MUL` as `MUL` (alias of `MADD`), the compare `CMP` as
    `SUBS` (`armCmp`), the loads and stores as `LDR` and `STR`, and `MOVQ` as `MOV`. `none`
    for a base outside the alphabet. -/
def armMnemOfBase : String → Option CT.ArmMnem
  | "ADD" => some .add
  | "SUB" => some .sub
  | "AND" => some .and
  | "OR" => some .orr
  | "XOR" => some .eor
  | "MUL" => some .mul
  | "MOV" => some .mov
  | "MOVQ" => some .mov
  | "CMP" => some .subs
  | "LOAD" => some .ldr
  | "LOADIDX" => some .ldr
  | "STORE" => some .str
  | "STOREIDX" => some .str
  | _ => none

/-- The AArch64 leakage regime with `PSTATE.DIT = 1`: the FEAT_DIT table `CT.ArmMnem` at the
    mnemonic of the base, every operand observable for a base outside the alphabet. -/
def armLeaksOperands (base : String) : Bool :=
  ((armMnemOfBase base).map CT.ArmMnem.leaksOperands).getD true

/-- The mnemonic bases of the AArch64 alphabet. -/
def armBases : List String :=
  ["ADD", "SUB", "AND", "OR", "XOR", "MUL", "MOV", "CMP", "LOADIDX", "STOREIDX", "LOAD",
   "STORE", "MOVQ"]

/-- The AAPCS64 caller-saved (corruptible) integer registers: `x0`–`x17` and the link
    register `x30`. The platform register `x18` is excluded. -/
def armCallerSaved : List String := armRegs ++ ["x30"]

/-- **The AArch64 data**: the AAPCS64 register file with the intra-procedure-call registers
    `x16`, `x17` as scratch, the save slot of a callee-saved register at its index, the stack
    pointer `sp`, the return registers `x0`, `x1`, the caller-saved registers and no red zone,
    the three-address legaliser data (no tied form, the commutative bases, the copy `MOV` at
    the width of the operation), the leakage regime `armLeaksOperands`, the alphabet
    `armBases`, no implicit reads, and the register loop guard `cbnz ctr, top`. -/
def armData : IsaData where
  allocPool := armAllocPool
  scratch := ["x16", "x17"]
  argRegs := armArgRegs
  calleeSaved := armCalleeSaved
  saveSlot := fun r => armCalleeSaved.findIdx? (· == r)
  sp := "sp"
  retRegs := ["x0", "x1"]
  callerSaved := armCallerSaved
  redZone := 0
  tied := fun _ _ => false
  commutes := fun base => ["ADD", "MUL", "AND", "OR", "XOR"].contains base
  tieScratch := "x16"
  copyMnemonic := fun opn => if hasSuffix opn ":64" then some "MOV:64" else some "MOV"
  leaksOperands := armLeaksOperands
  supports := fun base => armBases.contains base
  implicitReads := fun _ => []
  loopGuard := fun ctr top => [.Lcond (.reg ctr) top]

/-! ## The step -/

/-- The AArch64 branch condition: `Z` holds when `zf` is set (`B.EQ`), `NZ` when it is clear
    (`B.NE`), and a register condition when the register is non-zero (`CBNZ`). -/
def armCond (s : LstateMF) (c : LOperand) : Bool :=
  match c with
  | .reg "Z" => s.zf
  | .reg "NZ" => !s.zf
  | _ => condNZ s.prog.base c

/-- The AArch64 compare `CMP a, b` (`SUBS XZR, a, b`): `Z` is `a = b` and `C` is the absence
    of a borrow, `b ≤ a` unsigned; the registers are unchanged. -/
def armCmp (i : LinstrRM) (s : LstateMF) : Option (Option LstateMF) :=
  match cmpArgs? i with
  | some (a, b) =>
      some (match evalOperandN s.prog.base.reg 64 a, evalOperandN s.prog.base.reg 64 b with
        | some va, some vb =>
            some { prog := { s.prog with base := { s.prog.base.nextPc with cf := !(va.ult vb) } },
                   zf := va == vb }
        | _, _ => none)
  | none => none

/-- **The AArch64 instruction set**: the data `armData`, the step of the alphabet `armBases`
    with the compare `armCmp`, and the branch condition `armCond`. -/
def armIsa : Isa where
  toIsaData := armData
  step := subsetStep armBases armCond armCmp
  condEval := armCond
  step_ctl := subsetStep_ctl armBases armCond armCmp

theorem armIsa_step : armIsa.step = subsetStep armBases armCond armCmp := rfl

theorem armIsa_condEval : armIsa.condEval = armCond := rfl

theorem armIsa_leaksOperands : armIsa.leaksOperands = armLeaksOperands := rfl

theorem armIsa_supports : armIsa.supports = fun base => armBases.contains base := rfl

/-- No base of the AArch64 alphabet leaks its data operands under `PSTATE.DIT = 1`. -/
theorem armIsa_leaksOperands_bases : ∀ b ∈ armBases, armIsa.leaksOperands b = false := by
  decide

/-! ## Instruction selection -/

/-- The register-arithmetic operations of the selection. -/
def armBops : List JasminBinOp := [.add, .sub, .and, .or, .xor]

/-- The operation whose 64-bit mnemonic is `opn`, among `armBops`. -/
def armBopOf? (opn : String) : Option JasminBinOp :=
  armBops.find? (fun o => withWidthTag 64 (binOpName o) == opn)

/-- The `BInst` of a register-arithmetic operation. -/
def armBinst (bop : JasminBinOp) (d a b : String) : Option BInst :=
  match bop with
  | .add => some (.add d a b)
  | .sub => some (.sub d a b)
  | .and => some (.and d a b)
  | .or => some (.orr d a b)
  | .xor => some (.eor d a b)
  | _ => none

/-- **The AArch64 selection of the register fragment**: a 64-bit three-register `ADD`,
    `SUB`, `AND`, `OR` or `XOR` with the register tag, and a 64-bit register `MOV`, over the
    registers `armRegs`. -/
def armSel : LinstrRM → Option BInst
  | (.Lopn [.reg d] opn [.reg a, .reg b], .reg none) =>
      if armRegs.contains d && armRegs.contains a && armRegs.contains b then
        (armBopOf? opn).bind (fun o => armBinst o d a b)
      else none
  | (.Lopn [.reg d] opn [.reg a], _) =>
      if opn == withWidthTag 64 "MOV" && armRegs.contains d && armRegs.contains a then
        some (.mov d a)
      else none
  | _ => none

/-- The identity register assignment on `armRegs`. -/
def armAlloc : GpAlloc := armRegs.map (fun r => (r, r))

/-- The identity assignment maps each register of `armRegs` to itself. -/
theorem gpOf_armAlloc {r : String} (h : r ∈ armRegs) : gpOf armAlloc r = r := by
  have hl : ∀ l : List String, r ∈ l → (l.map (fun x => (x, x))).lookup r = some r := by
    intro l hm
    induction l with
    | nil => cases hm
    | cons x l ih =>
        simp only [List.map_cons, List.lookup_cons]
        by_cases hx : r = x
        · subst hx; simp
        · have : (r == x) = false := by simp [hx]
          rw [this]
          exact ih (by simpa [hx] using hm)
  unfold gpOf armAlloc
  rw [hl armRegs h]
  split_ifs <;> simp_all

/-- A register of `armRegs` is fixed by `xRegName ∘ xNum`. -/
theorem xRegName_xNum_armRegs {r : String} (h : r ∈ armRegs) :
    xRegName (xNum (gpOf armAlloc r)) = gpOf armAlloc r := by
  rw [gpOf_armAlloc h]
  exact xRegName_xNum r (List.mem_append_left _ h)

/-- No register of `armRegs` is the zero register. -/
theorem ne_xzr_of_armRegs {r : String} (h : r ∈ armRegs) : r ≠ "xzr" := by
  have hall : ∀ x ∈ armRegs, x ≠ "xzr" := by decide
  exact hall r h

/-- The inversion of `armBopOf?`. -/
theorem armBopOf?_eq_some {opn : String} {o : JasminBinOp} (h : armBopOf? opn = some o) :
    opn = withWidthTag 64 (binOpName o) ∧ o ∈ armBops := by
  have hp := List.find?_some h
  exact ⟨(beq_iff_eq.mp hp).symm, List.mem_of_find?_eq_some h⟩

/-- **The inversion of the selection**: a selected instruction is a register-arithmetic
    instruction of `armBops` or a register `MOV`, on registers of `armRegs`. -/
theorem armSel_inv {i : LinstrRM} {bi : BInst} (h : armSel i = some bi) :
    (∃ o d a b, i = (.Lopn [.reg d] (withWidthTag 64 (binOpName o)) [.reg a, .reg b], .reg none)
        ∧ o ∈ armBops ∧ d ∈ armRegs ∧ a ∈ armRegs ∧ b ∈ armRegs ∧ armBinst o d a b = some bi)
    ∨ (∃ d a tag, i = (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a], tag)
        ∧ d ∈ armRegs ∧ a ∈ armRegs ∧ bi = .mov d a) := by
  unfold armSel at h
  split at h
  · rename_i d opn a b
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      obtain ⟨o, ho, hb⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hopn, hmem⟩ := armBopOf?_eq_some ho
      exact Or.inl ⟨o, d, a, b, by rw [hopn], hmem, hc.1.1, hc.1.2, hc.2, hb⟩
    · cases h
  · rename_i d opn a tag
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
      cases h
      exact Or.inr ⟨d, a, tag, by rw [hc.1.1], hc.1.2, hc.2, rfl⟩
    · cases h
  · cases h

/-! ## The byte round trip -/

/-- **The byte round trip of a selected instruction**: decoding the encoder's word with
    `decodeB64` and `rebuildB` recovers the instruction. -/
theorem armSel_decode {i : LinstrRM} {bi : BInst} (h : armSel i = some bi) :
    (decodeB64 (encodeBInst armAlloc bi)).bind rebuildB = some bi := by
  rcases armSel_inv h with ⟨o, d, a, b, -, ho, hd, ha, hb, hbi⟩ | ⟨d, a, -, -, hd, ha, rfl⟩
  · have ed := gpOf_armAlloc hd
    have ea := gpOf_armAlloc ha
    have eb := gpOf_armAlloc hb
    have xd := xRegName_xNum_armRegs hd
    have xa := xRegName_xNum_armRegs ha
    have xb := xRegName_xNum_armRegs hb
    simp only [armBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [armBinst, Option.some.injEq] at hbi <;>
      subst hbi
    · rw [roundtrip_binst_add armAlloc d a b xd xa xb, ed, ea, eb]
    · rw [roundtrip_binst_sub armAlloc d a b xd xa xb, ed, ea, eb]
    · rw [roundtrip_binst_and armAlloc d a b xd xa xb, ed, ea, eb]
    · have hane : xNum (gpOf armAlloc a) ≠ 31 := by
        intro h31
        have hx := xa
        rw [h31] at hx
        exact ne_xzr_of_armRegs ha (by rw [← ea, ← hx]; rfl)
      rw [roundtrip_binst_orr armAlloc d a b xd xa xb hane, ed, ea, eb]
    · rw [roundtrip_binst_eor armAlloc d a b xd xa xb, ed, ea, eb]
  · rw [roundtrip_binst_mov armAlloc d a (xRegName_xNum_armRegs hd) (xRegName_xNum_armRegs ha),
      gpOf_armAlloc hd, gpOf_armAlloc ha]

/-- Decode a byte stream of 4-byte AArch64 words with `decodeB64` and `rebuildB`; `none` on
    a word outside the decoder or a trailing partial word. -/
def decodeBBlock : List (BitVec 8) → Option (List BInst)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      ((decodeB64 [b0, b1, b2, b3]).bind rebuildB).bind
        (fun i => (decodeBBlock rest).map (fun is => i :: is))
  | _ => none

/-- A four-byte word followed by a stream decodes as the word followed by the stream. -/
theorem decodeBBlock_append (w rest : List (BitVec 8)) (hw : w.length = 4) :
    decodeBBlock (w ++ rest) =
      ((decodeB64 w).bind rebuildB).bind (fun i => (decodeBBlock rest).map (fun is => i :: is)) := by
  match w, hw with
  | [b0, b1, b2, b3], _ => rfl

/-- **The block round trip**: the encoded bytes of a selected block decode to the block. -/
theorem armSel_decodeBlock :
    ∀ (is : List LinstrRM) (bs : List BInst), is.mapM armSel = some bs →
      decodeBBlock (encodeBBlock armAlloc bs) = some bs
  | [], bs, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; rfl
  | i :: is, bs, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      simp only [encodeBBlock, List.flatMap_cons]
      rw [decodeBBlock_append _ _ (encodeBInst_length armAlloc bi), armSel_decode hi]
      simp only [Option.bind_some]
      have ih := armSel_decodeBlock is bs' hs
      simp only [encodeBBlock] at ih
      rw [ih]
      rfl

/-! ## The step simulation -/

/-- A machine write to a register of `armRegs` reads back as the write. -/
theorem get_set_armRegs (b : BState) {d : String} (hd : d ∈ armRegs) (v : BitVec 64)
    (r : String) : (b.set d v).get r = if r = d then v else b.get r := by
  have hdz := ne_xzr_of_armRegs hd
  by_cases hr : r = d
  · subst hr; simp [BState.set, hdz]
  · simp only [BState.get, BState.set, hdz, if_false, hr]

/-- **The one-step simulation of the selection**: from related states, the `armIsa` step
    of a selected instruction succeeds, and the result is related to the `BInst` step of
    the selected instruction, with the frame of one step. -/
theorem armSel_step (P : LprogM) {i : LinstrRM} {bi : BInst} (h : armSel i = some bi)
    (s : LstateMF) (b : BState) (hrel : RegRel armRegs s b.get) :
    ∃ s', armIsa.step P i s = some s' ∧ RegRel armRegs s' (evalBInst b bi).get
      ∧ Frame 1 s s' := by
  rcases armSel_inv h with ⟨o, d, a, c, rfl, ho, hd, ha, hc, hbi⟩ | ⟨d, a, tag, rfl, hd, ha, rfl⟩
  · have hstrip := stripWidthTag_withWidthTag_binOpName' 64 o
    simp only [armBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    have hok : mnemOk armBases
        (.Lopn [.reg d] (withWidthTag 64 (binOpName o)) [.reg a, .reg c]) = true := by
      simp only [mnemOk, hstrip]
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    have hcmp : armCmp (.Lopn [.reg d] (withWidthTag 64 (binOpName o)) [.reg a, .reg c],
        .reg none) s = none := by
      simp only [armCmp, cmpArgs?]
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> rw [if_neg (by decide +kernel)]
    refine ⟨{ s with prog := { s.prog with
      base := (s.prog.base.setReg d (o.apply (b.get a) (b.get c))).nextPc } },
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [armIsa_step]
      simp only [subsetStep, isCtl, hok, hcmp, Bool.false_eq_true, if_false, if_true]
      exact coreStep_binop P o d a c s _ _ (hrel.getW ha) (hrel.getW hc)
    · refine RegRel_setReg hrel d _ (fun r _ => ?_)
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        simp only [armBinst, Option.some.injEq] at hbi <;> subst hbi <;>
        simp only [evalBInst, get_set_armRegs b hd, JasminBinOp.apply, opAnd64, opOrr64,
          opEor64]
  · have hok : mnemOk armBases (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a]) = true := by
      simp only [mnemOk]
      rw [show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide +kernel]
      decide
    have hcmp : armCmp (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a], tag) s = none := by
      simp only [armCmp, cmpArgs?]
    refine ⟨{ s with prog := { s.prog with base := (s.prog.base.setReg d (b.get a)).nextPc } },
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [armIsa_step]
      simp only [subsetStep, isCtl, hok, hcmp, Bool.false_eq_true, if_false, if_true]
      exact coreStep_mov P d a tag s _ (hrel a ha)
    · exact RegRel_setReg hrel d _ (fun r _ => by simp only [evalBInst, get_set_armRegs b hd])

/-- **The Asm lemma of the AArch64 register fragment.** For a block `is` that the selection
    maps to `bs`: the bytes `encodeBBlock armAlloc bs` decode to `bs`, and from an `LstateMF`
    related to a machine state `b` on `armRegs`, the `armIsa` run of `is` succeeds and ends
    related to the `BInst` run `runBBlock b bs`, with the zero, carry and overflow flags, the
    function, the arrays and the word memory unchanged and the counter advanced by the length
    of the block. -/
theorem arm_asm (P : LprogM) :
    ∀ (is : List LinstrRM) (bs : List BInst), is.mapM armSel = some bs →
      ∀ (s : LstateMF) (b : BState), RegRel armRegs s b.get →
        decodeBBlock (encodeBBlock armAlloc bs) = some bs ∧
        ∃ s', armIsa.runL P is s = some s' ∧ RegRel armRegs s' (runBBlock b bs).get
          ∧ Frame is.length s s'
  | [], bs, h, s, b, hrel => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, s, rfl, hrel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | i :: is, bs, h, s, b, hrel => by
      refine ⟨armSel_decodeBlock _ _ h, ?_⟩
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      obtain ⟨s1, hs1, hrel1, f1⟩ := armSel_step P hi s b hrel
      obtain ⟨-, s2, hs2, hrel2, f2⟩ := arm_asm P is bs' hs s1 (evalBInst b bi) hrel1
      refine ⟨s2, ?_, hrel2, ?_⟩
      · simp only [Isa.runL, hs1, Option.bind_some, hs2]
      · obtain ⟨a1, b1, c1, d1, e1, g1, k1⟩ := f1
        obtain ⟨a2, b2, c2, d2, e2, g2, k2⟩ := f2
        refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, g2.trans g1, ?_⟩
        rw [k2, k1, List.length_cons]; omega

/-! ## The memory fragment

The selection `armSelM` adds to the register fragment the array load `LOADIDX` and store
`STOREIDX` at width 64 (one `LDR`/`STR` with the scaled register offset each) and the 64-bit
`ADD`/`SUB` with an immediate (`ADD`/`SUB` immediate). The arrays `arrs` of sizes `sz` are
named by the registers holding their addresses; the selection refuses a register write to
an array base. `ArmMemRel` relates the `Lprog` arrays to the machine memory, `ArmArrsSep` states
the array layout, and `arm_asm_mem` is the Asm lemma of the fragment. -/

open CatCrypt.Crypto.SecureCompilation.MachineMem64
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift

/-- The `ADD`/`SUB` immediate of an operation, among `ADD` and `SUB`. -/
def armImmOf? (opn : String) (d a : String) (k : Nat) : Option BMInst :=
  if opn = withWidthTag 64 (binOpName .add) then some (.addi d a k)
  else if opn = withWidthTag 64 (binOpName .sub) then some (.subi d a k)
  else none

/-- **The AArch64 selection of the memory fragment** over the arrays `arrs` of sizes `sz`:
    `LOADIDX` at width 64 becomes `LDR d, [base, idx, LSL #3]`, `STOREIDX` at width 64
    becomes `STR v, [base, idx, LSL #3]`, a 64-bit `ADD`/`SUB` of a register and an immediate
    below `2¹²` becomes `ADD`/`SUB` immediate, and an instruction of `armSel` becomes that
    instruction. The registers are in `armRegs`, the array bases in `arrs`, and no register
    write has an array base as destination. -/
def armSelM (arrs : List String) (sz : String → Nat) : LinstrRM → Option BMInst
  | (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx _], .load 64 n) =>
      if armRegs.contains d && armRegs.contains idx && armRegs.contains base
          && arrs.contains base && !arrs.contains d && n == sz base then
        some (.ldrr d base idx)
      else none
  | (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx _, .reg v], .store 64 n) =>
      if dst == base && armRegs.contains v && armRegs.contains idx
          && armRegs.contains base && arrs.contains base && n == sz base then
        some (.strr v base idx)
      else none
  | (.Lopn [.reg d] opn [.reg a, .imm k], .reg none) =>
      if armRegs.contains d && armRegs.contains a && !arrs.contains d && decide (k < 0x1000)
      then armImmOf? opn d a k
      else none
  | (.Lopn [.reg d] opn srcs, tag) =>
      if arrs.contains d then none else (armSel (.Lopn [.reg d] opn srcs, tag)).map .alu
  | _ => none

/-- The inversion of `armImmOf?`. -/
theorem armImmOf?_inv {opn d a : String} {k : Nat} {bi : BMInst}
    (h : armImmOf? opn d a k = some bi) :
    (opn = withWidthTag 64 (binOpName .add) ∧ bi = .addi d a k)
      ∨ (opn = withWidthTag 64 (binOpName .sub) ∧ bi = .subi d a k) := by
  unfold armImmOf? at h
  split at h
  · cases h; exact Or.inl ⟨by assumption, rfl⟩
  · split at h
    · cases h; exact Or.inr ⟨by assumption, rfl⟩
    · cases h

/-- **The inversion of the memory selection.** -/
theorem armSelM_inv {arrs : List String} {sz : String → Nat} {i : LinstrRM} {bi : BMInst}
    (h : armSelM arrs sz i = some bi) :
    (∃ d base idx sc, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], .load 64 (sz base))
        ∧ d ∈ armRegs ∧ idx ∈ armRegs ∧ base ∈ armRegs ∧ base ∈ arrs ∧ d ∉ arrs
        ∧ bi = .ldrr d base idx)
    ∨ (∃ base idx v sc, i = (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v],
          .store 64 (sz base))
        ∧ v ∈ armRegs ∧ idx ∈ armRegs ∧ base ∈ armRegs ∧ base ∈ arrs ∧ bi = .strr v base idx)
    ∨ (∃ bop d a k, i = (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k],
          .reg none)
        ∧ d ∈ armRegs ∧ a ∈ armRegs ∧ d ∉ arrs ∧ k < 0x1000
        ∧ ((bop = .add ∧ bi = .addi d a k) ∨ (bop = .sub ∧ bi = .subi d a k)))
    ∨ (∃ d opn srcs tag bb, i = (.Lopn [.reg d] opn srcs, tag) ∧ d ∉ arrs
        ∧ armSel i = some bb ∧ bi = .alu bb) := by
  unfold armSelM at h
  split at h
  · rename_i d base idx sc n
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true', beq_iff_eq] at hc
      cases h
      obtain ⟨⟨⟨⟨⟨hd, hi⟩, hb⟩, ha⟩, hda⟩, hn⟩ := hc
      subst hn
      exact Or.inl ⟨d, base, idx, sc, rfl, hd, hi, hb, ha, not_mem_of_contains_false hda, rfl⟩
    · cases h
  · rename_i dst base idx sc v n
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
      cases h
      obtain ⟨⟨⟨⟨⟨hdb, hv⟩, hi⟩, hb⟩, ha⟩, hn⟩ := hc
      subst hdb hn
      exact Or.inr (Or.inl ⟨dst, idx, v, sc, rfl, hv, hi, hb, ha, rfl⟩)
    · cases h
  · rename_i d opn a k
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true',
        decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hd, ha⟩, hda⟩, hk⟩ := hc
      rcases armImmOf?_inv h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨.add, d, a, k, rfl, hd, ha,
          not_mem_of_contains_false hda, hk, Or.inl ⟨rfl, rfl⟩⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨.sub, d, a, k, rfl, hd, ha,
          not_mem_of_contains_false hda, hk, Or.inr ⟨rfl, rfl⟩⟩))
    · cases h
  · rename_i d opn srcs tag _ _ _
    split at h
    · cases h
    · rename_i hc
      obtain ⟨bb, hbb, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Or.inr (Or.inr (Or.inr ⟨d, opn, srcs, tag, bb, rfl,
        not_mem_of_contains_false (Bool.eq_false_iff.mpr hc), hbb, rfl⟩))
  · cases h

/-! ### The byte round trip of the memory fragment -/

/-- The word of a register instruction of `armSel` is outside the memory-and-branch classes. -/
theorem armSel_memNone {i : LinstrRM} {bi : BInst} (h : armSel i = some bi) :
    (leWord (encodeBInst armAlloc bi)).bind decodeMemWord = none := by
  rcases armSel_inv h with ⟨o, d, a, b, -, ho, -, -, -, hbi⟩ | ⟨d, a, -, -, -, -, rfl⟩
  · simp only [armBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [armBinst, Option.some.injEq] at hbi <;>
      subst hbi <;> simp only [encodeBInst]
    · exact memNone_addsubX _ _ _ _
    · exact memNone_addsubX _ _ _ _
    · exact memNone_andX _ _ _
    · exact memNone_orrX _ _ _
    · exact memNone_eorX _ _ _
  · simp only [encodeBInst]; exact memNone_orrX _ _ _

/-- **The byte round trip of a selected instruction of the memory fragment.** -/
theorem armSelM_decode {arrs : List String} {sz : String → Nat} {i : LinstrRM} {bi : BMInst}
    (h : armSelM arrs sz i = some bi) : decodeBM64 (encodeBMInst armAlloc bi) = some bi := by
  rcases armSelM_inv h with ⟨d, base, idx, sc, -, hd, hi, hb, -, -, rfl⟩
    | ⟨base, idx, v, sc, -, hv, hi, hb, -, rfl⟩
    | ⟨bop, d, a, k, -, hd, ha, -, hk, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
    | ⟨d, opn, srcs, tag, bb, -, -, hbb, rfl⟩
  · rw [roundtrip_bminst_ldrr armAlloc d base idx (xRegName_xNum_armRegs hd)
      (xRegName_xNum_armRegs hb) (xRegName_xNum_armRegs hi),
      gpOf_armAlloc hd, gpOf_armAlloc hb, gpOf_armAlloc hi]
  · rw [roundtrip_bminst_strr armAlloc v base idx (xRegName_xNum_armRegs hv)
      (xRegName_xNum_armRegs hb) (xRegName_xNum_armRegs hi),
      gpOf_armAlloc hv, gpOf_armAlloc hb, gpOf_armAlloc hi]
  · rw [roundtrip_bminst_addi armAlloc d a k (xRegName_xNum_armRegs hd)
      (xRegName_xNum_armRegs ha) hk, gpOf_armAlloc hd, gpOf_armAlloc ha]
  · rw [roundtrip_bminst_subi armAlloc d a k (xRegName_xNum_armRegs hd)
      (xRegName_xNum_armRegs ha) hk, gpOf_armAlloc hd, gpOf_armAlloc ha]
  · exact roundtrip_bminst_alu armAlloc bb bb (armSel_memNone hbb) (armSel_decode hbb)

/-- Decode a byte stream of 4-byte AArch64 words with `decodeBM64`; `none` on a word outside
    the decoder or a trailing partial word. -/
def decodeBMBlock : List (BitVec 8) → Option (List BMInst)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (decodeBM64 [b0, b1, b2, b3]).bind (fun i => (decodeBMBlock rest).map (fun is => i :: is))
  | _ => none

/-- A four-byte word followed by a stream decodes as the word followed by the stream. -/
theorem decodeBMBlock_append (w rest : List (BitVec 8)) (hw : w.length = 4) :
    decodeBMBlock (w ++ rest) =
      (decodeBM64 w).bind (fun i => (decodeBMBlock rest).map (fun is => i :: is)) := by
  match w, hw with
  | [b0, b1, b2, b3], _ => rfl

/-- **The block round trip of the memory fragment.** -/
theorem armSelM_decodeBlock {arrs : List String} {sz : String → Nat} :
    ∀ (is : List LinstrRM) (bs : List BMInst), is.mapM (armSelM arrs sz) = some bs →
      decodeBMBlock (encodeBMBlock armAlloc bs) = some bs
  | [], bs, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; rfl
  | i :: is, bs, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      simp only [encodeBMBlock, List.flatMap_cons]
      rw [decodeBMBlock_append _ _ (encodeBMInst_length armAlloc bi), armSelM_decode hi]
      simp only [Option.bind_some]
      have ih := armSelM_decodeBlock is bs' hs
      simp only [encodeBMBlock] at ih
      rw [ih]
      rfl

/-! ### The memory relation and the step simulation -/

/-- **The memory relation**: each array `a` of `arrs` has shape `(64, sz a)` in the `Lprog`
    state, and the machine memory holds it at the address in the register `a`. -/
def ArmMemRel (arrs : List String) (sz : String → Nat) (s : LstateMF) (b : BMState) : Prop :=
  ∀ a ∈ arrs, ∃ arr : Fin (sz a) → BitVec 64,
    s.prog.base.larr a = ⟨64, sz a, arr⟩ ∧ ArrAt b.mem (b.regs.get a) (sz a) arr

/-- **The array layout**: the array bases are registers of `armRegs`, each array has at most
    `2⁶¹` doublewords, and the cells of distinct arrays at the addresses `g a` are separated. -/
def ArmArrsSep (arrs : List String) (sz : String → Nat) (g : String → BitVec 64) : Prop :=
  (∀ a ∈ arrs, a ∈ armRegs) ∧ (∀ a ∈ arrs, 8 * sz a ≤ 2 ^ 64) ∧
  ∀ a ∈ arrs, ∀ a' ∈ arrs, a ≠ a' → ∀ (j : Fin (sz a)) (k : Fin (sz a')),
    MemSep (g a + BitVec.ofNat 64 (8 * j.val)) (g a' + BitVec.ofNat 64 (8 * k.val))

/-- The `armIsa` step of an instruction of the alphabet that is not a compare is the core
    step. -/
theorem armIsa_step_core (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (hok : mnemOk armBases i.fst = true) (hctl : isCtl i.fst = false)
    (hcmp : armCmp i s = none) : armIsa.step P i s = coreStep P i s := by
  rw [armIsa_step]
  simp only [subsetStep, hctl, hok, hcmp, Bool.false_eq_true, if_false, if_true]

/-- A register write outside the array bases leaves the memory relation. -/
theorem ArmMemRel_setReg {arrs : List String} {sz : String → Nat} {s : LstateMF} {b : BMState}
    (hmem : ArmMemRel arrs sz s b) (d : String) (hda : d ∉ arrs) (hd : d ∈ armRegs)
    (v : BitVec 64) (b' : BMState) (hregs : b'.regs = b.regs.set d v) (hm : b'.mem = b.mem)
    (w : Nat) (vw : BitVec w) :
    ArmMemRel arrs sz { s with prog := { s.prog with base := (s.prog.base.setReg d vw).nextPc } }
      b' := by
  intro a ha
  obtain ⟨arr, harr, hat⟩ := hmem a ha
  have had : a ≠ d := fun e => hda (e ▸ ha)
  refine ⟨arr, by simpa using harr, ?_⟩
  rw [hm, hregs, get_set_armRegs _ hd, if_neg had]
  exact hat

/-- **The one-step simulation of the memory selection**: from related states with in-range
    indices, the `armIsa` step of a selected instruction succeeds, and the result is related
    to the `BMInst` step on `armRegs` and on the arrays, with the array base registers
    unchanged and the frame of one step. -/
theorem armSelM_step (P : LprogM) {arrs : List String} {sz : String → Nat} {i : LinstrRM}
    {bi : BMInst} (h : armSelM arrs sz i = some bi) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel arrs sz s b)
    (hsep : ArmArrsSep arrs sz b.regs.get) (hbd : IdxBound sz i b.regs.get) :
    ∃ s', armIsa.step P i s = some s' ∧ RegRel armRegs s' (evalBMInst b bi).regs.get
      ∧ ArmMemRel arrs sz s' (evalBMInst b bi)
      ∧ (∀ a ∈ arrs, (evalBMInst b bi).regs.get a = b.regs.get a) ∧ FrameM 1 s s' := by
  rcases armSelM_inv h with ⟨d, base, idx, sc, rfl, hd, hi, hb, ha, hda, rfl⟩
    | ⟨base, idx, v, sc, rfl, hv, hi, hb, ha, rfl⟩
    | ⟨bop, d, a, k, rfl, hd, ha, hda, hk, hbop⟩
    | ⟨d, opn, srcs, tag, bb, rfl, hda, hbb, rfl⟩
  · -- the array load
    have hlt : (b.regs.get idx).toNat < sz base := hbd.1 d base idx (by simp [loadStruct?])
    obtain ⟨arr, harr, hat⟩ := hmem base ha
    have hval : read64 b.mem (armAddrR b.regs base idx) = stackGet arr (b.regs.get idx).toNat := by
      rw [armAddrR, shiftLeft_three_eq, hat ⟨_, hlt⟩, ← stackGet_id arr ⟨_, hlt⟩]
    refine ⟨{ s with prog := { s.prog with
        base := (s.prog.base.setReg d (stackGet arr (b.regs.get idx).toNat)).nextPc } },
      ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [armIsa_step_core P _ s (by simp only [mnemOk]; decide +kernel) rfl rfl]
      exact coreStep_loadIdx P d base idx sc (sz base) s arr _ harr (hrel.getW hi)
    · refine RegRel_setReg hrel d _ (fun r _ => ?_)
      simp only [evalBMInst]
      rw [get_set_armRegs _ hd, hval]
    · exact ArmMemRel_setReg hmem d hda hd (read64 b.mem (armAddrR b.regs base idx))
        (evalBMInst b (.ldrr d base idx)) rfl rfl _ _
    · intro x hx
      simp only [evalBMInst]
      rw [get_set_armRegs _ hd, if_neg (fun (e : x = d) => hda (e ▸ hx))]
  · -- the array store
    have hlt : (b.regs.get idx).toNat < sz base :=
      hbd.2 base base idx v (by simp [storeStruct?])
    obtain ⟨arr, harr, hat⟩ := hmem base ha
    have hfmem : (evalBMInst b (.strr v base idx)).mem
        = write64 b.mem (b.regs.get base + BitVec.ofNat 64 (8 * (b.regs.get idx).toNat))
            (b.regs.get v) := by
      simp only [evalBMInst, armAddrR, shiftLeft_three_eq]
    have hcmp : armCmp (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v],
        .store 64 (sz base)) s = none := by
      simp only [armCmp, cmpArgs?]; rw [if_neg (by decide +kernel)]
    refine ⟨{ s with prog := { s.prog with
        base := (s.prog.base.setArr base
          (stackSet arr (b.regs.get idx).toNat (b.regs.get v))).nextPc } },
      ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [armIsa_step_core P _ s (by simp only [mnemOk]; decide +kernel) rfl hcmp]
      exact coreStep_storeIdx P base idx v sc (sz base) s arr _ _ harr (hrel.getW hi)
        (hrel.getW hv)
    · intro r hr
      simp only [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.lvm_nextPc]
      exact hrel r hr
    · intro x hx
      show ∃ arr', _ ∧ ArrAt (evalBMInst b (.strr v base idx)).mem (b.regs.get x) _ arr'
      rw [hfmem]
      by_cases hxb : x = base
      · subst hxb
        refine ⟨stackSet arr (b.regs.get idx).toNat (b.regs.get v), by simp, ?_⟩
        rw [stackSet_eq_of_lt arr _ hlt]
        exact ArrAt_write_cell hat (hsep.2.1 x hx) _ hlt _
      · obtain ⟨arr', harr', hat'⟩ := hmem x hx
        refine ⟨arr', by simpa [hxb] using harr', ?_⟩
        exact ArrAt_write_sep hat' _ _
          (fun j => hsep.2.2 base ha x hx (Ne.symm hxb) ⟨_, hlt⟩ j)
    · intro x _; rfl
  · -- the register-immediate operation
    have hbop' : bop = .add ∨ bop = .sub := by
      rcases hbop with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hval : (evalBMInst b bi).regs = b.regs.set d (bop.apply (b.regs.get a) (BitVec.ofNat 64 k)) := by
      rcases hbop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    have hok : mnemOk armBases
        (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k]) = true := by
      simp only [mnemOk, stripWidthTag_withWidthTag_binOpName' 64 bop]
      rcases hbop' with rfl | rfl <;> decide
    have hcmp : armCmp (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k],
        .reg none) s = none := by
      simp only [armCmp, cmpArgs?]
      rcases hbop' with rfl | rfl <;> rw [if_neg (by decide +kernel)]
    refine ⟨{ s with prog := { s.prog with
        base := (s.prog.base.setReg d (bop.apply (b.regs.get a) (BitVec.ofNat 64 k))).nextPc } },
      ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [armIsa_step_core P _ s hok rfl hcmp]
      exact coreStep_binopImm P bop d a k s _ (by rcases hbop' with rfl | rfl <;> decide)
        (hrel.getW ha)
    · refine RegRel_setReg hrel d _ (fun r _ => ?_)
      rw [hval, get_set_armRegs _ hd]
    · exact ArmMemRel_setReg hmem d hda hd _ _ hval
        (by rcases hbop with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl)
        _ _
    · intro x hx
      rw [hval, get_set_armRegs _ hd, if_neg (fun (e : x = d) => hda (e ▸ hx))]
  · -- a register instruction of `armSel`
    obtain ⟨s', hs', hrel', fr⟩ := armSel_step P hbb s b.regs hrel
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := fr
    have hdst : ∃ w, evalBInst b.regs bb = b.regs.set d w ∧ d ∈ armRegs := by
      rcases armSel_inv hbb with ⟨o, d', a, c, he, ho, hd', -, -, hbi⟩
        | ⟨d', a, tag', he, hd', -, rfl⟩
      · simp only [Prod.mk.injEq, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
          and_true] at he
        obtain ⟨⟨rfl, -, -⟩, -⟩ := he
        simp only [armBops, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          simp only [armBinst, Option.some.injEq] at hbi <;> subst hbi <;>
          exact ⟨_, rfl, hd'⟩
      · simp only [Prod.mk.injEq, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
          and_true] at he
        obtain ⟨⟨rfl, -, -⟩, -⟩ := he
        exact ⟨_, rfl, hd'⟩
    obtain ⟨w, hw, hd⟩ := hdst
    have hbase : ∀ x ∈ arrs, (evalBMInst b (.alu bb)).regs.get x = b.regs.get x := by
      intro x hx
      rw [evalBMInst_alu_regs, hw, get_set_armRegs _ hd, if_neg (fun (e : x = d) => hda (e ▸ hx))]
    refine ⟨s', hs', hrel', ?_, hbase, f1, f2, f4, f5, f6, f7⟩
    intro x hx
    obtain ⟨arr, harr, hat⟩ := hmem x hx
    refine ⟨arr, by rw [f3]; exact harr, ?_⟩
    rw [hbase x hx]; exact hat

/-- The array layout depends on the base registers only. -/
theorem ArmArrsSep_congr {arrs : List String} {sz : String → Nat} {g g' : String → BitVec 64}
    (h : ArmArrsSep arrs sz g) (hg : ∀ a ∈ arrs, g' a = g a) : ArmArrsSep arrs sz g' := by
  refine ⟨h.1, h.2.1, fun a ha a' ha' hne j k => ?_⟩
  rw [hg a ha, hg a' ha']
  exact h.2.2 a ha a' ha' hne j k

/-- **The index bounds of a block**: along the machine run of the selected block, each array
    load or store has its index below the size of its array. -/
def BoundsOK (arrs : List String) (sz : String → Nat) : List LinstrRM → BMState → Prop
  | [], _ => True
  | i :: is, b => IdxBound sz i b.regs.get ∧
      ∀ bi, armSelM arrs sz i = some bi → BoundsOK arrs sz is (evalBMInst b bi)

/-- **The Asm lemma of the AArch64 memory fragment.** For a block `is` that the selection
    `armSelM arrs sz` maps to `bs`: the bytes `encodeBMBlock armAlloc bs` decode to `bs`, and
    from an `LstateMF` related to a machine state `b` on `armRegs` and on the arrays, with the
    array layout `ArmArrsSep` and in-range indices along the run, the `armIsa` run of `is`
    succeeds and ends related to the `BMInst` run `runBMBlock b bs` on `armRegs` and on the
    arrays, with the zero, carry and overflow flags, the function and the word memory
    unchanged and the counter advanced by the length of the block. -/
theorem arm_asm_mem (P : LprogM) (arrs : List String) (sz : String → Nat) :
    ∀ (is : List LinstrRM) (bs : List BMInst), is.mapM (armSelM arrs sz) = some bs →
      ∀ (s : LstateMF) (b : BMState), RegRel armRegs s b.regs.get → ArmMemRel arrs sz s b →
        ArmArrsSep arrs sz b.regs.get → BoundsOK arrs sz is b →
        decodeBMBlock (encodeBMBlock armAlloc bs) = some bs ∧
        ∃ s', armIsa.runL P is s = some s' ∧ RegRel armRegs s' (runBMBlock b bs).regs.get
          ∧ ArmMemRel arrs sz s' (runBMBlock b bs) ∧ FrameM is.length s s'
  | [], bs, h, s, b, hrel, hmem, _, _ => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, s, rfl, hrel, hmem, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | i :: is, bs, h, s, b, hrel, hmem, hsep, hbd => by
      refine ⟨armSelM_decodeBlock _ _ h, ?_⟩
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      obtain ⟨hb1, hbr⟩ := hbd
      obtain ⟨s1, hs1, hrel1, hmem1, hbase1, f1⟩ := armSelM_step P hi s b hrel hmem hsep hb1
      obtain ⟨-, s2, hs2, hrel2, hmem2, f2⟩ := arm_asm_mem P arrs sz is bs' hs s1
        (evalBMInst b bi) hrel1 hmem1 (ArmArrsSep_congr hsep hbase1) (hbr bi hi)
      refine ⟨s2, ?_, hrel2, hmem2, ?_⟩
      · simp only [Isa.runL, hs1, Option.bind_some, hs2]
      · obtain ⟨a1, b1, d1, e1, g1, k1⟩ := f1
        obtain ⟨a2, b2, d2, e2, g2, k2⟩ := f2
        refine ⟨a2.trans a1, b2.trans b1, d2.trans d1, e2.trans e1, g2.trans g1, ?_⟩
        rw [k2, k1, List.length_cons]; omega

/-! ### The branch conditions -/

/-- **The `CBNZ` condition**: for a register of `armRegs`, the `armIsa` branch condition of
    `Lcond (.reg r)` is the `CBNZ` test `r ≠ 0` of a related machine state, and the `CBNZ`
    step takes the branch exactly when it holds. -/
theorem armCond_cbnz (s : LstateMF) (b : BMState) (hrel : RegRel armRegs s b.regs.get)
    {r : String} (hr : r ∈ armRegs) (off : Int) :
    armCond s (.reg r) = decide (b.regs.get r ≠ 0)
      ∧ (evalBMInst b (.cbnz r off)).pc
          = if armCond s (.reg r) then b.pc + BitVec.ofInt 64 off else b.pc + 4 := by
  have hz : r ≠ "Z" ∧ r ≠ "NZ" := by
    have hall : ∀ x ∈ armRegs, x ≠ "Z" ∧ x ≠ "NZ" := by decide
    exact hall r hr
  have hc : armCond s (.reg r) = decide (b.regs.get r ≠ 0) := by
    unfold armCond
    split
    · rename_i he; cases he; exact absurd rfl hz.1
    · rename_i he; cases he; exact absurd rfl hz.2
    · simp only [condNZ, evalOperandN, hrel.getW hr]; rfl
  refine ⟨hc, ?_⟩
  rw [hc]
  simp only [evalBMInst, decide_eq_true_eq]

/-- **The `B.NE` condition**: when the zero flags agree, the `armIsa` branch condition of
    `Lcond (.reg "NZ")` is the `NE` condition of the machine state, and the `B.NE` step takes
    the branch exactly when it holds. -/
theorem armCond_bne (s : LstateMF) (b : BMState) (hz : s.zf = b.zf) (off : Int) :
    armCond s (.reg "NZ") = BCond.ne.holds b.zf b.regs.cf
      ∧ (evalBMInst b (.bcond .ne off)).pc
          = if armCond s (.reg "NZ") then b.pc + BitVec.ofInt 64 off else b.pc + 4 := by
  have hc : armCond s (.reg "NZ") = BCond.ne.holds b.zf b.regs.cf := by
    simp only [armCond, BCond.holds, hz]
  exact ⟨hc, by rw [hc]; rfl⟩

/-! ### The compare and the immediate-offset load and store

The `Lprog` compare `CMP:64 a, c` is the arm `armCmp` of the step and the A64 `CMP`. The
compile-time-offset load `MOVQ d, [p + off]` (tag `.loadC`) and store `MOVQ [p + off], v`
(tag `.storeC`) read and write the word memory `lmem`; at a doubleword offset `off = 8·k`
with `k < 2¹²` they are the A64 `LDR`/`STR` with the unsigned scaled immediate `k`.
`ArmWordRel` relates the word memory on a list of cells to the machine memory, and
`ArmFlagRel` the zero and carry flags. -/

/-- **The word-memory relation** on the cells `cells`: for a cell `(p, off)`, the word
    `lmem p off` of the `LstateMF` is the doubleword of the machine memory at the address in
    the register `p` plus `off`. -/
def ArmWordRel (cells : List (String × Nat)) (s : LstateMF) (b : BMState) : Prop :=
  ∀ c ∈ cells, s.prog.base.lmem c.1 (Int.ofNat c.2)
    = read64 b.mem (b.regs.get c.1 + BitVec.ofNat 64 c.2)

/-- The flag relation: the zero and carry flags of the `LstateMF` are those of the machine. -/
def ArmFlagRel (s : LstateMF) (b : BMState) : Prop :=
  s.zf = b.zf ∧ s.prog.base.cf = b.regs.cf

/-- **The step of the compare**: on registers of `armRegs` of related states, the `armIsa`
    step of `CMP:64 a, c` advances the counter and takes the zero and carry flags of the A64
    `CMP a, c`. -/
theorem armIsa_step_cmp (P : LprogM) (x : LOperand) (a c : String) (tag : MemTag)
    (s : LstateMF) (b : BMState) (hrel : RegRel armRegs s b.regs.get) (ha : a ∈ armRegs)
    (hc : c ∈ armRegs) :
    armIsa.step P (.Lopn [x] (withWidthTag 64 "CMP") [.reg a, .reg c], tag) s
      = some { prog := { s.prog with base := { s.prog.base.nextPc with
          cf := (evalBMInst b (.cmp a c)).regs.cf } }, zf := (evalBMInst b (.cmp a c)).zf } := by
  have hok : mnemOk armBases (.Lopn [x] (withWidthTag 64 "CMP") [.reg a, .reg c]) = true := by
    simp only [mnemOk]; decide +kernel
  rw [armIsa_step]
  simp only [subsetStep, isCtl, hok, Bool.false_eq_true, if_false, if_true, armCmp, cmpArgs?,
    evalOperandN, hrel.getW ha, hrel.getW hc, evalBMInst]

/-- A register write leaves the carry flag of the A64 register file. -/
theorem BState_cf_set (b : BState) (r : String) (v : BitVec 64) : (b.set r v).cf = b.cf := by
  unfold BState.set; split <;> rfl

/-- **The AArch64 selection of the compare and the immediate-offset load and store** over the
    arrays `arrs` and the cells `cells`: `CMP:64 a, c` becomes `CMP a, c`, a load
    `MOVQ d, [p + off]` of a cell becomes `LDR d, [p, #off]` and a store `MOVQ [p + off], v`
    of a cell becomes `STR v, [p, #off]`, for a doubleword offset `off < 2¹⁵`. The registers
    are in `armRegs`, and the destination of a load is neither an array base nor a cell
    base. -/
def armSelC (arrs : List String) (cells : List (String × Nat)) : LinstrRM → Option BMInst
  | (.Lopn [_] opn [.reg a, .reg c], _) =>
      if opn = withWidthTag 64 "CMP" ∧ a ∈ armRegs ∧ c ∈ armRegs then some (.cmp a c) else none
  | (.Lopn [.reg d] opn [.arr p off], .loadC) =>
      if opn = "MOVQ" ∧ d ∈ armRegs ∧ p ∈ armRegs ∧ (p, off) ∈ cells ∧ d ∉ arrs
          ∧ (∀ c ∈ cells, c.1 ≠ d) ∧ off % 8 = 0 ∧ off / 8 < 0x1000 then
        some (.ldr d p (off / 8))
      else none
  | (.Lopn [.arr p off] opn [.reg v], .storeC) =>
      if opn = "MOVQ" ∧ v ∈ armRegs ∧ p ∈ armRegs ∧ (p, off) ∈ cells ∧ off % 8 = 0
          ∧ off / 8 < 0x1000 then
        some (.str v p (off / 8))
      else none
  | _ => none

/-- The destination of an instruction is a register outside the cell bases. -/
def armDstFree (cells : List (String × Nat)) : LinstrRM → Bool
  | (.Lopn [.reg d] _ _, _) => cells.all (fun c => c.1 != d)
  | _ => false

/-- **The AArch64 selection with the compare and the word memory**: `armSelC`, and otherwise
    the memory selection `armSelM` on an instruction whose destination is not a cell base. -/
def armSelX (arrs : List String) (sz : String → Nat) (cells : List (String × Nat))
    (i : LinstrRM) : Option BMInst :=
  match armSelC arrs cells i with
  | some bi => some bi
  | none => if armDstFree cells i then armSelM arrs sz i else none

/-- **The inversion of `armSelC`.** -/
theorem armSelC_inv {arrs : List String} {cells : List (String × Nat)} {i : LinstrRM}
    {bi : BMInst} (h : armSelC arrs cells i = some bi) :
    (∃ x a c tag, i = (.Lopn [x] (withWidthTag 64 "CMP") [.reg a, .reg c], tag)
        ∧ a ∈ armRegs ∧ c ∈ armRegs ∧ bi = .cmp a c)
    ∨ (∃ d p off, i = (.Lopn [.reg d] "MOVQ" [.arr p off], .loadC)
        ∧ d ∈ armRegs ∧ p ∈ armRegs ∧ (p, off) ∈ cells ∧ d ∉ arrs ∧ (∀ c ∈ cells, c.1 ≠ d)
        ∧ off % 8 = 0 ∧ off / 8 < 0x1000 ∧ bi = .ldr d p (off / 8))
    ∨ (∃ p off v, i = (.Lopn [.arr p off] "MOVQ" [.reg v], .storeC)
        ∧ v ∈ armRegs ∧ p ∈ armRegs ∧ (p, off) ∈ cells ∧ off % 8 = 0 ∧ off / 8 < 0x1000
        ∧ bi = .str v p (off / 8)) := by
  unfold armSelC at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, ha, hc'⟩ := hc
      cases h
      exact Or.inl ⟨_, _, _, _, rfl, ha, hc', rfl⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨rfl, hd, hp, hpc, hda, hcd, h8, hk⟩ := hc
      cases h
      exact Or.inr (Or.inl ⟨_, _, _, rfl, hd, hp, hpc, hda, hcd, h8, hk, rfl⟩)
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨rfl, hv, hp, hpc, h8, hk⟩ := hc
      cases h
      exact Or.inr (Or.inr ⟨_, _, _, rfl, hv, hp, hpc, h8, hk, rfl⟩)
    · cases h
  · cases h

/-- **The byte round trip of a selected instruction of `armSelX`.** -/
theorem armSelX_decode {arrs : List String} {sz : String → Nat} {cells : List (String × Nat)}
    {i : LinstrRM} {bi : BMInst} (h : armSelX arrs sz cells i = some bi) :
    decodeBM64 (encodeBMInst armAlloc bi) = some bi := by
  unfold armSelX at h
  split at h
  · rename_i bi' hc
    cases h
    rcases armSelC_inv hc with ⟨x, a, c, tag, -, ha, hc', rfl⟩
      | ⟨d, p, off, -, hd, hp, -, -, -, -, hk, rfl⟩ | ⟨p, off, v, -, hv, hp, -, -, hk, rfl⟩
    · rw [roundtrip_bminst_cmp armAlloc a c (xRegName_xNum_armRegs ha)
        (xRegName_xNum_armRegs hc'), gpOf_armAlloc ha, gpOf_armAlloc hc']
    · rw [roundtrip_bminst_ldr armAlloc d p _ (xRegName_xNum_armRegs hd)
        (xRegName_xNum_armRegs hp) hk, gpOf_armAlloc hd, gpOf_armAlloc hp]
    · rw [roundtrip_bminst_str armAlloc v p _ (xRegName_xNum_armRegs hv)
        (xRegName_xNum_armRegs hp) hk, gpOf_armAlloc hv, gpOf_armAlloc hp]
  · split at h
    · exact armSelM_decode h
    · cases h

/-- **The block round trip of `armSelX`.** -/
theorem armSelX_decodeBlock {arrs : List String} {sz : String → Nat}
    {cells : List (String × Nat)} :
    ∀ (is : List LinstrRM) (bs : List BMInst), is.mapM (armSelX arrs sz cells) = some bs →
      decodeBMBlock (encodeBMBlock armAlloc bs) = some bs
  | [], bs, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; rfl
  | i :: is, bs, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      simp only [encodeBMBlock, List.flatMap_cons]
      rw [decodeBMBlock_append _ _ (encodeBMInst_length armAlloc bi), armSelX_decode hi]
      simp only [Option.bind_some]
      have ih := armSelX_decodeBlock is bs' hs
      simp only [encodeBMBlock] at ih
      rw [ih]
      rfl

/-- **The effect of an instruction of the memory selection** on the machine: the
    instruction has a register destination `d`; the zero and carry flags and every register
    other than `d` are unchanged; the memory is unchanged or written at a cell of the array
    `d`. -/
theorem armSelM_effect {arrs : List String} {sz : String → Nat} {i : LinstrRM} {bi : BMInst}
    (h : armSelM arrs sz i = some bi) (b : BMState) (hbd : IdxBound sz i b.regs.get) :
    ∃ d opn srcs, i.1 = .Lopn [.reg d] opn srcs
      ∧ (evalBMInst b bi).zf = b.zf ∧ (evalBMInst b bi).regs.cf = b.regs.cf
      ∧ (∀ r, r ≠ d → (evalBMInst b bi).regs.get r = b.regs.get r)
      ∧ ((evalBMInst b bi).mem = b.mem
        ∨ ∃ (j : Fin (sz d)) (v : BitVec 64), d ∈ arrs
          ∧ (evalBMInst b bi).mem
            = write64 b.mem (b.regs.get d + BitVec.ofNat 64 (8 * j.val)) v) := by
  rcases armSelM_inv h with ⟨d, base, idx, sc, rfl, hd, -, -, -, -, rfl⟩
    | ⟨base, idx, v, sc, rfl, -, -, -, ha, rfl⟩
    | ⟨bop, d, a, k, rfl, hd, -, -, -, hbop⟩
    | ⟨d, opn, srcs, tag, bb, rfl, -, hbb, rfl⟩
  · refine ⟨d, _, _, rfl, rfl, BState_cf_set _ _ _, fun r hr => ?_, Or.inl rfl⟩
    simp only [evalBMInst]
    rw [get_set_armRegs _ hd, if_neg hr]
  · have hlt : (b.regs.get idx).toNat < sz base :=
      hbd.2 base base idx v (by simp [storeStruct?])
    refine ⟨base, _, _, rfl, rfl, rfl, fun r _ => rfl, Or.inr ⟨⟨_, hlt⟩, b.regs.get v, ha, ?_⟩⟩
    simp only [evalBMInst, armAddrR, shiftLeft_three_eq]
  · rcases hbop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨d, _, _, rfl, rfl, BState_cf_set _ _ _, fun r hr => ?_, Or.inl rfl⟩
      simp only [evalBMInst]
      rw [get_set_armRegs _ hd, if_neg hr]
    · refine ⟨d, _, _, rfl, rfl, BState_cf_set _ _ _, fun r hr => ?_, Or.inl rfl⟩
      simp only [evalBMInst]
      rw [get_set_armRegs _ hd, if_neg hr]
  · have hdst : ∃ w, evalBInst b.regs bb = b.regs.set d w ∧ d ∈ armRegs := by
      rcases armSel_inv hbb with ⟨o, d', a, c, he, ho, hd', -, -, hbi⟩
        | ⟨d', a, tag', he, hd', -, rfl⟩
      · simp only [Prod.mk.injEq, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
          and_true] at he
        obtain ⟨⟨rfl, -, -⟩, -⟩ := he
        simp only [armBops, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          simp only [armBinst, Option.some.injEq] at hbi <;> subst hbi <;>
          exact ⟨_, rfl, hd'⟩
      · simp only [Prod.mk.injEq, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
          and_true] at he
        obtain ⟨⟨rfl, -, -⟩, -⟩ := he
        exact ⟨_, rfl, hd'⟩
    obtain ⟨w, hw, hd⟩ := hdst
    refine ⟨d, opn, srcs, rfl, rfl, ?_, fun r hr => ?_, Or.inl rfl⟩
    · rw [evalBMInst_alu_regs, hw, BState_cf_set]
    · rw [evalBMInst_alu_regs, hw, get_set_armRegs _ hd, if_neg hr]

/-- **The layout of the word cells**: distinct cells at the addresses `g p + off` are
    separated, and each cell is separated from each cell of each array of `arrs`. -/
def ArmCellsSep (arrs : List String) (sz : String → Nat) (cells : List (String × Nat))
    (g : String → BitVec 64) : Prop :=
  (∀ c ∈ cells, ∀ c' ∈ cells, c ≠ c' →
    MemSep (g c.1 + BitVec.ofNat 64 c.2) (g c'.1 + BitVec.ofNat 64 c'.2))
  ∧ ∀ c ∈ cells, ∀ a ∈ arrs, ∀ j : Fin (sz a),
    MemSep (g c.1 + BitVec.ofNat 64 c.2) (g a + BitVec.ofNat 64 (8 * j.val))

/-- The layout of the word cells depends on the array bases and the cell bases only. -/
theorem ArmCellsSep_congr {arrs : List String} {sz : String → Nat}
    {cells : List (String × Nat)} {g g' : String → BitVec 64} (h : ArmCellsSep arrs sz cells g)
    (ha : ∀ a ∈ arrs, g' a = g a) (hc : ∀ c ∈ cells, g' c.1 = g c.1) :
    ArmCellsSep arrs sz cells g' := by
  refine ⟨fun c hc1 c' hc2 hne => ?_, fun c hc1 a ha1 j => ?_⟩
  · rw [hc c hc1, hc c' hc2]; exact h.1 c hc1 c' hc2 hne
  · rw [hc c hc1, ha a ha1]; exact h.2 c hc1 a ha1 j

/-- **The one-step simulation of `armSelX`**: from states related on `armRegs`, on the arrays,
    on the word cells and on the flags, with the array and cell layouts and in-range indices,
    the `armIsa` step of a selected instruction succeeds and the result is related to the
    `BMInst` step in the same four relations, with the array and cell base registers
    unchanged and the frame of one step. -/
theorem armSelX_step (P : LprogM) {arrs : List String} {sz : String → Nat}
    {cells : List (String × Nat)} {i : LinstrRM} {bi : BMInst}
    (h : armSelX arrs sz cells i = some bi) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel arrs sz s b)
    (hword : ArmWordRel cells s b) (hflag : ArmFlagRel s b)
    (hsep : ArmArrsSep arrs sz b.regs.get) (hcs : ArmCellsSep arrs sz cells b.regs.get)
    (hbd : IdxBound sz i b.regs.get) :
    ∃ s', armIsa.step P i s = some s' ∧ RegRel armRegs s' (evalBMInst b bi).regs.get
      ∧ ArmMemRel arrs sz s' (evalBMInst b bi) ∧ ArmWordRel cells s' (evalBMInst b bi)
      ∧ ArmFlagRel s' (evalBMInst b bi)
      ∧ (∀ a ∈ arrs, (evalBMInst b bi).regs.get a = b.regs.get a)
      ∧ (∀ c ∈ cells, (evalBMInst b bi).regs.get c.1 = b.regs.get c.1) ∧ FrameX 1 s s' := by
  unfold armSelX at h
  split at h
  · rename_i bi' hc
    cases h
    rcases armSelC_inv hc with ⟨x, a, c, tag, rfl, ha, hc', rfl⟩
      | ⟨d, p, off, rfl, hd, hp, hpc, hda, hcd, h8, hk, rfl⟩
      | ⟨p, off, v, rfl, hv, hp, hpc, h8, hk, rfl⟩
    · -- the compare
      refine ⟨_, armIsa_step_cmp P x a c tag s b hrel ha hc', fun r hr => ?_, hmem, hword,
        ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
      exact hrel r hr
    · -- the immediate-offset load
      have haddr : armAddrI b.regs p (off / 8) = b.regs.get p + BitVec.ofNat 64 off := by
        rw [armAddrI, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h8)]
      have hval : read64 b.mem (armAddrI b.regs p (off / 8))
          = s.prog.base.lmem p (Int.ofNat off) := by
        rw [haddr]; exact (hword (p, off) hpc).symm
      have hok : mnemOk armBases (.Lopn [.reg d] "MOVQ" [.arr p off]) = true := by
        simp only [mnemOk]; decide +kernel
      refine ⟨{ s with prog := { s.prog with
          base := (s.prog.base.setReg d (s.prog.base.lmem p (Int.ofNat off))).nextPc } },
        ?_, ?_, ?_, ?_, ⟨hflag.1, ?_⟩, ?_, ?_, rfl, rfl, rfl⟩
      · rw [armIsa_step_core P _ s hok rfl rfl]
        exact coreStep_loadC P d p off s
      · refine RegRel_setReg hrel d _ (fun r _ => ?_)
        simp only [evalBMInst]
        rw [get_set_armRegs _ hd, hval]
      · exact ArmMemRel_setReg hmem d hda hd _ (evalBMInst b (.ldr d p (off / 8))) rfl rfl _ _
      · intro c hc
        simp only [LstateM.lmem_nextPc, LstateM.lmem_setReg, evalBMInst]
        rw [get_set_armRegs _ hd, if_neg (hcd c hc)]
        exact hword c hc
      · exact (BState_cf_set _ _ _).symm ▸ hflag.2
      · intro a ha
        simp only [evalBMInst]
        rw [get_set_armRegs _ hd, if_neg (fun (e : a = d) => hda (e ▸ ha))]
      · intro c hc
        simp only [evalBMInst]
        rw [get_set_armRegs _ hd, if_neg (hcd c hc)]
    · -- the immediate-offset store
      have haddr : armAddrI b.regs p (off / 8) = b.regs.get p + BitVec.ofNat 64 off := by
        rw [armAddrI, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h8)]
      have hok : mnemOk armBases (.Lopn [.arr p off] "MOVQ" [.reg v]) = true := by
        simp only [mnemOk]; decide +kernel
      have hfmem : (evalBMInst b (.str v p (off / 8))).mem
          = write64 b.mem (b.regs.get p + BitVec.ofNat 64 off) (b.regs.get v) := by
        simp only [evalBMInst, haddr]
      refine ⟨{ s with prog := { s.prog with
          base := (s.prog.base.storeMemC p (Int.ofNat off) (b.regs.get v)).nextPc } },
        ?_, ?_, ?_, ?_, hflag, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
      · rw [armIsa_step_core P _ s hok rfl rfl]
        exact coreStep_storeC P p v off s _ (hrel.getW hv)
      · intro r hr
        simp only [LstateM.reg_nextPc, LstateM.reg_storeMemC, LstateN.lvm_nextPc]
        exact hrel r hr
      · intro a ha
        obtain ⟨arr, harr, hat⟩ := hmem a ha
        refine ⟨arr, by simpa using harr, ?_⟩
        show ArrAt (evalBMInst b (.str v p (off / 8))).mem (b.regs.get a) _ arr
        rw [hfmem]
        exact ArrAt_write_sep hat _ _ (fun j => hcs.2 (p, off) hpc a ha j)
      · intro c hc
        show _ = read64 (evalBMInst b (.str v p (off / 8))).mem
          (b.regs.get c.1 + BitVec.ofNat 64 c.2)
        rw [hfmem]
        by_cases hce : c = (p, off)
        · subst hce
          simp only [LstateM.lmem_nextPc, LstateM.lmem_storeMemC_same]
          rw [read64_write64_same]
        · have hne : ¬ (c.1 = p ∧ Int.ofNat c.2 = Int.ofNat off) := by
            rintro ⟨h1, h2⟩
            exact hce (Prod.ext h1 (Int.ofNat.inj h2))
          simp only [LstateM.lmem_nextPc, LstateM.lmem_storeMemC_other _ _ _ _ _ _ hne]
          rw [read64_write64_sep _ _ (hcs.1 (p, off) hpc c hc (Ne.symm hce))]
          exact hword c hc
  · split at h
    · rename_i hnone hfree
      obtain ⟨s', hs', hrel', hmem', hbase, f1, f2, f3, f4, f5, f6⟩ :=
        armSelM_step P h s b hrel hmem hsep hbd
      obtain ⟨d, opn, srcs, hi, hz, hcf, hother, hmeff⟩ := armSelM_effect h b hbd
      have hcd : ∀ c ∈ cells, c.1 ≠ d := by
        obtain ⟨i1, i2⟩ := i
        simp only at hi
        subst hi
        simp only [armDstFree, List.all_eq_true, bne_iff_ne, ne_eq] at hfree
        exact hfree
      refine ⟨s', hs', hrel', hmem', fun c hc => ?_, ⟨?_, ?_⟩, hbase,
        fun c hc => hother _ (hcd c hc), f2, f5, f6⟩
      · rw [f3, hother _ (hcd c hc), hword c hc]
        rcases hmeff with he | ⟨j, v, hda, he⟩
        · rw [he]
        · rw [he, read64_write64_sep _ _ (by
            obtain ⟨m1, m2⟩ := hcs.2 c hc d hda j
            exact ⟨m2, m1⟩)]
      · rw [f1, hz]; exact hflag.1
      · rw [f4, hcf]; exact hflag.2
    · cases h

/-- **The index bounds of a block of `armSelX`**: along the machine run of the selected
    block, each array load or store has its index below the size of its array. -/
def BoundsOKX (arrs : List String) (sz : String → Nat) (cells : List (String × Nat)) :
    List LinstrRM → BMState → Prop
  | [], _ => True
  | i :: is, b => IdxBound sz i b.regs.get ∧
      ∀ bi, armSelX arrs sz cells i = some bi → BoundsOKX arrs sz cells is (evalBMInst b bi)

/-- **The Asm lemma of the AArch64 fragment with the compare and the word memory.** For a
    block `is` that `armSelX arrs sz cells` maps to `bs`: the bytes
    `encodeBMBlock armAlloc bs` decode to `bs`, and from an `LstateMF` related to a machine
    state `b` on `armRegs`, on the arrays, on the word cells and on the zero and carry flags,
    with the array and cell layouts and in-range indices along the run, the `armIsa` run of
    `is` succeeds and ends related to `runBMBlock b bs` in the same four relations, with the
    function and the overflow flag unchanged and the counter advanced by the length of the
    block. -/
theorem arm_asm_x (P : LprogM) (arrs : List String) (sz : String → Nat)
    (cells : List (String × Nat)) :
    ∀ (is : List LinstrRM) (bs : List BMInst), is.mapM (armSelX arrs sz cells) = some bs →
      ∀ (s : LstateMF) (b : BMState), RegRel armRegs s b.regs.get → ArmMemRel arrs sz s b →
        ArmWordRel cells s b → ArmFlagRel s b → ArmArrsSep arrs sz b.regs.get →
        ArmCellsSep arrs sz cells b.regs.get → BoundsOKX arrs sz cells is b →
        decodeBMBlock (encodeBMBlock armAlloc bs) = some bs ∧
        ∃ s', armIsa.runL P is s = some s' ∧ RegRel armRegs s' (runBMBlock b bs).regs.get
          ∧ ArmMemRel arrs sz s' (runBMBlock b bs) ∧ ArmWordRel cells s' (runBMBlock b bs)
          ∧ ArmFlagRel s' (runBMBlock b bs) ∧ FrameX is.length s s'
  | [], bs, h, s, b, hrel, hmem, hword, hflag, _, _, _ => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, s, rfl, hrel, hmem, hword, hflag, rfl, rfl, rfl⟩
  | i :: is, bs, h, s, b, hrel, hmem, hword, hflag, hsep, hcs, hbd => by
      refine ⟨armSelX_decodeBlock _ _ h, ?_⟩
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      obtain ⟨hb1, hbr⟩ := hbd
      obtain ⟨s1, hs1, hrel1, hmem1, hword1, hflag1, hbase1, hcell1, f1⟩ :=
        armSelX_step P hi s b hrel hmem hword hflag hsep hcs hb1
      obtain ⟨-, s2, hs2, hrel2, hmem2, hword2, hflag2, f2⟩ := arm_asm_x P arrs sz cells is bs'
        hs s1 (evalBMInst b bi) hrel1 hmem1 hword1 hflag1 (ArmArrsSep_congr hsep hbase1)
        (ArmCellsSep_congr hcs hbase1 hcell1) (hbr bi hi)
      refine ⟨s2, ?_, hrel2, hmem2, hword2, hflag2, ?_⟩
      · simp only [Isa.runL, hs1, Option.bind_some, hs2]
      · obtain ⟨a1, b1, k1⟩ := f1
        obtain ⟨a2, b2, k2⟩ := f2
        refine ⟨a2.trans a1, b2.trans b1, ?_⟩
        rw [k2, k1, List.length_cons]; omega

/-! ### The `mpn_and_n` loop body at AArch64 -/

/-- The `mpn_and_n` limb body at AArch64 registers, over arrays of `n` limbs: the inputs at
    `x0`, `x1`, the output at `x3`, the index `x4` and the count `x2`. The two loads, the
    conjunction and the store of the canonical chain, the index step and the count step, as in
    `RvIsa.rvAndBody`. The back edge is `Lcond (.reg "x2")`, whose condition `armCond_cbnz`
    relates to `CBNZ x2`. -/
def armAndBody (n : Nat) : List LinstrRM :=
  [ (.Lopn [.reg "x9"] "LOADIDX" [.arrIdx "x1" "x4" 8], .load 64 n)
  , (.Lopn [.reg "x10"] "LOADIDX" [.arrIdx "x0" "x4" 8], .load 64 n)
  , (.Lopn [.reg "x11"] "AND:64" [.reg "x9", .reg "x10"], .reg none)
  , (.Lopn [.reg "x3"] "STOREIDX" [.arrIdx "x3" "x4" 8, .reg "x11"], .store 64 n)
  , (.Lopn [.reg "x4"] "ADD:64" [.reg "x4", .imm 1], .reg none)
  , (.Lopn [.reg "x2"] "SUB:64" [.reg "x2", .imm 1], .reg none) ]

/-- The arrays of the `mpn_and_n` body. -/
def armAndArrs : List String := ["x0", "x1", "x3"]

/-- The AArch64 instructions of the `mpn_and_n` body. -/
def armAndCode : List BMInst :=
  [ .ldrr "x9" "x1" "x4", .ldrr "x10" "x0" "x4", .alu (.and "x11" "x9" "x10"),
    .strr "x11" "x3" "x4", .addi "x4" "x4" 1, .subi "x2" "x2" 1 ]

/-- The registers of the `mpn_and_n` body are registers of `armRegs`. -/
theorem armAndRegs_mem :
    "x0" ∈ armRegs ∧ "x1" ∈ armRegs ∧ "x2" ∈ armRegs ∧ "x3" ∈ armRegs ∧ "x4" ∈ armRegs
      ∧ "x9" ∈ armRegs ∧ "x10" ∈ armRegs ∧ "x11" ∈ armRegs := by
  decide

/-- The memory selection maps the `mpn_and_n` body to `armAndCode`. -/
theorem armAndBody_sel (n : Nat) :
    (armAndBody n).mapM (armSelM armAndArrs (fun _ => n)) = some armAndCode := by
  simp [armAndRegs_mem, armAndBody, armSelM, armSel, armBopOf?, armBops, armBinst, armImmOf?,
    armAndArrs, armAndCode, withWidthTag, binOpName]

/-- The index bounds of the `mpn_and_n` body hold when the index `x4` is below `n`. -/
theorem armAndBody_bounds (n : Nat) (b : BMState) (h : (b.regs.get "x4").toNat < n) :
    BoundsOK armAndArrs (fun _ => n) (armAndBody n) b := by
  simp [armAndRegs_mem, BoundsOK, IdxBound, armAndBody, loadStruct?, storeStruct?, armSelM,
    armSel, armBopOf?, armBops, armBinst, armImmOf?, armAndArrs, withWidthTag, binOpName] at h ⊢
  refine ⟨h, by simpa [evalBMInst, BState.set] using h, ?_⟩
  rintro _ _ _ _ rfl rfl rfl rfl
  simpa [evalBMInst, evalBInst, BState.set] using h

/-- **The `mpn_and_n` body at AArch64 bytes.** The bytes of `armAndCode` decode to it, and from
    an `LstateMF` related to a machine state on `armRegs` and on the arrays `x0`, `x1`, `x3` of
    `n` limbs, laid out separately, with the index `x4` below `n`, the `armIsa` run of the body
    succeeds and ends related to the machine run of `armAndCode`. -/
theorem arm_and_body (P : LprogM) (n : Nat) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel armAndArrs (fun _ => n) s b)
    (hsep : ArmArrsSep armAndArrs (fun _ => n) b.regs.get) (hidx : (b.regs.get "x4").toNat < n) :
    decodeBMBlock (encodeBMBlock armAlloc armAndCode) = some armAndCode ∧
    ∃ s', armIsa.runL P (armAndBody n) s = some s'
      ∧ RegRel armRegs s' (runBMBlock b armAndCode).regs.get
      ∧ ArmMemRel armAndArrs (fun _ => n) s' (runBMBlock b armAndCode)
      ∧ FrameM 6 s s' :=
  arm_asm_mem P armAndArrs (fun _ => n) (armAndBody n) armAndCode (armAndBody_sel n) s b hrel
    hmem hsep (armAndBody_bounds n b hidx)

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
