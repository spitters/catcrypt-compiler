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

/-- **The AArch64 data**: the AAPCS64 register file with the intra-procedure-call registers
    `x16`, `x17` as scratch, the save slot of a callee-saved register at its index, the
    three-address legaliser data (no tied form, the commutative bases, the copy `MOV` at the
    width of the operation), and the leakage regime `armLeaksOperands`. -/
def armData : IsaData where
  allocPool := armAllocPool
  scratch := ["x16", "x17"]
  argRegs := armArgRegs
  calleeSaved := armCalleeSaved
  saveSlot := fun r => armCalleeSaved.findIdx? (· == r)
  tied := fun _ _ => false
  commutes := fun base => ["ADD", "MUL", "AND", "OR", "XOR"].contains base
  tieScratch := "x16"
  copyMnemonic := fun opn => if hasSuffix opn ":64" then some "MOV:64" else some "MOV"
  leaksOperands := armLeaksOperands

/-! ## The step -/

/-- The mnemonic bases of the AArch64 alphabet. -/
def armBases : List String :=
  ["ADD", "SUB", "AND", "OR", "XOR", "MUL", "MOV", "CMP", "LOADIDX", "STOREIDX", "LOAD",
   "STORE", "MOVQ"]

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

/-- No base of the AArch64 alphabet leaks its data operands under `PSTATE.DIT = 1`. -/
theorem armIsa_leaksOperands_bases : ∀ b ∈ armBases, armIsa.leaksOperands b = false := by
  decide

/-! ## Instruction selection -/

/-- The register-arithmetic operations of the selection. -/
def armBops : List JasminBinOp := [.add, .sub, .and, .or, .xor]

/-- The operation whose 64-bit mnemonic is `opn`, among `armBops`. -/
def bopOf? (opn : String) : Option JasminBinOp :=
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
        (bopOf? opn).bind (fun o => armBinst o d a b)
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

/-- The inversion of `bopOf?`. -/
theorem bopOf?_eq_some {opn : String} {o : JasminBinOp} (h : bopOf? opn = some o) :
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
      obtain ⟨hopn, hmem⟩ := bopOf?_eq_some ho
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

/-- The frame of a register step: the zero flag, the function, the arrays, the word memory
    and the carry and overflow flags are unchanged and the counter advances by `n`. -/
def Frame (n : Nat) (s s' : LstateMF) : Prop :=
  s'.zf = s.zf ∧ s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.larr = s.prog.base.larr
    ∧ s'.prog.base.lmem = s.prog.base.lmem ∧ s'.prog.base.cf = s.prog.base.cf
    ∧ s'.prog.base.of = s.prog.base.of ∧ s'.prog.base.reg.lpc = s.prog.base.reg.lpc + n

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

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
