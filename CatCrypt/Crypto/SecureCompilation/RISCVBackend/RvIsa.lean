/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaSubset
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
public import CatCrypt.Crypto.SecureCompilation.CT.RiscvTiming
public import CatCrypt.Crypto.SecureCompilation.MachineMem64

@[expose] public section

set_option autoImplicit false

/-!
# The RV64 instance of the `Lprog` instruction-set record

`rvIsa` is the `LprogIsa.Isa` of RV64. Its data are the RISC-V psABI register file and calling
convention (allocatable `a0`–`a7`, `t0`–`t4`, scratch `t5`/`t6`, arguments `a0`–`a7`,
callee-saved `s0`–`s11`), the three-address legaliser data (no tied form) and the leakage
regime of the Zkt table `CT.RvMnem` (`rvLeaksOperands`). RV64 has no
flags register: the step is `LprogIsa.subsetStep` over the alphabet `rvBases` with no
instruction-set arm, so it writes none of `zf`, `cf`, `of`, and the branch condition is the
register test `condNZ` (`BNEZ`). The alphabet has no compare and none of the x86 carry,
wide-multiply and flag mnemonics; `rvIsa_refuse_x86` states that the step of each of them
is `none`.

The instruction selection `rvSel` maps the register fragment of the alphabet (64-bit `ADD`,
`SUB`, `AND`, `OR`, `XOR` with three register operands, and the register `MOV`) on the
registers `rvRegs` to `RInst64`. `RiscvEncoder64.encodeRBlock64` writes its bytes, and
`decodeRBlock64` reads them back through `SailRiscvDecoder64.riscvDecode64`.

`rv_asm` is the Asm lemma of the register fragment: for a selected block, the encoded bytes
decode to the selected instructions, and the `RInst64` run of those instructions agrees with
the `rvIsa` run of the `Lprog` block on every register of `rvRegs`, with memory, flags,
function and the counter advance of the `Lprog` run stated.

The memory selection `rvSelM` adds the array load and store at width 64 (the address
`base + 8 idx` formed in the scratch register `t5`, then `LD` or `SD` with offset 0) and the
64-bit `ADD`/`SUB` with an immediate (`ADDI`), on the registers `rvMemRegs`. `rv_asm_mem` is
its Asm lemma: the register relation on `rvMemRegs` and the memory relation `MemRel`, which
places each array at the address held in its base register, are preserved under the array
layout `ArrsSep` and the index bounds `MemBounds`. `rvCond_bne` relates the register branch
condition to `BNE r, zero`. `rv_and_body` instantiates the Asm lemma at the `mpn_and_n` limb
body.

## Main results

* `rvIsa`: the RV64 instruction set.
* `rvLeaksOperands`, `rvIsa_leaksOperands_bases`: the leakage regime of Zkt and its
  operand-leaking bases, the loads and stores.
* `rvIsa_refuse_x86`: the x86-only mnemonics have no step.
* `rvSel`, `rvSel_decode`, `rvSel_step`: the selection, its byte round trip and its one-step
  simulation.
* `decodeRBlock64`, `rv_asm`: the block decoder and the Asm lemma of the register fragment.
* `rvSelM`, `rvSelM_step`, `rvSelM_roundTrip`, `decodeRMBlock64`, `rv_asm_mem`: the memory
  selection, its one-step simulation, its byte round trip and its Asm lemma.
* `rvCond_bne`: the branch condition and `BNE`.
* `rvAndBody`, `rv_and_body`: the `mpn_and_n` body at RV64 bytes.
-/

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64

/-! ## The instruction-set data -/

/-- The registers of the selection: `a0`–`a7` and `t0`–`t6`, the non-zero registers of the
    decoder round trip `regName_reg5`. -/
def rvRegs : List String :=
  ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4", "t5", "t6"]

/-- The RISC-V psABI callee-saved registers `s0`–`s11`. -/
def rvCalleeSaved : List String :=
  ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]

/-- The RV64 mnemonic of a mnemonic base of the RV64 alphabet `rvBases`: the register
    operations as `rvSel` selects them, `MUL` as `MUL`, `MOV` and `MOVQ` as `MV`, the loads
    and stores as `LD` and `SD`. `none` for a base outside the alphabet. -/
def rvMnemOfBase : String → Option CT.RvMnem
  | "ADD" => some .add
  | "SUB" => some .sub
  | "AND" => some .and
  | "OR" => some .or
  | "XOR" => some .xor
  | "MUL" => some .mul
  | "MOV" => some .mv
  | "MOVQ" => some .mv
  | "LOAD" => some .ld
  | "LOADIDX" => some .ld
  | "STORE" => some .sd
  | "STOREIDX" => some .sd
  | _ => none

/-- The RV64 leakage regime of an implementation of Zkt: the table `CT.RvMnem` at the
    mnemonic of the base, every operand observable for a base outside the alphabet. -/
def rvLeaksOperands (base : String) : Bool :=
  ((rvMnemOfBase base).map CT.RvMnem.leaksOperands).getD true

/-- **The RV64 data**: the psABI register file with `t5`, `t6` as scratch, the save slot of a
    callee-saved register at its index, the three-address legaliser data (no tied form, the
    commutative bases, the copy `MOV` at the width of the operation), and the leakage regime
    `rvLeaksOperands`. -/
def rvData : IsaData where
  allocPool := ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4"]
  scratch := ["t5", "t6"]
  argRegs := ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
  calleeSaved := rvCalleeSaved
  saveSlot := fun r => rvCalleeSaved.findIdx? (· == r)
  tied := fun _ _ => false
  commutes := fun base => ["ADD", "MUL", "AND", "OR", "XOR"].contains base
  tieScratch := "t5"
  copyMnemonic := fun opn => if hasSuffix opn ":64" then some "MOV:64" else some "MOV"
  leaksOperands := rvLeaksOperands

/-! ## The step -/

/-- The mnemonic bases of the RV64 alphabet: no compare, no flag-reading or flag-writing
    mnemonic. -/
def rvBases : List String :=
  ["ADD", "SUB", "AND", "OR", "XOR", "MUL", "MOV", "LOADIDX", "STOREIDX", "LOAD", "STORE",
   "MOVQ"]

/-- The RV64 branch condition: the register is non-zero (`BNEZ`). -/
def rvCond (s : LstateMF) (c : LOperand) : Bool := condNZ s.prog.base c

/-- **The RV64 instruction set**: the data `rvData`, the flagless step of the alphabet
    `rvBases`, and the register branch condition `rvCond`. -/
def rvIsa : Isa where
  toIsaData := rvData
  step := subsetStep rvBases rvCond (fun _ _ => none)
  condEval := rvCond
  step_ctl := subsetStep_ctl rvBases rvCond (fun _ _ => none)

theorem rvIsa_step : rvIsa.step = subsetStep rvBases rvCond (fun _ _ => none) := rfl

theorem rvIsa_condEval : rvIsa.condEval = rvCond := rfl

theorem rvIsa_leaksOperands : rvIsa.leaksOperands = rvLeaksOperands := rfl

/-- The bases of the RV64 alphabet that leak their data operands under Zkt are the loads and
    stores, which Zkt excludes. -/
theorem rvIsa_leaksOperands_bases :
    rvBases.filter rvIsa.leaksOperands = ["LOADIDX", "STOREIDX", "LOAD", "STORE"] := by
  decide

/-- The x86 mnemonic bases with no RV64 counterpart: the flag compare, the carry chain
    (`ADC`, `SBB`, `ADCX`, `ADOX`) and the flag-quiet wide multiply (`MULX`, `MULXHI`). -/
def x86OnlyBases : List String := ["CMP", "ADC", "SBB", "ADCX", "ADOX", "MULX", "MULXHI"]

/-- **The x86-only mnemonics are refused on RV64**: an `Lopn` whose mnemonic base is one of
    `x86OnlyBases`, at any width tag and on any operands, has no `rvIsa` step. -/
theorem rvIsa_refuse_x86 (P : LprogM) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (tag : MemTag) (s : LstateMF)
    (h : stripWidthTag opn ∈ x86OnlyBases) :
    rvIsa.step P (.Lopn dsts opn srcs, tag) s = none := by
  have hall : ∀ b ∈ x86OnlyBases, rvBases.contains b = false := by decide
  rw [rvIsa_step]
  exact subsetStep_refuse _ _ _ P dsts opn srcs tag s (hall _ h)

/-- `MULX` at width 64 is refused on RV64. -/
theorem rvIsa_refuse_mulx (P : LprogM) (dsts srcs : List LOperand) (tag : MemTag)
    (s : LstateMF) : rvIsa.step P (.Lopn dsts "MULX:64" srcs, tag) s = none :=
  rvIsa_refuse_x86 P dsts _ srcs tag s (by decide +kernel)

/-- `ADCX` at width 64 is refused on RV64. -/
theorem rvIsa_refuse_adcx (P : LprogM) (dsts srcs : List LOperand) (tag : MemTag)
    (s : LstateMF) : rvIsa.step P (.Lopn dsts "ADCX:64" srcs, tag) s = none :=
  rvIsa_refuse_x86 P dsts _ srcs tag s (by decide +kernel)

/-! ## Instruction selection -/

/-- The register-arithmetic operations of the selection. -/
def rvBops : List JasminBinOp := [.add, .sub, .and, .or, .xor]

/-- The operation whose 64-bit mnemonic is `opn`, among `rvBops`. -/
def bopOf? (opn : String) : Option JasminBinOp :=
  rvBops.find? (fun o => withWidthTag 64 (binOpName o) == opn)

/-- The `RInst64` of a register-arithmetic operation. -/
def rvRinst (bop : JasminBinOp) (d a b : String) : Option RInst64 :=
  match bop with
  | .add => some (.add d a b)
  | .sub => some (.sub d a b)
  | .and => some (.and d a b)
  | .or => some (.or d a b)
  | .xor => some (.xor d a b)
  | _ => none

/-- **The RV64 selection of the register fragment**: a 64-bit three-register `ADD`, `SUB`,
    `AND`, `OR` or `XOR` with the register tag, and a 64-bit register `MOV`, over the
    registers `rvRegs`. -/
def rvSel : LinstrRM → Option RInst64
  | (.Lopn [.reg d] opn [.reg a, .reg b], .reg none) =>
      if rvRegs.contains d && rvRegs.contains a && rvRegs.contains b then
        (bopOf? opn).bind (fun o => rvRinst o d a b)
      else none
  | (.Lopn [.reg d] opn [.reg a], _) =>
      if opn == withWidthTag 64 "MOV" && rvRegs.contains d && rvRegs.contains a then
        some (.mv d a)
      else none
  | _ => none

/-- The inversion of `bopOf?`. -/
theorem bopOf?_eq_some {opn : String} {o : JasminBinOp} (h : bopOf? opn = some o) :
    opn = withWidthTag 64 (binOpName o) ∧ o ∈ rvBops := by
  have hp := List.find?_some h
  exact ⟨(beq_iff_eq.mp hp).symm, List.mem_of_find?_eq_some h⟩

/-- **The inversion of the selection**: a selected instruction is a register-arithmetic
    instruction of `rvBops` or a register `MOV`, on registers of `rvRegs`. -/
theorem rvSel_inv {i : LinstrRM} {ri : RInst64} (h : rvSel i = some ri) :
    (∃ o d a b, i = (.Lopn [.reg d] (withWidthTag 64 (binOpName o)) [.reg a, .reg b], .reg none)
        ∧ o ∈ rvBops ∧ d ∈ rvRegs ∧ a ∈ rvRegs ∧ b ∈ rvRegs ∧ rvRinst o d a b = some ri)
    ∨ (∃ d a tag, i = (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a], tag)
        ∧ d ∈ rvRegs ∧ a ∈ rvRegs ∧ ri = .mv d a) := by
  unfold rvSel at h
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

/-- Every register of `rvRegs` is an emitted register of the decoder round trip. -/
theorem emittedRegs_of_rvRegs {r : String} (h : r ∈ rvRegs) : r ∈ emittedRegs := by
  have hall : ∀ x ∈ rvRegs, x ∈ emittedRegs := by decide
  exact hall r h

/-- No register of `rvRegs` is the zero register. -/
theorem ne_zero_of_rvRegs {r : String} (h : r ∈ rvRegs) : ¬ (r = "zero" ∨ r = "x0") := by
  have hall : ∀ x ∈ rvRegs, ¬ (x = "zero" ∨ x = "x0") := by decide
  exact hall r h

/-! ## The byte round trip -/

/-- The little-endian word of four bytes. -/
def leWord32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  BitVec.ofNat 32 (b0.toNat + b1.toNat * 0x100 + b2.toNat * 0x10000 + b3.toNat * 0x1000000)

/-- Decode a byte stream of 4-byte RV64 words with `riscvDecode64`; `none` on a word outside
    the decoder or a trailing partial word. -/
def decodeRBlock64 : List (BitVec 8) → Option (List RInst64)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (riscvDecode64 (leWord32 b0 b1 b2 b3)).bind
        (fun i => (decodeRBlock64 rest).map (fun is => i :: is))
  | _ => none

/-- The little-endian bytes of a word followed by a stream decode as the word followed by the
    stream. -/
theorem decodeRBlock64_wordLE (w : BitVec 32) (rest : List (BitVec 8)) :
    decodeRBlock64 (wordLE w ++ rest) =
      (riscvDecode64 w).bind (fun i => (decodeRBlock64 rest).map (fun is => i :: is)) := by
  have hw : leWord32 (BitVec.ofNat 8 (w.toNat &&& 0xff)) (BitVec.ofNat 8 ((w.toNat >>> 8) &&& 0xff))
      (BitVec.ofNat 8 ((w.toNat >>> 16) &&& 0xff)) (BitVec.ofNat 8 ((w.toNat >>> 24) &&& 0xff))
      = w := by
    apply BitVec.eq_of_toNat_eq
    have hlt := w.isLt
    simp only [leWord32, show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  simp only [wordLE, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeRBlock64, hw]

/-- A selected instruction is not the `LI` pseudo-instruction, and its encoder word is the
    word its bytes carry. -/
theorem rvSel_encode {i : LinstrRM} {ri : RInst64} (h : rvSel i = some ri) :
    encodeRInst64 ri = wordLE (encodeWord64 ri).get! := by
  rcases rvSel_inv h with ⟨o, d, a, b, -, ho, -, -, -, hri⟩ | ⟨d, a, -, -, -, -, rfl⟩
  · simp only [rvBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rvRinst, Option.some.injEq] at hri <;>
      subst hri <;> rfl
  · rfl

/-- **The byte round trip of a selected instruction**: decoding the encoder word with
    `riscvDecode64` recovers the instruction. -/
theorem rvSel_decode {i : LinstrRM} {ri : RInst64} (h : rvSel i = some ri) :
    riscvDecode64 (encodeWord64 ri).get! = some ri := by
  rcases rvSel_inv h with ⟨o, d, a, b, -, ho, hd, ha, hb, hri⟩ | ⟨d, a, -, -, hd, ha, rfl⟩
  · have ed := emittedRegs_of_rvRegs hd
    have ea := emittedRegs_of_rvRegs ha
    have eb := emittedRegs_of_rvRegs hb
    simp only [rvBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rvRinst, Option.some.injEq] at hri <;>
      subst hri <;>
      exact roundtrip_RInst64 _ (fun _ _ h => by cases h)
        ⟨ed, by simp only [rinst64DstSrcs, List.mem_cons, List.not_mem_nil, or_false]
                rintro r (rfl | rfl) <;> assumption⟩ (fun _ _ _ h => by simp at h)
  · exact roundtrip_RInst64 _ (fun _ _ h => by cases h)
      ⟨emittedRegs_of_rvRegs hd, by
        simp only [rinst64DstSrcs, List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl; exact emittedRegs_of_rvRegs ha⟩ (fun _ _ _ h => by simp at h)

/-- **The block round trip**: the encoded bytes of a selected block decode to the block. -/
theorem rvSel_decodeBlock :
    ∀ (is : List LinstrRM) (rs : List RInst64), is.mapM rvSel = some rs →
      decodeRBlock64 (encodeRBlock64 rs) = some rs
  | [], rs, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; rfl
  | i :: is, rs, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨ri, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      simp only [encodeRBlock64, List.flatMap_cons]
      rw [rvSel_encode hi, decodeRBlock64_wordLE, rvSel_decode hi]
      simp only [Option.bind_some]
      have ih := rvSel_decodeBlock is rs' hs
      simp only [encodeRBlock64] at ih
      rw [ih]
      rfl

/-! ## The step simulation -/

/-- The frame of a register step: the zero flag, the function, the arrays, the word memory
    and the carry and overflow flags are unchanged and the counter advances by `n`. -/
def Frame (n : Nat) (s s' : LstateMF) : Prop :=
  s'.zf = s.zf ∧ s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.larr = s.prog.base.larr
    ∧ s'.prog.base.lmem = s.prog.base.lmem ∧ s'.prog.base.cf = s.prog.base.cf
    ∧ s'.prog.base.of = s.prog.base.of ∧ s'.prog.base.reg.lpc = s.prog.base.reg.lpc + n

/-- A machine write to a register of `rvRegs` reads back as the write on `rvRegs`. -/
theorem get_set_rvRegs (b : RState64) {d : String} (hd : d ∈ rvRegs) (v : BitVec 64)
    {r : String} (hr : r ∈ rvRegs) : (b.set d v).get r = if r = d then v else b.get r := by
  have hdz := ne_zero_of_rvRegs hd
  have hrz := ne_zero_of_rvRegs hr
  by_cases hrd : r = d
  · subst hrd; simp only [RState64.get, RState64.set, hdz, if_false, if_true]
  · simp only [RState64.get, RState64.set, hdz, hrz, if_false, hrd]

/-- **The one-step simulation of the selection**: from related states, the `rvIsa` step of
    a selected instruction succeeds, and the result is related to the `RInst64` step of the
    selected instruction, with the frame of one step. -/
theorem rvSel_step (P : LprogM) {i : LinstrRM} {ri : RInst64} (h : rvSel i = some ri)
    (s : LstateMF) (b : RState64) (hrel : RegRel rvRegs s b.get) :
    ∃ s', rvIsa.step P i s = some s' ∧ RegRel rvRegs s' (evalRInst64 b ri).get
      ∧ Frame 1 s s' := by
  rcases rvSel_inv h with ⟨o, d, a, c, rfl, ho, hd, ha, hc, hri⟩ | ⟨d, a, tag, rfl, hd, ha, rfl⟩
  · have hstrip := stripWidthTag_withWidthTag_binOpName' 64 o
    simp only [rvBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    have hok : mnemOk rvBases
        (.Lopn [.reg d] (withWidthTag 64 (binOpName o)) [.reg a, .reg c]) = true := by
      simp only [mnemOk, hstrip]
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨{ s with prog := { s.prog with
      base := (s.prog.base.setReg d (o.apply (b.get a) (b.get c))).nextPc } },
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [rvIsa_step]
      simp only [subsetStep, isCtl, hok, Bool.false_eq_true, if_false, if_true]
      exact coreStep_binop P o d a c s _ _ (hrel.getW ha) (hrel.getW hc)
    · refine RegRel_setReg hrel d _ (fun r hr => ?_)
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        simp only [rvRinst, Option.some.injEq] at hri <;> subst hri <;>
        simp only [evalRInst64, get_set_rvRegs b hd _ hr, JasminBinOp.apply, opAdd64, opSub64,
          opAnd64, opOr64, opXor64]
  · have hok : mnemOk rvBases (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a]) = true := by
      simp only [mnemOk]
      rw [show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide +kernel]
      decide
    refine ⟨{ s with prog := { s.prog with base := (s.prog.base.setReg d (b.get a)).nextPc } },
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [rvIsa_step]
      simp only [subsetStep, isCtl, hok, Bool.false_eq_true, if_false, if_true]
      exact coreStep_mov P d a tag s _ (hrel a ha)
    · exact RegRel_setReg hrel d _ (fun r hr => by simp only [evalRInst64, get_set_rvRegs b hd _ hr])

/-- **The Asm lemma of the RV64 register fragment.** For a block `is` that the selection maps
    to `rs`: the bytes `encodeRBlock64 rs` decode to `rs`, and from an `LstateMF` related to a
    machine state `b` on `rvRegs`, the `rvIsa` run of `is` succeeds and ends related to the
    `RInst64` run `runRBlock64 b rs`, with the flags, the function, the arrays and the word
    memory unchanged and the counter advanced by the length of the block. -/
theorem rv_asm (P : LprogM) :
    ∀ (is : List LinstrRM) (rs : List RInst64), is.mapM rvSel = some rs →
      ∀ (s : LstateMF) (b : RState64), RegRel rvRegs s b.get →
        decodeRBlock64 (encodeRBlock64 rs) = some rs ∧
        ∃ s', rvIsa.runL P is s = some s' ∧ RegRel rvRegs s' (runRBlock64 b rs).get
          ∧ Frame is.length s s'
  | [], rs, h, s, b, hrel => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, s, rfl, hrel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | i :: is, rs, h, s, b, hrel => by
      refine ⟨rvSel_decodeBlock _ _ h, ?_⟩
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨ri, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      obtain ⟨s1, hs1, hrel1, f1⟩ := rvSel_step P hi s b hrel
      obtain ⟨-, s2, hs2, hrel2, f2⟩ := rv_asm P is rs' hs s1 (evalRInst64 b ri) hrel1
      refine ⟨s2, ?_, hrel2, ?_⟩
      · simp only [Isa.runL, hs1, Option.bind_some, hs2]
      · obtain ⟨a1, b1, c1, d1, e1, g1, k1⟩ := f1
        obtain ⟨a2, b2, c2, d2, e2, g2, k2⟩ := f2
        refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, g2.trans g1, ?_⟩
        rw [k2, k1, List.length_cons]; omega

/-! ## The memory fragment -/

open CatCrypt.Crypto.SecureCompilation.MachineMem64

/-- An array cell of shape `(64, n)` reads back at that shape. -/
theorem getArr_of_larr {s : LstateM} {base : String} {n : Nat} {arr : Fin n → BitVec 64}
    (h : s.larr base = ⟨64, n, arr⟩) : s.getArr base 64 n = some arr := by
  unfold LstateM.getArr
  rw [h]
  simp

/-- **The core step of an array load** `d := base[idx]` at width 64: the destination takes
    the element `stackGet arr idx` of the array. -/
theorem coreStep_loadIdx (P : LprogM) (d base idx : String) (sc n : Nat) (s : LstateMF)
    (arr : Fin n → BitVec 64) (vi : BitVec 64) (harr : s.prog.base.larr base = ⟨64, n, arr⟩)
    (hvi : s.prog.base.reg.getW idx 64 = some vi) :
    coreStep P (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], .load 64 n) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setReg d (stackGet arr vi.toNat)).nextPc } } := by
  have hga : s.prog.base.getArr base 64 n = some arr := getArr_of_larr harr
  unfold coreStep
  have hmov : movRegArgs? (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], MemTag.load 64 n)
      = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩]
  simp only [lsemStepMem, loadStruct?, if_true, hga, hvi, Option.map_some]

/-- **The core step of an array store** `base[idx] := v` at width 64: the array takes the
    update `stackSet arr idx v`. -/
theorem coreStep_storeIdx (P : LprogM) (base idx v : String) (sc n : Nat) (s : LstateMF)
    (arr : Fin n → BitVec 64) (vi vv : BitVec 64) (harr : s.prog.base.larr base = ⟨64, n, arr⟩)
    (hvi : s.prog.base.reg.getW idx 64 = some vi) (hvv : s.prog.base.reg.getW v 64 = some vv) :
    coreStep P (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v], .store 64 n) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setArr base (stackSet arr vi.toNat vv)).nextPc } } := by
  have hga : s.prog.base.getArr base 64 n = some arr := getArr_of_larr harr
  unfold coreStep
  have hmov : movRegArgs? (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v],
      MemTag.store 64 n) = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩]
  simp only [lsemStepMem, storeStruct?, if_true, hga, hvi, hvv, Option.map_some]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift in
/-- **The core step of a 64-bit register-immediate arithmetic instruction** `d := a ⊙ k`: the
    destination takes the value of the operation on the immediate `k` at width 64. -/
theorem coreStep_binopImm (P : LprogM) (bop : JasminBinOp) (d a : String) (k : Nat)
    (s : LstateMF) (va : BitVec 64) (hsar : binOpName bop ≠ "SAR")
    (hva : s.prog.base.reg.getW a 64 = some va) :
    coreStep P (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k], .reg none) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setReg d (bop.apply va (BitVec.ofNat 64 k))).nextPc } } := by
  have hstrip := stripWidthTag_withWidthTag_binOpName' 64 bop
  have hm : mulhiStruct? (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k])
      = none := by
    simp only [mulhiStruct?]
  have hs : sarStruct? (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k])
      = none := by
    simp only [sarStruct?, hstrip, if_neg hsar]
  have hstep : lsemStepMem
      (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k], .reg none) s.prog.base
      = some ((s.prog.base.setReg d (bop.apply va (BitVec.ofNat 64 k))).nextPc) := by
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm rfl rfl rfl rfl, lsemStepSh_of_not_sar _ _ hs]
    simp only [lsemStepN, readReg_of_getW hva, evalOperandN, hstrip,
      applyOpnN_binOpName, Option.map_some]
    rfl
  unfold coreStep
  have hmov : movRegArgs?
      (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k], MemTag.reg none)
      = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩, hstep]
  rfl

/-- On an in-range index the update `stackSet` changes that cell only. -/
theorem stackSet_eq_of_lt {w n : Nat} (arr : Fin n → BitVec w) (k : Nat) (hk : k < n)
    (v : BitVec w) : stackSet arr k v = fun j => if j.val = k then v else arr j := by
  cases n with
  | zero => omega
  | succ m =>
      funext j
      simp only [stackSet, Fin.ext_iff, Nat.mod_eq_of_lt hk]

/-- The registers of the memory selection: `rvRegs` without the scratch registers `t5`,
    `t6`. The address of an array access is formed in `t5`. -/
def rvMemRegs : List String :=
  ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4"]

theorem rvRegs_of_rvMemRegs {r : String} (h : r ∈ rvMemRegs) : r ∈ rvRegs := by
  have hall : ∀ x ∈ rvMemRegs, x ∈ rvRegs := by decide
  exact hall r h

theorem ne_t5_of_rvMemRegs {r : String} (h : r ∈ rvMemRegs) : r ≠ "t5" := by
  have hall : ∀ x ∈ rvMemRegs, x ≠ "t5" := by decide
  exact hall r h

theorem not_mem_of_contains_false {l : List String} {a : String} (h : l.contains a = false) :
    a ∉ l := fun hm => by rw [List.contains_iff_mem.mpr hm] at h; cases h

/-- The address of the element `base[idx]` of a doubleword array in `t5`:
    `SLLI t5, idx, 3 ; ADD t5, base, t5`. -/
def rvIdxAddr (base idx : String) : List RMInst64 :=
  [.alu (.slli "t5" idx 3), .alu (.add "t5" base "t5")]

/-- **The RV64 selection of the memory fragment** over the arrays `arrs` of sizes `sz`: an
    array load `LOADIDX` at width 64 becomes the address computation and `LD d, 0(t5)`, an
    array store `STOREIDX` at width 64 the address computation and `SD v, 0(t5)`, and an
    instruction of the register selection `rvSel` on the registers `rvMemRegs` with its
    destination outside `arrs` becomes that instruction. The array bases are registers of
    `rvMemRegs` holding the array addresses; no register write touches them. -/
def rvSelM (arrs : List String) (sz : String → Nat) : LinstrRM → Option (List RMInst64)
  | (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx _], .load 64 n) =>
      if rvMemRegs.contains d && rvMemRegs.contains idx && rvMemRegs.contains base
          && arrs.contains base && !arrs.contains d && n == sz base then
        some (rvIdxAddr base idx ++ [.ld d "t5" 0])
      else none
  | (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx _, .reg v], .store 64 n) =>
      if dst == base && rvMemRegs.contains v && rvMemRegs.contains idx
          && rvMemRegs.contains base && arrs.contains base && n == sz base then
        some (rvIdxAddr base idx ++ [.sd v "t5" 0])
      else none
  | (.Lopn [.reg d] "ADD:64" [.reg a, .imm k], .reg none) =>
      if rvMemRegs.contains d && rvMemRegs.contains a && !arrs.contains d && 0 < k && k < 2048
      then some [.addi d a k] else none
  | (.Lopn [.reg d] "SUB:64" [.reg a, .imm k], .reg none) =>
      if rvMemRegs.contains d && rvMemRegs.contains a && !arrs.contains d && 0 < k && k ≤ 2048
      then some [.addi d a (-(k : Int))] else none
  | i => (rvSel i).bind (fun ri =>
      if (rinst64DstSrcs ri).2.all rvMemRegs.contains && rvMemRegs.contains (rinst64DstSrcs ri).1
          && !arrs.contains (rinst64DstSrcs ri).1 then some [.alu ri] else none)

/-- **The inversion of the memory selection.** -/
theorem rvSelM_inv {arrs : List String} {sz : String → Nat} {i : LinstrRM}
    {rs : List RMInst64} (h : rvSelM arrs sz i = some rs) :
    (∃ d base idx sc, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], .load 64 (sz base))
        ∧ d ∈ rvMemRegs ∧ idx ∈ rvMemRegs ∧ base ∈ rvMemRegs ∧ base ∈ arrs ∧ d ∉ arrs
        ∧ rs = rvIdxAddr base idx ++ [.ld d "t5" 0])
    ∨ (∃ base idx v sc, i = (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v],
          .store 64 (sz base))
        ∧ v ∈ rvMemRegs ∧ idx ∈ rvMemRegs ∧ base ∈ rvMemRegs ∧ base ∈ arrs
        ∧ rs = rvIdxAddr base idx ++ [.sd v "t5" 0])
    ∨ (∃ d a k, i = (.Lopn [.reg d] "ADD:64" [.reg a, .imm k], .reg none)
        ∧ d ∈ rvMemRegs ∧ a ∈ rvMemRegs ∧ d ∉ arrs ∧ 0 < k ∧ k < 2048
        ∧ rs = [.addi d a k])
    ∨ (∃ d a k, i = (.Lopn [.reg d] "SUB:64" [.reg a, .imm k], .reg none)
        ∧ d ∈ rvMemRegs ∧ a ∈ rvMemRegs ∧ d ∉ arrs ∧ 0 < k ∧ k ≤ 2048
        ∧ rs = [.addi d a (-(k : Int))])
    ∨ (∃ ri, rvSel i = some ri ∧ (∀ r ∈ (rinst64DstSrcs ri).2, r ∈ rvMemRegs)
        ∧ (rinst64DstSrcs ri).1 ∈ rvMemRegs ∧ (rinst64DstSrcs ri).1 ∉ arrs ∧ rs = [.alu ri]) := by
  unfold rvSelM at h
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
  · rename_i d a k
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true',
        decide_eq_true_eq] at hc
      cases h
      obtain ⟨⟨⟨⟨hd, ha⟩, hda⟩, h0⟩, hk⟩ := hc
      exact Or.inr (Or.inr (Or.inl
        ⟨d, a, k, rfl, hd, ha, not_mem_of_contains_false hda, h0, hk, rfl⟩))
    · cases h
  · rename_i d a k
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true',
        decide_eq_true_eq] at hc
      cases h
      obtain ⟨⟨⟨⟨hd, ha⟩, hda⟩, h0⟩, hk⟩ := hc
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, a, k, rfl, hd, ha, not_mem_of_contains_false hda, h0, hk, rfl⟩)))
    · cases h
  · obtain ⟨ri, hri, h'⟩ := Option.bind_eq_some_iff.mp h
    split at h'
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
        Bool.not_eq_true'] at hc
      cases h'
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨ri, hri, hc.1.1, hc.1.2, not_mem_of_contains_false hc.2, rfl⟩)))
    · cases h'

/-! ### The memory relation and the machine address computation -/

/-- **The memory relation**: each array `a` of `arrs` has shape `(64, sz a)` in the `Lprog`
    state, and the machine memory holds it at the address in the register `a`. -/
def MemRel (arrs : List String) (sz : String → Nat) (s : LstateMF) (b : RMState64) : Prop :=
  ∀ a ∈ arrs, ∃ arr : Fin (sz a) → BitVec 64,
    s.prog.base.larr a = ⟨64, sz a, arr⟩ ∧ ArrAt b.mem (b.regs.get a) (sz a) arr

/-- **The array layout**: each array of `arrs` has at most `2⁶¹` doublewords, and the cells
    of distinct arrays at the addresses `g a` are separated. -/
def ArrsSep (arrs : List String) (sz : String → Nat) (g : String → BitVec 64) : Prop :=
  (∀ a ∈ arrs, a ∈ rvMemRegs) ∧ (∀ a ∈ arrs, 8 * sz a ≤ 2 ^ 64) ∧
  ∀ a ∈ arrs, ∀ a' ∈ arrs, a ≠ a' → ∀ (j : Fin (sz a)) (k : Fin (sz a')),
    MemSep (g a + BitVec.ofNat 64 (8 * j.val)) (g a' + BitVec.ofNat 64 (8 * k.val))

/-- **The index bound** of an instruction under the register values `g`: the index of an
    array load or store is below the size of its array. -/
def IdxBound (sz : String → Nat) (i : LinstrRM) (g : String → BitVec 64) : Prop :=
  (∀ d base idx, loadStruct? i.1 = some (d, base, idx) → (g idx).toNat < sz base) ∧
  (∀ d base idx v, storeStruct? i.1 = some (d, base, idx, v) → (g idx).toNat < sz base)

/-- The frame of a step of the memory fragment: the zero flag, the function, the word memory
    and the carry and overflow flags are unchanged and the counter advances by `n`. -/
def FrameM (n : Nat) (s s' : LstateMF) : Prop :=
  s'.zf = s.zf ∧ s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.lmem = s.prog.base.lmem
    ∧ s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of
    ∧ s'.prog.base.reg.lpc = s.prog.base.reg.lpc + n

/-- A left shift by 3 is the multiplication by 8. -/
theorem shl3_eq (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

/-- The address computation `rvIdxAddr` writes `base + 8 idx` to `t5`, changes no other
    register and leaves the memory unchanged. -/
theorem idxAddr_facts (b : RMState64) {base : String} (idx : String) (hb : base ≠ "t5") :
    (runRMBlock64 b (rvIdxAddr base idx)).regs.get "t5"
        = b.regs.get base + BitVec.ofNat 64 (8 * (b.regs.get idx).toNat)
      ∧ (∀ r, r ≠ "t5" → (runRMBlock64 b (rvIdxAddr base idx)).regs.get r = b.regs.get r)
      ∧ (runRMBlock64 b (rvIdxAddr base idx)).mem = b.mem := by
  have ht5 : ¬ ("t5" = "zero" ∨ "t5" = "x0") := by decide
  refine ⟨?_, ?_, rfl⟩
  · simp only [rvIdxAddr, runRMBlock64_cons, runRMBlock64_nil, evalRMInst64, evalRInst64,
      RState64.get_set_same _ _ _ ht5, RState64.get_set_other _ _ _ _ hb, opAdd64, shl3_eq]
  · intro r hr
    simp only [rvIdxAddr, runRMBlock64_cons, runRMBlock64_nil, evalRMInst64, evalRInst64,
      RState64.get_set_other _ _ _ _ hr]

/-- The `rvIsa` step of an instruction of the alphabet outside the control instructions is
    the core step. -/
theorem rvIsa_step_core (P : LprogM) (d : List LOperand) (opn : String) (srcs : List LOperand)
    (tag : MemTag) (s : LstateMF) (h : rvBases.contains (stripWidthTag opn) = true) :
    rvIsa.step P (.Lopn d opn srcs, tag) s = coreStep P (.Lopn d opn srcs, tag) s := by
  rw [rvIsa_step]
  simp only [subsetStep, isCtl, mnemOk, h, Bool.false_eq_true, if_false, if_true]

/-- **The one-step simulation of an array load**: the `rvIsa` step of `LOADIDX` and the
    machine run of the address computation and `LD` preserve the register relation on
    `rvMemRegs`, the memory relation and the array base registers. -/
theorem rvSelM_step_load (P : LprogM) {arrs : List String} {sz : String → Nat}
    (d base idx : String) (sc : Nat) (hd : d ∈ rvMemRegs) (hi : idx ∈ rvMemRegs)
    (hb : base ∈ rvMemRegs) (ha : base ∈ arrs) (hda : d ∉ arrs)
    (s : LstateMF) (b : RMState64) (hrel : RegRel rvMemRegs s b.regs.get)
    (hmem : MemRel arrs sz s b) (hsep : ArrsSep arrs sz b.regs.get)
    (hlt : (b.regs.get idx).toNat < sz base) :
    ∃ s', rvIsa.step P (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], .load 64 (sz base)) s
          = some s'
      ∧ RegRel rvMemRegs s' (runRMBlock64 b (rvIdxAddr base idx ++ [.ld d "t5" 0])).regs.get
      ∧ MemRel arrs sz s' (runRMBlock64 b (rvIdxAddr base idx ++ [.ld d "t5" 0]))
      ∧ (∀ a ∈ arrs, (runRMBlock64 b (rvIdxAddr base idx ++ [.ld d "t5" 0])).regs.get a
          = b.regs.get a)
      ∧ FrameM 1 s s' := by
  obtain ⟨arr, harr, hat⟩ := hmem base ha
  obtain ⟨h5, hoth, hm⟩ := idxAddr_facts b idx (ne_t5_of_rvMemRegs hb)
  have hval : MachineMem64.read64 (runRMBlock64 b (rvIdxAddr base idx)).mem
      (rvAddr (runRMBlock64 b (rvIdxAddr base idx)).regs "t5" 0)
      = stackGet arr (b.regs.get idx).toNat := by
    rw [hm, rvAddr, h5, show ∀ x : BitVec 64, x + BitVec.ofInt 64 0 = x from
      fun x => by simp, hat ⟨_, hlt⟩, ← stackGet_id arr ⟨_, hlt⟩]
  have hrun : runRMBlock64 b (rvIdxAddr base idx ++ [.ld d "t5" 0])
      = evalRMInst64 (runRMBlock64 b (rvIdxAddr base idx)) (.ld d "t5" 0) := by
    rw [runRMBlock64_append]; rfl
  have hreg : ∀ r, r ≠ d → r ≠ "t5" →
      (runRMBlock64 b (rvIdxAddr base idx ++ [.ld d "t5" 0])).regs.get r = b.regs.get r := by
    intro r hrd hr5
    rw [hrun]
    simp only [evalRMInst64]
    rw [RState64.get_set_other _ _ _ _ hrd, hoth r hr5]
  refine ⟨{ s with prog := { s.prog with
      base := (s.prog.base.setReg d (stackGet arr (b.regs.get idx).toNat)).nextPc } },
    ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [rvIsa_step_core P _ _ _ _ s (by decide)]
    exact coreStep_loadIdx P d base idx sc (sz base) s arr _ harr (hrel.getW hi)
  · refine RegRel_setReg hrel d _ (fun r hr => ?_)
    rw [hrun]
    simp only [evalRMInst64]
    rw [get_set_rvRegs _ (rvRegs_of_rvMemRegs hd) _ (rvRegs_of_rvMemRegs hr), hval,
      hoth r (ne_t5_of_rvMemRegs hr)]
  · intro a haa
    obtain ⟨arr', harr', hat'⟩ := hmem a haa
    refine ⟨arr', by simpa using harr', ?_⟩
    have had : a ≠ d := fun e => hda (e ▸ haa)
    rw [hreg a had (ne_t5_of_rvMemRegs (hsep.1 a haa)), hrun]
    simp only [evalRMInst64]
    rw [hm]; exact hat'
  · intro a haa
    exact hreg a (fun e => hda (e ▸ haa)) (ne_t5_of_rvMemRegs (hsep.1 a haa))

/-- **The one-step simulation of an array store**: the `rvIsa` step of `STOREIDX` and the
    machine run of the address computation and `SD` preserve the register relation on
    `rvMemRegs`, the memory relation and the array base registers. -/
theorem rvSelM_step_store (P : LprogM) {arrs : List String} {sz : String → Nat}
    (base idx v : String) (sc : Nat) (hv : v ∈ rvMemRegs) (hi : idx ∈ rvMemRegs)
    (hb : base ∈ rvMemRegs) (ha : base ∈ arrs)
    (s : LstateMF) (b : RMState64) (hrel : RegRel rvMemRegs s b.regs.get)
    (hmem : MemRel arrs sz s b) (hsep : ArrsSep arrs sz b.regs.get)
    (hlt : (b.regs.get idx).toNat < sz base) :
    ∃ s', rvIsa.step P (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v],
          .store 64 (sz base)) s = some s'
      ∧ RegRel rvMemRegs s' (runRMBlock64 b (rvIdxAddr base idx ++ [.sd v "t5" 0])).regs.get
      ∧ MemRel arrs sz s' (runRMBlock64 b (rvIdxAddr base idx ++ [.sd v "t5" 0]))
      ∧ (∀ a ∈ arrs, (runRMBlock64 b (rvIdxAddr base idx ++ [.sd v "t5" 0])).regs.get a
          = b.regs.get a)
      ∧ FrameM 1 s s' := by
  obtain ⟨arr, harr, hat⟩ := hmem base ha
  obtain ⟨h5, hoth, hm⟩ := idxAddr_facts b idx (ne_t5_of_rvMemRegs hb)
  have hrun : runRMBlock64 b (rvIdxAddr base idx ++ [.sd v "t5" 0])
      = evalRMInst64 (runRMBlock64 b (rvIdxAddr base idx)) (.sd v "t5" 0) := by
    rw [runRMBlock64_append]; rfl
  have hfmem : (runRMBlock64 b (rvIdxAddr base idx ++ [.sd v "t5" 0])).mem
      = MachineMem64.write64 b.mem
          (b.regs.get base + BitVec.ofNat 64 (8 * (b.regs.get idx).toNat)) (b.regs.get v) := by
    rw [hrun]
    simp only [evalRMInst64]
    rw [hm, rvAddr, h5, show ∀ x : BitVec 64, x + BitVec.ofInt 64 0 = x from
      fun x => by simp, hoth v (ne_t5_of_rvMemRegs hv)]
  have hreg : ∀ r, r ≠ "t5" →
      (runRMBlock64 b (rvIdxAddr base idx ++ [.sd v "t5" 0])).regs.get r = b.regs.get r := by
    intro r hr5
    rw [hrun]
    exact hoth r hr5
  refine ⟨{ s with prog := { s.prog with
      base := (s.prog.base.setArr base
        (stackSet arr (b.regs.get idx).toNat (b.regs.get v))).nextPc } },
    ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [rvIsa_step_core P _ _ _ _ s (by decide)]
    exact coreStep_storeIdx P base idx v sc (sz base) s arr _ _ harr (hrel.getW hi)
      (hrel.getW hv)
  · intro r hr
    simp only [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.lvm_nextPc]
    rw [hreg r (ne_t5_of_rvMemRegs hr)]
    exact hrel r hr
  · intro a haa
    rw [hreg a (ne_t5_of_rvMemRegs (hsep.1 a haa)), hfmem]
    by_cases hab : a = base
    · subst hab
      refine ⟨stackSet arr (b.regs.get idx).toNat (b.regs.get v), by simp, ?_⟩
      rw [stackSet_eq_of_lt arr _ hlt]
      exact ArrAt_write_cell hat (hsep.2.1 a haa) _ hlt _
    · obtain ⟨arr', harr', hat'⟩ := hmem a haa
      refine ⟨arr', by simpa [hab] using harr', ?_⟩
      exact ArrAt_write_sep hat' _ _
        (fun j => hsep.2.2 base ha a haa (Ne.symm hab) ⟨_, hlt⟩ j)
  · intro a haa
    exact hreg a (ne_t5_of_rvMemRegs (hsep.1 a haa))

/-- **The one-step simulation of a register instruction on `rvMemRegs`**: the `rvIsa` step
    of an instruction of `rvSel` whose registers are in `rvMemRegs` and whose destination is
    not an array base preserves the register relation on `rvMemRegs`, the memory relation and
    the array base registers. -/
theorem rvSelM_step_alu (P : LprogM) {arrs : List String} {sz : String → Nat}
    {i : LinstrRM} {ri : RInst64} (h : rvSel i = some ri)
    (hsrc : ∀ r ∈ (rinst64DstSrcs ri).2, r ∈ rvMemRegs) (hdst : (rinst64DstSrcs ri).1 ∈ rvMemRegs)
    (hda : (rinst64DstSrcs ri).1 ∉ arrs)
    (s : LstateMF) (b : RMState64) (hrel : RegRel rvMemRegs s b.regs.get)
    (hmem : MemRel arrs sz s b) :
    ∃ s', rvIsa.step P i s = some s'
      ∧ RegRel rvMemRegs s' (runRMBlock64 b [.alu ri]).regs.get
      ∧ MemRel arrs sz s' (runRMBlock64 b [.alu ri])
      ∧ (∀ a ∈ arrs, (runRMBlock64 b [.alu ri]).regs.get a = b.regs.get a)
      ∧ FrameM 1 s s' := by
  have hrun : (runRMBlock64 b [.alu ri]).regs = evalRInst64 b.regs ri := rfl
  have hmrun : (runRMBlock64 b [.alu ri]).mem = b.mem := rfl
  rcases rvSel_inv h with ⟨o, d, a, c, rfl, ho, -, -, -, hri⟩ | ⟨d, a, tag, rfl, -, -, rfl⟩
  · simp only [rvBops, List.mem_cons, List.not_mem_nil, or_false] at ho
    have hd' : d ∈ rvMemRegs := by
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rvRinst, Option.some.injEq] at hri <;>
        subst hri <;> exact hdst
    have hda' : d ∉ arrs := by
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rvRinst, Option.some.injEq] at hri <;>
        subst hri <;> exact hda
    have ha' : a ∈ rvMemRegs ∧ c ∈ rvMemRegs := by
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rvRinst, Option.some.injEq] at hri <;>
        subst hri <;> exact ⟨hsrc a (by simp [rinst64DstSrcs]), hsrc c (by simp [rinst64DstSrcs])⟩
    have hget : ∀ r, (runRMBlock64 b [.alu ri]).regs.get r
        = (b.regs.set d (o.apply (b.regs.get a) (b.regs.get c))).get r := by
      intro r
      rw [hrun]
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rvRinst, Option.some.injEq] at hri <;>
        subst hri <;> rfl
    have hstrip := stripWidthTag_withWidthTag_binOpName' 64 o
    have hok : rvBases.contains (stripWidthTag (withWidthTag 64 (binOpName o))) = true := by
      rw [hstrip]; rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨{ s with prog := { s.prog with
      base := (s.prog.base.setReg d (o.apply (b.regs.get a) (b.regs.get c))).nextPc } },
      ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [rvIsa_step_core P _ _ _ _ s hok]
      exact coreStep_binop P o d a c s _ _ (hrel.getW ha'.1) (hrel.getW ha'.2)
    · refine RegRel_setReg hrel d _ (fun r hr => ?_)
      rw [hget, get_set_rvRegs _ (rvRegs_of_rvMemRegs hd') _ (rvRegs_of_rvMemRegs hr)]
    · intro x hx
      obtain ⟨arr', harr', hat'⟩ := hmem x hx
      have hxd : x ≠ d := fun e => hda' (e ▸ hx)
      refine ⟨arr', by simpa using harr', ?_⟩
      rw [hmrun, hget, RState64.get_set_other _ _ _ _ hxd]; exact hat'
    · intro x hx
      rw [hget, RState64.get_set_other _ _ _ _ (fun (e : x = d) => hda' (e ▸ hx))]
  · simp only [rinst64DstSrcs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hsrc hdst hda
    have hget : ∀ r, (runRMBlock64 b [.alu (.mv d a)]).regs.get r
        = (b.regs.set d (b.regs.get a)).get r := fun r => rfl
    have hok : rvBases.contains (stripWidthTag (withWidthTag 64 "MOV")) = true := by
      rw [show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide +kernel]; decide
    refine ⟨{ s with prog := { s.prog with base := (s.prog.base.setReg d (b.regs.get a)).nextPc } },
      ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [rvIsa_step_core P _ _ _ _ s hok]
      exact coreStep_mov P d a tag s _ (hrel a hsrc)
    · refine RegRel_setReg hrel d _ (fun r hr => ?_)
      rw [hget, get_set_rvRegs _ (rvRegs_of_rvMemRegs hdst) _ (rvRegs_of_rvMemRegs hr)]
    · intro x hx
      obtain ⟨arr', harr', hat'⟩ := hmem x hx
      have hxd : x ≠ d := fun e => hda (e ▸ hx)
      refine ⟨arr', by simpa using harr', ?_⟩
      rw [hmrun, hget, RState64.get_set_other _ _ _ _ hxd]; exact hat'
    · intro x hx
      rw [hget, RState64.get_set_other _ _ _ _ (fun (e : x = d) => hda (e ▸ hx))]

/-- **The one-step simulation of a register-immediate instruction**: the `rvIsa` step of
    `d := a ⊙ k` and the machine step of `ADDI d, a, imm`, where `x ⊙ k = x + imm`, preserve
    the register relation on `rvMemRegs`, the memory relation and the array base registers. -/
theorem rvSelM_step_addi (P : LprogM) {arrs : List String} {sz : String → Nat}
    (bop : JasminBinOp) (hsar : binOpName bop ≠ "SAR")
    (hok : rvBases.contains (stripWidthTag (withWidthTag 64 (binOpName bop))) = true)
    (d a : String) (k : Nat) (imm : Int)
    (hv : ∀ x : BitVec 64, bop.apply x (BitVec.ofNat 64 k) = x + BitVec.ofInt 64 imm)
    (hd : d ∈ rvMemRegs) (ha : a ∈ rvMemRegs) (hda : d ∉ arrs)
    (s : LstateMF) (b : RMState64) (hrel : RegRel rvMemRegs s b.regs.get)
    (hmem : MemRel arrs sz s b) :
    ∃ s', rvIsa.step P (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k],
          .reg none) s = some s'
      ∧ RegRel rvMemRegs s' (runRMBlock64 b [.addi d a imm]).regs.get
      ∧ MemRel arrs sz s' (runRMBlock64 b [.addi d a imm])
      ∧ (∀ x ∈ arrs, (runRMBlock64 b [.addi d a imm]).regs.get x = b.regs.get x)
      ∧ FrameM 1 s s' := by
  have hget : ∀ r, (runRMBlock64 b [.addi d a imm]).regs.get r
      = (b.regs.set d (bop.apply (b.regs.get a) (BitVec.ofNat 64 k))).get r := by
    intro r; rw [hv]; rfl
  refine ⟨{ s with prog := { s.prog with
      base := (s.prog.base.setReg d (bop.apply (b.regs.get a) (BitVec.ofNat 64 k))).nextPc } },
    ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [rvIsa_step_core P _ _ _ _ s hok]
    exact coreStep_binopImm P bop d a k s _ hsar (hrel.getW ha)
  · refine RegRel_setReg hrel d _ (fun r hr => ?_)
    rw [hget, get_set_rvRegs _ (rvRegs_of_rvMemRegs hd) _ (rvRegs_of_rvMemRegs hr)]
  · intro x hx
    obtain ⟨arr', harr', hat'⟩ := hmem x hx
    have hxd : x ≠ d := fun e => hda (e ▸ hx)
    refine ⟨arr', by simpa using harr', ?_⟩
    rw [hget, RState64.get_set_other _ _ _ _ hxd]; exact hat'
  · intro x hx
    rw [hget, RState64.get_set_other _ _ _ _ (fun (e : x = d) => hda (e ▸ hx))]

/-- **The one-step simulation of the memory selection**: from related states with the array
    layout `ArrsSep` and the index bound of the instruction, the `rvIsa` step of a selected
    instruction succeeds, and the result is related to the machine run of the selected
    instructions on `rvMemRegs` and the arrays, the array base registers are unchanged, and the
    frame of one step holds. -/
theorem rvSelM_step (P : LprogM) {arrs : List String} {sz : String → Nat} {i : LinstrRM}
    {rs : List RMInst64} (h : rvSelM arrs sz i = some rs) (s : LstateMF) (b : RMState64)
    (hrel : RegRel rvMemRegs s b.regs.get) (hmem : MemRel arrs sz s b)
    (hsep : ArrsSep arrs sz b.regs.get) (hb : IdxBound sz i b.regs.get) :
    ∃ s', rvIsa.step P i s = some s'
      ∧ RegRel rvMemRegs s' (runRMBlock64 b rs).regs.get
      ∧ MemRel arrs sz s' (runRMBlock64 b rs)
      ∧ (∀ a ∈ arrs, (runRMBlock64 b rs).regs.get a = b.regs.get a)
      ∧ FrameM 1 s s' := by
  rcases rvSelM_inv h with
    ⟨d, base, idx, sc, rfl, hd, hi, hbs, ha, hda, rfl⟩ |
    ⟨base, idx, v, sc, rfl, hv, hi, hbs, ha, rfl⟩ |
    ⟨d, a, k, rfl, hd, ha, hda, -, -, rfl⟩ |
    ⟨d, a, k, rfl, hd, ha, hda, -, -, rfl⟩ |
    ⟨ri, hri, hsrc, hdst, hda, rfl⟩
  · exact rvSelM_step_load P d base idx sc hd hi hbs ha hda s b hrel hmem hsep
      (hb.1 d base idx (by simp [loadStruct?]))
  · exact rvSelM_step_store P base idx v sc hv hi hbs ha s b hrel hmem hsep
      (hb.2 base base idx v (by simp [storeStruct?]))
  · rw [show "ADD:64" = withWidthTag 64 (binOpName .add) by decide +kernel]
    exact rvSelM_step_addi P .add (by decide +kernel) (by decide +kernel) d a k k
      (fun x => by simp [JasminBinOp.apply]) hd ha hda s b hrel hmem
  · rw [show "SUB:64" = withWidthTag 64 (binOpName .sub) by decide +kernel]
    exact rvSelM_step_addi P .sub (by decide +kernel) (by decide +kernel) d a k (-(k : Int))
      (fun x => by
        simp only [JasminBinOp.apply]
        rw [BitVec.sub_eq_add_neg, BitVec.ofInt_neg, BitVec.ofInt_natCast])
      hd ha hda s b hrel hmem
  · exact rvSelM_step_alu P hri hsrc hdst hda s b hrel hmem

/-- The array layout depends only on the array base registers. -/
theorem ArrsSep_congr {arrs : List String} {sz : String → Nat} {g g' : String → BitVec 64}
    (h : ArrsSep arrs sz g) (hg : ∀ a ∈ arrs, g' a = g a) : ArrsSep arrs sz g' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun a ha a' ha' hne j k => ?_⟩
  rw [hg a ha, hg a' ha']
  exact h3 a ha a' ha' hne j k

/-- **The index bounds of a block**: the index bound of each instruction at the machine state
    reached by the selected instructions before it. -/
def MemBounds (arrs : List String) (sz : String → Nat) : List LinstrRM → RMState64 → Prop
  | [], _ => True
  | i :: is, b => IdxBound sz i b.regs.get ∧
      ∀ rs, rvSelM arrs sz i = some rs → MemBounds arrs sz is (runRMBlock64 b rs)

/-! ### The byte round trip of the memory fragment -/

/-- Decode a byte stream of 4-byte RV64 words with `riscvDecodeM64`; `none` on a word
    outside the decoder or a trailing partial word. -/
def decodeRMBlock64 : List (BitVec 8) → Option (List RMInst64)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (riscvDecodeM64 (leWord32 b0 b1 b2 b3)).bind
        (fun i => (decodeRMBlock64 rest).map (fun is => i :: is))
  | _ => none

/-- The little-endian bytes of a word followed by a stream decode as the word followed by the
    stream. -/
theorem decodeRMBlock64_wordLE (w : BitVec 32) (rest : List (BitVec 8)) :
    decodeRMBlock64 (wordLE w ++ rest) =
      (riscvDecodeM64 w).bind (fun i => (decodeRMBlock64 rest).map (fun is => i :: is)) := by
  have hw : leWord32 (BitVec.ofNat 8 (w.toNat &&& 0xff)) (BitVec.ofNat 8 ((w.toNat >>> 8) &&& 0xff))
      (BitVec.ofNat 8 ((w.toNat >>> 16) &&& 0xff)) (BitVec.ofNat 8 ((w.toNat >>> 24) &&& 0xff))
      = w := by
    apply BitVec.eq_of_toNat_eq
    have hlt := w.isLt
    simp only [leWord32, show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  simp only [wordLE, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeRMBlock64, hw]

/-- An instruction whose bytes are the bytes of its encoder word, which `riscvDecodeM64`
    decodes back to it. -/
def RMRoundTrip (x : RMInst64) : Prop :=
  encodeRMInst64 x = wordLE (encodeMWord64 x).get! ∧
    riscvDecodeM64 (encodeMWord64 x).get! = some x

/-- **The block round trip of the memory fragment**: a block of instructions that each round
    trip decodes from its bytes. -/
theorem decodeRMBlock64_encode :
    ∀ xs : List RMInst64, (∀ x ∈ xs, RMRoundTrip x) →
      decodeRMBlock64 (encodeRMBlock64 xs) = some xs
  | [], _ => rfl
  | x :: xs, h => by
      obtain ⟨he, hd⟩ := h x (by simp)
      simp only [encodeRMBlock64, List.flatMap_cons]
      rw [he, decodeRMBlock64_wordLE, hd]
      simp only [Option.bind_some]
      have ih := decodeRMBlock64_encode xs (fun y hy => h y (by simp [hy]))
      simp only [encodeRMBlock64] at ih
      rw [ih]
      rfl

theorem emittedRegs_of_rvMemRegs {r : String} (h : r ∈ rvMemRegs) : r ∈ emittedRegs :=
  emittedRegs_of_rvRegs (rvRegs_of_rvMemRegs h)

/-- The address computation round trips. -/
theorem rvIdxAddr_roundTrip {base idx : String} (hb : base ∈ rvMemRegs)
    (hi : idx ∈ rvMemRegs) : ∀ x ∈ rvIdxAddr base idx, RMRoundTrip x := by
  have h5 : "t5" ∈ emittedRegs := by decide
  have eb := emittedRegs_of_rvMemRegs hb
  have ei := emittedRegs_of_rvMemRegs hi
  intro x hx
  simp only [rvIdxAddr, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · refine ⟨rfl, roundtrip_RMInst64 _ ?_ trivial ?_⟩
    · intro r hr
      simp only [rminst64Regs, rinst64DstSrcs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> assumption
    · intro j hj
      cases hj
      refine ⟨fun _ _ h => ?_, fun _ _ _ h => ?_⟩
      · cases h
      · rcases h with h | h <;> cases h
        decide
  · refine ⟨rfl, roundtrip_RMInst64 _ ?_ trivial ?_⟩
    · intro r hr
      simp only [rminst64Regs, rinst64DstSrcs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> assumption
    · intro j hj
      cases hj
      refine ⟨fun _ _ h => ?_, fun _ _ _ h => ?_⟩
      · cases h
      · rcases h with h | h <;> cases h

/-- **The byte round trip of a selected instruction**: each instruction of the selection of
    an `Lprog` instruction round trips. -/
theorem rvSelM_roundTrip {arrs : List String} {sz : String → Nat} {i : LinstrRM}
    {rs : List RMInst64} (h : rvSelM arrs sz i = some rs) : ∀ x ∈ rs, RMRoundTrip x := by
  have h5 : "t5" ∈ emittedRegs := by decide
  rcases rvSelM_inv h with
    ⟨d, base, idx, sc, rfl, hd, hi, hbs, ha, hda, rfl⟩ |
    ⟨base, idx, v, sc, rfl, hv, hi, hbs, ha, rfl⟩ |
    ⟨d, a, k, rfl, hd, ha, hda, h0, hk, rfl⟩ |
    ⟨d, a, k, rfl, hd, ha, hda, h0, hk, rfl⟩ |
    ⟨ri, hri, hsrc, hdst, hda, rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact rvIdxAddr_roundTrip hbs hi x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      refine ⟨rfl, roundtrip_RMInst64 _ ?_ ⟨by decide, by decide⟩ (fun j hj => by cases hj)⟩
      intro r hr
      simp only [rminst64Regs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact emittedRegs_of_rvMemRegs hd
      · exact h5
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact rvIdxAddr_roundTrip hbs hi x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      refine ⟨rfl, roundtrip_RMInst64 _ ?_ ⟨by decide, by decide⟩ (fun j hj => by cases hj)⟩
      intro r hr
      simp only [rminst64Regs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact emittedRegs_of_rvMemRegs hv
      · exact h5
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    refine ⟨rfl, roundtrip_RMInst64 _ ?_ ⟨by omega, by omega, by omega⟩ (fun j hj => by cases hj)⟩
    intro r hr
    simp only [rminst64Regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact emittedRegs_of_rvMemRegs hd
    · exact emittedRegs_of_rvMemRegs ha
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    refine ⟨rfl, roundtrip_RMInst64 _ ?_ ⟨by omega, by omega, by omega⟩ (fun j hj => by cases hj)⟩
    intro r hr
    simp only [rminst64Regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact emittedRegs_of_rvMemRegs hd
    · exact emittedRegs_of_rvMemRegs ha
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact ⟨rvSel_encode hri, riscvDecodeM64_of_decode64 (rvSel_decode hri)⟩

/-! ### The branch -/

/-- **The branch condition is the `BNE` test against `zero`**: for a related register `r`,
    the `rvIsa` condition `rvCond s (.reg r)` holds exactly when `BNE r, zero, off` is taken,
    and the program counter after `BNE` is the branch target when the condition holds and the
    next instruction otherwise. -/
theorem rvCond_bne {regs : List String} {s : LstateMF} {b : RMState64}
    (hrel : RegRel regs s b.regs.get) {r : String} (hr : r ∈ regs) (off : Int) :
    rvCond s (.reg r) = decide (b.regs.get r ≠ b.regs.get "zero")
      ∧ (evalRMInst64 b (.bne r "zero" off)).pc
          = if rvCond s (.reg r) then b.pc + BitVec.ofInt 64 off else b.pc + 4 := by
  have hc : rvCond s (.reg r) = decide (b.regs.get r ≠ b.regs.get "zero") := by
    simp only [rvCond, condNZ, evalOperandN, hrel.getW hr]
    simp
  refine ⟨hc, ?_⟩
  rw [hc]
  simp only [evalRMInst64]
  split <;> simp_all

/-- Each instruction of the selection of a block round trips. -/
theorem rvSelM_roundTrip_block {arrs : List String} {sz : String → Nat} :
    ∀ (is : List LinstrRM) (rss : List (List RMInst64)), is.mapM (rvSelM arrs sz) = some rss →
      ∀ x ∈ rss.flatten, RMRoundTrip x
  | [], rss, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | i :: is, rss, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨rs, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rss', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      intro x hx
      rw [List.flatten_cons] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact rvSelM_roundTrip hi x hx
      · exact rvSelM_roundTrip_block is rss' hs x hx

/-- **The Asm lemma of the RV64 memory fragment.** For a block `is` that the memory selection
    maps to the instruction lists `rss`: the bytes of the concatenation decode to it, and from
    an `LstateMF` related to a machine state `b` on `rvMemRegs` and on the arrays `arrs`, with
    the array layout `ArrsSep` and the index bounds `MemBounds` of the block, the `rvIsa` run of
    `is` succeeds and ends related to the machine run of the concatenation, on the registers
    and on the arrays, with the frame of the block. -/
theorem rv_asm_mem (P : LprogM) (arrs : List String) (sz : String → Nat) :
    ∀ (is : List LinstrRM) (rss : List (List RMInst64)), is.mapM (rvSelM arrs sz) = some rss →
      ∀ (s : LstateMF) (b : RMState64), RegRel rvMemRegs s b.regs.get → MemRel arrs sz s b →
        ArrsSep arrs sz b.regs.get → MemBounds arrs sz is b →
        decodeRMBlock64 (encodeRMBlock64 rss.flatten) = some rss.flatten ∧
        ∃ s', rvIsa.runL P is s = some s'
          ∧ RegRel rvMemRegs s' (runRMBlock64 b rss.flatten).regs.get
          ∧ MemRel arrs sz s' (runRMBlock64 b rss.flatten)
          ∧ FrameM is.length s s'
  | [], rss, h, s, b, hrel, hmem, _, _ => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, s, rfl, hrel, hmem, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | i :: is, rss, h, s, b, hrel, hmem, hsep, hbd => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨rs, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rss', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      obtain ⟨hb1, hbr⟩ := hbd
      obtain ⟨s1, hs1, hrel1, hmem1, hbase1, f1⟩ := rvSelM_step P hi s b hrel hmem hsep hb1
      obtain ⟨hdec, s2, hs2, hrel2, hmem2, f2⟩ :=
        rv_asm_mem P arrs sz is rss' hs s1 (runRMBlock64 b rs) hrel1 hmem1
          (ArrsSep_congr hsep hbase1) (hbr rs hi)
      refine ⟨?_, s2, ?_, ?_, ?_, ?_⟩
      · refine decodeRMBlock64_encode _ (fun x hx => ?_)
        rw [List.flatten_cons] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact rvSelM_roundTrip hi x hx
        · exact rvSelM_roundTrip_block is rss' hs x hx
      · simp only [Isa.runL, hs1, Option.bind_some, hs2]
      · rw [List.flatten_cons, runRMBlock64_append]; exact hrel2
      · rw [List.flatten_cons, runRMBlock64_append]; exact hmem2
      · obtain ⟨a1, b1, d1, e1, g1, k1⟩ := f1
        obtain ⟨a2, b2, d2, e2, g2, k2⟩ := f2
        refine ⟨a2.trans a1, b2.trans b1, d2.trans d1, e2.trans e1, g2.trans g1, ?_⟩
        rw [k2, k1, List.length_cons]; omega

/-! ### The `mpn_and_n` loop body at RV64 -/

/-- The `mpn_and_n` limb body at RV64 registers, over arrays of `n` limbs: the inputs at `a0`,
    `a1`, the output at `a3`, the index `a4` and the count `a2`. The two loads, the
    conjunction and the store of the canonical chain (`JasminLsemExportPhysAnd.andChainRM`, whose
    shift by `0` is the identity and is dropped), the index step and the count step. The
    back edge is `Lcond (.reg "a2")`, whose condition `rvCond_bne` relates to `BNE a2, zero`. -/
def rvAndBody (n : Nat) : List LinstrRM :=
  [ (.Lopn [.reg "t0"] "LOADIDX" [.arrIdx "a1" "a4" 8], .load 64 n)
  , (.Lopn [.reg "t1"] "LOADIDX" [.arrIdx "a0" "a4" 8], .load 64 n)
  , (.Lopn [.reg "t2"] "AND:64" [.reg "t0", .reg "t1"], .reg none)
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "a4" 8, .reg "t2"], .store 64 n)
  , (.Lopn [.reg "a4"] "ADD:64" [.reg "a4", .imm 1], .reg none)
  , (.Lopn [.reg "a2"] "SUB:64" [.reg "a2", .imm 1], .reg none) ]

/-- The arrays of the `mpn_and_n` body. -/
def rvAndArrs : List String := ["a0", "a1", "a3"]

/-- The RV64 instructions of the `mpn_and_n` body. -/
def rvAndCode : List (List RMInst64) :=
  [ rvIdxAddr "a1" "a4" ++ [.ld "t0" "t5" 0]
  , rvIdxAddr "a0" "a4" ++ [.ld "t1" "t5" 0]
  , [.alu (.and "t2" "t0" "t1")]
  , rvIdxAddr "a3" "a4" ++ [.sd "t2" "t5" 0]
  , [.addi "a4" "a4" 1]
  , [.addi "a2" "a2" (-1)] ]

/-- The memory selection maps the `mpn_and_n` body to `rvAndCode`. -/
theorem rvAndBody_sel (n : Nat) :
    (rvAndBody n).mapM (rvSelM rvAndArrs (fun _ => n)) = some rvAndCode := by
  simp [rvAndBody, rvSelM, rvSel, bopOf?, rvBops, rvRinst, rvMemRegs, rvAndArrs, rvRegs,
    rinst64DstSrcs, rvAndCode, withWidthTag, binOpName]

/-- The index bounds of the `mpn_and_n` body hold when the index `a4` is below `n`. -/
theorem rvAndBody_bounds (n : Nat) (b : RMState64) (h : (b.regs.get "a4").toNat < n) :
    MemBounds rvAndArrs (fun _ => n) (rvAndBody n) b := by
  simp [MemBounds, IdxBound, rvAndBody, loadStruct?, storeStruct?, rvSelM, rvSel, bopOf?,
    rvBops, rvRinst, rvMemRegs, rvAndArrs, rvRegs, rinst64DstSrcs, withWidthTag, binOpName,
    rvIdxAddr, runRMBlock64, evalRMInst64, evalRInst64, RState64.set] at h ⊢
  refine ⟨h, ?_⟩
  rintro _ _ _ _ rfl rfl rfl rfl
  simpa using h

/-- **The `mpn_and_n` body at RV64 bytes.** The bytes of `rvAndCode` decode to it, and from an
    `LstateMF` related to a machine state on `rvMemRegs` and on the arrays `a0`, `a1`, `a3` of
    `n` limbs, laid out separately, with the index `a4` below `n`, the `rvIsa` run of the body
    succeeds and ends related to the machine run of `rvAndCode`. -/
theorem rv_and_body (P : LprogM) (n : Nat) (s : LstateMF) (b : RMState64)
    (hrel : RegRel rvMemRegs s b.regs.get) (hmem : MemRel rvAndArrs (fun _ => n) s b)
    (hsep : ArrsSep rvAndArrs (fun _ => n) b.regs.get) (hidx : (b.regs.get "a4").toNat < n) :
    decodeRMBlock64 (encodeRMBlock64 rvAndCode.flatten) = some rvAndCode.flatten ∧
    ∃ s', rvIsa.runL P (rvAndBody n) s = some s'
      ∧ RegRel rvMemRegs s' (runRMBlock64 b rvAndCode.flatten).regs.get
      ∧ MemRel rvAndArrs (fun _ => n) s' (runRMBlock64 b rvAndCode.flatten)
      ∧ FrameM 6 s s' :=
  rv_asm_mem P rvAndArrs (fun _ => n) (rvAndBody n) rvAndCode (rvAndBody_sel n) s b hrel hmem
    hsep (rvAndBody_bounds n b hidx)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
