/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaSubset
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
public import CatCrypt.Crypto.SecureCompilation.CT.RiscvTiming

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

## Main results

* `rvIsa`: the RV64 instruction set.
* `rvLeaksOperands`, `rvIsa_leaksOperands_bases`: the leakage regime of Zkt and its
  operand-leaking bases, the loads and stores.
* `rvIsa_refuse_x86`: the x86-only mnemonics have no step.
* `rvSel`, `rvSel_decode`, `rvSel_step`: the selection, its byte round trip and its one-step
  simulation.
* `decodeRBlock64`, `rv_asm`: the block decoder and the Asm lemma of the register fragment.
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

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
