/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean

/-!
# The owned x86 instruction model against Sail-x86 and the Intel SDM, over all inputs

`SailX86Lean` transcribes the pure bodies of the Sail-x86 instruction specs
(`sailAdd`, `sailSub`, `sailAdc`, `sailSbb`, `sailAnd`, `sailOr`, `sailXor`,
`sailMulx`, `sailAdcxAdox`) and compares `evalInstr` with them on concrete
inputs, and for `MULX`/`ADCX`/`ADOX` on all operand values at fixed register
names and a fixed starting state. This module states the comparison for every
starting state `s : JState 64`, every destination and source register name, and
every operand value and incoming flag, for the instructions of the s2n-bignum
P-384 Montgomery multiplication block
(`Ascent/Demos/S2nMontmulP384.lean` in the dev tree).

Each result has two parts: the value part (the destination word and the flags
the instruction writes, as functions of the operand values and incoming flags)
and the frame part (every other register, the memory and, where the instruction
writes only some flags, the other flags, are unchanged).

Three kinds of comparison are used, and the theorem names say which:

* `*_eq_sail` is an equality with a transcribed Sail-exported body, from
  `SailX86Lean` or from this module. Covered: `ADD`, `SUB`, `ADC`, `SBB`, `AND`,
  `OR`, `XOR` (the data word and the five flags `CF`, `OF`, `SF`, `ZF`, `PF`),
  `XOR r, r`, `MULX` with a register or memory second source (both words),
  `ADCX` (word and `CF`), `ADOX` (word and `OF`), `SHL` at masked counts
  `1 … 63` (word and five flags, against `sal_shl_spec_64`), `CMOVNE`, `CMOVE`
  and `CMOVB` with a register source (the 64-bit register-to-register data path
  of `x86_cmovcc` with the condition of `jcc_cmovcc_setcc_spec`), and `MOV`
  with a register or immediate source (the 64-bit data paths of
  `x86_mov_op_en_rm`/`x86_mov_op_en_mr`, `x86_mov_op_en_oi` and
  `x86_mov_op_en_mi`).
* `*_refines_sail` is a refinement: the data words are equal, and every flag
  the model defines equals the Sail flag. `shl_refines_sail` covers all counts;
  at masked count `0` Sail keeps the incoming flags and the model marks all five
  undefined (`shl_count_zero`).
* `*_eq_sdm` is an equality with a definition in this module transcribed from
  the Intel 64 and IA-32 Architectures Software Developer's Manual (SDM),
  Volume 2: `MOV` (`sdmMov`), `CMOVNE` (`sdmCmovne`, any operand) and `SHL` by
  an immediate count at masked counts `1 … 63` (`sdmShl`).

The Sail transcriptions of this module are taken from the Lean package that
`sail --lean` (Sail 0.20.1) generates from the `sail-x86-from-acl2` model
(commit `0c6c023`, sources `model/shifts_spec.sail`, `model/conditional.sail`,
`model/move.sail`); the generated files cited below (`Out/ShiftsSpec.lean`,
`Out/Conditional.lean`, `Out/Move.lean`, `Out/RotateAndShift.lean`,
`Out/RegisterReadersAndWriters.lean`, `Out/DecodingAndSpecUtils.lean`,
`Out/Prelude.lean`, `Out/Sail/Sail.lean`) belong to that external package, which
is not vendored in this repository. In the generated runtime,
`Sail.BitVec.truncate x n` is `x.truncate n` and `Sail.BitVec.zeroExtend x n` is
`x.zeroExtend n`, both `BitVec.setWidth n x`; `bits_of_int x n` is
`get_slice_int n x 0`, which is `BitVec.extractLsb' 0 n (BitVec.ofInt (n + 1) x)`;
`BitVec.toNatInt x` is `Int.ofNat x.toNat`; `eq_bits_nat x y` is
`BitVec.toNatInt x == y`; `bool_to_bits` maps `true`/`false` to `1#1`/`0#1`.
A one-bit flag is carried here as a `Bool`, `1#1` read as `true`, except in
`sailJccCond`, which keeps the `BitVec 1` flag inputs of the generated code.

Memory loads and stores (`loadMem`, `storeMem`) are not covered here: their
reference semantics depends on the byte-level memory model, which is outside
this module. `mulxMem` is covered with its second source taken as the model's
`JState.load` word.

## Main results

* `add_eq_sail`, `sub_eq_sail`, `adc_eq_sail`, `sbb_eq_sail`, `and_eq_sail`,
  `or_eq_sail`, `xor_eq_sail`: word and five flags equal the Sail body, for any
  operand (`JOperand`); `*_reg_eq_sail` and `*_imm_eq_sail` are the register and
  immediate forms.
* `aluOp_frame`: the seven two-address ALU instructions leave every other
  register and the memory unchanged.
* `xor_self_eq_sail`, `xor_self_eq_zero`: `XOR r, r` writes `0` with
  `CF = OF = SF = 0`, `ZF = PF = 1`.
* `mulx_eq_sail_general`, `mulxMem_eq_sail_general`, `adcx_eq_sail_general`,
  `adox_eq_sail_general`: the ADX/BMI2 instructions over any state and any
  (distinct, for `MULX`) register names.
* `shl_eq_sail`, `shl_imm_eq_sail`: `SHL` at masked counts `1 … 63` equals
  `sailShl64`; `shl_refines_sail`: `SHL` at every count refines `sailShl64`;
  `shl_count_zero`: both sides at masked count `0`.
* `sailJccCond_ne`, `sailJccCond_e`, `sailJccCond_b`: the condition of
  `jcc_cmovcc_setcc_spec` for opcodes `0x45`, `0x44`, `0x42` reads `ZF = 0`,
  `ZF = 1`, `CF = 1`.
* `cmovne_eq_sail`, `cmove_eq_sail`, `cmovb_eq_sail`: the register forms of the
  three `CMOVcc` instructions equal `sailCmovcc64` under that condition.
* `mov_reg_eq_sail`, `mov_imm_eq_sail_oi`, `mov_imm_eq_sail_mi`: `MOV` equals
  the Sail MOV data paths.
* `mov_eq_sdm`, `cmovne_eq_sdm`, `cmovne_zf_clear_eq_sdm`,
  `cmovne_zf_set_eq_sdm`, `shl_imm_eq_sdm`: the SDM-transcribed instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

namespace SailX86LeanUniversal

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean

/-! ## Projections of the model to the `SailOut` shape -/

/-- The data word and the five flags of a `B5W` result, in the `SailOut` shape. -/
def b5wOut (t : B5W 64) : SailOut :=
  { word := t.word, cf := t.cf, of := t.of, sf := t.sf, zf := t.zf, pf := t.pf }

/-- The word in register `dst` and the five flags of a state, in the `SailOut`
    shape. -/
def regOut (s : JState 64) (dst : String) : SailOut :=
  { word := s.get dst, cf := s.flags.cf, of := s.flags.of, sf := s.flags.sf
    zf := s.flags.zf, pf := s.flags.pf }

theorem regOut_writeB5W (s : JState 64) (dst : String) (t : B5W 64) :
    regOut (s.writeB5W dst t) dst = b5wOut t := by
  simp [regOut, b5wOut, JState.writeB5W, JState.get]

/-- `writeB5W` changes no register other than `dst`, and not the memory. -/
theorem writeB5W_frame (s : JState 64) (dst : String) (t : B5W 64) :
    (∀ r, r ≠ dst → (s.writeB5W dst t).get r = s.get r) ∧ (s.writeB5W dst t).mem = s.mem := by
  refine ⟨fun r hr => ?_, rfl⟩
  simp [JState.writeB5W, JState.get, hr]

/-! ## Flag lemmas -/

/-- The model's sign flag is Sail's `sf_spec64`. -/
theorem SF_of_word_eq_sailSF (r : BitVec 64) : SF_of_word r = sailSF r := by
  simp [SF_of_word, msb, sailSF, BitVec.msb_eq_getLsbD_last]

/-- Signed overflow of a 64-bit addition: the wrapped signed sum differs from the
    integer sum exactly when the integer sum is outside `[-2^63, 2^63)`. -/
theorem toInt_add_ne_iff (a b : BitVec 64) :
    (a + b).toInt ≠ a.toInt + b.toInt ↔
      (a.toInt + b.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ a.toInt + b.toInt) := by
  have h1 := a.toInt_lt; have h2 := a.le_toInt; have h3 := b.toInt_lt; have h4 := b.le_toInt
  rw [BitVec.toInt_add, Int.bmod_def]
  simp only [Nat.reducePow, Nat.cast_ofNat] at *
  split_ifs <;> omega

/-- Signed overflow of a 64-bit subtraction, as `toInt_add_ne_iff`. -/
theorem toInt_sub_ne_iff (a b : BitVec 64) :
    (a - b).toInt ≠ a.toInt - b.toInt ↔
      (a.toInt - b.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ a.toInt - b.toInt) := by
  have h1 := a.toInt_lt; have h2 := a.le_toInt; have h3 := b.toInt_lt; have h4 := b.le_toInt
  rw [BitVec.toInt_sub, Int.bmod_def]
  simp only [Nat.reducePow, Nat.cast_ofNat] at *
  split_ifs <;> omega

/-- The model's `add_carry` word is the 64-bit sum with the carry word. -/
theorem add_carry_eq_add (a b : BitVec 64) (c : Bool) :
    add_carry a b (if c then 1 else 0) = a + b + BitVec.ofNat 64 (if c then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add_carry, BitVec.toNat_ofNat, BitVec.toNat_add]
  cases c <;> simp

/-- The model's `sub_borrow` word is the 64-bit difference with the borrow word. -/
theorem sub_borrow_eq_sub (a b : BitVec 64) (c : Bool) :
    sub_borrow a b (if c then 1 else 0) = a - (b + BitVec.ofNat 64 (if c then 1 else 0)) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [sub_borrow, BitVec.toNat_ofInt, BitVec.toNat_sub, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  cases c <;> simp <;> omega

/-! ## The ALU semantic functions equal the Sail bodies -/

theorem x86_ADD_eq_sail (a b : BitVec 64) : b5wOut (x86_ADD a b) = sailAdd a b := by
  simp only [b5wOut, x86_ADD, rflags_of_aluop, sailAdd, SailOut.mk.injEq]
  refine ⟨trivial, congrArg some ?_, congrArg some ?_, congrArg some (SF_of_word_eq_sailSF _),
    rfl, rfl⟩
  · rw [sailCF, decide_eq_decide, wunsigned, BitVec.toNat_add]
    have ha := a.isLt; have hb := b.isLt
    omega
  · rw [sailOF, decide_eq_decide, wsigned, wsigned, wsigned]
    exact toInt_add_ne_iff a b

theorem x86_SUB_eq_sail (a b : BitVec 64) : b5wOut (x86_SUB a b) = sailSub a b := by
  simp only [b5wOut, x86_SUB, sailSub, SailOut.mk.injEq]
  refine ⟨trivial, congrArg some ?_, congrArg some ?_, congrArg some (SF_of_word_eq_sailSF _),
    rfl, rfl⟩
  · rw [decide_eq_decide, wunsigned, BitVec.toNat_sub]
    have ha := a.isLt; have hb := b.isLt
    omega
  · rw [sailOF, decide_eq_decide, wsigned, wsigned, wsigned]
    exact toInt_sub_ne_iff a b

theorem x86_ADC_eq_sail (a b : BitVec 64) (c : Bool) :
    b5wOut (x86_ADC a b c) = sailAdc a b c := by
  have ha := a.isLt; have hb := b.isLt
  have h1 := a.toInt_lt; have h2 := a.le_toInt; have h3 := b.toInt_lt; have h4 := b.le_toInt
  simp only [b5wOut, x86_ADC, rflags_of_aluop, sailAdc, add_carry_eq_add,
    SF_of_word_eq_sailSF, SailOut.mk.injEq, wsigned, wunsigned, sailCF, sailOF,
    Option.some.injEq, decide_eq_decide]
  refine ⟨trivial, ?_, ?_, trivial, rfl, rfl⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; cases c <;> simp
  · simp only [BitVec.toInt_add]; cases c <;> simp [Int.bmod_def] at * <;> omega

theorem x86_SBB_eq_sail (a b : BitVec 64) (c : Bool) :
    b5wOut (x86_SBB a b c) = sailSbb a b c := by
  have ha := a.isLt; have hb := b.isLt
  have h1 := a.toInt_lt; have h2 := a.le_toInt; have h3 := b.toInt_lt; have h4 := b.le_toInt
  simp only [b5wOut, x86_SBB, sailSbb, sub_borrow_eq_sub, SF_of_word_eq_sailSF,
    SailOut.mk.injEq, wsigned, wunsigned, sailOF, Option.some.injEq, decide_eq_decide]
  refine ⟨trivial, ?_, ?_, trivial, rfl, rfl⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    cases c <;> simp <;> omega
  · simp only [BitVec.toInt_add, BitVec.toInt_sub]
    cases c <;> simp [Int.bmod_def] at * <;> omega

theorem rflags_of_bwop_eq (r : BitVec 64) :
    b5wOut (rflags_of_bwop r)
      = { word := r, cf := some false, of := some false, sf := some (sailSF r)
          zf := some (sailZF r), pf := some (sailPF r) } := by
  simp [b5wOut, rflags_of_bwop, SF_of_word_eq_sailSF, sailZF, ZF_of_word, sailPF, PF_of_word]

theorem x86_AND_eq_sail (a b : BitVec 64) : b5wOut (x86_AND a b) = sailAnd a b :=
  rflags_of_bwop_eq _

theorem x86_OR_eq_sail (a b : BitVec 64) : b5wOut (x86_OR a b) = sailOr a b :=
  rflags_of_bwop_eq _

theorem x86_XOR_eq_sail (a b : BitVec 64) : b5wOut (x86_XOR a b) = sailXor a b :=
  rflags_of_bwop_eq _

/-! ## `evalInstr` on the ALU instructions equals the Sail bodies

For every state `s`, destination `dst` and source operand `src` (a register,
which may equal `dst`, or an immediate), the destination word and the five flags
after the instruction are the Sail body applied to `s.get dst`, `src.eval s` and,
for `ADC`/`SBB`, the incoming `CF` (read by `JState.flagB`, undefined as
`false`). -/

theorem add_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.add dst src)) dst = sailAdd (s.get dst) (src.eval s) := by
  simp only [evalInstr, regOut_writeB5W, x86_ADD_eq_sail]

theorem sub_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.sub dst src)) dst = sailSub (s.get dst) (src.eval s) := by
  simp only [evalInstr, regOut_writeB5W, x86_SUB_eq_sail]

theorem adc_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.adc dst src)) dst
      = sailAdc (s.get dst) (src.eval s) (s.flagB (·.cf)) := by
  simp only [evalInstr, regOut_writeB5W, x86_ADC_eq_sail]

theorem sbb_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.sbb dst src)) dst
      = sailSbb (s.get dst) (src.eval s) (s.flagB (·.cf)) := by
  simp only [evalInstr, regOut_writeB5W, x86_SBB_eq_sail]

theorem and_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.and_ dst src)) dst = sailAnd (s.get dst) (src.eval s) := by
  simp only [evalInstr, regOut_writeB5W, x86_AND_eq_sail]

theorem or_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.or_ dst src)) dst = sailOr (s.get dst) (src.eval s) := by
  simp only [evalInstr, regOut_writeB5W, x86_OR_eq_sail]

theorem xor_eq_sail (s : JState 64) (dst : String) (src : JOperand) :
    regOut (evalInstr s (.xor_ dst src)) dst = sailXor (s.get dst) (src.eval s) := by
  simp only [evalInstr, regOut_writeB5W, x86_XOR_eq_sail]

/-- `ADC` with a defined incoming carry `c`. -/
theorem adc_eq_sail_of_cf (s : JState 64) (dst : String) (src : JOperand) (c : Bool)
    (hc : s.flags.cf = some c) :
    regOut (evalInstr s (.adc dst src)) dst = sailAdc (s.get dst) (src.eval s) c := by
  rw [adc_eq_sail]; simp [JState.flagB, hc]

/-- `SBB` with a defined incoming borrow `c`. -/
theorem sbb_eq_sail_of_cf (s : JState 64) (dst : String) (src : JOperand) (c : Bool)
    (hc : s.flags.cf = some c) :
    regOut (evalInstr s (.sbb dst src)) dst = sailSbb (s.get dst) (src.eval s) c := by
  rw [sbb_eq_sail]; simp [JState.flagB, hc]

/-! ### Register-source and immediate-source forms -/

theorem add_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.add dst (.reg src))) dst = sailAdd (s.get dst) (s.get src) :=
  add_eq_sail s dst _

theorem add_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.add dst (.imm k))) dst
      = sailAdd (s.get dst) (BitVec.ofNat 64 k) :=
  add_eq_sail s dst _

theorem sub_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.sub dst (.reg src))) dst = sailSub (s.get dst) (s.get src) :=
  sub_eq_sail s dst _

theorem sub_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.sub dst (.imm k))) dst
      = sailSub (s.get dst) (BitVec.ofNat 64 k) :=
  sub_eq_sail s dst _

theorem adc_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.adc dst (.reg src))) dst
      = sailAdc (s.get dst) (s.get src) (s.flagB (·.cf)) :=
  adc_eq_sail s dst _

theorem adc_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.adc dst (.imm k))) dst
      = sailAdc (s.get dst) (BitVec.ofNat 64 k) (s.flagB (·.cf)) :=
  adc_eq_sail s dst _

theorem sbb_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.sbb dst (.reg src))) dst
      = sailSbb (s.get dst) (s.get src) (s.flagB (·.cf)) :=
  sbb_eq_sail s dst _

theorem sbb_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.sbb dst (.imm k))) dst
      = sailSbb (s.get dst) (BitVec.ofNat 64 k) (s.flagB (·.cf)) :=
  sbb_eq_sail s dst _

theorem and_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.and_ dst (.reg src))) dst = sailAnd (s.get dst) (s.get src) :=
  and_eq_sail s dst _

theorem and_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.and_ dst (.imm k))) dst
      = sailAnd (s.get dst) (BitVec.ofNat 64 k) :=
  and_eq_sail s dst _

theorem or_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.or_ dst (.reg src))) dst = sailOr (s.get dst) (s.get src) :=
  or_eq_sail s dst _

theorem or_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.or_ dst (.imm k))) dst
      = sailOr (s.get dst) (BitVec.ofNat 64 k) :=
  or_eq_sail s dst _

theorem xor_reg_eq_sail (s : JState 64) (dst src : String) :
    regOut (evalInstr s (.xor_ dst (.reg src))) dst = sailXor (s.get dst) (s.get src) :=
  xor_eq_sail s dst _

theorem xor_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) :
    regOut (evalInstr s (.xor_ dst (.imm k))) dst
      = sailXor (s.get dst) (BitVec.ofNat 64 k) :=
  xor_eq_sail s dst _

/-! ### Frame of the ALU instructions -/

/-- The seven two-address ALU instructions change no register other than the
    destination, and not the memory. -/
theorem aluOp_frame (s : JState 64) (dst : String) (src : JOperand)
    (op : String → JOperand → JInstr 64)
    (hop : op = .add ∨ op = .sub ∨ op = .adc ∨ op = .sbb ∨ op = .and_ ∨ op = .or_ ∨
      op = .xor_) :
    (∀ r, r ≠ dst → (evalInstr s (op dst src)).get r = s.get r) ∧
      (evalInstr s (op dst src)).mem = s.mem := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact writeB5W_frame _ _ _

/-! ## `XOR r, r` -/

/-- `XOR r, r` equals Sail's `XOR` on two equal operands. -/
theorem xor_self_eq_sail (s : JState 64) (r : String) :
    regOut (evalInstr s (.xor_ r (.reg r))) r = sailXor (s.get r) (s.get r) :=
  xor_eq_sail s r _

/-- Sail's `XOR` on equal operands: word `0`, `CF = OF = SF = 0`, `ZF = PF = 1`. -/
theorem sailXor_self (v : BitVec 64) :
    sailXor v v = { word := 0, cf := some false, of := some false, sf := some false
                    zf := some true, pf := some true } := by
  simp only [sailXor, BitVec.xor_self]
  rfl

/-- `XOR r, r` writes `0` to `r`, with `CF = OF = SF = 0` and `ZF = PF = 1`. -/
theorem xor_self_eq_zero (s : JState 64) (r : String) :
    regOut (evalInstr s (.xor_ r (.reg r))) r
      = { word := 0, cf := some false, of := some false, sf := some false
          zf := some true, pf := some true } := by
  rw [xor_self_eq_sail, sailXor_self]

/-! ## ADX / BMI2 over any state and register names

These restate `SailX86Lean.mulx_eq_sail`, `adcx_eq_sail` and `adox_eq_sail`
without the fixed register names and starting states. -/

/-- The model's `waddcarry` is Sail's `adcx_adox_spec_64` with the pair swapped. -/
theorem waddcarry_eq_sailAdcxAdox (a b : BitVec 64) (c : Bool) :
    waddcarry a b c = ((sailAdcxAdox a b c).2, (sailAdcxAdox a b c).1) := by
  simp only [waddcarry, sailAdcxAdox, Nat.add_assoc]

/-- `MULX` into distinct registers `dstHi`, `dstLo`: the two words are Sail's
    `mulx_spec_64` of the operand values; flags, memory and all other registers
    are unchanged. -/
theorem mulx_eq_sail_general (s : JState 64) (dstHi dstLo : String) (a b : JOperand)
    (hne : dstLo ≠ dstHi) :
    let s' := evalInstr s (.mulx dstHi dstLo a b)
    (s'.get dstLo, s'.get dstHi) = sailMulx (a.eval s) (b.eval s) ∧
      s'.flags = s.flags ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dstLo → r ≠ dstHi → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp [evalInstr, x86_MULX_lo_hi, wumul, high_bits, JState.setReg, sailMulx, hne]
  · simp [evalInstr, JState.setReg, h1, h2]

/-- `MULX` with its second source read from the model memory at `[base + off]`:
    as `mulx_eq_sail_general`, with `s.load base off` for the second operand. -/
theorem mulxMem_eq_sail_general (s : JState 64) (dstHi dstLo : String) (a : JOperand)
    (base : String) (off : Int) (hne : dstLo ≠ dstHi) :
    let s' := evalInstr s (.mulxMem dstHi dstLo a base off)
    (s'.get dstLo, s'.get dstHi) = sailMulx (a.eval s) (s.load base off) ∧
      s'.flags = s.flags ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dstLo → r ≠ dstHi → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp [evalInstr, x86_MULX_lo_hi, wumul, high_bits, JState.setReg, sailMulx, hne]
  · simp [evalInstr, JState.setReg, h1, h2]

/-- `ADCX`: the destination word and `CF` are Sail's `adcx_adox_spec_64` of the
    operand values and the incoming `CF`; the other four flags, the memory and all
    other registers are unchanged. -/
theorem adcx_eq_sail_general (s : JState 64) (dst : String) (src : JOperand) :
    let s' := evalInstr s (.adcx dst src)
    let o := sailAdcxAdox (s.get dst) (src.eval s) (s.flagB (·.cf))
    s'.get dst = o.1 ∧ s'.flags = { s.flags with cf := some o.2 } ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, ?_, rfl, fun r hr => ?_⟩
  · simp [evalInstr, x86_ADCX, waddcarry_eq_sailAdcxAdox]
  · simp [evalInstr, x86_ADCX, waddcarry_eq_sailAdcxAdox]
  · simp [evalInstr, hr]

/-- `ADOX`: as `adcx_eq_sail_general`, with the carry read from and written to
    `OF`; `CF` and the other flags are unchanged. -/
theorem adox_eq_sail_general (s : JState 64) (dst : String) (src : JOperand) :
    let s' := evalInstr s (.adox dst src)
    let o := sailAdcxAdox (s.get dst) (src.eval s) (s.flagB (·.of))
    s'.get dst = o.1 ∧ s'.flags = { s.flags with of := some o.2 } ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, ?_, rfl, fun r hr => ?_⟩
  · simp [evalInstr, x86_ADCX, waddcarry_eq_sailAdcxAdox]
  · simp [evalInstr, x86_ADCX, waddcarry_eq_sailAdcxAdox]
  · simp [evalInstr, hr]

/-! ## SDM-transcribed instructions

The definitions below follow the Intel SDM, Volume 2 (Instruction Set
Reference), for 64-bit operands (REX.W). They are not Sail exports. -/

/-- SDM Vol. 2B, §4.3 "MOV—Move": `DEST ← SRC`; no flag is affected. -/
def sdmMov (src : BitVec 64) : BitVec 64 := src

/-- SDM Vol. 2A, §3.3 "CMOVcc—Conditional Move", condition `NE`/`NZ`
    (`ZF = 0`): `DEST ← SRC` if `ZF = 0`, otherwise `DEST` keeps its value; no
    flag is affected. -/
def sdmCmovne (zf : Bool) (dst src : BitVec 64) : BitVec 64 :=
  if zf then dst else src

/-- SDM parity flag: set iff the least-significant byte of the result has an
    even number of set bits. -/
def sdmPF (r : BitVec 64) : Bool :=
  decide ((List.range 8).countP (fun i => r.getLsbD i) % 2 = 0)

/-- The data word and the five flags defined by an SDM instruction description,
    `none` where the SDM leaves the flag undefined. -/
structure SdmOut where
  word : BitVec 64
  cf : JFlag
  of : JFlag
  sf : JFlag
  zf : JFlag
  pf : JFlag
deriving DecidableEq, Repr

/-- SDM Vol. 2B, §4.3 "SAL/SAR/SHL/SHR—Shift", `SHL r/m64, imm8`, for a count
    `k`: the count is masked to 6 bits, `n = k mod 64`. For `n ≠ 0`, the result is
    `DEST << n`; `CF` is the last bit shifted out (bit `64 - n` of `DEST`); `OF`
    is defined only for `n = 1`, as the exclusive or of the result's most
    significant bit and `CF`, and undefined otherwise; `SF`, `ZF` and `PF` are set
    from the result. (For `n = 0` the SDM leaves all flags unaffected; this
    definition is used only for `n ≠ 0`.) -/
def sdmShl (v : BitVec 64) (k : Nat) : SdmOut :=
  let n := k % 64
  let r := v <<< n
  let cf := v.getLsbD (64 - n)
  { word := r
    cf := some cf
    of := if n = 1 then some (r.getLsbD 63 != cf) else none
    sf := some (r.getLsbD 63)
    zf := some (decide (r = 0))
    pf := some (sdmPF r) }

/-- The word in `dst` and the five flags of a state, in the `SdmOut` shape. -/
def regSdmOut (s : JState 64) (dst : String) : SdmOut :=
  { word := s.get dst, cf := s.flags.cf, of := s.flags.of, sf := s.flags.sf
    zf := s.flags.zf, pf := s.flags.pf }

/-- `MOV dst, src` (register or immediate source): `dst` holds `sdmMov` of the
    source value; flags, memory and all other registers are unchanged. -/
theorem mov_eq_sdm (s : JState 64) (dst : String) (src : JOperand) :
    let s' := evalInstr s (.mov dst src)
    s'.get dst = sdmMov (src.eval s) ∧ s'.flags = s.flags ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · simp [evalInstr, x86_MOV, sdmMov, JState.setReg]
  · simp [evalInstr, JState.setReg, hr]

/-- `CMOVNE dst, src` with a defined `ZF = z`: `dst` holds `sdmCmovne z` of the
    old destination and the source value; flags, memory and all other registers
    are unchanged. -/
theorem cmovne_eq_sdm (s : JState 64) (dst : String) (src : JOperand) (z : Bool)
    (hz : s.flags.zf = some z) :
    let s' := evalInstr s (.cmovne dst src)
    s'.get dst = sdmCmovne z (s.get dst) (src.eval s) ∧ s'.flags = s.flags ∧
      s'.mem = s.mem ∧ ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · cases z <;> simp [evalInstr, x86_CMOVcc, sdmCmovne, JState.flagB, JState.setReg, hz]
  · simp [evalInstr, JState.setReg, hr]

/-- `CMOVNE` with `ZF = 0` moves the source. -/
theorem cmovne_zf_clear_eq_sdm (s : JState 64) (dst : String) (src : JOperand)
    (hz : s.flags.zf = some false) :
    (evalInstr s (.cmovne dst src)).get dst = src.eval s :=
  (cmovne_eq_sdm s dst src false hz).1

/-- `CMOVNE` with `ZF = 1` keeps the destination. -/
theorem cmovne_zf_set_eq_sdm (s : JState 64) (dst : String) (src : JOperand)
    (hz : s.flags.zf = some true) :
    (evalInstr s (.cmovne dst src)).get dst = s.get dst :=
  (cmovne_eq_sdm s dst src true hz).1

/-- The model's parity fold is the SDM's even-popcount parity. -/
theorem foldl_bne_eq (f : Nat → Bool) (l : List Nat) (acc : Bool) :
    l.foldl (fun acc i => acc != f i) acc = (acc != decide (l.countP f % 2 = 1)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : xs.countP f % 2 = 1 <;> cases acc <;> cases hx : f x <;> simp [h] <;> omega

theorem PF_of_word_eq_sdmPF (r : BitVec 64) : PF_of_word r = sdmPF r := by
  rw [PF_of_word, foldl_bne_eq, sdmPF]
  by_cases h : (List.range 8).countP (fun i => r.getLsbD i) % 2 = 1
  · simp [h]
  · simp [h]; omega

/-- The model's shift count of an immediate `k` is `k mod 64`. -/
theorem shiftCount_ofNat_64 (k : Nat) : shiftCount (BitVec.ofNat 64 k) = k % 64 := by
  simp only [shiftCount, BitVec.toNat_ofNat]; omega

/-- The model's `SHL` carry, the top bit of `v` shifted by `n - 1`, is bit
    `64 - n` of `v`. -/
theorem msb_wshl_pred (v : BitVec 64) (n : Nat) (h1 : 1 ≤ n) (h2 : n < 64) :
    msb (wshl v (n - 1)) = v.getLsbD (64 - n) := by
  simp only [msb, wshl, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have hm : min 64 (n - 1) = n - 1 := by omega
  have hi : 64 - 1 - (n - 1) = 64 - n := by omega
  rw [hm]
  simp [hi]
  omega

/-- `SHL dst, k` for an immediate `k` with `k mod 64 ≠ 0`: the destination word
    and all five flags equal `sdmShl`, with `OF` compared as a defined value at
    masked count `1` and as `none` (undefined) at masked counts `2 … 63`. -/
theorem shl_imm_eq_sdm (s : JState 64) (dst : String) (k : Nat) (hk : k % 64 ≠ 0) :
    regSdmOut (evalInstr s (.shl dst (.imm k))) dst = sdmShl (s.get dst) k := by
  have hlt : k % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hmin : min 64 (k % 64) = k % 64 := by omega
  simp only [regSdmOut, evalInstr, JOperand.eval, JState.writeB5W, x86_SHL,
    shiftCount_ofNat_64, hk, ↓reduceIte, rflags_OF,
    msb_wshl_pred _ _ (Nat.one_le_iff_ne_zero.mpr hk) hlt]
  simp only [wshl, hmin, sdmShl, SF_of_word, ZF_of_word, PF_of_word_eq_sdmPF, msb,
    BitVec.msb_eq_getLsbD_last, JState.get, ↓reduceIte, SdmOut.mk.injEq, true_and,
    and_true]
  simp [BitVec.toNat_eq]

/-- `SHL` changes no register other than the destination, and not the memory. -/
theorem shl_frame (s : JState 64) (dst : String) (src : JOperand) :
    (∀ r, r ≠ dst → (evalInstr s (.shl dst src)).get r = s.get r) ∧
      (evalInstr s (.shl dst src)).mem = s.mem :=
  writeB5W_frame _ _ _

/-! ## `SHL` against Sail's `sal_shl_spec_64`

`Out/RotateAndShift.lean`, `x86_sal_sar_shl_shr_rcl_rcr_rol_ror`, masks the
count and passes its low six bits to the shift spec (`reg = 4` selects
`sal_shl_spec`, which at size `8` is `sal_shl_spec_64`):

```lean
  let countmask : Int :=
    if (((logbitp_bits 3 rex_byte) && (! byte_operand?)) : Bool)
    then 63
    else 31
  let shift_rotate_by : (BitVec 128) := ((bits_of_int countmask 128) &&& shift_rotate_by)
  ...
                      (sal_shl_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
                        (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
```

The count operand is the one-byte immediate for opcode `0xC1` and the low byte
of `CL` for opcode `0xD3`; with `REX.W` its six-bit value is the operand modulo
`64`. -/

/-- The five status flags of Sail's `rflagsbits` input, each bit read as a
    `Bool`. -/
structure SailFlags5 where
  cf : Bool
  of : Bool
  sf : Bool
  zf : Bool
  pf : Bool
deriving DecidableEq, Repr

/-- `sal_shl_spec_64` (`Out/ShiftsSpec.lean`), as the result word and the five
    flags, `none` where the flag is in `undefined_flags` or is not written. The
    generated body is

    ```lean
    def sal_shl_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
      let raw_result : Int := (ash_left_int (BitVec.toNatInt dst) (BitVec.toNatInt src))
      let result : (BitVec 64) := (bits_of_int raw_result 64)
      let (output_rflags, undefined_flags) ← (( do
        let v_85 := src
        if ((eq_bits_nat v_85 0) : Bool)
        then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
        else
          (do
            if ((eq_bits_nat v_85 1) : Bool)
            then
              (do
                let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 63 63)
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 63 result)))
                  ) : SailM Int )
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_sf
                      (_update_rflagsbits_zf
                        (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                    (bits_of_int of 1))
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                if ((64 ≤b (BitVec.toNatInt src)) : Bool)
                then
                  (do
                    let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                    let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                    let sf : (BitVec 1) := (sf_spec64 result)
                    let output_rflags : rflagsbits :=
                      (_update_rflagsbits_sf
                        (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                    let undefined_flags : rflagsbits :=
                      (_update_rflagsbits_of
                        (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                          1#1) 1#1)
                    (pure (output_rflags, undefined_flags)))
                else
                  (do
                    let cf ← (( do (bitslice dst (64 -i (BitVec.toNatInt src)) 1) ) : SailM (BitVec 1)
                      )
                    let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                    let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                    let sf : (BitVec 1) := (sf_spec64 result)
                    let output_rflags : rflagsbits :=
                      (_update_rflagsbits_sf
                        (_update_rflagsbits_zf
                          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                    let undefined_flags : rflagsbits :=
                      (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                        1#1)
                    (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
      (pure (result, output_rflags, undefined_flags))
    ```

    with `ash_left_int x n = x * 2 ^ n` (`Out/Prelude.lean`); `bitslice dst
    (64 - n) 1` is bit `64 - n` of `dst`, `logbit_bits 63 result` is bit `63`
    of `result`, `b_xor` is the exclusive or of two bits, and `pf_spec64`,
    `zf_spec`, `sf_spec64` are `sailPF`, `sailZF`, `sailSF`. The branch
    `64 ≤ src` is unreachable for a six-bit `src`. -/
def sailShl64 (dst : BitVec 64) (src : BitVec 6) (rf : SailFlags5) : SailOut :=
  let result : BitVec 64 :=
    BitVec.extractLsb' 0 64 (BitVec.ofInt 65 ((dst.toNat : Int) * 2 ^ src.toNat))
  if src.toNat = 0 then
    { word := result, cf := some rf.cf, of := some rf.of, sf := some rf.sf
      zf := some rf.zf, pf := some rf.pf }
  else if src.toNat = 1 then
    let cf := dst.getLsbD 63
    { word := result, cf := some cf, of := some (cf != result.getLsbD 63)
      sf := some (sailSF result), zf := some (sailZF result), pf := some (sailPF result) }
  else if 64 ≤ src.toNat then
    { word := result, cf := none, of := none
      sf := some (sailSF result), zf := some (sailZF result), pf := some (sailPF result) }
  else
    { word := result, cf := some (dst.getLsbD (64 - src.toNat)), of := none
      sf := some (sailSF result), zf := some (sailZF result), pf := some (sailPF result) }

/-- Sail's shift result `bits_of_int (dst * 2 ^ n) 64` is `dst <<< n`. -/
theorem sailShl_word (dst : BitVec 64) (n : Nat) :
    BitVec.extractLsb' 0 64 (BitVec.ofInt 65 ((dst.toNat : Int) * 2 ^ n)) = dst <<< n := by
  apply BitVec.eq_of_toNat_eq
  have hc : ((dst.toNat : Int) * 2 ^ n) = ((dst.toNat * 2 ^ n : Nat) : Int) := by push_cast; rfl
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, hc]
  rw [← Int.natCast_emod, Int.toNat_natCast]
  simp only [Nat.shiftRight_zero, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_mod_of_dvd _ (by norm_num)

/-- `SHL dst, src` with masked count `(src.eval s).toNat % 64 ≠ 0`: the
    destination word and the five flags equal `sal_shl_spec_64` on the
    destination value and the six-bit count, for any incoming flags `rf`. -/
theorem shl_eq_sail (s : JState 64) (dst : String) (src : JOperand) (rf : SailFlags5)
    (hk : (src.eval s).toNat % 64 ≠ 0) :
    regOut (evalInstr s (.shl dst src)) dst
      = sailShl64 (s.get dst) ((src.eval s).setWidth 6) rf := by
  have hlt : (src.eval s).toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have h6 : ((src.eval s).setWidth 6).toNat = (src.eval s).toNat % 64 := by
    simp [BitVec.toNat_setWidth]
  have hsc : shiftCount (src.eval s) = (src.eval s).toNat % 64 := rfl
  simp only [regOut, evalInstr, JState.writeB5W, x86_SHL, sailShl64, hsc, h6]
  generalize (src.eval s).toNat % 64 = n at hk hlt ⊢
  have h64 : ¬ 64 ≤ n := by omega
  have hw : wshl (s.regs dst) n = s.regs dst <<< n := by simp [wshl, Nat.min_eq_right hlt.le]
  simp only [hk, h64, ↓reduceIte, rflags_OF,
    msb_wshl_pred _ _ (Nat.one_le_iff_ne_zero.mpr hk) hlt, sailShl_word, hw, JState.get,
    SF_of_word_eq_sailSF]
  by_cases h1 : n = 1
  · subst h1
    simp [msb, BitVec.msb_eq_getLsbD_last, sailZF, ZF_of_word, sailPF, PF_of_word]
    cases (s.regs dst)[62] <;> cases (s.regs dst)[63] <;> rfl
  · simp [h1, sailZF, ZF_of_word, sailPF, PF_of_word]

/-- `SHL dst, k` for an immediate `k` with `k mod 64 ≠ 0` equals
    `sal_shl_spec_64` with the six-bit count `k mod 64`. -/
theorem shl_imm_eq_sail (s : JState 64) (dst : String) (k : Nat) (rf : SailFlags5)
    (hk : k % 64 ≠ 0) :
    regOut (evalInstr s (.shl dst (.imm k))) dst
      = sailShl64 (s.get dst) (BitVec.ofNat 6 k) rf := by
  rw [shl_eq_sail s dst (.imm k) rf (by simpa [Nat.mod_mod_of_dvd] using hk)]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

/-- A model flag refines a reference flag when every value the model defines is
    the reference value. -/
def flagRefines (m t : JFlag) : Prop := ∀ b, m = some b → t = some b

/-- `m` refines `t`: equal data words, and each of the five flags of `m`
    refines the corresponding flag of `t`. -/
def sailOutRefines (m t : SailOut) : Prop :=
  m.word = t.word ∧ flagRefines m.cf t.cf ∧ flagRefines m.of t.of ∧
    flagRefines m.sf t.sf ∧ flagRefines m.zf t.zf ∧ flagRefines m.pf t.pf

theorem sailOutRefines_refl (m : SailOut) : sailOutRefines m m :=
  ⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- `SHL` at masked count `0`: the model keeps the word and marks all five flags
    undefined, and `sal_shl_spec_64` keeps the word and the incoming flags. -/
theorem shl_count_zero (s : JState 64) (dst : String) (src : JOperand) (rf : SailFlags5)
    (hk : (src.eval s).toNat % 64 = 0) :
    regOut (evalInstr s (.shl dst src)) dst
        = { word := s.get dst, cf := none, of := none, sf := none, zf := none, pf := none } ∧
      sailShl64 (s.get dst) ((src.eval s).setWidth 6) rf
        = { word := s.get dst, cf := some rf.cf, of := some rf.of, sf := some rf.sf
            zf := some rf.zf, pf := some rf.pf } := by
  have h6 : ((src.eval s).setWidth 6).toNat = 0 := by
    simp only [BitVec.toNat_setWidth, Nat.reducePow, hk]
  have hsc : shiftCount (src.eval s) = 0 := hk
  refine ⟨?_, ?_⟩
  · simp only [regOut, evalInstr, JState.writeB5W, x86_SHL, hsc, ↓reduceIte, rflags_None,
      JState.get]
  · simp only [sailShl64, h6, ↓reduceIte, sailShl_word, BitVec.shiftLeft_zero]

/-- `SHL dst, src` at every count refines `sal_shl_spec_64`, for any incoming
    flags `rf`. -/
theorem shl_refines_sail (s : JState 64) (dst : String) (src : JOperand) (rf : SailFlags5) :
    sailOutRefines (regOut (evalInstr s (.shl dst src)) dst)
      (sailShl64 (s.get dst) ((src.eval s).setWidth 6) rf) := by
  by_cases hk : (src.eval s).toNat % 64 = 0
  · obtain ⟨h1, h2⟩ := shl_count_zero s dst src rf hk
    rw [h1, h2]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> intro _ h <;> cases h
  · rw [shl_eq_sail s dst src rf hk]
    exact sailOutRefines_refl _

/-! ## `CMOVcc` against Sail's `x86_cmovcc`

`Out/Conditional.lean`, `x86_cmovcc`:

```lean
  let (reg_mem, increment_rip_by, addr) ← (( do
    (x86_operand_from_modr_m_and_sib_bytes proc_mode 0#1 operand_size inst_ac? false seg_reg
      prefixes temp_rip rex_byte r_m mod_var sib 0b000#3) ) : SailM
    ((BitVec 128) × Int × (sbits 64)) )
  ...
  let branch_cond ← (( do (jcc_cmovcc_setcc_spec opcode) ) : SailM Bool )
  if (branch_cond : Bool)
  then
    (write_rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2)
      (Sail.BitVec.truncate reg_mem 64) rex_byte)
  else
    (do
      if (((operand_size == 4) && ((in_64bit_mode proc_mode) || (in_compatibility_mode proc_mode))) : Bool)
      then (wr32 (reg_index reg rex_byte 0b10#2) (← (rr32 (reg_index reg rex_byte 0b10#2))))
      else (pure ()))
  (write_iptr proc_mode temp_rip)
```

For a register source (`mod_var = 0b11`), `x86_operand_from_modr_m_and_sib_bytes`
(`Out/DecodingAndSpecUtils.lean`) returns
`Sail.BitVec.zeroExtend (← (rgfi_size (bits_of_int operand_size 4) (reg_index r_m rex_byte 0b00#2) rex_byte)) 128`,
and at operand size `8` `rgfi_size` is `rr64` and `write_rgfi_size` is `wr64`
(`Out/RegisterReadersAndWriters.lean`). At operand size `8` the `else` branch
writes nothing. -/

/-- Sail's `bool_to_bits` (`Out/Prelude.lean`). -/
def boolBit (b : Bool) : BitVec 1 := if b then 1#1 else 0#1

/-- The arms `0 … 5` of `jcc_cmovcc_setcc_spec` (`Out/Conditional.lean`), with
    the `OF`, `CF`, `ZF` bits of `rflags` as arguments; `none` for the other
    low nibbles, which this definition does not transcribe. The generated arms
    are

    ```lean
    def jcc_cmovcc_setcc_spec (opcode : (BitVec 8)) : SailM Bool := do
      let low_nibble : (BitVec 4) := (Sail.BitVec.truncate (opcode &&& 0x0F#8) 4)
      let v_58 := low_nibble
      if ((eq_bits_nat v_58 0) : Bool)
      then
        (pure (1#1 == (← do
              let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
              (pure (_get_rflagsbits_of rflags_var)))))
      else
        (do
          if ((eq_bits_nat v_58 1) : Bool)
          then
            (pure (0#1 == (← do ... (pure (_get_rflagsbits_of rflags_var)))))
          else
            (do
              if ((eq_bits_nat v_58 2) : Bool)
              then
                (pure (1#1 == (← do ... (pure (_get_rflagsbits_cf rflags_var)))))
              else
                (do
                  if ((eq_bits_nat v_58 3) : Bool)
                  then
                    (pure (0#1 == (← do ... (pure (_get_rflagsbits_cf rflags_var)))))
                  else
                    (do
                      if ((eq_bits_nat v_58 4) : Bool)
                      then
                        (pure (1#1 == (← do ... (pure (_get_rflagsbits_zf rflags_var)))))
                      else
                        (do
                          if ((eq_bits_nat v_58 5) : Bool)
                          then
                            (pure (0#1 == (← do ... (pure (_get_rflagsbits_zf rflags_var)))))
                          else ...
    ```

    where each elided `...` is
    `let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )`. -/
def sailJccCond (opcode : BitVec 8) (of cf zf : BitVec 1) : Option Bool :=
  let low_nibble : BitVec 4 := (opcode &&& 0x0F#8).setWidth 4
  if low_nibble.toNat = 0 then some (1#1 == of)
  else if low_nibble.toNat = 1 then some (0#1 == of)
  else if low_nibble.toNat = 2 then some (1#1 == cf)
  else if low_nibble.toNat = 3 then some (0#1 == cf)
  else if low_nibble.toNat = 4 then some (1#1 == zf)
  else if low_nibble.toNat = 5 then some (0#1 == zf)
  else none

/-- For `CMOVNE` (opcode `0x0F 0x45`) the condition is `ZF = 0`. -/
theorem sailJccCond_ne (of cf zf : BitVec 1) :
    sailJccCond 0x45#8 of cf zf = some (0#1 == zf) := rfl

/-- For `CMOVE` (opcode `0x0F 0x44`) the condition is `ZF = 1`. -/
theorem sailJccCond_e (of cf zf : BitVec 1) :
    sailJccCond 0x44#8 of cf zf = some (1#1 == zf) := rfl

/-- For `CMOVB` (opcode `0x0F 0x42`) the condition is `CF = 1`. -/
theorem sailJccCond_b (of cf zf : BitVec 1) :
    sailJccCond 0x42#8 of cf zf = some (1#1 == cf) := rfl

theorem zero_beq_boolBit (b : Bool) : (0#1 == boolBit b) = !b := by cases b <;> rfl

theorem one_beq_boolBit (b : Bool) : (1#1 == boolBit b) = b := by cases b <;> rfl

/-- The 64-bit register-to-register data path of `x86_cmovcc`: the new value of
    the `reg` register, from `branch_cond`, its old value `reg` and the source
    register value `reg_mem` (`rr64`, zero-extended to 128 bits by
    `x86_operand_from_modr_m_and_sib_bytes` and truncated to 64 bits before
    `wr64`). -/
def sailCmovcc64 (branch_cond : Bool) (reg reg_mem : BitVec 64) : BitVec 64 :=
  if branch_cond then (reg_mem.setWidth 128).setWidth 64 else reg

/-- `CMOVNE dst, src` with a defined `ZF = z`: the condition of
    `jcc_cmovcc_setcc_spec 0x45` is defined, and `sailCmovcc64` under it gives
    the new `dst`; flags, memory and all other registers are unchanged. -/
theorem cmovne_eq_sail (s : JState 64) (dst src : String) (z : Bool)
    (hz : s.flags.zf = some z) (o c : BitVec 1) :
    let s' := evalInstr s (.cmovne dst (.reg src))
    (sailJccCond 0x45#8 o c (boolBit z)).map (sailCmovcc64 · (s.get dst) (s.get src))
        = some (s'.get dst) ∧
      s'.flags = s.flags ∧ s'.mem = s.mem ∧ ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · rw [sailJccCond_ne, zero_beq_boolBit]
    cases z <;> simp [evalInstr, x86_CMOVcc, sailCmovcc64, JState.flagB, JState.setReg, hz]
  · simp [evalInstr, JState.setReg, hr]

/-- `CMOVE dst, src` with a defined `ZF = z`, as `cmovne_eq_sail` for opcode
    `0x44`. -/
theorem cmove_eq_sail (s : JState 64) (dst src : String) (z : Bool)
    (hz : s.flags.zf = some z) (o c : BitVec 1) :
    let s' := evalInstr s (.cmove dst (.reg src))
    (sailJccCond 0x44#8 o c (boolBit z)).map (sailCmovcc64 · (s.get dst) (s.get src))
        = some (s'.get dst) ∧
      s'.flags = s.flags ∧ s'.mem = s.mem ∧ ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · rw [sailJccCond_e, one_beq_boolBit]
    cases z <;> simp [evalInstr, x86_CMOVcc, sailCmovcc64, JState.flagB, JState.setReg, hz]
  · simp [evalInstr, JState.setReg, hr]

/-- `CMOVB dst, src` with a defined `CF = cfv`, as `cmovne_eq_sail` for opcode
    `0x42`. -/
theorem cmovb_eq_sail (s : JState 64) (dst src : String) (cfv : Bool)
    (hc : s.flags.cf = some cfv) (o z : BitVec 1) :
    let s' := evalInstr s (.cmovb dst (.reg src))
    (sailJccCond 0x42#8 o (boolBit cfv) z).map (sailCmovcc64 · (s.get dst) (s.get src))
        = some (s'.get dst) ∧
      s'.flags = s.flags ∧ s'.mem = s.mem ∧ ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · rw [sailJccCond_b, one_beq_boolBit]
    cases cfv <;> simp [evalInstr, x86_CMOVcc, sailCmovcc64, JState.flagB, JState.setReg, hc]
  · simp [evalInstr, JState.setReg, hr]

/-! ## `MOV` against Sail's MOV instruction functions

Each function below transcribes the value written to the destination register
by a Sail MOV instruction function (`Out/Move.lean`) at operand size `8` with a
register destination (`mod_var = 0b11` where a ModRM byte is present). Besides
that register, the quoted functions write only the instruction pointer; none
writes `rflags`. -/

/-- The 64-bit register-to-register data path of `x86_mov_op_en_rm` (opcode
    `0x8B`) and `x86_mov_op_en_mr` (opcode `0x89`), as a function of the source
    register value `register_var` (`rr64`). The generated code is

    ```lean
    -- x86_mov_op_en_rm
      let (reg_mem, increment_rip_by, addr) ← (( do
        (x86_operand_from_modr_m_and_sib_bytes proc_mode 0#1 operand_size inst_ac? false seg_reg
          prefixes temp_rip rex_byte r_m mod_var sib 0b000#3) ) : SailM
        ((BitVec 128) × Int × (sbits 64)) )
      ...
      (write_rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2)
        (Sail.BitVec.truncate reg_mem 64) rex_byte)
    -- x86_mov_op_en_mr
      let register_var ← (( do
        (rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2) rex_byte) ) : SailM
        (BitVec 64) )
      ...
      (x86_operand_to_reg_mem proc_mode operand_size inst_ac? false
        (Sail.BitVec.zeroExtend register_var 128) seg_reg addr prefixes rex_byte r_m mod_var sib)
    ```

    where, at `mod_var = 0b11`, `reg_mem` is
    `Sail.BitVec.zeroExtend (← (rgfi_size ...)) 128` and
    `x86_operand_to_reg_mem` is
    `write_rgfi_size (bits_of_int operand_size 4) (reg_index r_m rex_byte 0b00#2) (Sail.BitVec.truncate operand 64) rex_byte`
    (`Out/DecodingAndSpecUtils.lean`). -/
def sailMovRegReg64 (register_var : BitVec 64) : BitVec 64 :=
  (register_var.setWidth 128).setWidth 64

/-- The 64-bit data path of `x86_mov_op_en_oi` (opcode `REX.W 0xB8+r`), as a
    function of the eight-byte immediate `imm`, which `rme_size` returns
    zero-extended to 128 bits:

    ```lean
      let imm ← (( do
        (rme_size proc_mode (← (select_address_size proc_mode (some prefixes))) operand_size
          (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM (BitVec 128) )
      ...
      let reg : (BitVec 3) := (Sail.BitVec.truncate (0x07#8 &&& opcode) 3)
      (write_rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b00#2)
        (Sail.BitVec.truncate imm 64) rex_byte)
    ``` -/
def sailMovOi64 (imm : BitVec 64) : BitVec 64 := (imm.setWidth 128).setWidth 64

/-- The 64-bit register-destination data path of `x86_mov_op_en_mi` (opcode
    `REX.W 0xC7 /0`), as a function of the four-byte immediate `imm`:

    ```lean
      let reg_mem_size : Int :=
        if (((opcode == 0xC7#8) && (logbitp_bits 3 rex_byte)) : Bool)
        then 8
        else imm_size
      ...
      let imm : (BitVec 128) :=
        if ((reg_mem_size == 8) : Bool)
        then (Sail.BitVec.zeroExtend (Sail.BitVec.signExtend (Sail.BitVec.truncate imm 32) 64) 128)
        else imm
      let inst_ac? : Bool := true
      (x86_operand_to_reg_mem proc_mode reg_mem_size inst_ac? false imm seg_reg addr prefixes rex_byte
        r_m mod_var sib)
    ``` -/
def sailMovMi64 (imm : BitVec 32) : BitVec 64 :=
  ((imm.signExtend 64).setWidth 128).setWidth 64

/-- `MOV dst, src` with a register source: `dst` holds `sailMovRegReg64` of the
    source value; flags, memory and all other registers are unchanged. -/
theorem mov_reg_eq_sail (s : JState 64) (dst src : String) :
    let s' := evalInstr s (.mov dst (.reg src))
    s'.get dst = sailMovRegReg64 (s.get src) ∧ s'.flags = s.flags ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · simp [evalInstr, x86_MOV, sailMovRegReg64, JState.setReg]
  · simp [evalInstr, JState.setReg, hr]

/-- `MOV dst, k` as the eight-byte immediate form: `dst` holds `sailMovOi64` of
    `k mod 2^64`; flags, memory and all other registers are unchanged. -/
theorem mov_imm_eq_sail_oi (s : JState 64) (dst : String) (k : Nat) :
    let s' := evalInstr s (.mov dst (.imm k))
    s'.get dst = sailMovOi64 (BitVec.ofNat 64 k) ∧ s'.flags = s.flags ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · simp [evalInstr, x86_MOV, sailMovOi64, JState.setReg]
  · simp [evalInstr, JState.setReg, hr]

/-- `MOV dst, k` as the sign-extended four-byte immediate form, for a `k` whose
    64-bit value is the sign extension of its low 32 bits: `dst` holds
    `sailMovMi64` of `k mod 2^32`; flags, memory and all other registers are
    unchanged. -/
theorem mov_imm_eq_sail_mi (s : JState 64) (dst : String) (k : Nat)
    (hk : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k) :
    let s' := evalInstr s (.mov dst (.imm k))
    s'.get dst = sailMovMi64 (BitVec.ofNat 32 k) ∧ s'.flags = s.flags ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ dst → s'.get r = s.get r := by
  refine ⟨?_, rfl, rfl, fun r hr => ?_⟩
  · simp [evalInstr, x86_MOV, sailMovMi64, JState.setReg, hk]
  · simp [evalInstr, JState.setReg, hr]

end SailX86LeanUniversal

end CatCrypt.Crypto.SecureCompilation.X86Backend
