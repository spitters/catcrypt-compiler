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

Two kinds of reference semantics are used, and the theorem names say which:

* `*_eq_sail` compares with a transcribed Sail-exported body from `SailX86Lean`.
  Covered: `ADD`, `SUB`, `ADC`, `SBB`, `AND`, `OR`, `XOR` (the data word and the
  five flags `CF`, `OF`, `SF`, `ZF`, `PF`), `XOR r, r`, `MULX` with a register or
  memory second source (both words), `ADCX` (word and `CF`), `ADOX` (word and
  `OF`).
* `*_eq_sdm` compares with a definition in this module transcribed from the
  Intel 64 and IA-32 Architectures Software Developer's Manual (SDM), Volume 2,
  for instructions that have no Sail export in the transcription: `MOV`
  (`sdmMov`), `CMOVNE` (`sdmCmovne`) and `SHL` by an immediate count
  (`sdmShl`).

The `SHL` comparison covers masked counts `1 … 63` and all five flags, with
`OF` compared as a defined value at count `1` and as `none` (undefined in the
SDM, `none` in the model) at counts `2 … 63`. At masked count `0` the SDM leaves
the flags unaffected while the model marks them undefined, so that count is
excluded by hypothesis.

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

end SailX86LeanUniversal

end CatCrypt.Crypto.SecureCompilation.X86Backend
