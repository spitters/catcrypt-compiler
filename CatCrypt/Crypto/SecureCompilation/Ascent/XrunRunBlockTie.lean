/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresDescentX86

/-!
# The `xrun` machine lifted to `runBlock`

The x86 `ScalarTarget` of `ScalarLinX86Demo` runs `xrun`, the `step` fold of
`X86Backend.Model` over `List (Instr 64)`: a register file and the flags
`CF`/`OF`/`ZF`/`SF`. The `runBlock` leaf library of
`Ascent/RunBlockCorres.lean` (`corresJ_sbb`, `corresJ_adc`, `CorresSolver`) runs
`runBlock`, the `evalInstr` fold of `X86Backend.JasminModel` over
`List (JInstr 64)`: registers, memory and five `Option Bool` flags, the
transcription of Jasmin's Rocq semantics. `corres_of_refines_x86` lands a descent
result on the first machine; the leaves live on the second. This module
translates the first machine's instructions to the second's and lifts a run of
the one to a run of the other.

The two machines agree on every register a covered instruction writes; on the
flags they agree only where the `Model` writes what Jasmin writes. `XJTrack`
selects which of `CF`/`OF`/`ZF` the state relation `XJRel` tracks, and
`XJFaithful t` is the instruction set on which `XJRel t` is preserved. `add`
and `sub` are faithful at every track: the `Model` writes all of `CF`/`OF`/`ZF`
as Jasmin's `rflags_of_aluop` does (`add_cf_eq`, `add_of_eq`, `zf_eq` and the
`sub` twins). An instruction is excluded at a track when Jasmin writes a
tracked flag the `Model` leaves alone (`adc`/`sbb`/`neg` at `OF` and `ZF`;
`imul`, the bitwise ops and the shifts at all three), when it reads an
untracked flag (`adc`/`sbb`/`adcx`/`cmov b` need `CF`, `adox` needs `OF`,
`cmov e`/`cmov ne` need `ZF`), or when its shift count is not an immediate
below the word width (Jasmin masks the count, the `Model` does not).

## Main results

* `xinstrToJ` — the total translation `Instr 64 → JInstr 64`.
* `XJRel`, `XJFaithful` — the tracked state relation and its preserved
  instruction set.
* `step_evalInstr_xj` — one instruction preserves `XJRel t` under `XJFaithful t`.
* `xrun_runBlock_tie` — the lift: `XJRel t s j` and a faithful block give
  `XJRel t (xrun s xs) (runBlock j (xs.map xinstrToJ))`.
* `corresMPost_runBlock_of_xrun` — a `CorresMPost` at `xrunStep` whose relations
  read only the registers is a `CorresMPost` at `runBlockStep` for the
  translated block.
* `corres_of_refines_x86_runBlock` — `corres_of_refines_x86` at `runBlockStep`.
* `runBlock_readout_of_refines_x86` — the same, unfolded to a register readout.
* `add_descent_runBlock` — the compiled `fieldAddCom` block, translated and run
  on `runBlock`, leaves `a + b` in the result register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
open CatCrypt.Crypto.SecureCompilation.RelationalCompile
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The instruction translation -/

/-- An `X86Backend.Model` operand as a `JasminModel` operand. -/
def operandToJ : Operand → JOperand
  | .reg r => .reg r
  | .imm v => .imm v

/-- A translated operand evaluates as the original does whenever the register
    files agree. -/
theorem operandToJ_eval (o : Operand) (s : State 64) (j : JState 64)
    (h : s.regs = j.regs) : (operandToJ o).eval j = o.eval s := by
  cases o <;> simp [operandToJ, h]

/-- The `X86Backend.Model` instruction as its `JasminModel` transcription. Total:
    every arm of `Instr` names an `Ox86_*_instr` that `JInstr` carries. -/
def xinstrToJ : Instr 64 → JInstr 64
  | .mov d s => .mov d (operandToJ s)
  | .add d s => .add d (operandToJ s)
  | .sub d s => .sub d (operandToJ s)
  | .adc d s => .adc d (operandToJ s)
  | .sbb d s => .sbb d (operandToJ s)
  | .mul d s => .imul d (operandToJ s)
  | .and_ d s => .and_ d (operandToJ s)
  | .or_ d s => .or_ d (operandToJ s)
  | .xor_ d s => .xor_ d (operandToJ s)
  | .shl d s => .shl d (operandToJ s)
  | .shr d s => .shr d (operandToJ s)
  | .sar d s => .sar d (operandToJ s)
  | .cmov .e d s => .cmove d (operandToJ s)
  | .cmov .ne d s => .cmovne d (operandToJ s)
  | .cmov .b d s => .cmovb d (operandToJ s)
  | .mulx dHi dLo a b => .mulx dHi dLo (operandToJ a) (operandToJ b)
  | .adcx d s => .adcx d (operandToJ s)
  | .adox d s => .adox d (operandToJ s)
  | .not_ d => .not_ d
  | .neg d => .neg d

/-! ## 2. The tracked state relation -/

/-- Which of the flags the `Model` carries the relation tracks. -/
structure XJTrack where
  /-- Track the carry flag. -/
  cf : Bool
  /-- Track the overflow flag. -/
  of : Bool
  /-- Track the zero flag. -/
  zf : Bool

/-- Registers only. -/
def XJTrack.regs : XJTrack := ⟨false, false, false⟩

/-- Registers and the carry flag: the `adc`/`sbb` chain. -/
def XJTrack.carry : XJTrack := ⟨true, false, false⟩

/-- Registers and both carry chains: the `mulx`/`adcx`/`adox` idiom. -/
def XJTrack.adx : XJTrack := ⟨true, true, false⟩

/-- Registers and all three tracked flags: `add`/`sub` blocks with conditional
    moves on the zero flag. -/
def XJTrack.alu : XJTrack := ⟨true, true, true⟩

/-- The register files agree, and each tracked flag of the `Model` equals the
    corresponding Jasmin flag read as a `Bool` (`Undef` reads as `false`). -/
def XJRel (t : XJTrack) (s : State 64) (j : JState 64) : Prop :=
  s.regs = j.regs ∧ (t.cf = true → s.flags.cf = j.flagB (·.cf)) ∧
    (t.of = true → s.flags.of = j.flagB (·.of)) ∧
    (t.zf = true → s.flags.zf = j.flagB (·.zf))

/-- A shift count the two models agree on: an immediate below the word width. -/
def ShiftOpOK : Operand → Prop
  | .imm i => i < 64
  | .reg _ => False

/-- The instructions on which `XJRel t` is preserved. -/
def XJFaithful (t : XJTrack) : Instr 64 → Prop
  | .mov _ _ | .mulx _ _ _ _ | .not_ _ | .add _ _ | .sub _ _ => True
  | .neg _ => t.of = false ∧ t.zf = false
  | .adc _ _ | .sbb _ _ => t.cf = true ∧ t.of = false ∧ t.zf = false
  | .adcx _ _ => t.cf = true
  | .adox _ _ => t.of = true
  | .mul _ _ | .and_ _ _ | .or_ _ _ | .xor_ _ _ => t.cf = false ∧ t.of = false ∧ t.zf = false
  | .shl _ src | .shr _ src | .sar _ src =>
      t.cf = false ∧ t.of = false ∧ t.zf = false ∧ ShiftOpOK src
  | .cmov .b _ _ => t.cf = true
  | .cmov .e _ _ | .cmov .ne _ _ => t.zf = true

/-! ## 3. The word and flag arithmetic the two models share -/

/-- The `Model`'s add-with-carry word is Jasmin's `add_carry`. -/
theorem add_carry_word (a b : BitVec 64) (c : Bool) :
    a + b + (if c then 1 else 0) = add_carry a b (if c then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [add_carry, BitVec.toNat_ofNat]
  cases c <;> simp [BitVec.toNat_add]

/-- The `Model`'s subtract-with-borrow word is Jasmin's `sub_borrow`. -/
theorem sub_borrow_word (a b : BitVec 64) (c : Bool) :
    a - b - (if c then 1 else 0) = sub_borrow a b (if c then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [sub_borrow, BitVec.toNat_ofInt]
  have ha := a.isLt
  have hb := b.isLt
  cases c <;> simp [BitVec.toNat_sub] <;> omega

/-- The `Model`'s multiply word is Jasmin's `wumul` low word. -/
theorem mul_word (a b : BitVec 64) : a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]

/-- Jasmin's `x86_ADD` carry is the `Model`'s carry-out. -/
theorem add_cf_eq (a b : BitVec 64) :
    decide ((a + b).toNat ≠ a.toNat + b.toNat) = addCarry a b false := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [addCarry, decide_eq_decide, BitVec.toNat_add, Bool.false_eq_true, if_false]
  omega

/-- Jasmin's `x86_SUB` carry is the `Model`'s borrow-out. -/
theorem sub_cf_eq (a b : BitVec 64) :
    decide (((a - b).toNat : Int) ≠ (a.toNat : Int) - (b.toNat : Int))
      = subBorrow a b false := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [subBorrow, decide_eq_decide, BitVec.toNat_sub, Bool.false_eq_true, if_false]
  omega

/-- Jasmin's `add_carry` carry is the `Model`'s carry-out. -/
theorem adc_cf_eq (a b : BitVec 64) (c : Bool) :
    decide ((add_carry a b (if c then 1 else 0)).toNat
        ≠ a.toNat + b.toNat + (if c then 1 else 0))
      = addCarry a b c := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [addCarry, decide_eq_decide, add_carry, BitVec.toNat_ofNat]
  cases c <;> simp

/-- Jasmin's `sub_borrow` borrow is the `Model`'s borrow-out. -/
theorem sbb_cf_eq (a b : BitVec 64) (c : Bool) :
    decide (((sub_borrow a b (if c then 1 else 0)).toNat : Int)
        ≠ (a.toNat : Int) - (b.toNat + (if c then 1 else 0 : Nat)))
      = subBorrow a b c := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [subBorrow, decide_eq_decide, sub_borrow, BitVec.toNat_ofInt,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide : ((2 ^ 64 : Nat) : Int) ≠ 0))]
  cases c <;> simp <;> omega

/-- Jasmin's `x86_ADD` overflow flag is the `Model`'s signed overflow. -/
theorem add_of_eq (a b : BitVec 64) :
    decide ((a + b).toInt ≠ a.toInt + b.toInt) = addOverflow a b false := by
  have ha := a.toInt_lt
  have ha' := a.le_toInt
  have hb := b.toInt_lt
  have hb' := b.le_toInt
  simp only [addOverflow, signedOverflow, Bool.false_eq_true, if_false, add_zero,
    decide_eq_decide, BitVec.toInt_add]
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.reduceSub, Int.reducePow] at *
  split <;> omega

/-- Jasmin's `x86_SUB` overflow flag is the `Model`'s signed overflow. -/
theorem sub_of_eq (a b : BitVec 64) :
    decide ((a - b).toInt ≠ a.toInt - b.toInt) = subOverflow a b false := by
  have ha := a.toInt_lt
  have ha' := a.le_toInt
  have hb := b.toInt_lt
  have hb' := b.le_toInt
  simp only [subOverflow, signedOverflow, Bool.false_eq_true, if_false, sub_zero,
    decide_eq_decide, BitVec.toInt_sub]
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.reduceSub, Int.reducePow] at *
  split <;> omega

/-- Jasmin's `ZF_of_word` is the zero test of the word, the `Model`'s `ZF`. -/
theorem zf_eq (v : BitVec 64) : ZF_of_word v = decide (v = 0) := by
  simp only [ZF_of_word, decide_eq_decide, BitVec.toNat_eq]
  exact Iff.rfl

/-- The data word of `x86_SHL` is the shift by the masked count. -/
theorem x86_SHL_word (v i : BitVec 64) : (x86_SHL v i).word = v <<< (i.toNat % 64) := by
  simp only [x86_SHL, shiftCount]
  by_cases h : i.toNat % 64 = 0 <;> simp_all [rflags_None, rflags_OF, wshl,
    Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 64)))]

/-- The data word of `x86_SHR` is the shift by the masked count. -/
theorem x86_SHR_word (v i : BitVec 64) : (x86_SHR v i).word = v >>> (i.toNat % 64) := by
  simp only [x86_SHR, shiftCount]
  by_cases h : i.toNat % 64 = 0 <;> simp_all [rflags_None, rflags_OF, wshr,
    Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 64)))]

/-- The data word of `x86_SAR` is the arithmetic shift by the masked count. -/
theorem x86_SAR_word (v i : BitVec 64) :
    (x86_SAR v i).word = BitVec.sshiftRight v (i.toNat % 64) := by
  simp only [x86_SAR, shiftCount]
  by_cases h : i.toNat % 64 = 0 <;> simp_all [rflags_None, rflags_OF, wsar,
    Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 64)))]

/-- An immediate below the word width is its own operand value. -/
theorem imm_toNat_lt (n : Nat) (h : n < 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## 4. One instruction -/

/-- One faithful instruction preserves the tracked relation. -/
theorem step_evalInstr_xj (t : XJTrack) {s : State 64} {j : JState 64} (i : Instr 64)
    (hi : XJFaithful t i) (h : XJRel t s j) :
    XJRel t (step s i) (evalInstr j (xinstrToJ i)) := by
  obtain ⟨hreg, hcf, hof, hzf⟩ := h
  obtain ⟨sr, sf⟩ := s
  obtain ⟨jr, jf, jm⟩ := j
  dsimp only at hreg
  subst hreg
  simp only [JState.flagB] at hcf hof hzf
  have hop : ∀ o : Operand, (operandToJ o).eval ⟨sr, jf, jm⟩ = o.eval ⟨sr, sf⟩ :=
    fun o => operandToJ_eval o _ _ rfl
  cases i with
  | mov d o =>
    simp only [step, evalInstr, xinstrToJ, hop, State.set, JState.setReg, x86_MOV]
    exact ⟨rfl, hcf, hof, hzf⟩
  | add d o =>
    simp only [step, evalInstr, xinstrToJ, hop, State.setALU, State.set, State.get,
      JState.writeB5W, JState.get, wunsigned, wsigned, x86_ADD, rflags_of_aluop, aluFlags]
    exact ⟨rfl, fun _ => (add_cf_eq _ _).symm, fun _ => (add_of_eq _ _).symm,
      fun _ => (zf_eq _).symm⟩
  | sub d o =>
    simp only [step, evalInstr, xinstrToJ, hop, State.setALU, State.set, State.get,
      JState.writeB5W, JState.get, wunsigned, wsigned, x86_SUB, aluFlags]
    exact ⟨rfl, fun _ => (sub_cf_eq _ _).symm, fun _ => (sub_of_eq _ _).symm,
      fun _ => (zf_eq _).symm⟩
  | adc d o =>
    simp only [XJFaithful] at hi
    obtain ⟨hc, ho, hz⟩ := hi
    have hcf' := hcf hc
    simp only [step, evalInstr, xinstrToJ, hop, State.setCF, State.set, State.get,
      JState.writeB5W, JState.get, JState.flagB, wunsigned, x86_ADC, rflags_of_aluop, hcf',
      add_carry_word]
    exact ⟨rfl, fun _ => (adc_cf_eq _ _ _).symm, by simp [ho], by simp [hz]⟩
  | sbb d o =>
    simp only [XJFaithful] at hi
    obtain ⟨hc, ho, hz⟩ := hi
    have hcf' := hcf hc
    simp only [step, evalInstr, xinstrToJ, hop, State.setCF, State.set, State.get,
      JState.writeB5W, JState.get, JState.flagB, wunsigned, x86_SBB, hcf', sub_borrow_word]
    exact ⟨rfl, fun _ => (sbb_cf_eq _ _ _).symm, by simp [ho], by simp [hz]⟩
  | mul d o =>
    simp only [XJFaithful] at hi
    simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.writeB5W,
      JState.get, x86_IMULt, rflags_of_mul]
    exact ⟨rfl, by simp [hi.1], by simp [hi.2.1], by simp [hi.2.2]⟩
  | and_ d o =>
    simp only [XJFaithful] at hi
    simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.writeB5W,
      JState.get, x86_AND, rflags_of_bwop]
    exact ⟨rfl, by simp [hi.1], by simp [hi.2.1], by simp [hi.2.2]⟩
  | or_ d o =>
    simp only [XJFaithful] at hi
    simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.writeB5W,
      JState.get, x86_OR, rflags_of_bwop]
    exact ⟨rfl, by simp [hi.1], by simp [hi.2.1], by simp [hi.2.2]⟩
  | xor_ d o =>
    simp only [XJFaithful] at hi
    simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.writeB5W,
      JState.get, x86_XOR, rflags_of_bwop]
    exact ⟨rfl, by simp [hi.1], by simp [hi.2.1], by simp [hi.2.2]⟩
  | shl d o =>
    simp only [XJFaithful] at hi
    obtain ⟨hc, ho, hz, hsh⟩ := hi
    cases o with
    | reg _ => exact absurd hsh id
    | imm n =>
      simp only [step, evalInstr, xinstrToJ, operandToJ, Operand.eval, JOperand.eval,
        State.set, State.get, JState.writeB5W, JState.get, x86_SHL_word,
        imm_toNat_lt n hsh, Nat.mod_eq_of_lt hsh, shiftMask_of_lt hsh]
      exact ⟨rfl, by simp [hc], by simp [ho], by simp [hz]⟩
  | shr d o =>
    simp only [XJFaithful] at hi
    obtain ⟨hc, ho, hz, hsh⟩ := hi
    cases o with
    | reg _ => exact absurd hsh id
    | imm n =>
      simp only [step, evalInstr, xinstrToJ, operandToJ, Operand.eval, JOperand.eval,
        State.set, State.get, JState.writeB5W, JState.get, x86_SHR_word,
        imm_toNat_lt n hsh, Nat.mod_eq_of_lt hsh, shiftMask_of_lt hsh]
      exact ⟨rfl, by simp [hc], by simp [ho], by simp [hz]⟩
  | sar d o =>
    simp only [XJFaithful] at hi
    obtain ⟨hc, ho, hz, hsh⟩ := hi
    cases o with
    | reg _ => exact absurd hsh id
    | imm n =>
      simp only [step, evalInstr, xinstrToJ, operandToJ, Operand.eval, JOperand.eval,
        State.set, State.get, JState.writeB5W, JState.get, x86_SAR_word,
        imm_toNat_lt n hsh, Nat.mod_eq_of_lt hsh, shiftMask_of_lt hsh]
      exact ⟨rfl, by simp [hc], by simp [ho], by simp [hz]⟩
  | cmov cc d o =>
    cases cc with
    | e =>
      simp only [XJFaithful] at hi
      have hzf' := hzf hi
      simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.setReg,
        JState.get, JState.flagB, Cond.eval, x86_CMOVcc, hzf']
      exact ⟨rfl, hcf, hof, hzf⟩
    | ne =>
      simp only [XJFaithful] at hi
      have hzf' := hzf hi
      simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.setReg,
        JState.get, JState.flagB, Cond.eval, x86_CMOVcc, hzf']
      exact ⟨rfl, hcf, hof, hzf⟩
    | b =>
      simp only [XJFaithful] at hi
      have hcf' := hcf hi
      simp only [step, evalInstr, xinstrToJ, hop, State.set, State.get, JState.setReg,
        JState.get, JState.flagB, Cond.eval, x86_CMOVcc, hcf']
      exact ⟨rfl, hcf, hof, hzf⟩
  | mulx dHi dLo a b =>
    simp only [step, evalInstr, xinstrToJ, hop, State.setLoHi, State.set, JState.setReg,
      x86_MULX_lo_hi, wumul, high_bits, mulHi, mul_word]
    exact ⟨rfl, hcf, hof, hzf⟩
  | adcx d o =>
    simp only [XJFaithful] at hi
    have hcf' := hcf hi
    simp only [step, evalInstr, xinstrToJ, hop, State.setCF, State.set, State.get,
      JState.get, JState.flagB, x86_ADCX, waddcarry, hcf', add_carry_word, add_carry,
      addCarry]
    exact ⟨rfl, fun _ => rfl, hof, hzf⟩
  | adox d o =>
    simp only [XJFaithful] at hi
    have hof' := hof hi
    simp only [step, evalInstr, xinstrToJ, hop, State.setOF, State.set, State.get,
      JState.get, JState.flagB, x86_ADCX, waddcarry, hof', add_carry_word, add_carry,
      addCarry]
    exact ⟨rfl, hcf, fun _ => rfl, hzf⟩
  | not_ d =>
    simp only [step, evalInstr, xinstrToJ, State.set, State.get, JState.setReg, JState.get,
      x86_NOT]
    exact ⟨rfl, hcf, hof, hzf⟩
  | neg d =>
    simp only [XJFaithful] at hi
    simp only [step, evalInstr, xinstrToJ, State.setCF, State.set, State.get,
      JState.writeB5W, JState.get, x86_NEG]
    exact ⟨rfl, fun _ => rfl, by simp [hi.1], by simp [hi.2]⟩

/-! ## 5. The lift -/

/-- **The lift.** From related states, a block whose every instruction is faithful
    at the track `t` runs to related states: `xrun` on the `Model`, `runBlock` on
    the translated block. -/
theorem xrun_runBlock_tie (t : XJTrack) {s : State 64} {j : JState 64} (h : XJRel t s j)
    (xs : List XInstr) (hf : ∀ i ∈ xs, XJFaithful t i) :
    XJRel t (xrun s xs) (runBlock j (xs.map xinstrToJ)) := by
  induction xs generalizing s j with
  | nil => exact h
  | cons i is ih =>
    show XJRel t (xrun (step s i) is) (runBlock (evalInstr j (xinstrToJ i)) (is.map xinstrToJ))
    exact ih (step_evalInstr_xj t i (hf i (by simp)) h) (fun i' hi' => hf i' (by simp [hi']))

/-! ## 6. The descent bridge at `runBlock` -/

/-- A `CorresMPost` at `xrunStep` whose entry and exit relations read only the
    register file is a `CorresMPost` at `runBlockStep` for the translated block,
    provided every instruction is faithful at the register-only track. -/
theorem corresMPost_runBlock_of_xrun {AState : Type}
    (Rin Rout : (String → BitVec 64) → AState → Prop) {P : AState → Prop}
    {fa : AState → AState} {c : List XInstr} (hf : ∀ i ∈ c, XJFaithful .regs i)
    (h : CorresMPost xrunStep (fun s : XState => Rin s.regs) (fun s : XState => Rout s.regs)
      P fa c) :
    CorresMPost runBlockStep (fun j : JState 64 => Rin j.regs) (fun j : JState 64 => Rout j.regs)
      P fa (c.map xinstrToJ) := by
  intro j a hin hP
  obtain ⟨m', hm', hout⟩ := h ⟨j.regs, {}⟩ a hin hP
  rw [xrunStep, Option.some.injEq] at hm'
  subst hm'
  refine ⟨_, rfl, ?_⟩
  have htie := xrun_runBlock_tie .regs (s := ⟨j.regs, {}⟩) (j := j)
    ⟨rfl, by simp [XJTrack.regs], by simp [XJTrack.regs], by simp [XJTrack.regs]⟩ c hf
  dsimp only at hout ⊢
  rw [htie.1] at hout
  exact hout

/-- The shift immediates of a statement are below the word width. -/
def ShiftAmtLt64 : RegStmt → Prop
  | .shrI _ _ i | .shlI _ _ i => i < 64
  | _ => True

/-- A shift immediate below the word width is in the `ShiftAmtOK` range. -/
theorem shiftAmtOK_of_lt64 {stmt : RegStmt} (h : ShiftAmtLt64 stmt) : ShiftAmtOK stmt := by
  cases stmt <;> simp only [ShiftAmtLt64, ShiftAmtOK] at h ⊢ <;> omega

/-- Every instruction `toX86` selects for a statement whose shift immediate is
    below the word width is faithful at the register-only track. -/
theorem toX86_XJFaithful (stmt : RegStmt) (hs : ShiftAmtLt64 stmt) :
    ∀ i ∈ toX86 stmt, XJFaithful .regs i := by
  cases stmt <;> simp_all [toX86, XJFaithful, ShiftOpOK, XJTrack.regs, ShiftAmtLt64]

/-- Every instruction the x86 `ScalarTarget` emits for a program whose shift
    immediates are below the word width is faithful at the register-only track. -/
theorem compile_XJFaithful (p : RegProg) (hsh : ∀ stmt ∈ p, ShiftAmtLt64 stmt) :
    ∀ i ∈ x86Target.compile p, XJFaithful .regs i := by
  intro i hi
  simp only [ScalarTarget.compile] at hi
  obtain ⟨stmt, hstmt, hmem⟩ := List.mem_flatMap.mp hi
  exact toX86_XJFaithful stmt (hsh stmt hstmt) i hmem

/-- **The x86 bridge at `runBlock`.** `corres_of_refines_x86`, with the compiled
    block translated to `JInstr` and run under `runBlock`: the forward simulation
    from `SRview` to `SRret` at the abstract step `spec`, on the machine of the
    `CorresJ` leaf library. The shift side condition is the one the two models
    share, `ShiftAmtLt64`. -/
theorem corres_of_refines_x86_runBlock {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (e : Env 64 Γ) {spec : StateStep 64} {frag : Frag 64} (h : Refines spec frag) (dst : Nat)
    (hok : ComOK (descentCom frag e dst))
    (hsh : ∀ stmt ∈ comToRegProg (descentCom frag e dst) Γ.length, ShiftAmtLt64 stmt) :
    CorresMPost runBlockStep (SRview (fun j : JState 64 => j.regs) e)
      (SRret (fun j : JState 64 => j.regs) (comRetName (descentCom frag e dst) Γ.length) dst)
      (fun _ => True) spec
      ((x86Target.compile (comToRegProg (descentCom frag e dst) Γ.length)).map xinstrToJ) :=
  corresMPost_runBlock_of_xrun (SRview (M := String → BitVec 64) id e)
    (SRret (M := String → BitVec 64) id (comRetName (descentCom frag e dst) Γ.length) dst)
    (compile_XJFaithful _ hsh)
    (corres_of_refines_x86 hΓ e h dst hok (fun stmt hm => shiftAmtOK_of_lt64 (hsh stmt hm)))

/-- The bridge unfolded: from a `JState` reflecting the valuation `V`, `runBlock`
    over the translated block leaves slot `dst` of `spec` at the readout of `V` in
    the result register. -/
theorem runBlock_readout_of_refines_x86 {Γ : Ctxt jasminDialect} (hΓ : AllReg64 Γ)
    (e : Env 64 Γ) {spec : StateStep 64} {frag : Frag 64} (h : Refines spec frag) (dst : Nat)
    (hok : ComOK (descentCom frag e dst))
    (hsh : ∀ stmt ∈ comToRegProg (descentCom frag e dst) Γ.length, ShiftAmtLt64 stmt)
    (V : Ctxt.Valuation Γ) (j : JState 64) (hj : j.regs = envOf Γ.length V) :
    (runBlock j
        ((x86Target.compile (comToRegProg (descentCom frag e dst) Γ.length)).map xinstrToJ)).regs
        (comRetName (descentCom frag e dst) Γ.length)
      = (spec (readView e V)).slot dst := by
  obtain ⟨m', hstep, hout⟩ :=
    corres_of_refines_x86_runBlock hΓ e h dst hok hsh j _ ⟨V, hj, rfl⟩ trivial
  rw [runBlockStep, Option.some.injEq] at hstep
  subst hstep
  exact hout

/-! ## 7. The `fieldAddCom` block on `runBlock` -/

/-- The two-argument kernel compiles to statements whose shift immediates are
    below the word width (it has none). -/
theorem binCom_shiftLt64 (op : JasminBinOp) :
    ∀ stmt ∈ comToRegProg (descentCom (binFrag op) twoArgEnv 0) 2, ShiftAmtLt64 stmt := by
  rw [binCom_flatten]
  intro stmt hstmt
  cases op <;> simp_all [opToStmts, ShiftAmtLt64]

/-- The compiled x86 block of `fieldAddCom`, translated to `JInstr` and run under
    `runBlock` from a state with `a` in `v0` and `b` in `v1`, leaves `a + b` in the
    result register. -/
theorem add_descent_runBlock (a b : BitVec 64) (j : JState 64)
    (hj : j.regs = envOf 2 (twoArgVal a b)) :
    (runBlock j
        ((x86Target.compile (comToRegProg FieldEmitGoldenPath.fieldAddCom 2)).map xinstrToJ)).regs
        (comRetName FieldEmitGoldenPath.fieldAddCom 2)
      = a + b :=
  runBlock_readout_of_refines_x86 FieldEmitGoldenPath.allReg64_two twoArgEnv
    (binFrag_refines .add) 0 (binCom_ok .add (by supported_op)) (binCom_shiftLt64 .add)
    (twoArgVal a b) j hj

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.xrun_runBlock_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xrun_runBlock_tie

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.corres_of_refines_x86_runBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corres_of_refines_x86_runBlock

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.add_descent_runBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_descent_runBlock

end CatCrypt.Crypto.SecureCompilation.Ascent
