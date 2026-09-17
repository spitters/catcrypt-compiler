/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.Vale.P384FieldMul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Correctness of the imported `bignum_montmul_p384` block

This module proves that `S2nMontmulP384.s2nMontmulP384Block` computes the Montgomery
product modulo `p384 = 2^384 - 2^128 - 2^96 + 2^32 - 1` under `runBlock`: for six-limb
inputs `x`, `y` with `x · y ≤ 2^384 · p384` it stores `z < p384` with
`z = x · y · (2^384)⁻¹` in `ZMod p384`.

The object of the proof is the imported block, not s2n-bignum's object file. The block was
produced by an untrusted importer (`bench/s2n_import/import_s2n.sh`), re-emitted and tested
against the original; the theorems here are stated over the block itself, so its
correctness does not depend on the importer translating the source faithfully. The
results are functional and say nothing about timing.

## Memory and calling convention

`JState.mem` is keyed by the base register's name. The block reads `x` through `%rsi`,
copies `%rdx` to `%rcx` and reads `y` through `%rcx`, and writes `z` through `%rdi`; the
hypotheses therefore place `x` at `st.mem "%rsi"` and `y` at `st.mem "%rcx"`, and the
result is read at `mem "%rdi"`. Distinct names are distinct memory banks, so an output
buffer aliasing an input buffer is outside the model. In the same model the register copy
`movq %rdx, %rcx` does not decide which bank `(%rcx)` addresses: that the bank named
`"%rcx"` holds the buffer the caller passed in `%rdx` is an assumption of name-keyed
memory, shared by every kernel whose loads go through `JasminModel`'s memory operations,
not a consequence of this proof. The saved-register frame is not part
of the block and is not described.

## Proof structure

* Transport lemmas, one per instruction form (`run_mov`, `run_loadMem`, `run_xor_self`,
  `run_mulxMem`, `run_mulx`, `run_adcx`, `run_adox`, `run_adc`, `run_add`, `run_sub`,
  `run_sbb`, `run_shl32`, `run_cmovne`, `run_storeMem`), over a state description `Desc`
  (register valuation, `CF`, `OF`, `ZF`, memory). Each names the words the instruction
  writes and records their equation over `Nat` (`w + 2^64 c = x + y + cin`,
  `hi · 2^64 + lo = x · y`), in the style of `Ascent.SolinasSquareCorrect`.
* Segment specifications closed by pure `Nat` lemmas: the first multiply row
  (`seg02_row0`, `row0_arith`), the five further rows (`RowSpec`, `seg04_row` …
  `seg12_row`, `row_arith`), the six reduction rounds (`RedcSpec`, `seg03_redc` …
  `seg13_redc`, `redc_arith`) and the final conditional subtraction with the output stores
  (`FinalSpec`, `final_spec`, `final_arith`).
* The reduction rounds are specialised to P-384: the multiplier is
  `d = c0 + (c0 << 32) = c0 · (2^32 + 1) mod 2^64`, which is `n' = -p384⁻¹ mod 2^64`, and
  `d · p384` is formed from the constants `2^64 - 2^32 + 1` and `2^32 - 1`. `redc_arith`
  shows that a round adds `d · p384` to the window and drops the zero low word; `redcF_mul`
  shows that the division is exact because `(2^32 + 1) · p384 ≡ -1 (mod 2^64)`.
* Each segment specification gives a `CorresJ SRm` step over the abstract state `AMont`
  (`corresJ_seg01`, `corresJ_seg02`, `corresJ_row`, `corresJ_redc`, `corresJ_final`), and
  `corresJ_append` composes the seventeen segments.

## Main results

* `s2nMontmulP384_corresJ`: the block refines the abstract algorithm `montAbs` through
  `SRm`.
* `montAbs_spec`: `montAbs x y < p384` and `montAbs x y = x · y · (2^384)⁻¹` in
  `ZMod p384`, for `y < 2^384` with `x · y ≤ 2^384 · p384`.
* `s2nMontmulP384_correct`: the machine-level statement over `runBlock`.
* `s2nMontmulP384_fmul_denote`: the same value is `P384_fmul_denote x y` in `P384Fp`, the
  specification of the P-384 field-multiply leaf (`Vale.P384FieldMul`).
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## State descriptions and one transport lemma per instruction form -/

/-- A flag read as a carry bit (`1` when set). -/
def cb (b : Bool) : Nat := if b then 1 else 0

theorem cb_le_one (b : Bool) : cb b ≤ 1 := by cases b <;> simp [cb]

theorem ite_cb (b : Bool) : (if b = true then 1 else 0 : Nat) = cb b := rfl

/-- The register valuation `R` with `d` overwritten by `w`. -/
def upd (R : String → BitVec 64) (d : String) (w : BitVec 64) : String → BitVec 64 :=
  fun r => if r = d then w else R r

/-- The value of an operand under the register valuation `R`. -/
def opv (R : String → BitVec 64) : JOperand → BitVec 64
  | .reg r => R r
  | .imm k => BitVec.ofNat 64 k

/-- A machine state described by its register valuation `R`, the three flags the block
    reads (`CF`, `OF`, `ZF`, each as `flagB` reads it) and its memory `M`. -/
structure Desc (R : String → BitVec 64) (cf of zf : Bool) (M : JMem 64) (s : JState 64) :
    Prop where
  regs : s.regs = R
  mem : s.mem = M
  hcf : s.flagB (·.cf) = cf
  hof : s.flagB (·.of) = of
  hzf : s.flagB (·.zf) = zf

theorem Desc.eval {R : String → BitVec 64} {cf of zf : Bool} {M : JMem 64} {s : JState 64}
    (hs : Desc R cf of zf M s) (o : JOperand) : o.eval s = opv R o := by
  cases o <;> simp [opv, hs.regs]

section Transport

variable {Q : JState 64 → Prop} {rest : List (JInstr 64)} {R : String → BitVec 64}
  {cf of zf : Bool} {M : JMem 64} {s : JState 64}

theorem run_mov (d : String) (o : JOperand) (hs : Desc R cf of zf M s)
    (h : ∀ t, Desc (upd R d (opv R o)) cf of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.mov d o :: rest)) := by
  rw [runBlock_cons]
  refine h _ ⟨?_, hs.mem, hs.hcf, hs.hof, hs.hzf⟩
  funext r
  simp only [evalInstr, JState.setReg, x86_MOV, hs.eval, upd, hs.regs]

theorem run_loadMem (d b : String) (o : Int) (hs : Desc R cf of zf M s)
    (h : ∀ t, Desc (upd R d (M b o)) cf of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.loadMem d b o :: rest)) := by
  rw [runBlock_cons]
  refine h _ ⟨?_, hs.mem, hs.hcf, hs.hof, hs.hzf⟩
  funext r
  simp only [evalInstr, JState.setReg, x86_MOV, JState.load, upd, hs.regs, hs.mem]

theorem run_xor_self (d : String) (hs : Desc R cf of zf M s)
    (h : ∀ z t, Desc (upd R d 0) false false z M t → Q (runBlock t rest)) :
    Q (runBlock s (.xor_ d (.reg d) :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ ⟨?_, hs.mem, rfl, rfl, rfl⟩
  funext r
  simp [evalInstr, JState.writeB5W, x86_XOR, rflags_of_bwop, upd, hs.regs]

theorem mulx_fact (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 (x * y / 2 ^ 64)).toNat * 2 ^ 64 + (BitVec.ofNat 64 (x * y)).toNat
      = x * y := by
  have hxy : x * y < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
  have hq : x * y / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hxy
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  have := Nat.div_add_mod (x * y) (2 ^ 64)
  rw [Nat.mul_comm] at this
  exact this

theorem run_mulxMem (hi lo a b : String) (o : Int) (hs : Desc R cf of zf M s)
    (h : ∀ wh wl : BitVec 64, wh.toNat * 2 ^ 64 + wl.toNat = (R a).toNat * (M b o).toNat →
      ∀ t, Desc (upd (upd R lo wl) hi wh) cf of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.mulxMem hi lo (.reg a) b o :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ (mulx_fact _ _ (R a).isLt (M b o).isLt) _ ⟨?_, hs.mem, hs.hcf, hs.hof, hs.hzf⟩
  funext r
  simp only [evalInstr, JState.setReg, x86_MULX_lo_hi, wumul, high_bits, JOperand.eval,
    JState.get, JState.load, upd, hs.regs, hs.mem]

theorem run_mulx (hi lo a b : String) (hs : Desc R cf of zf M s)
    (h : ∀ wh wl : BitVec 64, wh.toNat * 2 ^ 64 + wl.toNat = (R a).toNat * (R b).toNat →
      ∀ t, Desc (upd (upd R lo wl) hi wh) cf of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.mulx hi lo (.reg a) (.reg b) :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ (mulx_fact _ _ (R a).isLt (R b).isLt) _ ⟨?_, hs.mem, hs.hcf, hs.hof, hs.hzf⟩
  funext r
  simp only [evalInstr, JState.setReg, x86_MULX_lo_hi, wumul, high_bits, JOperand.eval,
    JState.get, upd, hs.regs]

theorem addc_fact (x y c : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hc : c ≤ 1) :
    (BitVec.ofNat 64 (x + y + c)).toNat + 2 ^ 64 * cb (decide (2 ^ 64 ≤ x + y + c))
      = x + y + c := by
  simp only [BitVec.toNat_ofNat, cb]
  by_cases h : 2 ^ 64 ≤ x + y + c
  · simp only [h, decide_true, if_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; omega

theorem run_adcx (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * cb c = (R d).toNat + (R src).toNat + cb cf → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) c of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.adcx d (.reg src) :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ (addc_fact _ _ _ (R d).isLt (R src).isLt (cb_le_one cf)) (cb_le_one _) _
    ⟨?_, hs.mem, ?_, hs.hof, hs.hzf⟩
  · funext r
    simp only [evalInstr, x86_ADCX, waddcarry, JOperand.eval, JState.get, upd, hs.regs, hs.hcf,
      cb]
  · have := hs.hcf
    simp only [JState.flagB] at this ⊢
    simp only [evalInstr, x86_ADCX, waddcarry, JOperand.eval, JState.get, hs.regs, cb,
      Option.getD_some, JState.flagB, this]
    rfl

theorem run_adox (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * cb c = (R d).toNat + (R src).toNat + cb of → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) cf c zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.adox d (.reg src) :: rest)) := by
  rw [runBlock_cons]
  refine h _ _ (addc_fact _ _ _ (R d).isLt (R src).isLt (cb_le_one of)) (cb_le_one _) _
    ⟨?_, hs.mem, hs.hcf, ?_, hs.hzf⟩
  · funext r
    simp only [evalInstr, x86_ADCX, waddcarry, JOperand.eval, JState.get, upd, hs.regs, hs.hof,
      cb]
  · have := hs.hof
    simp only [JState.flagB] at this ⊢
    simp only [evalInstr, x86_ADCX, waddcarry, JOperand.eval, JState.get, hs.regs, cb,
      Option.getD_some, JState.flagB, this]
    rfl

theorem run_adc (d : String) (o : JOperand) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool),
      w.toNat + 2 ^ 64 * cb c = (R d).toNat + (opv R o).toNat + cb cf → cb c ≤ 1 →
      z = decide (w.toNat = 0) →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.adc d o :: rest)) := by
  rw [runBlock_cons]
  have hx := (R d).isLt
  have hy := (opv R o).isLt
  have hc := cb_le_one cf
  refine h (BitVec.ofNat 64 ((R d).toNat + (opv R o).toNat + cb cf))
    (decide (2 ^ 64 ≤ (R d).toNat + (opv R o).toNat + cb cf)) _ _
    (addc_fact _ _ _ hx hy hc) (cb_le_one _) rfl _ ⟨?_, hs.mem, ?_, rfl, ?_⟩
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry, JState.get,
      hs.eval, hs.hcf, upd, hs.regs, cb]
  · simp only [evalInstr, hs.hcf, hs.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry, wunsigned,
      BitVec.toNat_ofNat, Option.getD_some, ite_cb]
    apply decide_eq_decide.mpr
    constructor <;> intro <;> omega
  · simp only [evalInstr, hs.hcf, hs.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry,
      Option.getD_some, ite_cb, ZF_of_word]
    exact decide_eq_decide.mpr Iff.rfl

theorem run_add (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool),
      w.toNat + 2 ^ 64 * cb c = (R d).toNat + (R src).toNat → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.add d (.reg src) :: rest)) := by
  rw [runBlock_cons]
  have hx := (R d).isLt
  have hy := (R src).isLt
  have hf := addc_fact _ _ _ hx hy (Nat.zero_le 1)
  simp only [Nat.add_zero] at hf
  refine h (BitVec.ofNat 64 ((R d).toNat + (R src).toNat))
    (decide (2 ^ 64 ≤ (R d).toNat + (R src).toNat)) _ _ hf (cb_le_one _) _
    ⟨?_, hs.mem, ?_, rfl, rfl⟩
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, JState.get,
      JOperand.eval, upd, hs.regs]
    split <;> simp [BitVec.ofNat_add]
  · simp only [evalInstr, JOperand.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_ADD, rflags_of_aluop, wunsigned,
      BitVec.toNat_add, Option.getD_some]
    apply decide_eq_decide.mpr
    constructor <;> intro <;> omega

theorem run_sub (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool),
      (R d).toNat + 2 ^ 64 * cb c = w.toNat + (R src).toNat → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.sub d (.reg src) :: rest)) := by
  rw [runBlock_cons]
  have hx := (R d).isLt
  have hy := (R src).isLt
  refine h (R d - R src) (decide ((R d).toNat < (R src).toNat)) _ _ ?_ (cb_le_one _) _
    ⟨?_, hs.mem, ?_, rfl, rfl⟩
  · simp only [BitVec.toNat_sub, cb]
    split <;> simp_all <;> omega
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_SUB, JState.get, JOperand.eval, upd, hs.regs]
  · simp only [evalInstr, JOperand.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_SUB, wunsigned, BitVec.toNat_sub,
      Option.getD_some]
    apply decide_eq_decide.mpr
    constructor <;> intro <;> omega

theorem run_sbb (d : String) (o : JOperand) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (c o' z : Bool),
      (R d).toNat + 2 ^ 64 * cb c = w.toNat + (opv R o).toNat + cb cf → cb c ≤ 1 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.sbb d o :: rest)) := by
  rw [runBlock_cons]
  have hx := (R d).isLt
  have hy := (opv R o).isLt
  have hc := cb_le_one cf
  refine h (sub_borrow (R d) (opv R o) (cb cf))
    (decide ((R d).toNat < (opv R o).toNat + cb cf)) _ _ ?_ (cb_le_one _) _
    ⟨?_, hs.mem, ?_, rfl, rfl⟩
  · simp only [sub_borrow, BitVec.toNat_ofInt, cb] at hc ⊢
    split <;> split <;> simp_all <;> omega
  · funext r
    simp only [evalInstr, JState.writeB5W, x86_SBB, JState.get, hs.eval, hs.hcf, upd, hs.regs,
      cb]
  · simp only [evalInstr, hs.hcf, hs.eval, JState.get, hs.regs]
    simp only [JState.flagB, JState.writeB5W, x86_SBB, wunsigned, sub_borrow,
      BitVec.toNat_ofInt, Option.getD_some]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, ne_eq]
    simp only [cb] at hc ⊢
    split <;> omega

theorem run_shl32 (d : String) (hs : Desc R cf of zf M s)
    (h : ∀ (w : BitVec 64) (k : Nat) (c o' z : Bool),
      w.toNat + 2 ^ 64 * k = (R d).toNat * 2 ^ 32 →
      ∀ t, Desc (upd R d w) c o' z M t → Q (runBlock t rest)) :
    Q (runBlock s (.shl d (.imm 32) :: rest)) := by
  rw [runBlock_cons]
  refine h (R d <<< 32) ((R d).toNat * 2 ^ 32 / 2 ^ 64) _ _ _ ?_ _ ⟨?_, hs.mem, rfl, rfl, rfl⟩
  · simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  · funext r
    simp [evalInstr, JState.writeB5W, x86_SHL, shiftCount, rflags_OF, wshl, upd, hs.regs]

theorem run_cmovne (d src : String) (hs : Desc R cf of zf M s)
    (h : ∀ t, Desc (upd R d (if zf then R d else R src)) cf of zf M t → Q (runBlock t rest)) :
    Q (runBlock s (.cmovne d (.reg src) :: rest)) := by
  rw [runBlock_cons]
  refine h _ ⟨?_, hs.mem, hs.hcf, hs.hof, hs.hzf⟩
  funext r
  simp only [evalInstr, JState.setReg, x86_CMOVcc, JOperand.eval, JState.get, hs.hzf, upd,
    hs.regs]
  cases zf <;> rfl

theorem run_storeMem (b : String) (o : Int) (src : String) (hs : Desc R cf of zf M s)
    (h : ∀ t, Desc R cf of zf (fun b' o' => if b' = b ∧ o' = o then R src else M b' o') t →
      Q (runBlock t rest)) :
    Q (runBlock s (.storeMem b o (.reg src) :: rest)) := by
  rw [runBlock_cons]
  refine h _ ⟨hs.regs, ?_, hs.hcf, hs.hof, hs.hzf⟩
  funext b' o'
  simp only [evalInstr, JState.store, x86_MOV, JOperand.eval, JState.get, hs.regs, hs.mem]

end Transport

theorem cb_false : cb false = 0 := rfl

/-- The states described by some register valuation, flags and memory satisfying `P`. -/
def Reach (P : (String → BitVec 64) → JMem 64 → Prop) (t : JState 64) : Prop :=
  ∃ R cf of zf M, Desc R cf of zf M t ∧ P R M

theorem reach_nil {P : (String → BitVec 64) → JMem 64 → Prop} {R : String → BitVec 64}
    {cf of zf : Bool} {M : JMem 64} {t : JState 64} (hs : Desc R cf of zf M t) (hP : P R M) :
    Reach P (runBlock t []) :=
  ⟨R, cf, of, zf, M, hs, hP⟩


/-- The carry equations of a multiply row: the `CF` chain `e0 … e4, e5 … e7` and the `OF`
    chain `f0 … f5` add the six partial products to the seven-limb window. The dropped `OF`
    out of the top limb is zero because that limb is at most one. -/
theorem row_arith (a0 a1 a2 a3 a4 a5 a6 : Nat) (ha6 : a6 ≤ 1)
    (p0 p1 p2 p3 p4 p5 h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 : Nat)
    (m0 : h0 * 2 ^ 64 + l0 = p0) (m1 : h1 * 2 ^ 64 + l1 = p1) (m2 : h2 * 2 ^ 64 + l2 = p2)
    (m3 : h3 * 2 ^ 64 + l3 = p3) (m4 : h4 * 2 ^ 64 + l4 = p4) (m5 : h5 * 2 ^ 64 + l5 = p5)
    (A0 A1 A2 A3 A4 A5 A6 A7 B1 B2 B3 B4 B5 B6 : Nat)
    (c0 c1 c2 c3 c4 c5 c6 c7 o1 o2 o3 o4 o5 o6 : Nat)
    (bc6 : c6 ≤ 1) (bo5 : o5 ≤ 1)
    (e0 : A0 + 2 ^ 64 * c0 = a0 + l0 + 0)
    (f0 : B1 + 2 ^ 64 * o1 = a1 + h0 + 0)
    (e1 : A1 + 2 ^ 64 * c1 = B1 + l1 + c0)
    (f1 : B2 + 2 ^ 64 * o2 = a2 + h1 + o1)
    (e2 : A2 + 2 ^ 64 * c2 = B2 + l2 + c1)
    (f2 : B3 + 2 ^ 64 * o3 = a3 + h2 + o2)
    (e3 : A3 + 2 ^ 64 * c3 = B3 + l3 + c2)
    (f3 : B4 + 2 ^ 64 * o4 = a4 + h3 + o3)
    (e4 : A4 + 2 ^ 64 * c4 = B4 + l4 + c3)
    (f4 : B5 + 2 ^ 64 * o5 = a5 + h4 + o4)
    (f5 : B6 + 2 ^ 64 * o6 = a6 + 0 + o5)
    (e5 : A5 + 2 ^ 64 * c5 = B5 + l5 + c4)
    (e6 : A6 + 2 ^ 64 * c6 = B6 + h5 + c5)
    (e7 : A7 + 2 ^ 64 * c7 = 0 + 0 + c6) :
    A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3 + 2 ^ 256 * A4 + 2 ^ 320 * A5
      + 2 ^ 384 * A6 + 2 ^ 448 * A7
    = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5
      + 2 ^ 384 * a6 + (p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4
      + 2 ^ 320 * p5) := by
  have ho6 : o6 = 0 := by clear * - ha6 bo5 f5; omega
  have hc7 : c7 = 0 := by clear * - bc6 e7; omega
  subst ho6 hc7
  clear ha6 bc6 bo5
  omega

/-- The P-384 prime `2^384 - 2^128 - 2^96 + 2^32 - 1`. -/
def p384 : Nat := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- The carry equations of a P-384 reduction round: `d = c0 · (2^32 + 1) mod 2^64` is formed
    by `shl`/`add` (`eS`, `eD`); `d · (2^384 - p384)` is formed from the constants
    `2^64 - 2^32 + 1` and `2^32 - 1` (`m1`, `m2`, `e9`–`e11`); it is subtracted from limbs
    `1 … 5` (`e12`–`e16`) and `d` is added at limb `6` (`e17`–`e19`). The low word of the
    first product equals `c0`, and the borrow out of `d` and the carry out of the top limb
    are zero, so the seven limbs `c1 … c7` hold `(⟦c0 … c7⟧ + d · p384) / 2^64`. -/
theorem redc_arith (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (hc0 : c0 < 2 ^ 64) (hc7 : c7 ≤ 1)
    (S k D ca H1 L1 H2 L2 X1 X2 X3 d1 d2 d3 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Z b1 b2 b3 b4 b5 b6 e1 e2 : Nat)
    (_hS : S < 2 ^ 64) (hD : D < 2 ^ 64) (hL1 : L1 < 2 ^ 64) (hH1 : H1 < 2 ^ 64)
    (hL2 : L2 < 2 ^ 64) (hH2 : H2 < 2 ^ 64) (hX1 : X1 < 2 ^ 64) (hX2 : X2 < 2 ^ 64)
    (_hX3 : X3 < 2 ^ 64) (hY1 : Y1 < 2 ^ 64) (hY2 : Y2 < 2 ^ 64) (hY3 : Y3 < 2 ^ 64)
    (hY4 : Y4 < 2 ^ 64) (hY5 : Y5 < 2 ^ 64) (_hY6 : Y6 < 2 ^ 64) (_hY7 : Y7 < 2 ^ 64)
    (hZ : Z < 2 ^ 64) (_hc1 : c1 < 2 ^ 64) (_hc2 : c2 < 2 ^ 64) (_hc3 : c3 < 2 ^ 64)
    (_hc4 : c4 < 2 ^ 64) (_hc5 : c5 < 2 ^ 64)
    (bd1 : d1 ≤ 1) (bd2 : d2 ≤ 1) (_bb1 : b1 ≤ 1) (_bb2 : b2 ≤ 1) (_bb3 : b3 ≤ 1)
    (_bb4 : b4 ≤ 1)
    (bb5 : b5 ≤ 1) (be1 : e1 ≤ 1)
    (eS : S + 2 ^ 64 * k = c0 * 2 ^ 32)
    (eD : D + 2 ^ 64 * ca = S + c0)
    (m1 : H1 * 2 ^ 64 + L1 = D * 18446744069414584321)
    (m2 : H2 * 2 ^ 64 + L2 = D * 4294967295)
    (e9 : X1 + 2 ^ 64 * d1 = H1 + L2 + 0)
    (e10 : X2 + 2 ^ 64 * d2 = H2 + D + d1)
    (e11 : X3 + 2 ^ 64 * d3 = 0 + 0 + d2)
    (e12 : c1 + 2 ^ 64 * b1 = Y1 + X1)
    (e13 : c2 + 2 ^ 64 * b2 = Y2 + X2 + b1)
    (e14 : c3 + 2 ^ 64 * b3 = Y3 + X3 + b2)
    (e15 : c4 + 2 ^ 64 * b4 = Y4 + 0 + b3)
    (e16 : c5 + 2 ^ 64 * b5 = Y5 + 0 + b4)
    (e17 : D + 2 ^ 64 * b6 = Z + 0 + b5)
    (e18 : Y6 + 2 ^ 64 * e1 = c6 + Z)
    (e19 : Y7 + 2 ^ 64 * e2 = c7 + 0 + e1) :
    D = c0 * 4294967297 % 2 ^ 64 ∧
    2 ^ 64 * (Y1 + 2 ^ 64 * Y2 + 2 ^ 128 * Y3 + 2 ^ 192 * Y4 + 2 ^ 256 * Y5 + 2 ^ 320 * Y6
      + 2 ^ 384 * Y7)
    = c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 + 2 ^ 320 * c5
      + 2 ^ 384 * c6 + 2 ^ 448 * c7 + D * p384 := by
  have hDv : D = c0 * 4294967297 % 2 ^ 64 := by clear * - eS eD hD; omega
  refine ⟨hDv, ?_⟩
  have hL1c : L1 = c0 := by clear * - eS eD hD m1 hL1 hc0 hH1; omega
  have hd3 : d3 = 0 := by clear * - e11 bd2; omega
  have he2 : e2 = 0 := by clear * - e19 hc7 be1; omega
  have hb6 : b6 = 0 := by
    rcases Nat.eq_zero_or_pos D with h0 | hpos
    · subst h0
      have : H1 = 0 ∧ L1 = 0 ∧ H2 = 0 ∧ L2 = 0 := by clear * - m1 m2; omega
      obtain ⟨rfl, rfl, rfl, rfl⟩ := this
      have : X1 = 0 ∧ d1 = 0 := by clear * - e9; omega
      obtain ⟨rfl, rfl⟩ := this
      have : X2 = 0 ∧ d2 = 0 := by clear * - e10; omega
      obtain ⟨rfl, rfl⟩ := this
      clear * - e11 e12 e13 e14 e15 e16 e17 hY1 hY2 hY3 hY4 hY5 hZ bb5
      omega
    · clear * - e17 hpos hZ bb5; omega
  subst hL1c hd3 he2 hb6
  clear * - m1 m2 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19
  have key : 2 ^ 64 * (Y1 + 2 ^ 64 * Y2 + 2 ^ 128 * Y3 + 2 ^ 192 * Y4 + 2 ^ 256 * Y5
      + 2 ^ 320 * Y6 + 2 ^ 384 * Y7) + (D * 2 ^ 128 + D * 2 ^ 96 + D)
    = L1 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 + 2 ^ 320 * c5
      + 2 ^ 384 * c6 + 2 ^ 448 * c7 + D * 2 ^ 384 + D * 2 ^ 32 := by
    omega
  have hp : D * p384 + (D * 2 ^ 128 + D * 2 ^ 96 + D) = D * 2 ^ 384 + D * 2 ^ 32 := by
    have h1 : p384 + 2 ^ 128 + 2 ^ 96 + 1 = 2 ^ 384 + 2 ^ 32 := rfl
    calc D * p384 + (D * 2 ^ 128 + D * 2 ^ 96 + D) = D * (p384 + 2 ^ 128 + 2 ^ 96 + 1) := by
          ring
      _ = D * 2 ^ 384 + D * 2 ^ 32 := by rw [h1, Nat.mul_add]
  omega

/-! ## Limb windows -/

/-- The value of the seven registers `a0, …, a6`, little-endian. -/
def v7 (R : String → BitVec 64) (a0 a1 a2 a3 a4 a5 a6 : String) : Nat :=
  (R a0).toNat + 2 ^ 64 * (R a1).toNat + 2 ^ 128 * (R a2).toNat + 2 ^ 192 * (R a3).toNat
    + 2 ^ 256 * (R a4).toNat + 2 ^ 320 * (R a5).toNat + 2 ^ 384 * (R a6).toNat

/-- The value of the eight registers `a0, …, a7`, little-endian. -/
def v8 (R : String → BitVec 64) (a0 a1 a2 a3 a4 a5 a6 a7 : String) : Nat :=
  v7 R a0 a1 a2 a3 a4 a5 a6 + 2 ^ 448 * (R a7).toNat

/-- The value of the six memory words at `[b + 0], …, [b + 40]`, little-endian. -/
def mem6 (M : JMem 64) (b : String) : Nat :=
  (M b 0).toNat + 2 ^ 64 * (M b 8).toNat + 2 ^ 128 * (M b 16).toNat + 2 ^ 192 * (M b 24).toNat
    + 2 ^ 256 * (M b 32).toNat + 2 ^ 320 * (M b 40).toNat

/-- The six partial products of the word `(M "%rcx" off)` with the words of `x` at `%rsi`,
    each at its weight. -/
def rowProd (M : JMem 64) (off : Int) : Nat :=
  (M "%rcx" off).toNat * (M "%rsi" 0).toNat
    + 2 ^ 64 * ((M "%rcx" off).toNat * (M "%rsi" 8).toNat)
    + 2 ^ 128 * ((M "%rcx" off).toNat * (M "%rsi" 16).toNat)
    + 2 ^ 192 * ((M "%rcx" off).toNat * (M "%rsi" 24).toNat)
    + 2 ^ 256 * ((M "%rcx" off).toNat * (M "%rsi" 32).toNat)
    + 2 ^ 320 * ((M "%rcx" off).toNat * (M "%rsi" 40).toNat)

theorem rowProd_eq (M : JMem 64) (off : Int) :
    rowProd M off = (M "%rcx" off).toNat * mem6 M "%rsi" := by
  simp only [rowProd, mem6]; ring

/-- The specification of a multiply row over the window `a0, …, a7` reading `y` at
    `[%rcx + off]`: the eight-register window afterwards holds the seven-register window
    before plus the product of that word of `y` with `x`, when the top register of the
    seven-register window is at most one. -/
def RowSpec (seg : List (JInstr 64)) (a0 a1 a2 a3 a4 a5 a6 a7 : String) (off : Int) : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → (R a6).toNat ≤ 1 →
    Reach (fun R' M' => M' = M ∧
      v8 R' a0 a1 a2 a3 a4 a5 a6 a7 = v7 R a0 a1 a2 a3 a4 a5 a6 + rowProd M off)
      (runBlock s seg)

/-- The symbolic run of a multiply row, closed by `row_arith`. -/
macro "row_tac" seg:ident : tactic => `(tactic| (
  intro R cf of zf M s hs h6
  simp only [$seg:ident]
  refine run_loadMem _ _ _ hs ?_; intro t0 hs0
  refine run_xor_self _ hs0 ?_; intro z1 t1 hs1
  refine run_mulxMem _ _ _ _ _ hs1 ?_; intro H0 L0 m0 t2 hs2
  refine run_adcx _ _ hs2 ?_; intro A0 c0 e0 bc0 t3 hs3
  refine run_adox _ _ hs3 ?_; intro B1 o1 f0 bo1 t4 hs4
  refine run_mulxMem _ _ _ _ _ hs4 ?_; intro H1 L1 m1 t5 hs5
  refine run_adcx _ _ hs5 ?_; intro A1 c1 e1 bc1 t6 hs6
  refine run_adox _ _ hs6 ?_; intro B2 o2 f1 bo2 t7 hs7
  refine run_mulxMem _ _ _ _ _ hs7 ?_; intro H2 L2 m2 t8 hs8
  refine run_adcx _ _ hs8 ?_; intro A2 c2 e2 bc2 t9 hs9
  refine run_adox _ _ hs9 ?_; intro B3 o3 f2 bo3 t10 hs10
  refine run_mulxMem _ _ _ _ _ hs10 ?_; intro H3 L3 m3 t11 hs11
  refine run_adcx _ _ hs11 ?_; intro A3 c3 e3 bc3 t12 hs12
  refine run_adox _ _ hs12 ?_; intro B4 o4 f3 bo4 t13 hs13
  refine run_mulxMem _ _ _ _ _ hs13 ?_; intro H4 L4 m4 t14 hs14
  refine run_adcx _ _ hs14 ?_; intro A4 c4 e4 bc4 t15 hs15
  refine run_adox _ _ hs15 ?_; intro B5 o5 f4 bo5 t16 hs16
  refine run_adox _ _ hs16 ?_; intro B6 o6 f5 bo6 t17 hs17
  refine run_mulxMem _ _ _ _ _ hs17 ?_; intro H5 L5 m5 t18 hs18
  refine run_adc _ _ hs18 ?_; intro A5 c5 p5 z5 e5 bc5 hz5 t19 hs19
  refine run_adc _ _ hs19 ?_; intro A6 c6 p6 z6 e6 bc6 hz6 t20 hs20
  refine run_adc _ _ hs20 ?_; intro A7 c7 p7 z7 e7 bc7 hz7 t21 hs21
  refine reach_nil hs21 ⟨rfl, ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, cb_false, BitVec.toNat_zero] at m0 m1 m2 m3 m4 m5 e0 e1 e2 e3 e4 e5 e6 e7 f0 f1 f2 f3 f4 f5
  simp only [v7, v8, rowProd, upd, ↓reduceIte, String.reduceEq]
  exact row_arith _ _ _ _ _ _ _ h6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m1 m2 m3 m4 m5
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bc6 bo5
    e0 f0 e1 f1 e2 f2 e3 f3 e4 f4 f5 e5 e6 e7))

theorem seg04_row : RowSpec s2nMontmulP384Seg04 "%r9" "%r10" "%r11" "%r12" "%r13" "%r14"
    "%r15" "%r8" 8 := by
  row_tac s2nMontmulP384Seg04

theorem seg06_row : RowSpec s2nMontmulP384Seg06 "%r10" "%r11" "%r12" "%r13" "%r14" "%r15"
    "%r8" "%r9" 16 := by
  row_tac s2nMontmulP384Seg06

theorem seg08_row : RowSpec s2nMontmulP384Seg08 "%r11" "%r12" "%r13" "%r14" "%r15" "%r8"
    "%r9" "%r10" 24 := by
  row_tac s2nMontmulP384Seg08

theorem seg10_row : RowSpec s2nMontmulP384Seg10 "%r12" "%r13" "%r14" "%r15" "%r8" "%r9"
    "%r10" "%r11" 32 := by
  row_tac s2nMontmulP384Seg10

theorem seg12_row : RowSpec s2nMontmulP384Seg12 "%r13" "%r14" "%r15" "%r8" "%r9" "%r10"
    "%r11" "%r12" 40 := by
  row_tac s2nMontmulP384Seg12

/-! ## The first row -/

/-- The carry equations of the first multiply row: one `CF` chain adds the high words to the
    low words of the next product; the carry out of the top limb is zero because the
    product is below `2^448`. -/
theorem row0_arith (p0 p1 p2 p3 p4 p5 h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 : Nat)
    (m0 : h0 * 2 ^ 64 + l0 = p0) (m1 : h1 * 2 ^ 64 + l1 = p1) (m2 : h2 * 2 ^ 64 + l2 = p2)
    (m3 : h3 * 2 ^ 64 + l3 = p3) (m4 : h4 * 2 ^ 64 + l4 = p4) (m5 : h5 * 2 ^ 64 + l5 = p5)
    (hP : p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4 + 2 ^ 320 * p5
      < 2 ^ 448)
    (A1 A2 A3 A4 A5 A6 c1 c2 c3 c4 c5 c6 : Nat) (_hA6 : A6 < 2 ^ 64)
    (e1 : A1 + 2 ^ 64 * c1 = h0 + l1)
    (e2 : A2 + 2 ^ 64 * c2 = h1 + l2 + c1)
    (e3 : A3 + 2 ^ 64 * c3 = h2 + l3 + c2)
    (e4 : A4 + 2 ^ 64 * c4 = h3 + l4 + c3)
    (e5 : A5 + 2 ^ 64 * c5 = h4 + l5 + c4)
    (e6 : A6 + 2 ^ 64 * c6 = h5 + 0 + c5) :
    l0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3 + 2 ^ 256 * A4 + 2 ^ 320 * A5
      + 2 ^ 384 * A6 + 2 ^ 448 * 0
    = p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4 + 2 ^ 320 * p5 := by
  have key : l0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3 + 2 ^ 256 * A4 + 2 ^ 320 * A5
      + 2 ^ 384 * A6 + 2 ^ 448 * c6
    = p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4 + 2 ^ 320 * p5 := by
    clear hP _hA6
    omega
  have hc6 : c6 = 0 := by
    clear * - key hP
    omega
  subst hc6
  exact key

/-- The specification of the first multiply row: the window `%r8, …, %r15` afterwards holds
    the product of the word of `y` at `[%rcx + 0]` with `x`. -/
def Row0Spec (seg : List (JInstr 64)) : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s →
    Reach (fun R' M' => M' = M ∧
      v8 R' "%r8" "%r9" "%r10" "%r11" "%r12" "%r13" "%r14" "%r15" = rowProd M 0)
      (runBlock s seg)

theorem rowProd_lt (M : JMem 64) (off : Int) : rowProd M off < 2 ^ 448 := by
  rw [rowProd_eq]
  have h1 := (M "%rcx" off).isLt
  have h2 : mem6 M "%rsi" < 2 ^ 384 := by
    simp only [mem6]
    have := (M "%rsi" 0).isLt; have := (M "%rsi" 8).isLt; have := (M "%rsi" 16).isLt
    have := (M "%rsi" 24).isLt; have := (M "%rsi" 32).isLt; have := (M "%rsi" 40).isLt
    omega
  calc _ < 2 ^ 64 * 2 ^ 384 := Nat.mul_lt_mul'' h1 h2
    _ = 2 ^ 448 := (Nat.pow_add 2 64 384).symm

theorem seg02_row0 : Row0Spec s2nMontmulP384Seg02 := by
  intro R cf of zf M s hs
  have hP := rowProd_lt M 0
  simp only [s2nMontmulP384Seg02]
  refine run_loadMem _ _ _ hs ?_; intro t0 hs0
  refine run_xor_self _ hs0 ?_; intro z1 t1 hs1
  refine run_mulxMem _ _ _ _ _ hs1 ?_; intro H0 L0 m0 t2 hs2
  refine run_mulxMem _ _ _ _ _ hs2 ?_; intro H1 L1 m1 t3 hs3
  refine run_add _ _ hs3 ?_; intro A1 c1 p1 z1 e1 bc1 t4 hs4
  refine run_mulxMem _ _ _ _ _ hs4 ?_; intro H2 L2 m2 t5 hs5
  refine run_adc _ _ hs5 ?_; intro A2 c2 p2 z2 e2 bc2 hz2 t6 hs6
  refine run_mulxMem _ _ _ _ _ hs6 ?_; intro H3 L3 m3 t7 hs7
  refine run_adc _ _ hs7 ?_; intro A3 c3 p3 z3 e3 bc3 hz3 t8 hs8
  refine run_mulxMem _ _ _ _ _ hs8 ?_; intro H4 L4 m4 t9 hs9
  refine run_adc _ _ hs9 ?_; intro A4 c4 p4 z4 e4 bc4 hz4 t10 hs10
  refine run_mulxMem _ _ _ _ _ hs10 ?_; intro H5 L5 m5 t11 hs11
  refine run_adc _ _ hs11 ?_; intro A5 c5 p5 z5 e5 bc5 hz5 t12 hs12
  refine run_adc _ _ hs12 ?_; intro A6 c6 p6 z6 e6 bc6 hz6 t13 hs13
  refine reach_nil hs13 ⟨rfl, ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq] at m0 m1 m2 m3 m4 m5 e1 e2 e3 e4 e5 e6
  simp only [rowProd] at hP
  simp only [v7, v8, rowProd, upd, ↓reduceIte, String.reduceEq]
  exact row0_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m1 m2 m3 m4 m5 hP
    _ _ _ _ _ _ _ _ _ _ _ _ A6.isLt e1 e2 e3 e4 e5 e6

/-! ## The Montgomery reduction rounds -/

/-- The specification of a reduction round over the window `c0, …, c7`: with
    `d = c0 · (2^32 + 1) mod 2^64`, the seven registers `c1, …, c7` afterwards hold
    `(⟦c0 … c7⟧ + d · p384) / 2^64`, when the top register is at most one. -/
def RedcSpec (seg : List (JInstr 64)) (c0 c1 c2 c3 c4 c5 c6 c7 : String) : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → (R c7).toNat ≤ 1 →
    Reach (fun R' M' => M' = M ∧
      2 ^ 64 * v7 R' c1 c2 c3 c4 c5 c6 c7
        = v8 R c0 c1 c2 c3 c4 c5 c6 c7 + (R c0).toNat * 4294967297 % 2 ^ 64 * p384)
      (runBlock s seg)

/-- The symbolic run of a reduction round, closed by `redc_arith`. -/
macro "redc_tac" seg:ident : tactic => `(tactic| (
  intro R cf of zf M s hs h7
  simp only [$seg:ident]
  refine run_mov _ _ hs ?_; intro t0 hs0
  refine run_shl32 _ hs0 ?_; intro S k q1 q2 q3 eS t1 hs1
  refine run_add _ _ hs1 ?_; intro D ca q4 q5 eD bca t2 hs2
  refine run_xor_self _ hs2 ?_; intro z3 t3 hs3
  refine run_mov _ _ hs3 ?_; intro t4 hs4
  refine run_mulx _ _ _ _ hs4 ?_; intro H1 L1 m1 t5 hs5
  refine run_mov _ _ hs5 ?_; intro t6 hs6
  refine run_mulx _ _ _ _ hs6 ?_; intro H2 L2 m2 t7 hs7
  refine run_adc _ _ hs7 ?_; intro X1 d1 q6 q7 e9 bd1 hz9 t8 hs8
  refine run_adc _ _ hs8 ?_; intro X2 d2 q8 q9 e10 bd2 hz10 t9 hs9
  refine run_adc _ _ hs9 ?_; intro X3 d3 q10 q11 e11 bd3 hz11 t10 hs10
  refine run_sub _ _ hs10 ?_; intro Y1 b1 q12 q13 e12 bb1 t11 hs11
  refine run_sbb _ _ hs11 ?_; intro Y2 b2 q14 q15 e13 bb2 t12 hs12
  refine run_sbb _ _ hs12 ?_; intro Y3 b3 q16 q17 e14 bb3 t13 hs13
  refine run_sbb _ _ hs13 ?_; intro Y4 b4 q18 q19 e15 bb4 t14 hs14
  refine run_sbb _ _ hs14 ?_; intro Y5 b5 q20 q21 e16 bb5 t15 hs15
  refine run_sbb _ _ hs15 ?_; intro Z b6 q22 q23 e17 bb6 t16 hs16
  refine run_add _ _ hs16 ?_; intro Y6 e1 q24 q25 e18 be1 t17 hs17
  refine run_adc _ _ hs17 ?_; intro Y7 e2 q26 q27 e19 be2 hz19 t18 hs18
  refine reach_nil hs18 ⟨rfl, ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, cb_false, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.zero_mod] at eS eD m1 m2 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19
  simp only [v7, v8, upd, ↓reduceIte, String.reduceEq]
  have hr := redc_arith _ _ _ _ _ _ _ _ (BitVec.isLt _) h7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ S.isLt D.isLt L1.isLt H1.isLt L2.isLt H2.isLt X1.isLt X2.isLt
    X3.isLt Y1.isLt Y2.isLt Y3.isLt Y4.isLt Y5.isLt Y6.isLt Y7.isLt Z.isLt (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) bd1 bd2 bb1 bb2 bb3 bb4
    bb5 be1 eS eD m1 m2 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19
  rw [← hr.1]
  exact hr.2))

theorem seg03_redc : RedcSpec s2nMontmulP384Seg03 "%r8" "%r9" "%r10" "%r11" "%r12" "%r13"
    "%r14" "%r15" := by
  redc_tac s2nMontmulP384Seg03

theorem seg05_redc : RedcSpec s2nMontmulP384Seg05 "%r9" "%r10" "%r11" "%r12" "%r13" "%r14"
    "%r15" "%r8" := by
  redc_tac s2nMontmulP384Seg05

theorem seg07_redc : RedcSpec s2nMontmulP384Seg07 "%r10" "%r11" "%r12" "%r13" "%r14" "%r15"
    "%r8" "%r9" := by
  redc_tac s2nMontmulP384Seg07

theorem seg09_redc : RedcSpec s2nMontmulP384Seg09 "%r11" "%r12" "%r13" "%r14" "%r15" "%r8"
    "%r9" "%r10" := by
  redc_tac s2nMontmulP384Seg09

theorem seg11_redc : RedcSpec s2nMontmulP384Seg11 "%r12" "%r13" "%r14" "%r15" "%r8" "%r9"
    "%r10" "%r11" := by
  redc_tac s2nMontmulP384Seg11

theorem seg13_redc : RedcSpec s2nMontmulP384Seg13 "%r13" "%r14" "%r15" "%r8" "%r9" "%r10"
    "%r11" "%r12" := by
  redc_tac s2nMontmulP384Seg13

/-! ## The entry move and the final conditional subtraction -/

/-- The entry segment `movq %rdx, %rcx` leaves the memory unchanged. -/
theorem seg01_mem (R : String → BitVec 64) (cf of zf : Bool) (M : JMem 64) (s : JState 64)
    (hs : Desc R cf of zf M s) :
    Reach (fun _ M' => M' = M) (runBlock s s2nMontmulP384Seg01) := by
  exact run_mov _ _ hs fun _ h => reach_nil h rfl

/-- The final conditional subtraction on a value `A < 2^385` held in seven limbs: with
    `S = (A mod 2^384) + (2^384 - p384)`, the result is `S mod 2^384` when the top limb of `A`
    or the carry out of `S` is set, and `A mod 2^384` otherwise. -/
def finalF (A : Nat) : Nat :=
  if A / 2 ^ 384 + (A % 2 ^ 384 + (2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1)) / 2 ^ 384 = 0 then
    A % 2 ^ 384
  else (A % 2 ^ 384 + (2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1)) % 2 ^ 384

/-- The carry equations of the final segments: the chain `e0 … e5` adds
    `2^384 - p384` to the low six limbs, `e6` adds the carry to the top limb, and the
    conditional moves select the sum when the resulting top word is nonzero. -/
theorem final_arith (a0 a1 a2 a3 a4 a5 a6 : Nat) (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (ha4 : a4 < 2 ^ 64) (ha5 : a5 < 2 ^ 64)
    (ha6 : a6 ≤ 1)
    (F0 F1 F2 F3 F4 F5 F6 g0 g1 g2 g3 g4 g5 g6 : Nat)
    (hF0 : F0 < 2 ^ 64) (hF1 : F1 < 2 ^ 64) (hF2 : F2 < 2 ^ 64) (hF3 : F3 < 2 ^ 64)
    (hF4 : F4 < 2 ^ 64) (hF5 : F5 < 2 ^ 64) (_hF6 : F6 < 2 ^ 64)
    (_bg0 : g0 ≤ 1) (_bg1 : g1 ≤ 1) (_bg2 : g2 ≤ 1) (_bg3 : g3 ≤ 1) (_bg4 : g4 ≤ 1)
    (bg5 : g5 ≤ 1)
    (e0 : F0 + 2 ^ 64 * g0 = 18446744069414584321 + a0)
    (e1 : F1 + 2 ^ 64 * g1 = 4294967295 + a1 + g0)
    (e2 : F2 + 2 ^ 64 * g2 = 1 + a2 + g1)
    (e3 : F3 + 2 ^ 64 * g3 = 0 + a3 + g2)
    (e4 : F4 + 2 ^ 64 * g4 = 0 + a4 + g3)
    (e5 : F5 + 2 ^ 64 * g5 = 0 + a5 + g4)
    (e6 : F6 + 2 ^ 64 * g6 = a6 + 0 + g5) :
    (if F6 = 0 then a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5
      else F0 + 2 ^ 64 * F1 + 2 ^ 128 * F2 + 2 ^ 192 * F3 + 2 ^ 256 * F4 + 2 ^ 320 * F5)
    = finalF (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5
        + 2 ^ 384 * a6) := by
  have hF6v : F6 = a6 + g5 := by clear * - e6 ha6 bg5; omega
  have hL : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5
      + 2 ^ 384 * a6) % 2 ^ 384
      = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5 := by
    clear * - ha0 ha1 ha2 ha3 ha4 ha5; omega
  have hH : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5
      + 2 ^ 384 * a6) / 2 ^ 384 = a6 := by
    clear * - ha0 ha1 ha2 ha3 ha4 ha5; omega
  have hS : a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4 + 2 ^ 320 * a5
      + (2 ^ 128 + 2 ^ 96 - 2 ^ 32 + 1)
      = F0 + 2 ^ 64 * F1 + 2 ^ 128 * F2 + 2 ^ 192 * F3 + 2 ^ 256 * F4 + 2 ^ 320 * F5
        + 2 ^ 384 * g5 := by
    clear * - e0 e1 e2 e3 e4 e5; omega
  have hSd : (F0 + 2 ^ 64 * F1 + 2 ^ 128 * F2 + 2 ^ 192 * F3 + 2 ^ 256 * F4 + 2 ^ 320 * F5
        + 2 ^ 384 * g5) / 2 ^ 384 = g5 := by
    clear * - hF0 hF1 hF2 hF3 hF4 hF5; omega
  have hSm : (F0 + 2 ^ 64 * F1 + 2 ^ 128 * F2 + 2 ^ 192 * F3 + 2 ^ 256 * F4 + 2 ^ 320 * F5
        + 2 ^ 384 * g5) % 2 ^ 384
      = F0 + 2 ^ 64 * F1 + 2 ^ 128 * F2 + 2 ^ 192 * F3 + 2 ^ 256 * F4 + 2 ^ 320 * F5 := by
    clear * - hF0 hF1 hF2 hF3 hF4 hF5; omega
  unfold finalF
  rw [hL, hH, hS, hSd, hSm, hF6v]

/-- The specification of the last four segments: they store `finalF` of the seven-limb
    window `%r14, %r15, %r8, …, %r12` at `[%rdi + 0], …, [%rdi + 40]` and write no other
    memory, when the top limb is at most one. -/
def FinalSpec : Prop :=
  ∀ R cf of zf M s, Desc R cf of zf M s → (R "%r12").toNat ≤ 1 →
    Reach (fun _ M' => (∀ b o, b ≠ "%rdi" → M' b o = M b o) ∧
      mem6 M' "%rdi" = finalF (v7 R "%r14" "%r15" "%r8" "%r9" "%r10" "%r11" "%r12"))
      (runBlock s (s2nMontmulP384Seg14 ++ s2nMontmulP384Seg15 ++ s2nMontmulP384Seg16 ++
        s2nMontmulP384Seg17))

theorem final_spec : FinalSpec := by
  intro R cf of zf M s hs h6
  simp only [s2nMontmulP384Seg14, s2nMontmulP384Seg15, s2nMontmulP384Seg16,
    s2nMontmulP384Seg17, List.cons_append, List.nil_append]
  refine run_xor_self _ hs ?_; intro z0 t0 hs0
  refine run_xor_self _ hs0 ?_; intro z1 t1 hs1
  refine run_xor_self _ hs1 ?_; intro z2 t2 hs2
  refine run_mov _ _ hs2 ?_; intro t3 hs3
  refine run_add _ _ hs3 ?_; intro F0 g0 q0 q1 e0 bg0 t4 hs4
  refine run_mov _ _ hs4 ?_; intro t5 hs5
  refine run_adc _ _ hs5 ?_; intro F1 g1 q2 q3 e1 bg1 hz1 t6 hs6
  refine run_mov _ _ hs6 ?_; intro t7 hs7
  refine run_adc _ _ hs7 ?_; intro F2 g2 q4 q5 e2 bg2 hz2 t8 hs8
  refine run_adc _ _ hs8 ?_; intro F3 g3 q6 q7 e3 bg3 hz3 t9 hs9
  refine run_adc _ _ hs9 ?_; intro F4 g4 q8 q9 e4 bg4 hz4 t10 hs10
  refine run_adc _ _ hs10 ?_; intro F5 g5 q10 q11 e5 bg5 hz5 t11 hs11
  refine run_adc _ _ hs11 ?_; intro F6 g6 q12 z6 e6 bg6 hz6 t12 hs12
  refine run_cmovne _ _ hs12 ?_; intro t13 hs13
  refine run_cmovne _ _ hs13 ?_; intro t14 hs14
  refine run_cmovne _ _ hs14 ?_; intro t15 hs15
  refine run_cmovne _ _ hs15 ?_; intro t16 hs16
  refine run_cmovne _ _ hs16 ?_; intro t17 hs17
  refine run_cmovne _ _ hs17 ?_; intro t18 hs18
  refine run_storeMem _ _ _ hs18 ?_; intro t19 hs19
  refine run_storeMem _ _ _ hs19 ?_; intro t20 hs20
  refine run_storeMem _ _ _ hs20 ?_; intro t21 hs21
  refine run_storeMem _ _ _ hs21 ?_; intro t22 hs22
  refine run_storeMem _ _ _ hs22 ?_; intro t23 hs23
  refine run_storeMem _ _ _ hs23 ?_; intro t24 hs24
  refine reach_nil hs24 ⟨fun b o hb => by simp [hb], ?_⟩
  simp only [upd, opv, ↓reduceIte, String.reduceEq, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.zero_mod] at e0 e1 e2 e3 e4 e5 e6
  subst hz6
  simp only [mem6, v7, upd, ↓reduceIte, String.reduceEq]
  have key := final_arith _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) h6 _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0.isLt F1.isLt F2.isLt F3.isLt F4.isLt F5.isLt F6.isLt bg0 bg1 bg2 bg3 bg4 bg5
    e0 e1 e2 e3 e4 e5 e6
  rw [← key]
  by_cases hF : F6.toNat = 0 <;> simp [hF]

/-! ## The abstract algorithm -/

/-- Word `j` of `y`, little-endian. -/
def ydig (y j : Nat) : Nat := y / 2 ^ (64 * j) % 2 ^ 64

/-- One Montgomery reduction round with the P-384 multiplier `n' = 2^32 + 1`. -/
def redcF (T : Nat) : Nat := (T + T % 2 ^ 64 * 4294967297 % 2 ^ 64 * p384) / 2 ^ 64

/-- The abstract Montgomery multiplication the block refines: six rounds, each adding
    one word of `y` times `x` and reducing by one word, then `finalF`. -/
def montAbs (x y : Nat) : Nat :=
  finalF (redcF (redcF (redcF (redcF (redcF (redcF (ydig y 0 * x)
    + ydig y 1 * x) + ydig y 2 * x) + ydig y 3 * x) + ydig y 4 * x) + ydig y 5 * x))

/-- The abstract state of the block: the stage reached (the number of segments run, with
    stage `17` after the last four), the inputs `x`, `y` and the accumulator. -/
structure AMont where
  /-- Segments run. -/
  stage : Nat
  /-- The value of `x`. -/
  x : Nat
  /-- The value of `y`. -/
  y : Nat
  /-- The accumulator. -/
  acc : Nat

/-- Where the accumulator lives after each stage: an eight-register window after a multiply
    row, a seven-register window after a reduction round, and the output memory after the
    last segment. -/
def StageRel : Nat → JState 64 → Nat → Prop
  | 2, st, v => v8 st.regs "%r8" "%r9" "%r10" "%r11" "%r12" "%r13" "%r14" "%r15" = v
  | 3, st, v => v7 st.regs "%r9" "%r10" "%r11" "%r12" "%r13" "%r14" "%r15" = v
  | 4, st, v => v8 st.regs "%r9" "%r10" "%r11" "%r12" "%r13" "%r14" "%r15" "%r8" = v
  | 5, st, v => v7 st.regs "%r10" "%r11" "%r12" "%r13" "%r14" "%r15" "%r8" = v
  | 6, st, v => v8 st.regs "%r10" "%r11" "%r12" "%r13" "%r14" "%r15" "%r8" "%r9" = v
  | 7, st, v => v7 st.regs "%r11" "%r12" "%r13" "%r14" "%r15" "%r8" "%r9" = v
  | 8, st, v => v8 st.regs "%r11" "%r12" "%r13" "%r14" "%r15" "%r8" "%r9" "%r10" = v
  | 9, st, v => v7 st.regs "%r12" "%r13" "%r14" "%r15" "%r8" "%r9" "%r10" = v
  | 10, st, v => v8 st.regs "%r12" "%r13" "%r14" "%r15" "%r8" "%r9" "%r10" "%r11" = v
  | 11, st, v => v7 st.regs "%r13" "%r14" "%r15" "%r8" "%r9" "%r10" "%r11" = v
  | 12, st, v => v8 st.regs "%r13" "%r14" "%r15" "%r8" "%r9" "%r10" "%r11" "%r12" = v
  | 13, st, v => v7 st.regs "%r14" "%r15" "%r8" "%r9" "%r10" "%r11" "%r12" = v
  | 17, st, v => mem6 st.mem "%rdi" = v
  | _, _, _ => True

/-- The state relation: `x` and `y` are the six words at `%rsi` and `%rcx`, and the
    accumulator is where `StageRel` places it. -/
def SRm (st : JState 64) (a : AMont) : Prop :=
  mem6 st.mem "%rsi" = a.x ∧ mem6 st.mem "%rcx" = a.y ∧ StageRel a.stage st a.acc

theorem desc_self (st : JState 64) :
    Desc st.regs (st.flagB (·.cf)) (st.flagB (·.of)) (st.flagB (·.zf)) st.mem st :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem p384_lt : p384 < 2 ^ 384 := by decide

theorem top7_le (R : String → BitVec 64) (a0 a1 a2 a3 a4 a5 a6 : String) (B : Nat)
    (h : v7 R a0 a1 a2 a3 a4 a5 a6 < B) (hB : B ≤ 2 ^ 385) : (R a6).toNat ≤ 1 := by
  simp only [v7] at h
  omega

theorem top8_le (R : String → BitVec 64) (a0 a1 a2 a3 a4 a5 a6 a7 : String) (B : Nat)
    (h : v8 R a0 a1 a2 a3 a4 a5 a6 a7 < B) (hB : B ≤ 2 ^ 449) : (R a7).toNat ≤ 1 := by
  simp only [v8, v7] at h
  omega

/-- A multiply row refines the abstract row step. -/
theorem corresJ_row {seg : List (JInstr 64)} {a0 a1 a2 a3 a4 a5 a6 a7 : String} {off : Int}
    (hspec : RowSpec seg a0 a1 a2 a3 a4 a5 a6 a7 off) (k j : Nat)
    (hin : ∀ st v, StageRel k st v = (v7 st.regs a0 a1 a2 a3 a4 a5 a6 = v))
    (hout : ∀ st v, StageRel (k + 1) st v = (v8 st.regs a0 a1 a2 a3 a4 a5 a6 a7 = v))
    (hdig : ∀ M : JMem 64, (M "%rcx" off).toNat = ydig (mem6 M "%rcx") j) :
    CorresJ SRm (fun a => a.stage = k ∧ a.x < 2 ^ 384 ∧ a.acc < 2 ^ 384 + p384)
      (fun a => { a with stage := k + 1, acc := a.acc + ydig a.y j * a.x }) seg := by
  intro st a ⟨hx, hy, hrel⟩ ⟨hk, _, hacc⟩
  rw [hk, hin] at hrel
  have h6 := top7_le _ _ _ _ _ _ _ _ _ (hrel ▸ hacc) (by have := p384_lt; omega)
  obtain ⟨R', _, _, _, M', hs', hM, hv⟩ := hspec _ _ _ _ _ st (desc_self st) h6
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show StageRel (k + 1) _ (a.acc + ydig a.y j * a.x)
  rw [hout, hs'.regs, hv, hrel, rowProd_eq, hdig, hx, hy, Nat.mul_comm (ydig _ _)]

/-- A reduction round refines `redcF`. -/
theorem corresJ_redc {seg : List (JInstr 64)} {c0 c1 c2 c3 c4 c5 c6 c7 : String}
    (hspec : RedcSpec seg c0 c1 c2 c3 c4 c5 c6 c7) (k : Nat)
    (hin : ∀ st v, StageRel k st v = (v8 st.regs c0 c1 c2 c3 c4 c5 c6 c7 = v))
    (hout : ∀ st v, StageRel (k + 1) st v = (v7 st.regs c1 c2 c3 c4 c5 c6 c7 = v)) :
    CorresJ SRm (fun a => a.stage = k ∧ a.x < 2 ^ 384 ∧ a.acc < 2 ^ 448 + p384)
      (fun a => { a with stage := k + 1, acc := redcF a.acc }) seg := by
  intro st a ⟨hx, hy, hrel⟩ ⟨hk, _, hacc⟩
  rw [hk, hin] at hrel
  have h7 := top8_le _ _ _ _ _ _ _ _ _ _ (hrel ▸ hacc) (by have := p384_lt; omega)
  obtain ⟨R', _, _, _, M', hs', hM, hv⟩ := hspec _ _ _ _ _ st (desc_self st) h7
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show StageRel (k + 1) _ (redcF a.acc)
  rw [hout, hs'.regs]
  have hc0 : (st.regs c0).toNat = v8 st.regs c0 c1 c2 c3 c4 c5 c6 c7 % 2 ^ 64 := by
    simp only [v8, v7]
    omega
  rw [redcF, ← hrel, ← hc0, ← hv]
  simp

/-- The entry move refines the stage step. -/
theorem corresJ_seg01 :
    CorresJ SRm (fun a => a.stage = 0 ∧ a.x < 2 ^ 384) (fun a => { a with stage := 1 })
      s2nMontmulP384Seg01 := by
  intro st a ⟨hx, hy, _⟩ _
  obtain ⟨R', _, _, _, M', hs', hM⟩ := seg01_mem _ _ _ _ _ st (desc_self st)
  subst hM
  exact ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, trivial⟩

theorem digit0 (M : JMem 64) : (M "%rcx" 0).toNat = ydig (mem6 M "%rcx") 0 := by
  have := (M "%rcx" 0).isLt; have := (M "%rcx" 8).isLt; have := (M "%rcx" 16).isLt
  have := (M "%rcx" 24).isLt; have := (M "%rcx" 32).isLt; have := (M "%rcx" 40).isLt
  simp only [ydig, mem6]; omega

theorem digit1 (M : JMem 64) : (M "%rcx" 8).toNat = ydig (mem6 M "%rcx") 1 := by
  have := (M "%rcx" 0).isLt; have := (M "%rcx" 8).isLt; have := (M "%rcx" 16).isLt
  have := (M "%rcx" 24).isLt; have := (M "%rcx" 32).isLt; have := (M "%rcx" 40).isLt
  simp only [ydig, mem6]; omega

theorem digit2 (M : JMem 64) : (M "%rcx" 16).toNat = ydig (mem6 M "%rcx") 2 := by
  have := (M "%rcx" 0).isLt; have := (M "%rcx" 8).isLt; have := (M "%rcx" 16).isLt
  have := (M "%rcx" 24).isLt; have := (M "%rcx" 32).isLt; have := (M "%rcx" 40).isLt
  simp only [ydig, mem6]; omega

theorem digit3 (M : JMem 64) : (M "%rcx" 24).toNat = ydig (mem6 M "%rcx") 3 := by
  have := (M "%rcx" 0).isLt; have := (M "%rcx" 8).isLt; have := (M "%rcx" 16).isLt
  have := (M "%rcx" 24).isLt; have := (M "%rcx" 32).isLt; have := (M "%rcx" 40).isLt
  simp only [ydig, mem6]; omega

theorem digit4 (M : JMem 64) : (M "%rcx" 32).toNat = ydig (mem6 M "%rcx") 4 := by
  have := (M "%rcx" 0).isLt; have := (M "%rcx" 8).isLt; have := (M "%rcx" 16).isLt
  have := (M "%rcx" 24).isLt; have := (M "%rcx" 32).isLt; have := (M "%rcx" 40).isLt
  simp only [ydig, mem6]; omega

theorem digit5 (M : JMem 64) : (M "%rcx" 40).toNat = ydig (mem6 M "%rcx") 5 := by
  have := (M "%rcx" 0).isLt; have := (M "%rcx" 8).isLt; have := (M "%rcx" 16).isLt
  have := (M "%rcx" 24).isLt; have := (M "%rcx" 32).isLt; have := (M "%rcx" 40).isLt
  simp only [ydig, mem6]; omega

/-- The first multiply row refines its abstract step. -/
theorem corresJ_seg02 :
    CorresJ SRm (fun a => a.stage = 1 ∧ a.x < 2 ^ 384)
      (fun a => { a with stage := 2, acc := ydig a.y 0 * a.x }) s2nMontmulP384Seg02 := by
  intro st a ⟨hx, hy, _⟩ _
  obtain ⟨R', _, _, _, M', hs', hM, hv⟩ := seg02_row0 _ _ _ _ _ st (desc_self st)
  subst hM
  refine ⟨by rw [hs'.mem]; exact hx, by rw [hs'.mem]; exact hy, ?_⟩
  show v8 _ _ _ _ _ _ _ _ _ = ydig a.y 0 * a.x
  rw [hs'.regs, hv, rowProd_eq, digit0, hx, hy, Nat.mul_comm]

/-- The last four segments refine `finalF`. -/
theorem corresJ_final :
    CorresJ SRm (fun a => a.stage = 13 ∧ a.x < 2 ^ 384 ∧ a.acc < 2 ^ 384 + p384)
      (fun a => { a with stage := 17, acc := finalF a.acc })
      (s2nMontmulP384Seg14 ++ s2nMontmulP384Seg15 ++ s2nMontmulP384Seg16 ++
        s2nMontmulP384Seg17) := by
  intro st a ⟨hx, hy, hrel⟩ ⟨hk, _, hacc⟩
  rw [hk] at hrel
  change v7 st.regs _ _ _ _ _ _ _ = a.acc at hrel
  have h6 := top7_le _ _ _ _ _ _ _ _ _ (hrel ▸ hacc) (by have := p384_lt; omega)
  obtain ⟨R', _, _, _, M', hs', hfr, hv⟩ := final_spec _ _ _ _ _ st (desc_self st) h6
  have hsi : mem6 M' "%rsi" = mem6 st.mem "%rsi" := by
    simp only [mem6, hfr "%rsi" _ (by decide)]
  have hcx : mem6 M' "%rcx" = mem6 st.mem "%rcx" := by
    simp only [mem6, hfr "%rcx" _ (by decide)]
  refine ⟨by rw [hs'.mem, hsi]; exact hx, by rw [hs'.mem, hcx]; exact hy, ?_⟩
  show mem6 _ "%rdi" = finalF a.acc
  rw [hs'.mem, hv, hrel]

theorem row_bound (A x y j : Nat) (hA : A < 2 ^ 384 + p384) (hx : x < 2 ^ 384) :
    A + ydig y j * x < 2 ^ 448 + p384 := by
  have hd : ydig y j < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have : ydig y j * x ≤ (2 ^ 64 - 1) * (2 ^ 384 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * (2 ^ 384 - 1) + 2 ^ 384 ≤ 2 ^ 448 := by decide
  omega

theorem row0_bound (x y : Nat) (hx : x < 2 ^ 384) : ydig y 0 * x < 2 ^ 448 + p384 := by
  have := row_bound 0 x y 0 (by have := p384_lt; omega) hx
  omega

theorem redc_bound (T : Nat) (hT : T < 2 ^ 448 + p384) : redcF T < 2 ^ 384 + p384 := by
  unfold redcF p384 at *; omega

/-- **The block refines the abstract Montgomery multiplication.** From stage `0` with
    `x < 2^384`, running `s2nMontmulP384Block` under `runBlock` reaches stage `17`, where
    the six words at `%rdi` hold `montAbs x y`. Composed from the seventeen segment
    correspondences by `corresJ_append`. -/
theorem s2nMontmulP384_corresJ :
    CorresJ SRm (fun a => a.stage = 0 ∧ a.x < 2 ^ 384)
      (fun a => { stage := 17, x := a.x, y := a.y, acc := montAbs a.x a.y })
      s2nMontmulP384Block := by
  have c13 := corresJ_append SRm (corresJ_redc seg13_redc 12 (fun _ _ => rfl) (fun _ _ => rfl))
    corresJ_final (fun _ h => ⟨rfl, h.2.1, redc_bound _ h.2.2⟩)
  have c12 := corresJ_append SRm
    (corresJ_row seg12_row 11 5 (fun _ _ => rfl) (fun _ _ => rfl) digit5) c13
    (fun _ h => ⟨rfl, h.2.1, row_bound _ _ _ _ h.2.2 h.2.1⟩)
  have c11 := corresJ_append SRm (corresJ_redc seg11_redc 10 (fun _ _ => rfl) (fun _ _ => rfl))
    c12 (fun _ h => ⟨rfl, h.2.1, redc_bound _ h.2.2⟩)
  have c10 := corresJ_append SRm
    (corresJ_row seg10_row 9 4 (fun _ _ => rfl) (fun _ _ => rfl) digit4) c11
    (fun _ h => ⟨rfl, h.2.1, row_bound _ _ _ _ h.2.2 h.2.1⟩)
  have c09 := corresJ_append SRm (corresJ_redc seg09_redc 8 (fun _ _ => rfl) (fun _ _ => rfl))
    c10 (fun _ h => ⟨rfl, h.2.1, redc_bound _ h.2.2⟩)
  have c08 := corresJ_append SRm
    (corresJ_row seg08_row 7 3 (fun _ _ => rfl) (fun _ _ => rfl) digit3) c09
    (fun _ h => ⟨rfl, h.2.1, row_bound _ _ _ _ h.2.2 h.2.1⟩)
  have c07 := corresJ_append SRm (corresJ_redc seg07_redc 6 (fun _ _ => rfl) (fun _ _ => rfl))
    c08 (fun _ h => ⟨rfl, h.2.1, redc_bound _ h.2.2⟩)
  have c06 := corresJ_append SRm
    (corresJ_row seg06_row 5 2 (fun _ _ => rfl) (fun _ _ => rfl) digit2) c07
    (fun _ h => ⟨rfl, h.2.1, row_bound _ _ _ _ h.2.2 h.2.1⟩)
  have c05 := corresJ_append SRm (corresJ_redc seg05_redc 4 (fun _ _ => rfl) (fun _ _ => rfl))
    c06 (fun _ h => ⟨rfl, h.2.1, redc_bound _ h.2.2⟩)
  have c04 := corresJ_append SRm
    (corresJ_row seg04_row 3 1 (fun _ _ => rfl) (fun _ _ => rfl) digit1) c05
    (fun _ h => ⟨rfl, h.2.1, row_bound _ _ _ _ h.2.2 h.2.1⟩)
  have c03 := corresJ_append SRm (corresJ_redc seg03_redc 2 (fun _ _ => rfl) (fun _ _ => rfl))
    c04 (fun _ h => ⟨rfl, h.2.1, redc_bound _ h.2.2⟩)
  have c02 := corresJ_append SRm corresJ_seg02 c03
    (fun _ h => ⟨rfl, h.2, row0_bound _ _ h.2⟩)
  unfold s2nMontmulP384Block
  simpa only [List.append_assoc, montAbs] using
    corresJ_append SRm corresJ_seg01 c02 (fun _ h => ⟨rfl, h.2⟩)

/-! ## The abstract algorithm computes the Montgomery product -/

/-- A reduction round divides exactly: `redcF T · 2^64 = T + d · p384` with
    `d = (T mod 2^64) · (2^32 + 1) mod 2^64`, because `(2^32 + 1) · p384 ≡ -1 (mod 2^64)`. -/
theorem redcF_mul (T : Nat) :
    redcF T * 2 ^ 64 = T + T % 2 ^ 64 * 4294967297 % 2 ^ 64 * p384 := by
  unfold redcF p384; omega

/-- Six rounds of `A_{k+1} · B = A_k + y_k x + d_k p` telescope to
    `A_6 · B^6 = x · ⟦y⟧ + p · ⟦d⟧` in base `B`. -/
theorem chain6 {R : Type} [CommRing R] (B x p y0 y1 y2 y3 y4 y5 d0 d1 d2 d3 d4 d5
    A1 A2 A3 A4 A5 A6 : R)
    (h1 : A1 * B = y0 * x + d0 * p) (h2 : A2 * B = A1 + y1 * x + d1 * p)
    (h3 : A3 * B = A2 + y2 * x + d2 * p) (h4 : A4 * B = A3 + y3 * x + d3 * p)
    (h5 : A5 * B = A4 + y4 * x + d4 * p) (h6 : A6 * B = A5 + y5 * x + d5 * p) :
    A6 * B ^ 6 = x * (y0 + B * y1 + B ^ 2 * y2 + B ^ 3 * y3 + B ^ 4 * y4 + B ^ 5 * y5)
      + p * (d0 + B * d1 + B ^ 2 * d2 + B ^ 3 * d3 + B ^ 4 * d4 + B ^ 5 * d5) := by
  linear_combination B ^ 5 * h6 + B ^ 4 * h5 + B ^ 3 * h4 + B ^ 2 * h3 + B * h2 + h1

theorem digits_recompose (y : Nat) (hy : y < 2 ^ 384) :
    y = ydig y 0 + 2 ^ 64 * ydig y 1 + (2 ^ 64) ^ 2 * ydig y 2 + (2 ^ 64) ^ 3 * ydig y 3
      + (2 ^ 64) ^ 4 * ydig y 4 + (2 ^ 64) ^ 5 * ydig y 5 := by
  simp only [ydig]
  norm_num
  omega

theorem finalF_eq (A : Nat) (hA : A < 2 * p384) : finalF A = A % p384 := by
  unfold finalF p384 at *; split <;> omega

theorem p384_coprime_R : Nat.Coprime (2 ^ 384) p384 :=
  Nat.Coprime.pow_left 384 (by decide)

/-- **The abstract algorithm computes the Montgomery product.** For `y < 2^384` with
    `x · y ≤ 2^384 · p384`, `montAbs x y` is below `p384` and equals `x · y · (2^384)⁻¹` in
    `ZMod p384`. -/
theorem montAbs_spec (x y : Nat) (hy : y < 2 ^ 384)
    (hxy : x * y ≤ 2 ^ 384 * p384) :
    montAbs x y < p384 ∧
      ((montAbs x y : Nat) : ZMod p384)
        = (x : ZMod p384) * y * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ := by
  set A1 := redcF (ydig y 0 * x) with hA1
  set A2 := redcF (A1 + ydig y 1 * x) with hA2
  set A3 := redcF (A2 + ydig y 2 * x) with hA3
  set A4 := redcF (A3 + ydig y 3 * x) with hA4
  set A5 := redcF (A4 + ydig y 4 * x) with hA5
  set A6 := redcF (A5 + ydig y 5 * x) with hA6
  have hm : montAbs x y = finalF A6 := rfl
  have e1 := redcF_mul (ydig y 0 * x)
  have e2 := redcF_mul (A1 + ydig y 1 * x)
  have e3 := redcF_mul (A2 + ydig y 2 * x)
  have e4 := redcF_mul (A3 + ydig y 3 * x)
  have e5 := redcF_mul (A4 + ydig y 4 * x)
  have e6 := redcF_mul (A5 + ydig y 5 * x)
  rw [← hA1] at e1; rw [← hA2] at e2; rw [← hA3] at e3; rw [← hA4] at e4
  rw [← hA5] at e5; rw [← hA6] at e6
  set d0 := ydig y 0 * x % 2 ^ 64 * 4294967297 % 2 ^ 64
  set d1 := (A1 + ydig y 1 * x) % 2 ^ 64 * 4294967297 % 2 ^ 64
  set d2 := (A2 + ydig y 2 * x) % 2 ^ 64 * 4294967297 % 2 ^ 64
  set d3 := (A3 + ydig y 3 * x) % 2 ^ 64 * 4294967297 % 2 ^ 64
  set d4 := (A4 + ydig y 4 * x) % 2 ^ 64 * 4294967297 % 2 ^ 64
  set d5 := (A5 + ydig y 5 * x) % 2 ^ 64 * 4294967297 % 2 ^ 64
  have hd : ∀ n : Nat, n % 2 ^ 64 * 4294967297 % 2 ^ 64 < 2 ^ 64 :=
    fun n => Nat.mod_lt _ (by norm_num)
  have key := chain6 (R := ℤ) (2 ^ 64) x p384 (ydig y 0) (ydig y 1) (ydig y 2) (ydig y 3)
    (ydig y 4) (ydig y 5) d0 d1 d2 d3 d4 d5 A1 A2 A3 A4 A5 A6
    (by exact_mod_cast e1) (by exact_mod_cast e2) (by exact_mod_cast e3)
    (by exact_mod_cast e4) (by exact_mod_cast e5) (by exact_mod_cast e6)
  have hyr := digits_recompose y hy
  have keyN : A6 * 2 ^ 384 = x * y
      + p384 * (d0 + 2 ^ 64 * d1 + (2 ^ 64) ^ 2 * d2 + (2 ^ 64) ^ 3 * d3 + (2 ^ 64) ^ 4 * d4
        + (2 ^ 64) ^ 5 * d5) := by
    have h384 : (2 : ℤ) ^ 384 = (2 ^ 64) ^ 6 := by rw [← pow_mul]
    rw [hyr]
    exact_mod_cast h384 ▸ key
  have hD : d0 + 2 ^ 64 * d1 + (2 ^ 64) ^ 2 * d2 + (2 ^ 64) ^ 3 * d3 + (2 ^ 64) ^ 4 * d4
      + (2 ^ 64) ^ 5 * d5 < 2 ^ 384 := by
    have := hd (ydig y 0 * x); have := hd (A1 + ydig y 1 * x); have := hd (A2 + ydig y 2 * x)
    have := hd (A3 + ydig y 3 * x); have := hd (A4 + ydig y 4 * x)
    have := hd (A5 + ydig y 5 * x)
    norm_num
    omega
  have hA6lt : A6 < 2 * p384 := by
    have hp := p384_lt
    have hb : p384 * (d0 + 2 ^ 64 * d1 + (2 ^ 64) ^ 2 * d2 + (2 ^ 64) ^ 3 * d3
        + (2 ^ 64) ^ 4 * d4 + (2 ^ 64) ^ 5 * d5) ≤ p384 * (2 ^ 384 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have : A6 * 2 ^ 384 < 2 * p384 * 2 ^ 384 := by
      rw [keyN]
      have : p384 * (2 ^ 384 - 1) + 2 ^ 384 * p384 < 2 * p384 * 2 ^ 384 := by
        have hP : 0 < p384 := by decide
        have hQ : 0 < (2 : Nat) ^ 384 := by positivity
        generalize p384 = P at hP ⊢
        generalize (2 : Nat) ^ 384 = Q at hQ ⊢
        have h1 : P * (Q - 1) < P * Q := Nat.mul_lt_mul_of_pos_left (by omega) hP
        calc P * (Q - 1) + Q * P < P * Q + Q * P := by omega
          _ = 2 * P * Q := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  rw [hm, finalF_eq A6 hA6lt]
  refine ⟨Nat.mod_lt _ (by decide), ?_⟩
  rw [ZMod.natCast_mod]
  have hcast : (A6 : ZMod p384) * ((2 ^ 384 : Nat) : ZMod p384) = (x : ZMod p384) * y := by
    have := congrArg (Nat.cast : Nat → ZMod p384) keyN
    push_cast at this
    rw [ZMod.natCast_self, zero_mul, add_zero] at this
    exact_mod_cast this
  have hinv := ZMod.coe_mul_inv_eq_one (2 ^ 384) p384_coprime_R
  calc (A6 : ZMod p384)
      = (A6 : ZMod p384)
          * (((2 ^ 384 : Nat) : ZMod p384) * ((2 ^ 384 : Nat) : ZMod p384)⁻¹) := by
        rw [hinv, mul_one]
    _ = (x : ZMod p384) * y * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ := by rw [← mul_assoc, hcast]

theorem mem6_lt (M : JMem 64) (b : String) : mem6 M b < 2 ^ 384 := by
  have := (M b 0).isLt; have := (M b 8).isLt; have := (M b 16).isLt
  have := (M b 24).isLt; have := (M b 32).isLt; have := (M b 40).isLt
  simp only [mem6]
  omega

/-! ## The machine-level result -/

/-- **`bignum_montmul_p384` as imported computes the Montgomery product modulo p384.** For
    every machine state whose six words at `%rsi` hold `x` and whose six words at `%rcx`
    hold `y`, with `x · y ≤ 2^384 · p384`, running `s2nMontmulP384Block` under `runBlock`
    stores at `[%rdi + 0], …, [%rdi + 40]` a value `z < p384` with
    `z = x · y · (2^384)⁻¹` in `ZMod p384`. -/
theorem s2nMontmulP384_correct (st : JState 64)
    (hxy : mem6 st.mem "%rsi" * mem6 st.mem "%rcx" ≤ 2 ^ 384 * p384) :
    mem6 (runBlock st s2nMontmulP384Block).mem "%rdi" < p384 ∧
      ((mem6 (runBlock st s2nMontmulP384Block).mem "%rdi" : Nat) : ZMod p384)
        = (mem6 st.mem "%rsi" : ZMod p384) * (mem6 st.mem "%rcx" : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ := by
  have h := s2nMontmulP384_corresJ st
    ⟨0, mem6 st.mem "%rsi", mem6 st.mem "%rcx", 0⟩ ⟨rfl, rfl, trivial⟩
    ⟨rfl, mem6_lt _ _⟩
  have hz : mem6 (runBlock st s2nMontmulP384Block).mem "%rdi"
      = montAbs (mem6 st.mem "%rsi") (mem6 st.mem "%rcx") := h.2.2
  rw [hz]
  exact montAbs_spec _ _ (mem6_lt _ _) hxy

theorem p384_eq_p384Prime : p384 = CatCrypt.Crypto.Vale.P384FieldMul.p384Prime := by
  decide

/-- **The imported block meets the P-384 field-multiply denotation.** Under the hypotheses of
    `s2nMontmulP384_correct`, the stored value is below `p384Prime` and, in `P384Fp`, equals
    `P384_fmul_denote x y`, the specification the P-384 field-multiply leaf carries. -/
theorem s2nMontmulP384_fmul_denote (st : JState 64)
    (hxy : mem6 st.mem "%rsi" * mem6 st.mem "%rcx" ≤ 2 ^ 384 * p384) :
    mem6 (runBlock st s2nMontmulP384Block).mem "%rdi"
        < CatCrypt.Crypto.Vale.P384FieldMul.p384Prime ∧
      ((mem6 (runBlock st s2nMontmulP384Block).mem "%rdi" : Nat)
          : CatCrypt.Crypto.Vale.P384FieldMul.P384Fp)
        = CatCrypt.Crypto.Vale.P384FieldMul.P384_fmul_denote
            (mem6 st.mem "%rsi" : CatCrypt.Crypto.Vale.P384FieldMul.P384Fp)
            (mem6 st.mem "%rcx" : CatCrypt.Crypto.Vale.P384FieldMul.P384Fp) := by
  have h := s2nMontmulP384_correct st hxy
  rw [p384_eq_p384Prime] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
