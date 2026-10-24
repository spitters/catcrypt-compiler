/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the register-count shifts

`RunBlockLsemAgreeShift.lean` bridges the total `JState` fold `runBlock` and the
partial `LstateM` fold `lsemStraightMem` on `InShiftSubset`, the ALU core plus
the three shifts at an **immediate** count below the word width. This module
extends that subset with the shifts whose count comes from a **register**: the
two-address `shl` / `shr` over a `.reg` source operand and the BMI2 three-address
`shlx` / `shrx`.

## The count mask is a runtime condition

`JState`'s `x86_SHL` / `x86_SHR` / `x86_SHLX` / `x86_SHRX` mask the count with
`shiftCount i = i.toNat % 64`; the lsem `applyOpnN 64 "SHL" [a, b] = some (a <<<
b.toNat)` shifts by the unmasked count. At an immediate count the mask is
discharged syntactically (`n < 64` on the opcode). At a register count the count
is a runtime value, so no predicate on the opcode can discharge it: the side
condition is carried on the *state*. `ShiftCountInRange s i` says the count
register of `i` holds a value below the word width in `s`; `ShiftCountsInRange s
b` folds it along the block, evaluating each prefix, and
`ShiftCountsInRangeLoop s n b` folds that along the trip count. A caller
discharges it from whatever bounds its count — a masked count register, a loop
index below the limb count, a constant materialised by an earlier `mov`.

## Opcodes outside this extension

* `.sar dst (.reg c)` and `.sarx dst src c` have **no lsem image**. `applyOpnN`
  carries no `"SAR"` arm (`SHL` and `SHR` are the only shifts in it), and the
  structured arithmetic-shift recognizer `sarStruct?` matches only
  `Lopn [.reg dst] "SAR:w" [.reg s, .imm n]` — the count operand must be an
  `.imm`. So the arithmetic shift at a register count fails at every layer of the
  `lsemStepMem → lsemStepCast → lsemStepMC → lsemStepSh → lsemStepN` chain,
  and stays outside the bridged subset until the lsem side grows a
  variable-count arithmetic-shift arm.
* `.rorx`, and every opcode already outside `InShiftSubset` (the flag/carry
  spine, `cmove`, the runtime-index memory ops), are unchanged here.

## Main results

* `ShiftCountInRange` / `ShiftCountsInRange` / `ShiftCountsInRangeLoop`: the
  runtime count-range side condition, per opcode, per block, and per counted
  loop.
* `InShiftRegSubset`: the covered opcode set — `InShiftSubset` plus the
  register-count `shl` / `shr` and the BMI2 `shlx` / `shrx`.
* `jToRMShR`: the `JInstr` to wire lowering for that set.
* `x86_SHL_word_reg`, `x86_SHR_word_reg`, `x86_SHLX_reg`, `x86_SHRX_reg`: the
  `JState` shift data words at an in-range register count.
* `jToRMShR_agrees`: per-opcode totality and `JLstateCorr` preservation.
* `runBlock_lsem_agreeShR`: the block-induction lift over a straight-line block.
* `runBlock_lsem_agreeShR_loop`: the counted-loop lift.
* `x86_SHRX_mask` / `x86_SHLX_mask`, `lowerAluJ2_shr_reg_lsem_agree` /
  `lowerAluJ2_shl_reg_lsem_agree`: the register-count `SHR:64` / `SHL:64` export
  lowers through `LoweringExtended.lowerAluJ2` to the single `shrx` / `shlx`,
  whose `JState` word is the shift by the count masked to six bits, and at an
  in-range count that block agrees with `lsemStraightMem` on the export.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShiftReg

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-! ## 1. The masked count on an in-range runtime value -/

/-- For a count word below the word width the `JState` shift mask is the
    identity: `shiftCount c = c.toNat`. -/
theorem shiftCount_of_toNat_lt {c : BitVec 64} (h : c.toNat < 64) :
    shiftCount c = c.toNat := by
  simp only [shiftCount, VIR.shiftMask_64, Nat.mod_eq_of_lt h]

/-! ## 2. The `JState` shift data words at an in-range register count -/

/-- The `x86_SHL` data word at an in-range count is the plain left shift
    `v <<< c.toNat` (the count mask and the `wshl` clamp are both vacuous). -/
theorem x86_SHL_word_reg {c : BitVec 64} (h : c.toNat < 64) (v : BitVec 64) :
    (x86_SHL v c).word = v <<< c.toNat := by
  have hmin : min 64 c.toNat = c.toNat := by omega
  simp only [x86_SHL, shiftCount_of_toNat_lt h]
  by_cases h0 : c.toNat = 0
  · rw [ite_eq_left h0, h0]; simp [rflags_None]
  · simp only [ite_eq_right h0, rflags_OF, wshl, hmin]

/-- The `x86_SHR` data word at an in-range count is the plain logical right shift
    `v >>> c.toNat`. -/
theorem x86_SHR_word_reg {c : BitVec 64} (h : c.toNat < 64) (v : BitVec 64) :
    (x86_SHR v c).word = v >>> c.toNat := by
  have hmin : min 64 c.toNat = c.toNat := by omega
  simp only [x86_SHR, shiftCount_of_toNat_lt h]
  by_cases h0 : c.toNat = 0
  · rw [ite_eq_left h0, h0]; simp [rflags_None]
  · simp only [ite_eq_right h0, rflags_OF, wshr, hmin]

/-- The BMI2 `x86_SHLX` word at an in-range count is `v <<< c.toNat`. `SHLX`
    writes no flag, so this is the whole result. -/
theorem x86_SHLX_reg {c : BitVec 64} (h : c.toNat < 64) (v : BitVec 64) :
    x86_SHLX v c = v <<< c.toNat := by
  have hmin : min 64 c.toNat = c.toNat := by omega
  simp only [x86_SHLX, shiftCount_of_toNat_lt h, wshl, hmin]

/-- The BMI2 `x86_SHRX` word at an in-range count is `v >>> c.toNat`. -/
theorem x86_SHRX_reg {c : BitVec 64} (h : c.toNat < 64) (v : BitVec 64) :
    x86_SHRX v c = v >>> c.toNat := by
  have hmin : min 64 c.toNat = c.toNat := by omega
  simp only [x86_SHRX, shiftCount_of_toNat_lt h, wshr, hmin]

/-! ## 3. The runtime side condition -/

/-- The runtime count-range side condition of a single opcode: a register-count
    shift requires its count register to hold a value below the word width in the
    state the opcode runs from; every other opcode carries no condition. -/
def ShiftCountInRange (s : JState 64) : JInstr 64 → Prop
  | .shl _ (.reg c) => (s.get c).toNat < 64
  | .shr _ (.reg c) => (s.get c).toNat < 64
  | .shlx _ _ c => (s.get c).toNat < 64
  | .shrx _ _ c => (s.get c).toNat < 64
  | _ => True

/-- The count-range side condition along a straight-line block: each opcode's
    condition holds in the state that opcode runs from, which is the `JState`
    fold of the prefix before it. -/
def ShiftCountsInRange : JState 64 → List (JInstr 64) → Prop
  | _, [] => True
  | s, i :: is => ShiftCountInRange s i ∧ ShiftCountsInRange (evalInstr s i) is

/-- The count-range side condition along a counted loop: the block condition
    holds at the entry state of every trip. -/
def ShiftCountsInRangeLoop : JState 64 → Nat → List (JInstr 64) → Prop
  | _, 0, _ => True
  | s, k + 1, b => ShiftCountsInRange s b ∧ ShiftCountsInRangeLoop (runBlock s b) k b

/-! ## 4. The lowering and the covered subset -/

/-- `jToRMShR`: `jToRMSh` extended with the register-count shifts. A two-address
    `shl` / `shr` over a `.reg` count lowers to the two-address wire
    `Lopn [.reg dst] (withWidthTag 64 mnem) [.reg dst, .reg c]`; the BMI2
    `shlx` / `shrx` lower to the three-address form with the shifted source in
    operand 0. Every other opcode keeps its `jToRMSh` image. -/
def jToRMShR : JInstr 64 → LinstrRM
  | .shl dst (.reg c) =>
      (.Lopn [.reg dst] (withWidthTag 64 "SHL") [.reg dst, .reg c], .reg none)
  | .shr dst (.reg c) =>
      (.Lopn [.reg dst] (withWidthTag 64 "SHR") [.reg dst, .reg c], .reg none)
  | .shlx dst src c =>
      (.Lopn [.reg dst] (withWidthTag 64 "SHL") [.reg src, .reg c], .reg none)
  | .shrx dst src c =>
      (.Lopn [.reg dst] (withWidthTag 64 "SHR") [.reg src, .reg c], .reg none)
  | i => jToRMSh i

/-- `InShiftSubset` extended with the register-count logical shifts. The
    count-range condition is absent here by design — it is a runtime property,
    carried by `ShiftCountInRange` on the state. The arithmetic shifts `.sar` at
    a `.reg` count and `.sarx` are **not** in the set: `applyOpnN` has no `"SAR"`
    arm and `sarStruct?` requires an `.imm` count, so they have no lsem image. -/
def InShiftRegSubset : JInstr 64 → Prop
  | .shl _ (.reg _) => True
  | .shr _ (.reg _) => True
  | .shlx _ _ _ => True
  | .shrx _ _ _ => True
  | i => InShiftSubset i

/-! ## 5. Per-opcode agreement -/

/-- **Per-opcode agreement for `.shl dst (.reg c)`** at an in-range count. -/
theorem shlReg_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst c : String) (h : (s.get c).toNat < 64) :
    ∃ ls', lsemStraightMem [jToRMShR (.shl dst (.reg c))] ls = some ls' ∧
      JLstateCorr (runBlock s [.shl dst (.reg c)]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (s.get dst <<< (s.get c).toNat) ?_ ?_⟩
  · show lsemStraightMem
      [(.Lopn [.reg dst] (withWidthTag 64 "SHL") [.reg dst, .reg c], .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_regArith dst "SHL" (.reg c) ls (stripWidthTag_withWidthTag_SHL 64)
      (by decide) (by decide) (by decide) (by decide)
      (s.get dst) (s.get c) _ (hcorr.regAgree dst)
      (evalOperandN_toLOp s ls hcorr (.reg c))
      (by rw [← VIR.shiftMask_of_lt (w := 64) h]; rfl)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, JOperand.eval,
      x86_SHL_word_reg h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]

/-- **Per-opcode agreement for `.shr dst (.reg c)`** at an in-range count. -/
theorem shrReg_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst c : String) (h : (s.get c).toNat < 64) :
    ∃ ls', lsemStraightMem [jToRMShR (.shr dst (.reg c))] ls = some ls' ∧
      JLstateCorr (runBlock s [.shr dst (.reg c)]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (s.get dst >>> (s.get c).toNat) ?_ ?_⟩
  · show lsemStraightMem
      [(.Lopn [.reg dst] (withWidthTag 64 "SHR") [.reg dst, .reg c], .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_regArith dst "SHR" (.reg c) ls (stripWidthTag_withWidthTag_SHR 64)
      (by decide) (by decide) (by decide) (by decide)
      (s.get dst) (s.get c) _ (hcorr.regAgree dst)
      (evalOperandN_toLOp s ls hcorr (.reg c))
      (by rw [← VIR.shiftMask_of_lt (w := 64) h]; rfl)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, JOperand.eval,
      x86_SHR_word_reg h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]

/-- **Per-opcode agreement for the BMI2 `.shlx dst src c`** at an in-range count.
    The three-address wire reads the shifted word from `src`, leaving it
    intact. -/
theorem shlxReg_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst src c : String) (h : (s.get c).toNat < 64) :
    ∃ ls', lsemStraightMem [jToRMShR (.shlx dst src c)] ls = some ls' ∧
      JLstateCorr (runBlock s [.shlx dst src c]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (s.get src <<< (s.get c).toNat) ?_ ?_⟩
  · show lsemStraightMem
      [(.Lopn [.reg dst] (withWidthTag 64 "SHL") [.reg src, .reg c], .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_regArith3 dst src (.reg c) ls "SHL" (stripWidthTag_withWidthTag_SHL 64)
      (by decide) (by decide) (by decide) (by decide)
      (s.get src) (s.get c) _ (hcorr.regAgree src)
      (evalOperandN_toLOp s ls hcorr (.reg c))
      (by rw [← VIR.shiftMask_of_lt (w := 64) h]; rfl)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_SHLX_reg h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]

/-- **Per-opcode agreement for the BMI2 `.shrx dst src c`** at an in-range
    count. -/
theorem shrxReg_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst src c : String) (h : (s.get c).toNat < 64) :
    ∃ ls', lsemStraightMem [jToRMShR (.shrx dst src c)] ls = some ls' ∧
      JLstateCorr (runBlock s [.shrx dst src c]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (s.get src >>> (s.get c).toNat) ?_ ?_⟩
  · show lsemStraightMem
      [(.Lopn [.reg dst] (withWidthTag 64 "SHR") [.reg src, .reg c], .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_regArith3 dst src (.reg c) ls "SHR" (stripWidthTag_withWidthTag_SHR 64)
      (by decide) (by decide) (by decide) (by decide)
      (s.get src) (s.get c) _ (hcorr.regAgree src)
      (evalOperandN_toLOp s ls hcorr (.reg c))
      (by rw [← VIR.shiftMask_of_lt (w := 64) h]; rfl)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, x86_SHRX_reg h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]

/-- **Per-opcode agreement on the register-count shift subset.** For an
    `InShiftRegSubset` opcode whose runtime count condition holds in `s`, the lsem
    twin `lsemStraightMem [jToRMShR i]` does not fail and its result corresponds —
    via `JLstateCorr` — to the `runBlock` result. The four register-count shift
    arms are the cases above; every other opcode defers to `jToRMSh_agrees`. -/
theorem jToRMShR_agrees (i : JInstr 64) (hi : InShiftRegSubset i)
    (s : JState 64) (ls : LstateM) (hcnt : ShiftCountInRange s i)
    (hcorr : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem [jToRMShR i] ls = some ls' ∧ JLstateCorr (runBlock s [i]) ls' := by
  cases i
  case shl dst src =>
    cases src
    case reg c => exact shlReg_case s ls hcorr dst c hcnt
    case imm n => exact jToRMSh_agrees (.shl dst (.imm n)) hi s ls hcorr
  case shr dst src =>
    cases src
    case reg c => exact shrReg_case s ls hcorr dst c hcnt
    case imm n => exact jToRMSh_agrees (.shr dst (.imm n)) hi s ls hcorr
  case shlx dst src c => exact shlxReg_case s ls hcorr dst src c hcnt
  case shrx dst src c => exact shrxReg_case s ls hcorr dst src c hcnt
  case sar dst src =>
    cases src
    case imm n => exact jToRMSh_agrees (.sar dst (.imm n)) hi s ls hcorr
    case reg c => exact hi.elim
  case mov dst src => exact jToRMSh_agrees (.mov dst src) hi s ls hcorr
  case add dst src => exact jToRMSh_agrees (.add dst src) hi s ls hcorr
  case sub dst src => exact jToRMSh_agrees (.sub dst src) hi s ls hcorr
  case imul dst src => exact jToRMSh_agrees (.imul dst src) hi s ls hcorr
  case and_ dst src => exact jToRMSh_agrees (.and_ dst src) hi s ls hcorr
  case or_ dst src => exact jToRMSh_agrees (.or_ dst src) hi s ls hcorr
  case xor_ dst src => exact jToRMSh_agrees (.xor_ dst src) hi s ls hcorr
  case loadMem dst base off => exact jToRMSh_agrees (.loadMem dst base off) hi s ls hcorr
  case storeMem base off src => exact jToRMSh_agrees (.storeMem base off src) hi s ls hcorr
  all_goals exact hi.elim

/-! ## 6. Block-level lift -/

/-- **Block-level agreement over the register-count shift subset.** A whole
    straight-line block all of whose opcodes are in `InShiftRegSubset`, and whose
    register-count shifts all have in-range counts along the run
    (`ShiftCountsInRange`), runs to completion under `lsemStraightMem` on
    `b.map jToRMShR`, and its result corresponds — on the register and the memory
    axis — to the `runBlock` result. Straight-line induction on the block. -/
theorem runBlock_lsem_agreeShR (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InShiftRegSubset i) (s : JState 64) (ls : LstateM)
    (hcnt : ShiftCountsInRange s b) (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (b.map jToRMShR) ls = some ls' ∧ JLstateCorr (runBlock s b) ls' := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨hcnti, hcntis⟩ := hcnt
    obtain ⟨ls1, hstep1, hcorr1⟩ :=
      jToRMShR_agrees i (hb i (List.mem_cons_self ..)) s ls hcnti h
    have hstep : lsemStepMem (jToRMShR i) ls = some ls1 := by
      rwa [lsemStraightMem_single] at hstep1
    have hri : runBlock s [i] = evalInstr s i := by
      simp only [runBlock_cons, runBlock_nil]
    obtain ⟨ls', hstep', hcorr'⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) (runBlock s [i]) ls1
        (by rw [hri]; exact hcntis) hcorr1
    refine ⟨ls', ?_, ?_⟩
    · simp only [List.map_cons, lsemStraightMem_cons, hstep]
      exact hstep'
    · simpa only [runBlock_cons, runBlock_nil] using hcorr'

/-! ## 7. Counted-loop lift -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The counted-loop lift on the register-count shift subset.** A straight-line
    body `b` all of whose opcodes are in `InShiftRegSubset`, iterated `n` times
    with the count-range condition holding at the entry state of every trip
    (`ShiftCountsInRangeLoop`), agrees on both machine models: the `n`-fold
    `runBoundedLoopMem` over the lowered body `b.map jToRMShR` runs to completion
    and its result corresponds — via `JLstateCorr` — to the `JState`-side `n`-fold
    `runBoundedLoop`. Induction on the trip count: each trip is one
    `runBlock_lsem_agreeShR`, and the inter-trip `setLpc 1` is absorbed by
    `JLstateCorr_setLpc`. -/
theorem runBlock_lsem_agreeShR_loop (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InShiftRegSubset i) (n : Nat) (s : JState 64) (ls : LstateM)
    (hcnt : ShiftCountsInRangeLoop s n b) (h : JLstateCorr s ls) :
    ∃ ls', runBoundedLoopMem (b.map jToRMShR) n ls = some ls' ∧
      JLstateCorr (runBoundedLoop s n b) ls' := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨hcntb, hcntl⟩ := hcnt
      obtain ⟨ls1, hstep1, hcorr1⟩ := runBlock_lsem_agreeShR b hb s ls hcntb h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s b) (ls1.setLpc 1) hcntl (JLstateCorr_setLpc _ _ hcorr1 1)

/-! ## 8. The lowered register-count shift export

The SSA exporter emits a register-count shift as
`Lopn [.reg dst] (withWidthTag 64 "SHR") [.reg v, .reg c]`, and
`LoweringExtended.lowerAluJ2` lowers it to the single BMI2 `[.shrx dst v c]`.
The `JState` word of that instruction is `v >>> (c.toNat % 64)` at every count
(`x86_SHRX_mask`); the lsem word `applyOpnN 64 "SHR" [a, b] = some (a >>> b.toNat)`
is unmasked, so the two agree exactly on the in-range counts `c.toNat < 64`
(`ShiftCountInRange`), which is the side condition the agreement theorem carries. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
  (lowerAluJ2 lowerAluJ2_shr_reg lowerAluJ2_shl_reg)

/-- The `x86_SHRX` word at every count: the shift by the count masked to six
    bits. -/
theorem x86_SHRX_mask (v c : BitVec 64) : x86_SHRX v c = v >>> (c.toNat % 64) := by
  have hmin : min 64 (c.toNat % 64) = c.toNat % 64 :=
    Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  simp only [x86_SHRX, shiftCount, wshr, VIR.shiftMask_64, hmin]

/-- The `x86_SHLX` word at every count: the shift by the count masked to six
    bits. -/
theorem x86_SHLX_mask (v c : BitVec 64) : x86_SHLX v c = v <<< (c.toNat % 64) := by
  have hmin : min 64 (c.toNat % 64) = c.toNat % 64 :=
    Nat.min_eq_right (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  simp only [x86_SHLX, shiftCount, wshl, VIR.shiftMask_64, hmin]

/-- `runBlock` of the lowered `shrx` block writes the masked shift to `dst`. -/
theorem runBlock_shrx (s : JState 64) (dst v c : String) :
    runBlock s [.shrx dst v c] = s.setReg dst (s.get v >>> ((s.get c).toNat % 64)) := by
  simp only [runBlock_cons, runBlock_nil, evalInstr, x86_SHRX_mask]

/-- `runBlock` of the lowered `shlx` block writes the masked shift to `dst`. -/
theorem runBlock_shlx (s : JState 64) (dst v c : String) :
    runBlock s [.shlx dst v c] = s.setReg dst (s.get v <<< ((s.get c).toNat % 64)) := by
  simp only [runBlock_cons, runBlock_nil, evalInstr, x86_SHLX_mask]

/-- **The lowered register-count `SHR` agrees with its export.** The exporter's
    `Lopn [dst] "SHR:64" [reg v, reg c]` lowers through `lowerAluJ2` to
    `[shrx dst v c]`, and at an in-range count `(s.get c).toNat < 64` the
    `runBlock` result of that block corresponds, via `JLstateCorr`, to the
    `lsemStraightMem` result on the export. -/
theorem lowerAluJ2_shr_reg_lsem_agree (s : JState 64) (ls : LstateM)
    (hcorr : JLstateCorr s ls) (dst v c : String) (h : (s.get c).toNat < 64) :
    ∃ b ls', lowerAluJ2 dst (withWidthTag 64 "SHR") (.reg v) (.reg c) = some b ∧
      lsemStraightMem
        [(.Lopn [.reg dst] (withWidthTag 64 "SHR") [.reg v, .reg c], .reg none)] ls
        = some ls' ∧
      JLstateCorr (runBlock s b) ls' := by
  obtain ⟨ls', hstep, hc⟩ := shrxReg_case s ls hcorr dst v c h
  exact ⟨_, ls', lowerAluJ2_shr_reg dst _ v c (stripWidthTag_withWidthTag_SHR 64), hstep, hc⟩

/-- **The lowered register-count `SHL` agrees with its export**, the left-shift
    twin of `lowerAluJ2_shr_reg_lsem_agree`. -/
theorem lowerAluJ2_shl_reg_lsem_agree (s : JState 64) (ls : LstateM)
    (hcorr : JLstateCorr s ls) (dst v c : String) (h : (s.get c).toNat < 64) :
    ∃ b ls', lowerAluJ2 dst (withWidthTag 64 "SHL") (.reg v) (.reg c) = some b ∧
      lsemStraightMem
        [(.Lopn [.reg dst] (withWidthTag 64 "SHL") [.reg v, .reg c], .reg none)] ls
        = some ls' ∧
      JLstateCorr (runBlock s b) ls' := by
  obtain ⟨ls', hstep, hc⟩ := shlxReg_case s ls hcorr dst v c h
  exact ⟨_, ls', lowerAluJ2_shl_reg dst _ v c (stripWidthTag_withWidthTag_SHL 64), hstep, hc⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShiftReg
