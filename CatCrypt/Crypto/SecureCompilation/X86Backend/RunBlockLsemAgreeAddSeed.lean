/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the flag-seeding `add` / `sub`

`RunBlockLsemAgree.lean` §2 carries the flag-**discarding** `.add` / `.sub` under
the plain register+memory correspondence `JLstateCorr`: their lsem image is the
two-address `regArith` wire, whose result records the data word but not the
carry/borrow-out. A Montgomery reduce's conditional-subtract fold instead uses an
`.add` / `.sub` whose carry-out is **read** by a following `.adc` / `.sbb`, so its
machine-faithful lowering must **capture** that carry-out into a `CF` slot.

This module carries that flag-seeding form: the carry/borrow-out of `.add` /
`.sub` is captured into a fresh `JLstateCorrCF` slot `fr` via an `ADCXHI` /
`SBBHI` wire whose carry-in is a width-1 zero register `zc`, so the result lands
in `JLstateCorrCF` ready to feed the carry chain.

## Why the `ADCXHI` wire with a zero carry-in realises `.add`'s carry-out

`x86_ADD v1 v2` and `x86_ADC v1 v2 false` produce the same data word and the same
`CF`: both are `v1 + v2` with carry-out `2^64 ≤ v1.toNat + v2.toNat`. So the
carry-capture wire `ADCXHI fr ← dst, src, zc` with `zc = 0#1` writes
`carryOutBit dst src 0#1 = flagBit ((x86_ADD dst src).cf)` — exactly the carry-out
`.add` records — and `ADCX dst ← dst, src, zc` writes `addCarryWord dst src 0#1 =
(x86_ADD dst src).word`. The `.sub` borrow-out factors through `x86_SUB` /
`x86_SBB false` the same way.

## The zero carry-in register `zc`

The carry-in operand of `ADCXHI` / `SBBHI` is read at **width 1**
(`getW zc 1`), and `lsemStepMC` accepts only a register there, never an
immediate. The lemmas therefore take the width-1 zero-carry register as a
precondition `getW zc 1 = some (flagBit false)`: `zc` lies in the synthetic flag
namespace `flg` (so it is exempt from the width-64 `regAgree`, which holds only
off `flg`) and is supplied by the ambient block invariant: the immediate-MOV wire
materialises a register only at width 32 or 64 (`widthFromTag`), so it cannot
produce the width-1 carry-in, and `lsemStepMC` reads the carry operand only from a
register, never an immediate.

## Main results

* `x86ADD_word`, `x86ADD_cf`: `x86_ADD.word` / `.cf` reduce to `waddcarry _ _ false`.
* `addCarryWord_x86ADD_eq`, `carryOutBit_x86ADD_eq`: the data / carry-out of a
  zero-carry `addCarryWord` / `carryOutBit` equal `x86_ADD`'s.
* `subBorrowWord_x86SUB_eq`, `borrowOutBit_x86SUB_eq`: the `.sub` duals via `x86_SUB`.
* `addSeed_case`: a flag-seeding `.add dst (.reg src)` step agrees with the lsem
  image `[ADCXHI fr←dst,src,zc; ADCX dst←dst,src,zc]` and lands in `JLstateCorrCF`
  with the carry-out in `fr`, given a width-1 zero-carry register `zc`.
* `subSeed_case`: the `.sub` borrow analogue via `SBBHI` / `SBB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddSeed

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. `add` / `sub` share the zero-carry `adcx` / `sbb` data and carry -/

/-- The `x86_ADD` data word is the `waddcarry _ _ false` low word. -/
theorem x86ADD_word (v1 v2 : BitVec 64) :
    (x86_ADD v1 v2).word = (waddcarry v1 v2 false).2 := by
  simp only [x86_ADD, rflags_of_aluop, waddcarry]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  exact BitVec.add_def v1 v2

/-- The `x86_ADD` carry-out flag is the `waddcarry _ _ false` carry bit. -/
theorem x86ADD_cf (v1 v2 : BitVec 64) :
    (x86_ADD v1 v2).cf.getD false = (waddcarry v1 v2 false).1 := by
  have h1 : v1.toNat < 2 ^ 64 := v1.isLt
  have h2 : v2.toNat < 2 ^ 64 := v2.isLt
  simp only [x86_ADD, rflags_of_aluop, waddcarry, wunsigned, Option.getD_some,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [decide_eq_decide, BitVec.toNat_add]
  omega

/-- **`add` seed data agreement.** The zero-carry lsem carry-add word equals the
    `JState` `x86_ADD` data output. -/
theorem addCarryWord_x86ADD_eq (v1 v2 : BitVec 64) :
    addCarryWord v1 v2 (flagBit false) = (x86_ADD v1 v2).word := by
  rw [adcx_data_eq, x86ADD_word]

/-- **`add` seed carry-out agreement.** The zero-carry lsem carry-out bit equals
    the flag bit of the `JState` `x86_ADD` carry-out. -/
theorem carryOutBit_x86ADD_eq (v1 v2 : BitVec 64) :
    carryOutBit v1 v2 (flagBit false) = flagBit ((x86_ADD v1 v2).cf.getD false) := by
  rw [adcx_carry_eq, x86ADD_cf]

/-- The zero-borrow `sub_borrow v1 v2 0` is the plain `BitVec` difference `v1 - v2`. -/
theorem sub_borrow_zero (v1 v2 : BitVec 64) : sub_borrow v1 v2 0 = v1 - v2 := by
  apply BitVec.eq_of_toNat_eq
  rw [sub_borrow, BitVec.toNat_ofInt, BitVec.toNat_sub]
  omega

/-- `x86_SUB` is `x86_SBB` at borrow-in `false`: the plain subtract is the
    zero-borrow subtract-with-borrow on every flag and the data word. -/
theorem x86SUB_eq_SBB_false (v1 v2 : BitVec 64) : x86_SUB v1 v2 = x86_SBB v1 v2 false := by
  simp only [x86_SUB, x86_SBB, Bool.false_eq_true, if_false, Nat.cast_zero, add_zero,
    sub_borrow_zero]

/-- **`sub` seed data agreement.** The zero-borrow lsem borrow-subtract word equals
    the `JState` `x86_SUB` data output. -/
theorem subBorrowWord_x86SUB_eq (v1 v2 : BitVec 64) :
    subBorrowWord v1 v2 (flagBit false) = (x86_SUB v1 v2).word := by
  rw [subBorrowWord_flagBit_eq, x86SUB_eq_SBB_false]

/-- **`sub` seed borrow-out agreement.** The zero-borrow lsem borrow-out bit equals
    the flag bit of the `JState` `x86_SUB` borrow-out. -/
theorem borrowOutBit_x86SUB_eq (v1 v2 : BitVec 64) :
    borrowOutBit v1 v2 (flagBit false) = flagBit ((x86_SUB v1 v2).cf.getD false) := by
  rw [borrowOutBit_flagBit_eq, x86SUB_eq_SBB_false]

/-! ## 2. Per-opcode agreement for the flag-seeding `add` -/

/-- **Per-opcode agreement for the flag-seeding `.add dst (.reg src)`.** Given a
    width-1 zero-carry register `zc` (distinct from the fresh slot `fr`), the pair
    `[ADCXHI fr←dst,src,zc; ADCX dst←dst,src,zc]` does not fail and its
    result satisfies `JLstateCorrCF` with the fresh `CF` slot `fr`: `dst` receives
    `dst + src`, `fr` the carry-out bit, and the register / memory axes agree with
    the `runBlock` `x86_ADD`. -/
theorem addSeed_case (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (hreg : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r))
    (hmem : ∀ (base : String) (off : Int), ls.lmem base off = s.mem base off)
    (dst src zc fr : String) (hzero : ls.reg.getW zc 1 = some (flagBit false))
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) (hfr : flg fr)
    (hdst_fr : dst ≠ fr) (hsrc_fr : src ≠ fr) (hzc_fr : zc ≠ fr) :
    ∃ ls', lsemStraightMem
        [ (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "ADCXHI")
            [LOperand.reg dst, LOperand.reg src, LOperand.reg zc], MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "ADCX")
            [LOperand.reg dst, LOperand.reg src, LOperand.reg zc], MemTag.reg none) ]
        ls = some ls' ∧
      JLstateCorrCF (runBlock s [.add dst (.reg src)]) ls' flg fr := by
  have hva : ls.reg.getW dst 64 = some (s.regs dst) := hreg dst hdst
  have hvb : ls.reg.getW src 64 = some (s.regs src) := hreg src hsrc
  -- Step 1: the carry-out to the fresh slot `fr`.
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg fr
        (carryOutBit (s.regs dst) (s.regs src) (flagBit false))).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
        [.reg dst, .reg src, .reg zc], MemTag.reg none) ls = some ls1 :=
    lsemStepMem_adcxhi3 fr dst src zc ls _ _ _ hva hvb hzero
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_fr]; exact hva
  have hvb1 : ls1.reg.getW src 64 = some (s.regs src) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hsrc_fr]; exact hvb
  have hvc1 : ls1.reg.getW zc 1 = some (flagBit false) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hzc_fr]; exact hzero
  -- Step 2: the data to `dst`.
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (addCarryWord (s.regs dst) (s.regs src) (flagBit false))).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
        [.reg dst, .reg src, .reg zc], MemTag.reg none) ls1 = some ls2 :=
    lsemStepMem_adcx3 dst dst src zc ls1 _ _ _ hva1 hvb1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  · have hrun : runBlock s [.add dst (.reg src)] =
        s.writeB5W dst (x86_ADD (s.regs dst) (s.regs src)) := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
    rw [hrun]
    have hdata : addCarryWord (s.regs dst) (s.regs src) (flagBit false)
        = (x86_ADD (s.regs dst) (s.regs src)).word :=
      addCarryWord_x86ADD_eq _ _
    have hcarry : carryOutBit (s.regs dst) (s.regs src) (flagBit false)
        = flagBit ((x86_ADD (s.regs dst) (s.regs src)).cf.getD false) :=
      carryOutBit_x86ADD_eq _ _
    refine ⟨?_, ?_, ?_, hfr⟩
    · -- regAgree off flg
      intro r hr
      have hr_fr : r ≠ fr := by rintro rfl; exact hr hfr
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp [JState.writeB5W]
      · simp only [hls2, hls1, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_fr]
        rw [hreg r hr]; simp [JState.writeB5W, hrd]
    · -- memAgree
      intro base off
      simp only [JState.writeB5W]
      exact hmem base off
    · -- cfAgree at the new slot fr
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_fr), LstateN.getW_setReg_same]
      rw [hcarry]; simp only [JState.flagB, JState.writeB5W_flags]

/-! ## 3. Per-opcode agreement for the flag-seeding `sub` -/

/-- **Per-opcode agreement for the flag-seeding `.sub dst (.reg src)`.** The borrow
    analogue of `addSeed_case`: with a width-1 zero-borrow register `zc` (distinct
    from the fresh slot `fr`), the pair
    `[SBBHI fr←dst,src,zc; SBB dst←dst,src,zc]` does not fail and lands in
    `JLstateCorrCF` with the borrow-out in the fresh slot `fr`, matching the
    `runBlock` `x86_SUB`. -/
theorem subSeed_case (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (hreg : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r))
    (hmem : ∀ (base : String) (off : Int), ls.lmem base off = s.mem base off)
    (dst src zc fr : String) (hzero : ls.reg.getW zc 1 = some (flagBit false))
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) (hfr : flg fr)
    (hdst_fr : dst ≠ fr) (hsrc_fr : src ≠ fr) (hzc_fr : zc ≠ fr) :
    ∃ ls', lsemStraightMem
        [ (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "SBBHI")
            [LOperand.reg dst, LOperand.reg src, LOperand.reg zc], MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "SBB")
            [LOperand.reg dst, LOperand.reg src, LOperand.reg zc], MemTag.reg none) ]
        ls = some ls' ∧
      JLstateCorrCF (runBlock s [.sub dst (.reg src)]) ls' flg fr := by
  have hva : ls.reg.getW dst 64 = some (s.regs dst) := hreg dst hdst
  have hvb : ls.reg.getW src 64 = some (s.regs src) := hreg src hsrc
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg fr
        (borrowOutBit (s.regs dst) (s.regs src) (flagBit false))).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg fr] (withWidthTag 64 "SBBHI")
        [.reg dst, .reg src, .reg zc], MemTag.reg none) ls = some ls1 :=
    lsemStepMem_sbbhi3 fr dst src zc ls _ _ _ hva hvb hzero
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_fr]; exact hva
  have hvb1 : ls1.reg.getW src 64 = some (s.regs src) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hsrc_fr]; exact hvb
  have hvc1 : ls1.reg.getW zc 1 = some (flagBit false) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hzc_fr]; exact hzero
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (subBorrowWord (s.regs dst) (s.regs src) (flagBit false))).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "SBB")
        [.reg dst, .reg src, .reg zc], MemTag.reg none) ls1 = some ls2 :=
    lsemStepMem_sbb3 dst dst src zc ls1 _ _ _ hva1 hvb1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  · have hrun : runBlock s [.sub dst (.reg src)] =
        s.writeB5W dst (x86_SUB (s.regs dst) (s.regs src)) := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
    rw [hrun]
    have hdata : subBorrowWord (s.regs dst) (s.regs src) (flagBit false)
        = (x86_SUB (s.regs dst) (s.regs src)).word :=
      subBorrowWord_x86SUB_eq _ _
    have hcarry : borrowOutBit (s.regs dst) (s.regs src) (flagBit false)
        = flagBit ((x86_SUB (s.regs dst) (s.regs src)).cf.getD false) :=
      borrowOutBit_x86SUB_eq _ _
    refine ⟨?_, ?_, ?_, hfr⟩
    · intro r hr
      have hr_fr : r ≠ fr := by rintro rfl; exact hr hfr
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp [JState.writeB5W]
      · simp only [hls2, hls1, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_fr]
        rw [hreg r hr]; simp [JState.writeB5W, hrd]
    · intro base off
      simp only [JState.writeB5W]
      exact hmem base off
    · simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_fr), LstateN.getW_setReg_same]
      rw [hcarry]; simp only [JState.flagB, JState.writeB5W_flags]

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddSeed
