/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the immediate-source `adc`

`RunBlockLsemAgree.lean` §9 carries the ADX carry ops `adcx` / `adox` under the
two-slot `JLstateCorrF`, and §11 the borrow op `sbb` under the CF-only
`JLstateCorrCF`. This module adds the **plain add-with-carry** `adc` at an
immediate source, the carry-propagation opcode of a Montgomery-reduce fold
chain (`Curve4MontMulProvenEmit.emitMontRedcStepAt`'s `adc dᵢ, 0`).

## Why the existing `ADCX` wire realises `adc`

`x86_ADC` and `x86_ADCX` share the same data/carry function `waddcarry`
(`x86_ADC v1 v2 c |>.word = (waddcarry v1 v2 c).2`,
`x86_ADC v1 v2 c |>.cf.getD false = (waddcarry v1 v2 c).1`): `adc` is
`dst := dst + src + CF` with carry-out, exactly `adcx`'s data effect. The two
differ only in which `JState` flags they clobber — `adc` writes all five,
`adcx` only `CF` — which is invisible to the flagless lsem register machine, so
the structured `ADCX` / `ADCXHI` wires (`lsemStepMem_adcx3` /
`lsemStepMem_adcxhi3`) are the faithful lsem image of `adc` as well. Because
`adc` clobbers `OF`, the correspondence is the CF-only `JLstateCorrCF`, not the
two-slot `JLstateCorrF`.

## The lowering

`.adc dst (.imm n)` with materialising register `z` and fresh `CF` slot `fr`,
at current slot `cfN`, becomes three wires:

* `MOV z, n` — the literal at width 64;
* `ADCXHI fr ← dst, z, cfN` — the carry-out to the fresh slot;
* `ADCX dst ← dst, z, cfN` — the data to `dst`.

`z` and `fr` lie in the synthetic flag namespace `flg`, so writes to them are
invisible to `JLstateCorrCF.regAgree` (asserted off `flg`).

## Main results

* `adcImm_case`: a `.adc dst (.imm n)` step under `JLstateCorrCF` agrees with the
  lsem straight-line image `[MOV z n; ADCXHI fr←dst,z,cfN; ADCX dst←dst,z,cfN]` and
  lands in `JLstateCorrCF` with the carry migrated to `fr`.
* `x86ADC_word`, `x86ADC_cf`: `x86_ADC.word` / `.cf` reduce to `waddcarry`.
* `addCarryWord_x86ADC_eq`, `carryOutBit_x86ADC_eq`: transfer the proven
  `adcx_data_eq` / `adcx_carry_eq` to `.adc`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddImm

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. `adc` shares `adcx`'s data / carry function -/

/-- The `x86_ADC` data word is the `waddcarry` low word — the same word the
    `ADCX`/`ADOX` semantics produce. -/
theorem x86ADC_word (v1 v2 : BitVec 64) (c : Bool) :
    (x86_ADC v1 v2 c).word = (waddcarry v1 v2 c).2 := by
  simp only [x86_ADC, rflags_of_aluop, add_carry, waddcarry]

/-- The `x86_ADC` carry-out flag is the `waddcarry` carry bit. -/
theorem x86ADC_cf (v1 v2 : BitVec 64) (c : Bool) :
    (x86_ADC v1 v2 c).cf.getD false = (waddcarry v1 v2 c).1 := by
  have h1 : v1.toNat < 2 ^ 64 := v1.isLt
  have h2 : v2.toNat < 2 ^ 64 := v2.isLt
  simp only [x86_ADC, rflags_of_aluop, add_carry, waddcarry, wunsigned, Option.getD_some]
  refine decide_eq_decide.mpr ?_
  simp only [BitVec.toNat_ofNat]
  cases c <;> simp

/-- **`adc` data agreement.** The lsem carry-add word equals the `JState`
    `x86_ADC` data output. -/
theorem addCarryWord_x86ADC_eq (v1 v2 : BitVec 64) (c : Bool) :
    addCarryWord v1 v2 (flagBit c) = (x86_ADC v1 v2 c).word := by
  rw [adcx_data_eq, x86ADC_word]

/-- **`adc` carry-out agreement.** The lsem carry-out bit equals the flag bit of
    the `JState` `x86_ADC` carry-out. -/
theorem carryOutBit_x86ADC_eq (v1 v2 : BitVec 64) (c : Bool) :
    carryOutBit v1 v2 (flagBit c) = flagBit ((x86_ADC v1 v2 c).cf.getD false) := by
  rw [adcx_carry_eq, x86ADC_cf]

/-! ## 2. Per-opcode agreement for the immediate-source `adc` -/

/-- **Per-opcode agreement for `.adc dst (.imm n)`.** The three-wire lowering
    (materialise `n` in `z`, then the `ADCXHI`/`ADCX` pair reading the `CF` slot
    `cfN`) does not fail, and its result satisfies `JLstateCorrCF` with the `CF`
    slot migrated to `fr`: `dst` receives `dst + n + CF`, `fr` the carry-out bit,
    and the register / memory axes agree with the `runBlock` `x86_ADC`. -/
theorem adcImm_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN : String)
    (hcorr : JLstateCorrCF s ls flg cfN) (dst z fr : String) (n : Nat)
    (hdst : ¬ flg dst) (hz : flg z) (hfr : flg fr)
    (hzcf : z ≠ cfN) (hzfr : z ≠ fr) (hfrcf : fr ≠ cfN) :
    ∃ ls', lsemStraightMem
        [ (movImmLinstr 64 z n, MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "ADCXHI")
            [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "ADCX")
            [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none) ]
        ls = some ls' ∧
      JLstateCorrCF (runBlock s [.adc dst (.imm n)]) ls' flg fr := by
  have hdst_z : dst ≠ z := fun h => hdst (h ▸ hz)
  have hdst_fr : dst ≠ fr := fun h => hdst (h ▸ hfr)
  have hdst_cf : dst ≠ cfN := fun h => hdst (h ▸ hcorr.cfFlg)
  -- Step 0: materialise the literal in the synthetic register `z`.
  set ls0 : LstateM :=
    { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 n)).nextPc } with hls0
  have hstep0 : lsemStepMem (movImmLinstr 64 z n, MemTag.reg none) ls = some ls0 :=
    lsemStepMem_movImm z n ls
  have hva0 : ls0.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls0]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_z]; exact hcorr.regAgree dst hdst
  have hvz0 : ls0.reg.getW z 64 = some (BitVec.ofNat 64 n) := by
    rw [hls0]; simp only [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hvc0 : ls0.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    rw [hls0]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzcf)]; exact hcorr.cfAgree
  -- Step 1: the carry-out to the fresh slot `fr`.
  set ls1 : LstateM :=
    { ls0 with reg := (ls0.reg.setReg fr
        (carryOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
        [.reg dst, .reg z, .reg cfN], MemTag.reg none) ls0 = some ls1 :=
    lsemStepMem_adcxhi3 fr dst z cfN ls0 _ _ _ hva0 hvz0 hvc0
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_fr]; exact hva0
  have hvz1 : ls1.reg.getW z 64 = some (BitVec.ofNat 64 n) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hzfr]; exact hvz0
  have hvc1 : ls1.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hfrcf)]; exact hvc0
  -- Step 2: the data to `dst`.
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (addCarryWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
        [.reg dst, .reg z, .reg cfN], MemTag.reg none) ls1 = some ls2 :=
    lsemStepMem_adcx3 dst dst z cfN ls1 _ _ _ hva1 hvz1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep0, hstep1, hstep2, lsemStraightMem_nil]
  · have hrun : runBlock s [.adc dst (.imm n)] =
        s.writeB5W dst (x86_ADC (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))) := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
    rw [hrun]
    have hdata : addCarryWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf)))
        = (x86_ADC (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))).word :=
      addCarryWord_x86ADC_eq _ _ _
    have hcarry : carryOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf)))
        = flagBit ((x86_ADC (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))).cf.getD false) :=
      carryOutBit_x86ADC_eq _ _ _
    refine ⟨?_, ?_, ?_, hfr⟩
    · -- regAgree off flg
      intro r hr
      have hr_fr : r ≠ fr := by rintro rfl; exact hr hfr
      have hr_z : r ≠ z := by rintro rfl; exact hr hz
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, hls0, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp [JState.writeB5W]
      · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_fr,
          LstateN.getW_setReg_other _ _ _ _ _ hr_z]
        rw [hcorr.regAgree r hr]; simp [JState.writeB5W, hrd]
    · -- memAgree
      intro base off
      simp only [JState.writeB5W]
      exact hcorr.memAgree base off
    · -- cfAgree at the new slot fr
      simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_fr), LstateN.getW_setReg_same]
      rw [hcarry]; simp only [JState.flagB, JState.writeB5W_flags]

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddImm
