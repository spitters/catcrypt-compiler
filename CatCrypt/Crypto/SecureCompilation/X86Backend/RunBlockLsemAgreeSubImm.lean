/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the immediate-source `sbb`

`RunBlockLsemAgree.lean` §11 carries the borrow op `sbb` at a register source
under the CF-only `JLstateCorrCF` (`sbb_case`). This module adds the
**immediate-source** `sbb`, the borrow-propagation opcode of a multi-limb
subtract fold at a literal subtrahend.

## The lowering

`.sbb dst (.imm n)` with materialising register `z` and fresh `CF` slot `fr`,
at current slot `cfN`, becomes three wires:

* `MOV z, n` — the literal at width 64;
* `SBBHI fr ← dst, z, cfN` — the borrow-out to the fresh slot;
* `SBB dst ← dst, z, cfN` — the data to `dst`.

`z` and `fr` lie in the synthetic flag namespace `flg`, so writes to them are
invisible to `JLstateCorrCF.regAgree` (asserted off `flg`). Unlike the `adc`
immediate case, the `.sbb` `runBlock` step and the `SBB` / `SBBHI` wires both
factor through `x86_SBB`, so the register-source transfer lemmas
`subBorrowWord_flagBit_eq` / `borrowOutBit_flagBit_eq` apply directly with no
opcode bridge.

## Main results

* `sbbImm_case`: a `.sbb dst (.imm n)` step under `JLstateCorrCF` agrees with the
  lsem straight-line image `[MOV z n; SBBHI fr←dst,z,cfN; SBB dst←dst,z,cfN]` and
  lands in `JLstateCorrCF` with the borrow migrated to `fr`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeSubImm

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## Per-opcode agreement for the immediate-source `sbb` -/

/-- **Per-opcode agreement for `.sbb dst (.imm n)`.** The three-wire lowering
    (materialise `n` in `z`, then the `SBBHI`/`SBB` pair reading the `CF` slot
    `cfN`) does not fail, and its result satisfies `JLstateCorrCF` with the `CF`
    slot migrated to `fr`: `dst` receives `dst − n − CF`, `fr` the borrow-out bit,
    and the register / memory axes agree with the `runBlock` `x86_SBB`. -/
theorem sbbImm_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN : String)
    (hcorr : JLstateCorrCF s ls flg cfN) (dst z fr : String) (n : Nat)
    (hdst : ¬ flg dst) (hz : flg z) (hfr : flg fr)
    (hzcf : z ≠ cfN) (hzfr : z ≠ fr) (hfrcf : fr ≠ cfN) :
    ∃ ls', lsemStraightMem
        [ (movImmLinstr 64 z n, MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "SBBHI")
            [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "SBB")
            [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none) ]
        ls = some ls' ∧
      JLstateCorrCF (runBlock s [.sbb dst (.imm n)]) ls' flg fr := by
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
  -- Step 1: the borrow-out to the fresh slot `fr`.
  set ls1 : LstateM :=
    { ls0 with reg := (ls0.reg.setReg fr
        (borrowOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg fr] (withWidthTag 64 "SBBHI")
        [.reg dst, .reg z, .reg cfN], MemTag.reg none) ls0 = some ls1 :=
    lsemStepMem_sbbhi3 fr dst z cfN ls0 _ _ _ hva0 hvz0 hvc0
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
        (subBorrowWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "SBB")
        [.reg dst, .reg z, .reg cfN], MemTag.reg none) ls1 = some ls2 :=
    lsemStepMem_sbb3 dst dst z cfN ls1 _ _ _ hva1 hvz1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep0, hstep1, hstep2, lsemStraightMem_nil]
  · have hrun : runBlock s [.sbb dst (.imm n)] =
        s.writeB5W dst (x86_SBB (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))) := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
    rw [hrun]
    have hdata : subBorrowWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf)))
        = (x86_SBB (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))).word :=
      subBorrowWord_flagBit_eq _ _ _
    have hcarry : borrowOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf)))
        = flagBit ((x86_SBB (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))).cf.getD false) :=
      borrowOutBit_flagBit_eq _ _ _
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeSubImm
