/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddSeed
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeSubImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCmov
public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the conditional-subtract round

The 4-limb branch-free conditional-subtract round of a Montgomery reduce —
trial-subtract the modulus through the borrow chain and the top word, then
`CMOVB` each result limb back to its saved copy on a final borrow — as one block
agreement under the CF-only correspondence `JLstateCorrCF`:

```
sub  res0, p0          -- borrow seed (borrow-out captured to a fresh slot)
sbb  res1, p1
sbb  res2, p2
sbb  res3, p3
sbb  rtop, 0           -- top word; its borrow-out is the final CF
cmovb res0, sav0       -- restore on borrow; reads the final CF, writes no flag
cmovb res1, sav1
cmovb res2, sav2
cmovb res3, sav3
```

The borrow spine is composed from the per-opcode leaves proven elsewhere: the
flag-seeding `.sub` (`subSeed_case`), the register-source `.sbb`
(`sbbColumn_agree`, wrapping `sbb_case`), and the immediate-source `.sbb`
(`sbbImm_case`), chained with the borrow-slot-migrating composition
`runBlock_lsem_agreeCF_seq_migrate`. The four `.cmovb` steps READ the final
borrow slot but do not migrate it (`cmovb` writes no flag), so the block lands
in `JLstateCorrCF` at the last `.sbb`'s fresh slot.

The `.sub` seed reads a width-1 zero register `zc` as its carry-in (see the
`RunBlockLsemAgreeAddSeed` module header for the `zc` contract: `zc` lies in the
synthetic flag namespace and the ambient block invariant supplies its zero
value). The immediate `.sbb` materialises its literal in a synthetic register
`z`.

## Main results

* `JLstateCorrCF_of_F`: `JLstateCorrF` weakens to `JLstateCorrCF` by dropping
  the `OF` axis.
* `JLstateCorrCF_setReg`: `JLstateCorrCF` is preserved by a matched
  flag-transparent register write; the shared tail of the flag-reader cases.
* `cmovb_caseCF`: per-opcode agreement for `.cmovb dst (.reg src)` under
  `JLstateCorrCF`, preserving the designated slot.
* `condSubRoundL`: the lsem lowering of the parametric source block
  `Curve4MontMulProvenEmit.condSubRoundJ`, over the same register-name
  parameters.
* `condSubRound_lsem_agree`: the block agreement from a `JLstateCorrCF` entry.
* `condSubRound_lsem_agree_of_F`: the same agreement from a `JLstateCorrF`
  entry, via the weakening.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSub

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddSeed
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeSubImm
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCmov
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit (condSubRoundJ)
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The `F → CF` weakening -/

/-- `JLstateCorrF` weakens to `JLstateCorrCF`: dropping the `OF` axis keeps the
    register, memory, and `CF`-slot fields unchanged. -/
theorem JLstateCorrCF_of_F (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (cfN ofN : String) (h : JLstateCorrF s ls flg cfN ofN) :
    JLstateCorrCF s ls flg cfN where
  regAgree := h.regAgree
  memAgree := h.memAgree
  cfAgree := h.cfAgree
  cfFlg := h.cfFlg

/-! ## 2. Per-opcode agreement for `cmovb` under `JLstateCorrCF` -/

/-- `JLstateCorrCF` is preserved by a **matched** register write to a non-flag
    name: the `JState` result `snew` differs from `s` only in `dst := v` on the
    register axis, with memory and flags unchanged, and the lsem state writes the
    same `v` to `dst` at width 64. The `JLstateCorrCF` analogue of
    `JLstateCorrZ_setReg`. -/
theorem JLstateCorrCF_setReg (s snew : JState 64) (ls : LstateM) (flg : String → Prop)
    (cfN : String) (hcorr : JLstateCorrCF s ls flg cfN)
    (dst : String) (v : BitVec 64) (hdst : ¬ flg dst)
    (hs : ∀ r, snew.regs r = if r = dst then v else s.regs r)
    (hmem : ∀ base off, snew.mem base off = s.mem base off)
    (hflags : snew.flags = s.flags) :
    JLstateCorrCF snew { ls with reg := (ls.reg.setReg dst v).nextPc } flg cfN := by
  have hdst_ne_cf : dst ≠ cfN := by rintro rfl; exact hdst hcorr.cfFlg
  have hcf : snew.flagB (·.cf) = s.flagB (·.cf) := by simp only [JState.flagB, hflags]
  refine ⟨?_, ?_, ?_, hcorr.cfFlg⟩
  · intro r hr
    show ((ls.reg.setReg dst v).nextPc).getW r 64 = some (snew.regs r)
    rw [LstateN.getW_nextPc, hs r]
    by_cases hrd : r = dst
    · subst hrd; rw [LstateN.getW_setReg_same]; simp
    · rw [LstateN.getW_setReg_other _ _ _ _ _ hrd, hcorr.regAgree r hr, if_neg hrd]
  · intro base off
    show ls.lmem base off = snew.mem base off
    rw [hmem base off]; exact hcorr.memAgree base off
  · show ((ls.reg.setReg dst v).nextPc).getW cfN 1 = some (flagBit (snew.flagB (·.cf)))
    rw [hcf, LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_ne_cf)]
    exact hcorr.cfAgree

/-- **Per-opcode agreement for `.cmovb dst (.reg src)` under `JLstateCorrCF`.**
    The `CMOV` wire `[cfN, src, dst]` (condition slot, taken value, kept value —
    the `jToRMZ` operand order) does not fail and its result satisfies
    `JLstateCorrCF` with the SAME designated slot `cfN`: `cmovb` reads `CF` and
    writes no flag, so the slot carries over. The `JLstateCorrCF` counterpart of
    the `JLstateCorrZ`-packaged `cmov_case`. -/
theorem cmovb_caseCF (flg : String → Prop) (cfN dst src : String)
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem
          [ (cmovLinstr 64 dst [.reg cfN, .reg src, .reg dst], MemTag.reg none) ] ls
        = some ls' ∧
        JLstateCorrCF (runBlock s [.cmovb dst (.reg src)]) ls' flg cfN := by
  intro s ls hcorr
  have hstep : lsemStraightMem
      [ (cmovLinstr 64 dst [.reg cfN, .reg src, .reg dst], MemTag.reg none) ] ls
      = some { ls with reg := (ls.reg.setReg dst
          (selectW (flagBit (s.flagB (·.cf))) (s.regs src) (s.regs dst))).nextPc } := by
    rw [lsemStraightMem_single]
    exact lsemStepMem_cmov dst cfN src dst ls _ _ _ hcorr.cfAgree
      (hcorr.regAgree src hsrc) (hcorr.regAgree dst hdst)
  refine ⟨_, hstep, ?_⟩
  rw [selectW_flagBit]
  refine JLstateCorrCF_setReg s _ ls flg cfN hcorr dst _ hdst ?_ ?_ ?_
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.get,
      JOperand.eval]
  · intro base off
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]

/-! ## 3. The lsem lowering of the parametric block -/

/-- The lsem lowering of `condSubRoundJ`, threading the fresh borrow slots
    `fr0,…,fr4`: the seed `.sub` captures its borrow-out to `fr0` through the
    width-1 zero register `zc`; each register-source `.sbb` migrates the slot
    (`sbbColumnL`); the immediate `.sbb` materialises `0` in the synthetic
    register `z` and lands the final borrow in `fr4`; the four `CMOV` wires read
    `fr4` without writing any slot. -/
def condSubRoundL (r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop zc z
    fr0 fr1 fr2 fr3 fr4 : String) : List LinstrRM :=
  [ (LinstrR.Lopn [LOperand.reg fr0] (withWidthTag 64 "SBBHI")
      [LOperand.reg r0, LOperand.reg q0, LOperand.reg zc], MemTag.reg none),
    (LinstrR.Lopn [LOperand.reg r0] (withWidthTag 64 "SBB")
      [LOperand.reg r0, LOperand.reg q0, LOperand.reg zc], MemTag.reg none) ]
    ++ (sbbColumnL r1 q1 fr0 fr1
    ++ (sbbColumnL r2 q2 fr1 fr2
    ++ (sbbColumnL r3 q3 fr2 fr3
    ++ ([ (movImmLinstr 64 z 0, MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg fr4] (withWidthTag 64 "SBBHI")
            [LOperand.reg rtop, LOperand.reg z, LOperand.reg fr3], MemTag.reg none),
          (LinstrR.Lopn [LOperand.reg rtop] (withWidthTag 64 "SBB")
            [LOperand.reg rtop, LOperand.reg z, LOperand.reg fr3], MemTag.reg none) ]
    ++ ([ (cmovLinstr 64 r0 [.reg fr4, .reg v0, .reg r0], MemTag.reg none) ]
    ++ ([ (cmovLinstr 64 r1 [.reg fr4, .reg v1, .reg r1], MemTag.reg none) ]
    ++ ([ (cmovLinstr 64 r2 [.reg fr4, .reg v2, .reg r2], MemTag.reg none) ]
    ++  [ (cmovLinstr 64 r3 [.reg fr4, .reg v3, .reg r3], MemTag.reg none) ])))))))

/-! ## 4. The block agreement -/

/-- **Block agreement for the conditional-subtract round (CF entry).** Under the
    off-flag conditions on the data registers, the flag-name conditions on the
    fresh slots `fr0,…,fr4` and the materialising register `z`, the slot-chain
    distinctness, and a width-1 zero register `zc`, the whole round
    `condSubRoundJ` over `runBlock` corresponds — on the register (off flag),
    memory, and borrow-slot axes — to its lsem lowering `condSubRoundL` run to
    completion under `lsemStraightMem` (TOTALITY), landing in `JLstateCorrCF` at
    the final borrow slot `fr4` (the `.sbb rtop (.imm 0)` step's fresh slot,
    which the four `CMOV` wires read but do not migrate). Composition of
    `subSeed_case`, three `sbbColumn_agree`, `sbbImm_case`, and four
    `cmovb_caseCF` through `runBlock_lsem_agreeCF_seq_migrate`. -/
theorem condSubRound_lsem_agree (flg : String → Prop) (cfN : String)
    (r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop zc z fr0 fr1 fr2 fr3 fr4 : String)
    (hr0 : ¬ flg r0) (hr1 : ¬ flg r1) (hr2 : ¬ flg r2) (hr3 : ¬ flg r3)
    (hq0 : ¬ flg q0) (hq1 : ¬ flg q1) (hq2 : ¬ flg q2) (hq3 : ¬ flg q3)
    (hv0 : ¬ flg v0) (hv1 : ¬ flg v1) (hv2 : ¬ flg v2) (hv3 : ¬ flg v3)
    (hrtop : ¬ flg rtop)
    (hfr0 : flg fr0) (hfr1 : flg fr1) (hfr2 : flg fr2) (hfr3 : flg fr3)
    (hfr4 : flg fr4) (hz : flg z)
    (hzc0 : zc ≠ fr0) (h10 : fr1 ≠ fr0) (h21 : fr2 ≠ fr1) (h32 : fr3 ≠ fr2)
    (hz3 : z ≠ fr3) (hz4 : z ≠ fr4) (h43 : fr4 ≠ fr3)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorrCF s ls flg cfN)
    (hzero : ls.reg.getW zc 1 = some (flagBit false)) :
    ∃ ls', lsemStraightMem
        (condSubRoundL r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop zc z fr0 fr1 fr2 fr3 fr4)
        ls = some ls' ∧
      JLstateCorrCF (runBlock s (condSubRoundJ r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop))
        ls' flg fr4 := by
  have hne : ∀ {a b : String}, ¬ flg a → flg b → b ≠ a := fun ha hb h => ha (h ▸ hb)
  have hcol1 := sbbColumn_agree flg r1 q1 fr0 fr1 hr1 hq1 hfr1
    (hne hr1 hfr1) (hne hq1 hfr1) h10
  have hcol2 := sbbColumn_agree flg r2 q2 fr1 fr2 hr2 hq2 hfr2
    (hne hr2 hfr2) (hne hq2 hfr2) h21
  have hcol3 := sbbColumn_agree flg r3 q3 fr2 fr3 hr3 hq3 hfr3
    (hne hr3 hfr3) (hne hq3 hfr3) h32
  have hImm := fun (s : JState 64) (ls : LstateM) (h : JLstateCorrCF s ls flg fr3) =>
    sbbImm_case s ls flg fr3 h rtop z fr4 0 hrtop hz hfr4 hz3 hz4 h43
  have hcm0 := cmovb_caseCF flg fr4 r0 v0 hr0 hv0
  have hcm1 := cmovb_caseCF flg fr4 r1 v1 hr1 hv1
  have hcm2 := cmovb_caseCF flg fr4 r2 v2 hr2 hv2
  have hcm3 := cmovb_caseCF flg fr4 r3 v3 hr3 hv3
  have t7 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr4 fr4 fr4 hcm2 hcm3
  have t6 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr4 fr4 fr4 hcm1 t7
  have t5 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr4 fr4 fr4 hcm0 t6
  have t4 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr3 fr4 fr4 hImm t5
  have t3 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr2 fr3 fr4 hcol3 t4
  have t2 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr1 fr2 fr4 hcol2 t3
  have t1 := runBlock_lsem_agreeCF_seq_migrate _ _ _ _ flg fr0 fr1 fr4 hcol1 t2
  obtain ⟨ls1, e1, c1⟩ := subSeed_case s ls flg hcorr.regAgree hcorr.memAgree
    r0 q0 zc fr0 hzero hr0 hq0 hfr0 (hne hr0 hfr0).symm (hne hq0 hfr0).symm hzc0
  obtain ⟨ls', e', c'⟩ := t1 (runBlock s [.sub r0 (.reg q0)]) ls1 c1
  refine ⟨ls', ?_, ?_⟩
  · simp only [condSubRoundL]
    rw [lsemStraightMem_append, e1]
    exact e'
  · simp only [condSubRoundJ]
    rw [Jasmin.runBlock_append]
    exact c'

/-- **Block agreement for the conditional-subtract round (F entry).** The same
    agreement as `condSubRound_lsem_agree` from a dual-slot `JLstateCorrF` entry,
    via the `JLstateCorrCF_of_F` weakening: the round re-seeds the borrow with
    its leading `.sub`, so the incoming `CF` / `OF` slots are both discarded. -/
theorem condSubRound_lsem_agree_of_F (flg : String → Prop) (cfN ofN : String)
    (r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop zc z fr0 fr1 fr2 fr3 fr4 : String)
    (hr0 : ¬ flg r0) (hr1 : ¬ flg r1) (hr2 : ¬ flg r2) (hr3 : ¬ flg r3)
    (hq0 : ¬ flg q0) (hq1 : ¬ flg q1) (hq2 : ¬ flg q2) (hq3 : ¬ flg q3)
    (hv0 : ¬ flg v0) (hv1 : ¬ flg v1) (hv2 : ¬ flg v2) (hv3 : ¬ flg v3)
    (hrtop : ¬ flg rtop)
    (hfr0 : flg fr0) (hfr1 : flg fr1) (hfr2 : flg fr2) (hfr3 : flg fr3)
    (hfr4 : flg fr4) (hz : flg z)
    (hzc0 : zc ≠ fr0) (h10 : fr1 ≠ fr0) (h21 : fr2 ≠ fr1) (h32 : fr3 ≠ fr2)
    (hz3 : z ≠ fr3) (hz4 : z ≠ fr4) (h43 : fr4 ≠ fr3)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorrF s ls flg cfN ofN)
    (hzero : ls.reg.getW zc 1 = some (flagBit false)) :
    ∃ ls', lsemStraightMem
        (condSubRoundL r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop zc z fr0 fr1 fr2 fr3 fr4)
        ls = some ls' ∧
      JLstateCorrCF (runBlock s (condSubRoundJ r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop))
        ls' flg fr4 :=
  condSubRound_lsem_agree flg cfN r0 r1 r2 r3 q0 q1 q2 q3 v0 v1 v2 v3 rtop zc z
    fr0 fr1 fr2 fr3 fr4 hr0 hr1 hr2 hr3 hq0 hq1 hq2 hq3 hv0 hv1 hv2 hv3 hrtop
    hfr0 hfr1 hfr2 hfr3 hfr4 hz hzc0 h10 h21 h32 hz3 hz4 h43 s ls
    (JLstateCorrCF_of_F s ls flg cfN ofN hcorr) hzero

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSub
