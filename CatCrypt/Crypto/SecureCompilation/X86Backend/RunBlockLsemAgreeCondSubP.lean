/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontRedc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the emitted canonicalisation block

The emitted branch-free canonicalisation `Curve4MontMulProvenEmit.emitCondSubP` —
a `res ← window` refresh followed by `condSubRounds` copies of
`condSubRoundFull` (one conditional-subtract round, the save-copy refresh
`acc[4..7] ← res`, and a `xor rtop, rtop` top-word clear) — as one block
agreement between the total `runBlock` fold and its lsem lowering under the
single-slot correspondence `JLstateCorrCF`.

## The zero width-1 slot

`condSubRound`'s leading `.sub` reads a zero carry-in, so its lsem lowering
`RunBlockLsemAgreeCondSub.condSubRoundL` consumes a width-1 zero register `zc`.
Each round produces its own `zc` in-line from the current designated slot: with
`z` holding the 64-bit zero (one `MOV z, 0`), the wire `ADCXHI zc ← z, z, cfN`
writes `carryOutBit 0 0 _ = 0` for every carry-in (`carryOutBit_zero_zero`).

## The reseed after the top-word clear

The round's closing `xor rtop, rtop` resets the `JState` `CF`. The lowering
reseeds a fresh zero slot `zres` right after the clear (the same `MOV`/`ADCXHI`
gadget), which mirrors the zero `CF`; every round enters and leaves at `zres`,
so the rounds chain.

## Main results

* `movReg_caseCF`: per-opcode agreement for `.mov dst (.reg src)` under
  `JLstateCorrCF`, preserving the designated slot.
* `produceZeroSlot_caseCF`: the `MOV`/`ADCXHI` gadget producing a width-1 zero
  slot, preserving the designated slot.
* `xorReseed_caseCF`: the `xor d, d` top-word clear followed by the fresh-slot
  reseed, landing `JLstateCorrCF` at the reseeded slot.
* `condSubRoundZ_agree`: the zero-slot production composed with `condSubRound`.
* `condSubRoundFull_lsem_agree`: one full canonicalisation round, entering and
  leaving `JLstateCorrCF` at `zres`.
* `repeatRound_agree`: `n` chained full rounds.
* `emitCondSubP_lsem_agree`: the whole emitted canonicalisation block.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSubP

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSub
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontRedc
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The register-to-register `MOV` under `JLstateCorrCF` -/

/-- **Per-opcode agreement for `.mov dst (.reg src)` under `JLstateCorrCF`.**
    `x86_MOV` writes one data register and touches no flag, so the register-source
    move preserves the designated slot `cfN`. The `JLstateCorrCF` analogue of
    `movReg_caseF`. -/
theorem movReg_caseCF (flg : String → Prop) (cfN dst src : String)
    (hDst : ¬ flg dst) (hSrc : ¬ flg src) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem
          [ (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "MOV")
              [LOperand.reg src], MemTag.reg none) ] ls = some ls' ∧
        JLstateCorrCF (runBlock s [.mov dst (.reg src)]) ls' flg cfN := by
  intro s ls hcorr
  have hva : ls.reg.getW src 64 = some (s.regs src) := hcorr.regAgree src hSrc
  refine ⟨_, ?_, JLstateCorrCF_setReg s _ ls flg cfN hcorr dst (s.regs src) hDst ?_ ?_ ?_⟩
  · rw [lsemStraightMem_single]
    exact lsemStepMem_movReg dst src ls (s.regs src) hva
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.get,
      JState.setReg]
  · intro base off
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg]

/-! ## 2. The width-1 zero-slot production -/

/-- The two-wire lsem gadget producing a width-1 zero slot `zc`: `MOV z, 0`, then
    `ADCXHI zc ← z, z, cfN` writing `carryOutBit 0 0 _ = 0`. The junk carry-in is
    read from the current designated slot `cfN`. -/
def produceZeroSlotL (z zc cfN : String) : List LinstrRM :=
  [ (movImmLinstr 64 z 0, MemTag.reg none),
    (LinstrR.Lopn [LOperand.reg zc] (withWidthTag 64 "ADCXHI")
      [LOperand.reg z, LOperand.reg z, LOperand.reg cfN], MemTag.reg none) ]

/-- **The zero-slot production preserves the correspondence.** From a
    `JLstateCorrCF` entry at `cfN`, `produceZeroSlotL` does not fail, leaves the
    `JState` unchanged, preserves `JLstateCorrCF` at `cfN`, and lands a width-1
    zero in the fresh slot `zc`. -/
theorem produceZeroSlot_caseCF (flg : String → Prop) (cfN z zc : String)
    (hz : flg z) (hzc : flg zc) (hz_cf : z ≠ cfN) (hzc_cf : zc ≠ cfN) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (produceZeroSlotL z zc cfN) ls = some ls' ∧
        JLstateCorrCF s ls' flg cfN ∧ ls'.reg.getW zc 1 = some (flagBit false) := by
  intro s ls hcorr
  have e0 : lsemStepMem (movImmLinstr 64 z 0, MemTag.reg none) ls
      = some { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 0)).nextPc } :=
    lsemStepMem_movImm z 0 ls
  set ls0 : LstateM := { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 0)).nextPc } with hls0
  have hz0 : ls0.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls.reg.setReg z _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hcf0 : ls0.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls.reg.setReg z _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hz_cf)]
    exact hcorr.cfAgree
  have e1 := lsemStepMem_adcxhi3 zc z z cfN ls0 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz0 hz0 hcf0
  set ls1 : LstateM :=
    { ls0 with reg := (ls0.reg.setReg zc
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls1
  refine ⟨ls1, ?_, ?_, ?_⟩
  · simp only [produceZeroSlotL, lsemStraightMem_cons, e0, e1, lsemStraightMem_nil]
  · refine ⟨?_, ?_, ?_, hcorr.cfFlg⟩
    · intro r hr
      have hrz : r ≠ z := fun h => hr (h ▸ hz)
      have hrzc : r ≠ zc := fun h => hr (h ▸ hzc)
      show ((ls0.reg.setReg zc _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrzc]
      show ((ls.reg.setReg z _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrz]
      exact hcorr.regAgree r hr
    · intro base off
      show ls.lmem base off = s.mem base off
      exact hcorr.memAgree base off
    · show ((ls0.reg.setReg zc _).nextPc).getW cfN 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzc_cf)]
      exact hcf0
  · show ((ls0.reg.setReg zc _).nextPc).getW zc 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero]

/-! ## 3. The top-word clear with a fresh-slot reseed -/

/-- The three-wire lsem lowering of the closing `xor d, d`: the self-`XOR` data
    wire, then the zero-slot production reseeding `zres` from the junk carry-in
    slot `junkCF`. The reseeded slot mirrors the `CF` the `xor` reset to zero. -/
def xorReseedL (d z zres junkCF : String) : List LinstrRM :=
  (LinstrR.Lopn [LOperand.reg d] (withWidthTag 64 "XOR") [LOperand.reg d, LOperand.reg d],
     MemTag.reg none)
  :: produceZeroSlotL z zres junkCF

/-- **Block agreement for the top-word clear + reseed.** From a `JLstateCorrCF`
    entry at `junkCF`, `xorReseedL` does not fail and lands `JLstateCorrCF` at the
    reseeded slot `zres` (holding the zero the `xor` reset the `JState` `CF` to),
    matching the `runBlock` `.xor_ d (.reg d)`. -/
theorem xorReseed_caseCF (flg : String → Prop) (junkCF d z zres : String)
    (hd : ¬ flg d) (hz : flg z) (hzres : flg zres) (hz_junk : z ≠ junkCF) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg junkCF →
      ∃ ls', lsemStraightMem (xorReseedL d z zres junkCF) ls = some ls' ∧
        JLstateCorrCF (runBlock s [.xor_ d (.reg d)]) ls' flg zres := by
  intro s ls hcorr
  have hjunk_d : junkCF ≠ d := fun h => hd (h ▸ hcorr.cfFlg)
  have e1 := xorSelf_case s ls flg hcorr.regAgree d hd
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg d ((x86_XOR (s.regs d) (s.regs d)).word)).nextPc } with hls1
  set s' : JState 64 := runBlock s [.xor_ d (.reg d)] with hs'
  have hs'r : ∀ r, s'.regs r = if r = d then (x86_XOR (s.regs d) (s.regs d)).word
      else s.regs r := by
    intro r; rw [hs']
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, JOperand.eval, JState.get]
  have hreg1 : ∀ r, ¬ flg r → ls1.reg.getW r 64 = some (s'.regs r) :=
    regAgree_setReg_matched s ls flg hcorr.regAgree s' d _ hs'r
  have hmem1 : ∀ (base : String) (off : Int), ls1.lmem base off = s'.mem base off := by
    intro base off
    show ls.lmem base off = s'.mem base off
    rw [hs']; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    exact hcorr.memAgree base off
  have hcf1 : ls1.reg.getW junkCF 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls.reg.setReg d _).nextPc).getW junkCF 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hjunk_d]
    exact hcorr.cfAgree
  have e2 : lsemStepMem (movImmLinstr 64 z 0, MemTag.reg none) ls1
      = some { ls1 with reg := (ls1.reg.setReg z (BitVec.ofNat 64 0)).nextPc } :=
    lsemStepMem_movImm z 0 ls1
  set ls2 : LstateM := { ls1 with reg := (ls1.reg.setReg z (BitVec.ofNat 64 0)).nextPc } with hls2
  have hz2 : ls2.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls1.reg.setReg z _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hcf2 : ls2.reg.getW junkCF 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls1.reg.setReg z _).nextPc).getW junkCF 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hz_junk)]
    exact hcf1
  have e3 := lsemStepMem_adcxhi3 zres z z junkCF ls2 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz2 hz2 hcf2
  set ls3 : LstateM :=
    { ls2 with reg := (ls2.reg.setReg zres
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls3
  refine ⟨ls3, ?_, ?_⟩
  · simp only [xorReseedL, produceZeroSlotL, lsemStraightMem_cons, e1, e2, e3, lsemStraightMem_nil]
  · have hcfv : s'.flagB (·.cf) = false := by rw [hs']; exact flagB_cf_xorSelf s d
    refine ⟨?_, ?_, ?_, hzres⟩
    · intro r hr
      have hrz : r ≠ z := fun h => hr (h ▸ hz)
      have hrzres : r ≠ zres := fun h => hr (h ▸ hzres)
      show ((ls2.reg.setReg zres _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrzres]
      show ((ls1.reg.setReg z _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrz]
      exact hreg1 r hr
    · intro base off
      show ls1.lmem base off = s'.mem base off
      exact hmem1 base off
    · show ((ls2.reg.setReg zres _).nextPc).getW zres 1 = some (flagBit (s'.flagB (·.cf)))
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero, hcfv]

/-! ## 4. The per-round freshness bundle -/

/-- The freshness / non-aliasing side conditions of the canonicalisation block:
    the data registers (result / modulus-limb / saved-copy / top-word) off the
    flag namespace; the materialising register `z`, the per-round zero slot `zc`,
    the reseed slot `zres`, and the borrow slots `fr0,…,fr4` flag names; and the
    distinctness the zero-slot production, `condSubRound`, and the reseed need. -/
structure CondSubPFresh (flg : String → Prop) (z zc zres fr0 fr1 fr2 fr3 fr4 : String) :
    Prop where
  /-- result limb `r0` off the flag namespace -/
  r0R : ¬ flg "r0"
  /-- result limb `r1` off the flag namespace -/
  r1R : ¬ flg "r1"
  /-- result limb `r2` off the flag namespace -/
  r2R : ¬ flg "r2"
  /-- result limb `r3` off the flag namespace -/
  r3R : ¬ flg "r3"
  /-- modulus limb `p0` off the flag namespace -/
  p0R : ¬ flg "p0"
  /-- modulus limb `p1` off the flag namespace -/
  p1R : ¬ flg "p1"
  /-- modulus limb `p2` off the flag namespace -/
  p2R : ¬ flg "p2"
  /-- modulus limb `p3` off the flag namespace -/
  p3R : ¬ flg "p3"
  /-- saved copy `t4` off the flag namespace -/
  t4R : ¬ flg "t4"
  /-- saved copy `t5` off the flag namespace -/
  t5R : ¬ flg "t5"
  /-- saved copy `t6` off the flag namespace -/
  t6R : ¬ flg "t6"
  /-- saved copy `t7` off the flag namespace -/
  t7R : ¬ flg "t7"
  /-- top word off the flag namespace -/
  rtopR : ¬ flg rtopName
  /-- the materialising register is a flag name -/
  zF : flg z
  /-- the per-round zero slot is a flag name -/
  zcF : flg zc
  /-- the reseed slot is a flag name -/
  zresF : flg zres
  /-- borrow slot `fr0` is a flag name -/
  fr0F : flg fr0
  /-- borrow slot `fr1` is a flag name -/
  fr1F : flg fr1
  /-- borrow slot `fr2` is a flag name -/
  fr2F : flg fr2
  /-- borrow slot `fr3` is a flag name -/
  fr3F : flg fr3
  /-- borrow slot `fr4` is a flag name -/
  fr4F : flg fr4
  /-- `z` avoids the reseed slot -/
  z_zres : z ≠ zres
  /-- the zero slot avoids the reseed slot -/
  zc_zres : zc ≠ zres
  /-- the zero slot avoids the first borrow slot -/
  zc_fr0 : zc ≠ fr0
  /-- the borrow slots are distinct (1/0) -/
  fr1_fr0 : fr1 ≠ fr0
  /-- the borrow slots are distinct (2/1) -/
  fr2_fr1 : fr2 ≠ fr1
  /-- the borrow slots are distinct (3/2) -/
  fr3_fr2 : fr3 ≠ fr2
  /-- `z` avoids the fourth borrow slot -/
  z_fr3 : z ≠ fr3
  /-- `z` avoids the final borrow slot -/
  z_fr4 : z ≠ fr4
  /-- the borrow slots are distinct (4/3) -/
  fr4_fr3 : fr4 ≠ fr3

/-! ## 5. The zero-slot production composed with `condSubRound` -/

/-- The lsem lowering of `condSubRound` prefixed with the per-round zero-slot
    production: produce `zc` from the entry slot `zres`, then the parametric
    conditional-subtract round lowering at the concrete curve register names. -/
def condSubRoundZL (z zc zres fr0 fr1 fr2 fr3 fr4 : String) : List LinstrRM :=
  produceZeroSlotL z zc zres
    ++ condSubRoundL "r0" "r1" "r2" "r3" "p0" "p1" "p2" "p3" "t4" "t5" "t6" "t7" rtopName
        zc z fr0 fr1 fr2 fr3 fr4

/-- **Block agreement for the zero-slot production + `condSubRound`.** From a
    `JLstateCorrCF` entry at `zres`, the composite lowering does not fail and lands
    `JLstateCorrCF` at the final borrow slot `fr4`, matching the `runBlock`
    `condSubRound`. -/
theorem condSubRoundZ_agree (flg : String → Prop) (z zc zres fr0 fr1 fr2 fr3 fr4 : String)
    (hf : CondSubPFresh flg z zc zres fr0 fr1 fr2 fr3 fr4) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg zres →
      ∃ ls', lsemStraightMem (condSubRoundZL z zc zres fr0 fr1 fr2 fr3 fr4) ls = some ls' ∧
        JLstateCorrCF (runBlock s condSubRound) ls' flg fr4 := by
  intro s ls hcorr
  obtain ⟨ls1, e1, c1, hzero1⟩ :=
    produceZeroSlot_caseCF flg zres z zc hf.zF hf.zcF hf.z_zres hf.zc_zres s ls hcorr
  obtain ⟨ls', e', c'⟩ := condSubRound_concrete_lsem_agree flg zres zc z fr0 fr1 fr2 fr3 fr4
    hf.r0R hf.r1R hf.r2R hf.r3R hf.p0R hf.p1R hf.p2R hf.p3R hf.t4R hf.t5R hf.t6R hf.t7R hf.rtopR
    hf.fr0F hf.fr1F hf.fr2F hf.fr3F hf.fr4F hf.zF hf.zc_fr0 hf.fr1_fr0 hf.fr2_fr1 hf.fr3_fr2
    hf.z_fr3 hf.z_fr4 hf.fr4_fr3 s ls1 c1 hzero1
  refine ⟨ls', ?_, c'⟩
  simp only [condSubRoundZL]
  rw [lsemStraightMem_append, e1]
  exact e'

/-! ## 6. One full canonicalisation round -/

/-- The four saved-copy refresh moves `acc[4..7] ← res[0..3]` as register pairs. -/
def savePairs : List (String × String) :=
  (List.range 4).map (fun k => (accNames.getD (k + 4) default, resNames.getD k default))

/-- The four `res ← window` moves `res[0..3] ← acc[4..7]` as register pairs. -/
def windowPairs : List (String × String) :=
  (List.range 4).map (fun k => (resNames.getD k default, accNames.getD (k + 4) default))

/-- The lsem lowering of a register-to-register `MOV` pair. -/
def movPairWire (p : String × String) : LinstrRM :=
  (LinstrR.Lopn [LOperand.reg p.1] (withWidthTag 64 "MOV") [LOperand.reg p.2], MemTag.reg none)

/-- **Block agreement for a register-to-register `MOV` list under
    `JLstateCorrCF`.** Every pair's data registers off the flag namespace, the
    whole list preserves the designated slot `cfN`. Straight-line induction, each
    move via `movReg_caseCF`. -/
theorem movRegPairs_agreeCF (flg : String → Prop) (cfN : String) :
    ∀ (ps : List (String × String)), (∀ p ∈ ps, ¬ flg p.1 ∧ ¬ flg p.2) →
      ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
        ∃ ls', lsemStraightMem (ps.map movPairWire) ls = some ls' ∧
          JLstateCorrCF (runBlock s (ps.map (fun p => JInstr.mov p.1 (.reg p.2)))) ls' flg cfN := by
  intro ps
  induction ps with
  | nil => intro _ s ls h; exact ⟨ls, rfl, h⟩
  | cons p ps ih =>
    intro hmem
    obtain ⟨hp1, hp2⟩ := hmem p (List.mem_cons_self ..)
    have htail := ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))
    have hcomp := runBlock_lsem_agreeCF_seq_migrate
      [JInstr.mov p.1 (.reg p.2)] (ps.map (fun p => JInstr.mov p.1 (.reg p.2)))
      [movPairWire p] (ps.map movPairWire) flg cfN cfN cfN
      (movReg_caseCF flg cfN p.1 p.2 hp1 hp2) htail
    intro s ls h
    simpa only [List.map_cons, List.singleton_append] using hcomp s ls h

/-- The lsem lowering of one full canonicalisation round: the zero-slot
    production + `condSubRound`, the saved-copy refresh, and the top-word clear
    with its reseed. -/
def condSubRoundFullL (z zc zres fr0 fr1 fr2 fr3 fr4 : String) : List LinstrRM :=
  condSubRoundZL z zc zres fr0 fr1 fr2 fr3 fr4
    ++ savePairs.map movPairWire
    ++ xorReseedL rtopName z zres fr4

/-- **Block agreement for one full canonicalisation round.** From a
    `JLstateCorrCF` entry at `zres`, `condSubRoundFullL` does not fail and lands
    `JLstateCorrCF` back at `zres`, matching the `runBlock` `condSubRoundFull`.
    Composition of `condSubRoundZ_agree`, `movRegPairs_agreeCF`, and
    `xorReseed_caseCF` via `runBlock_lsem_agreeCF_seq_migrate`. -/
theorem condSubRoundFull_lsem_agree (flg : String → Prop)
    (z zc zres fr0 fr1 fr2 fr3 fr4 : String)
    (hf : CondSubPFresh flg z zc zres fr0 fr1 fr2 fr3 fr4) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg zres →
      ∃ ls', lsemStraightMem (condSubRoundFullL z zc zres fr0 fr1 fr2 fr3 fr4) ls = some ls' ∧
        JLstateCorrCF (runBlock s condSubRoundFull) ls' flg zres := by
  have hsaveMem : ∀ p ∈ savePairs, ¬ flg p.1 ∧ ¬ flg p.2 := by
    intro p hp
    have hsp : savePairs = [("t4", "r0"), ("t5", "r1"), ("t6", "r2"), ("t7", "r3")] := rfl
    rw [hsp] at hp
    fin_cases hp <;>
      exact ⟨by first | exact hf.t4R | exact hf.t5R | exact hf.t6R | exact hf.t7R,
             by first | exact hf.r0R | exact hf.r1R | exact hf.r2R | exact hf.r3R⟩
  have hA := condSubRoundZ_agree flg z zc zres fr0 fr1 fr2 fr3 fr4 hf
  have hB := movRegPairs_agreeCF flg fr4 savePairs hsaveMem
  have hC := xorReseed_caseCF flg fr4 rtopName z zres hf.rtopR hf.zF hf.zresF hf.z_fr4
  have hAB := runBlock_lsem_agreeCF_seq_migrate condSubRound
    (savePairs.map (fun p => JInstr.mov p.1 (.reg p.2)))
    (condSubRoundZL z zc zres fr0 fr1 fr2 fr3 fr4) (savePairs.map movPairWire)
    flg zres fr4 fr4 hA hB
  have hABC := runBlock_lsem_agreeCF_seq_migrate
    (condSubRound ++ savePairs.map (fun p => JInstr.mov p.1 (.reg p.2)))
    [JInstr.xor_ rtopName (.reg rtopName)]
    (condSubRoundZL z zc zres fr0 fr1 fr2 fr3 fr4 ++ savePairs.map movPairWire)
    (xorReseedL rtopName z zres fr4) flg zres fr4 zres hAB hC
  intro s ls h
  have hEq : condSubRoundFull
      = (condSubRound ++ savePairs.map (fun p => JInstr.mov p.1 (.reg p.2)))
          ++ [JInstr.xor_ rtopName (.reg rtopName)] := rfl
  rw [hEq]
  exact hABC s ls h

/-! ## 7. The chained rounds and the whole block -/

/-- The source of `n` chained full canonicalisation rounds. -/
def roundsJ (n : Nat) : List (JInstr 64) :=
  (List.range n).flatMap (fun _ => condSubRoundFull)

/-- The lsem lowering of `n` chained full canonicalisation rounds, each entering
    and leaving at `zres`. -/
def roundsL (z zc zres fr0 fr1 fr2 fr3 fr4 : String) (n : Nat) : List LinstrRM :=
  (List.range n).flatMap (fun _ => condSubRoundFullL z zc zres fr0 fr1 fr2 fr3 fr4)

/-- **Block agreement for `n` chained full canonicalisation rounds.** From a
    `JLstateCorrCF` entry at `zres`, `roundsL n` does not fail and lands
    `JLstateCorrCF` back at `zres`, matching `runBlock (roundsJ n)`. Induction on
    `n`, each round via `condSubRoundFull_lsem_agree`. -/
theorem repeatRound_agree (flg : String → Prop)
    (z zc zres fr0 fr1 fr2 fr3 fr4 : String)
    (hf : CondSubPFresh flg z zc zres fr0 fr1 fr2 fr3 fr4) :
    ∀ (n : Nat) (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg zres →
      ∃ ls', lsemStraightMem (roundsL z zc zres fr0 fr1 fr2 fr3 fr4 n) ls = some ls' ∧
        JLstateCorrCF (runBlock s (roundsJ n)) ls' flg zres := by
  intro n
  induction n with
  | zero => intro s ls h; exact ⟨ls, rfl, h⟩
  | succ n ih =>
    have hstep := condSubRoundFull_lsem_agree flg z zc zres fr0 fr1 fr2 fr3 fr4 hf
    have hcomp := runBlock_lsem_agreeCF_seq_migrate (roundsJ n) condSubRoundFull
      (roundsL z zc zres fr0 fr1 fr2 fr3 fr4 n) (condSubRoundFullL z zc zres fr0 fr1 fr2 fr3 fr4)
      flg zres zres zres ih hstep
    intro s ls h
    have hJ : roundsJ (n + 1) = roundsJ n ++ condSubRoundFull := by
      simp only [roundsJ, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    have hL : roundsL z zc zres fr0 fr1 fr2 fr3 fr4 (n + 1)
        = roundsL z zc zres fr0 fr1 fr2 fr3 fr4 n ++ condSubRoundFullL z zc zres fr0 fr1 fr2 fr3 fr4 := by
      simp only [roundsL, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    rw [hJ, hL]
    exact hcomp s ls h

/-- The lsem lowering of the whole emitted canonicalisation block: the
    `res ← window` refresh, then `condSubRounds` chained full rounds. -/
def emitCondSubPL (z zc zres fr0 fr1 fr2 fr3 fr4 : String) : List LinstrRM :=
  windowPairs.map movPairWire
    ++ roundsL z zc zres fr0 fr1 fr2 fr3 fr4 condSubRounds

/-- **Block agreement for the emitted canonicalisation block.** From a
    `JLstateCorrCF` entry at the reseed slot `zres`, the whole
    `emitCondSubP` over `runBlock` corresponds to `emitCondSubPL` run to
    completion, landing `JLstateCorrCF` back at `zres`. The `res ← window` refresh
    via `movRegPairs_agreeCF`, then `repeatRound_agree` for the `condSubRounds`
    rounds, composed with `runBlock_lsem_agreeCF_seq_migrate`. -/
theorem emitCondSubP_lsem_agree (flg : String → Prop)
    (z zc zres fr0 fr1 fr2 fr3 fr4 : String)
    (hf : CondSubPFresh flg z zc zres fr0 fr1 fr2 fr3 fr4) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg zres →
      ∃ ls', lsemStraightMem (emitCondSubPL z zc zres fr0 fr1 fr2 fr3 fr4) ls = some ls' ∧
        JLstateCorrCF (runBlock s emitCondSubP) ls' flg zres := by
  have hwindowMem : ∀ p ∈ windowPairs, ¬ flg p.1 ∧ ¬ flg p.2 := by
    intro p hp
    have hwp : windowPairs = [("r0", "t4"), ("r1", "t5"), ("r2", "t6"), ("r3", "t7")] := rfl
    rw [hwp] at hp
    fin_cases hp <;>
      exact ⟨by first | exact hf.r0R | exact hf.r1R | exact hf.r2R | exact hf.r3R,
             by first | exact hf.t4R | exact hf.t5R | exact hf.t6R | exact hf.t7R⟩
  have hW := movRegPairs_agreeCF flg zres windowPairs hwindowMem
  have hR := repeatRound_agree flg z zc zres fr0 fr1 fr2 fr3 fr4 hf condSubRounds
  have hcomp := runBlock_lsem_agreeCF_seq_migrate
    (windowPairs.map (fun p => JInstr.mov p.1 (.reg p.2))) (roundsJ condSubRounds)
    (windowPairs.map movPairWire) (roundsL z zc zres fr0 fr1 fr2 fr3 fr4 condSubRounds)
    flg zres zres zres hW hR
  intro s ls h
  have hEq : emitCondSubP
      = windowPairs.map (fun p => JInstr.mov p.1 (.reg p.2)) ++ roundsJ condSubRounds := rfl
  rw [hEq]
  exact hcomp s ls h

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSubP
