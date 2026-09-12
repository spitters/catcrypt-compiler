/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSub
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeColumnReset
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the emitted Montgomery reduce block

The 4-limb emitted Montgomery reduce `Curve4MontMulProvenEmit.emitMontRedc4Block`
— four chained reduce word-steps `emitMontRedcStepAt i`, each a flag-clearing
`xor` prologue, a digit column + `m·p` accumulate row (`emitMontRedcStep`), a
flag-seeding carry-fold `add`, and an immediate-`adc` carry-propagation chain —
as one block agreement between the total `runBlock` fold and its lsem lowering
under the designated-slot correspondences `JLstateCorrCF` / `JLstateCorrF`.

## The width-1 zero-slot production

The lsem carry wires read their carry-in from a width-1 slot register, and the
immediate-`MOV` wire materialises only widths 32/64, so a width-1 zero cannot be
written directly. The gadget used here produces one from any current width-1
slot: with `z` holding the 64-bit zero (one `MOV z, 0`), the wire
`ADCXHI zc ← z, z, c` writes `carryOutBit 0 0 vc`, which is `0` for **every**
carry-in `vc` (`carryOutBit_zero_zero`). This supplies

* the two zero slots that mirror `CF = OF = 0` after the `xor` prologue
  (`clearTriple_case`), and
* the zero carry-in the mid-block flag-seeding `add` needs (`addSeedMid_case`),
  without any ambient zero-register invariant.

## The `xor` flag-reset entry

`JState`'s `.xor_` writes its result through `x86_XOR = rflags_of_bwop`, which
sets `CF = OF = false`. The lsem `XOR` wire records only the data word, so the
prologue lowering appends the two zero-slot productions above and the block
lands in `JLstateCorrF` at the freshly-zeroed pair — the flag-reset entry the
reduce step's MAC chain requires.

## Main results

* `carryOutBit_zero_zero`: `carryOutBit 0 0 vc = 0` for every width-1 `vc`.
* `xorSelf_case` / `flagB_cf_xorSelf` / `flagB_of_xorSelf`: the self-`XOR` wire
  equation and the `CF`/`OF` reset of the `JState` `.xor_`.
* `clearTripleJ` / `clearTripleL` / `clearTriple_case`: the three-`xor` prologue
  block agreement, `JLstateCorrCF` entry to `JLstateCorrF` at the zeroed pair.
* `addSeedMidL` / `addSeedMid_case`: the flag-seeding `.add dst (.reg src)` from
  a `JLstateCorrCF` entry, with the zero carry-in produced in-line.
* `adcImmChainL` / `AdcImmChainFresh` / `adcImmChain_agree`: the immediate-`adc`
  carry-propagation chain, slot-migrating, via `adcImm_case`.
* `montStepCore_agree`: `emitMontRedcStep` (digit column + accumulate row) under
  `JLstateCorrF`, from `emitColumnReset_lsem_agree` / `emitRowBlock_lsem_agree`.
* `montRedcStepJ_lsem_agree` / `emitMontRedcStepAt_lsem_agree`: one reduce
  word-step, `JLstateCorrCF` to `JLstateCorrCF`.
* `emitMontRedc4Block_lsem_agree`: the four chained reduce word-steps.
* `condSubRound_concrete_lsem_agree`: the emit module's `condSubRound` — the
  parametric `condSubRoundJ` at the concrete curve register names — inherits the
  parametric block agreement.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontRedc

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddSeed
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeAddImm
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSub
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeColumnReset
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The width-1 zero-slot production -/

/-- The carry-out of `0 + 0 + vc` is `0` for every width-1 carry-in `vc`: the sum
    is at most `1`, below `2 ^ 64`. The value fact behind the zero-slot production
    wire `ADCXHI zc ← z, z, c` (with `z` the 64-bit zero). -/
theorem carryOutBit_zero_zero (vc : BitVec 1) :
    carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) vc = flagBit false := by
  have h : vc.toNat < 2 := vc.isLt
  simp only [carryOutBit, flagBit, BitVec.toNat_ofNat]
  norm_num
  omega

/-! ## 2. The self-`XOR` wire and the `JState` flag reset -/

/-- **The lsem twin of the self-`XOR` wire** of `.xor_ d (.reg d)`: the
    two-address `regArith` `XOR` wire writes `(x86_XOR v v).word` to `d` and does
    not fail, given `d` reads back the `JState` value. -/
theorem xorSelf_case (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (hreg : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r))
    (d : String) (hd : ¬ flg d) :
    lsemStepMem (.Lopn [.reg d] (withWidthTag 64 "XOR") [.reg d, .reg d], MemTag.reg none) ls
      = some { ls with reg := (ls.reg.setReg d ((x86_XOR (s.regs d) (s.regs d)).word)).nextPc } := by
  have hva : ls.reg.getW d 64 = some (s.regs d) := hreg d hd
  exact lsemStepMem_regArith d "XOR" (.reg d) ls
    (stripWidthTag_withWidthTag_binOpName' 64 .xor) (by decide) (by decide) (by decide) (by decide)
    (s.regs d) (s.regs d) _ hva (by simpa [evalOperandN] using hva) rfl

/-- The `JState` `.xor_` resets `CF`: `x86_XOR` routes through `rflags_of_bwop`,
    whose `cf` is `some false`. -/
theorem flagB_cf_xorSelf (s : JState 64) (d : String) :
    (evalInstr s (JInstr.xor_ d (.reg d))).flagB (·.cf) = false := by
  simp only [evalInstr, JState.flagB, JState.writeB5W_flags, x86_XOR, rflags_of_bwop,
    Option.getD_some]

/-- The `JState` `.xor_` resets `OF`: `x86_XOR` routes through `rflags_of_bwop`,
    whose `of` is `some false`. -/
theorem flagB_of_xorSelf (s : JState 64) (d : String) :
    (evalInstr s (JInstr.xor_ d (.reg d))).flagB (·.of) = false := by
  simp only [evalInstr, JState.flagB, JState.writeB5W_flags, x86_XOR, rflags_of_bwop,
    Option.getD_some]

/-- Off-flag register agreement is preserved by a matched register write: if the
    `JState` result writes `w` to `d` and leaves the other registers, and the lsem
    side writes the same `w` to `d`, the width-64 agreement off `flg` carries
    over. The raw-agreement core shared by the per-wire steps of this module. -/
theorem regAgree_setReg_matched (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (hreg : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r))
    (snew : JState 64) (d : String) (w : BitVec 64)
    (hs : ∀ r, snew.regs r = if r = d then w else s.regs r) :
    ∀ r : String, ¬ flg r → ((ls.reg.setReg d w).nextPc).getW r 64 = some (snew.regs r) := by
  intro r hr
  rw [LstateN.getW_nextPc, hs r]
  by_cases hrd : r = d
  · subst hrd; rw [LstateN.getW_setReg_same]; simp
  · rw [LstateN.getW_setReg_other _ _ _ _ _ hrd, hreg r hr, if_neg hrd]

/-! ## 3. The three-`xor` flag-clearing prologue -/

/-- The reduce word-step's clearing prologue: zero the digit accumulator, the
    digit carry, and the row carry by self-`xor`, resetting `CF = OF = 0` (the
    last `xor`). The first three instructions of
    `Curve4MontMulProvenEmit.emitMontRedcStepAt`. -/
def clearTripleJ (m dcy rcy : String) : List (JInstr 64) :=
  [JInstr.xor_ m (.reg m), JInstr.xor_ dcy (.reg dcy), JInstr.xor_ rcy (.reg rcy)]

/-- The lsem lowering of the clearing prologue: the three self-`XOR` data wires,
    then the zero-slot production — `MOV z, 0` and two `ADCXHI` wires writing
    `carryOutBit 0 0 _ = 0` to the fresh slots `zc1` / `zc2`, which mirror the
    reset `CF` / `OF`. The junk carry-in is read from the incoming slot `cfN`. -/
def clearTripleL (m dcy rcy z cfN zc1 zc2 : String) : List LinstrRM :=
  [ (.Lopn [.reg m] (withWidthTag 64 "XOR") [.reg m, .reg m], MemTag.reg none),
    (.Lopn [.reg dcy] (withWidthTag 64 "XOR") [.reg dcy, .reg dcy], MemTag.reg none),
    (.Lopn [.reg rcy] (withWidthTag 64 "XOR") [.reg rcy, .reg rcy], MemTag.reg none),
    (movImmLinstr 64 z 0, MemTag.reg none),
    (.Lopn [.reg zc1] (withWidthTag 64 "ADCXHI") [.reg z, .reg z, .reg cfN], MemTag.reg none),
    (.Lopn [.reg zc2] (withWidthTag 64 "ADCXHI") [.reg z, .reg z, .reg cfN], MemTag.reg none) ]

/-- **Block agreement for the clearing prologue (the flag-reset entry).** From a
    `JLstateCorrCF` entry at any slot `cfN`, the prologue `clearTripleJ` over
    `runBlock` corresponds to `clearTripleL` run to completion, landing in the
    dual-slot `JLstateCorrF` at the freshly-zeroed pair `(zc1, zc2)` — which
    mirrors the `CF = OF = 0` the three `JState` `xor`s establish. -/
theorem clearTriple_case (flg : String → Prop) (cfN m dcy rcy z zc1 zc2 : String)
    (hm : ¬ flg m) (hdcy : ¬ flg dcy) (hrcy : ¬ flg rcy)
    (hz : flg z) (hzc1 : flg zc1) (hzc2 : flg zc2)
    (hzcf : z ≠ cfN) (h1z : zc1 ≠ z) (h1cf : zc1 ≠ cfN) (h21 : zc2 ≠ zc1) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (clearTripleL m dcy rcy z cfN zc1 zc2) ls = some ls' ∧
        JLstateCorrF (runBlock s (clearTripleJ m dcy rcy)) ls' flg zc1 zc2 := by
  intro s ls hcorr
  have hne : ∀ {a b : String}, ¬ flg a → flg b → b ≠ a := fun ha hb h => ha (h ▸ hb)
  have hcfN_m : cfN ≠ m := hne hm hcorr.cfFlg
  have hcfN_dcy : cfN ≠ dcy := hne hdcy hcorr.cfFlg
  have hcfN_rcy : cfN ≠ rcy := hne hrcy hcorr.cfFlg
  -- Step 1: `XOR m, m`.
  have e1 := xorSelf_case s ls flg hcorr.regAgree m hm
  set s1 : JState 64 := evalInstr s (JInstr.xor_ m (.reg m)) with hs1
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg m ((x86_XOR (s.regs m) (s.regs m)).word)).nextPc } with hls1
  have hs1r : ∀ r, s1.regs r = if r = m then (x86_XOR (s.regs m) (s.regs m)).word
      else s.regs r := by
    intro r; rw [hs1]; simp only [evalInstr, JState.writeB5W, JOperand.eval, JState.get]
  have hreg1 : ∀ r, ¬ flg r → ls1.reg.getW r 64 = some (s1.regs r) :=
    regAgree_setReg_matched s ls flg hcorr.regAgree s1 m _ hs1r
  have hmem1 : ∀ (base : String) (off : Int), ls1.lmem base off = s1.mem base off := by
    intro base off
    show ls.lmem base off = s1.mem base off
    rw [hs1]; simp only [evalInstr, JState.writeB5W]
    exact hcorr.memAgree base off
  have hcf1 : ls1.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls.reg.setReg m _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hcfN_m]
    exact hcorr.cfAgree
  -- Step 2: `XOR dcy, dcy`.
  have e2 := xorSelf_case s1 ls1 flg hreg1 dcy hdcy
  set s2 : JState 64 := evalInstr s1 (JInstr.xor_ dcy (.reg dcy)) with hs2
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dcy ((x86_XOR (s1.regs dcy) (s1.regs dcy)).word)).nextPc }
    with hls2
  have hs2r : ∀ r, s2.regs r = if r = dcy then (x86_XOR (s1.regs dcy) (s1.regs dcy)).word
      else s1.regs r := by
    intro r; rw [hs2]; simp only [evalInstr, JState.writeB5W, JOperand.eval, JState.get]
  have hreg2 : ∀ r, ¬ flg r → ls2.reg.getW r 64 = some (s2.regs r) :=
    regAgree_setReg_matched s1 ls1 flg hreg1 s2 dcy _ hs2r
  have hmem2 : ∀ (base : String) (off : Int), ls2.lmem base off = s2.mem base off := by
    intro base off
    show ls1.lmem base off = s2.mem base off
    rw [hs2]; simp only [evalInstr, JState.writeB5W]
    exact hmem1 base off
  have hcf2 : ls2.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls1.reg.setReg dcy _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hcfN_dcy]
    exact hcf1
  -- Step 3: `XOR rcy, rcy` — the flag reset.
  have e3 := xorSelf_case s2 ls2 flg hreg2 rcy hrcy
  set s3 : JState 64 := evalInstr s2 (JInstr.xor_ rcy (.reg rcy)) with hs3
  set ls3 : LstateM :=
    { ls2 with reg := (ls2.reg.setReg rcy ((x86_XOR (s2.regs rcy) (s2.regs rcy)).word)).nextPc }
    with hls3
  have hs3r : ∀ r, s3.regs r = if r = rcy then (x86_XOR (s2.regs rcy) (s2.regs rcy)).word
      else s2.regs r := by
    intro r; rw [hs3]; simp only [evalInstr, JState.writeB5W, JOperand.eval, JState.get]
  have hreg3 : ∀ r, ¬ flg r → ls3.reg.getW r 64 = some (s3.regs r) :=
    regAgree_setReg_matched s2 ls2 flg hreg2 s3 rcy _ hs3r
  have hmem3 : ∀ (base : String) (off : Int), ls3.lmem base off = s3.mem base off := by
    intro base off
    show ls2.lmem base off = s3.mem base off
    rw [hs3]; simp only [evalInstr, JState.writeB5W]
    exact hmem2 base off
  have hcf3 : ls3.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls2.reg.setReg rcy _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hcfN_rcy]
    exact hcf2
  -- the reset flags of the post-prologue `JState`
  have hcf3v : s3.flagB (·.cf) = false := by rw [hs3]; exact flagB_cf_xorSelf s2 rcy
  have hof3v : s3.flagB (·.of) = false := by rw [hs3]; exact flagB_of_xorSelf s2 rcy
  -- Step 4: `MOV z, 0`.
  have e4 : lsemStepMem (movImmLinstr 64 z 0, MemTag.reg none) ls3
      = some { ls3 with reg := (ls3.reg.setReg z (BitVec.ofNat 64 0)).nextPc } :=
    lsemStepMem_movImm z 0 ls3
  set ls4 : LstateM := { ls3 with reg := (ls3.reg.setReg z (BitVec.ofNat 64 0)).nextPc } with hls4
  have hz4 : ls4.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls3.reg.setReg z _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hcf4 : ls4.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls3.reg.setReg z _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzcf)]
    exact hcf3
  -- Step 5: `ADCXHI zc1 ← z, z, cfN` — the `CF` zero slot.
  have e5 := lsemStepMem_adcxhi3 zc1 z z cfN ls4 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz4 hz4 hcf4
  set ls5 : LstateM :=
    { ls4 with reg := (ls4.reg.setReg zc1
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls5
  have hz5 : ls5.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls4.reg.setReg zc1 _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h1z)]
    exact hz4
  have hcf5 : ls5.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls4.reg.setReg zc1 _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h1cf)]
    exact hcf4
  -- Step 6: `ADCXHI zc2 ← z, z, cfN` — the `OF` zero slot.
  have e6 := lsemStepMem_adcxhi3 zc2 z z cfN ls5 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz5 hz5 hcf5
  set ls6 : LstateM :=
    { ls5 with reg := (ls5.reg.setReg zc2
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls6
  refine ⟨ls6, ?_, ?_⟩
  · simp only [clearTripleL, lsemStraightMem_cons, e1, e2, e3, e4, e5, e6, lsemStraightMem_nil]
  · have hrunEq : runBlock s (clearTripleJ m dcy rcy) = s3 := by
      rw [hs3, hs2, hs1]
      simp only [clearTripleJ, runBlock_cons, runBlock_nil]
    rw [hrunEq]
    refine ⟨?_, ?_, ?_, ?_, hzc1, hzc2, Ne.symm h21⟩
    · -- regAgree off flg
      intro r hr
      have hr1 : r ≠ zc1 := fun h => hr (h ▸ hzc1)
      have hr2 : r ≠ zc2 := fun h => hr (h ▸ hzc2)
      have hrz : r ≠ z := fun h => hr (h ▸ hz)
      show ((ls5.reg.setReg zc2 _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hr2]
      show ((ls4.reg.setReg zc1 _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hr1]
      show ((ls3.reg.setReg z _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrz]
      exact hreg3 r hr
    · -- memAgree
      intro base off
      show ls3.lmem base off = s3.mem base off
      exact hmem3 base off
    · -- cfAgree at the `CF` zero slot `zc1`
      show ((ls5.reg.setReg zc2 _).nextPc).getW zc1 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h21)]
      show ((ls4.reg.setReg zc1 _).nextPc).getW zc1 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero, hcf3v]
    · -- ofAgree at the `OF` zero slot `zc2`
      show ((ls5.reg.setReg zc2 _).nextPc).getW zc2 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero, hof3v]

/-! ## 4. The mid-block flag-seeding `add` -/

/-- The lsem lowering of a mid-block flag-seeding `.add dst (.reg src)`: produce
    a width-1 zero slot `zc` in-line (`MOV z, 0`, then `ADCXHI zc ← z, z, cfN`
    with the current slot as junk carry-in), then the seed pair
    `ADCXHI fr ← dst, src, zc` / `ADCX dst ← dst, src, zc` capturing the
    carry-out to the fresh slot `fr`. -/
def addSeedMidL (dst src z zc fr cfN : String) : List LinstrRM :=
  [ (movImmLinstr 64 z 0, MemTag.reg none),
    (.Lopn [.reg zc] (withWidthTag 64 "ADCXHI") [.reg z, .reg z, .reg cfN], MemTag.reg none),
    (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
      [.reg dst, .reg src, .reg zc], MemTag.reg none),
    (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
      [.reg dst, .reg src, .reg zc], MemTag.reg none) ]

/-- **Block agreement for the mid-block flag-seeding `add`.** From a
    `JLstateCorrCF` entry at `cfN`, the four-wire lowering `addSeedMidL` does not
    fail and lands in `JLstateCorrCF` at the fresh carry slot `fr`, matching the
    `runBlock` `.add dst (.reg src)`. The zero carry-in is produced in-line, so
    no ambient zero-register invariant is required (unlike `addSeed_case`). -/
theorem addSeedMid_case (flg : String → Prop) (cfN dst src z zc fr : String)
    (hdst : ¬ flg dst) (hsrc : ¬ flg src)
    (hz : flg z) (hzc : flg zc) (hfr : flg fr)
    (hzcf : z ≠ cfN) (hzcfr : zc ≠ fr) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (addSeedMidL dst src z zc fr cfN) ls = some ls' ∧
        JLstateCorrCF (runBlock s [.add dst (.reg src)]) ls' flg fr := by
  intro s ls hcorr
  -- Step 0: `MOV z, 0`.
  have e0 : lsemStepMem (movImmLinstr 64 z 0, MemTag.reg none) ls
      = some { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 0)).nextPc } :=
    lsemStepMem_movImm z 0 ls
  set ls0 : LstateM := { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 0)).nextPc } with hls0
  have hz0 : ls0.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls.reg.setReg z _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hcf0 : ls0.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls.reg.setReg z _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzcf)]
    exact hcorr.cfAgree
  -- Step 1: `ADCXHI zc ← z, z, cfN` — the zero slot.
  have e1 := lsemStepMem_adcxhi3 zc z z cfN ls0 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz0 hz0 hcf0
  set ls1 : LstateM :=
    { ls0 with reg := (ls0.reg.setReg zc
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls1
  have hreg1 : ∀ r, ¬ flg r → ls1.reg.getW r 64 = some (s.regs r) := by
    intro r hr
    have hrz : r ≠ z := fun h => hr (h ▸ hz)
    have hrzc : r ≠ zc := fun h => hr (h ▸ hzc)
    show ((ls0.reg.setReg zc _).nextPc).getW r 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrzc]
    show ((ls.reg.setReg z _).nextPc).getW r 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrz]
    exact hcorr.regAgree r hr
  have hmem1 : ∀ (base : String) (off : Int), ls1.lmem base off = s.mem base off := by
    intro base off
    show ls.lmem base off = s.mem base off
    exact hcorr.memAgree base off
  have hzero1 : ls1.reg.getW zc 1 = some (flagBit false) := by
    show ((ls0.reg.setReg zc _).nextPc).getW zc 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero]
  -- Steps 2–3: the seed pair, via `addSeed_case` on the intermediate state.
  obtain ⟨ls', etail, hcorr'⟩ := addSeed_case s ls1 flg hreg1 hmem1 dst src zc fr hzero1
    hdst hsrc hfr (fun h => hdst (h ▸ hfr)) (fun h => hsrc (h ▸ hfr)) hzcfr
  refine ⟨ls', ?_, hcorr'⟩
  have hsplit : addSeedMidL dst src z zc fr cfN
      = [ (movImmLinstr 64 z 0, MemTag.reg none),
          (.Lopn [.reg zc] (withWidthTag 64 "ADCXHI")
            [.reg z, .reg z, .reg cfN], MemTag.reg none) ]
        ++ [ (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
              [.reg dst, .reg src, .reg zc], MemTag.reg none),
             (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
              [.reg dst, .reg src, .reg zc], MemTag.reg none) ] := rfl
  have e01 : lsemStraightMem
      [ (movImmLinstr 64 z 0, MemTag.reg none),
        (.Lopn [.reg zc] (withWidthTag 64 "ADCXHI")
          [.reg z, .reg z, .reg cfN], MemTag.reg none) ] ls = some ls1 := by
    simp only [lsemStraightMem_cons, e0, e1, lsemStraightMem_nil]
  rw [hsplit, lsemStraightMem_append, e01, Option.bind]
  exact etail

/-! ## 5. The immediate-`adc` carry-propagation chain -/

/-- The three-wire lsem lowering of one `.adc dst (.imm 0)` fold-chain limb
    reading the slot `cfN` and migrating to the fresh slot `fr` — the list
    `adcImm_case` bridges, at literal `0`. -/
def adcImmColumnL (dst z cfN fr : String) : List LinstrRM :=
  [ (movImmLinstr 64 z 0, MemTag.reg none),
    (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
      [.reg dst, .reg z, .reg cfN], MemTag.reg none),
    (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
      [.reg dst, .reg z, .reg cfN], MemTag.reg none) ]

/-- `adcImm_case` at literal `0`, repackaged in the `∀ s ls, JLstateCorrCF → …`
    shape the chain lift consumes. -/
theorem adcImmColumn_agree (flg : String → Prop) (dst z cfN fr : String)
    (hdst : ¬ flg dst) (hz : flg z) (hfr : flg fr)
    (hzcf : z ≠ cfN) (hzfr : z ≠ fr) (hfrcf : fr ≠ cfN) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (adcImmColumnL dst z cfN fr) ls = some ls' ∧
        JLstateCorrCF (runBlock s [.adc dst (.imm 0)]) ls' flg fr := by
  intro s ls hcorr
  exact adcImm_case s ls flg cfN hcorr dst z fr 0 hdst hz hfr hzcf hzfr hfrcf

/-- The source-side fold chain: one `.adc d (.imm 0)` per destination. -/
def adcImmChainJ (ds : List String) : List (JInstr 64) :=
  ds.map (fun d => JInstr.adc d (.imm 0))

/-- The lsem lowering of a whole `.adc _ (.imm 0)` chain, threading the fresh
    carry slots `frs` (one per limb) from the initial slot `cf0`, with the shared
    materialising register `z`. -/
def adcImmChainL (z : String) : String → List String → List String → List LinstrRM
  | cf0, d :: ds, fr :: frs => adcImmColumnL d z cf0 fr ++ adcImmChainL z fr ds frs
  | _, _, _ => []

/-- The freshness side conditions of the `.adc _ (.imm 0)` chain: at each limb
    `d` with fresh slot `fr`, the destination is off the flag namespace, `fr` is
    a flag name distinct from the materialising register and the current slot,
    and `z` avoids the current slot; `frs` has one slot per limb. -/
def AdcImmChainFresh (flg : String → Prop) (z : String) :
    String → List String → List String → Prop
  | _, [], [] => True
  | cf0, d :: ds, fr :: frs =>
      ¬ flg d ∧ flg fr ∧ z ≠ cf0 ∧ z ≠ fr ∧ fr ≠ cf0 ∧ AdcImmChainFresh flg z fr ds frs
  | _, _, _ => False

/-- **The `.adc _ (.imm 0)` chain block lift.** Under the freshness fold, the
    whole fold chain runs to completion under `lsemStraightMem` on the threaded
    lowering and its result corresponds — on the register (off flag), memory, and
    carry-slot axes — to the `runBlock` fold, migrating the slot `cf0` to
    `finalSlot cf0 frs`. Straight-line induction, each limb via
    `adcImmColumn_agree`, composed with `runBlock_lsem_agreeCF_seq_migrate`. -/
theorem adcImmChain_agree (flg : String → Prop) (z : String) (hz : flg z) :
    ∀ (ds frs : List String) (cf0 : String), AdcImmChainFresh flg z cf0 ds frs →
      ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cf0 →
        ∃ ls', lsemStraightMem (adcImmChainL z cf0 ds frs) ls = some ls' ∧
          JLstateCorrCF (runBlock s (adcImmChainJ ds)) ls' flg (finalSlot cf0 frs) := by
  intro ds
  induction ds with
  | nil =>
    intro frs cf0 hfresh s ls h
    match frs, hfresh with
    | [], _ => exact ⟨ls, rfl, h⟩
  | cons d ds ih =>
    intro frs cf0 hfresh s ls h
    match frs, hfresh with
    | fr :: rest, hfresh =>
      obtain ⟨hd, hfr, hzcf, hzfr, hfrcf, htail⟩ := hfresh
      have hcol := adcImmColumn_agree flg d z cf0 fr hd hz hfr hzcf hzfr hfrcf
      have htl := ih rest fr htail
      have hcomp := runBlock_lsem_agreeCF_seq_migrate
        [.adc d (.imm 0)] (adcImmChainJ ds)
        (adcImmColumnL d z cf0 fr) (adcImmChainL z fr ds rest)
        flg cf0 fr (finalSlot fr rest) hcol htl s ls h
      simpa only [adcImmChainL, adcImmChainJ, finalSlot, List.map_cons,
        List.singleton_append] using hcomp

/-! ## 6. Composition across correspondence changes -/

/-- **Sequential composition across a correspondence change.** Two bridged blocks
    compose when the first lands in the correspondence the second consumes; the
    output correspondence is the second's. Generalises the fixed-axis and
    slot-migrating sequential compositions to arbitrary state relations. -/
theorem agree_seq_corr {P Q R : JState 64 → LstateM → Prop}
    (b1 b2 : List (JInstr 64)) (lb1 lb2 : List LinstrRM)
    (h1 : ∀ (s : JState 64) (ls : LstateM), P s ls →
      ∃ ls', lsemStraightMem lb1 ls = some ls' ∧ Q (runBlock s b1) ls')
    (h2 : ∀ (s : JState 64) (ls : LstateM), Q s ls →
      ∃ ls', lsemStraightMem lb2 ls = some ls' ∧ R (runBlock s b2) ls') :
    ∀ (s : JState 64) (ls : LstateM), P s ls →
      ∃ ls', lsemStraightMem (lb1 ++ lb2) ls = some ls' ∧
        R (runBlock s (b1 ++ b2)) ls' := by
  intro s ls h
  obtain ⟨ls1, e1, c1⟩ := h1 s ls h
  obtain ⟨ls2, e2, c2⟩ := h2 (runBlock s b1) ls1 c1
  refine ⟨ls2, ?_, ?_⟩
  · rw [lsemStraightMem_append, e1, Option.bind]; exact e2
  · rw [Jasmin.runBlock_append]; exact c2

/-! ## 7. The reduce word-step core: digit column + accumulate row -/

/-- The lsem lowering of `emitMontRedcStep` (the digit column, then the `m·p`
    accumulate row): one `columnResetL` for the digit, then `rowResetL` over the
    window/modulus register zip, threading the carry namespace through the digit
    column's slot pairs into the per-column row slots. -/
def montStepCoreL (z m t0 np dcy hi lo : String) (win pN : List String)
    (rcy cf0 of0 c1 o1 c2 o2 : String)
    (rs : List ((String × String) × (String × String))) : List LinstrRM :=
  columnResetL z m t0 np dcy hi lo cf0 of0 c1 o1 c2 o2
    ++ rowResetL z m rcy hi lo c2 o2 (win.zip pN) rs

/-- **Block agreement for the reduce word-step core.** Under the digit column's
    `ColumnResetFresh` and the accumulate row's `RowResetFresh`, the
    `emitMontRedcStep` block over `runBlock` corresponds to `montStepCoreL` run
    to completion, migrating the carry namespace `(cf0, of0)` through the digit
    column to the row's final pair. Composition of `emitColumnReset_lsem_agree`
    and `emitRowBlock_lsem_agree` via `runBlock_lsem_agreeF_seq_migrate`. -/
theorem montStepCore_agree (flg : String → Prop)
    (z m t0 np dcy hi lo rcy : String) (win pN : List String)
    (cf0 of0 c1 o1 c2 o2 : String)
    (rs : List ((String × String) × (String × String)))
    (hcol : ColumnResetFresh flg z m t0 np dcy hi lo cf0 of0 c1 o1 c2 o2)
    (hrow : RowResetFresh flg z m rcy hi lo c2 o2 (win.zip pN) rs) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cf0 of0 →
      ∃ ls', lsemStraightMem
          (montStepCoreL z m t0 np dcy hi lo win pN rcy cf0 of0 c1 o1 c2 o2 rs) ls = some ls' ∧
        JLstateCorrF (runBlock s (emitMontRedcStep m t0 np dcy hi lo win pN rcy hi lo)) ls'
          flg (rowFinal (c2, o2) rs).1 (rowFinal (c2, o2) rs).2 := by
  intro s ls h
  have hcolA := emitColumnReset_lsem_agree flg z m t0 np dcy hi lo cf0 of0 c1 o1 c2 o2 hcol
  have hrowA := emitRowBlock_lsem_agree flg z m rcy hi lo win pN rs c2 o2 hrow
  have hcomp := runBlock_lsem_agreeF_seq_migrate
    (emitColumnReset m t0 np dcy hi lo) (emitRowBlock win pN m rcy hi lo)
    (columnResetL z m t0 np dcy hi lo cf0 of0 c1 o1 c2 o2)
    (rowResetL z m rcy hi lo c2 o2 (win.zip pN) rs)
    flg cf0 of0 c2 o2 (rowFinal (c2, o2) rs).1 (rowFinal (c2, o2) rs).2 hcolA hrowA s ls h
  simpa only [montStepCoreL, emitMontRedcStep, emitMontDigit] using hcomp

/-! ## 8. One reduce word-step -/

/-- The per-step lsem slot data: the prologue zero pair, the digit column's two
    slot pairs, the per-column row slots, the seed's zero and carry slots, and
    the fold chain's slot list. -/
structure StepSlots where
  /-- the prologue `CF` zero slot -/
  zc1 : String
  /-- the prologue `OF` zero slot -/
  zc2 : String
  /-- the digit column's MAC fresh `CF` slot -/
  c1 : String
  /-- the digit column's MAC fresh `OF` slot -/
  o1 : String
  /-- the digit column's gadget fresh `CF` slot -/
  c2 : String
  /-- the digit column's gadget fresh `OF` slot -/
  o2 : String
  /-- the accumulate row's per-column slot pair pairs -/
  rs : List ((String × String) × (String × String))
  /-- the seed's in-line zero slot -/
  zcS : String
  /-- the seed's fresh carry slot -/
  frS : String
  /-- the fold chain's fresh carry slots -/
  frs : List String

/-- The carry slot one reduce word-step ends in: the fold chain's final slot. -/
def stepFinal (sl : StepSlots) : String := finalSlot sl.frS sl.frs

/-- One reduce word-step as a source block, parametric over the register names
    and window lists: the clearing prologue, the digit + accumulate core, the
    flag-seeding carry-fold `add`, and the immediate-`adc` fold chain. At the
    concrete names this is `Curve4MontMulProvenEmit.emitMontRedcStepAt`
    (`emitMontRedcStepAt_eq`). -/
def montRedcStepJ (m dcy rcy t0 np hi lo : String) (win pN : List String)
    (nextW : String) (foldDsts : List String) : List (JInstr 64) :=
  clearTripleJ m dcy rcy
    ++ emitMontRedcStep m t0 np dcy hi lo win pN rcy hi lo
    ++ [JInstr.add nextW (.reg rcy)]
    ++ adcImmChainJ foldDsts

/-- The lsem lowering of one reduce word-step: the prologue, core, seed, and
    fold-chain lowerings threaded through the step's slot data. -/
def montRedcStepL (z m dcy rcy t0 np hi lo nextW : String)
    (win pN foldDsts : List String) (cfIn : String) (sl : StepSlots) : List LinstrRM :=
  clearTripleL m dcy rcy z cfIn sl.zc1 sl.zc2
    ++ montStepCoreL z m t0 np dcy hi lo win pN rcy sl.zc1 sl.zc2 sl.c1 sl.o1 sl.c2 sl.o2 sl.rs
    ++ addSeedMidL nextW rcy z sl.zcS sl.frS (rowFinal (sl.c2, sl.o2) sl.rs).1
    ++ adcImmChainL z sl.frS foldDsts sl.frs

/-- The freshness side conditions of one reduce word-step: the data registers off
    the flag namespace, the prologue zero pair fresh against the materialising
    register and the incoming slot, the digit column's `ColumnResetFresh`, the
    row's `RowResetFresh`, the seed's slots fresh against the row's final `CF`
    slot, and the fold chain's `AdcImmChainFresh`. -/
structure StepFresh (flg : String → Prop) (z m dcy rcy t0 np hi lo nextW : String)
    (win pN foldDsts : List String) (cfIn : String) (sl : StepSlots) : Prop where
  /-- the materialising register is a flag name -/
  zF : flg z
  /-- the digit accumulator is off the flag namespace -/
  mR : ¬ flg m
  /-- the digit carry is off the flag namespace -/
  dcyR : ¬ flg dcy
  /-- the row carry is off the flag namespace -/
  rcyR : ¬ flg rcy
  /-- the carry-fold destination is off the flag namespace -/
  nextWR : ¬ flg nextW
  /-- the prologue `CF` zero slot is a flag name -/
  zc1F : flg sl.zc1
  /-- the prologue `OF` zero slot is a flag name -/
  zc2F : flg sl.zc2
  /-- `z` avoids the incoming slot -/
  z_cfIn : z ≠ cfIn
  /-- the prologue `CF` slot avoids `z` -/
  zc1_z : sl.zc1 ≠ z
  /-- the prologue `CF` slot avoids the incoming slot -/
  zc1_cfIn : sl.zc1 ≠ cfIn
  /-- the prologue slots are distinct -/
  zc2_zc1 : sl.zc2 ≠ sl.zc1
  /-- the digit column's freshness -/
  colFresh : ColumnResetFresh flg z m t0 np dcy hi lo sl.zc1 sl.zc2 sl.c1 sl.o1 sl.c2 sl.o2
  /-- the accumulate row's freshness -/
  rowFresh : RowResetFresh flg z m rcy hi lo sl.c2 sl.o2 (win.zip pN) sl.rs
  /-- the seed's zero slot is a flag name -/
  zcSF : flg sl.zcS
  /-- the seed's carry slot is a flag name -/
  frSF : flg sl.frS
  /-- `z` avoids the row's final `CF` slot -/
  z_rf : z ≠ (rowFinal (sl.c2, sl.o2) sl.rs).1
  /-- the seed's slots are distinct -/
  zcS_frS : sl.zcS ≠ sl.frS
  /-- the fold chain's freshness -/
  chainFresh : AdcImmChainFresh flg z sl.frS foldDsts sl.frs

/-- **Block agreement for one reduce word-step (parametric).** From a
    `JLstateCorrCF` entry at `cfIn`, the step `montRedcStepJ` over `runBlock`
    corresponds to `montRedcStepL` run to completion, landing in `JLstateCorrCF`
    at the fold chain's final slot. Composition of `clearTriple_case`,
    `montStepCore_agree`, `addSeedMid_case` (through the `JLstateCorrCF_of_F`
    weakening), and `adcImmChain_agree` via `agree_seq_corr`. -/
theorem montRedcStepJ_lsem_agree (flg : String → Prop)
    (z m dcy rcy t0 np hi lo nextW : String) (win pN foldDsts : List String)
    (cfIn : String) (sl : StepSlots)
    (hf : StepFresh flg z m dcy rcy t0 np hi lo nextW win pN foldDsts cfIn sl) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfIn →
      ∃ ls', lsemStraightMem
          (montRedcStepL z m dcy rcy t0 np hi lo nextW win pN foldDsts cfIn sl) ls = some ls' ∧
        JLstateCorrCF (runBlock s (montRedcStepJ m dcy rcy t0 np hi lo win pN nextW foldDsts))
          ls' flg (stepFinal sl) := by
  have hA := clearTriple_case flg cfIn m dcy rcy z sl.zc1 sl.zc2 hf.mR hf.dcyR hf.rcyR
    hf.zF hf.zc1F hf.zc2F hf.z_cfIn hf.zc1_z hf.zc1_cfIn hf.zc2_zc1
  have hB := montStepCore_agree flg z m t0 np dcy hi lo rcy win pN sl.zc1 sl.zc2
    sl.c1 sl.o1 sl.c2 sl.o2 sl.rs hf.colFresh hf.rowFresh
  have hC : ∀ (s : JState 64) (ls : LstateM),
      JLstateCorrF s ls flg (rowFinal (sl.c2, sl.o2) sl.rs).1 (rowFinal (sl.c2, sl.o2) sl.rs).2 →
      ∃ ls', lsemStraightMem
          (addSeedMidL nextW rcy z sl.zcS sl.frS (rowFinal (sl.c2, sl.o2) sl.rs).1) ls
          = some ls' ∧
        JLstateCorrCF (runBlock s [.add nextW (.reg rcy)]) ls' flg sl.frS := by
    intro s ls h
    exact addSeedMid_case flg (rowFinal (sl.c2, sl.o2) sl.rs).1 nextW rcy z sl.zcS sl.frS
      hf.nextWR hf.rcyR hf.zF hf.zcSF hf.frSF hf.z_rf hf.zcS_frS s ls
      (JLstateCorrCF_of_F s ls flg _ _ h)
  have hD := adcImmChain_agree flg z hf.zF foldDsts sl.frs sl.frS hf.chainFresh
  have hAB := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrF s ls flg sl.zc1 sl.zc2)
    (R := fun s ls => JLstateCorrF s ls flg
      (rowFinal (sl.c2, sl.o2) sl.rs).1 (rowFinal (sl.c2, sl.o2) sl.rs).2)
    _ _ _ _ hA hB
  have hABC := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrF s ls flg
      (rowFinal (sl.c2, sl.o2) sl.rs).1 (rowFinal (sl.c2, sl.o2) sl.rs).2)
    (R := fun s ls => JLstateCorrCF s ls flg sl.frS)
    _ _ _ _ hAB hC
  have hABCD := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrCF s ls flg sl.frS)
    (R := fun s ls => JLstateCorrCF s ls flg (finalSlot sl.frS sl.frs))
    _ _ _ _ hABC hD
  intro s ls h
  simpa only [montRedcStepJ, montRedcStepL, stepFinal] using hABCD s ls h

/-! ## 9. The concrete reduce word-steps and the four-step block -/

/-- The accumulator window of reduce word-step `i`. -/
def stepWin (i : Nat) : List String := (accNames.drop i).take 4

/-- The low window register of reduce word-step `i` (the digit source). -/
def stepT0 (i : Nat) : String := (stepWin i).headD default

/-- The carry-fold destination of reduce word-step `i`. -/
def stepNextW (i : Nat) : String := accNames.getD (i + 4) default

/-- The fold-chain destinations of reduce word-step `i`: every accumulator word
    strictly above the fold destination, then the top-carry word. -/
def stepFoldDsts (i : Nat) : List String :=
  (List.range (accNames.length - (i + 5))).map (fun j => accNames.getD (i + 5 + j) default)
    ++ [rtopName]

/-- `emitMontRedcStepAt i` is `montRedcStepJ` at the emit module's register names
    and the step-`i` window data. -/
theorem emitMontRedcStepAt_eq (i : Nat) :
    emitMontRedcStepAt i
      = montRedcStepJ mName dcyName rcyName (stepT0 i) npName hiName loName
          (stepWin i) pNames (stepNextW i) (stepFoldDsts i) := by
  simp only [emitMontRedcStepAt, montRedcStepJ, clearTripleJ, adcImmChainJ, stepT0, stepWin,
    stepNextW, stepFoldDsts, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, List.append_assoc]

/-- The lsem lowering of reduce word-step `i` at the emit module's register
    names. -/
def montRedcStepAtL (z : String) (i : Nat) (cfIn : String) (sl : StepSlots) : List LinstrRM :=
  montRedcStepL z mName dcyName rcyName (stepT0 i) npName hiName loName
    (stepNextW i) (stepWin i) pNames (stepFoldDsts i) cfIn sl

/-- The step-`i` freshness at the emit module's register names. -/
def StepFreshAt (flg : String → Prop) (z : String) (i : Nat) (cfIn : String)
    (sl : StepSlots) : Prop :=
  StepFresh flg z mName dcyName rcyName (stepT0 i) npName hiName loName (stepNextW i)
    (stepWin i) pNames (stepFoldDsts i) cfIn sl

/-- **Block agreement for `emitMontRedcStepAt i`.** The parametric step agreement
    at the emit module's register names and the step-`i` window data. -/
theorem emitMontRedcStepAt_lsem_agree (i : Nat) (flg : String → Prop) (z cfIn : String)
    (sl : StepSlots) (hf : StepFreshAt flg z i cfIn sl) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfIn →
      ∃ ls', lsemStraightMem (montRedcStepAtL z i cfIn sl) ls = some ls' ∧
        JLstateCorrCF (runBlock s (emitMontRedcStepAt i)) ls' flg (stepFinal sl) := by
  intro s ls h
  rw [emitMontRedcStepAt_eq i]
  exact montRedcStepJ_lsem_agree flg z mName dcyName rcyName (stepT0 i) npName hiName loName
    (stepNextW i) (stepWin i) pNames (stepFoldDsts i) cfIn sl hf s ls h

/-- The lsem lowering of the four chained reduce word-steps, each entering at the
    previous step's final slot. -/
def montRedc4L (z cf0 : String) (sl0 sl1 sl2 sl3 : StepSlots) : List LinstrRM :=
  montRedcStepAtL z 0 cf0 sl0
    ++ montRedcStepAtL z 1 (stepFinal sl0) sl1
    ++ montRedcStepAtL z 2 (stepFinal sl1) sl2
    ++ montRedcStepAtL z 3 (stepFinal sl2) sl3

/-- **Block agreement for `emitMontRedc4Block`.** From a `JLstateCorrCF` entry at
    `cf0`, the four chained reduce word-steps over `runBlock` correspond to
    `montRedc4L` run to completion (TOTALITY), landing in `JLstateCorrCF` at the
    last step's final slot. Four applications of
    `emitMontRedcStepAt_lsem_agree`, composed with `agree_seq_corr`. -/
theorem emitMontRedc4Block_lsem_agree (flg : String → Prop) (z cf0 : String)
    (sl0 sl1 sl2 sl3 : StepSlots)
    (hf0 : StepFreshAt flg z 0 cf0 sl0)
    (hf1 : StepFreshAt flg z 1 (stepFinal sl0) sl1)
    (hf2 : StepFreshAt flg z 2 (stepFinal sl1) sl2)
    (hf3 : StepFreshAt flg z 3 (stepFinal sl2) sl3) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cf0 →
      ∃ ls', lsemStraightMem (montRedc4L z cf0 sl0 sl1 sl2 sl3) ls = some ls' ∧
        JLstateCorrCF (runBlock s emitMontRedc4Block) ls' flg (stepFinal sl3) := by
  have h0 := emitMontRedcStepAt_lsem_agree 0 flg z cf0 sl0 hf0
  have h1 := emitMontRedcStepAt_lsem_agree 1 flg z (stepFinal sl0) sl1 hf1
  have h2 := emitMontRedcStepAt_lsem_agree 2 flg z (stepFinal sl1) sl2 hf2
  have h3 := emitMontRedcStepAt_lsem_agree 3 flg z (stepFinal sl2) sl3 hf3
  have h01 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cf0)
    (Q := fun s ls => JLstateCorrCF s ls flg (stepFinal sl0))
    (R := fun s ls => JLstateCorrCF s ls flg (stepFinal sl1))
    _ _ _ _ h0 h1
  have h012 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cf0)
    (Q := fun s ls => JLstateCorrCF s ls flg (stepFinal sl1))
    (R := fun s ls => JLstateCorrCF s ls flg (stepFinal sl2))
    _ _ _ _ h01 h2
  have hall := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cf0)
    (Q := fun s ls => JLstateCorrCF s ls flg (stepFinal sl2))
    (R := fun s ls => JLstateCorrCF s ls flg (stepFinal sl3))
    _ _ _ _ h012 h3
  intro s ls h
  simpa only [emitMontRedc4Block, montRedc4L] using hall s ls h

/-! ## 10. The conditional-subtract round at the concrete names -/

/-- **Block agreement for the emit module's `condSubRound`.** The parametric
    round agreement `condSubRound_lsem_agree` at the emit module's concrete
    register names: results `r0..r3`, modulus limbs `p0..p3`, saved copies
    `t4..t7`, top word `rtop`. -/
theorem condSubRound_concrete_lsem_agree (flg : String → Prop) (cfN zc z : String)
    (fr0 fr1 fr2 fr3 fr4 : String)
    (hr0 : ¬ flg "r0") (hr1 : ¬ flg "r1") (hr2 : ¬ flg "r2") (hr3 : ¬ flg "r3")
    (hq0 : ¬ flg "p0") (hq1 : ¬ flg "p1") (hq2 : ¬ flg "p2") (hq3 : ¬ flg "p3")
    (hv0 : ¬ flg "t4") (hv1 : ¬ flg "t5") (hv2 : ¬ flg "t6") (hv3 : ¬ flg "t7")
    (hrtop : ¬ flg rtopName)
    (hfr0 : flg fr0) (hfr1 : flg fr1) (hfr2 : flg fr2) (hfr3 : flg fr3)
    (hfr4 : flg fr4) (hz : flg z)
    (hzc0 : zc ≠ fr0) (h10 : fr1 ≠ fr0) (h21 : fr2 ≠ fr1) (h32 : fr3 ≠ fr2)
    (hz3 : z ≠ fr3) (hz4 : z ≠ fr4) (h43 : fr4 ≠ fr3)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorrCF s ls flg cfN)
    (hzero : ls.reg.getW zc 1 = some (flagBit false)) :
    ∃ ls', lsemStraightMem
        (condSubRoundL "r0" "r1" "r2" "r3" "p0" "p1" "p2" "p3" "t4" "t5" "t6" "t7" rtopName
          zc z fr0 fr1 fr2 fr3 fr4) ls = some ls' ∧
      JLstateCorrCF (runBlock s condSubRound) ls' flg fr4 := by
  exact condSubRound_lsem_agree flg cfN "r0" "r1" "r2" "r3" "p0" "p1" "p2" "p3"
    "t4" "t5" "t6" "t7" rtopName zc z fr0 fr1 fr2 fr3 fr4
    hr0 hr1 hr2 hr3 hq0 hq1 hq2 hq3 hv0 hv1 hv2 hv3 hrtop
    hfr0 hfr1 hfr2 hfr3 hfr4 hz hzc0 h10 h21 h32 hz3 hz4 h43 s ls hcorr hzero

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontRedc
