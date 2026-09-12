/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the flag readers

`RunBlockLsemAgree.lean` bridges the total `JState` fold `runBlock` and the
partial `LstateM` fold `lsemStraightMem` on the register ALU core, the
compile-time-offset word memory, the two-write `mulx`, and the flag WRITERS
(`adcx` / `adox` / `sbb`, carried by the designated-slot correspondences
`JLstateCorrF` / `JLstateCorrCF`). This module covers the flag READERS: `setc`
(materialises `CF`), `cmovb` (reads `CF`), and `cmove` / `cmovne` (read `ZF`).

## The correspondence

`JLstateCorrZ s ls flg cfN zfN` is `JLstateCorrF` with the `OF` axis replaced by
`ZF`: register agreement off the synthetic flag namespace `flg`, memory agreement
cell-for-cell, and two designated width-1 slots `cfN` / `zfN` (both in `flg`,
distinct) mirroring `s.flags.cf` / `s.flags.zf`.

## The lowerings

Each reader is a single lsem instruction, so `jToRMZ` is single-valued and the
block lift runs over `b.map (jToRMZ cfN zfN)`, mirroring `runBlock_lsem_agree`.

* `setc dst` → the bare-mnemonic cast wire `Lopn [.reg dst] "ZEROEXT" [.reg cfN]`
  under the cast descriptor `MemTag.reg (some 64)`. `lsemStepCast` writes
  `(flagBit CF).zeroExtend 64`, which is the model's `if CF then 1 else 0`.
* `cmovb dst (.reg src)` → the `CMOV` wire
  `Lopn [.reg dst] "CMOV:64" [.reg cfN, .reg src, .reg dst]`. `lsemStepN`'s
  width-mixing arm writes `selectW CF src dst`, which is `x86_CMOVcc CF src dst`.
* `cmove dst (.reg src)` → the same wire on `zfN`.
* `cmovne dst (.reg src)` → the same wire on `zfN` with the two data operands
  **swapped** (`[.reg zfN, .reg dst, .reg src]`): the sense of the condition is
  carried by the operand order, so no negated flag slot is needed.

The three `cmov` arms take a REGISTER source: `lsemStepN`'s `CMOV` arm recovers
the data width from the second operand's store tag (`readReg`), which is `none`
on an immediate.

## Flag transparency

All four opcodes write one register and touch no flag (`evalInstr`'s `setc` /
`cmove` / `cmovne` / `cmovb` arms are `JState.setReg`), so each preserves both
designated slots. That is what lets a block of them thread a single pair of
slots, and it is why the flag-clobbering ALU ops (`add` … `xor_`, whose
`writeB5W` rewrites all five flags) stay outside `InFlagReaderSubset`. The
flag-transparent immediate `mov` is inside it.

## Main results

* `JLstateCorrZ`: the register/memory/CF/ZF correspondence, `JLstateCorrF` with
  `OF` replaced by a designated `ZF` slot.
* `InFlagReaderSubset` / `jToRMZ`: the flag-reading opcodes and their wires.
* `lsemStepMem_cmov`, `lsemStepMem_zeroext1`: the raw-wire step lemmas.
* `jToRMZ_agrees`, `runBlock_lsem_agreeZ`: per-opcode agreement and its block lift.
* `JLstateCorrZ_setLpc`: the correspondence absorbs a program-counter reset.
* `runBlock_lsem_agreeZ_loop`: the counted-loop lift, threading both designated
  slots across the back-edge.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCmov

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The lsem twins of the reader wires -/

/-- The five structured recognizers of `lsemStepMC`, and `sarStruct?`, are all
    `none` on a `CMOV` wire, so `lsemStepMem` on such a wire delegates down to
    `lsemStepN`'s width-mixing `CMOV` arm. Stated once so that no call site pays a
    mnemonic decision. -/
theorem cmovWire_delegates (dst : String) (srcs : List LOperand) :
    mulhiStruct? (cmovLinstr 64 dst srcs) = none ∧
    adcxStruct? (cmovLinstr 64 dst srcs) = none ∧
    adcxhiStruct? (cmovLinstr 64 dst srcs) = none ∧
    sbbStruct? (cmovLinstr 64 dst srcs) = none ∧
    sbbhiStruct? (cmovLinstr 64 dst srcs) = none ∧
    sarStruct? (cmovLinstr 64 dst srcs) = none := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := struct?_select (w := 64) dst srcs
  exact ⟨h1, h2, h3, h4, h5, sarStruct?_select (w := 64) dst srcs⟩

/-- **The lsem twin of a `CMOV` wire.** With the condition slot `cond` readable at
    width 1 and both data operands readable at width 64, `lsemStepMem` writes
    `selectW vc va vb` to `dst`; it does not fail. -/
theorem lsemStepMem_cmov (dst cond a b : String) (ls : LstateM)
    (vc : BitVec 1) (va vb : BitVec 64)
    (hvc : ls.reg.getW cond 1 = some vc)
    (hva : ls.reg.getW a 64 = some va)
    (hvb : ls.reg.getW b 64 = some vb) :
    lsemStepMem
        (cmovLinstr 64 dst [.reg cond, .reg a, .reg b], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (selectW vc va vb)).nextPc } := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cmovWire_delegates dst [.reg cond, .reg a, .reg b]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ h1 h2 h3 h4 h5, lsemStepSh_of_not_sar _ _ h6]
  simp only [cmovLinstr, lsemStepN, stripWidthTag_withWidthTag_CMOV, if_pos, operandName, hvc,
    readReg_of_getW hva, evalOperandN, hvb, Option.map_some]

/-- `castStruct?` recognises the bare-mnemonic `ZEROEXT` wire. -/
theorem castStruct?_zeroext (dst a : String) :
    castStruct? (zeroextLinstr dst a) = some (dst, a) := by
  simp [castStruct?, zeroextLinstr]

/-- **The lsem twin of a `ZEROEXT` wire under the width-64 cast descriptor.** With
    the source `a` holding a width-1 word, `lsemStepMem` writes its zero-extension
    to `dst` at width 64; it does not fail. -/
theorem lsemStepMem_zeroext1 (dst a : String) (ls : LstateM) (va : BitVec 1)
    (hva : ls.reg.getW a 1 = some va) :
    lsemStepMem (zeroextLinstr dst a, .reg (some 64)) ls
      = some { ls with reg := (ls.reg.setReg dst (va.zeroExtend 64)).nextPc } := by
  have hlvm : ls.reg.lvm a = ⟨1, va⟩ := getW_eq_some_iff.mp hva
  rw [lsemStepMem_reg]
  simp only [lsemStepCast, castStruct?_zeroext, readReg, hlvm, Option.map_some]

/-! ## 2. The register + `CF` + `ZF` correspondence -/

/-- `JLstateCorrZ s ls flg cfN zfN`: the register+memory correspondence **plus**
    the `CF` and `ZF` axes. `regAgree` holds off the synthetic flag namespace
    `flg`; `cfN` / `zfN` are the designated `CF` / `ZF` slots (in `flg`, distinct)
    whose width-1 contents mirror the `JState` flags. The `ZF` analogue of
    `JLstateCorrF`, which tracks `CF` / `OF`. -/
structure JLstateCorrZ (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN zfN : String) :
    Prop where
  /-- Register agreement off the flag namespace. -/
  regAgree : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r)
  /-- Memory agreement. -/
  memAgree : ∀ (base : String) (off : Int), ls.lmem base off = s.mem base off
  /-- The designated `CF` slot mirrors `s.flags.cf`. -/
  cfAgree : ls.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf)))
  /-- The designated `ZF` slot mirrors `s.flags.zf`. -/
  zfAgree : ls.reg.getW zfN 1 = some (flagBit (s.flagB (·.zf)))
  /-- The `CF` slot is a flag name. -/
  cfFlg : flg cfN
  /-- The `ZF` slot is a flag name. -/
  zfFlg : flg zfN
  /-- The two designated slots are distinct. -/
  cf_ne_zf : cfN ≠ zfN

/-- `JLstateCorrZ` is preserved by a **matched** register write to a non-flag name:
    the `JState` result `snew` differs from `s` only in `dst := v` on the register
    axis, with memory and flags unchanged, and the lsem state writes the same `v`
    to `dst` at width 64. The shared tail of every flag-reader case. -/
theorem JLstateCorrZ_setReg (s snew : JState 64) (ls : LstateM) (flg : String → Prop)
    (cfN zfN : String) (hcorr : JLstateCorrZ s ls flg cfN zfN)
    (dst : String) (v : BitVec 64) (hdst : ¬ flg dst)
    (hs : ∀ r, snew.regs r = if r = dst then v else s.regs r)
    (hmem : ∀ base off, snew.mem base off = s.mem base off)
    (hflags : snew.flags = s.flags) :
    JLstateCorrZ snew { ls with reg := (ls.reg.setReg dst v).nextPc } flg cfN zfN := by
  have hdst_ne_cf : dst ≠ cfN := by rintro rfl; exact hdst hcorr.cfFlg
  have hdst_ne_zf : dst ≠ zfN := by rintro rfl; exact hdst hcorr.zfFlg
  have hcf : snew.flagB (·.cf) = s.flagB (·.cf) := by simp only [JState.flagB, hflags]
  have hzf : snew.flagB (·.zf) = s.flagB (·.zf) := by simp only [JState.flagB, hflags]
  refine ⟨?_, ?_, ?_, ?_, hcorr.cfFlg, hcorr.zfFlg, hcorr.cf_ne_zf⟩
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
  · show ((ls.reg.setReg dst v).nextPc).getW zfN 1 = some (flagBit (snew.flagB (·.zf)))
    rw [hzf, LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_ne_zf)]
    exact hcorr.zfAgree

/-! ## 3. The instruction translation -/

/-- The flag-reader subset: the `CF` materialisation `setc`, the three
    register-source conditional moves, and the flag-transparent immediate `mov`.
    Every opcode here writes one register and touches no flag, so a block of them
    threads a single pair of designated slots. -/
def InFlagReaderSubset : JInstr 64 → Prop
  | .setc _            => True
  | .cmove _ (.reg _)  => True
  | .cmovne _ (.reg _) => True
  | .cmovb _ (.reg _)  => True
  | .mov _ (.imm _)    => True
  | _                  => False

/-- The registers a flag-reader instruction reads or writes lie off the synthetic
    flag namespace `flg`. This is the side condition that keeps the designated
    slots and the real registers apart; it is vacuous off the subset. -/
def ReaderRegsOff (flg : String → Prop) : JInstr 64 → Prop
  | .setc dst              => ¬ flg dst
  | .cmove dst (.reg src)  => ¬ flg dst ∧ ¬ flg src
  | .cmovne dst (.reg src) => ¬ flg dst ∧ ¬ flg src
  | .cmovb dst (.reg src)  => ¬ flg dst ∧ ¬ flg src
  | .mov dst (.imm _)      => ¬ flg dst
  | _                      => True

/-- `jToRMZ cfN zfN`: lower a flag-reader `JInstr` to its lsem wire, given the
    designated `CF` / `ZF` slot names. `setc` becomes the width-64 `ZEROEXT` cast
    of the `CF` slot; each conditional move becomes a three-source `CMOV` reading
    its flag slot as the condition, with the operand order carrying the sense of
    the condition (`cmovne` swaps the data operands rather than negating the
    slot); the immediate `mov` keeps its `regConst` wire. Out-of-subset opcodes
    map to `Lret` (never claimed to agree). -/
def jToRMZ (cfN zfN : String) : JInstr 64 → LinstrRM
  | .setc dst => (zeroextLinstr dst cfN, .reg (some 64))
  | .cmove dst (.reg src) =>
      (cmovLinstr 64 dst [.reg zfN, .reg src, .reg dst], .reg none)
  | .cmovne dst (.reg src) =>
      (cmovLinstr 64 dst [.reg zfN, .reg dst, .reg src], .reg none)
  | .cmovb dst (.reg src) =>
      (cmovLinstr 64 dst [.reg cfN, .reg src, .reg dst], .reg none)
  | .mov dst (.imm n) => (movImmLinstr 64 dst n, .reg none)
  | _ => (.Lret, .reg none)

/-! ## 4. Value agreement -/

/-- The zero-extension of a flag bit to width 64 is the model's materialised flag
    word `if b then 1 else 0`. The value half of the `setc` agreement. -/
theorem zeroExtend_flagBit (b : Bool) :
    (flagBit b).zeroExtend 64 = (if b then 1 else 0 : BitVec 64) := by
  cases b <;> rfl

/-- `selectW` on a flag bit is `x86_CMOVcc` on that flag. The value half of the
    three conditional-move agreements. -/
theorem selectW_flagBit (b : Bool) (x y : BitVec 64) :
    selectW (flagBit b) x y = x86_CMOVcc b x y := by
  cases b <;> rfl

/-- Negating an `x86_CMOVcc` condition swaps its two data operands. This is what
    lets `cmovne` read the `ZF` slot directly, with the operand order carrying the
    negation. -/
theorem x86_CMOVcc_not (b : Bool) (x y : BitVec 64) :
    x86_CMOVcc (! b) x y = x86_CMOVcc b y x := by
  cases b <;> rfl

/-! ## 5. Per-opcode agreement -/

/-- **Per-opcode agreement for `setc`.** The `ZEROEXT` twin of `.setc dst` does not
    fail and its result satisfies `JLstateCorrZ` with the same designated slots:
    `dst` receives the materialised carry `if CF then 1 else 0`, and no flag
    moves. -/
theorem setc_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN zfN : String)
    (hcorr : JLstateCorrZ s ls flg cfN zfN) (dst : String) (hdst : ¬ flg dst) :
    ∃ ls', lsemStraightMem [jToRMZ cfN zfN (.setc dst)] ls = some ls' ∧
      JLstateCorrZ (runBlock s [.setc dst]) ls' flg cfN zfN := by
  have hstep : lsemStraightMem [jToRMZ cfN zfN (.setc dst)] ls
      = some { ls with reg :=
          (ls.reg.setReg dst ((flagBit (s.flagB (·.cf))).zeroExtend 64)).nextPc } := by
    show lsemStraightMem [(zeroextLinstr dst cfN, MemTag.reg (some 64))] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_zeroext1 dst cfN ls _ hcorr.cfAgree
  refine ⟨_, hstep, ?_⟩
  rw [zeroExtend_flagBit]
  refine JLstateCorrZ_setReg s _ ls flg cfN zfN hcorr dst _ hdst ?_ ?_ ?_
  · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
  · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]

/-- **Per-opcode agreement for a register-source conditional move.** Factored over
    the flag the condition reads: given the designated slot `flagN` holding
    `flagBit c`, the `CMOV` wire `[flagN, x, y]` does not fail and writes
    `x86_CMOVcc c (s.regs x) (s.regs y)` to `dst`, which is the `JState` result
    whenever the opcode's `evalInstr` is that write (`hrun`). -/
theorem cmov_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN zfN : String)
    (hcorr : JLstateCorrZ s ls flg cfN zfN)
    (dst x y flagN : String) (c : Bool)
    (hdst : ¬ flg dst) (hx : ¬ flg x) (hy : ¬ flg y)
    (hflag : ls.reg.getW flagN 1 = some (flagBit c))
    (jinstr : JInstr 64)
    (hji : jToRMZ cfN zfN jinstr =
      (cmovLinstr 64 dst [.reg flagN, .reg x, .reg y], .reg none))
    (hrun : ∀ r, (runBlock s [jinstr]).regs r =
      if r = dst then x86_CMOVcc c (s.regs x) (s.regs y) else s.regs r)
    (hmem : ∀ base off, (runBlock s [jinstr]).mem base off = s.mem base off)
    (hflags : (runBlock s [jinstr]).flags = s.flags) :
    ∃ ls', lsemStraightMem [jToRMZ cfN zfN jinstr] ls = some ls' ∧
      JLstateCorrZ (runBlock s [jinstr]) ls' flg cfN zfN := by
  have hstep : lsemStraightMem [jToRMZ cfN zfN jinstr] ls
      = some { ls with reg :=
          (ls.reg.setReg dst (selectW (flagBit c) (s.regs x) (s.regs y))).nextPc } := by
    rw [hji, lsemStraightMem_single]
    exact lsemStepMem_cmov dst flagN x y ls _ _ _ hflag (hcorr.regAgree x hx) (hcorr.regAgree y hy)
  refine ⟨_, hstep, ?_⟩
  rw [selectW_flagBit]
  exact JLstateCorrZ_setReg s _ ls flg cfN zfN hcorr dst _ hdst hrun hmem hflags

/-- **Per-opcode agreement for the immediate `mov`.** The `regConst` twin writes
    the literal at width 64 and touches no flag, so both designated slots carry
    over. -/
theorem movImm_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN zfN : String)
    (hcorr : JLstateCorrZ s ls flg cfN zfN) (dst : String) (n : Nat) (hdst : ¬ flg dst) :
    ∃ ls', lsemStraightMem [jToRMZ cfN zfN (.mov dst (.imm n))] ls = some ls' ∧
      JLstateCorrZ (runBlock s [.mov dst (.imm n)]) ls' flg cfN zfN := by
  have hstep : lsemStraightMem [jToRMZ cfN zfN (.mov dst (.imm n))] ls
      = some { ls with reg := (ls.reg.setReg dst (BitVec.ofNat 64 n)).nextPc } := by
    show lsemStraightMem
      [(movImmLinstr 64 dst n, MemTag.reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_movImm dst n ls
  refine ⟨_, hstep, ?_⟩
  refine JLstateCorrZ_setReg s _ ls flg cfN zfN hcorr dst _ hdst ?_ ?_ ?_
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JOperand.eval, x86_MOV]
  · intro base off
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]

/-- **Per-instruction agreement on the flag-reader subset.** Every opcode of
    `InFlagReaderSubset` whose registers lie off the flag namespace lowers through
    `jToRMZ` to a wire that does not fail and whose result again satisfies
    `JLstateCorrZ` with the same designated slots. The reader-axis analogue of
    `jToRM_agrees`. -/
theorem jToRMZ_agrees (i : JInstr 64) (hi : InFlagReaderSubset i)
    (flg : String → Prop) (cfN zfN : String) (hoff : ReaderRegsOff flg i)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorrZ s ls flg cfN zfN) :
    ∃ ls', lsemStraightMem [jToRMZ cfN zfN i] ls = some ls' ∧
      JLstateCorrZ (runBlock s [i]) ls' flg cfN zfN := by
  cases i
  case setc dst => exact setc_case s ls flg cfN zfN hcorr dst hoff
  case mov dst src =>
    cases src
    case imm n => exact movImm_case s ls flg cfN zfN hcorr dst n hoff
    case reg r => exact hi.elim
  case cmove dst src =>
    cases src
    case reg r =>
      have hoff' : ¬ flg dst ∧ ¬ flg r := hoff
      refine cmov_case s ls flg cfN zfN hcorr dst r dst zfN (s.flagB (·.zf))
        hoff'.1 hoff'.2 hoff'.1 hcorr.zfAgree _ rfl ?_ ?_ ?_
      · intro r'
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.get,
          JOperand.eval]
      · intro base off
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
      · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
    case imm n => exact hi.elim
  case cmovb dst src =>
    cases src
    case reg r =>
      have hoff' : ¬ flg dst ∧ ¬ flg r := hoff
      refine cmov_case s ls flg cfN zfN hcorr dst r dst cfN (s.flagB (·.cf))
        hoff'.1 hoff'.2 hoff'.1 hcorr.cfAgree _ rfl ?_ ?_ ?_
      · intro r'
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.get,
          JOperand.eval]
      · intro base off
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
      · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
    case imm n => exact hi.elim
  case cmovne dst src =>
    cases src
    case reg r =>
      have hoff' : ¬ flg dst ∧ ¬ flg r := hoff
      refine cmov_case s ls flg cfN zfN hcorr dst dst r zfN (s.flagB (·.zf))
        hoff'.1 hoff'.1 hoff'.2 hcorr.zfAgree _ rfl ?_ ?_ ?_
      · intro r'
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.get,
          JOperand.eval, x86_CMOVcc_not]
      · intro base off
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
      · simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
    case imm n => exact hi.elim
  all_goals exact hi.elim

/-! ## 6. Block and loop lifts -/

/-- **Block-level agreement on the flag-reader subset.** A whole straight-line
    block of flag-reader opcodes, all of whose registers lie off the flag
    namespace, runs to completion under `lsemStraightMem` and its result
    corresponds — on the register, memory, `CF` and `ZF` axes — to the `runBlock`
    result, in the same designated slots. Straight-line induction on the block, as
    in `runBlock_lsem_agree`. -/
theorem runBlock_lsem_agreeZ (b : List (JInstr 64))
    (flg : String → Prop) (cfN zfN : String)
    (hb : ∀ i ∈ b, InFlagReaderSubset i) (hoff : ∀ i ∈ b, ReaderRegsOff flg i)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrZ s ls flg cfN zfN) :
    ∃ ls', lsemStraightMem (b.map (jToRMZ cfN zfN)) ls = some ls' ∧
      JLstateCorrZ (runBlock s b) ls' flg cfN zfN := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨ls1, hstep1, hcorr1⟩ :=
      jToRMZ_agrees i (hb i (List.mem_cons_self ..)) flg cfN zfN
        (hoff i (List.mem_cons_self ..)) s ls h
    have hstep : lsemStepMem (jToRMZ cfN zfN i) ls = some ls1 := by
      rwa [lsemStraightMem_single] at hstep1
    obtain ⟨ls', hstep', hcorr'⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj))
        (fun j hj => hoff j (List.mem_cons_of_mem i hj)) (runBlock s [i]) ls1 hcorr1
    have hri : runBlock s (i :: is) = runBlock (runBlock s [i]) is := by
      simp only [runBlock_cons, runBlock_nil]
    refine ⟨ls', ?_, ?_⟩
    · simp only [List.map_cons, lsemStraightMem_cons, hstep]
      have hri' : runBlock (evalInstr s i) is = runBlock (runBlock s [i]) is := by
        simp only [runBlock_cons, runBlock_nil]
      rw [hri'] at *
      exact hstep'
    · rw [hri]; exact hcorr'

/-- `JLstateCorrZ` is insensitive to the loop back-edge `setLpc`: the program
    counter lives on the register half's `lpc` field, off the register-value map
    (`getW` reads only `lvm`), the memory carrier (`lmem`), and the two designated
    flag slots. The reader-axis analogue of `JLstateCorrF_setLpc`. -/
theorem JLstateCorrZ_setLpc (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (cfN zfN : String) (h : JLstateCorrZ s ls flg cfN zfN) (pc : Nat) :
    JLstateCorrZ s (ls.setLpc pc) flg cfN zfN where
  regAgree r := h.regAgree r
  memAgree base off := h.memAgree base off
  cfAgree := h.cfAgree
  zfAgree := h.zfAgree
  cfFlg := h.cfFlg
  zfFlg := h.zfFlg
  cf_ne_zf := h.cf_ne_zf

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The counted-loop lift on the flag-reader subset.** Every reader opcode
    preserves the designated slots, so the per-trip agreement returns to the SAME
    `(cfN, zfN)` and lifts over a runtime trip count by induction: the `n`-fold
    `runBoundedLoopMem` over the lowered body runs to completion and its result
    corresponds to the `JState`-side `n`-fold `runBoundedLoop`. The inter-trip
    `setLpc 1` is absorbed by `JLstateCorrZ_setLpc`. -/
theorem runBlock_lsem_agreeZ_loop (b : List (JInstr 64))
    (flg : String → Prop) (cfN zfN : String)
    (hb : ∀ i ∈ b, InFlagReaderSubset i) (hoff : ∀ i ∈ b, ReaderRegsOff flg i)
    (n : Nat) (s : JState 64) (ls : LstateM) (h : JLstateCorrZ s ls flg cfN zfN) :
    ∃ ls', runBoundedLoopMem (b.map (jToRMZ cfN zfN)) n ls = some ls' ∧
      JLstateCorrZ (runBoundedLoop s n b) ls' flg cfN zfN := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨ls1, hstep1, hcorr1⟩ := runBlock_lsem_agreeZ b flg cfN zfN hb hoff s ls h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s b) (ls1.setLpc 1) (JLstateCorrZ_setLpc _ _ _ _ _ hcorr1 1)

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCmov
