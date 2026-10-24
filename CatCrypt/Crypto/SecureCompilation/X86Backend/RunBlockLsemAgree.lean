/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop

/-!
# `runBlock` ↔ `lsemStraightMem` agreement (the machine-model bridge)

`RolledScalarMulEmit.lean` names the wall this module addresses: the point-op bricks
(`jacDblBlock` / `jacAddBlock` / `copyBankBlock`) are `List (JInstr 64)` with the
**total** fold semantics `runBlock` over `JState` (`JasminModel.lean`), while the
counted-loop node's per-trip machine body is `List LinstrRM` with the **partial**
`lsemStraightMem` over `LstateM` (`JasminLsemMem.lean`). `JasminLsem.lean:76`
states outright that the two straight-line machines are the *same shape* but their
agreement is **not** proved. This module builds that bridge for the fragment on
which the two models coincide, and reports — with a concrete witness —
exactly where they do **not** (the honesty gate the task requires).

## The state correspondence

`JLstateCorr s ls` ties `JState` to `LstateM` on **both** the register and the
compile-time-offset memory axes: every register name reads back at width 64 with
the `JState` value (`ls.reg.getW r 64 = some (s.regs r)`), and every memory cell of
the lsem word carrier `lmem` equals the `JState` cell
(`ls.lmem base off = s.mem base off`). The register half is the natural agreement
`JasminLsem.lean:76` alludes to (`String → BitVec w`), pinned at width 64; the
memory half is over the **type-identical** carrier `JMem 64 = String → Int →
BitVec 64` — the restored increment-1 `Lstate.lmem`, now on `LstateM` as `lmem`.
Flags are still **not** in the correspondence — see the honesty gate for why.

## The translatable subset (`InFieldArithSubset`)

The opcodes on which `runBlock` and `lsemStraightMem` provably agree are the
**flag-free, single-write register-ALU core plus the compile-time-offset word
memory ops**: the two-address `add`/`sub`/`imul`/`and`/`or`/`xor` (source a
register or an immediate), the immediate `mov`, and — for a non-negative
displacement — `loadMem` / `storeMem` (register source). `jToRM` lowers each ALU op
to the two-address `Lopn [.reg dst] (withWidthTag 64 mnem) [.reg dst, src]` wire
(tag `.reg none`), and each memory op to the `MOVQ` wire over a `.arr base off`
operand (tag `.loadC` / `.storeC`, the `JState.loadMem`/`storeMem` twins).
`jToRM_agrees` proves, per opcode, that the lsem twin **does not fail** (totality on
the subset) and lands in a state that again satisfies `JLstateCorr`;
`runBlock_lsem_agree` lifts this over a whole straight-line block by induction.

## The honesty gate: memory + `mulx` are CLOSED; the flag/carry spine remains

Two of the three original divergences are **closed**. (1) The memory axis —
`LstateM` carries the compile-time-offset word memory `lmem` (type-identical to
`JMem 64`), the `.loadC` / `.storeC` `MemTag` arms mirror `JState.loadMem` /
`JState.storeMem`, and `JLstateCorr` tracks memory cell-for-cell; the point-op
frame prologue/epilogue `loadSlot4` / `storeSlot4` are **inside** the subset
(`loadSlot4_lsem_agree` / `storeSlot4_lsem_agree`, §8). (3) The two-write `mulx` —
`JInstr.mulx dstHi dstLo a b` lowers 1→2 to `MUL` (lo) + `MULXHI` (hi) via
`jToRMs`, agreeing under an aliasing side-condition (`mulLo_eq` / `mulHi_eq`, §6a);
it is in `InSubsetM` and covered by `jToRMs_agrees` / `runBlock_lsem_agreeM`. The
runtime-indexed `stackLoad` / `stackStore` remain the separate runtime-index
memory axis, orthogonal to this compile-time one. One divergence remains:

2. **Flag / carry threading.** `JState`'s `adc` / `sbb` / `adcx` / `adox` read and
   write an **implicit** flag register (`s.flagB (·.cf)`, `s.flags`), and `setc`
   materialises `CF`, `cmove`/`cmovne` read `ZF`, `cmovb` reads `CF`. The lsem
   register state has **no flag field**; its carry fragment (`addCarryLo` /
   `addCarryHi`) threads the carry as an **explicit** `.reg 1` operand valued with
   `addCarryWord` / `carryOutBit` — the *same* functions the `JState` `adcx` /
   `adox` arms compute, so the *value* agreement is already in hand. Phase 3 (§9)
   adds the **designated-register correspondence** (`JLstateCorrF`, tracking which
   `.reg 1` name currently mirrors `CF` / `OF`) and the in-place `.adcx` / `.adox`
   1→2 lowering. The `ZF` readers sit in `RunBlockLsemAgreeCmov`, which covers
   `setc`, `cmovb`, `cmove` and `cmovne` under `JLstateCorrZ` — `JLstateCorrF`
   with the `OF` axis replaced by `ZF`. Outside the scheme: the *immediate*-carry
   gadget `materialiseCarry` (`.adcx hi (.imm 0)` / `.adox hi (.imm 0)`), where
   the structured lsem `ADCX` recognizer wants three register operands, so an
   immediate carry-in has no structured wire — a zero register or an lsem
   immediate-carry form is required.

## Rolling assessment (does this bridge alone re-roll a point-op body?)

**No — and even for an in-subset body the front is a second necessary piece.** The
counted-loop node `ComL.forLoopNRt`'s per-trip update body is a
`Com jasminDialect` (`update : Com jasminDialect (accTy :: …) accTy`), and its
emitted machine body is obtained through the front (`frontLoopBodyJ` →
`straightOpsMem`), *not* by translating raw `JInstr` with a `jToRM` like this one.
This `runBlock ↔ lsem` bridge closes the *semantic-agreement* obligation for the
ALU-core opcodes, but it does **not** supply a front-generated `Com jasminDialect`
body — the loop node consumes a `Com`, whose lsem body is `straightOpsMem`'s
output, and the no-hand-authoring rule forbids substituting a hand-built `Com`
twin of `jToRM`'s output. Hence: the bridge is **necessary but not sufficient**;
a field-arith `LowCT` front generating the `Com jasminDialect` loop body is a
**second, independent** required piece. This bridge closes the machine-model
agreement for the ALU core **and** the compile-time-offset memory ops (§8); items 2
(front source) and 3 (limb-level `abs`) remain, and the machine-model agreement
itself remains open only for the flag/carry and two-write `mulx` opcodes (§ honesty
gate, phases 2–3).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The state correspondence -/

/-- `JLstateCorr s ls`: the `JState`-`LstateM` correspondence at the uniform word
    width 64, on **both** the register and the compile-time-offset memory axes.
    Every register name reads back from the lsem width-tagged bank at width 64 with
    exactly the `JState` value (`regAgree`, the natural `String → BitVec 64`
    agreement `JasminLsem.lean:76` alludes to), and every memory cell of the lsem
    word carrier `lmem` equals the `JState` cell (`memAgree`, over the
    type-identical `JMem 64 = String → Int → BitVec 64` carrier). Flags are still
    not tracked (the lsem register state has no flag field — see the module
    header's honesty gate). -/
structure JLstateCorr (s : JState 64) (ls : LstateM) : Prop where
  /-- Register agreement: `ls.reg` reads back the `JState` register at width 64. -/
  regAgree : ∀ r : String, ls.reg.getW r 64 = some (s.regs r)
  /-- Memory agreement: `ls.lmem` equals `JState.mem` cell-for-cell (the restored
      compile-time-offset carrier, type-identical to `JMem 64`). -/
  memAgree : ∀ (base : String) (off : Int), ls.lmem base off = s.mem base off

/-! ## 2. The instruction translation for the ALU-core subset -/

/-- The field-arith ALU-core subset the two machine models provably agree on:
    the flag-free, memory-free, single-write register ops. Every other opcode
    (memory, flag/carry, `mulx`, shifts, `cmove`, `neg`) is out of scope — see the
    module header's honesty gate for the three divergences. -/
def InFieldArithSubset : JInstr 64 → Prop
  | .mov _ (.imm _)  => True
  | .add _ _         => True
  | .sub _ _         => True
  | .imul _ _        => True
  | .and_ _ _        => True
  | .or_ _ _         => True
  | .xor_ _ _        => True
  -- Compile-time-offset word memory (`loadC`/`storeC` twins): in-subset for a
  -- non-negative displacement (the `.arr base off` operand carries a `Nat`
  -- offset, so `0 ≤ off` is exactly the condition `Int.ofNat off.toNat = off`).
  -- The point-op frame offsets `slotOff i k = 32·i + 8·k` are all `≥ 0`.
  | .loadMem _ _ off        => 0 ≤ off
  | .storeMem _ off (.reg _) => 0 ≤ off
  | _                => False

/-- Translate a `JOperand` source to the lsem `LOperand` wire operand. -/
def toLOp : JOperand → LOperand
  | .reg r => .reg r
  | .imm n => .imm n

/-- The lsem base mnemonic for a two-address ALU opcode. -/
def baseMnem : JInstr 64 → String
  | .mov _ _  => "MOV"
  | .add _ _  => "ADD"
  | .sub _ _  => "SUB"
  | .imul _ _ => "MUL"
  | .and_ _ _ => "AND"
  | .or_ _ _  => "OR"
  | .xor_ _ _ => "XOR"
  | _         => "?"

/-- `jToRM`: lower a subset `JInstr` to the exact `LinstrRM` wire the front emits
    for it — a two-address `Lopn [.reg dst] (withWidthTag 64 mnem) [.reg dst, src]`
    (the destination is source 0, matching `JState`'s two-address form) with the
    register-binding tag `.reg none`; the immediate `mov` is the nullary
    `regConst` form `Lopn [.reg dst] "MOV:64" [.imm n]`. Out-of-subset opcodes map
    to `Lret` (never claimed to agree). -/
def jToRM : JInstr 64 → LinstrRM
  | .mov dst (.imm n) => (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.imm n], .reg none)
  | .add dst src  => (.Lopn [.reg dst] (withWidthTag 64 "ADD") [.reg dst, toLOp src], .reg none)
  | .sub dst src  => (.Lopn [.reg dst] (withWidthTag 64 "SUB") [.reg dst, toLOp src], .reg none)
  | .imul dst src => (.Lopn [.reg dst] (withWidthTag 64 "MUL") [.reg dst, toLOp src], .reg none)
  | .and_ dst src => (.Lopn [.reg dst] (withWidthTag 64 "AND") [.reg dst, toLOp src], .reg none)
  | .or_ dst src  => (.Lopn [.reg dst] (withWidthTag 64 "OR")  [.reg dst, toLOp src], .reg none)
  | .xor_ dst src => (.Lopn [.reg dst] (withWidthTag 64 "XOR") [.reg dst, toLOp src], .reg none)
  -- Compile-time-offset word load/store: the `MOVQ` wire over a `.arr base off`
  -- operand, tagged `.loadC` / `.storeC` (the `JState.loadMem`/`storeMem` twins).
  -- The displacement is carried as the `Nat` `off.toNat` (faithful for `off ≥ 0`).
  | .loadMem dst base off => (.Lopn [.reg dst] "MOVQ" [.arr base off.toNat], .loadC)
  | .storeMem base off (.reg src) =>
      (.Lopn [.arr base off.toNat] "MOVQ" [.reg src], .storeC)
  | _ => (.Lret, .reg none)

/-! ## 3. The lsem-side reduction for the ALU-core wires

The tag `.reg none` routes `lsemStepMem` through the delegation chain
`lsemStepCast → lsemStepMC → lsemStepSh → lsemStepN` (each layer's structured
recognizer misses the ALU-core mnemonics), landing in `lsemStepN`'s `regArith` /
`regConst` arm. -/

/-- **The lsem twin of a two-address `regArith` wire.** For a base mnemonic that no
    structured recognizer claims (`MULXHI` / `ADCX` / `ADCXHI` / `SAR`), given the
    accumulator register `dst` reads `va` at width 64 and the source operand `b`
    evaluates to `vb`, `lsemStepMem` runs `applyOpnN` and writes the result to
    `dst` — it does **not** fail (totality on the subset). -/
theorem lsemStepMem_regArith
    (dst base : String) (b : LOperand) (ls : LstateM)
    (hstrip : stripWidthTag (withWidthTag 64 base) = base)
    (h1 : base ≠ "MULXHI") (_h2 : base ≠ "ADCX") (_h3 : base ≠ "ADCXHI") (h4 : base ≠ "SAR")
    (va vb v : BitVec 64)
    (hva : ls.reg.getW dst 64 = some va)
    (hvb : evalOperandN ls.reg 64 b = some vb)
    (hop : applyOpnN 64 base [va, vb] = some v) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 base) [.reg dst, b], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst v).nextPc } := by
  have hm : mulhiStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg dst, b]) = none := by
    cases b <;> simp only [mulhiStruct?, hstrip, ite_eq_right h1]
  have ha : adcxStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg dst, b]) = none := by
    cases b <;> rfl
  have hh : adcxhiStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg dst, b]) = none := by
    cases b <;> rfl
  have hs : sarStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg dst, b]) = none := by
    cases b <;> simp only [sarStruct?, hstrip, ite_eq_right h4]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm ha hh (by cases b <;> rfl) (by cases b <;> rfl),
      lsemStepSh_of_not_sar _ _ hs]
  simp only [lsemStepN, readReg_of_getW hva, hvb, hstrip, hop, Option.map_some]

/-- **The lsem twin of the immediate-`MOV` (`regConst`) wire.** Writes the literal
    at width 64 to `dst`; never fails. -/
theorem lsemStepMem_movImm (dst : String) (n : Nat) (ls : LstateM) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.imm n], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (BitVec.ofNat 64 n)).nextPc } := by
  have hstr : stripWidthTag (withWidthTag 64 "MOV") = "MOV" :=
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar.stripWidthTag_withWidthTag_MOV 64
  have hwidth : widthFromTag (withWidthTag 64 "MOV") = 64 :=
    widthFromTag_withWidthTag_MOV (Or.inl rfl)
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl, lsemStepSh_of_not_sar _ _ rfl]
  simp only [lsemStepN, hstr, Option.map_some, ite_eq_left]
  rw [hwidth]

/-! ## 4. Correspondence preservation and the value-agreement lemmas -/

/-- `JLstateCorr` is preserved by a **matched** register write: if the `JState`
    result `snew` differs from `s` only in `dst := v` on the register axis and
    leaves memory unchanged (`hmem`), and the lsem state writes the *same* `v` to
    `dst` at width 64 (leaving `lmem` untouched), the correspondence carries over on
    both axes. (Flags in `snew` are irrelevant — `JLstateCorr` reads only `.regs`
    and `.mem`.) -/
theorem JLstateCorr_setReg (s snew : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) (v : BitVec 64)
    (hs : ∀ r, snew.regs r = if r = dst then v else s.regs r)
    (hmem : ∀ base off, snew.mem base off = s.mem base off) :
    JLstateCorr snew { ls with reg := (ls.reg.setReg dst v).nextPc } := by
  constructor
  · intro r
    show ((ls.reg.setReg dst v).nextPc).getW r 64 = some (snew.regs r)
    rw [LstateN.getW_nextPc, hs r]
    by_cases hr : r = dst
    · subst hr; rw [LstateN.getW_setReg_same]; simp
    · rw [LstateN.getW_setReg_other _ _ _ _ _ hr, hcorr.regAgree r, ite_eq_right hr]
  · intro base off
    show ls.lmem base off = snew.mem base off
    rw [hmem base off]; exact hcorr.memAgree base off

/-- The `JOperand` source evaluates, under the correspondence, to the same word in
    the lsem operand model at width 64. -/
theorem evalOperandN_toLOp (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (src : JOperand) : evalOperandN ls.reg 64 (toLOp src) = some (src.eval s) := by
  cases src with
  | reg r => simpa [toLOp, evalOperandN, JOperand.eval, JState.get] using hcorr.regAgree r
  | imm n => simp [toLOp, evalOperandN, JOperand.eval]

/-! ## 5. Per-opcode agreement -/

/-- The `[jToRM x]` singleton runs as a single `lsemStepMem`. -/
theorem lsemStraightMem_single (x : LinstrRM) (ls : LstateM) :
    lsemStraightMem [x] ls = lsemStepMem x ls := by
  simp only [lsemStraightMem]; cases lsemStepMem x ls <;> rfl

/-- **Factored binop case.** For a two-address ALU opcode `jinstr` whose `jToRM`
    lowering is the `regArith` wire for base mnemonic `base`, given the lsem
    value-agreement (`hop`) and the `JState` register update (`hrun`), the lsem
    twin does not fail and the result corresponds. -/
theorem binop_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) (src : JOperand) (base : String) (w : BitVec 64)
    (hstrip : stripWidthTag (withWidthTag 64 base) = base)
    (h1 : base ≠ "MULXHI") (h2 : base ≠ "ADCX") (h3 : base ≠ "ADCXHI") (h4 : base ≠ "SAR")
    (hop : applyOpnN 64 base [s.get dst, src.eval s] = some w)
    (jinstr : JInstr 64)
    (hji : jToRM jinstr = (.Lopn [.reg dst] (withWidthTag 64 base) [.reg dst, toLOp src], .reg none))
    (hrun : ∀ r, (runBlock s [jinstr]).regs r = if r = dst then w else s.regs r)
    (hmemrun : ∀ base off, (runBlock s [jinstr]).mem base off = s.mem base off) :
    ∃ ls', lsemStraightMem [jToRM jinstr] ls = some ls' ∧
      JLstateCorr (runBlock s [jinstr]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst w hrun hmemrun⟩
  rw [hji, lsemStraightMem_single]
  exact lsemStepMem_regArith dst base (toLOp src) ls hstrip h1 h2 h3 h4
    (s.get dst) (src.eval s) w (hcorr.regAgree dst) (evalOperandN_toLOp s ls hcorr src) hop

/-- **Factored `loadMem` case (compile-time-offset word load).** For a non-negative
    displacement, the `.loadC`-tagged `MOVQ` twin of `.loadMem dst base off` does not
    fail and its result corresponds: the loaded register reads `s.mem base off` (via
    the memory-agreement half of `hcorr`), and memory is unchanged. -/
theorem loadMem_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst base : String) (off : Int) (hoff : 0 ≤ off) :
    ∃ ls', lsemStraightMem [jToRM (.loadMem dst base off)] ls = some ls' ∧
      JLstateCorr (runBlock s [.loadMem dst base off]) ls' := by
  have hio : (Int.ofNat off.toNat) = off := Int.toNat_of_nonneg hoff
  have hV : ls.lmem base (Int.ofNat off.toNat) = s.mem base off := by
    rw [hio]; exact hcorr.memAgree base off
  refine ⟨(ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc, ?_, ?_⟩
  · show lsemStraightMem [(.Lopn [.reg dst] "MOVQ" [.arr base off.toNat], .loadC)] ls = _
    rw [lsemStraightMem_single, lsemStepMem_loadC]
  · constructor
    · intro r
      show ((ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc).reg.getW r 64
        = some ((runBlock s [.loadMem dst base off]).regs r)
      rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
      have hrhs : (runBlock s [.loadMem dst base off]).regs r
          = if r = dst then s.mem base off else s.regs r := by
        simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg, JState.load]
      rw [hrhs]
      by_cases hr : r = dst
      · subst hr; rw [LstateN.getW_setReg_same, hV, ite_eq_left rfl]
      · rw [LstateN.getW_setReg_other _ _ _ _ _ hr, hcorr.regAgree r, ite_eq_right hr]
    · intro base' off'
      show ((ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc).lmem base' off'
        = (runBlock s [.loadMem dst base off]).mem base' off'
      rw [LstateM.lmem_nextPc, LstateM.lmem_setReg]
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg, JState.load]
      exact hcorr.memAgree base' off'

/-- **Factored `storeMem` case (compile-time-offset word store).** For a non-negative
    displacement and a register source, the `.storeC`-tagged `MOVQ` twin of
    `.storeMem base off (.reg src)` does not fail and its result corresponds: memory
    cell `[base + off]` becomes `s.regs src` on both sides, registers are unchanged. -/
theorem storeMem_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (base : String) (off : Int) (src : String) (hoff : 0 ≤ off) :
    ∃ ls', lsemStraightMem [jToRM (.storeMem base off (.reg src))] ls = some ls' ∧
      JLstateCorr (runBlock s [.storeMem base off (.reg src)]) ls' := by
  have hio : (Int.ofNat off.toNat) = off := Int.toNat_of_nonneg hoff
  refine ⟨(ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc, ?_, ?_⟩
  · show lsemStraightMem [(.Lopn [.arr base off.toNat] "MOVQ" [.reg src], .storeC)] ls = _
    rw [lsemStraightMem_single,
      lsemStepMem_storeC base off.toNat src ls (s.regs src) (hcorr.regAgree src)]
  · constructor
    · intro r
      show ((ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc).reg.getW r 64
        = some ((runBlock s [.storeMem base off (.reg src)]).regs r)
      rw [LstateM.reg_nextPc, LstateM.reg_storeMemC, LstateN.getW_nextPc, hcorr.regAgree r]
      simp only [runBlock_cons, runBlock_nil, evalInstr, JState.regs_store]
    · intro base' off'
      show ((ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc).lmem base' off'
        = (runBlock s [.storeMem base off (.reg src)]).mem base' off'
      rw [LstateM.lmem_nextPc, hio]
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.get,
        JState.store, LstateM.storeMemC]
      split_ifs with h
      · rfl
      · exact hcorr.memAgree base' off'

/-- **Per-opcode agreement on the field-arith subset.** For a subset opcode `i`, the
    lsem twin `lsemStraightMem [jToRM i]` does not fail (TOTALITY) and its result
    corresponds — via `JLstateCorr` — to the `runBlock` result. Proved by a case
    split; each arm combines the lsem-side reduction (§3) with correspondence
    preservation (§4) and the definitional `word`/`applyOpnN` value agreement. The
    memory arms (`loadMem`/`storeMem`) use the compile-time-offset `loadC`/`storeC`
    twins and the memory-agreement half of `JLstateCorr`. -/
theorem jToRM_agrees (i : JInstr 64) (hi : InFieldArithSubset i)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem [jToRM i] ls = some ls' ∧ JLstateCorr (runBlock s [i]) ls' := by
  cases i
  case mov dst src =>
    cases src
    case imm n =>
      refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (BitVec.ofNat 64 n) ?_ ?_⟩
      · show lsemStraightMem [jToRM (.mov dst (.imm n))] ls = _
        rw [show jToRM (.mov dst (.imm n))
              = (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.imm n], .reg none) from rfl,
          lsemStraightMem_single]
        exact lsemStepMem_movImm dst n ls
      · intro r
        simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.setReg]
      · intro base off
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
    case reg r => exact hi.elim
  case add dst src =>
    refine binop_case s ls hcorr dst src "ADD" (x86_ADD (s.get dst) (src.eval s)).word
      (stripWidthTag_withWidthTag_binOpName' 64 .add) (by decide) (by decide) (by decide) (by decide) rfl
      (.add dst src) rfl ?_ ?_
    · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
  case sub dst src =>
    refine binop_case s ls hcorr dst src "SUB" (x86_SUB (s.get dst) (src.eval s)).word
      (stripWidthTag_withWidthTag_binOpName' 64 .sub) (by decide) (by decide) (by decide) (by decide) rfl
      (.sub dst src) rfl ?_ ?_
    · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
  case imul dst src =>
    refine binop_case s ls hcorr dst src "MUL" (x86_IMULt (s.get dst) (src.eval s)).word
      (stripWidthTag_withWidthTag_binOpName' 64 .mul) (by decide) (by decide) (by decide) (by decide) rfl
      (.imul dst src) rfl ?_ ?_
    · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
  case and_ dst src =>
    refine binop_case s ls hcorr dst src "AND" (x86_AND (s.get dst) (src.eval s)).word
      (stripWidthTag_withWidthTag_binOpName' 64 .and) (by decide) (by decide) (by decide) (by decide) rfl
      (.and_ dst src) rfl ?_ ?_
    · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
  case or_ dst src =>
    refine binop_case s ls hcorr dst src "OR" (x86_OR (s.get dst) (src.eval s)).word
      (stripWidthTag_withWidthTag_binOpName' 64 .or) (by decide) (by decide) (by decide) (by decide) rfl
      (.or_ dst src) rfl ?_ ?_
    · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
  case xor_ dst src =>
    refine binop_case s ls hcorr dst src "XOR" (x86_XOR (s.get dst) (src.eval s)).word
      (stripWidthTag_withWidthTag_binOpName' 64 .xor) (by decide) (by decide) (by decide) (by decide) rfl
      (.xor_ dst src) rfl ?_ ?_
    · intro r; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
    · intro base off; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]
  case loadMem dst base off =>
    exact loadMem_case s ls hcorr dst base off hi
  case storeMem base off src =>
    cases src
    case reg r => exact storeMem_case s ls hcorr base off r hi
    case imm n => exact hi.elim
  all_goals exact hi.elim

/-! ## 6. Block-level lift -/

/-- **Block-level agreement.** A whole straight-line `List (JInstr 64)` all of whose
    opcodes are in the ALU-core subset runs to completion under `lsemStraightMem`
    (no failure) and its result corresponds to the `runBlock` result. Straight-line
    induction on the block. -/
theorem runBlock_lsem_agree (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InFieldArithSubset i) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (b.map jToRM) ls = some ls' ∧ JLstateCorr (runBlock s b) ls' := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨ls1, hstep1, hcorr1⟩ :=
      jToRM_agrees i (hb i (List.mem_cons_self ..)) s ls h
    -- `lsemStraightMem [jToRM i] ls = lsemStepMem (jToRM i) ls`, and the head step succeeds
    have hstep : lsemStepMem (jToRM i) ls = some ls1 := by
      have : lsemStraightMem [jToRM i] ls = lsemStepMem (jToRM i) ls := by
        simp only [lsemStraightMem]; cases lsemStepMem (jToRM i) ls <;> rfl
      rw [this] at hstep1; exact hstep1
    obtain ⟨ls', hstep', hcorr'⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) (runBlock s [i]) ls1 hcorr1
    refine ⟨ls', ?_, ?_⟩
    · simp only [List.map_cons, lsemStraightMem_cons, hstep]
      -- `runBlock s (i :: is)` starts with `evalInstr s i = runBlock s [i]`
      have hri : runBlock (evalInstr s i) is = runBlock (runBlock s [i]) is := by
        simp only [runBlock_cons, runBlock_nil]
      rw [hri] at *
      exact hstep'
    · have hri : runBlock s (i :: is) = runBlock (runBlock s [i]) is := by
        simp only [runBlock_cons, runBlock_nil]
      rw [hri]; exact hcorr'

/-! ## 6a. Phase 2: the two-write `mulx` (1→2 lowering)

`JInstr.mulx dstHi dstLo a b` writes **both** product words in one instruction;
the lsem model has no two-write op, so the faithful lowering is a *pair* of
single-write lsem instructions — a three-address `MUL` (low word, `dstLo := a·b`)
and a structured `MULXHI` (high word, `dstHi := mulHiW a b`). The value functions
are already proven equal to the `JState` ones: the high word is `mulHiW = (wumul
a b).1` (definitional) and the low word is `a·b = (wumul a b).2` (`mulLo_eq`). The
only non-value content is the **ordering / aliasing** side-condition
(`dstLo ∉ {a, b}`, `dstHi ≠ dstLo`) that makes the sequential two-op form
reproduce the simultaneous two-write. Because `mulx` touches **no flag**, this
axis closes over the *existing* `JLstateCorr` (register + memory only). -/

/-- The lsem low-word product `a·b` equals the `JState` `MULX` low output
    `(x86_MULX_lo_hi a b).1` (`= (wumul a b).2`). A `BitVec` identity: both have
    `toNat = a.toNat·b.toNat mod 2^64`. -/
theorem mulLo_eq (va vb : BitVec 64) : va * vb = (x86_MULX_lo_hi va vb).1 := by
  have h : (x86_MULX_lo_hi va vb).1 = BitVec.ofNat 64 (va.toNat * vb.toNat) := rfl
  rw [h]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

/-- The lsem high-word product `mulHiW a b` equals the `JState` `MULX` high output
    `(x86_MULX_lo_hi a b).2` (`= (wumul a b).1 = high_bits …`) — definitionally
    (`mulHiW` and `high_bits` are the same `ofNat (·/2^w)`). -/
theorem mulHi_eq (va vb : BitVec 64) :
    mulHiW va vb = (x86_MULX_lo_hi va vb).2 := rfl

/-- **The lsem twin of a three-address `regArith` wire** (first source a register
    `a`, not the destination). Mirrors `lsemStepMem_regArith` but reads source 0
    from `a` — the shape a `mulx`-lowered `MUL` (`dstLo := a·b`) needs. -/
theorem lsemStepMem_regArith3
    (dst a : String) (b : LOperand) (ls : LstateM) (base : String)
    (hstrip : stripWidthTag (withWidthTag 64 base) = base)
    (h1 : base ≠ "MULXHI") (_h2 : base ≠ "ADCX") (_h3 : base ≠ "ADCXHI") (h4 : base ≠ "SAR")
    (va vb v : BitVec 64)
    (hva : ls.reg.getW a 64 = some va)
    (hvb : evalOperandN ls.reg 64 b = some vb)
    (hop : applyOpnN 64 base [va, vb] = some v) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst v).nextPc } := by
  have hm : mulhiStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> simp only [mulhiStruct?, hstrip, ite_eq_right h1]
  have ha : adcxStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> rfl
  have hh : adcxhiStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> rfl
  have hs : sarStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> simp only [sarStruct?, hstrip, ite_eq_right h4]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm ha hh (by cases b <;> rfl) (by cases b <;> rfl),
      lsemStepSh_of_not_sar _ _ hs]
  simp only [lsemStepN, readReg_of_getW hva, hvb, hstrip, hop, Option.map_some]

/-- **The lsem twin of a three-address structured `MULXHI` wire.** Reads both
    sources `a, b` at width 64 and writes `mulHiW a b`; never fails. The high-word
    half of the `mulx` lowering. -/
theorem lsemStepMem_mulhi3 (dst a b : String) (ls : LstateM) (va vb : BitVec 64)
    (hva : ls.reg.getW a 64 = some va) (hvb : ls.reg.getW b 64 = some vb) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "MULXHI") [.reg a, .reg b], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (mulHiW va vb)).nextPc } := by
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  simp only [lsemStepMC, mulhiStruct?_mulhi, readReg_of_getW hva, hvb, Option.map_some]

/-- `jToRMs`: the **list-valued** lowering, extending `jToRM` to the two-write
    `mulx` — one `JInstr` may lower to *several* `LinstrRM`. Every single-write
    opcode lowers to the `[jToRM i]` singleton; `mulx dstHi dstLo a b` (register
    sources) lowers to the pair `[MUL dstLo a b; MULXHI dstHi a b]`. -/
def jToRMs : JInstr 64 → List LinstrRM
  | .mulx dstHi dstLo (.reg a) (.reg b) =>
      [(.Lopn [.reg dstLo] (withWidthTag 64 "MUL") [.reg a, .reg b], .reg none),
       (.Lopn [.reg dstHi] (withWidthTag 64 "MULXHI") [.reg a, .reg b], .reg none)]
  | i => [jToRM i]

/-- The field-arith subset **plus** the two-write `mulx`. On `mulx` the aliasing
    side-condition (`dstLo ∉ {a, b}`, `dstHi ≠ dstLo`, register sources) makes the
    sequential `MUL; MULXHI` reproduce the simultaneous two-write; every other
    opcode defers to `InFieldArithSubset`. -/
def InSubsetM : JInstr 64 → Prop
  | .mulx dstHi dstLo (.reg a) (.reg b) => dstLo ≠ a ∧ dstLo ≠ b ∧ dstHi ≠ dstLo
  | i => InFieldArithSubset i

/-- **Per-opcode agreement for `mulx`.** For register sources with the aliasing
    side-condition, the `MUL; MULXHI` pair does not fail and its result
    corresponds (register + memory) to the `runBlock` two-write result: `dstLo`
    gets `a·b` (`mulLo_eq`), `dstHi` gets `mulHiW a b` (`mulHi_eq`). -/
theorem mulx_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dstHi dstLo a b : String) (hLoA : dstLo ≠ a) (hLoB : dstLo ≠ b) (hHiLo : dstHi ≠ dstLo) :
    ∃ ls', lsemStraightMem (jToRMs (.mulx dstHi dstLo (.reg a) (.reg b))) ls = some ls' ∧
      JLstateCorr (runBlock s [.mulx dstHi dstLo (.reg a) (.reg b)]) ls' := by
  -- Intermediate `JState` and `LstateM` after the low-word `MUL`.
  set lo : BitVec 64 := (s.regs a) * (s.regs b) with hlo
  set s1 : JState 64 := s.setReg dstLo lo with hs1def
  have hva : ls.reg.getW a 64 = some (s.regs a) := hcorr.regAgree a
  have hvb : evalOperandN ls.reg 64 (.reg b) = some (s.regs b) := by
    have := evalOperandN_toLOp s ls hcorr (.reg b); simpa [toLOp] using this
  -- Step 1: the `MUL` writes `dstLo := a·b`; correspondence to `s1`.
  set ls1 : LstateM := { ls with reg := (ls.reg.setReg dstLo lo).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg dstLo] (withWidthTag 64 "MUL") [.reg a, .reg b], .reg none) ls = some ls1 :=
    lsemStepMem_regArith3 dstLo a (.reg b) ls "MUL" (stripWidthTag_withWidthTag_binOpName' 64 .mul) (by decide) (by decide)
      (by decide) (by decide) (s.regs a) (s.regs b) lo hva hvb rfl
  have hcorr1 : JLstateCorr s1 ls1 := by
    refine JLstateCorr_setReg s s1 ls hcorr dstLo lo ?_ ?_
    · intro r; rw [hs1def]; by_cases hr : r = dstLo
      · subst hr; simp [JState.setReg]
      · simp [JState.setReg, hr]
    · intro base off; rw [hs1def]; simp [JState.setReg]
  -- Step 2: the `MULXHI` writes `dstHi := mulHiW a b`; reads `a, b` unchanged.
  have hva1 : ls1.reg.getW a 64 = some (s.regs a) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hLoA), hva]
  have hvb1 : ls1.reg.getW b 64 = some (s.regs b) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hLoB), hcorr.regAgree b]
  set hi : BitVec 64 := mulHiW (s.regs a) (s.regs b) with hhi
  set s2 : JState 64 := s1.setReg dstHi hi with hs2def
  set ls2 : LstateM := { ls1 with reg := (ls1.reg.setReg dstHi hi).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dstHi] (withWidthTag 64 "MULXHI") [.reg a, .reg b], .reg none) ls1 = some ls2 :=
    lsemStepMem_mulhi3 dstHi a b ls1 (s.regs a) (s.regs b) hva1 hvb1
  have hcorr2 : JLstateCorr s2 ls2 := by
    refine JLstateCorr_setReg s1 s2 ls1 hcorr1 dstHi hi ?_ ?_
    · intro r; rw [hs2def]; by_cases hr : r = dstHi
      · subst hr; simp [JState.setReg]
      · simp [JState.setReg, hr]
    · intro base off; rw [hs2def]; simp [JState.setReg]
  -- Assemble the two-step straightline and identify with `runBlock`.
  refine ⟨ls2, ?_, ?_⟩
  · simp only [jToRMs, lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  · have hrun : runBlock s [.mulx dstHi dstLo (.reg a) (.reg b)] = s2 := by
      rw [hs2def, hs1def, hlo, hhi]
      simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
      rw [mulLo_eq (s.regs a) (s.regs b), mulHi_eq (s.regs a) (s.regs b)]
    rw [hrun]; exact hcorr2

/-- **List-valued per-opcode agreement.** For any `InSubsetM` opcode, the
    (possibly two-instruction) lowering `jToRMs i` does not fail and its result
    corresponds to `runBlock s [i]`. Single-write opcodes reuse `jToRM_agrees`;
    `mulx` uses `mulx_case`. -/
theorem jToRMs_agrees (i : JInstr 64) (hi : InSubsetM i)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (jToRMs i) ls = some ls' ∧ JLstateCorr (runBlock s [i]) ls' := by
  match i, hi with
  | .mulx dstHi dstLo (.reg a) (.reg b), hi =>
      exact mulx_case s ls hcorr dstHi dstLo a b hi.1 hi.2.1 hi.2.2
  | .mov dst src, hi => exact jToRM_agrees (.mov dst src) hi s ls hcorr
  | .add dst src, hi => exact jToRM_agrees (.add dst src) hi s ls hcorr
  | .sub dst src, hi => exact jToRM_agrees (.sub dst src) hi s ls hcorr
  | .imul dst src, hi => exact jToRM_agrees (.imul dst src) hi s ls hcorr
  | .and_ dst src, hi => exact jToRM_agrees (.and_ dst src) hi s ls hcorr
  | .or_ dst src, hi => exact jToRM_agrees (.or_ dst src) hi s ls hcorr
  | .xor_ dst src, hi => exact jToRM_agrees (.xor_ dst src) hi s ls hcorr
  | .loadMem dst base off, hi => exact jToRM_agrees (.loadMem dst base off) hi s ls hcorr
  | .storeMem base off src, hi => exact jToRM_agrees (.storeMem base off src) hi s ls hcorr

/-- Straight-line execution distributes over concatenation: running `xs ++ ys`
    is running `xs` then, on success, `ys`. -/
theorem lsemStraightMem_append (xs ys : List LinstrRM) (ls : LstateM) :
    lsemStraightMem (xs ++ ys) ls =
      (lsemStraightMem xs ls).bind (fun ls' => lsemStraightMem ys ls') := by
  induction xs generalizing ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, lsemStraightMem_cons]
    cases lsemStepMem x ls with
    | none => rfl
    | some ls' => simp only [ih, Option.bind]

/-- **Block-level agreement over the ALU-core + memory + `mulx` subset.** A whole
    straight-line block all of whose opcodes are in `InSubsetM` runs to completion
    under `lsemStraightMem` on the concatenated lowering `b.flatMap jToRMs` and its
    result corresponds to `runBlock`. The block map is `flatMap` (not `map`) because
    `mulx` lowers 1→2. -/
theorem runBlock_lsem_agreeM (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InSubsetM i) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (b.flatMap jToRMs) ls = some ls' ∧ JLstateCorr (runBlock s b) ls' := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨ls1, hstep1, hcorr1⟩ := jToRMs_agrees i (hb i (List.mem_cons_self ..)) s ls h
    obtain ⟨ls', hstep', hcorr'⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) (runBlock s [i]) ls1 hcorr1
    refine ⟨ls', ?_, ?_⟩
    · rw [List.flatMap_cons, lsemStraightMem_append, hstep1, Option.bind]
      have hri : runBlock (evalInstr s i) is = runBlock (runBlock s [i]) is := by
        simp only [runBlock_cons, runBlock_nil]
      rw [hri] at *; exact hstep'
    · have hri : runBlock s (i :: is) = runBlock (runBlock s [i]) is := by
        simp only [runBlock_cons, runBlock_nil]
      rw [hri]; exact hcorr'

/-! ## 7. Honesty gate: memory + `mulx` are CLOSED; the flag/carry spine remains

Two of the original three divergences are now **closed**:

1. **Memory** — `LstateM` carries the compile-time-offset word memory `lmem`
   (type-identical to `JMem 64`), the `.loadC` / `.storeC` `MemTag` arms mirror
   `JState.loadMem` / `JState.storeMem`, and `JLstateCorr` tracks memory
   cell-for-cell; `loadMem` / `storeMem` are in `InFieldArithSubset`
   (`jToRM_agrees`).
3. **`mulx` two-write** — closed by the 1→2 lowering (§6a): one `JInstr.mulx`
   becomes the pair `MUL` (lo) + `MULXHI` (hi), agreeing via `mulLo_eq` /
   `mulHi_eq` under the aliasing side-condition; `mulx` is in `InSubsetM` and
   covered by `jToRMs_agrees` / `runBlock_lsem_agreeM`.

One model gap remains:

2. **Flag / carry threading.** `JState`'s `adc`/`sbb`/`adcx`/`adox`/`setc`/`cmove…`
   read and write an **implicit** flag register; the lsem register state has **no
   flag field**. The lsem carry ops thread the carry as an explicit `.reg 1`
   operand and value it with `addCarryWord`/`carryOutBit` (`JasminDialect`) — the
   same functions the `JState` `adcx`/`adox` arms compute (`X86Backend.Model`), so
   the *value* agreement is already in hand. The remaining content is a
   **designated-register correspondence**: track which `.reg 1` SSA name currently
   mirrors `CF` (and `OF`), lower a two-address in-place `.adcx` to the two
   single-write lsem ops (`ADCXHI` carry-out → a *fresh* CF-slot, then `ADCX` data
   → `dst`, both reading the *current* CF-slot, so the pre-write reads are not
   clobbered), and thread the current CF/OF-slot names through the induction. This
   is phase 3 (below, §9). -/

/-! ## 8. The memory fragment is now covered: `loadSlot4` / `storeSlot4`

The frame prologue/epilogue of every framed field op — `loadSlot4` (four
compile-time-offset `loadMem`s) and `storeSlot4` (four compile-time-offset
`storeMem`s, register sources) — now lie **entirely inside** `InFieldArithSubset`,
because every slot offset `slotOff slot k = 32·slot + 8·k` is non-negative. So the
`runBlock`↔`lsem` agreement (`runBlock_lsem_agree`) discharges the whole memory
fragment: the block runs to completion under `lsemStraightMem` and its result
corresponds — on both the register and the memory axis — to the `runBlock` result.
This is the concrete point-op memory-fragment corollary the bridge now supplies. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock in
/-- Every instruction of `loadSlot4` is in the field-arith subset (a compile-time
    `loadMem` at the non-negative offset `slotOff slot k`). -/
theorem loadSlot4_subset (r0 r1 r2 r3 base : String) (slot : Nat) :
    ∀ i ∈ loadSlot4 r0 r1 r2 r3 base slot, InFieldArithSubset i := by
  intro i hi
  simp only [loadSlot4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h <;> subst h <;>
    · show (0 : Int) ≤ slotOff slot _
      simp only [slotOff]; omega

open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock in
/-- Every instruction of `storeSlot4` is in the field-arith subset (a compile-time
    `storeMem` with a register source at the non-negative offset `slotOff slot k`). -/
theorem storeSlot4_subset (r0 r1 r2 r3 base : String) (slot : Nat) :
    ∀ i ∈ storeSlot4 r0 r1 r2 r3 base slot, InFieldArithSubset i := by
  intro i hi
  simp only [storeSlot4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h <;> subst h <;>
    · show (0 : Int) ≤ slotOff slot _
      simp only [slotOff]; omega

open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock in
/-- **Point-op frame-load fragment corollary.** The `loadSlot4` prologue — a whole
    compile-time-offset memory block — runs to completion under `lsemStraightMem`
    (no failure) and its result corresponds, on both axes, to the `runBlock` result.
    The memory fragment the original honesty gate named as the wall is now closed. -/
theorem loadSlot4_lsem_agree (r0 r1 r2 r3 base : String) (slot : Nat)
    (s : JState 64) (ls : LstateM) (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem ((loadSlot4 r0 r1 r2 r3 base slot).map jToRM) ls = some ls' ∧
      JLstateCorr (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)) ls' :=
  runBlock_lsem_agree _ (loadSlot4_subset r0 r1 r2 r3 base slot) s ls h

open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock in
/-- **Point-op frame-store fragment corollary.** The `storeSlot4` epilogue runs to
    completion under `lsemStraightMem` and its result corresponds on both axes to
    the `runBlock` result (memory now tracked cell-for-cell). -/
theorem storeSlot4_lsem_agree (r0 r1 r2 r3 base : String) (slot : Nat)
    (s : JState 64) (ls : LstateM) (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem ((storeSlot4 r0 r1 r2 r3 base slot).map jToRM) ls = some ls' ∧
      JLstateCorr (runBlock s (storeSlot4 r0 r1 r2 r3 base slot)) ls' :=
  runBlock_lsem_agree _ (storeSlot4_subset r0 r1 r2 r3 base slot) s ls h

/-! ## 9. Phase 3: the flag/carry axis (designated-register correspondence)

The last divergence — the implicit `CF` / `OF` flag register — is closed by a
**designated-register correspondence**. The lsem model threads a carry as an
explicit `.reg 1` operand valued by `addCarryWord` (data) / `carryOutBit`
(carry-out); the `JState` `adcx` / `adox` arms compute the *same* words
(`waddcarry`), so the value agreement is the two definitional-modular identities
`adcx_data_eq` / `adcx_carry_eq`. The only new content is the **bookkeeping**:

* `JLstateCorrF s ls flg cfN ofN` extends the register+memory correspondence with
  a **flag namespace** `flg : String → Prop` (the synthetic `.reg 1` carry-slot
  names, which the real block registers avoid) — `regAgree` is asserted only off
  `flg` — plus two **designated slots** `cfN` / `ofN` (in `flg`) whose width-1
  contents mirror `s.flags.cf` / `s.flags.of`.
* A two-address in-place `.adcx dst src` lowers 1→2: `ADCXHI` writes the
  carry-out to a *fresh* CF-slot `cfNew`, then `ADCX` writes the data to `dst`,
  **both reading the current slot `cfN`**. Doing `ADCXHI` first (to `cfNew ≠ dst`)
  keeps `dst` and `cfN` at their pre-op values for the `ADCX` read, so the
  simultaneous flag+data write of the in-place instruction is reproduced. The new
  correspondence uses `cfNew`. `.adox` is identical on the `OF` slot.

**Residuals** (outside the register-source CF/OF scheme):
the *immediate*-carry gadget `materialiseCarry` (`.adcx hi (.imm 0)` /
`.adox hi (.imm 0)`) — the structured lsem `ADCX` recognizer needs three
*register* operands, so an immediate carry-in has no structured wire (a zero
register or an lsem immediate-carry form is required); and `cmove` / `cmovne`
reading `ZF`, which the CF/OF carry scheme does not track. -/

/-- The 1-bit flag value: `1` if the flag is set, `0` otherwise. The `BitVec 1`
    the lsem carry ops thread as the explicit carry operand. -/
def flagBit (b : Bool) : BitVec 1 := if b then 1 else 0

/-- The `toNat` of the flag bit is `1`/`0` (a `Nat`), the form the carry
    arithmetic reasons over. -/
theorem flagBit_toNat (c : Bool) : (flagBit c).toNat = (if c then 1 else 0) := by
  cases c <;> rfl

/-- **`adcx` data agreement.** The lsem carry-add word `addCarryWord v1 v2 (bit
    c)` equals the `JState` `ADCX`/`ADOX` data output `(waddcarry v1 v2 c).2`.
    Both are `ofNat 64 (v1.toNat + v2.toNat + [c])` up to the modular wrap. -/
theorem adcx_data_eq (v1 v2 : BitVec 64) (c : Bool) :
    addCarryWord v1 v2 (flagBit c) = (waddcarry v1 v2 c).2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [addCarryWord, waddcarry, flagBit_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  cases c <;> omega

/-- **`adcx` carry-out agreement.** The lsem carry-out bit `carryOutBit v1 v2 (bit
    c)` equals the flag bit of the `JState` `ADCX`/`ADOX` carry-out
    `(waddcarry v1 v2 c).1`. Both fire iff the unbounded sum reached `2^64`. -/
theorem adcx_carry_eq (v1 v2 : BitVec 64) (c : Bool) :
    carryOutBit v1 v2 (flagBit c) = flagBit (waddcarry v1 v2 c).1 := by
  have key : ∀ n : Nat, (if 2 ^ 64 ≤ n then (1 : BitVec 1) else 0) = flagBit (decide (2 ^ 64 ≤ n)) := by
    intro n; by_cases h : 2 ^ 64 ≤ n <;> simp [flagBit, h]
  simp only [carryOutBit, waddcarry, flagBit_toNat, ge_iff_le]
  exact key _

/-- **The lsem twin of a three-address structured `ADCX` wire** (`dst := addCarryWord
    a b c`, carry-in `c` at width 1). The data half of an `adcx`/`adox` lowering. -/
theorem lsemStepMem_adcx3 (dst a b c : String) (ls : LstateM) (va vb : BitVec 64) (vc : BitVec 1)
    (hva : ls.reg.getW a 64 = some va) (hvb : ls.reg.getW b 64 = some vb)
    (hvc : ls.reg.getW c 1 = some vc) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "ADCX") [.reg a, .reg b, .reg c], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (addCarryWord va vb vc)).nextPc } := by
  have hstep : lsemStepMC
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX") [.reg a, .reg b, .reg c]) ls.reg
      = some ((ls.reg.setReg dst (addCarryWord va vb vc)).nextPc) := by
    simp only [lsemStepMC, mulhiStruct?_adcx, adcxStruct?_adcx, readReg_of_getW hva, hvb, hvc]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl), hstep]
  rfl

/-- **The lsem twin of a three-address structured `ADCXHI` wire** (`dst := carryOutBit
    a b c`, a `BitVec 1`). The carry-out half of an `adcx`/`adox` lowering. -/
theorem lsemStepMem_adcxhi3 (dst a b c : String) (ls : LstateM) (va vb : BitVec 64) (vc : BitVec 1)
    (hva : ls.reg.getW a 64 = some va) (hvb : ls.reg.getW b 64 = some vb)
    (hvc : ls.reg.getW c 1 = some vc) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "ADCXHI") [.reg a, .reg b, .reg c], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (carryOutBit va vb vc)).nextPc } := by
  have hstep : lsemStepMC
      (.Lopn [.reg dst] (withWidthTag 64 "ADCXHI") [.reg a, .reg b, .reg c]) ls.reg
      = some ((ls.reg.setReg dst (carryOutBit va vb vc)).nextPc) := by
    simp only [lsemStepMC, mulhiStruct?_adcxhi, adcxStruct?_adcxhi, adcxhiStruct?_adcxhi,
      readReg_of_getW hva, hvb, hvc]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl), hstep]
  rfl

/-- `JLstateCorrF s ls flg cfN ofN`: the register+memory correspondence **plus** the
    flag axis. `regAgree` holds off the synthetic flag namespace `flg`; `cfN` / `ofN`
    are the designated `CF` / `OF` slots (in `flg`, distinct), whose width-1 contents
    mirror the `JState` flags. -/
structure JLstateCorrF (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String) :
    Prop where
  /-- Register agreement off the flag namespace. -/
  regAgree : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r)
  /-- Memory agreement (unchanged from `JLstateCorr`). -/
  memAgree : ∀ (base : String) (off : Int), ls.lmem base off = s.mem base off
  /-- The designated `CF` slot mirrors `s.flags.cf`. -/
  cfAgree : ls.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf)))
  /-- The designated `OF` slot mirrors `s.flags.of`. -/
  ofAgree : ls.reg.getW ofN 1 = some (flagBit (s.flagB (·.of)))
  /-- The `CF` slot is a flag name. -/
  cfFlg : flg cfN
  /-- The `OF` slot is a flag name. -/
  ofFlg : flg ofN
  /-- The two designated slots are distinct. -/
  cf_ne_of : cfN ≠ ofN

/-- **Per-opcode agreement for the register-source `.adcx` (CF chain).** Given a
    fresh CF-slot `cfNew` (a flag name distinct from `dst`, `src`, `cfN`, `ofN`),
    the pair `[ADCXHI cfNew; ADCX dst]` — both reading the current slot `cfN` — does
    not fail and its result satisfies `JLstateCorrF` with the new CF slot `cfNew`,
    matching the in-place `.adcx dst (.reg src)` on the register, flag, and memory
    axes. -/
theorem adcx_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN)
    (dst src cfNew : String)
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) (hNew : flg cfNew)
    (hNe_dst : cfNew ≠ dst) (hNe_src : cfNew ≠ src) (hNe_cf : cfNew ≠ cfN) (hNe_of : cfNew ≠ ofN) :
    ∃ ls', lsemStraightMem
        [ (.Lopn [.reg cfNew] (withWidthTag 64 "ADCXHI") [.reg dst, .reg src, .reg cfN], .reg none),
          (.Lopn [.reg dst]   (withWidthTag 64 "ADCX")   [.reg dst, .reg src, .reg cfN], .reg none) ]
        ls = some ls' ∧
      JLstateCorrF (runBlock s [.adcx dst (.reg src)]) ls' flg cfNew ofN := by
  have hdst_ne_cf : dst ≠ cfN := fun h => hdst (h ▸ hcorr.cfFlg)
  have hsrc_ne_cf : src ≠ cfN := fun h => hsrc (h ▸ hcorr.cfFlg)
  have hva : ls.reg.getW dst 64 = some (s.regs dst) := hcorr.regAgree dst hdst
  have hvb : ls.reg.getW src 64 = some (s.regs src) := hcorr.regAgree src hsrc
  have hvc : ls.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := hcorr.cfAgree
  -- Step 1: ADCXHI writes the carry-out to the fresh slot `cfNew`.
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg cfNew
        (carryOutBit (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf))))).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg cfNew] (withWidthTag 64 "ADCXHI") [.reg dst, .reg src, .reg cfN], .reg none) ls
      = some ls1 := lsemStepMem_adcxhi3 cfNew dst src cfN ls _ _ _ hva hvb hvc
  -- reads for step 2 are unchanged (ADCXHI wrote `cfNew`, distinct from dst/src/cfN).
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_dst), hva]
  have hvb1 : ls1.reg.getW src 64 = some (s.regs src) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_src), hvb]
  have hvc1 : ls1.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_cf), hvc]
  -- Step 2: ADCX writes the data to `dst`.
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (addCarryWord (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf))))).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX") [.reg dst, .reg src, .reg cfN], .reg none) ls1
      = some ls2 := lsemStepMem_adcx3 dst dst src cfN ls1 _ _ _ hva1 hvb1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  -- The correspondence to the `JState` `.adcx` result.
  · set co : Bool := (waddcarry (s.regs dst) (s.regs src) (s.flagB (·.cf))).1 with hco
    set res : BitVec 64 := (waddcarry (s.regs dst) (s.regs src) (s.flagB (·.cf))).2 with hres
    have hrun : runBlock s [.adcx dst (.reg src)] =
        { regs := fun r' => if r' = dst then res else s.regs r'
          flags := { s.flags with cf := some co }, mem := s.mem } := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, JOperand.eval, JState.get,
        hco, hres]
    rw [hrun]
    -- data value: addCarryWord = res
    have hdata : addCarryWord (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf))) = res := by
      rw [hres]; exact adcx_data_eq _ _ _
    -- carry value: carryOutBit = flagBit co
    have hcarry : carryOutBit (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf))) = flagBit co := by
      rw [hco]; exact adcx_carry_eq _ _ _
    have h_dst_of : dst ≠ ofN := by rintro rfl; exact hdst hcorr.ofFlg
    refine ⟨?_, ?_, ?_, ?_, hNew, hcorr.ofFlg, ?_⟩
    · -- regAgree off flg
      intro r hr
      have hr_ne_new : r ≠ cfNew := by rintro rfl; exact hr hNew
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp
      · simp only [hls2, hls1, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_ne_new]
        rw [hcorr.regAgree r hr]; simp [hrd]
    · -- memAgree
      intro base off; exact hcorr.memAgree base off
    · -- cfAgree at the new slot cfNew
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ hNe_dst, LstateN.getW_setReg_same]
      rw [hcarry]
      simp only [JState.flagB, Option.getD_some]
    · -- ofAgree unchanged (adcx wrote only cf)
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h_dst_of),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_of)]
      exact hcorr.ofAgree
    · exact hNe_of

/-- **Per-opcode agreement for the register-source `.adox` (OF chain).** Identical
    to `adcx_case` on the `OF` slot: `.adox` reads/writes `OF`, and its lsem image
    is the same structured `ADCX`/`ADCXHI` carry realizer threading `ofN`. -/
theorem adox_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN)
    (dst src ofNew : String)
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) (hNew : flg ofNew)
    (hNe_dst : ofNew ≠ dst) (hNe_src : ofNew ≠ src) (hNe_of : ofNew ≠ ofN) (hNe_cf : ofNew ≠ cfN) :
    ∃ ls', lsemStraightMem
        [ (.Lopn [.reg ofNew] (withWidthTag 64 "ADCXHI") [.reg dst, .reg src, .reg ofN], .reg none),
          (.Lopn [.reg dst]   (withWidthTag 64 "ADCX")   [.reg dst, .reg src, .reg ofN], .reg none) ]
        ls = some ls' ∧
      JLstateCorrF (runBlock s [.adox dst (.reg src)]) ls' flg cfN ofNew := by
  have hva : ls.reg.getW dst 64 = some (s.regs dst) := hcorr.regAgree dst hdst
  have hvb : ls.reg.getW src 64 = some (s.regs src) := hcorr.regAgree src hsrc
  have hvc : ls.reg.getW ofN 1 = some (flagBit (s.flagB (·.of))) := hcorr.ofAgree
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg ofNew
        (carryOutBit (s.regs dst) (s.regs src) (flagBit (s.flagB (·.of))))).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg ofNew] (withWidthTag 64 "ADCXHI") [.reg dst, .reg src, .reg ofN], .reg none) ls
      = some ls1 := lsemStepMem_adcxhi3 ofNew dst src ofN ls _ _ _ hva hvb hvc
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_dst), hva]
  have hvb1 : ls1.reg.getW src 64 = some (s.regs src) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_src), hvb]
  have hvc1 : ls1.reg.getW ofN 1 = some (flagBit (s.flagB (·.of))) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_of), hvc]
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (addCarryWord (s.regs dst) (s.regs src) (flagBit (s.flagB (·.of))))).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX") [.reg dst, .reg src, .reg ofN], .reg none) ls1
      = some ls2 := lsemStepMem_adcx3 dst dst src ofN ls1 _ _ _ hva1 hvb1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  · set co : Bool := (waddcarry (s.regs dst) (s.regs src) (s.flagB (·.of))).1 with hco
    set res : BitVec 64 := (waddcarry (s.regs dst) (s.regs src) (s.flagB (·.of))).2 with hres
    have hrun : runBlock s [.adox dst (.reg src)] =
        { regs := fun r' => if r' = dst then res else s.regs r'
          flags := { s.flags with of := some co }, mem := s.mem } := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, JOperand.eval, JState.get,
        hco, hres]
    rw [hrun]
    have hdata : addCarryWord (s.regs dst) (s.regs src) (flagBit (s.flagB (·.of))) = res := by
      rw [hres]; exact adcx_data_eq _ _ _
    have hcarry : carryOutBit (s.regs dst) (s.regs src) (flagBit (s.flagB (·.of))) = flagBit co := by
      rw [hco]; exact adcx_carry_eq _ _ _
    have h_dst_cf : dst ≠ cfN := by rintro rfl; exact hdst hcorr.cfFlg
    refine ⟨?_, ?_, ?_, ?_, hcorr.cfFlg, hNew, ?_⟩
    · intro r hr
      have hr_ne_new : r ≠ ofNew := by rintro rfl; exact hr hNew
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp
      · simp only [hls2, hls1, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_ne_new]
        rw [hcorr.regAgree r hr]; simp [hrd]
    · intro base off; exact hcorr.memAgree base off
    · -- cfAgree unchanged (adox wrote only of)
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h_dst_cf),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_cf)]
      exact hcorr.cfAgree
    · -- ofAgree at the new slot ofNew
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ hNe_dst, LstateN.getW_setReg_same]
      rw [hcarry]
      simp only [JState.flagB, Option.getD_some]
    · exact Ne.symm hNe_cf

/-! ## 10. The dual-carry MAC column (the fragment the rolled loop needs)

`selectMulxMac acc a b cy hi lo = [mulx hi lo a b; adcx acc lo; adox acc cy]` is
the repeated multiply-accumulate column of the point-op field multiply: a full
`MULX` product then the two independent-carry accumulates (`CF` via `adcx`, `OF`
via `adox`). It is **entirely register-source**, so it lies inside the bridged
subset: `mulx` (flag-transparent, `mulx_caseF`) then the two carry-op agreements
(`adcx_case` / `adox_case`), composed on all three axes. `mac_column_lsem_agree`
below is the concrete corollary. (The surrounding `emitColumnReset` adds the
immediate-carry `materialiseCarry` gadget and a register-`mov`, the named
residuals of §9.) -/

/-- **`mulx` under the flag correspondence.** `mulx` writes two data registers and
    touches no flag, so it preserves `JLstateCorrF` on every axis (the flag slots
    `cfN` / `ofN` are untouched because they are flag names and the destinations
    are not). The flag analogue of `mulx_case`. -/
theorem mulx_caseF (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN)
    (dstHi dstLo a b : String)
    (hHi : ¬ flg dstHi) (hLo : ¬ flg dstLo) (hA : ¬ flg a) (hB : ¬ flg b)
    (hLoA : dstLo ≠ a) (hLoB : dstLo ≠ b) (hHiLo : dstHi ≠ dstLo) :
    ∃ ls', lsemStraightMem (jToRMs (.mulx dstHi dstLo (.reg a) (.reg b))) ls = some ls' ∧
      JLstateCorrF (runBlock s [.mulx dstHi dstLo (.reg a) (.reg b)]) ls' flg cfN ofN := by
  have hva : ls.reg.getW a 64 = some (s.regs a) := hcorr.regAgree a hA
  have hvb : evalOperandN ls.reg 64 (.reg b) = some (s.regs b) := by
    simpa [evalOperandN] using hcorr.regAgree b hB
  set lo : BitVec 64 := (s.regs a) * (s.regs b) with hlo
  set ls1 : LstateM := { ls with reg := (ls.reg.setReg dstLo lo).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg dstLo] (withWidthTag 64 "MUL") [.reg a, .reg b], .reg none) ls = some ls1 :=
    lsemStepMem_regArith3 dstLo a (.reg b) ls "MUL" (stripWidthTag_withWidthTag_binOpName' 64 .mul) (by decide) (by decide)
      (by decide) (by decide) (s.regs a) (s.regs b) lo hva hvb rfl
  have hva1 : ls1.reg.getW a 64 = some (s.regs a) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hLoA), hva]
  have hvb1 : ls1.reg.getW b 64 = some (s.regs b) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hLoB), hcorr.regAgree b hB]
  set hi : BitVec 64 := mulHiW (s.regs a) (s.regs b) with hhi
  set ls2 : LstateM := { ls1 with reg := (ls1.reg.setReg dstHi hi).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dstHi] (withWidthTag 64 "MULXHI") [.reg a, .reg b], .reg none) ls1 = some ls2 :=
    lsemStepMem_mulhi3 dstHi a b ls1 (s.regs a) (s.regs b) hva1 hvb1
  have hHi_ne_cf : dstHi ≠ cfN := by rintro rfl; exact hHi hcorr.cfFlg
  have hHi_ne_of : dstHi ≠ ofN := by rintro rfl; exact hHi hcorr.ofFlg
  have hLo_ne_cf : dstLo ≠ cfN := by rintro rfl; exact hLo hcorr.cfFlg
  have hLo_ne_of : dstLo ≠ ofN := by rintro rfl; exact hLo hcorr.ofFlg
  have hrun : runBlock s [.mulx dstHi dstLo (.reg a) (.reg b)]
      = (s.setReg dstLo lo).setReg dstHi hi := by
    rw [hlo, hhi]
    simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
    rw [mulLo_eq (s.regs a) (s.regs b), mulHi_eq (s.regs a) (s.regs b)]
  refine ⟨ls2, ?_, ?_⟩
  · simp only [jToRMs, lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  · rw [hrun]
    refine ⟨?_, ?_, ?_, ?_, hcorr.cfFlg, hcorr.ofFlg, hcorr.cf_ne_of⟩
    · -- regAgree
      intro r hr
      by_cases hrhi : r = dstHi
      · subst hrhi
        simp only [hls2, hls1, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        simp [JState.setReg]
      · by_cases hrlo : r = dstLo
        · subst hrlo
          simp only [hls2, hls1, LstateN.getW_nextPc,
            LstateN.getW_setReg_other _ _ _ _ _ hrhi, LstateN.getW_setReg_same]
          simp [JState.setReg, hrhi]
        · simp only [hls2, hls1, LstateN.getW_nextPc,
            LstateN.getW_setReg_other _ _ _ _ _ hrhi, LstateN.getW_setReg_other _ _ _ _ _ hrlo]
          rw [hcorr.regAgree r hr]
          simp only [JState.setReg, ite_eq_right hrhi, ite_eq_right hrlo]
    · intro base off; exact hcorr.memAgree base off
    · -- cfAgree unchanged
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hHi_ne_cf),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hLo_ne_cf)]
      simpa only [JState.flagB] using! hcorr.cfAgree
    · -- ofAgree unchanged
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hHi_ne_of),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hLo_ne_of)]
      simpa only [JState.flagB] using! hcorr.ofAgree

/-- **The dual-carry MAC column bridges on all axes.** For the register-source
    column `[mulx hi lo a b; adcx acc lo; adox acc cy]`, with fresh CF/OF slots
    `cfNew` / `ofNew` and the natural register distinctness, the concatenated lsem
    lowering runs to completion under `lsemStraightMem` and its result corresponds —
    on the register, memory, `CF` and `OF` axes — to the `runBlock` column, with the
    updated designated slots `cfNew` / `ofNew`. This is the machine-model agreement
    for the field-multiply MAC unit the rolled loop repeats. -/
theorem mac_column_lsem_agree (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (cfN ofN acc a b cy hi lo cfNew ofNew : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN)
    -- the column registers are real (off the flag namespace)
    (hAcc : ¬ flg acc) (hA : ¬ flg a) (hB : ¬ flg b) (hCy : ¬ flg cy)
    (hHi : ¬ flg hi) (hLo : ¬ flg lo)
    -- `mulx` aliasing
    (hLoA : lo ≠ a) (hLoB : lo ≠ b) (hHiLo : hi ≠ lo)
    -- fresh CF slot for the `adcx`
    (hcfNew : flg cfNew) (hcf_acc : cfNew ≠ acc) (hcf_lo : cfNew ≠ lo)
    (hcf_cf : cfNew ≠ cfN) (hcf_of : cfNew ≠ ofN)
    -- fresh OF slot for the `adox`
    (hofNew : flg ofNew) (hof_acc : ofNew ≠ acc) (hof_cy : ofNew ≠ cy)
    (hof_of : ofNew ≠ ofN) (hof_cf : ofNew ≠ cfNew) (hof_cfN : ofNew ≠ cfN) :
    ∃ ls',
      lsemStraightMem
        (jToRMs (JInstr.mulx hi lo (JOperand.reg a) (JOperand.reg b))
          ++ [ (LinstrR.Lopn [LOperand.reg cfNew] (withWidthTag 64 "ADCXHI")
                  [LOperand.reg acc, LOperand.reg lo, LOperand.reg cfN], MemTag.reg none),
               (LinstrR.Lopn [LOperand.reg acc] (withWidthTag 64 "ADCX")
                  [LOperand.reg acc, LOperand.reg lo, LOperand.reg cfN], MemTag.reg none) ]
          ++ [ (LinstrR.Lopn [LOperand.reg ofNew] (withWidthTag 64 "ADCXHI")
                  [LOperand.reg acc, LOperand.reg cy, LOperand.reg ofN], MemTag.reg none),
               (LinstrR.Lopn [LOperand.reg acc] (withWidthTag 64 "ADCX")
                  [LOperand.reg acc, LOperand.reg cy, LOperand.reg ofN], MemTag.reg none) ])
        ls = some ls' ∧
      JLstateCorrF
        (runBlock s [.mulx hi lo (.reg a) (.reg b), .adcx acc (.reg lo), .adox acc (.reg cy)])
        ls' flg cfNew ofNew := by
  -- Step 1: the `MULX` product (flag-transparent).
  obtain ⟨ls1, hstep1, hcorr1⟩ :=
    mulx_caseF s ls flg cfN ofN hcorr hi lo a b hHi hLo hA hB hLoA hLoB hHiLo
  set s1 : JState 64 := runBlock s [.mulx hi lo (.reg a) (.reg b)] with hs1
  -- Step 2: the `CF`-chain accumulate `adcx acc lo`.
  obtain ⟨ls2, hstep2, hcorr2⟩ :=
    adcx_case s1 ls1 flg cfN ofN hcorr1 acc lo cfNew hAcc hLo hcfNew hcf_acc hcf_lo hcf_cf hcf_of
  set s2 : JState 64 := runBlock s1 [.adcx acc (.reg lo)] with hs2
  -- Step 3: the `OF`-chain accumulate `adox acc cy`.
  obtain ⟨ls3, hstep3, hcorr3⟩ :=
    adox_case s2 ls2 flg cfNew ofN hcorr2 acc cy ofNew hAcc hCy hofNew hof_acc hof_cy hof_of hof_cf
  refine ⟨ls3, ?_, ?_⟩
  · -- concatenate the three straight-line lowerings (the list is `(A ++ B) ++ C`)
    have hAB : lsemStraightMem
        (jToRMs (JInstr.mulx hi lo (JOperand.reg a) (JOperand.reg b))
          ++ [ (LinstrR.Lopn [LOperand.reg cfNew] (withWidthTag 64 "ADCXHI")
                  [LOperand.reg acc, LOperand.reg lo, LOperand.reg cfN], MemTag.reg none),
               (LinstrR.Lopn [LOperand.reg acc] (withWidthTag 64 "ADCX")
                  [LOperand.reg acc, LOperand.reg lo, LOperand.reg cfN], MemTag.reg none) ])
        ls = some ls2 := by
      rw [lsemStraightMem_append, hstep1, Option.bind]; exact hstep2
    rw [lsemStraightMem_append, hAB, Option.bind]; exact hstep3
  · -- the `runBlock` column peels into the three single-instruction steps
    have hpeel : runBlock s [.mulx hi lo (.reg a) (.reg b), .adcx acc (.reg lo), .adox acc (.reg cy)]
        = runBlock (runBlock (runBlock s [.mulx hi lo (.reg a) (.reg b)]) [.adcx acc (.reg lo)])
            [.adox acc (.reg cy)] := by
      simp only [runBlock_cons, runBlock_nil]
    rw [hpeel, ← hs1, ← hs2]; exact hcorr3

/-! ## 11. The loop lift: the straight-line agreement carries over a counted loop

The straight-line bridge (`runBlock_lsem_agree` / `runBlock_lsem_agreeM`) closes
the machine-model agreement for **one** pass of an in-subset body. A point-op
ladder / MSM repeats that body under a runtime trip count: the `JState` side folds
it with `LoopUnroll.runBoundedLoop`, the lsem side with `runBoundedLoopMem` (the
same body-fold, resetting the pc to the loop top after each trip). Because both
folds run the body once then recurse on the *same* remaining trip count, the
per-trip straight-line agreement lifts by induction on the trip count — the piece
the export-faithful loop headline's per-trip `hsim` obligation consumes on the
`JLstateCorr` axis. The only new content is that the back-edge `setLpc` is
invisible to `JLstateCorr` (the pc is off both the register-value and memory
axes). -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop in
/-- `JLstateCorr` is insensitive to the loop back-edge `setLpc`: the program
    counter lives on the register half's `lpc` field, off both the register-value
    map (`getW` reads only `lvm`) and the memory carrier (`lmem` is untouched), so
    resetting it preserves the correspondence definitionally. -/
theorem JLstateCorr_setLpc (s : JState 64) (ls : LstateM) (h : JLstateCorr s ls)
    (pc : Nat) : JLstateCorr s (ls.setLpc pc) where
  regAgree r := h.regAgree r
  memAgree base off := h.memAgree base off

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The loop lift (ALU-core + memory subset).** A whole straight-line body `b`
    all of whose opcodes are in `InFieldArithSubset`, iterated `n` times, agrees on
    both machine models: the `n`-fold `runBoundedLoopMem` over the lowered body
    `b.map jToRM` runs to completion (no failure) and its result corresponds — via
    `JLstateCorr` — to the `JState`-side `n`-fold `LoopUnroll.runBoundedLoop`. Proof
    by induction on the trip count: each trip is one `runBlock_lsem_agree`, and the
    inter-trip `setLpc 1` is absorbed by `JLstateCorr_setLpc`. This is the counted-
    loop machine-model agreement the point-op ladder repeats. -/
theorem runBlock_lsem_agree_loop (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InFieldArithSubset i) (n : Nat) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', runBoundedLoopMem (b.map jToRM) n ls = some ls' ∧
      JLstateCorr (runBoundedLoop s n b) ls' := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨ls1, hstep1, hcorr1⟩ := runBlock_lsem_agree b hb s ls h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s b) (ls1.setLpc 1) (JLstateCorr_setLpc _ _ hcorr1 1)

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The loop lift (ALU-core + memory + `mulx` subset).** As `runBlock_lsem_agree_loop`
    but over the wider `InSubsetM` fragment (adding the two-write `mulx`), whose
    per-instruction lowering `jToRMs` is list-valued (`mulx` lowers 1→2), so the
    per-trip body-fold is over the concatenated lowering `b.flatMap jToRMs`. Each
    trip is one `runBlock_lsem_agreeM`; the back-edge `setLpc` is again absorbed by
    `JLstateCorr_setLpc`. This is the counted-loop agreement for a body containing
    the field-multiply MAC unit (register-source `mulx`). -/
theorem runBlock_lsem_agreeM_loop (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InSubsetM i) (n : Nat) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', runBoundedLoopMem (b.flatMap jToRMs) n ls = some ls' ∧
      JLstateCorr (runBoundedLoop s n b) ls' := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨ls1, hstep1, hcorr1⟩ := runBlock_lsem_agreeM b hb s ls h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s b) (ls1.setLpc 1) (JLstateCorr_setLpc _ _ hcorr1 1)

/-! ## 12. The flag-axis loop lift (the ADX field-multiply body under a counted loop)

The loop lifts of §11 carry the register + memory correspondence (`JLstateCorr`)
over a counted body. The Curve25519 field multiply threads the two independent
carry chains through `adcx` / `adox`, whose lsem twins allocate a *fresh* CF / OF
slot (`cfNew` / `ofNew`) per accumulate (§9–§10). So the natural per-trip
correspondence is the flag-aware `JLstateCorrF`, and the fresh-slot allocation
means a trip that *begins* in the canonical flag namespace `(cfN, ofN)` ends, after
the MAC columns, in a migrated namespace `(cfNew, ofNew)`.

For the body to iterate, the back-edge must **re-establish the canonical flag
namespace**: the emitted body ends by renaming the live carry slots back to
`(cfN, ofN)`, so that the *next* trip again begins in `JLstateCorrF s ls flg cfN
ofN` with the very same designated slots. The loop lift below takes that
re-establishment as the per-trip contract on the body — a single-pass agreement
that returns to the **same** `(cfN, ofN)` — and lifts it over the runtime trip
count by induction, exactly as §11 does on the flag-free axis. The only new
content over §11 is that the back-edge `setLpc` is invisible to `JLstateCorrF`
too (the pc is off the register-value, memory, and flag axes). -/

/-- `JLstateCorrF` is insensitive to the loop back-edge `setLpc`: the program
    counter lives on the register half's `lpc` field, off the register-value map
    (`getW` reads only `lvm`), the memory carrier (`lmem`), and the two designated
    flag slots (also read by `getW`), so resetting it preserves every axis
    definitionally. The flag analogue of `JLstateCorr_setLpc`. -/
theorem JLstateCorrF_setLpc (s : JState 64) (ls : LstateM) (flg : String → Prop)
    (cfN ofN : String) (h : JLstateCorrF s ls flg cfN ofN) (pc : Nat) :
    JLstateCorrF s (ls.setLpc pc) flg cfN ofN where
  regAgree r := h.regAgree r
  memAgree base off := h.memAgree base off
  cfAgree := h.cfAgree
  ofAgree := h.ofAgree
  cfFlg := h.cfFlg
  ofFlg := h.ofFlg
  cf_ne_of := h.cf_ne_of

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The flag-axis loop lift.** A counted loop whose emitted body `lbody` runs
    one pass of the source body `body` under the flag-aware correspondence and
    **re-establishes the canonical flag namespace** — i.e. maps `JLstateCorrF s ls
    flg cfN ofN` to `JLstateCorrF (runBlock s body) ls' flg cfN ofN` with the SAME
    designated `(cfN, ofN)` slots (the fresh per-accumulate slots renamed back at
    the back-edge) — lifts to the `n`-fold loop: the `n`-fold `runBoundedLoopMem`
    over `lbody` runs to completion and its result corresponds — on the register,
    memory, and both carry axes — to the `JState`-side `n`-fold `runBoundedLoop`
    over `body`, still in the canonical namespace.

    Proof by induction on the trip count, exactly as `runBlock_lsem_agree_loop`:
    each trip is one application of the per-trip contract `hbody`, and the
    inter-trip `setLpc 1` is absorbed by `JLstateCorrF_setLpc`. This is the
    counted-loop machine-model agreement for the ADX field-multiply body (the
    dual-carry MAC columns of `mac_column_lsem_agree` followed by the flag-slot
    re-establishment) that the Montgomery ladder repeats. -/
theorem runBlock_lsem_agreeF_loop (body : List (JInstr 64)) (lbody : List LinstrRM)
    (flg : String → Prop) (cfN ofN : String)
    (hbody : ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem lbody ls = some ls' ∧
        JLstateCorrF (runBlock s body) ls' flg cfN ofN)
    (n : Nat) (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg cfN ofN) :
    ∃ ls', runBoundedLoopMem lbody n ls = some ls' ∧
      JLstateCorrF (runBoundedLoop s n body) ls' flg cfN ofN := by
  induction n generalizing s ls with
  | zero => exact ⟨ls, rfl, h⟩
  | succ k ih =>
      obtain ⟨ls1, hstep1, hcorr1⟩ := hbody s ls h
      rw [runBoundedLoopMem_succ, hstep1, Option.bind_some, runBoundedLoop_succ]
      exact ih (runBlock s body) (ls1.setLpc 1) (JLstateCorrF_setLpc _ _ _ _ _ hcorr1 1)

/-! ## 13. The call boundary: modular composition across (inlined) calls

The straight-line, loop, and flag lifts above all live on the `JState` machine
model, whose instruction type `JInstr` has **no call constructor** — `runBlock` is
a *flat* fold with no program environment, so it is inherently intra-procedural.
The `.Lcall` opcode exists only on the lsem side, where the program-indexed
`lsemFuelCallN` (`JasminLsemGeneralFaithfulCallN`) runs the callee body and returns
under a call frame. Two ways a call can be handled therefore split cleanly:

* **Inlining** (the front pass `ComInline.inline`, which replaces an `extCall`
  expression with the callee's renamed body at the `Com jasminDialect` level): the
  emitted caller body is then **call-free** `JInstr` on the `runBlock` side and
  **call-free** `LinstrRM` on the lsem side, so the call boundary reduces to block
  *concatenation*, which the straight-line bridge already handles. For a static
  call graph of bounded depth — every cryptographic kernel here — inlining fully
  discharges the inter-procedural obligation, and the composition below is its
  machine-model witness.

* **A non-inlined `.Lcall`** kept on the lsem side under `lsemFuelCallN`:
  tying it to the `runBlock` side would need a `JState` call model (a `.Lcall`
  constructor with a frame save/return in `runBlock`, or a program-indexed
  `runProg` fold), which does not exist. `JasminLsemGeneralFaithfulCallN` supplies
  the lsem half of that story (`Com → lsem`, not `runBlock → lsem`); the JState
  call-frame model is the residual, needed only for recursive / unbounded-depth
  call graphs the crypto surface does not contain.

This section proves the **modular composition primitive** for the inlining route:
if two blocks are *each* bridged (as a black-box `runBlock ↔ lsem` agreement
hypothesis — exactly the "prove per-function" contract), their sequential
composition is bridged, and hence `runBlock_lsem_agree` composes across a call
site whose callee is inlined. The callee agreement is a *hypothesis*, never
re-derived — this is the CompCert / Jasmin "compose across calls" capability,
realized at the inlined-body granularity. -/

/-- `runBlock` distributes over concatenation: running `b1 ++ b2` is running `b1`
    then `b2` from the resulting state. The `JState`-side twin of
    `lsemStraightMem_append`; the block-composition step of the call boundary. -/
theorem runBlock_append (s : JState 64) (b1 b2 : List (JInstr 64)) :
    runBlock s (b1 ++ b2) = runBlock (runBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons, ih]

/-- **Modular composition of two bridged blocks (register + memory axis).** Given
    two blocks `b1`, `b2` that are *each* independently bridged — each mapping any
    `JLstateCorr`-corresponding pair to a corresponding pair under its own lsem
    lowering `lb1` / `lb2` (the black-box "prove per-function" contract) — their
    sequential composition `b1 ++ b2` is bridged under the concatenated lowering
    `lb1 ++ lb2`. This is the call-boundary composition primitive: the callee
    agreement `h2` is a *hypothesis*, so `runBlock_lsem_agree` composes across an
    inlined call without re-deriving the callee. -/
theorem runBlock_lsem_agree_seq
    (b1 b2 : List (JInstr 64)) (lb1 lb2 : List LinstrRM)
    (h1 : ∀ (s : JState 64) (ls : LstateM), JLstateCorr s ls →
      ∃ ls', lsemStraightMem lb1 ls = some ls' ∧ JLstateCorr (runBlock s b1) ls')
    (h2 : ∀ (s : JState 64) (ls : LstateM), JLstateCorr s ls →
      ∃ ls', lsemStraightMem lb2 ls = some ls' ∧ JLstateCorr (runBlock s b2) ls')
    (s : JState 64) (ls : LstateM) (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (lb1 ++ lb2) ls = some ls' ∧
      JLstateCorr (runBlock s (b1 ++ b2)) ls' := by
  obtain ⟨ls1, hstep1, hcorr1⟩ := h1 s ls h
  obtain ⟨ls2, hstep2, hcorr2⟩ := h2 (runBlock s b1) ls1 hcorr1
  refine ⟨ls2, ?_, ?_⟩
  · rw [lsemStraightMem_append, hstep1, Option.bind]; exact hstep2
  · rw [runBlock_append]; exact hcorr2

/-- **The call boundary composes (register + memory axis).** A caller consisting of
    an in-subset straight-line prefix `pre`, an inlined callee body `fbody`, and an
    in-subset straight-line suffix `post` is bridged, *given only* a black-box
    `runBlock ↔ lsem` agreement for the callee (`hcallee`, with the callee's own
    lowering `lfbody`). The caller's inlined body `pre ++ fbody ++ post` lowers to
    `pre.map jToRM ++ lfbody ++ post.map jToRM` and its execution corresponds — on
    both axes — to `runBlock`. So `runBlock_lsem_agree` composes across an inlined
    call site: the callee is proved once and reused (not re-derived). This is the
    inter-procedural / modular-simulation capability, at the inlining granularity
    that a bounded static call graph (every crypto kernel) admits. -/
theorem runBlock_lsem_agree_call
    (pre post fbody : List (JInstr 64)) (lfbody : List LinstrRM)
    (hpre : ∀ i ∈ pre, InFieldArithSubset i)
    (hpost : ∀ i ∈ post, InFieldArithSubset i)
    (hcallee : ∀ (s : JState 64) (ls : LstateM), JLstateCorr s ls →
      ∃ ls', lsemStraightMem lfbody ls = some ls' ∧ JLstateCorr (runBlock s fbody) ls')
    (s : JState 64) (ls : LstateM) (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (pre.map jToRM ++ lfbody ++ post.map jToRM) ls = some ls' ∧
      JLstateCorr (runBlock s (pre ++ fbody ++ post)) ls' := by
  have hpreFbody :
      ∀ (s : JState 64) (ls : LstateM), JLstateCorr s ls →
        ∃ ls', lsemStraightMem (pre.map jToRM ++ lfbody) ls = some ls' ∧
          JLstateCorr (runBlock s (pre ++ fbody)) ls' :=
    fun s ls h => runBlock_lsem_agree_seq pre fbody (pre.map jToRM) lfbody
      (fun s ls h => runBlock_lsem_agree pre hpre s ls h) hcallee s ls h
  exact runBlock_lsem_agree_seq (pre ++ fbody) post (pre.map jToRM ++ lfbody) (post.map jToRM)
    hpreFbody (fun s ls h => runBlock_lsem_agree post hpost s ls h) s ls h

/-- **Modular composition of two bridged blocks (flag/carry axis).** The
    `JLstateCorrF` analogue of `runBlock_lsem_agree_seq`: two ADX-carrying blocks
    that each preserve the canonical carry namespace `(cfN, ofN)` — mapping
    `JLstateCorrF _ _ flg cfN ofN` to itself — compose sequentially in the same
    namespace. This is the call-boundary composition for a callee that threads the
    two carry chains and re-establishes `(cfN, ofN)` at return (the same per-pass
    contract `runBlock_lsem_agreeF_loop` consumes), so a dual-carry field-multiply
    body composes across an inlined call. -/
theorem runBlock_lsem_agreeF_seq
    (b1 b2 : List (JInstr 64)) (lb1 lb2 : List LinstrRM)
    (flg : String → Prop) (cfN ofN : String)
    (h1 : ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem lb1 ls = some ls' ∧ JLstateCorrF (runBlock s b1) ls' flg cfN ofN)
    (h2 : ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem lb2 ls = some ls' ∧ JLstateCorrF (runBlock s b2) ls' flg cfN ofN)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg cfN ofN) :
    ∃ ls', lsemStraightMem (lb1 ++ lb2) ls = some ls' ∧
      JLstateCorrF (runBlock s (b1 ++ b2)) ls' flg cfN ofN := by
  obtain ⟨ls1, hstep1, hcorr1⟩ := h1 s ls h
  obtain ⟨ls2, hstep2, hcorr2⟩ := h2 (runBlock s b1) ls1 hcorr1
  refine ⟨ls2, ?_, ?_⟩
  · rw [lsemStraightMem_append, hstep1, Option.bind]; exact hstep2
  · rw [runBlock_append]; exact hcorr2

/-! ## 14. The unrolled ADX field-multiply: namespace-MIGRATING composition

The fixed-namespace composition of §13 (`runBlock_lsem_agreeF_seq`) and the loop
lift of §12 (`runBlock_lsem_agreeF_loop`) both require the per-pass body to
**return to the same** designated slots `(cfN, ofN)`. A single dual-carry MAC
column does **not**: `mac_column_lsem_agree` allocates a *fresh* CF/OF slot pair
`(cfNew, ofNew)` per column (§10), so it maps the correspondence from `(cfN, ofN)`
to the *migrated* `(cfNew, ofNew)`. Returning to `(cfN, ofN)` would need a
register-to-register slot rename, which has **no arm in the `lsemStepMem`
delegate chain** (`JasminLsemMemFlagGuard.lean` records this: "the register-copy
form has no arm anywhere in the `lsemStepMem` delegate chain").

But the Curve25519 field multiply is **fully unrolled** — a fixed straight-line
chain of MAC columns, not a runtime loop — so no rename is needed: successive
columns simply thread the carry through the *previous* column's fresh slots. The
matching compositional primitive is therefore a **namespace-migrating** sequential
composition: `b1` migrates `(cfN, ofN)` to `(cf1, of1)`, `b2` migrates
`(cf1, of1)` to `(cf2, of2)`, and their concatenation migrates `(cfN, ofN)` to
`(cf2, of2)`. Because the fresh slots are distinct per column and the unrolled
body has a *fixed* number of columns, the whole chain of fresh names is
statically allocable — exactly the setting a rename-free unrolled multiply needs.
`runBlock_lsem_agreeF_seq_migrate` is that primitive; `mac2_columns_lsem_agree`
is the concrete two-column ADX field-multiply witness it produces from
`mac_column_lsem_agree`. -/

/-- **Namespace-migrating flag-axis sequential composition.** The `agreeF_seq`
    variant where each block MIGRATES the designated carry slots: `b1` moves the
    namespace `(cfN, ofN)` to `(cf1, of1)`, `b2` moves `(cf1, of1)` to
    `(cf2, of2)`; their concatenation `b1 ++ b2` moves `(cfN, ofN)` to
    `(cf2, of2)`. This is the compositional primitive the FULLY-UNROLLED ADX field
    multiply needs: each MAC column allocates a fresh CF/OF slot pair
    (`mac_column_lsem_agree`), so successive columns chain through a *migrating*
    namespace rather than the fixed one `runBlock_lsem_agreeF_seq` requires. The
    proof is the same block-concatenation as the fixed-namespace variant — the
    output namespace is simply `b2`'s, not the input one. -/
theorem runBlock_lsem_agreeF_seq_migrate
    (b1 b2 : List (JInstr 64)) (lb1 lb2 : List LinstrRM)
    (flg : String → Prop) (cfN ofN cf1 of1 cf2 of2 : String)
    (h1 : ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem lb1 ls = some ls' ∧ JLstateCorrF (runBlock s b1) ls' flg cf1 of1)
    (h2 : ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cf1 of1 →
      ∃ ls', lsemStraightMem lb2 ls = some ls' ∧ JLstateCorrF (runBlock s b2) ls' flg cf2 of2)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg cfN ofN) :
    ∃ ls', lsemStraightMem (lb1 ++ lb2) ls = some ls' ∧
      JLstateCorrF (runBlock s (b1 ++ b2)) ls' flg cf2 of2 := by
  obtain ⟨ls1, hstep1, hcorr1⟩ := h1 s ls h
  obtain ⟨ls2, hstep2, hcorr2⟩ := h2 (runBlock s b1) ls1 hcorr1
  refine ⟨ls2, ?_, ?_⟩
  · rw [lsemStraightMem_append, hstep1, Option.bind]; exact hstep2
  · rw [runBlock_append]; exact hcorr2

/-- The lowered straight-line lsem body of one dual-carry MAC column
    `[mulx hi lo a b; adcx acc lo; adox acc cy]`, with carry-in slots `(cfN, ofN)`
    and fresh carry-out slots `(cfNew, ofNew)`: the `MULX` pair, then the `CF`
    accumulate (`ADCXHI cfNew; ADCX acc`, both reading `cfN`), then the `OF`
    accumulate (`ADCXHI ofNew; ADCX acc`, both reading `ofN`). This is exactly the
    list `mac_column_lsem_agree` bridges; naming it makes the two-column
    concatenation readable. -/
def macColumnL (acc a b cy hi lo cfN ofN cfNew ofNew : String) : List LinstrRM :=
  jToRMs (JInstr.mulx hi lo (JOperand.reg a) (JOperand.reg b))
    ++ [ (LinstrR.Lopn [LOperand.reg cfNew] (withWidthTag 64 "ADCXHI")
            [LOperand.reg acc, LOperand.reg lo, LOperand.reg cfN], MemTag.reg none),
         (LinstrR.Lopn [LOperand.reg acc] (withWidthTag 64 "ADCX")
            [LOperand.reg acc, LOperand.reg lo, LOperand.reg cfN], MemTag.reg none) ]
    ++ [ (LinstrR.Lopn [LOperand.reg ofNew] (withWidthTag 64 "ADCXHI")
            [LOperand.reg acc, LOperand.reg cy, LOperand.reg ofN], MemTag.reg none),
         (LinstrR.Lopn [LOperand.reg acc] (withWidthTag 64 "ADCX")
            [LOperand.reg acc, LOperand.reg cy, LOperand.reg ofN], MemTag.reg none) ]

/-- The source-side one-column MAC block `[mulx hi lo a b; adcx acc lo; adox acc cy]`. -/
def macColumnJ (acc a b cy hi lo : String) : List (JInstr 64) :=
  [.mulx hi lo (.reg a) (.reg b), .adcx acc (.reg lo), .adox acc (.reg cy)]

/-- `mac_column_lsem_agree` repackaged over `macColumnL` / `macColumnJ` and in the
    `∀ s ls, JLstateCorrF → …` shape the migrating-seq composition consumes: one
    ADX MAC column bridges `runBlock ↔ lsem`, migrating `(cfN, ofN)` to the fresh
    `(cfNew, ofNew)`. -/
theorem macColumn_agree (flg : String → Prop)
    (cfN ofN acc a b cy hi lo cfNew ofNew : String)
    (hAcc : ¬ flg acc) (hA : ¬ flg a) (hB : ¬ flg b) (hCy : ¬ flg cy)
    (hHi : ¬ flg hi) (hLo : ¬ flg lo)
    (hLoA : lo ≠ a) (hLoB : lo ≠ b) (hHiLo : hi ≠ lo)
    (hcfNew : flg cfNew) (hcf_acc : cfNew ≠ acc) (hcf_lo : cfNew ≠ lo)
    (hcf_cf : cfNew ≠ cfN) (hcf_of : cfNew ≠ ofN)
    (hofNew : flg ofNew) (hof_acc : ofNew ≠ acc) (hof_cy : ofNew ≠ cy)
    (hof_of : ofNew ≠ ofN) (hof_cf : ofNew ≠ cfNew) (hof_cfN : ofNew ≠ cfN) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem (macColumnL acc a b cy hi lo cfN ofN cfNew ofNew) ls = some ls' ∧
        JLstateCorrF (runBlock s (macColumnJ acc a b cy hi lo)) ls' flg cfNew ofNew :=
  fun s ls hcorr =>
    mac_column_lsem_agree s ls flg cfN ofN acc a b cy hi lo cfNew ofNew hcorr
      hAcc hA hB hCy hHi hLo hLoA hLoB hHiLo
      hcfNew hcf_acc hcf_lo hcf_cf hcf_of hofNew hof_acc hof_cy hof_of hof_cf hof_cfN

/-- **Two dual-carry MAC columns compose end-to-end under `JLstateCorrF`.** The
    concrete witness that the existing per-column bridge (`mac_column_lsem_agree`)
    composes through the migrating-namespace sequential lift: two ADX MAC columns
    over a shared accumulator `acc` (column 1 = `a1·b1`, column 2 = `a2·b2`, the
    carry chain threaded `(cfN, ofN) → (cf1, of1) → (cf2, of2)`) run to completion
    under `lsemStraightMem` on the concatenated lowering and their result
    corresponds — on the register, memory, `CF` and `OF` axes — to the `runBlock`
    two-column block, in the final migrated namespace `(cf2, of2)`. This is the
    machine-model agreement for a two-term slice of the unrolled Curve25519 field
    multiply: the carry propagates across columns exactly as the ADX
    `mulx`/`adcx`/`adox` schedule intends, with no rename step. -/
theorem mac2_columns_lsem_agree (flg : String → Prop)
    (cfN ofN cf1 of1 cf2 of2 acc cy hi lo a1 b1 a2 b2 : String)
    -- real (off-flag) column registers
    (hAcc : ¬ flg acc) (hCy : ¬ flg cy) (hHi : ¬ flg hi) (hLo : ¬ flg lo)
    (hA1 : ¬ flg a1) (hB1 : ¬ flg b1) (hA2 : ¬ flg a2) (hB2 : ¬ flg b2)
    -- `mulx` aliasing (shared temporaries `hi`/`lo`, distinct per column inputs)
    (hLoA1 : lo ≠ a1) (hLoB1 : lo ≠ b1) (hLoA2 : lo ≠ a2) (hLoB2 : lo ≠ b2) (hHiLo : hi ≠ lo)
    -- column-1 fresh slots
    (hcf1 : flg cf1) (hcf1_acc : cf1 ≠ acc) (hcf1_lo : cf1 ≠ lo)
    (hcf1_cf : cf1 ≠ cfN) (hcf1_of : cf1 ≠ ofN)
    (hof1 : flg of1) (hof1_acc : of1 ≠ acc) (hof1_cy : of1 ≠ cy)
    (hof1_of : of1 ≠ ofN) (hof1_cf1 : of1 ≠ cf1) (hof1_cfN : of1 ≠ cfN)
    -- column-2 fresh slots (carry-in is now `(cf1, of1)`)
    (hcf2 : flg cf2) (hcf2_acc : cf2 ≠ acc) (hcf2_lo : cf2 ≠ lo)
    (hcf2_cf1 : cf2 ≠ cf1) (hcf2_of1 : cf2 ≠ of1)
    (hof2 : flg of2) (hof2_acc : of2 ≠ acc) (hof2_cy : of2 ≠ cy)
    (hof2_of1 : of2 ≠ of1) (hof2_cf2 : of2 ≠ cf2) (hof2_cf1 : of2 ≠ cf1)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg cfN ofN) :
    ∃ ls', lsemStraightMem
        (macColumnL acc a1 b1 cy hi lo cfN ofN cf1 of1
          ++ macColumnL acc a2 b2 cy hi lo cf1 of1 cf2 of2) ls = some ls' ∧
      JLstateCorrF
        (runBlock s (macColumnJ acc a1 b1 cy hi lo ++ macColumnJ acc a2 b2 cy hi lo))
        ls' flg cf2 of2 :=
  runBlock_lsem_agreeF_seq_migrate
    (macColumnJ acc a1 b1 cy hi lo) (macColumnJ acc a2 b2 cy hi lo)
    (macColumnL acc a1 b1 cy hi lo cfN ofN cf1 of1)
    (macColumnL acc a2 b2 cy hi lo cf1 of1 cf2 of2)
    flg cfN ofN cf1 of1 cf2 of2
    (macColumn_agree flg cfN ofN acc a1 b1 cy hi lo cf1 of1
      hAcc hA1 hB1 hCy hHi hLo hLoA1 hLoB1 hHiLo
      hcf1 hcf1_acc hcf1_lo hcf1_cf hcf1_of hof1 hof1_acc hof1_cy hof1_of hof1_cf1 hof1_cfN)
    (macColumn_agree flg cf1 of1 acc a2 b2 cy hi lo cf2 of2
      hAcc hA2 hB2 hCy hHi hLo hLoA2 hLoB2 hHiLo
      hcf2 hcf2_acc hcf2_lo hcf2_cf1 hcf2_of1 hof2 hof2_acc hof2_cy hof2_of1 hof2_cf2 hof2_cf1)
    s ls h

/-! ## 11. The subtract-with-borrow column (`sbb` / `sbbhi`, CF-only correspondence)

`sbb dst src` is the borrow-chain limb `dst := dst − src − CF`. Unlike `adcx`
(which touches only `CF`), `sbb` is a full SUB-style op that clobbers **all five**
flags, so its correspondence is the `CF`-only `JLstateCorrCF`, not `JLstateCorrF`.
Its lsem image is the structured `SBBHI`/`SBB` carry realizer threading the `CF`
slot — the dual of the `ADCXHI`/`ADCX` pair. -/

/-- **`sbb` data agreement.** The lsem borrow-subtract word `subBorrowWord v1 v2 (bit
    c)` equals the `JState` `SBB` data output `(x86_SBB v1 v2 c).word`. Both are the
    two's-complement `v1 − v2 − [c]` up to the modular wrap. -/
theorem subBorrowWord_flagBit_eq (v1 v2 : BitVec 64) (c : Bool) :
    subBorrowWord v1 v2 (flagBit c) = (x86_SBB v1 v2 c).word := by
  apply BitVec.eq_of_toNat_eq
  have hx : v1.toNat < 2 ^ 64 := v1.isLt
  have hy : v2.toNat < 2 ^ 64 := v2.isLt
  have hne : ((2 ^ 64 : Nat) : Int) ≠ 0 := by norm_num
  have hR : ((x86_SBB v1 v2 c).word.toNat : Int)
      = ((v1.toNat : Int) - v2.toNat - (if c then 1 else 0)) % ((2 ^ 64 : Nat) : Int) := by
    simp only [x86_SBB, sub_borrow, BitVec.toNat_ofInt]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hne)]
    push_cast
    ring_nf
  simp only [subBorrowWord, BitVec.toNat_sub, BitVec.toNat_ofNat, flagBit_toNat]
  cases c <;> simp_all <;> omega

/-- **`sbb` borrow-out agreement.** The lsem borrow-out bit `borrowOutBit v1 v2 (bit
    c)` equals the flag bit of the `JState` `SBB` carry-out `(x86_SBB v1 v2 c).cf`.
    Both fire iff the unbounded difference `v1 − v2 − [c]` went negative. -/
theorem borrowOutBit_flagBit_eq (v1 v2 : BitVec 64) (c : Bool) :
    borrowOutBit v1 v2 (flagBit c) = flagBit ((x86_SBB v1 v2 c).cf.getD false) := by
  have hx : v1.toNat < 2 ^ 64 := v1.isLt
  have hy : v2.toNat < 2 ^ 64 := v2.isLt
  have hne : ((2 ^ 64 : Nat) : Int) ≠ 0 := by norm_num
  have hcf : (x86_SBB v1 v2 c).cf.getD false
      = decide (v1.toNat < v2.toNat + (if c then 1 else 0)) := by
    simp only [x86_SBB, wunsigned, Option.getD_some]
    refine decide_eq_decide.mpr ?_
    have hR : ((sub_borrow v1 v2 (if c then 1 else 0)).toNat : Int)
        = ((v1.toNat : Int) - v2.toNat - (if c then 1 else 0)) % ((2 ^ 64 : Nat) : Int) := by
      simp only [sub_borrow, BitVec.toNat_ofInt]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hne)]
      push_cast
      ring_nf
    rw [hR]
    cases c <;> simp <;> omega
  rw [hcf, borrowOutBit, flagBit_toNat]
  by_cases h : v1.toNat < v2.toNat + (if c then 1 else 0) <;> simp [h, flagBit]

/-- **The lsem twin of a three-address structured `SBB` wire** (`dst := subBorrowWord
    a b c`, borrow-in `c` at width 1). The data half of an `sbb` lowering — the dual
    of `lsemStepMem_adcx3`. -/
theorem lsemStepMem_sbb3 (dst a b c : String) (ls : LstateM) (va vb : BitVec 64) (vc : BitVec 1)
    (hva : ls.reg.getW a 64 = some va) (hvb : ls.reg.getW b 64 = some vb)
    (hvc : ls.reg.getW c 1 = some vc) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "SBB") [.reg a, .reg b, .reg c], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (subBorrowWord va vb vc)).nextPc } := by
  have hstep : lsemStepMC
      (.Lopn [.reg dst] (withWidthTag 64 "SBB") [.reg a, .reg b, .reg c]) ls.reg
      = some ((ls.reg.setReg dst (subBorrowWord va vb vc)).nextPc) := by
    simp only [lsemStepMC, mulhiStruct?_sbb, adcxStruct?_sbb, adcxhiStruct?_sbb, sbbStruct?_sbb,
      readReg_of_getW hva, hvb, hvc]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl), hstep]
  rfl

/-- **The lsem twin of a three-address structured `SBBHI` wire** (`dst := borrowOutBit
    a b c`, a `BitVec 1`). The borrow-out half of an `sbb` lowering — the dual of
    `lsemStepMem_adcxhi3`. -/
theorem lsemStepMem_sbbhi3 (dst a b c : String) (ls : LstateM) (va vb : BitVec 64) (vc : BitVec 1)
    (hva : ls.reg.getW a 64 = some va) (hvb : ls.reg.getW b 64 = some vb)
    (hvc : ls.reg.getW c 1 = some vc) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "SBBHI") [.reg a, .reg b, .reg c], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (borrowOutBit va vb vc)).nextPc } := by
  have hstep : lsemStepMC
      (.Lopn [.reg dst] (withWidthTag 64 "SBBHI") [.reg a, .reg b, .reg c]) ls.reg
      = some ((ls.reg.setReg dst (borrowOutBit va vb vc)).nextPc) := by
    simp only [lsemStepMC, mulhiStruct?_sbbhi, adcxStruct?_sbbhi, adcxhiStruct?_sbbhi,
      sbbStruct?_sbbhi, sbbhiStruct?_sbbhi, readReg_of_getW hva, hvb, hvc]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl), hstep]
  rfl

/-- `JLstateCorrCF s ls flg cfN`: the register+memory correspondence **plus** a
    single `CF` flag slot. Unlike `JLstateCorrF` there is no `OF` axis: `sbb`
    clobbers all five flags, so only the designated `CF` slot `cfN` (in the synthetic
    flag namespace `flg`) is tracked against `s.flags.cf`. -/
structure JLstateCorrCF (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN : String) :
    Prop where
  /-- Register agreement off the flag namespace. -/
  regAgree : ∀ r : String, ¬ flg r → ls.reg.getW r 64 = some (s.regs r)
  /-- Memory agreement. -/
  memAgree : ∀ (base : String) (off : Int), ls.lmem base off = s.mem base off
  /-- The designated `CF` slot mirrors `s.flags.cf`. -/
  cfAgree : ls.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf)))
  /-- The `CF` slot is a flag name. -/
  cfFlg : flg cfN

/-- **Per-opcode agreement for the register-source `.sbb` (CF chain).** Given a fresh
    CF-slot `cfNew` (a flag name distinct from `dst`, `src`, `cfN`), the pair
    `[SBBHI cfNew; SBB dst]` — both reading the current slot `cfN` — does not fail and
    its result satisfies `JLstateCorrCF` with the new CF slot `cfNew`, matching the
    in-place `.sbb dst (.reg src)` on the register, `CF`, and memory axes. -/
theorem sbb_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN : String)
    (hcorr : JLstateCorrCF s ls flg cfN) (dst src cfNew : String)
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) (hNew : flg cfNew)
    (hNe_dst : cfNew ≠ dst) (hNe_src : cfNew ≠ src) (hNe_cf : cfNew ≠ cfN) :
    ∃ ls', lsemStraightMem
        [ (.Lopn [.reg cfNew] (withWidthTag 64 "SBBHI") [.reg dst, .reg src, .reg cfN], .reg none),
          (.Lopn [.reg dst]   (withWidthTag 64 "SBB")   [.reg dst, .reg src, .reg cfN], .reg none) ]
        ls = some ls' ∧
      JLstateCorrCF (runBlock s [.sbb dst (.reg src)]) ls' flg cfNew := by
  have hva : ls.reg.getW dst 64 = some (s.regs dst) := hcorr.regAgree dst hdst
  have hvb : ls.reg.getW src 64 = some (s.regs src) := hcorr.regAgree src hsrc
  have hvc : ls.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := hcorr.cfAgree
  -- Step 1: SBBHI writes the borrow-out to the fresh slot `cfNew`.
  set ls1 : LstateM :=
    { ls with reg := (ls.reg.setReg cfNew
        (borrowOutBit (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf))))).nextPc } with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg cfNew] (withWidthTag 64 "SBBHI") [.reg dst, .reg src, .reg cfN], .reg none) ls
      = some ls1 := lsemStepMem_sbbhi3 cfNew dst src cfN ls _ _ _ hva hvb hvc
  -- reads for step 2 are unchanged (SBBHI wrote `cfNew`, distinct from dst/src/cfN).
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_dst), hva]
  have hvb1 : ls1.reg.getW src 64 = some (s.regs src) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_src), hvb]
  have hvc1 : ls1.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hNe_cf), hvc]
  -- Step 2: SBB writes the data to `dst`.
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (subBorrowWord (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf))))).nextPc } with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "SBB") [.reg dst, .reg src, .reg cfN], .reg none) ls1
      = some ls2 := lsemStepMem_sbb3 dst dst src cfN ls1 _ _ _ hva1 hvb1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · simp only [lsemStraightMem_cons, hstep1, hstep2, lsemStraightMem_nil]
  -- The correspondence to the `JState` `.sbb` result.
  · have hrun : runBlock s [.sbb dst (.reg src)]
        = s.writeB5W dst (x86_SBB (s.regs dst) (s.regs src) (s.flagB (·.cf))) := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, JState.get]
    rw [hrun]
    have hdata : subBorrowWord (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf)))
        = (x86_SBB (s.regs dst) (s.regs src) (s.flagB (·.cf))).word :=
      subBorrowWord_flagBit_eq _ _ _
    have hcarry : borrowOutBit (s.regs dst) (s.regs src) (flagBit (s.flagB (·.cf)))
        = flagBit ((x86_SBB (s.regs dst) (s.regs src) (s.flagB (·.cf))).cf.getD false) :=
      borrowOutBit_flagBit_eq _ _ _
    refine ⟨?_, ?_, ?_, hNew⟩
    · -- regAgree off flg
      intro r hr
      have hr_ne_new : r ≠ cfNew := by rintro rfl; exact hr hNew
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp [JState.writeB5W]
      · simp only [hls2, hls1, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_ne_new]
        rw [hcorr.regAgree r hr]; simp [JState.writeB5W, hrd]
    · -- memAgree
      intro base off
      simp only [JState.writeB5W]
      exact hcorr.memAgree base off
    · -- cfAgree at the new slot cfNew
      simp only [hls2, hls1, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ hNe_dst, LstateN.getW_setReg_same]
      rw [hcarry]
      simp only [JState.flagB, JState.writeB5W_flags]

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
