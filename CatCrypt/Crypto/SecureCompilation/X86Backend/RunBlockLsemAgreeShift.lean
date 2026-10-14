/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the immediate-count shifts

`RunBlockLsemAgree.lean` bridges the total `JState` fold `runBlock` and the
partial `LstateM` fold `lsemStraightMem` on `InFieldArithSubset` (the two-address
register ALU core plus the compile-time-offset word memory ops). This module
extends the bridged subset with the three immediate-count shifts `shl` / `shr` /
`sar` and lifts the extension over a whole straight-line block.

## The wire

The lsem image of `.shl dst (.imm n)` is the structured shift instruction
`shiftLinstr "SHL" 64 dst (.reg dst) n = Lopn [.reg dst] "SHL:64" [.reg dst,
.imm n]` (`VIR/JasminLsemShift.lean`), the two-address form with the count in the
`.imm` operand; `.shr` and `.sar` are the same with base mnemonic `"SHR"` /
`"SAR"`. `SHL` and `SHR` are in the shared `applyOpnN` and step through
`lsemStepN`'s generic binop arm; `SAR` is the structured arm of `lsemStepSh`,
recognised by `sarStruct?`.

## The count range

`JState`'s `x86_SHL` / `x86_SHR` / `x86_SAR` mask the count with `shiftCount
i = i.toNat % 64`; the lsem side shifts by `i.toNat` unmasked. The two therefore
agree exactly when the count is below the word width, which is the side condition
`n < 64` carried on each shift arm of `InShiftSubset`.

## Opcodes outside this extension

* A **register-count** shift (`.shl dst (.reg r)`) has no syntactic count bound:
  `applyOpnN 64 "SHL" [a, b] = a <<< b.toNat` and
  `(x86_SHL a b).word = a <<< (b.toNat % 64)` differ at every `b` with
  `b.toNat ≥ 64`. The `SAR` recognizer `sarStruct?` additionally requires the
  second source to be an `.imm`.
* `.neg dst` has no lsem image: `applyOpnN` carries no `NEG` (nor `NOT`) arm and
  no layer of the `lsemStepMem → lsemStepCast → lsemStepMC → lsemStepSh →
  lsemStepN` chain has a structured unary-negate recognizer. `SUB [.imm 0, .reg dst]`
  steps at `lsemStepN` (`lsemStepN_immFirst`, at width `widthFromTag`).
* `.storeMem base off (.imm n)` has no lsem image: `storeCStruct?` matches only
  `Lopn [.arr base off] "MOVQ" [.reg src]` and the `.storeC` arm reads the source
  through `LstateN.getW`.

## Main results

* `InShiftSubset`: the covered opcode set — `InFieldArithSubset` plus
  `shl`/`shr`/`sar` at an immediate count below the width.
* `jToRMSh`: the `JInstr` to wire lowering for that set.
* `jToRMSh_agrees`: per-opcode totality and `JLstateCorr` preservation.
* `runBlock_lsem_agreeSh`: the block-induction lift over a whole straight-line block.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift

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

/-! ## 1. The masked count on an in-range immediate -/

/-- A count below the word width is below `2 ^ 64`, the range hypothesis the
    structured-shift representation squares take. -/
theorem lt_two_pow_64_of_lt {n : Nat} (h : n < 64) : n < 2 ^ 64 := by
  have : (64 : Nat) ≤ 2 ^ 64 := by decide
  omega

/-- For a count below the word width the `JState` shift mask is the identity:
    `shiftCount (BitVec.ofNat 64 n) = n`. -/
theorem shiftCount_ofNat_of_lt {n : Nat} (h : n < 64) :
    shiftCount (BitVec.ofNat 64 n) = n := by
  have h64 : n < 2 ^ 64 := lt_two_pow_64_of_lt h
  simp only [shiftCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h]

/-! ## 2. The `JState` shift data words on an in-range immediate count -/

/-- The `x86_SHL` data word at an in-range immediate count is the plain left
    shift `v <<< n` (the count mask and the `wshl` clamp are both vacuous). -/
theorem x86_SHL_word_ofNat {n : Nat} (h : n < 64) (v : BitVec 64) :
    (x86_SHL v (BitVec.ofNat 64 n)).word = v <<< n := by
  have hmin : min 64 n = n := by omega
  simp only [x86_SHL, shiftCount_ofNat_of_lt h]
  by_cases h0 : n = 0
  · subst h0; simp [rflags_None]
  · simp only [if_neg h0, rflags_OF, wshl, hmin]

/-- The `x86_SHR` data word at an in-range immediate count is the plain logical
    right shift `v >>> n`. -/
theorem x86_SHR_word_ofNat {n : Nat} (h : n < 64) (v : BitVec 64) :
    (x86_SHR v (BitVec.ofNat 64 n)).word = v >>> n := by
  have hmin : min 64 n = n := by omega
  simp only [x86_SHR, shiftCount_ofNat_of_lt h]
  by_cases h0 : n = 0
  · subst h0; simp [rflags_None]
  · simp only [if_neg h0, rflags_OF, wshr, hmin]

/-- The `x86_SAR` data word at an in-range immediate count is the plain
    arithmetic right shift `BitVec.sshiftRight v n`. -/
theorem x86_SAR_word_ofNat {n : Nat} (h : n < 64) (v : BitVec 64) :
    (x86_SAR v (BitVec.ofNat 64 n)).word = BitVec.sshiftRight v n := by
  have hmin : min 64 n = n := by omega
  simp only [x86_SAR, shiftCount_ofNat_of_lt h]
  by_cases h0 : n = 0
  · subst h0; simp [rflags_None]
  · simp only [if_neg h0, rflags_OF, wsar, hmin]

/-! ## 3. The lsem-side value and step reductions -/

/-- The `applyOpnN` value of the structured `SHL` wire at an in-range count. -/
theorem applyOpnN_SHL_ofNat {n : Nat} (h : n < 64) (a : BitVec 64) :
    applyOpnN 64 "SHL" [a, BitVec.ofNat 64 n] = some (a <<< n) := by
  rw [applyOpnN_SHL, structShl_eq (lt_two_pow_64_of_lt h), shiftMask_of_lt h]

/-- The `applyOpnN` value of the structured `SHR` wire at an in-range count. -/
theorem applyOpnN_SHR_ofNat {n : Nat} (h : n < 64) (a : BitVec 64) :
    applyOpnN 64 "SHR" [a, BitVec.ofNat 64 n] = some (a >>> n) := by
  rw [applyOpnN_SHR, structShr_eq (lt_two_pow_64_of_lt h), shiftMask_of_lt h]

/-- **The lsem twin of a structured `SAR` wire.** The `.reg none`-tagged
    `shiftLinstr "SAR"` instruction reads its source at width 64, writes
    `BitVec.sshiftRight` of it by the operand count, and does not fail. -/
theorem lsemStepMem_sarImm (dst src : String) (n : Nat) (ls : LstateM) (va : BitVec 64)
    (hva : ls.reg.getW src 64 = some va) :
    lsemStepMem (shiftLinstr "SAR" 64 dst (.reg src) n, .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (BitVec.sshiftRight va n)).nextPc } := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_shiftLinstr (w := 64) "SAR" dst (.reg src) n
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  simp only [lsemStepSh, sarStruct?_shiftLinstr_SAR, readReg_of_getW hva, Option.map_some]

/-! ## 4. The lowering and the per-opcode agreement -/

/-- `jToRMSh`: `jToRM` extended with the immediate-count shifts. Each shift
    lowers to the structured shift wire `shiftLinstr mnem 64 dst (.reg dst) n`
    (two-address, count in the `.imm` operand); every other opcode keeps its
    `jToRM` image. -/
def jToRMSh : JInstr 64 → LinstrRM
  | .shl dst (.imm n) => (shiftLinstr "SHL" 64 dst (.reg dst) n, .reg none)
  | .shr dst (.imm n) => (shiftLinstr "SHR" 64 dst (.reg dst) n, .reg none)
  | .sar dst (.imm n) => (shiftLinstr "SAR" 64 dst (.reg dst) n, .reg none)
  | i => jToRM i

/-- `InFieldArithSubset` extended with the three immediate-count shifts, each
    carrying the count-range side condition `n < 64` under which the `JState`
    count mask is vacuous. Every other opcode defers to `InFieldArithSubset`. -/
def InShiftSubset : JInstr 64 → Prop
  | .shl _ (.imm n) => n < 64
  | .shr _ (.imm n) => n < 64
  | .sar _ (.imm n) => n < 64
  | i => InFieldArithSubset i

/-- **Factored `SHL`/`SHR` case.** For a base mnemonic no structured recognizer
    claims, the structured shift wire over the `.imm` count does not fail and its
    result corresponds: the destination receives the `applyOpnN` value, memory is
    unchanged. -/
theorem shiftImm_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) (n : Nat) (base : String) (v : BitVec 64)
    (hstrip : stripWidthTag (withWidthTag 64 base) = base)
    (h1 : base ≠ "MULXHI") (h2 : base ≠ "ADCX") (h3 : base ≠ "ADCXHI") (h4 : base ≠ "SAR")
    (hop : applyOpnN 64 base [s.get dst, BitVec.ofNat 64 n] = some v)
    (jinstr : JInstr 64)
    (hrun : ∀ r, (runBlock s [jinstr]).regs r = if r = dst then v else s.regs r)
    (hmemrun : ∀ b o, (runBlock s [jinstr]).mem b o = s.mem b o) :
    ∃ ls', lsemStraightMem [(shiftLinstr base 64 dst (.reg dst) n, .reg none)] ls = some ls' ∧
      JLstateCorr (runBlock s [jinstr]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst v hrun hmemrun⟩
  rw [lsemStraightMem_single]
  exact lsemStepMem_regArith dst base (.imm n) ls hstrip h1 h2 h3 h4
    (s.get dst) (BitVec.ofNat 64 n) v (hcorr.regAgree dst) rfl hop

/-- **Per-opcode agreement for `.shl dst (.imm n)`** at an in-range count. -/
theorem shlImm_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) (n : Nat) (h : n < 64) :
    ∃ ls', lsemStraightMem [jToRMSh (.shl dst (.imm n))] ls = some ls' ∧
      JLstateCorr (runBlock s [.shl dst (.imm n)]) ls' := by
  refine shiftImm_case s ls hcorr dst n "SHL" (s.get dst <<< n)
    (stripWidthTag_withWidthTag_SHL 64) (by decide) (by decide) (by decide) (by decide)
    (applyOpnN_SHL_ofNat h _) (.shl dst (.imm n)) ?_ ?_
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, JOperand.eval,
      x86_SHL_word_ofNat h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]

/-- **Per-opcode agreement for `.shr dst (.imm n)`** at an in-range count. -/
theorem shrImm_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) (n : Nat) (h : n < 64) :
    ∃ ls', lsemStraightMem [jToRMSh (.shr dst (.imm n))] ls = some ls' ∧
      JLstateCorr (runBlock s [.shr dst (.imm n)]) ls' := by
  refine shiftImm_case s ls hcorr dst n "SHR" (s.get dst >>> n)
    (stripWidthTag_withWidthTag_SHR 64) (by decide) (by decide) (by decide) (by decide)
    (applyOpnN_SHR_ofNat h _) (.shr dst (.imm n)) ?_ ?_
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, JOperand.eval,
      x86_SHR_word_ofNat h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]

/-- **Per-opcode agreement for `.sar dst (.imm n)`** at an in-range count. The
    structured `SAR` arm of `lsemStepSh` supplies the lsem side. -/
theorem sarImm_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) (n : Nat) (h : n < 64) :
    ∃ ls', lsemStraightMem [jToRMSh (.sar dst (.imm n))] ls = some ls' ∧
      JLstateCorr (runBlock s [.sar dst (.imm n)]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst
    (BitVec.sshiftRight (s.get dst) n) ?_ ?_⟩
  · show lsemStraightMem [(shiftLinstr "SAR" 64 dst (.reg dst) n, .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_sarImm dst dst n ls (s.get dst) (hcorr.regAgree dst)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, JOperand.eval,
      x86_SAR_word_ofNat h]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]

/-- **Per-opcode agreement on the shift-extended subset.** For an `InShiftSubset`
    opcode the lsem twin `lsemStraightMem [jToRMSh i]` does not fail and its
    result corresponds — via `JLstateCorr` — to the `runBlock` result. The three
    shift arms are the cases above; every other opcode defers to
    `jToRM_agrees`. -/
theorem jToRMSh_agrees (i : JInstr 64) (hi : InShiftSubset i)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem [jToRMSh i] ls = some ls' ∧ JLstateCorr (runBlock s [i]) ls' := by
  cases i
  case shl dst src =>
    cases src
    case imm n => exact shlImm_case s ls hcorr dst n hi
    case reg r => exact hi.elim
  case shr dst src =>
    cases src
    case imm n => exact shrImm_case s ls hcorr dst n hi
    case reg r => exact hi.elim
  case sar dst src =>
    cases src
    case imm n => exact sarImm_case s ls hcorr dst n hi
    case reg r => exact hi.elim
  case mov dst src => exact jToRM_agrees (.mov dst src) hi s ls hcorr
  case add dst src => exact jToRM_agrees (.add dst src) hi s ls hcorr
  case sub dst src => exact jToRM_agrees (.sub dst src) hi s ls hcorr
  case imul dst src => exact jToRM_agrees (.imul dst src) hi s ls hcorr
  case and_ dst src => exact jToRM_agrees (.and_ dst src) hi s ls hcorr
  case or_ dst src => exact jToRM_agrees (.or_ dst src) hi s ls hcorr
  case xor_ dst src => exact jToRM_agrees (.xor_ dst src) hi s ls hcorr
  case loadMem dst base off => exact jToRM_agrees (.loadMem dst base off) hi s ls hcorr
  case storeMem base off src => exact jToRM_agrees (.storeMem base off src) hi s ls hcorr
  all_goals exact hi.elim

/-! ## 5. Block-level lift -/

/-- **Block-level agreement over the shift-extended subset.** A whole
    straight-line block all of whose opcodes are in `InShiftSubset` runs to
    completion under `lsemStraightMem` on `b.map jToRMSh` and its result
    corresponds — on the register and the memory axis — to the `runBlock` result.
    Straight-line induction on the block. -/
theorem runBlock_lsem_agreeSh (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InShiftSubset i) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (b.map jToRMSh) ls = some ls' ∧ JLstateCorr (runBlock s b) ls' := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨ls1, hstep1, hcorr1⟩ := jToRMSh_agrees i (hb i (List.mem_cons_self ..)) s ls h
    have hstep : lsemStepMem (jToRMSh i) ls = some ls1 := by
      rwa [lsemStraightMem_single] at hstep1
    obtain ⟨ls', hstep', hcorr'⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) (runBlock s [i]) ls1 hcorr1
    have hri : runBlock s (i :: is) = runBlock (runBlock s [i]) is := by
      simp only [runBlock_cons, runBlock_nil]
    refine ⟨ls', ?_, ?_⟩
    · simp only [List.map_cons, lsemStraightMem_cons, hstep]
      have hri' : runBlock (evalInstr s i) is = runBlock (runBlock s [i]) is := by
        simp only [runBlock_cons, runBlock_nil]
      rw [hri'] at *
      exact hstep'
    · rw [hri]; exact hcorr'

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift
