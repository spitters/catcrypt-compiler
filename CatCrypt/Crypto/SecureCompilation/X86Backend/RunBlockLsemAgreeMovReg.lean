/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the register-to-register `MOV`

`RunBlockLsemAgree.lean` bridges the total `JState` fold `runBlock` and the
partial `LstateM` fold `lsemStraightMem` on `InFieldArithSubset` (the two-address
register ALU core plus the compile-time-offset word memory ops, with the
*immediate* `mov`); `RunBlockLsemAgreeNeg.lean` extends the bridged subset with
the shifts and the unary negate. This module extends it once more with the
register-source `JInstr.mov dst (.reg src)` — the `MOV dst, src` copy the
schoolbook column emits to route a materialised carry word into the carry
register (`emitColumnReset`'s trailing move).

## The wire

The lsem image of `.mov dst (.reg src)` is the one-source instruction
`Lopn [.reg dst] "MOV:64" [.reg src]` with the register-binding tag `.reg none`,
the register-source counterpart of the nullary immediate `MOV` wire
`RunBlockLsemAgree.jToRM` lowers `.mov dst (.imm n)` to. It is stepped by
`lsemStepN`'s one-source arm — the arm gated on the stripped mnemonic, now
covering `"MOV"` alongside `"NEG"` — whose value comes from `applyOpnN`'s
`"MOV"` entry (the identity on the read word). The tag is `.reg none`, so
`lsemStepMem` reaches that arm through the delegation chain
`lsemStepCast → lsemStepMC → lsemStepSh → lsemStepN`, no structured recognizer
claiming the wire on the way down.

## The flags

`x86_MOV` returns a bare word (`JState.setReg`, no flag write). `JLstateCorr`
tracks registers and memory only, so the correspondence is preserved by the
matched register write with memory untouched, exactly as for the immediate `mov`.

## Main results

* `jToRMMov` / `InMovRegSubset`: the covered set and its lowering.
* `lsemStepMem_movReg`: the register-source move step over the real `lsemStepMem`.
* `movReg_case`, `jToRMMov_agrees`, `runBlock_lsem_agreeMov`: per-opcode agreement
  and its block lift.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The lsem-side reduction for the register-source `MOV` wire -/

/-- **The lsem twin of a register-source `MOV` wire.** Given the source register
    reads `va` at width 64, `lsemStepMem` writes `va` to `dst` — it does not
    fail. The five structured recognizers of the delegation chain miss the wire
    on arity alone (the same one-source shape as the negate), and the register
    binding tag discharges the cast layer; the one-source `lsemStepN` arm dispatches
    `"MOV"` through `applyOpnN`, which is the identity on the read word. -/
theorem lsemStepMem_movReg (dst src : String) (ls : LstateM) (va : BitVec 64)
    (hva : ls.reg.getW src 64 = some va) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst va).nextPc } := by
  have hstr : stripWidthTag (withWidthTag 64 "MOV") = "MOV" :=
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar.stripWidthTag_withWidthTag_MOV 64
  have hne : ¬ (("MOV" : String) = "NEG") := by decide
  have hm : mulhiStruct? (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src]) = none := rfl
  have ha : adcxStruct? (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src]) = none := rfl
  have hh : adcxhiStruct? (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src]) = none := rfl
  have hsb : sbbStruct? (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src]) = none := rfl
  have hsbh : sbbhiStruct? (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src]) = none := rfl
  have hs : sarStruct? (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src]) = none := rfl
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm ha hh hsb hsbh,
      lsemStepSh_of_not_sar _ _ hs]
  simp only [lsemStepN, hstr, ite_eq_right hne, ite_eq_left, readReg_of_getW hva, applyOpnN_MOV,
    Option.map_some]

/-! ## 2. The lowering and the per-opcode agreement -/

/-- `jToRMMov`: `jToRMNeg` extended with the register-source `.mov dst (.reg src)`,
    which lowers to the one-source wire `Lopn [.reg dst] "MOV:64" [.reg src]`. The
    immediate `.mov dst (.imm n)` (and every other opcode) defers to `jToRMNeg`. -/
def jToRMMov : JInstr 64 → LinstrRM
  | .mov dst (.reg src) => (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], .reg none)
  | i => jToRMNeg i

/-- `InNegSubset` extended with the register-source `.mov`. The immediate `.mov`
    stays in the subset through the `jToRMNeg` chain. -/
def InMovRegSubset : JInstr 64 → Prop
  | .mov _ (.reg _) => True
  | i => InNegSubset i

/-- Every opcode is either a register-source `.mov`, or one whose `jToRMMov`
    lowering and subset membership are `jToRMNeg`'s and `InNegSubset`'s. -/
theorem jToRMMov_cases (i : JInstr 64) :
    (∃ dst src, i = .mov dst (.reg src)) ∨
      (jToRMMov i = jToRMNeg i ∧ (InMovRegSubset i → InNegSubset i)) := by
  cases i
  case mov dst src =>
    cases src with
    | reg s => exact Or.inl ⟨dst, s, rfl⟩
    | imm n => exact Or.inr ⟨rfl, id⟩
  all_goals exact Or.inr ⟨rfl, id⟩

/-- **Per-opcode agreement for `.mov dst (.reg src)`.** The `runBlock` side writes
    `x86_MOV (s.get src) = s.get src` to `dst` and touches no flag or memory cell;
    the lsem side writes the same word, and `JLstateCorr` reads no flag. -/
theorem movReg_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst src : String) :
    ∃ ls', lsemStraightMem [jToRMMov (.mov dst (.reg src))] ls = some ls' ∧
      JLstateCorr (runBlock s [.mov dst (.reg src)]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (s.regs src) ?_ ?_⟩
  · show lsemStraightMem [(.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_movReg dst src ls (s.regs src) (hcorr.regAgree src)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.get,
      JState.setReg]
  · intro b o
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg]

/-- **Per-opcode agreement on the move-extended subset.** For an `InMovRegSubset`
    opcode the lsem twin `lsemStraightMem [jToRMMov i]` does not fail and its
    result corresponds — via `JLstateCorr` — to the `runBlock` result. -/
theorem jToRMMov_agrees (i : JInstr 64) (hi : InMovRegSubset i)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem [jToRMMov i] ls = some ls' ∧
      JLstateCorr (runBlock s [i]) ls' := by
  rcases jToRMMov_cases i with ⟨dst, src, rfl⟩ | ⟨heq, himp⟩
  · exact movReg_case s ls hcorr dst src
  · rw [heq]; exact jToRMNeg_agrees i (himp hi) s ls hcorr

/-! ## 3. Block-level lift -/

/-- **Block-level agreement over the move-extended subset.** A whole
    straight-line block all of whose opcodes are in `InMovRegSubset` runs to
    completion under `lsemStraightMem` on `b.map jToRMMov` and its result
    corresponds — on the register and the memory axis — to the `runBlock`
    result. Straight-line induction on the block. -/
theorem runBlock_lsem_agreeMov (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InMovRegSubset i) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (b.map jToRMMov) ls = some ls' ∧
      JLstateCorr (runBlock s b) ls' := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨ls1, hstep1, hcorr1⟩ := jToRMMov_agrees i (hb i (List.mem_cons_self ..)) s ls h
    have hstep : lsemStepMem (jToRMMov i) ls = some ls1 := by
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

/-! ## 4. The flag-track lift -/

/-- **Per-opcode agreement for `.mov dst (.reg src)` under the flag
    correspondence.** `x86_MOV` writes one data register and touches no flag, so
    the register-source move preserves `JLstateCorrF` on every axis: the
    designated slots `cfN` / `ofN` are flag names and the destination is not, so
    the matched register write leaves both carry slots and the memory untouched.
    The `JLstateCorrF` analogue of `movReg_case`. -/
theorem movReg_caseF (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN) (dst src : String)
    (hDst : ¬ flg dst) (hSrc : ¬ flg src) :
    ∃ ls', lsemStraightMem [jToRMMov (.mov dst (.reg src))] ls = some ls' ∧
      JLstateCorrF (runBlock s [.mov dst (.reg src)]) ls' flg cfN ofN := by
  have hva : ls.reg.getW src 64 = some (s.regs src) := hcorr.regAgree src hSrc
  have hDst_cf : dst ≠ cfN := by rintro rfl; exact hDst hcorr.cfFlg
  have hDst_of : dst ≠ ofN := by rintro rfl; exact hDst hcorr.ofFlg
  refine ⟨{ ls with reg := (ls.reg.setReg dst (s.regs src)).nextPc }, ?_, ?_⟩
  · show lsemStraightMem [(.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_movReg dst src ls (s.regs src) hva
  · have hrun : runBlock s [.mov dst (.reg src)] = s.setReg dst (s.regs src) := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.get]
    rw [hrun]
    refine ⟨?_, ?_, ?_, ?_, hcorr.cfFlg, hcorr.ofFlg, hcorr.cf_ne_of⟩
    · intro r hr
      by_cases hrd : r = dst
      · subst hrd
        simp only [LstateN.getW_nextPc, LstateN.getW_setReg_same]
        simp [JState.setReg]
      · simp only [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrd]
        rw [hcorr.regAgree r hr]
        simp only [JState.setReg, ite_eq_right hrd]
    · intro base off; exact hcorr.memAgree base off
    · simp only [LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hDst_cf)]
      simpa only [JState.flagB] using! hcorr.cfAgree
    · simp only [LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hDst_of)]
      simpa only [JState.flagB] using! hcorr.ofAgree

/-- `movReg_caseF` repackaged over the explicit one-wire block and in the
    `∀ s ls, JLstateCorrF → …` shape the migrating sequential composition
    consumes: the register-source `MOV` keeps the designated carry namespace
    `(cfN, ofN)`. -/
theorem movRegWire_agree (flg : String → Prop) (cfN ofN dst src : String)
    (hDst : ¬ flg dst) (hSrc : ¬ flg src) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem
          [ (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "MOV")
              [LOperand.reg src], MemTag.reg none) ] ls = some ls' ∧
        JLstateCorrF (runBlock s [.mov dst (.reg src)]) ls' flg cfN ofN :=
  fun s ls hcorr => movReg_caseF s ls flg cfN ofN hcorr dst src hDst hSrc

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg
