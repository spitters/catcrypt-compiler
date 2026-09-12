/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the unary two's-complement negate

`RunBlockLsemAgree.lean` bridges the total `JState` fold `runBlock` and the
partial `LstateM` fold `lsemStraightMem` on `InFieldArithSubset` (the two-address
register ALU core plus the compile-time-offset word memory ops);
`RunBlockLsemAgreeShift.lean` extends the bridged subset with the immediate-count
shifts. This module extends it further with `JInstr.neg`, the two's-complement
negate that carries the constant-time mask idiom `neg m; and m, q`.

## The wire

The lsem image of `.neg dst` is the one-source instruction
`negLinstr 64 dst (.reg dst)` = `Lopn [.reg dst] "NEG:64" [.reg dst]`, matching jasmin's
`Ox86 (NEG ws)` arity and the lowering `Fe25519LfundefBridge.lean` emits. It is
stepped by `lsemStepN`'s `regUn` arm — the one-source arm gated on the stripped
mnemonic `"NEG"` — whose value comes from `applyOpnN`'s `"NEG"` entry
`0 - a`. The tag is the register binding `.reg none`, so `lsemStepMem` reaches
that arm through the delegation chain `lsemStepCast → lsemStepMC → lsemStepSh →
lsemStepN`, no structured recognizer claiming the wire on the way down. The
agreement is therefore stated over the same `lsemStraightMem` fold as
`runBlock_lsem_agree` and `runBlock_lsem_agreeSh`.

## The flags

`x86_NEG` returns a `B5W` (word plus five flags) and `evalInstr` writes it with
`JState.writeB5W`, exactly as `add`/`sub` do. `JLstateCorr` tracks registers and
memory only, so the flag writes are discharged through the `JState.writeB5W`
simp lemmas.

## Opcodes outside this extension

A register-count shift, `.storeMem` with an immediate source, and the
flag-reading opcodes remain outside the subset for the reasons
`RunBlockLsemAgreeShift.lean` records.

## Main results

* `negStruct?`: the recognizer for the unary negate wire.
* `InNegSubset` / `jToRMNeg`: the covered set and its lowering.
* `lsemStepMem_neg`: the negate step over the real `lsemStepMem`.
* `jToRMNeg_agrees`, `runBlock_lsem_agreeNeg`: per-opcode agreement and its block lift.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The two sides' data word -/

/-- The `x86_NEG` data word is the two's-complement negation the `applyOpnN`
    `"NEG"` entry computes — the value agreement the bridge rests on. -/
theorem x86_NEG_word_eq_applyOpnN (a : BitVec 64) :
    applyOpnN 64 "NEG" [a] = some (x86_NEG a).word := rfl

/-! ## 2. The lsem-side reduction for the negate wire -/

/-- **The lsem twin of a one-source negate wire.** Given the source register
    reads `va` at width 64, `lsemStepMem` writes `0 - va` to `dst` — it does not
    fail. The five structured recognizers of the delegation chain miss the wire
    on arity alone (`mulhiStruct?`/`sarStruct?` want two source operands, the
    carry recognizers three), and the register binding tag discharges the cast
    layer. -/
theorem lsemStepMem_neg (dst src : String) (ls : LstateM) (va : BitVec 64)
    (hva : ls.reg.getW src 64 = some va) :
    lsemStepMem (negLinstr 64 dst (.reg src), .reg none) ls
      = some { ls with reg := (ls.reg.setReg dst (0 - va)).nextPc } := by
  have hm : mulhiStruct? (negLinstr 64 dst (.reg src)) = none := rfl
  have ha : adcxStruct? (negLinstr 64 dst (.reg src)) = none := rfl
  have hh : adcxhiStruct? (negLinstr 64 dst (.reg src)) = none := rfl
  have hsb : sbbStruct? (negLinstr 64 dst (.reg src)) = none := rfl
  have hsbh : sbbhiStruct? (negLinstr 64 dst (.reg src)) = none := rfl
  have hs : sarStruct? (negLinstr 64 dst (.reg src)) = none := rfl
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm ha hh hsb hsbh,
      lsemStepSh_of_not_sar _ _ hs]
  simp only [lsemStepN, negLinstr, stripWidthTag_withWidthTag_NEG, if_pos,
    readReg_of_getW hva, applyOpnN_NEG, Option.map_some]

/-! ## 3. The lowering and the per-opcode agreement -/

/-- `jToRMNeg`: `jToRMSh` extended with `.neg dst`, which lowers to the
    one-source wire `negLinstr 64 dst (.reg dst)` (the destination is also the source,
    matching `JState`'s two-address form). -/
def jToRMNeg : JInstr 64 → LinstrRM
  | .neg dst => (negLinstr 64 dst (.reg dst), .reg none)
  | i => jToRMSh i

/-- `InShiftSubset` extended with `.neg`. -/
def InNegSubset : JInstr 64 → Prop
  | .neg _ => True
  | i => InShiftSubset i

/-- Every opcode is either a `.neg`, or one whose `jToRMNeg` lowering and
    subset membership are `jToRMSh`'s and `InShiftSubset`'s. -/
theorem jToRMNeg_cases (i : JInstr 64) :
    (∃ dst, i = .neg dst) ∨
      (jToRMNeg i = jToRMSh i ∧ (InNegSubset i → InShiftSubset i)) := by
  cases i <;> first
    | exact Or.inr ⟨rfl, id⟩
    | exact Or.inl ⟨_, rfl⟩

/-- **Per-opcode agreement for `.neg dst`.** The `runBlock` side writes
    `(x86_NEG (s.get dst)).word = 0 - s.get dst` to `dst` plus five flags; the
    lsem side writes the same word, and `JLstateCorr` reads no flag. -/
theorem neg_case (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls)
    (dst : String) :
    ∃ ls', lsemStraightMem [jToRMNeg (.neg dst)] ls = some ls' ∧
      JLstateCorr (runBlock s [.neg dst]) ls' := by
  refine ⟨_, ?_, JLstateCorr_setReg s _ ls hcorr dst (0 - s.get dst) ?_ ?_⟩
  · show lsemStraightMem [(negLinstr 64 dst (.reg dst), .reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_neg dst dst ls (s.get dst) (hcorr.regAgree dst)
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, x86_NEG]
  · intro b o; simp only [runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W]

/-- **Per-opcode agreement on the negate-extended subset.** For an `InNegSubset`
    opcode the lsem twin `lsemStraightMem [jToRMNeg i]` does not fail and its
    result corresponds — via `JLstateCorr` — to the `runBlock` result. -/
theorem jToRMNeg_agrees (i : JInstr 64) (hi : InNegSubset i)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem [jToRMNeg i] ls = some ls' ∧
      JLstateCorr (runBlock s [i]) ls' := by
  rcases jToRMNeg_cases i with ⟨dst, rfl⟩ | ⟨heq, himp⟩
  · exact neg_case s ls hcorr dst
  · rw [heq]; exact jToRMSh_agrees i (himp hi) s ls hcorr

/-! ## 4. Block-level lift -/

/-- **Block-level agreement over the negate-extended subset.** A whole
    straight-line block all of whose opcodes are in `InNegSubset` runs to
    completion under `lsemStraightMem` on `b.map jToRMNeg` and its result
    corresponds — on the register and the memory axis — to the `runBlock`
    result. Straight-line induction on the block. -/
theorem runBlock_lsem_agreeNeg (b : List (JInstr 64))
    (hb : ∀ i ∈ b, InNegSubset i) (s : JState 64) (ls : LstateM)
    (h : JLstateCorr s ls) :
    ∃ ls', lsemStraightMem (b.map jToRMNeg) ls = some ls' ∧
      JLstateCorr (runBlock s b) ls' := by
  induction b generalizing s ls with
  | nil => exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    obtain ⟨ls1, hstep1, hcorr1⟩ := jToRMNeg_agrees i (hb i (List.mem_cons_self ..)) s ls h
    have hstep : lsemStepMem (jToRMNeg i) ls = some ls1 := by
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg
