/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.FieldReduce
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul

/-!
# The fused four-word Montgomery reduce on an eight-limb input

`Ascent.montRedc4RunBlock_proven` runs `Curve4MontMulProvenEmit.emitMontRedc4Block` from a
state whose reduce input is four limbs in `accNames.take 4`, with the upper window
`accNames[4..7]` and `rtop` cleared, and bound `⟦T⟧ < 2^64·⟦p⟧`. The emitted Montgomery
multiply `montMulProvenBlock` feeds the reduce the eight-limb schoolbook product of two
reduced operands, which lies below `2^256·⟦p⟧` and fills all eight accumulator registers.

This module states and proves the fused reduce for that input: from a state holding an
eight-limb `T` in `accNames` with `rtop` cleared and `⟦T⟧ < 2^256·⟦p⟧`, the top window
`accNames[4..7]` together with `rtop` reconstructs to `montRedc4 ⟦p⟧ n' ⟦T⟧`, which is
`< 2·⟦p⟧` and congruent to `⟦T⟧·2^-256` modulo `⟦p⟧`
(`RelationalFrontCiosFieldMul.montRedc4_full`).

## Main results

* `montRedcStep_chain_wide` — the carry elimination of one fused word-step, from a bound
  on the reduced value by the running window's weight.
* `stepAt_advance_wide` — one fused word-step at window offset `i` reconstructs the new
  running window to one `montgomeryReduce` step of the old one, given the reduced value
  is below `(2^64)^(8-i)`.
* `montRedc4_wide_steps_lt` — the four partial reductions of an input below `2^256·N`
  fit the four running windows.
* `montRedc4RunBlock_wide` — the fused reduce on an eight-limb input.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedcCarryFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven

/-- **Carry elimination of one fused word-step, by the window weight.** If the fused
    step's running window `accs.drop 1 ++ D` plus its carry bit reconstructs to the
    reduced value `montgomeryReduce ⟦p⟧ (2^64) n' W`, and that value lies below the
    window's weight `(2^64)^(|accs| - 1 + |D|)`, the carry is zero and the window alone
    reconstructs to the reduced value. -/
theorem montRedcStep_chain_wide (accs D : List String) (post : JState 64)
    (p : List (BitVec 64)) (nP : BitVec 64) (W : Nat)
    (hfold : valLimbs ((accs.drop 1 ++ D).map post.get)
          + (2 ^ 64) ^ (accs.length - 1 + D.length)
              * (if post.flagB (·.cf) then 1 else 0)
        = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W)
    (hMR : Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W
        < (2 ^ 64) ^ (accs.length - 1 + D.length)) :
    valLimbs ((accs.drop 1 ++ D).map post.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W := by
  have hcf1 : (if post.flagB (·.cf) then (1 : Nat) else 0) ≤ 1 := by split <;> omega
  have hwinlen : ((accs.drop 1 ++ D).map post.get).length = accs.length - 1 + D.length := by
    rw [List.length_map, List.length_append, List.length_drop]
  have ha := valLimbs_lt_pow ((accs.drop 1 ++ D).map post.get)
  rw [hwinlen] at ha
  exact (carry_elim _ _ _ _ _ hfold ha hcf1 hMR le_rfl).1

/-- **One fused word-step on a wide running value.** At window offset `i` (`i ≤ 3`), with
    the modulus in `pNames` and `n'` in `npName`, running `emitMontRedcStepAt i`
    reconstructs the new running window `win.drop 1 ++ D` to
    `montgomeryReduce ⟦p⟧ (2^64) n' (⟦win⟧ + 2^256·⟦D⟧)`, provided that value lies below
    `(2^64)^(8-i)`, the weight of the new running window. -/
theorem stepAt_advance_wide (s : JState 64) (i : Nat) (p : List (BitVec 64))
    (nP : BitVec 64) (win D : List String)
    (hwin : win = (accNames.drop i).take 4) (hD : D = accNames.drop (i + 4) ++ [rtopName])
    (hp4 : p.length = 4) (hi3 : i ≤ 3)
    (hpN : pNames.map s.get = p) (hnpv : s.get npName = nP)
    (hMR : Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
        (valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get))
        < (2 ^ 64) ^ (8 - i)) :
    valLimbs ((win.drop 1 ++ D).map (runBlock s (emitMontRedcStepAt i)).get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get)) := by
  subst hwin hD
  rw [emitMontRedcStepAt_fused i hi3]
  interval_cases i <;>
  · refine montRedcStep_chain_wide _ _ _ p nP _ ?_ hMR
    exact montRedcStep_fold_running_value s mName _ npName
      dcyName hiName loName _ pNames rcyName hiName loName _ p _ _ nP
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide)
      (by decide) hp4 (by decide) (by simp)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by rfl) hnpv hpN rfl
      (by simp) (by decide) (by simp) (by decide) (by decide) (by decide) rfl

/-- **The four partial reductions of a full-radix input fit the running windows.** For
    `N < 2^256` and `T < 2^256·N`, the successive per-word reductions
    `w₁ = redc T`, `w₂ = redc w₁`, `w₃ = redc w₂`, `w₄ = redc w₃` (radix `2^64`) lie below
    `(2^64)^8`, `(2^64)^7`, `(2^64)^6` and `(2^64)^5`. -/
theorem montRedc4_wide_steps_lt (N nP T : Nat) (hNlt : N < 2 ^ 256)
    (hT : T < 2 ^ 256 * N) :
    Number.montgomeryReduce N (2 ^ 64) nP T < (2 ^ 64) ^ (8 - 0)
      ∧ Number.montgomeryReduce N (2 ^ 64) nP (Number.montgomeryReduce N (2 ^ 64) nP T)
          < (2 ^ 64) ^ (8 - 1)
      ∧ Number.montgomeryReduce N (2 ^ 64) nP
          (Number.montgomeryReduce N (2 ^ 64) nP (Number.montgomeryReduce N (2 ^ 64) nP T))
          < (2 ^ 64) ^ (8 - 2)
      ∧ Number.montgomeryReduce N (2 ^ 64) nP (Number.montgomeryReduce N (2 ^ 64) nP
          (Number.montgomeryReduce N (2 ^ 64) nP (Number.montgomeryReduce N (2 ^ 64) nP T)))
          < (2 ^ 64) ^ (8 - 3) := by
  set w1 := Number.montgomeryReduce N (2 ^ 64) nP T with hw1
  set w2 := Number.montgomeryReduce N (2 ^ 64) nP w1 with hw2
  set w3 := Number.montgomeryReduce N (2 ^ 64) nP w2 with hw3
  set w4 := Number.montgomeryReduce N (2 ^ 64) nP w3 with hw4
  have hb1 := RelationalFrontCiosFieldMul.redc_step_mul_le N (2 ^ 64) nP T (by positivity)
  have hb2 := RelationalFrontCiosFieldMul.redc_step_mul_le N (2 ^ 64) nP w1 (by positivity)
  have hb3 := RelationalFrontCiosFieldMul.redc_step_mul_le N (2 ^ 64) nP w2 (by positivity)
  have hb4 := RelationalFrontCiosFieldMul.redc_step_mul_le N (2 ^ 64) nP w3 (by positivity)
  rw [← hw1] at hb1
  rw [← hw2] at hb2
  rw [← hw3] at hb3
  rw [← hw4] at hb4
  norm_num at hb1 hb2 hb3 hb4 hNlt hT ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The window-loaded state for the fused reduce on an eight-limb input: the eight
    accumulator registers `accNames` hold the input limbs `T`, the top-carry word `rtop`
    is cleared, the modulus limbs `p` are in `pNames`, and the Montgomery constant `nP` is
    in `npName`. -/
def MontRedc4LoadWide (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  accNames.map s.get = T ∧ s.get rtopName = 0 ∧ pNames.map s.get = p ∧ s.get npName = nP

/-- **The fused four-word reduce on an eight-limb input.** From a state loaded as
    `MontRedc4LoadWide` with `⟦T⟧ < 2^256·⟦p⟧`, running `emitMontRedc4Block`
    reconstructs the top window `accNames[4..7]` together with `rtop` to
    `montRedc4 ⟦p⟧ n' ⟦T⟧`. The carry of each word-step is eliminated by the size of
    the partial reductions alone, so neither the Montgomery constant relation nor
    `0 < ⟦p⟧` is used; `RelationalFrontCiosFieldMul.montRedc4_full` supplies the range
    and congruence of `montRedc4` under those. -/
theorem montRedc4RunBlock_wide (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64)
    (hp4 : p.length = 4)
    (hTbound : valLimbs T < 2 ^ 256 * valLimbs p)
    (hload : MontRedc4LoadWide s p T nP) :
    valLimbs ((accNames.drop 4).map (runBlock s emitMontRedc4Block).get)
      + (2 ^ 64) ^ 4 * ((runBlock s emitMontRedc4Block).get rtopName).toNat
    = montRedc4 (valLimbs p) nP.toNat (valLimbs T) := by
  obtain ⟨hall, hrtop, hpN, hnpv⟩ := hload
  have hplt : valLimbs p < 2 ^ 256 := by
    have := valLimbs_lt_pow p; rw [hp4] at this; norm_num at this ⊢; exact this
  obtain ⟨hm1, hm2, hm3, hm4⟩ :=
    montRedc4_wide_steps_lt (valLimbs p) nP.toNat (valLimbs T) hplt hTbound
  set s1 := runBlock s (emitMontRedcStepAt 0) with hs1
  set s2 := runBlock s1 (emitMontRedcStepAt 1) with hs2
  set s3 := runBlock s2 (emitMontRedcStepAt 2) with hs3
  set s4 := runBlock s3 (emitMontRedcStepAt 3) with hs4
  have k0 := stepAt_keeps s 0 (by norm_num); rw [← hs1] at k0
  have k1 := stepAt_keeps s1 1 (by norm_num); rw [← hs2] at k1
  have k2 := stepAt_keeps s2 2 (by norm_num); rw [← hs3] at k2
  have hpN1 : pNames.map s1.get = p := by rw [k0.1, hpN]
  have hnpv1 : s1.get npName = nP := by rw [k0.2, hnpv]
  have hpN2 : pNames.map s2.get = p := by rw [k1.1, hpN1]
  have hnpv2 : s2.get npName = nP := by rw [k1.2, hnpv1]
  have hpN3 : pNames.map s3.get = p := by rw [k2.1, hpN2]
  have hnpv3 : s3.get npName = nP := by rw [k2.2, hnpv2]
  have ha0 : valLimbs (((accNames.drop 0).take 4).map s.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (0 + 4) ++ [rtopName]).map s.get)
      = valLimbs T := by
    have e0 : valLimbs (((accNames.drop 0).take 4 ++ (accNames.drop (0 + 4) ++ [rtopName])).map s.get)
        = valLimbs (((accNames.drop 0).take 4).map s.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (0 + 4) ++ [rtopName]).map s.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 0).take 4).length = 4 from by decide]
    rw [← e0, show (accNames.drop 0).take 4 ++ (accNames.drop (0 + 4) ++ [rtopName])
        = accNames ++ [rtopName] from by decide,
      List.map_append, valLimbs_append, hall]
    have hr : (s.get rtopName).toNat = 0 := by rw [hrtop]; rfl
    simp [valLimbs]
    exact hr
  have hc0 := stepAt_advance_wide s 0 p nP ((accNames.drop 0).take 4)
    (accNames.drop (0 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN hnpv
    (by rw [ha0]; exact hm1)
  rw [← hs1] at hc0
  have ha1 : valLimbs (((accNames.drop 1).take 4).map s1.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T) := by
    have e1 : valLimbs (((accNames.drop 1).take 4 ++ (accNames.drop (1 + 4) ++ [rtopName])).map s1.get)
        = valLimbs (((accNames.drop 1).take 4).map s1.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 1).take 4).length = 4 from by decide]
    rw [← e1,
      show (accNames.drop 1).take 4 ++ (accNames.drop (1 + 4) ++ [rtopName])
        = ((accNames.drop 0).take 4).drop 1 ++ (accNames.drop (0 + 4) ++ [rtopName]) from by decide,
      hc0, ha0]
  have hc1 := stepAt_advance_wide s1 1 p nP ((accNames.drop 1).take 4)
    (accNames.drop (1 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN1 hnpv1
    (by rw [ha1]; exact hm2)
  rw [← hs2] at hc1
  have ha2 : valLimbs (((accNames.drop 2).take 4).map s2.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T)) := by
    have e2 : valLimbs (((accNames.drop 2).take 4 ++ (accNames.drop (2 + 4) ++ [rtopName])).map s2.get)
        = valLimbs (((accNames.drop 2).take 4).map s2.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 2).take 4).length = 4 from by decide]
    rw [← e2,
      show (accNames.drop 2).take 4 ++ (accNames.drop (2 + 4) ++ [rtopName])
        = ((accNames.drop 1).take 4).drop 1 ++ (accNames.drop (1 + 4) ++ [rtopName]) from by decide,
      hc1, ha1]
  have hc2 := stepAt_advance_wide s2 2 p nP ((accNames.drop 2).take 4)
    (accNames.drop (2 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN2 hnpv2
    (by rw [ha2]; exact hm3)
  rw [← hs3] at hc2
  have ha3 : valLimbs (((accNames.drop 3).take 4).map s3.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (3 + 4) ++ [rtopName]).map s3.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
            (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T))) := by
    have e3 : valLimbs (((accNames.drop 3).take 4 ++ (accNames.drop (3 + 4) ++ [rtopName])).map s3.get)
        = valLimbs (((accNames.drop 3).take 4).map s3.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (3 + 4) ++ [rtopName]).map s3.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 3).take 4).length = 4 from by decide]
    rw [← e3,
      show (accNames.drop 3).take 4 ++ (accNames.drop (3 + 4) ++ [rtopName])
        = ((accNames.drop 2).take 4).drop 1 ++ (accNames.drop (2 + 4) ++ [rtopName]) from by decide,
      hc2, ha2]
  have hc3 := stepAt_advance_wide s3 3 p nP ((accNames.drop 3).take 4)
    (accNames.drop (3 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN3 hnpv3
    (by rw [ha3]; exact hm4)
  rw [← hs4] at hc3
  have hpost : runBlock s emitMontRedc4Block = s4 := by
    rw [emitMontRedc4Block, runBlock_append, runBlock_append, runBlock_append,
        ← hs1, ← hs2, ← hs3, ← hs4]
  rw [hpost]
  have hfin : valLimbs ((accNames.drop 4).map s4.get) + (2 ^ 64) ^ 4 * (s4.get rtopName).toNat
      = valLimbs ((accNames.drop 4 ++ [rtopName]).map s4.get) := by
    rw [List.map_append, valLimbs_append, List.length_map,
        show (accNames.drop 4).length = 4 from by decide]
    simp
  rw [hfin,
    show accNames.drop 4 ++ [rtopName]
      = ((accNames.drop 3).take 4).drop 1 ++ (accNames.drop (3 + 4) ++ [rtopName]) from by decide,
    hc3, ha3]
  simp only [montRedc4]

end CatCrypt.Crypto.SecureCompilation.Ascent
