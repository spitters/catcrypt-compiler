/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.FieldReduce
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA

/-!
# The fused 4-limb Montgomery reduce over `runBlock` at the full product range

`Ascent.montRedc4RunBlock_proven` fuses the four `emitMontRedcStepAt` word-steps
over one `runBlock` trace, but only for an input `T` loaded into the low four
accumulator registers with the upper window cleared and the narrow bound
`⟦T⟧ < 2^64·⟦p⟧`. A general `256×256` product occupies all eight accumulator
registers `accNames = ["t0".."t7"]` and satisfies only the full-radix bound
`⟦T⟧ < 2^256·⟦p⟧ = R·⟦p⟧`; the narrow proof's per-step invariant (`each partial
< 2·⟦p⟧`) does not hold for it.

This module fuses the four word-steps at the full product range. The register
routing is `Ascent.montRedcStep_fold_running_value` (bound-free); the per-step
carry is zeroed from a window-fit bound (`montRedcStep_chain_full`), which holds
because the intermediate reductions shrink one word per step (the bounds
`Ascent`/`RelationalFrontCiosFieldMul.montRedc4_full` propagates). Chained four
times, `runBlock emitMontRedc4Block` on the full product lands
`montRedc4 ⟦p⟧ n' ⟦T⟧` in the top window `accNames[4..7]` and `rtop`, and by
`montRedc4_full` that value is `< 2·⟦p⟧` and `· 2^256 ≡ ⟦T⟧ (mod ⟦p⟧)`.

## Main results

* `montRedcStep_chain_full` — one fused word-step's carry is zero from a
  window-fit bound (no narrow `< 2^64·⟦p⟧` hypothesis).
* `stepFull_advance` — one fused word-step advances the running value by one
  `montgomeryReduce` step under a window-fit output bound.
* `montRedc4RunBlockFull` — the fused four-word reduce of a full eight-register
  product lands `montRedc4 ⟦p⟧ n' ⟦T⟧` in the top window.
* `montRedc4RunBlockFull_spec` — the same value is `< 2·⟦p⟧` and
  `· 2^256 ≡ ⟦T⟧ (mod ⟦p⟧)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockFused

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.Number

/-! ## 1. Window-fit carry zeroing (full range) -/

/-- **Full-range carry zeroing.** A fused reduce word-step reconstructs the new
    window `accs.drop 1 ++ D` plus a top carry bit to `montgomeryReduce ⟦p⟧ 2^64
    n' W` (`hfold`, from `Ascent.montRedcStep_fold_running_value`). If that
    reduced value fits the window (`< (2^64)^(|accs|−1+|D|)`), the carry is zero
    and the window reconstructs to the reduced value exactly. Unlike
    `Ascent.montRedcStep_chain`, no `W < 2^64·⟦p⟧` hypothesis is used — the fit
    bound is supplied directly, so it applies at the full product range. -/
theorem montRedcStep_chain_full (accs D : List String) (post : JState 64)
    (p : List (BitVec 64)) (nP : BitVec 64) (W : Nat)
    (hfold : valLimbs ((accs.drop 1 ++ D).map post.get)
          + (2 ^ 64) ^ (accs.length - 1 + D.length) * (if post.flagB (·.cf) then 1 else 0)
        = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W)
    (hOut : Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W
        < (2 ^ 64) ^ (accs.length - 1 + D.length)) :
    valLimbs ((accs.drop 1 ++ D).map post.get)
        = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat W := by
  have ha : valLimbs ((accs.drop 1 ++ D).map post.get)
      < (2 ^ 64) ^ (accs.length - 1 + D.length) := by
    have h := valLimbs_lt_pow ((accs.drop 1 ++ D).map post.get)
    rwa [List.length_map, List.length_append, List.length_drop] at h
  set c := (if post.flagB (·.cf) then (1 : Nat) else 0) with hc
  have hc01 : c = 0 ∨ c = 1 := by rw [hc]; split <;> simp
  rcases hc01 with h | h <;> rw [h] at hfold <;> omega

/-! ## 2. One fused word-step at the full range -/

/-- **One fused word-step advances the running value by one `montgomeryReduce`
    step (full range).** At window offset `i` (`i ≤ 3`), with the modulus in
    `pNames` and `n'` in `npName`, running `emitMontRedcStepAt i` reconstructs the
    new running window `win.drop 1 ++ D` to `montgomeryReduce ⟦p⟧ 2^64 n'
    (⟦win⟧ + 2^256·⟦D⟧)`, given only that the reduced value fits the window. The
    routing is `Ascent.montRedcStep_fold_running_value`; the carry is zeroed by
    `montRedcStep_chain_full`. -/
theorem stepFull_advance (s : JState 64) (i : Nat) (p : List (BitVec 64)) (nP : BitVec 64)
    (win D : List String)
    (hwin : win = (accNames.drop i).take 4) (hD : D = accNames.drop (i + 4) ++ [rtopName])
    (hp4 : p.length = 4) (hi3 : i ≤ 3)
    (hpN : pNames.map s.get = p) (hnpv : s.get npName = nP)
    (hOut : Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
              (valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get))
            < (2 ^ 64) ^ (win.drop 1 ++ D).length) :
    valLimbs ((win.drop 1 ++ D).map (runBlock s (emitMontRedcStepAt i)).get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (win.map s.get) + (2 ^ 64) ^ 4 * valLimbs (D.map s.get)) := by
  subst hwin hD
  rw [emitMontRedcStepAt_fused i hi3]
  interval_cases i <;>
  · refine montRedcStep_chain_full _ _ _ p nP _ ?_ ?_
    · exact montRedcStep_fold_running_value s mName _ npName
        dcyName hiName loName _ pNames rcyName hiName loName _ p _ _ nP
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide)
        (by decide) hp4 (by decide) (by simp)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
        (by rfl) hnpv hpN rfl
        (by simp) (by decide) (by simp) (by decide) (by decide) (by decide) rfl
    · simpa using hOut

/-! ## 3. The shrinking window-fit bounds -/

/-- **One reduce step shrinks the value by one word.** If `W < (2^64)^(a+1)·N +
    N`, then one `montgomeryReduce` word-step at radix `2^64` satisfies
    `montgomeryReduce N (2^64) n' W < (2^64)^a·N + N`. The Montgomery digit bound
    `redc_step_mul_le` gives `redc·2^64 ≤ W + (2^64−1)·N`; dividing by `2^64` drops
    one word. -/
theorem redc_shrink (N nP W a : Nat) (hW : W < (2 ^ 64) ^ (a + 1) * N + N) :
    Number.montgomeryReduce N (2 ^ 64) nP W < (2 ^ 64) ^ a * N + N := by
  have hS : 0 < (2 : Nat) ^ 64 := by positivity
  have hb := CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul.redc_step_mul_le
    N (2 ^ 64) nP W hS
  have hpow : (2 ^ 64 : Nat) ^ (a + 1) = (2 ^ 64) ^ a * 2 ^ 64 := by rw [pow_succ]
  have hlt : 2 ^ 64 * Number.montgomeryReduce N (2 ^ 64) nP W
      < 2 ^ 64 * ((2 ^ 64) ^ a * N + N) := by
    have hcomm : (2 : Nat) ^ 64 * Number.montgomeryReduce N (2 ^ 64) nP W
        = Number.montgomeryReduce N (2 ^ 64) nP W * 2 ^ 64 := by ring
    have hrhs : (2 : Nat) ^ 64 * ((2 ^ 64) ^ a * N + N) = (2 ^ 64) ^ (a + 1) * N + 2 ^ 64 * N := by
      rw [hpow]; ring
    rw [hcomm, hrhs]
    have hsn : (2 ^ 64 - 1) * N + N = 2 ^ 64 * N := by rw [Nat.sub_one_mul]; omega
    omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- **A shrunk value fits its window.** If `V < (2^64)^a·N + N` and `N ≤
    (2^64)^4`, then `V < (2^64)^(a+5)` — the running window (at least `a+5` words
    wide) holds it with no top carry. -/
theorem fit_helper (V N a : Nat) (hV : V < (2 ^ 64) ^ a * N + N) (hN : N ≤ (2 ^ 64) ^ 4) :
    V < (2 ^ 64) ^ (a + 5) := by
  have h1 : (2 ^ 64) ^ a * N ≤ (2 ^ 64) ^ a * (2 ^ 64) ^ 4 := Nat.mul_le_mul_left _ hN
  have h3 : (2 ^ 64 : Nat) ^ a * (2 ^ 64) ^ 4 = (2 ^ 64) ^ (a + 4) := by rw [← pow_add]
  have h2 : N ≤ (2 ^ 64 : Nat) ^ (a + 4) :=
    le_trans hN (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4 : (2 : Nat) ^ 64 * (2 ^ 64) ^ (a + 4) = (2 ^ 64) ^ (a + 5) := by rw [← pow_succ']
  have h5 : (2 : Nat) * (2 ^ 64) ^ (a + 4) ≤ 2 ^ 64 * (2 ^ 64) ^ (a + 4) := by
    apply Nat.mul_le_mul_right; norm_num
  rw [h3] at h1
  omega

/-! ## 4. The full-product load and the fused reduce -/

/-- The window-loaded input state for the fused full-product reduce: all eight
    accumulator registers `accNames` hold the product limbs `T8` (a full
    `256×256` product), the top-carry `rtop` is cleared, the modulus limbs `p`
    are in `pNames`, and the Montgomery constant `nP` is in `npName`. -/
def MontRedc4LoadFull (s : JState 64) (p T8 : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  accNames.map s.get = T8 ∧ s.get rtopName = 0 ∧
    pNames.map s.get = p ∧ s.get npName = nP

/-- **The fused four-word reduce of a full product lands `montRedc4` in the top
    window.** From a full-product window-loaded start state (`MontRedc4LoadFull`:
    all eight accumulator registers hold the product `T8`, `rtop` cleared, the
    modulus in `pNames`, `nP` in `npName`) meeting the full-radix Montgomery side
    conditions (`p` four limbs, `T8` eight limbs, `0 < ⟦p⟧`, `⟦p⟧ ≤ 2^256`, the
    constant relation `(⟦p⟧·nP) mod 2^64 = 2^64 − 1`, and the full-radix input
    bound `⟦T8⟧ < 2^256·⟦p⟧`), running the fused reduce block `emitMontRedc4Block`
    reconstructs the top window `accNames[4..7]` together with `rtop` to
    `montRedc4 ⟦p⟧ nP ⟦T8⟧`. Each `emitMontRedcStepAt` step advances via
    `stepFull_advance`; the per-step carry is zeroed by the shrinking window-fit
    bounds (`redc_shrink`/`fit_helper`/`montRedc4_full`), which need only the
    full-radix bound (unlike `Ascent.montRedc4RunBlock_proven`'s narrow
    `⟦T⟧ < 2^64·⟦p⟧`). -/
theorem montRedc4RunBlockFull (s : JState 64) (p T8 : List (BitVec 64)) (nP : BitVec 64)
    (hp4 : p.length = 4) (hT8 : T8.length = 8)
    (hN : 0 < valLimbs p) (hNleR : valLimbs p ≤ 2 ^ 256)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hTbound : valLimbs T8 < 2 ^ 256 * valLimbs p)
    (hload : MontRedc4LoadFull s p T8 nP) :
    valLimbs ((accNames.drop 4).map (runBlock s emitMontRedc4Block).get)
      + (2 ^ 64) ^ 4 * ((runBlock s emitMontRedc4Block).get rtopName).toNat
    = montRedc4 (valLimbs p) nP.toNat (valLimbs T8) := by
  obtain ⟨hacc8, hrtop0, hpN, hnpv⟩ := hload
  have hNleR' : valLimbs p ≤ (2 ^ 64) ^ 4 := by
    rw [show (2 ^ 64 : Nat) ^ 4 = 2 ^ 256 from by norm_num]; exact hNleR
  -- the shrinking window-fit bounds
  have hV0 : valLimbs T8 < (2 ^ 64) ^ 4 * valLimbs p + valLimbs p := by
    have h := hTbound
    rw [show (2 : Nat) ^ 256 = (2 ^ 64) ^ 4 from by norm_num] at h
    omega
  have hk1 := redc_shrink (valLimbs p) nP.toNat (valLimbs T8) 3 hV0
  have hk2 := redc_shrink (valLimbs p) nP.toNat
    (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T8)) 2 hk1
  have hk3 := redc_shrink (valLimbs p) nP.toNat
    (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
      (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T8))) 1 hk2
  have hfit1 := fit_helper _ (valLimbs p) 3 hk1 hNleR'
  have hfit2 := fit_helper _ (valLimbs p) 2 hk2 hNleR'
  have hfit3 := fit_helper _ (valLimbs p) 1 hk3 hNleR'
  have hpow5 : (2 : Nat) * (2 ^ 64) ^ 4 < (2 ^ 64) ^ 5 := by
    have he : (2 ^ 64 : Nat) ^ 5 = (2 ^ 64) ^ 4 * 2 ^ 64 := by rw [pow_succ]
    have hp : (0 : Nat) < (2 ^ 64) ^ 4 := by positivity
    rw [he]; nlinarith
  have hfit4 : Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
      (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
        (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat (valLimbs T8))))
      < (2 ^ 64) ^ 5 := by
    have hmr4 := (CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul.montRedc4_full
      (valLimbs p) nP.toNat (valLimbs T8) hN hnp64 hTbound).1
    rw [montRedc4] at hmr4
    omega
  -- states
  set s1 := runBlock s (emitMontRedcStepAt 0) with hs1
  set s2 := runBlock s1 (emitMontRedcStepAt 1) with hs2
  set s3 := runBlock s2 (emitMontRedcStepAt 2) with hs3
  set s4 := runBlock s3 (emitMontRedcStepAt 3) with hs4
  -- thread pNames/npName
  have k0 := stepAt_keeps s 0 (by norm_num); rw [← hs1] at k0
  have k1 := stepAt_keeps s1 1 (by norm_num); rw [← hs2] at k1
  have k2 := stepAt_keeps s2 2 (by norm_num); rw [← hs3] at k2
  have hpN1 : pNames.map s1.get = p := by rw [k0.1, hpN]
  have hnpv1 : s1.get npName = nP := by rw [k0.2, hnpv]
  have hpN2 : pNames.map s2.get = p := by rw [k1.1, hpN1]
  have hnpv2 : s2.get npName = nP := by rw [k1.2, hnpv1]
  have hpN3 : pNames.map s3.get = p := by rw [k2.1, hpN2]
  have hnpv3 : s3.get npName = nP := by rw [k2.2, hnpv2]
  -- initial value = valLimbs T8
  have ha0 : valLimbs (((accNames.drop 0).take 4).map s.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (0 + 4) ++ [rtopName]).map s.get)
      = valLimbs T8 := by
    rw [show (accNames.drop 0).take 4 = accNames.take 4 from by decide,
        show (accNames.drop (0 + 4) ++ [rtopName]) = accNames.drop 4 ++ [rtopName] from rfl]
    have hlow : (accNames.take 4).map s.get = T8.take 4 := by rw [List.map_take, hacc8]
    have hhigh : (accNames.drop 4 ++ [rtopName]).map s.get = T8.drop 4 ++ [(0 : BitVec 64)] := by
      rw [List.map_append, List.map_drop, hacc8]
      simp only [List.map_cons, List.map_nil, hrtop0]
    rw [hlow, hhigh]
    have hd0 : valLimbs (T8.drop 4 ++ [(0 : BitVec 64)]) = valLimbs (T8.drop 4) := by
      rw [valLimbs_append]; simp [valLimbs_cons, valLimbs_nil]
    rw [hd0]
    have htk : (T8.take 4).length = 4 := by simp [List.length_take, hT8]
    have happ := valLimbs_append (T8.take 4) (T8.drop 4)
    rw [htk] at happ
    rw [← happ, List.take_append_drop]
  -- step 0
  have hc0 := stepFull_advance s 0 p nP ((accNames.drop 0).take 4)
    (accNames.drop (0 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN hnpv
    (by rw [ha0]; exact hfit1)
  rw [← hs1] at hc0
  have ha1 : valLimbs (((accNames.drop 1).take 4).map s1.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (((accNames.drop 0).take 4).map s.get)
            + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (0 + 4) ++ [rtopName]).map s.get)) := by
    have e1 : valLimbs (((accNames.drop 1).take 4 ++ (accNames.drop (1 + 4) ++ [rtopName])).map s1.get)
        = valLimbs (((accNames.drop 1).take 4).map s1.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 1).take 4).length = 4 from by decide]
    rw [← e1,
      show (accNames.drop 1).take 4 ++ (accNames.drop (1 + 4) ++ [rtopName])
        = ((accNames.drop 0).take 4).drop 1 ++ (accNames.drop (0 + 4) ++ [rtopName]) from by decide,
      hc0]
  have hc1 := stepFull_advance s1 1 p nP ((accNames.drop 1).take 4)
    (accNames.drop (1 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN1 hnpv1
    (by rw [ha1, ha0]; exact hfit2)
  rw [← hs2] at hc1
  have ha2 : valLimbs (((accNames.drop 2).take 4).map s2.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (((accNames.drop 1).take 4).map s1.get)
            + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (1 + 4) ++ [rtopName]).map s1.get)) := by
    have e2 : valLimbs (((accNames.drop 2).take 4 ++ (accNames.drop (2 + 4) ++ [rtopName])).map s2.get)
        = valLimbs (((accNames.drop 2).take 4).map s2.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 2).take 4).length = 4 from by decide]
    rw [← e2,
      show (accNames.drop 2).take 4 ++ (accNames.drop (2 + 4) ++ [rtopName])
        = ((accNames.drop 1).take 4).drop 1 ++ (accNames.drop (1 + 4) ++ [rtopName]) from by decide,
      hc1]
  have hc2 := stepFull_advance s2 2 p nP ((accNames.drop 2).take 4)
    (accNames.drop (2 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN2 hnpv2
    (by rw [ha2, ha1, ha0]; exact hfit3)
  rw [← hs3] at hc2
  have ha3 : valLimbs (((accNames.drop 3).take 4).map s3.get)
        + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (3 + 4) ++ [rtopName]).map s3.get)
      = Number.montgomeryReduce (valLimbs p) (2 ^ 64) nP.toNat
          (valLimbs (((accNames.drop 2).take 4).map s2.get)
            + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (2 + 4) ++ [rtopName]).map s2.get)) := by
    have e3 : valLimbs (((accNames.drop 3).take 4 ++ (accNames.drop (3 + 4) ++ [rtopName])).map s3.get)
        = valLimbs (((accNames.drop 3).take 4).map s3.get)
          + (2 ^ 64) ^ 4 * valLimbs ((accNames.drop (3 + 4) ++ [rtopName]).map s3.get) := by
      rw [List.map_append, valLimbs_append, List.length_map,
          show ((accNames.drop 3).take 4).length = 4 from by decide]
    rw [← e3,
      show (accNames.drop 3).take 4 ++ (accNames.drop (3 + 4) ++ [rtopName])
        = ((accNames.drop 2).take 4).drop 1 ++ (accNames.drop (2 + 4) ++ [rtopName]) from by decide,
      hc2]
  have hc3 := stepFull_advance s3 3 p nP ((accNames.drop 3).take 4)
    (accNames.drop (3 + 4) ++ [rtopName]) rfl rfl hp4 (by norm_num) hpN3 hnpv3
    (by rw [ha3, ha2, ha1, ha0]; exact hfit4)
  rw [← hs4] at hc3
  have hpost : runBlock s emitMontRedc4Block = s4 := by
    rw [emitMontRedc4Block, Jasmin.runBlock_append, Jasmin.runBlock_append,
        Jasmin.runBlock_append, ← hs1, ← hs2, ← hs3, ← hs4]
  rw [hpost]
  have hfin : valLimbs ((accNames.drop 4).map s4.get) + (2 ^ 64) ^ 4 * (s4.get rtopName).toNat
      = valLimbs ((accNames.drop 4 ++ [rtopName]).map s4.get) := by
    rw [List.map_append, valLimbs_append, List.length_map,
        show (accNames.drop 4).length = 4 from by decide]
    simp
  rw [hfin,
    show accNames.drop 4 ++ [rtopName]
      = ((accNames.drop 3).take 4).drop 1 ++ (accNames.drop (3 + 4) ++ [rtopName]) from by decide,
    hc3, ha3, ha2, ha1, ha0]
  simp only [montRedc4]

/-! ## 5. The full-radix reduction spec and the residue bridge -/

/-- **The fused full-product reduce, with its range and residue.** The fused
    reduce's top-window value is `montRedc4 ⟦p⟧ n' ⟦T8⟧`, which is `< 2·⟦p⟧` and
    `· 2^256 ≡ ⟦T8⟧ (mod ⟦p⟧)` (`montRedc4_full`) — one conditional subtract from
    the canonical Montgomery representative. -/
theorem montRedc4RunBlockFull_spec (s : JState 64) (p T8 : List (BitVec 64)) (nP : BitVec 64)
    (hp4 : p.length = 4) (hT8 : T8.length = 8)
    (hN : 0 < valLimbs p) (hNleR : valLimbs p ≤ 2 ^ 256)
    (hnp64 : (valLimbs p * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1)
    (hTbound : valLimbs T8 < 2 ^ 256 * valLimbs p)
    (hload : MontRedc4LoadFull s p T8 nP) :
    valLimbs ((accNames.drop 4).map (runBlock s emitMontRedc4Block).get)
        + (2 ^ 64) ^ 4 * ((runBlock s emitMontRedc4Block).get rtopName).toNat
      = montRedc4 (valLimbs p) nP.toNat (valLimbs T8)
    ∧ montRedc4 (valLimbs p) nP.toNat (valLimbs T8) < 2 * valLimbs p
    ∧ montRedc4 (valLimbs p) nP.toNat (valLimbs T8) * 2 ^ 256
        ≡ valLimbs T8 [MOD valLimbs p] := by
  refine ⟨montRedc4RunBlockFull s p T8 nP hp4 hT8 hN hNleR hnp64 hTbound hload, ?_, ?_⟩
  · exact (CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul.montRedc4_full
      (valLimbs p) nP.toNat (valLimbs T8) hN hnp64 hTbound).1
  · exact (CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul.montRedc4_full
      (valLimbs p) nP.toNat (valLimbs T8) hN hnp64 hTbound).2

/-- **The per-word four-fold reduction and the full-radix reduction coincide mod
    `N`.** For an odd modulus `N`, the per-word constant `n'`
    (`N·n' ≡ −1 (mod 2^64)`), the full-radix constant `Nprime`
    (`N·Nprime ≡ −1 (mod 2^256)`), and a full-radix input `T < 2^256·N`, the fused
    four-word reduce `montRedc4 N n' T` and the single full-radix reduce
    `montgomeryReduce N (2^256) Nprime T` are congruent mod `N`: both satisfy
    `· 2^256 ≡ T (mod N)`, and `2^256` is a unit mod `N`. -/
theorem montRedc4_montgomeryReduce_bridge (N Nprime nP T : Nat) (hN : 0 < N)
    (hNprime : (N * Nprime) % 2 ^ 256 = 2 ^ 256 - 1)
    (hpin : (N * nP) % 2 ^ 64 = 2 ^ 64 - 1) (hTprod : T < 2 ^ 256 * N) :
    montRedc4 N nP T ≡ Number.montgomeryReduce N (2 ^ 256) Nprime T [MOD N] := by
  obtain ⟨_, h4c⟩ := CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul.montRedc4_full
    N nP T hN hpin hTprod
  obtain ⟨_, hfc⟩ := Number.montgomeryReduce_correct N (2 ^ 256) Nprime T hN (by positivity)
    hNprime hTprod
  have hco : Nat.Coprime (2 ^ 256) N := by
    have hdvd : Nat.gcd (2 ^ 256) N ∣ 1 := by
      have hgN : Nat.gcd (2 ^ 256) N ∣ N := Nat.gcd_dvd_right _ _
      have hgR : Nat.gcd (2 ^ 256) N ∣ 2 ^ 256 := Nat.gcd_dvd_left _ _
      have hgNN : Nat.gcd (2 ^ 256) N ∣ N * Nprime := hgN.mul_right Nprime
      have hgQ : Nat.gcd (2 ^ 256) N ∣ 2 ^ 256 * (N * Nprime / 2 ^ 256) :=
        hgR.mul_right _
      have hgsub : Nat.gcd (2 ^ 256) N ∣ (2 ^ 256 - 1) := by
        have hd := Nat.dvd_sub hgNN hgQ
        have hkey : N * Nprime - 2 ^ 256 * (N * Nprime / 2 ^ 256) = 2 ^ 256 - 1 := by
          have hdm := Nat.div_add_mod (N * Nprime) (2 ^ 256)
          omega
        rwa [hkey] at hd
      have : Nat.gcd (2 ^ 256) N ∣ (2 ^ 256 - (2 ^ 256 - 1)) := Nat.dvd_sub hgR hgsub
      simpa using this
    exact Nat.eq_one_of_dvd_one hdvd
  have hmul : montRedc4 N nP T * 2 ^ 256
      ≡ Number.montgomeryReduce N (2 ^ 256) Nprime T * 2 ^ 256 [MOD N] :=
    h4c.trans hfc.symm
  exact Nat.ModEq.cancel_right_of_coprime (by rwa [Nat.Coprime, Nat.gcd_comm] at hco) hmul

/-! ## 6. The secp256k1 general-input field-multiply reduce

Composing the fused reduce with the proven product side
(`Curve4LimbTierA.secp256k1_emit_montmul_runBlock4`): a state whose eight
accumulator registers hold the product `⟦x⟧·⟦yv⟧` of reduced inputs, run through
the emitted reduce block, yields the Montgomery field product `x·y·R^{-1} mod p`
in the top window — `< 2·p` and `· 2^256 ≡ ⟦x⟧·⟦yv⟧ (mod p)`. -/

/-- secp256k1's per-word Montgomery constant pin at the full `valLimbs` modulus:
    `(⟦secp256k1Limbs⟧ · n') mod 2^64 = 2^64 − 1`. The per-word pin
    `secp256k1NPrime_pin` is on the low limb `secp256k1Limbs[0]`; the full
    `valLimbs` reduces to the same low residue mod `2^64`. -/
theorem secpPerWordPin :
    (valLimbs secp256k1Limbs * secp256k1NPrime) % 2 ^ 64 = 2 ^ 64 - 1 := by
  have hlt : (secp256k1Limbs.headD 0).toNat < 2 ^ 64 := (secp256k1Limbs.headD 0).isLt
  have hv : valLimbs secp256k1Limbs % 2 ^ 64 = (secp256k1Limbs.headD 0).toNat := by
    rcases hsecp : secp256k1Limbs with _ | ⟨w0, rest⟩
    · simp [valLimbs_nil]
    · rw [valLimbs_cons, List.headD_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w0.isLt]
  have hmod : valLimbs secp256k1Limbs ≡ (secp256k1Limbs.headD 0).toNat [MOD 2 ^ 64] := by
    unfold Nat.ModEq; rw [hv, Nat.mod_eq_of_lt hlt]
  have hmm := hmod.mul_right secp256k1NPrime
  unfold Nat.ModEq at hmm
  rw [hmm]; exact secp256k1NPrime_pin

/-- **The secp256k1 fused reduce is a general-input field multiply over
    `runBlock`.** For a start state whose eight accumulator registers hold the
    product `⟦T8⟧ = ⟦x⟧·⟦yv⟧` of reduced inputs (`⟦x⟧, ⟦yv⟧ < p_secp256k1`), the
    top-carry `rtop` cleared, the modulus in `pNames`, and the per-word Montgomery
    constant `n' = secp256k1NPrime` in `npName`, running the fused reduce block
    `emitMontRedc4Block` lands a top-window value that is `< 2·p_secp256k1` and
    `· 2^256 ≡ ⟦x⟧·⟦yv⟧ (mod p_secp256k1)` — the Montgomery-domain field product,
    one conditional subtract from canonical. The product value is
    `Curve4LimbTierA.secp256k1_emit_montmul_runBlock4`; the reduce trace is
    `montRedc4RunBlockFull`. -/
theorem secp256k1_fused_reduce_montmul
    (s : JState 64) (T8 x yv : List (BitVec 64)) (nP : BitVec 64)
    (hT8 : T8.length = 8)
    (hxr : valLimbs x < valLimbs secp256k1Limbs) (hyr : valLimbs yv < valLimbs secp256k1Limbs)
    (hnP : nP.toNat = secp256k1NPrime)
    (hprod : valLimbs T8 = valLimbs x * valLimbs yv)
    (hload : MontRedc4LoadFull s secp256k1Limbs T8 nP) :
    valLimbs ((accNames.drop 4).map (runBlock s emitMontRedc4Block).get)
        + (2 ^ 64) ^ 4 * ((runBlock s emitMontRedc4Block).get rtopName).toNat
      < 2 * valLimbs secp256k1Limbs
    ∧ (valLimbs ((accNames.drop 4).map (runBlock s emitMontRedc4Block).get)
        + (2 ^ 64) ^ 4 * ((runBlock s emitMontRedc4Block).get rtopName).toNat) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs secp256k1Limbs] := by
  have hN : 0 < valLimbs secp256k1Limbs := by rw [secp256k1Limbs_value]; norm_num
  have hNleR : valLimbs secp256k1Limbs ≤ 2 ^ 256 := by rw [secp256k1Limbs_value]; norm_num
  have hnp64 : (valLimbs secp256k1Limbs * nP.toNat) % 2 ^ 64 = 2 ^ 64 - 1 := by
    rw [hnP]; exact secpPerWordPin
  have hTbound : valLimbs T8 < 2 ^ 256 * valLimbs secp256k1Limbs := by
    rw [hprod]
    have hxy : valLimbs x * valLimbs yv < valLimbs secp256k1Limbs * valLimbs secp256k1Limbs :=
      Nat.mul_lt_mul_of_lt_of_le hxr (le_of_lt hyr) hN
    have hle : valLimbs secp256k1Limbs * valLimbs secp256k1Limbs
        ≤ 2 ^ 256 * valLimbs secp256k1Limbs := by
      rw [Nat.mul_comm (2 ^ 256)]; exact Nat.mul_le_mul_left _ hNleR
    omega
  obtain ⟨hV, hrange, hcong⟩ := montRedc4RunBlockFull_spec s secp256k1Limbs T8 nP
    (by decide) hT8 hN hNleR hnp64 hTbound hload
  refine ⟨?_, ?_⟩
  · rw [hV]; exact hrange
  · rw [hV, ← hprod]; exact hcong

end CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockFused
