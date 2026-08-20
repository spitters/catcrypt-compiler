/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit

/-!
# `PreinvStepAgrees`: the Möller–Granlund reciprocal step equals the exact Euclidean step

`preinvStep dinv d u1 u0` (in `MpnDivRem1FrontEmit`) is the branch-free reciprocal
division step `udiv_qrnnd_preinv` — Algorithm 4 (DIV2BY1) of Möller and Granlund,
*Improved division by invariant integers*, IEEE TC 60(2), 2011. This module discharges
`PreinvStepAgrees`: for a normalised divisor `d` (bit 63 set), a dividend high word
`u1 < d`, and the precomputed reciprocal `dinv = ⌊(2^128 - 1) / d⌋ - 2^64`, the step
returns exactly the Euclidean quotient digit and remainder of `u1 · 2^64 + u0` by `d`.

## Main results

* `recip_k_bounds`: the reciprocal defect `k = 2^128 - ⌊(2^128-1)/d⌋ · d` lies in
  `[1, d]`, i.e. `(β + v) · d = β^2 - k` with `1 ≤ k ≤ d` (Theorem 2 hypothesis).
* `rtil_window`: Theorem 2 — the signed candidate remainder
  `r̃ = (u1·2^64 + u0) - q̃·d` (with `q̃ = q1 + 1`) satisfies
  `max(β-d, q0+1) - β ≤ r̃ < max(β-d, q0)`, delivered as the three inequalities the
  correction analysis consumes.
* `div2by1_abstract`: from that window, the two branch-free corrections of Algorithm 4
  land the quotient/remainder pair on the exact Euclidean `(⌊U/d⌋, U mod d)`.
* `preinvStep_agrees` / `preinvStepAgrees_proof`: `preinvStep dinv d u1 u0 = divLimb u1 u0 d`,
  i.e. `PreinvStepAgrees`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1PreinvAgree

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu bSltu_eq)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (mulHiW)
open CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo (mulHiW_toNat mulHiW_le mulx_reconstruct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (bSltu_le_one)

/-! ## 0. Word-level helpers -/

/-- `bSltu` as a `0`/`1` natural: the unsigned comparison of the underlying values. -/
theorem bSltu_toNat (a b : BitVec 64) :
    (bSltu a b).toNat = if a.toNat < b.toNat then 1 else 0 := by
  rw [bSltu_eq]
  by_cases h : a.toNat < b.toNat
  · rw [if_pos (BitVec.ult_iff_toNat_lt.mpr h), if_pos h]; rfl
  · rw [if_neg (fun hh => h (BitVec.ult_iff_toNat_lt.mp hh)), if_neg h]; rfl

/-- Reducing one factor mod `2^64` before multiplying leaves the product's residue fixed. -/
theorem mod_mul_mod (a b : Nat) : (a % 2 ^ 64 * b) % 2 ^ 64 = a * b % 2 ^ 64 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-! ## 1. The reciprocal defect bound -/

/-- For a normalised `dn` the reciprocal `Vn = ⌊(2^128-1)/dn⌋` satisfies
    `Vn · dn = 2^128 - k` with `1 ≤ k ≤ dn`, and `Vn ≥ 2^64` (so `Vn = 2^64 + v` for the
    single-word reciprocal `v`). This is the `(β+v)d = β^2 - k, 1 ≤ k ≤ d` of Theorem 2. -/
theorem recip_k_bounds (dn : Nat) (hd2 : 2 ^ 63 ≤ dn) (hdB : dn < 2 ^ 64) :
    ∃ k, 1 ≤ k ∧ k ≤ dn ∧
      ((2 ^ 128 - 1) / dn) * dn + k = 2 ^ 128 ∧ 2 ^ 64 ≤ (2 ^ 128 - 1) / dn := by
  have hdpos : 0 < dn := by omega
  have hpow : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by
    rw [← pow_add]
  set Vn := (2 ^ 128 - 1) / dn with hVn
  have hdm : dn * Vn + (2 ^ 128 - 1) % dn = 2 ^ 128 - 1 := Nat.div_add_mod (2 ^ 128 - 1) dn
  have hml : (2 ^ 128 - 1) % dn < dn := Nat.mod_lt _ hdpos
  -- Vn ≥ 2^64.
  have hVge : 2 ^ 64 ≤ Vn := by
    rw [hVn, Nat.le_div_iff_mul_le hdpos]
    have : 2 ^ 64 * dn ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have he : 2 ^ 64 * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 64 := by
      rw [Nat.mul_sub, hpow]; ring_nf
    omega
  refine ⟨2 ^ 128 - Vn * dn, ?_, ?_, ?_, hVge⟩
  · -- 1 ≤ k
    have : Vn * dn ≤ 2 ^ 128 - 1 := by rw [Nat.mul_comm]; omega
    omega
  · -- k ≤ dn
    have : Vn * dn = dn * Vn := Nat.mul_comm _ _
    omega
  · -- Vn * dn + k = 2^128
    have : Vn * dn ≤ 2 ^ 128 := by rw [Nat.mul_comm]; omega
    omega

/-! ## 2. Theorem 2: the candidate-remainder window -/

/-- The purely algebraic core of Theorem 2's bound, over abstract `Int` variables (so
    the concrete `2^64`/`2^128` literals never reach `nlinarith`). From the central
    identity `b·r̃ = k·u1 + u0·(b-d) + q0·d - b·d` with `1 ≤ k ≤ d`, `u1 < d`, `u0,q0 < b`,
    the candidate remainder obeys `-d ≤ r̃`, `q0 < r̃ + b`, and `r̃ < b-d ∨ r̃ < q0`. -/
theorem window_of_key
    (b dn u1n u0n q0 k rtil : Int)
    (hbpos : 0 < b) (hk1 : 1 ≤ k) (hkd : k ≤ dn)
    (hu1 : u1n < dn) (hu1nn : 0 ≤ u1n) (hu0nn : 0 ≤ u0n) (hu0 : u0n < b)
    (hq0nn : 0 ≤ q0) (hq0 : q0 < b) (_hdpos : 0 < dn) (hdb : dn < b)
    (key : b * rtil = k * u1n + u0n * (b - dn) + q0 * dn - b * dn) :
    -dn ≤ rtil ∧ q0 < rtil + b ∧ (rtil < b - dn ∨ rtil < q0) := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:Int) ≤ k) hu1nn,
      mul_nonneg hu0nn (by linarith : (0:Int) ≤ b - dn),
      mul_nonneg hq0nn (by linarith : (0:Int) ≤ dn)]
  · nlinarith [mul_nonneg (by linarith : (0:Int) ≤ k) hu1nn,
      mul_nonneg hu0nn (by linarith : (0:Int) ≤ b - dn),
      mul_lt_mul_of_neg_left (show dn < b by linarith) (show q0 - b < 0 by linarith)]
  · have hku : k * u1n ≤ dn * dn :=
      mul_le_mul hkd (le_of_lt hu1) hu1nn (by linarith : (0:Int) ≤ dn)
    have hu0m : u0n * (b - dn) ≤ (b - 1) * (b - dn) :=
      mul_le_mul_of_nonneg_right (by linarith : u0n ≤ b - 1) (by linarith : (0:Int) ≤ b - dn)
    have hub : b * rtil < (b - dn) * (b - dn) + q0 * dn := by nlinarith [hku, hu0m, key]
    rcases le_total (b - dn) q0 with hmax | hmax
    · right
      have hmul : (b - dn) * (b - dn) ≤ q0 * (b - dn) :=
        mul_le_mul_of_nonneg_right hmax (by linarith : (0:Int) ≤ b - dn)
      have h1 : b * rtil < b * q0 := by nlinarith [hub, hmul]
      exact lt_of_mul_lt_mul_left h1 (le_of_lt hbpos)
    · left
      have hmul : q0 * dn ≤ (b - dn) * dn :=
        mul_le_mul_of_nonneg_right hmax (by linarith : (0:Int) ≤ dn)
      have h1 : b * rtil < b * (b - dn) := by nlinarith [hub, hmul]
      exact lt_of_mul_lt_mul_left h1 (le_of_lt hbpos)

/-- **Möller–Granlund Theorem 2.** With `β = 2^64`, `β/2 ≤ dn < β`, `u1n < dn`,
    `u0n < β`, reciprocal `vn = ⌊(β^2-1)/dn⌋ - β`, and `⟨q1, q0⟩ = (β+vn)·u1n + u0n`
    (so `β·H + q0 = vn·u1n + u0n` with `q0 < β`), the signed candidate remainder
    `r̃ = (u1n·β + u0n) - q̃·dn` for `q̃ = u1n + H + 1` obeys
    `max(β-dn, q0+1) - β ≤ r̃ < max(β-dn, q0)`. The three consequences returned are the
    ones the correction analysis uses: `r̃ ≥ -dn`, `r̃ + β > q0`, and
    `r̃ < β-dn ∨ r̃ < q0`. -/
theorem rtil_window (dn u1n u0n vn H q0 : Nat) (rtil : Int)
    (hd2 : 2 ^ 63 ≤ dn) (hdB : dn < 2 ^ 64) (hu1 : u1n < dn) (hu0 : u0n < 2 ^ 64)
    (hv : vn = (2 ^ 128 - 1) / dn - 2 ^ 64)
    (hH : 2 ^ 64 * H + q0 = vn * u1n + u0n) (hq0 : q0 < 2 ^ 64)
    (hrt : rtil = ((u1n : Int) * 2 ^ 64 + u0n) - ((u1n + H + 1 : Nat) : Int) * dn) :
    -(dn : Int) ≤ rtil ∧ (q0 : Int) < rtil + 2 ^ 64 ∧
      (rtil < 2 ^ 64 - dn ∨ rtil < q0) := by
  obtain ⟨k, hk1, hkd, hVk, hVge⟩ := recip_k_bounds dn hd2 hdB
  -- vn·dn = 2^128 - k - 2^64·dn, as a Nat identity, then cast.
  have hvn : vn + 2 ^ 64 = (2 ^ 128 - 1) / dn := by omega
  have hvdn_nat : vn * dn + k + 2 ^ 64 * dn = 2 ^ 128 := by
    have : (vn + 2 ^ 64) * dn = ((2 ^ 128 - 1) / dn) * dn := by rw [hvn]
    have hexp : (vn + 2 ^ 64) * dn = vn * dn + 2 ^ 64 * dn := by ring
    omega
  -- The central identity: 2^64 · r̃ = k·u1 + u0·(β-dn) + q0·dn - β·dn  (in ℤ).
  have hHc : (2 ^ 64 : Int) * H = vn * u1n + u0n - q0 := by
    have := hH; push_cast; omega
  have hvdc : (vn : Int) * dn = 2 ^ 128 - k - 2 ^ 64 * dn := by
    have := hvdn_nat; push_cast; omega
  have key : (2 ^ 64 : Int) * rtil
      = k * u1n + u0n * (2 ^ 64 - dn) + q0 * dn - 2 ^ 64 * dn := by
    rw [hrt]
    push_cast
    linear_combination (-(dn : Int)) * hHc + (-(u1n : Int)) * hvdc
  -- Bounds on the ingredients, cast to ℤ.
  have hk1' : (1 : Int) ≤ k := by exact_mod_cast hk1
  have hkd' : (k : Int) ≤ dn := by exact_mod_cast hkd
  have hu1' : (u1n : Int) < dn := by exact_mod_cast hu1
  have hu0' : (u0n : Int) < 2 ^ 64 := by exact_mod_cast hu0
  have hq0' : (q0 : Int) < 2 ^ 64 := by exact_mod_cast hq0
  have hd2' : (2 ^ 63 : Int) ≤ dn := by exact_mod_cast hd2
  have hdB' : (dn : Int) < 2 ^ 64 := by exact_mod_cast hdB
  have hu1nn : (0 : Int) ≤ u1n := Int.natCast_nonneg _
  have hu0nn : (0 : Int) ≤ u0n := Int.natCast_nonneg _
  have hq0nn : (0 : Int) ≤ q0 := Int.natCast_nonneg _
  have hdpos' : (0 : Int) < dn := by exact_mod_cast (by omega : 0 < dn)
  exact window_of_key (2 ^ 64) dn u1n u0n q0 k rtil (by norm_num) hk1' hkd'
    hu1' hu1nn hu0nn hu0' hq0nn hq0' hdpos' hdB' key

/-! ## 3. Uniqueness of Euclidean division -/

/-- A nonnegative quotient/remainder pair with `fr < dn` and `Un = fq·dn + fr` is the
    Euclidean division of `Un` by `dn`. -/
theorem euclid_unique (Un dn : Nat) (fq fr : Int) (hdpos : 0 < dn)
    (hqge : 0 ≤ fq) (hrge : 0 ≤ fr) (hrlt : fr < dn)
    (hval : (Un : Int) = fq * dn + fr) :
    fq = ((Un / dn : Nat) : Int) ∧ fr = ((Un % dn : Nat) : Int) := by
  lift fq to Nat using hqge with fqn
  lift fr to Nat using hrge with frn
  have hrlt' : frn < dn := by exact_mod_cast hrlt
  have hval' : Un = dn * fqn + frn := by
    have h : (Un : Int) = ((dn * fqn + frn : Nat) : Int) := by push_cast; linear_combination hval
    exact_mod_cast h
  obtain ⟨h1, h2⟩ :=
    (Nat.div_mod_unique (a := Un) (b := dn) (d := fqn) (c := frn) hdpos).mpr ⟨by omega, hrlt'⟩
  exact ⟨by rw [h1], by rw [h2]⟩

/-! ## 4. Correctness of the two branch-free corrections -/

/-- **The Möller–Granlund corrections land the exact Euclidean pair.** Given the window of
    `rtil_window` on the signed candidate remainder `rtil = U - q̃·dn`, the line-4 remainder
    `rword` (the residue of `rtil` mod `β`), the branch-free `c1`/`c3` corrections, and the
    corrected `finalq`/`finalr`, one has `finalq = ⌊U/dn⌋` and `finalr = U mod dn`. -/
theorem div2by1_abstract
    (dn u1n u0n q0 qtil : Nat) (rtil rword c1 rmid c3 finalr finalq : Int)
    (hdpos : 0 < dn) (hd2 : 2 ^ 63 ≤ dn) (hqtil : 1 ≤ qtil) (hq0 : q0 < 2 ^ 64)
    (hrt : rtil = ((u1n * 2 ^ 64 + u0n : Nat) : Int) - (qtil : Int) * dn)
    (hlo1 : -(dn : Int) ≤ rtil) (hlo2 : (q0 : Int) < rtil + 2 ^ 64)
    (hup : rtil < 2 ^ 64 - dn ∨ rtil < q0)
    (hrword : rword = if rtil < 0 then rtil + 2 ^ 64 else rtil)
    (hc1 : c1 = if (q0 : Int) < rword then 1 else 0)
    (hrmid : rmid = if (q0 : Int) < rword then rtil + dn else rword)
    (hc3 : c3 = if (dn : Int) ≤ rmid then 1 else 0)
    (hfinalr : finalr = if (dn : Int) ≤ rmid then rmid - dn else rmid)
    (hfinalq : finalq = (qtil : Int) - c1 + c3) :
    finalq = ((u1n * 2 ^ 64 + u0n) / dn : Nat)
      ∧ finalr = ((u1n * 2 ^ 64 + u0n) % dn : Nat) := by
  have hqtil' : (1 : Int) ≤ qtil := by exact_mod_cast hqtil
  have hd2' : (2 ^ 63 : Int) ≤ dn := by exact_mod_cast hd2
  have hq0' : (q0 : Int) < 2 ^ 64 := by exact_mod_cast hq0
  have hpow : (2 : Int) ^ 64 = 2 * 2 ^ 63 := by norm_num
  subst hrword hc1 hrmid hc3 hfinalr hfinalq
  rcases lt_or_ge rtil 0 with hA | hA
  · -- Case B: rtil < 0 (over-estimate q̃ = q + 1).
    simp only [if_pos hA, if_pos hlo2]
    have hCf : ¬ ((dn : Int) ≤ rtil + dn) := by linarith
    simp only [if_neg hCf]
    refine euclid_unique _ _ _ _ hdpos ?_ ?_ ?_ ?_
    · linarith
    · linarith
    · linarith
    · linear_combination -hrt
  · -- Case A: 0 ≤ rtil (candidate not over the true quotient).
    have hAf : ¬ (rtil < 0) := not_lt.2 hA
    rcases lt_or_ge (q0 : Int) rtil with hB | hB
    · -- A1: q0 < rtil, so c1 fires; the window forces rtil < β - dn.
      have hrlt_bd : rtil < 2 ^ 64 - dn := by
        rcases hup with h | h
        · exact h
        · linarith
      simp only [if_neg hAf, if_pos hB]
      have hCt : (dn : Int) ≤ rtil + dn := by linarith
      simp only [if_pos hCt]
      refine euclid_unique _ _ _ _ hdpos ?_ ?_ ?_ ?_
      · linarith
      · linarith
      · linarith
      · linear_combination -hrt
    · -- A2: rtil ≤ q0, c1 does not fire.
      have hBf : ¬ ((q0 : Int) < rtil) := not_lt.2 hB
      rcases lt_or_ge rtil (dn : Int) with hC | hC
      · -- A2a: rtil < dn, c3 does not fire; q̃ = q.
        simp only [if_neg hAf, if_neg hBf]
        have hCf : ¬ ((dn : Int) ≤ rtil) := not_le.2 hC
        simp only [if_neg hCf]
        refine euclid_unique _ _ _ _ hdpos ?_ ?_ ?_ ?_
        · linarith
        · linarith
        · linarith
        · linear_combination -hrt
      · -- A2b: dn ≤ rtil, c3 fires; q̃ = q - 1, corrected up.
        have hrq : rtil < q0 := by
          rcases hup with h | h
          · exfalso; linarith
          · exact h
        simp only [if_neg hAf, if_neg hBf, if_pos hC]
        refine euclid_unique _ _ _ _ hdpos ?_ ?_ ?_ ?_
        · linarith
        · linarith
        · linarith
        · linear_combination -hrt

/-! ## 5. The word-level bridge -/

set_option maxHeartbeats 1000000 in
/-- **`PreinvStepAgrees`.** The Möller–Granlund reciprocal step equals the exact Euclidean
    step under the preconditions: `d` normalised, `u1 < d`, `dinv` the reciprocal. -/
theorem preinvStep_agrees (dinv d u1 u0 : BitVec 64)
    (hd2 : 2 ^ 63 ≤ d.toNat) (hu1lt : u1.toNat < d.toNat)
    (hv : dinv.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    preinvStep dinv d u1 u0 = divLimb u1 u0 d := by
  -- Name the words exactly as `preinvStep` binds them.
  set qh := mulHiW dinv u1 with hqh
  set ql := dinv * u1 with hql
  set qla := ql + u0 with hqla
  set c0 := bSltu qla ql with hc0
  set qhb := qh + (u1 + 1) + c0 with hqhb
  set rr := u0 - qhb * d with hrr
  set c1 := bSltu qla rr with hc1
  set m1 := (~~~c1) + 1 with hm1
  set qhbb := qhb + m1 with hqhbb
  set rp := rr + (m1 &&& d) with hrp
  set c2 := bSltu rp d with hc2
  set c3w := c2 ^^^ 1 with hc3w
  set m3 := (~~~c3w) + 1 with hm3
  have hstep : preinvStep dinv d u1 u0 = (qhbb + c3w, rp - (m3 &&& d)) := rfl
  -- Basic range facts.
  have hdpos : 0 < d.toNat := by omega
  have hdB : d.toNat < 2 ^ 64 := d.isLt
  have hu0B : u0.toNat < 2 ^ 64 := u0.isLt
  have hqlaB : qla.toNat < 2 ^ 64 := qla.isLt
  have hqlB : ql.toNat < 2 ^ 64 := ql.isLt
  -- The reciprocal-step value facts.
  have hmulx : ql.toNat + qh.toNat * 2 ^ 64 = dinv.toNat * u1.toNat := mulx_reconstruct dinv u1
  have hqla_n : qla.toNat = (ql.toNat + u0.toNat) % 2 ^ 64 := by rw [hqla, BitVec.toNat_add]
  have hc0_n : c0.toNat = if qla.toNat < ql.toNat then 1 else 0 := by rw [hc0, bSltu_toNat]
  have hc0div : c0.toNat = (ql.toNat + u0.toNat) / 2 ^ 64 := by
    rw [hc0_n, hqla_n]
    rcases Nat.lt_or_ge (ql.toNat + u0.toNat) (2 ^ 64) with h | h
    · rw [if_neg (by omega), Nat.div_eq_of_lt h]
    · rw [if_pos (by omega), show (ql.toNat + u0.toNat) / 2 ^ 64 = 1 from by omega]
  have hcarry : ql.toNat + u0.toNat = qla.toNat + c0.toNat * 2 ^ 64 := by
    rw [hqla_n, hc0div]; clear hv; omega
  -- `2^64·H + q0 = vn·u1 + u0` (the `rtil_window` hypothesis).
  have hH : 2 ^ 64 * (qh.toNat + c0.toNat) + qla.toNat = dinv.toNat * u1.toNat + u0.toNat := by
    have hrw : 2 ^ 64 * (qh.toNat + c0.toNat) + qla.toNat
        = qh.toNat * 2 ^ 64 + (qla.toNat + c0.toNat * 2 ^ 64) := by ring
    rw [hrw, ← hcarry]; omega
  set qtil : Nat := u1.toNat + (qh.toNat + c0.toNat) + 1 with hqtil_def
  set rtil : Int := ((u1.toNat * 2 ^ 64 + u0.toNat : Nat) : Int) - (qtil : Int) * d.toNat
    with hrtil_def
  obtain ⟨hlo1, hlo2, hup⟩ := rtil_window d.toNat u1.toNat u0.toNat dinv.toNat
    (qh.toNat + c0.toNat) qla.toNat rtil hd2 hdB hu1lt hu0B hv hH hqlaB
    (by rw [hrtil_def, hqtil_def]; push_cast; ring)
  -- `rtil` upper bound (needed below).
  have hq0B : (qla.toNat : Int) < 2 ^ 64 := by exact_mod_cast hqlaB
  have hdI : (0 : Int) < d.toNat := by exact_mod_cast hdpos
  have hrtil_ub : rtil < 2 ^ 64 := by rcases hup with h | h <;> linarith [hq0B]
  -- The abstract algorithm's Int quantities.
  set rword : Int := if rtil < 0 then rtil + 2 ^ 64 else rtil with hrword_def
  set c1v : Int := if (qla.toNat : Int) < rword then 1 else 0 with hc1v_def
  set rmid : Int := if (qla.toNat : Int) < rword then rtil + d.toNat else rword with hrmid_def
  set c3v : Int := if (d.toNat : Int) ≤ rmid then 1 else 0 with hc3v_def
  set finalr : Int := if (d.toNat : Int) ≤ rmid then rmid - d.toNat else rmid with hfinalr_def
  set finalq : Int := (qtil : Int) - c1v + c3v with hfinalq_def
  have hqtil1 : 1 ≤ qtil := by rw [hqtil_def]; omega
  obtain ⟨hfq, hfr⟩ := div2by1_abstract d.toNat u1.toNat u0.toNat qla.toNat qtil rtil
    rword c1v rmid c3v finalr finalq hdpos hd2 hqtil1 hqlaB hrtil_def hlo1 hlo2 hup
    hrword_def hc1v_def hrmid_def hc3v_def hfinalr_def hfinalq_def
  -- Word ↔ Int connections.
  have hqhb_n : qhb.toNat = qtil % 2 ^ 64 := by
    have h1 : (u1 + 1).toNat = u1.toNat + 1 := by
      rw [BitVec.toNat_add]; have ho : (1 : BitVec 64).toNat = 1 := rfl; omega
    rw [hqhb, BitVec.toNat_add, BitVec.toNat_add, h1, hqtil_def]; omega
  have hm_eq : (qhb.toNat * d.toNat) % 2 ^ 64 = (qtil * d.toNat) % 2 ^ 64 := by
    rw [hqhb_n]; exact mod_mul_mod qtil d.toNat
  have hrtil_P : rtil = ((u1.toNat * 2 ^ 64 + u0.toNat : Nat) : Int) - ((qtil * d.toNat : Nat) : Int) := by
    rw [hrtil_def]; push_cast; ring
  -- Line-4 remainder word equals `rword`.
  have hrr_n : rr.toNat = (2 ^ 64 - (qhb * d).toNat + u0.toNat) % 2 ^ 64 := by
    rw [hrr, BitVec.toNat_sub]
  have hrr_val : (rr.toNat : Int) = rword := by
    have hrrB : rr.toNat < 2 ^ 64 := rr.isLt
    have hrr_n2 : rr.toNat = (2 ^ 64 - (qtil * d.toNat) % 2 ^ 64 + u0.toNat) % 2 ^ 64 := by
      rw [hrr_n, BitVec.toNat_mul, hm_eq]
    have hmp : (qtil * d.toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
    rw [hrword_def]
    rcases lt_or_ge rtil 0 with h | h
    · rw [if_pos h]; clear hv; omega
    · rw [if_neg (not_lt.2 h)]; clear hv; omega
  -- The `c1` comparison bit matches `c1v`.
  have hc1cond : ((qla.toNat : Int) < rword) ↔ qla.toNat < rr.toNat := by
    rw [← hrr_val]; exact Nat.cast_lt
  have hc1v_eq : (c1.toNat : Int) = c1v := by
    rw [hc1v_def, hc1, bSltu_toNat]
    by_cases h : qla.toNat < rr.toNat
    · rw [if_pos h, if_pos (hc1cond.mpr h)]; simp
    · rw [if_neg h, if_neg (fun hh => h (hc1cond.mp hh))]; simp
  -- Line-7 remainder word equals `rmid`.
  have hrp_val : (rp.toNat : Int) = rmid := by
    rw [hrmid_def]
    by_cases hcc1 : qla.toNat < rr.toNat
    · have hc1e : c1 = 1 := by
        rw [hc1, bSltu_eq, if_pos (BitVec.ult_iff_toNat_lt.mpr hcc1)]
      have hmd : m1 &&& d = d := by rw [hm1, hc1e]; bv_decide
      have hrpn : rp.toNat = (rr.toNat + d.toNat) % 2 ^ 64 := by
        rw [hrp, hmd, BitVec.toNat_add]
      rw [if_pos (hc1cond.mpr hcc1)]
      rcases lt_or_ge rtil 0 with hs | hs
      · have he : (rr.toNat : Int) = rtil + 2 ^ 64 := by rw [hrr_val, hrword_def, if_pos hs]
        clear hv; omega
      · have he : (rr.toNat : Int) = rtil := by rw [hrr_val, hrword_def, if_neg (not_lt.2 hs)]
        have hrtlt : rtil < 2 ^ 64 - d.toNat := by
          rcases hup with h | h
          · exact h
          · have hqr : (qla.toNat : Int) < rtil := by rw [← he]; exact_mod_cast hcc1
            linarith
        clear hv; omega
    · have hc1e : c1 = 0 := by
        rw [hc1, bSltu_eq, if_neg (fun hh => hcc1 (BitVec.ult_iff_toNat_lt.mp hh))]
      have hmd : m1 &&& d = 0 := by rw [hm1, hc1e]; bv_decide
      have hrpn : rp.toNat = rr.toNat := by
        rw [hrp, hmd]; simp
      rw [if_neg (fun hh => hcc1 (hc1cond.mp hh)), hrpn, hrr_val]
  -- The `c3` bit matches `c3v`.
  have hc3wn : c3w.toNat = if rp.toNat < d.toNat then 0 else 1 := by
    rw [hc3w, hc2]
    by_cases h : rp.toNat < d.toNat
    · have he : bSltu rp d = 1 := by
        rw [bSltu_eq, if_pos (BitVec.ult_iff_toNat_lt.mpr h)]
      rw [he, if_pos h]; decide
    · have he : bSltu rp d = 0 := by
        rw [bSltu_eq, if_neg (fun hh => h (BitVec.ult_iff_toNat_lt.mp hh))]
      rw [he, if_neg h]; decide
  have hc3wle : c3w.toNat ≤ 1 := by rw [hc3wn]; split <;> omega
  have hc3v_eq : (c3w.toNat : Int) = c3v := by
    rw [hc3v_def, hc3wn]
    have hcond : ((d.toNat : Int) ≤ rmid) ↔ (d.toNat ≤ rp.toNat) := by
      rw [← hrp_val]; exact Nat.cast_le
    by_cases h : rp.toNat < d.toNat
    · rw [if_pos h, if_neg (fun hh => (Nat.not_lt.mpr (hcond.mp hh)) h)]; simp
    · rw [if_neg h, if_pos (hcond.mpr (Nat.not_lt.mp h))]; simp
  -- The two output words are the Euclidean quotient and remainder.
  have hqlt : (u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat < 2 ^ 64 := divLimb_quot_lt u1 u0 d hu1lt
  have hrlt : (u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ hdpos) hdB
  have hc1le : c1.toNat ≤ 1 := bSltu_le_one qla rr
  have hfq' : (qtil : Int) - c1.toNat + c3w.toNat
      = ((u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat : Nat) := by
    rw [hc1v_eq, hc3v_eq, ← hfinalq_def]; exact hfq
  have hout1 : (qhbb + c3w).toNat = (u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat := by
    have hm1neg : m1 = -c1 := by rw [hm1]; bv_decide
    have heq1 : qhbb + c3w = qhb - c1 + c3w := by rw [hqhbb, hm1neg]; ring
    rw [heq1, BitVec.toNat_add, BitVec.toNat_sub, hqhb_n]
    clear hv; omega
  have hout2 : (rp - (m3 &&& d)).toNat = (u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat := by
    rw [hfinalr_def] at hfr
    by_cases h : rp.toNat < d.toNat
    · have hc3e : c3w = 0 := by
        rw [hc3w, hc2, bSltu_eq, if_pos (BitVec.ult_iff_toNat_lt.mpr h)]; decide
      have hmd : m3 &&& d = 0 := by rw [hm3, hc3e]; bv_decide
      have hz : rp - (m3 &&& d) = rp := by rw [hmd]; simp
      rw [hz]
      have hlt : (d.toNat : Int) ≤ rmid → False := fun hh => (Nat.not_lt.mpr (by
        have := hh; rw [← hrp_val] at this; exact_mod_cast this)) h
      rw [if_neg hlt] at hfr
      have : (rp.toNat : Int) = ((u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat : Nat) := by
        rw [hrp_val]; exact hfr
      exact_mod_cast this
    · have hc3e : c3w = 1 := by
        rw [hc3w, hc2, bSltu_eq, if_neg (fun hh => h (BitVec.ult_iff_toNat_lt.mp hh))]; decide
      have hmd : m3 &&& d = d := by rw [hm3, hc3e]; bv_decide
      have hge : (d.toNat : Int) ≤ rmid := by rw [← hrp_val]; exact_mod_cast Nat.not_lt.mp h
      rw [if_pos hge] at hfr
      rw [hmd, BitVec.toNat_sub]
      have hrpge : d.toNat ≤ rp.toNat := Nat.not_lt.mp h
      have hval : (rp.toNat : Int) - d.toNat = ((u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat : Nat) := by
        rw [← hfr, hrp_val]
      clear hv; omega
  rw [hstep, divLimb, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [hout1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
  · apply BitVec.eq_of_toNat_eq
    rw [hout2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrlt]

/-- `PreinvStepAgrees`, the residual gap of `MpnDivRem1FrontEmit`, discharged. -/
theorem preinvStepAgrees_proof : PreinvStepAgrees := preinvStep_agrees

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1PreinvAgree
