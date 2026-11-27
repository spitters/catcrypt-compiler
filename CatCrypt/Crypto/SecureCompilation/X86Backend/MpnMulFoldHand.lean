/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCarryIdiomsHand

@[expose] public section

set_option autoImplicit false

/-!
# The schoolbook word model of the multiply, proved without `bv_decide`

`MpnMulBasecaseFrontEmit.bcFold_val` and `bcFold_val_zero` depend, through
`MpnMul1FrontEmit.addCarry_split` and `bSltu_le_one`, on the `bv_decide` certificate of
`FieldReduceIdioms.bSltu_eq`. The same statements are proved here on
`MpnCarryIdiomsHand.bSltu_eq_hand` (the proofs are those of the originals, with the hand
lemma in place of the certified one).

## Main results

* `addCarry_split_hand`, `mulAddLimb_val_hand`, `mulAddLimb_flush_hand`, `bcStep_val_hand`,
  `bcPartial_val_hand`, `bcRow_val_hand`, `bcFold_val_hand`, `bcFold_val_zero_hand`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulFoldHand

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_snoc)
open CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo (mulHiW_le mulx_reconstruct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit

/-- The carry-out bit of `x + cy` is `1` exactly when the unbounded sum reaches
    `2 ^ 64`, and the low word is the sum reduced. -/
theorem addCarry_split_hand (x cy : BitVec 64) :
    (x + cy).toNat + 2 ^ 64 * (bSltu (x + cy) x).toNat = x.toNat + cy.toNat := by
  have hx := x.isLt
  have hcy := cy.isLt
  have hsum : (x + cy).toNat = (x.toNat + cy.toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_add]
  rw [MpnCarryIdiomsHand.bSltu_eq_hand]
  by_cases h : 2 ^ 64 ≤ x.toNat + cy.toNat
  · have hlt : (x + cy).ult x = true := by
      simp only [BitVec.ult, decide_eq_true_eq, hsum]
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ite_eq_left hlt, hsum, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]
    omega
  · have hlt : (x + cy).ult x = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, hsum, Nat.not_lt]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ite_eq_right (by simp [hlt]), hsum, Nat.mod_eq_of_lt (by omega)]
    simp only [show ((0 : BitVec 64).toNat) = 0 from rfl]
    omega

/-- **The single-position addmul identity.** `mulAddLimb a v cy r` splits
    `a · v + cy + r` into a low word and a carry-out word:
    `low + 2 ^ 64 · carry-out = a · v + cy + r`. -/
theorem mulAddLimb_val_hand (a v cy r : BitVec 64) :
    (mulAddLimb a v cy r).1.toNat + 2 ^ 64 * (mulAddLimb a v cy r).2.toNat
      = a.toNat * v.toNat + cy.toNat + r.toNat := by
  have hab := mulx_reconstruct a v
  have h1 := addCarry_split_hand (a * v) cy
  have h2 := addCarry_split_hand (a * v + cy) r
  have hc1 := MpnCarryIdiomsHand.bSltu_le_one (a * v + cy) (a * v)
  have hc2 := MpnCarryIdiomsHand.bSltu_le_one (a * v + cy + r) (a * v + cy)
  have hhi := mulHiW_le a v
  have hlo := (a * v).isLt
  have hs1 := (a * v + cy).isLt
  have hs2 := (a * v + cy + r).isLt
  have hcy := cy.isLt
  have hr := r.isLt
  -- The true high word `hi + c1 + c2` is `< 2 ^ 64`, so neither addition wraps.
  have hsum : (mulHiW a v).toNat + (bSltu (a * v + cy) (a * v)).toNat
      + (bSltu (a * v + cy + r) (a * v + cy)).toNat < 2 ^ 64 := by
    have hprod : a.toNat * v.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := a.isLt; omega) (by have := v.isLt; omega)
    obtain ⟨P, hP⟩ : ∃ P, a.toNat * v.toNat = P := ⟨_, rfl⟩
    rw [hP] at hab hprod
    norm_num at hprod
    omega
  have hno1 : (mulHiW a v + bSltu (a * v + cy) (a * v)).toNat
      = (mulHiW a v).toNat + (bSltu (a * v + cy) (a * v)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hno2 : (mulHiW a v + bSltu (a * v + cy) (a * v)
        + bSltu (a * v + cy + r) (a * v + cy)).toNat
      = (mulHiW a v).toNat + (bSltu (a * v + cy) (a * v)).toNat
        + (bSltu (a * v + cy + r) (a * v + cy)).toNat := by
    rw [BitVec.toNat_add, hno1, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨P, hP⟩ : ∃ P, a.toNat * v.toNat = P := ⟨_, rfl⟩
  rw [hP] at hab ⊢
  simp only [mulAddLimb, hno2]
  omega

/-- At the flush trip the multiplicand limb is `0` and the destination word is
    `0`, so the step moves the carry into place and clears it. -/
theorem mulAddLimb_flush_hand (v cy : BitVec 64) :
    mulAddLimb 0 v cy 0 = (cy, 0) := by
  have hzero : ((0 : BitVec 64)).toNat = 0 := rfl
  have hval := mulAddLimb_val_hand 0 v cy 0
  simp only [hzero, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hval
  have hlt := (mulAddLimb 0 v cy 0).1.isLt
  have hcy := cy.isLt
  have h2 : (mulAddLimb 0 v cy 0).2.toNat = 0 := by omega
  have h1 : (mulAddLimb 0 v cy 0).1.toNat = cy.toNat := by omega
  refine Prod.ext ?_ ?_
  · exact BitVec.eq_of_toNat_eq h1
  · exact BitVec.eq_of_toNat_eq (by rw [h2, hzero])

/-- **One inner trip's value identity.** The trip moves
    `2 ^ (64(jd+t)) · (a · v)` into the accumulated product region, re-weighting
    the running carry from `2 ^ (64(jd+t))` to `2 ^ (64(jd+t+1))`. -/
theorem bcStep_val_hand {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd t : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hjt : jd + t < nc) :
    bignumVal (cells (bcStep up vp un nc jd acc t) nc)
        + (2 ^ 64) ^ (jd + t + 1)
            * (memGetDyn (bcStep up vp un nc jd acc t) nc).toNat
      = bignumVal (cells acc nc) + (2 ^ 64) ^ (jd + t) * (memGetDyn acc nc).toNat
        + (2 ^ 64) ^ (jd + t)
            * ((bcLimb up un t).toNat * (memGetDyn vp jd).toNat) := by
  set w := mulAddLimb (bcLimb up un t) (memGetDyn vp jd) (memGetDyn acc nc)
    (memGetDyn acc (jd + t)) with hw
  have hval : w.1.toNat + 2 ^ 64 * w.2.toNat
      = (bcLimb up un t).toNat * (memGetDyn vp jd).toNat
        + (memGetDyn acc nc).toNat + (memGetDyn acc (jd + t)).toNat :=
    mulAddLimb_val_hand _ _ _ _
  have hcarry : memGetDyn (bcStep up vp un nc jd acc t) nc = w.2 :=
    bcStep_carry up vp un nc jd acc t hnc
  have hcells : cells (bcStep up vp un nc jd acc t) nc
      = cells (memSetDyn acc (jd + t) w.1) nc :=
    cells_setDyn_of_le _ nc nc w.2 (by omega) hnc
  have hframe := bignumVal_cells_setDyn acc nc (jd + t) w.1 hjt (by omega)
  have hpow : (2 ^ 64 : Nat) ^ (jd + t + 1) = (2 ^ 64) ^ (jd + t) * 2 ^ 64 :=
    pow_succ _ _
  rw [hcarry, hcells, hpow]
  -- Scale the word identity by the position weight and cancel the destination word.
  have hscaled : (2 ^ 64 : Nat) ^ (jd + t) * w.1.toNat
        + (2 ^ 64) ^ (jd + t) * (2 ^ 64 * w.2.toNat)
      = (2 ^ 64) ^ (jd + t)
          * ((bcLimb up un t).toNat * (memGetDyn vp jd).toNat)
        + (2 ^ 64) ^ (jd + t) * (memGetDyn acc nc).toNat
        + (2 ^ 64) ^ (jd + t) * (memGetDyn acc (jd + t)).toNat := by
    rw [← Nat.mul_add, hval]; ring
  have hassoc : (2 ^ 64 : Nat) ^ (jd + t) * 2 ^ 64 * w.2.toNat
      = (2 ^ 64) ^ (jd + t) * (2 ^ 64 * w.2.toNat) := by ring
  rw [hassoc]
  omega

/-- **The row-prefix invariant.** After `T ≤ un` addmul trips of row `jd`, the
    product region plus the weighted running carry has absorbed
    `2 ^ (64·jd) · value(up[0..T)) · vp[jd]`. -/
theorem bcPartial_val_hand {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hjd : jd + un < nc) :
    ∀ T : Nat, T ≤ un →
      bignumVal (cells (bcPartial up vp un nc jd acc T) nc)
          + (2 ^ 64) ^ (jd + T)
              * (memGetDyn (bcPartial up vp un nc jd acc T) nc).toNat
        = bignumVal (cells acc nc) + (2 ^ 64) ^ jd * (memGetDyn acc nc).toNat
          + (2 ^ 64) ^ jd
              * (bignumVal (cells up T) * (memGetDyn vp jd).toNat) := by
  intro T
  induction T with
  | zero => intro _; simp [bcPartial, cells, bignumVal]
  | succ k ih =>
      intro hk
      have hkun : k < un := by omega
      have hstep := bcStep_val_hand up vp un nc jd k
        (bcPartial up vp un nc jd acc k) hnc (by omega)
      have hIH := ih (by omega)
      have hlimb : bcLimb up un k = memGetDyn up k := by
        simp [bcLimb, hkun]
      rw [hlimb] at hstep
      have hupsucc : bignumVal (cells up (k + 1))
          = bignumVal (cells up k) + (memGetDyn up k).toNat * (2 ^ 64) ^ k := by
        rw [cells_succ, bignumVal_snoc, cells_length]
      have hexpand : (2 ^ 64 : Nat) ^ jd
            * ((bignumVal (cells up k) + (memGetDyn up k).toNat * (2 ^ 64) ^ k)
                * (memGetDyn vp jd).toNat)
          = (2 ^ 64) ^ jd * (bignumVal (cells up k) * (memGetDyn vp jd).toNat)
            + (2 ^ 64) ^ (jd + k)
                * ((memGetDyn up k).toNat * (memGetDyn vp jd).toNat) := by
        rw [pow_add]; ring
      rw [bcPartial_succ, show jd + (k + 1) = jd + k + 1 from rfl, hupsucc, hexpand]
      linarith

/-- **One schoolbook row.** Given a clean carry cell and a zero destination word
    above the row's addmul range, the row adds
    `2 ^ (64·jd) · value(up[0..un)) · vp[jd]` to the product region and leaves
    the carry cell zero. -/
theorem bcRow_val_hand {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hjd : jd + un < nc)
    (hcy : memGetDyn acc nc = 0) (htop : memGetDyn acc (jd + un) = 0) :
    bignumVal (cells (bcRow up vp un nc jd acc) nc)
        = bignumVal (cells acc nc)
          + (2 ^ 64) ^ jd * (bignumVal (cells up un) * (memGetDyn vp jd).toNat)
      ∧ memGetDyn (bcRow up vp un nc jd acc) nc = 0 := by
  have hzero : ((0 : BitVec 64)).toNat = 0 := rfl
  have hA := bcPartial_val_hand up vp un nc jd acc hnc hjd un (by omega)
  -- The addmul prefix never touches the destination word of the flush trip.
  have htopA : memGetDyn (bcPartial up vp un nc jd acc un) (jd + un) = 0 := by
    rw [bcPartial_frame up vp un nc jd acc (jd + un) hnc (by omega) un
      (fun t ht => ⟨by omega, by omega⟩)]
    exact htop
  have hlimb : bcLimb up un un = 0 := by simp [bcLimb]
  have hstep := bcStep_val_hand up vp un nc jd un
    (bcPartial up vp un nc jd acc un) hnc (by omega)
  have hcarry := bcStep_carry up vp un nc jd (bcPartial up vp un nc jd acc un) un hnc
  rw [hlimb, htopA, mulAddLimb_flush_hand] at hcarry
  have hcarry0 : memGetDyn (bcStep up vp un nc jd
      (bcPartial up vp un nc jd acc un) un) nc = 0 := hcarry
  rw [hlimb, hcarry0] at hstep
  simp only [hzero, Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at hstep
  rw [hcy] at hA
  simp only [hzero, Nat.mul_zero, Nat.add_zero] at hA
  have hrow : bcRow up vp un nc jd acc
      = bcStep up vp un nc jd (bcPartial up vp un nc jd acc un) un := by
    rw [bcRow, bcPartial_succ]
  exact ⟨by rw [hrow]; linarith, by rw [hrow]; exact hcarry0⟩

/-- **The schoolbook loop invariant.** After `n` rows the product region holds
    the accumulated product `value(up[0..un)) · value(vp[0..n))`, the carry cell
    is zero, and the cells above the written range are still zero. -/
theorem bcFold_val_hand {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hcy : memGetDyn acc nc = 0) :
    ∀ n : Nat, n + un ≤ nc → ZeroFrom acc un nc →
      bignumVal (cells (bcFold up vp un nc n acc) nc)
          = bignumVal (cells acc nc)
            + bignumVal (cells up un) * bignumVal (cells vp n)
        ∧ memGetDyn (bcFold up vp un nc n acc) nc = 0
        ∧ ZeroFrom (bcFold up vp un nc n acc) (n + un) nc := by
  intro n
  induction n with
  | zero =>
      intro _ hz
      refine ⟨by simp [bcFold, cells, bignumVal], by simpa [bcFold] using hcy, ?_⟩
      simpa [bcFold] using hz
  | succ k ih =>
      intro hk hz
      obtain ⟨hV, hC, hZ⟩ := ih (by omega) hz
      have hjd : k + un < nc := by omega
      have htop : memGetDyn (bcFold up vp un nc k acc) (k + un) = 0 :=
        hZ (k + un) (by omega) (by omega)
      obtain ⟨hrowV, hrowC⟩ := bcRow_val_hand up vp un nc k
        (bcFold up vp un nc k acc) hnc hjd hC htop
      have hvsucc : bignumVal (cells vp (k + 1))
          = bignumVal (cells vp k) + (memGetDyn vp k).toNat * (2 ^ 64) ^ k := by
        rw [cells_succ, bignumVal_snoc, cells_length]
      refine ⟨?_, ?_, ?_⟩
      · rw [bcFold_succ, hrowV, hV, hvsucc]
        ring
      · rw [bcFold_succ]; exact hrowC
      · intro i hi hin
        rw [bcFold_succ, bcRow_frame_gt up vp un nc k _ i hnc hin (by omega)]
        exact hZ i (by omega) hin

/-- **The `mpn_mul_basecase` contract.** Starting from an all-zero accumulator,
    the schoolbook fold leaves the product `up[0..un) · vp[0..vn)` in cells
    `0, …, un+vn-1`. -/
theorem bcFold_val_zero_hand {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un vn : Nat) (acc : Fin NR → BitVec 64)
    (hnc : un + vn < NR) (hz : ∀ i, i < NR → memGetDyn acc i = 0) :
    bignumVal (cells (bcFold up vp un (un + vn) vn acc) (un + vn))
      = bignumVal (cells up un) * bignumVal (cells vp vn) := by
  obtain ⟨hV, _, _⟩ := bcFold_val_hand up vp un (un + vn) acc hnc
    (hz _ hnc) vn (by omega) (fun i _ hin => hz i (by omega))
  rw [hV, bignumVal_cells_zero acc (un + vn) (fun i hi => hz i (by omega))]
  simp

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulFoldHand
