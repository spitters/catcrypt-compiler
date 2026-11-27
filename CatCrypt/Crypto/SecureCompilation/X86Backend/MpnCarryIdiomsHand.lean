/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit

@[expose] public section

set_option autoImplicit false

/-!
# The carry idioms of the mpn kernels, proved without `bv_decide`

`FieldReduceIdioms.bSltu_eq`, `MpnAddSubFrontDenote.halfCarryW_eq` and
`MpnCmpFrontEmit.selW_eq` are proved by `bv_decide`, so every theorem through them depends on
`Lean.ofReduceBool` certificates. This module proves the same statements by hand (bit 63 of a
word and `toNat` arithmetic) and re-proves on them the word-model lemmas the kernels' end
theorems use: the add/sub limb identities and folds (`addFold_val_hand`, `subFold_val_hand`)
and the compare fold (`cmpFold_val_full_hand`).

## Main results

* `bSltu_eq_hand`, `halfCarryW_eq_hand`, `selW_eq_hand`: the three idioms.
* `addFold_val_hand`, `subFold_val_hand`, `cmpFold_val_full_hand`: the word-model invariants.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCarryIdiomsHand

open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_snoc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length memGetDyn_memSetDyn_self)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
  (halfCarryW addLimbW subLimbW addStep subStep addFold subFold addFold_succ subFold_succ
   xor_one_toNat cells_setDyn_succ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
  (cmpSign cmpSign_eq_zero_iff cmpSign_radix cmpStepW cmpSelW cmpFoldStep cmpFold cmpFold_succ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells segCells_cons)

/-! ## 1. Bit 63 and the unsigned compare -/

theorem bit63 (x : BitVec 64) : x.getLsbD 63 = decide (2 ^ 63 ≤ x.toNat) := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  exact decide_eq_decide.mpr (by omega)

theorem shr63 (x : BitVec 64) : x >>> 63 = if x.getLsbD 63 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, bit63, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  split_ifs with h
  · rw [decide_eq_true_eq] at h
    rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega
  · rw [decide_eq_true_eq] at h
    rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega

/-- **`bSltu` is the unsigned compare** (`FieldReduceIdioms.bSltu_eq`, by hand). -/
theorem bSltu_eq_hand (a b : BitVec 64) :
    bSltu a b = (if a.ult b then (1 : BitVec 64) else 0) := by
  unfold bSltu
  rw [shr63]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor]
  simp only [bit63, BitVec.ult, BitVec.toNat_sub]
  have ha := a.isLt
  have hb := b.isLt
  congr 1
  by_cases h1 : 2 ^ 63 ≤ a.toNat <;> by_cases h2 : 2 ^ 63 ≤ b.toNat <;>
    by_cases h3 : 2 ^ 63 ≤ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 <;>
    by_cases h4 : a.toNat < b.toNat <;> simp [*] <;> omega

theorem bSltu_le_one (a b : BitVec 64) : (bSltu a b).toNat ≤ 1 := by
  rw [bSltu_eq_hand]; split <;> simp

/-! ## 2. The half-add carry -/

theorem and_one_toNat (x y : BitVec 64) :
    ((x &&& y) &&& 1#64).toNat = (x.toNat % 2) * (y.toNat % 2) := by
  rw [BitVec.toNat_and, BitVec.toNat_and, show (1#64).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_mod_two_pow]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with h' | h' <;> simp [h, h']

/-- **The half-add carry word is `bSltu (x + y) x`** (`halfCarryW_eq`, by hand). -/
theorem halfCarryW_eq_hand (x y : BitVec 64) : halfCarryW x y = bSltu (x + y) x := by
  unfold halfCarryW
  rw [bSltu_eq_hand, shr63, bit63]
  have hx := x.isLt
  have hy := y.isLt
  have hp : (x.toNat % 2) * (y.toNat % 2) = (x.toNat % 2 + y.toNat % 2) / 2 := by
    rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with h' | h' <;> simp [h, h']
  have e : ((x >>> 1) + (y >>> 1) + ((x &&& y) &&& 1#64)).toNat
      = x.toNat / 2 + y.toNat / 2 + (x.toNat % 2) * (y.toNat % 2) := by
    rw [BitVec.toNat_add, BitVec.toNat_add, and_one_toNat, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    omega
  have key : (2 ^ 63 ≤ x.toNat / 2 + y.toNat / 2 + (x.toNat % 2) * (y.toNat % 2))
      ↔ (x + y).toNat < x.toNat := by
    rw [BitVec.toNat_add]; omega
  rw [e]
  simp only [BitVec.ult, key]

/-! ## 3. The add and sub limbs and folds -/

theorem addCarry_toNat_hand (a b : BitVec 64) :
    (a + b).toNat + (bSltu (a + b) a).toNat * 2 ^ 64 = a.toNat + b.toNat := by
  rw [bSltu_eq_hand]
  have ha := a.isLt; have hb := b.isLt
  have hadd : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  have h0 : (0 : BitVec 64).toNat = 0 := by decide
  by_cases h : (a + b).ult a
  · rw [ite_eq_left h, h1]
    have hlt : (a + b).toNat < a.toNat := by simpa [BitVec.ult] using h
    omega
  · rw [ite_eq_right h, h0]
    have hge : ¬ (a + b).toNat < a.toNat := by simpa [BitVec.ult] using h
    omega

theorem adc_toNat_hand (a b cin : BitVec 64) :
    (a + b + cin).toNat
        + (bSltu (a + b) a + bSltu (a + b + cin) (a + b)).toNat * 2 ^ 64
      = a.toNat + b.toNat + cin.toNat := by
  have e1 := addCarry_toNat_hand a b
  have e2 := addCarry_toNat_hand (a + b) cin
  have hc1 := bSltu_le_one (a + b) a
  have hc2 := bSltu_le_one (a + b + cin) (a + b)
  generalize bSltu (a + b) a = C1 at e1 hc1 ⊢
  generalize bSltu (a + b + cin) (a + b) = C2 at e2 hc2 ⊢
  have hsum2 : C1.toNat + C2.toNat < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.add_le_add hc1 hc2) (by norm_num)
  have hcsum : (C1 + C2).toNat = C1.toNat + C2.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum2]
  rw [hcsum]
  linarith [e1, e2]

theorem adc_carry_le_hand (a b cin : BitVec 64) (hc : cin.toNat ≤ 1) :
    (bSltu (a + b) a + bSltu (a + b + cin) (a + b)).toNat ≤ 1 := by
  have h := adc_toNat_hand a b cin
  have ha := a.isLt; have hb := b.isLt
  have hs := (a + b + cin).isLt
  nlinarith [h, ha, hb, hs, hc, Nat.zero_le (a + b + cin).toNat]

theorem addLimbW_val_hand (x y c : BitVec 64) (hc : c.toNat ≤ 1) :
    (addLimbW x y c).1.toNat + (addLimbW x y c).2.toNat * 2 ^ 64
        = x.toNat + y.toNat + c.toNat
      ∧ (addLimbW x y c).2.toNat ≤ 1 :=
  ⟨adc_toNat_hand x y c, adc_carry_le_hand x y c hc⟩

theorem subLimbW_val_hand (x y bw : BitVec 64) (hbw : bw.toNat ≤ 1) :
    (subLimbW x y bw).1.toNat + y.toNat + bw.toNat
        = x.toNat + (subLimbW x y bw).2.toNat * 2 ^ 64
      ∧ (subLimbW x y bw).2.toNat ≤ 1 := by
  have hcx : (bw ^^^ 1#64).toNat = 1 - bw.toNat := xor_one_toNat bw hbw
  have hcx1 : (bw ^^^ 1#64).toNat ≤ 1 := by omega
  obtain ⟨hv, hc⟩ := addLimbW_val_hand x (~~~y) (bw ^^^ 1#64) hcx1
  have hco := xor_one_toNat _ hc
  have hny : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := BitVec.toNat_not
  have hy := y.isLt
  simp only [subLimbW]
  refine ⟨?_, by omega⟩
  rw [hco]
  rw [hcx, hny] at hv
  generalize (addLimbW x (~~~y) (bw ^^^ 1#64)).2.toNat = C at hv hc ⊢
  generalize (addLimbW x (~~~y) (bw ^^^ 1#64)).1.toNat = S at hv ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega

/-- **The add loop invariant** (`addFold_val`, on the hand-proved limb identity). -/
theorem addFold_val_hand {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (o : Fin NR → BitVec 64) (c₀ : BitVec 64) (hc₀ : c₀.toNat ≤ 1) :
    ∀ k, k ≤ NR →
      bignumVal (cells (addFold ap bp k (o, c₀)).1 k)
          + (addFold ap bp k (o, c₀)).2.toNat * (2 ^ 64) ^ k
        = bignumVal (cells ap k) + bignumVal (cells bp k) + c₀.toNat
      ∧ (addFold ap bp k (o, c₀)).2.toNat ≤ 1 := by
  intro k
  induction k with
  | zero => intro _; simp [addFold, cells, bignumVal, hc₀]
  | succ k ih =>
      intro hk
      obtain ⟨hv, hc⟩ := ih (by omega)
      rw [addFold_succ]
      obtain ⟨hl, hl1⟩ := addLimbW_val_hand (memGetDyn ap k) (memGetDyn bp k)
        (addFold ap bp k (o, c₀)).2 hc
      refine ⟨?_, hl1⟩
      simp only [addStep]
      rw [cells_setDyn_succ _ _ _ (by omega), bignumVal_snoc, cells_length,
        cells_succ ap, cells_succ bp, bignumVal_snoc, bignumVal_snoc, cells_length,
        cells_length, pow_succ ((2 : Nat) ^ 64) k]
      generalize ((2 : Nat) ^ 64) ^ k = P at hv ⊢
      generalize (2 : Nat) ^ 64 = B at hl ⊢
      generalize (addFold ap bp k (o, c₀)).2.toNat = C at hv hl ⊢
      linear_combination hv + P * hl

/-- **The sub loop invariant** (`subFold_val`, on the hand-proved limb identity). -/
theorem subFold_val_hand {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (o : Fin NR → BitVec 64) (bw₀ : BitVec 64) (hbw₀ : bw₀.toNat ≤ 1) :
    ∀ k, k ≤ NR →
      bignumVal (cells (subFold ap bp k (o, bw₀)).1 k) + bignumVal (cells bp k) + bw₀.toNat
        = bignumVal (cells ap k) + (subFold ap bp k (o, bw₀)).2.toNat * (2 ^ 64) ^ k
      ∧ (subFold ap bp k (o, bw₀)).2.toNat ≤ 1 := by
  intro k
  induction k with
  | zero => intro _; simp [subFold, cells, bignumVal, hbw₀]
  | succ k ih =>
      intro hk
      obtain ⟨hv, hc⟩ := ih (by omega)
      rw [subFold_succ]
      obtain ⟨hl, hl1⟩ := subLimbW_val_hand (memGetDyn ap k) (memGetDyn bp k)
        (subFold ap bp k (o, bw₀)).2 hc
      refine ⟨?_, hl1⟩
      simp only [subStep]
      rw [cells_setDyn_succ _ _ _ (by omega), bignumVal_snoc, cells_length,
        cells_succ ap, cells_succ bp, bignumVal_snoc, bignumVal_snoc, cells_length,
        cells_length, pow_succ ((2 : Nat) ^ 64) k]
      generalize ((2 : Nat) ^ 64) ^ k = P at hv ⊢
      generalize (2 : Nat) ^ 64 = B at hl ⊢
      generalize (subFold ap bp k (o, bw₀)).2.toNat = C at hv hl ⊢
      linear_combination hv + P * hl

/-! ## 4. The compare -/

/-- **The emitted mask select** (`selW_eq`, by hand). -/
theorem selW_eq_hand (prev s : BitVec 64) :
    prev ^^^ ((bSltu 0 prev - 1) &&& (s ^^^ prev)) = if prev = 0 then s else prev := by
  rw [bSltu_eq_hand]
  by_cases h : prev = 0
  · subst h
    have h0 : (if (0 : BitVec 64).ult 0 then (1 : BitVec 64) else 0) = 0 := rfl
    rw [h0, ite_eq_left rfl, show (0 : BitVec 64) - 1 = BitVec.allOnes 64 from rfl,
      show s ^^^ (0 : BitVec 64) = s from BitVec.xor_zero, BitVec.allOnes_and]
    exact BitVec.zero_xor
  · have h0 : (0 : BitVec 64).toNat = 0 := rfl
    have hlt : (0 : BitVec 64).ult prev = true := by
      simp only [BitVec.ult, decide_eq_true_eq, h0]
      have : prev.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [h', h0]))
      omega
    rw [ite_eq_left hlt, ite_eq_right h, BitVec.sub_self, BitVec.zero_and, BitVec.xor_zero]

theorem cmpStepW_eq_hand (x y : BitVec 64) : cmpStepW x y = cmpSign x.toNat y.toNat := by
  unfold cmpStepW cmpSign
  rw [bSltu_eq_hand, bSltu_eq_hand]
  simp only [BitVec.ult, decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

theorem cmpSelW_eq_hand (prev x y : BitVec 64) :
    cmpSelW prev x y = if prev = 0 then cmpSign x.toNat y.toNat else prev := by
  rw [cmpSelW, selW_eq_hand, cmpStepW_eq_hand]

/-- **The comparison loop invariant** (`cmpFold_val`, on the hand-proved selection). -/
theorem cmpFold_val_hand {NR NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (top : Nat) (acc : Fin NR → BitVec 64) (hNR : 0 < NR)
    (h0 : memGetDyn acc 0 = 0) :
    ∀ k : Nat, k ≤ top + 1 →
      memGetDyn (cmpFold ap bp top k acc) 0
        = cmpSign (bignumVal (segCells ap (top + 1 - k) k))
            (bignumVal (segCells bp (top + 1 - k) k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [cmpFold, segCells, bignumVal, cmpSign, h0]
  | succ m ih =>
      intro hm
      have hm' : m ≤ top + 1 := by omega
      have hIH := ih hm'
      have hbase : top + 1 - (m + 1) = top - m := by omega
      have hshift : top - m + 1 = top + 1 - m := by omega
      rw [cmpFold_succ, cmpFoldStep, memGetDyn_memSetDyn_self _ 0 _ hNR,
        cmpSelW_eq_hand, hIH, hbase, segCells_cons, segCells_cons, hshift]
      simp only [bignumVal, cmpSign_radix]
      by_cases hEq : bignumVal (segCells ap (top + 1 - m) m)
          = bignumVal (segCells bp (top + 1 - m) m)
      · rw [ite_eq_left hEq, ite_eq_left ((cmpSign_eq_zero_iff _ _).mpr hEq)]
      · rw [ite_eq_right hEq, ite_eq_right (fun hc => hEq ((cmpSign_eq_zero_iff _ _).mp hc))]

theorem cmpFold_val_full_hand {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (top : Nat) (acc : Fin NR → BitVec 64) (hNR : 0 < NR)
    (h0 : memGetDyn acc 0 = 0) :
    memGetDyn (cmpFold ap bp top (top + 1) acc) 0
      = cmpSign (bignumVal (segCells ap 0 (top + 1)))
          (bignumVal (segCells bp 0 (top + 1))) := by
  have h := cmpFold_val_hand ap bp top acc hNR h0 (top + 1) (Nat.le_refl _)
  rwa [show top + 1 - (top + 1) = 0 from by omega] at h

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCarryIdiomsHand
