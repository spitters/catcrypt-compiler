/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.BitVec
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptOps


@[expose] public section
set_option autoImplicit false

/-!
# Layer A: BitVec → Nat coercion library for `poly_zp`

The `bv_to_nat` simp set lifts BitVec-64 polynomial expressions into
Nat with explicit modular reductions. It feeds into Layer B (carry-
chain elimination) and ultimately Layer C+D
(`five_limb_radix51_mul_spec`) for the F1 §3 sorry closure.

## Coverage

| Operation | Lemma | Mathlib? |
|---|---|---|
| `(a + b).toNat` | `BitVec.toNat_add`/`add_toNat_mod` | ✓ |
| `(a * b).toNat` | `BitVec.toNat_mul` | ✓ |
| `(a &&& b).toNat` | `BitVec.toNat_and` | ✓ |
| `(a >>> k).toNat` | `BitVec.toNat_ushiftRight` | ✓ |
| `(BitVec.ofNat n k).toNat` | `BitVec.toNat_ofNat` | ✓ |
| `addCarry a b` decomp | `addCarry_toNat_decomp` | new |
| `addCarryIn a b cin` decomp | `addCarryIn_toNat_decomp` | new |
| `mulx a b` decomp | `mulx_toNat_decomp` | new |
| `bzhi a 51` mask | `bzhi_toNat_51` | new |

The Mathlib lemmas are pulled into the `bv_to_nat` simp set;
the project-specific decompositions are the new content.
-/

namespace CatCrypt.Tactics.BvToNat

open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps

/-! ## §1. Carry-chain decomposition lemmas

These are the carry identities Layer B rests on. The shape is:
`carry · 2^64 + low = a + b + (carry-in)` as ℕ. After this, a chain
of `addCarry` / `addCarryIn` / `mulx` collapses to a polynomial sum
in ℕ. -/

/-- The defining identity for `addCarry`: the (cf, r) pair satisfies
    `cf · 2^64 + r = a + b` as natural numbers. -/
theorem addCarry_toNat_decomp (a b : BitVec 64) :
    (addCarry a b).1.toNat * 2^64 + (addCarry a b).2.toNat
      = a.toNat + b.toNat := by
  -- Both branches reduce to `omega` over the BitVec.toNat_add identity.
  have hadd : (a + b).toNat = (a.toNat + b.toNat) % 2^64 := BitVec.toNat_add a b
  have ha : a.toNat < 2^64 := a.isLt
  have hb : b.toNat < 2^64 := b.isLt
  by_cases h : (a + b).ult a
  · -- Carry case: cf = 1, r = a + b.
    have hult : (a + b).toNat < a.toNat := BitVec.ult_iff_toNat_lt.mp h
    have h1 : (addCarry a b).1.toNat = 1 := by
      simp [addCarry, h]
    have h2 : (addCarry a b).2.toNat = (a + b).toNat := by
      simp [addCarry]
    rw [h1, h2, hadd]
    omega
  · -- No-carry case: cf = 0, r = a + b.
    have hult : (a + b).toNat ≥ a.toNat := by
      by_contra hlt
      push_neg at hlt
      exact h (BitVec.ult_iff_toNat_lt.mpr hlt)
    have h1 : (addCarry a b).1.toNat = 0 := by
      simp [addCarry, h]
    have h2 : (addCarry a b).2.toNat = (a + b).toNat := by
      simp [addCarry]
    rw [h1, h2, hadd]
    omega

/-- Defining identity for `addCarryIn`. The `cin` is masked to {0, 1}
    (top 63 bits ignored, matching x86 ADC flag-input semantics).

    Proof structure: case-split on the two `ult` predicates that define
    the inner cf1 and cf2, four cases. The (cf1=1, cf2=1) case is shown
    impossible because `a + b + cin01 ≤ 2·(2^64 − 1) + 1 < 2·2^64`. -/
theorem addCarryIn_toNat_decomp (a b cin : BitVec 64) :
    (addCarryIn a b cin).1.toNat * 2^64 + (addCarryIn a b cin).2.toNat
      = a.toNat + b.toNat + (cin &&& 1).toNat := by
  have ha : a.toNat < 2^64 := a.isLt
  have hb : b.toNat < 2^64 := b.isLt
  -- cin01 = cin & 1 has value at most 1.
  have hcin_le : (cin &&& 1).toNat ≤ 1 := by
    rw [BitVec.toNat_and]
    have h1nat : ((1 : BitVec 64).toNat) = 1 := by decide
    rw [h1nat]
    exact Nat.and_le_right
  -- Names for the inner intermediate values.
  set cin01 : BitVec 64 := cin &&& 1 with hcin01_def
  set s1 : BitVec 64 := a + b with hs1_def
  set r : BitVec 64 := s1 + cin01 with hr_def
  have hs1_toNat : s1.toNat = (a.toNat + b.toNat) % 2^64 := BitVec.toNat_add a b
  have hs1_lt : s1.toNat < 2^64 := s1.isLt
  have hr_toNat : r.toNat = (s1.toNat + cin01.toNat) % 2^64 := BitVec.toNat_add s1 cin01
  -- `(addCarryIn a b cin)` unfolds to a pair of two if-then-else and r.
  show ((if s1.ult a then (1 : BitVec 64) else 0) |||
        (if r.ult s1 then (1 : BitVec 64) else 0)).toNat * 2^64
        + r.toNat = a.toNat + b.toNat + cin01.toNat
  -- BitVec literals 0, 1 as Nat.
  have h0nat : ((0 : BitVec 64).toNat) = 0 := by decide
  have h1nat : ((1 : BitVec 64).toNat) = 1 := by decide
  -- ult ↔ Nat <
  by_cases h1 : s1.ult a
  · have hu1 : s1.toNat < a.toNat := BitVec.ult_iff_toNat_lt.mp h1
    have hcarry1 : a.toNat + b.toNat ≥ 2^64 := by
      rw [hs1_toNat] at hu1
      have hmlt := Nat.mod_lt (a.toNat + b.toNat) (by decide : (2^64 : Nat) > 0)
      omega
    have hs1_eq : s1.toNat = a.toNat + b.toNat - 2^64 := by
      rw [hs1_toNat]; omega
    by_cases h2 : r.ult s1
    · -- cf1=1 ∧ cf2=1: impossible.
      exfalso
      have hu2 : r.toNat < s1.toNat := BitVec.ult_iff_toNat_lt.mp h2
      rw [hr_toNat] at hu2
      have hsum_le : s1.toNat + cin01.toNat ≤ 2^64 := by omega
      rcases Nat.lt_or_ge (s1.toNat + cin01.toNat) (2^64) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hu2; omega
      · -- s1+cin01 = 2^64. With cf1=1: s1 = a+b-2^64, so a+b+cin01 = 2·2^64.
        --   But a+b+cin01 ≤ 2·(2^64-1)+1 < 2·2^64. Contradiction.
        have heq : s1.toNat + cin01.toNat = 2^64 := by omega
        have : a.toNat + b.toNat + cin01.toNat = 2 * 2^64 := by omega
        omega
    · -- cf1=1, cf2=0.
      have hnu2 : ¬ r.toNat < s1.toNat := fun hh =>
        h2 (BitVec.ult_iff_toNat_lt.mpr hh)
      have hr_eq : r.toNat = s1.toNat + cin01.toNat := by
        rw [hr_toNat] at *
        rcases Nat.lt_or_ge (s1.toNat + cin01.toNat) (2^64) with hlt | hge
        · exact Nat.mod_eq_of_lt hlt
        · -- s1+cin01 ≥ 2^64; with s1<2^64 and cin01≤1, must equal 2^64; r mod = 0.
          --   Then 0 ≥ s1.toNat would force s1=0, but cin01=1 gives 0+1=2^64 absurd.
          exfalso
          have heq : s1.toNat + cin01.toNat = 2^64 := by omega
          rw [hr_toNat] at hnu2
          rw [show s1.toNat + cin01.toNat = 2^64 from heq] at hnu2
          simp at hnu2
          omega
      simp only [if_pos h1, if_neg h2]
      rw [BitVec.toNat_or, h1nat, h0nat]
      simp only [Nat.or_zero]
      omega
  · -- cf1=0
    have hnu1 : ¬ s1.toNat < a.toNat := fun hh =>
      h1 (BitVec.ult_iff_toNat_lt.mpr hh)
    have hnocarry1 : a.toNat + b.toNat < 2^64 := by
      by_contra hge
      push_neg at hge
      have hmod : (a.toNat + b.toNat) % 2^64 = a.toNat + b.toNat - 2^64 := by
        rw [Nat.mod_eq_sub_mod hge]
        apply Nat.mod_eq_of_lt
        omega
      apply hnu1
      rw [hs1_toNat, hmod]
      omega
    have hs1_eq0 : s1.toNat = a.toNat + b.toNat := by
      rw [hs1_toNat, Nat.mod_eq_of_lt hnocarry1]
    by_cases h2 : r.ult s1
    · -- cf1=0, cf2=1.
      have hu2 : r.toNat < s1.toNat := BitVec.ult_iff_toNat_lt.mp h2
      rw [hr_toNat] at hu2
      have hsum_le : s1.toNat + cin01.toNat ≤ 2^64 := by omega
      have hsum_eq : s1.toNat + cin01.toNat = 2^64 := by
        rcases Nat.lt_or_ge (s1.toNat + cin01.toNat) (2^64) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hu2; omega
        · omega
      have hr_zero : r.toNat = 0 := by
        rw [hr_toNat, hsum_eq, Nat.mod_self]
      simp only [if_neg h1, if_pos h2]
      rw [BitVec.toNat_or, h1nat, h0nat]
      simp only [Nat.zero_or]
      omega
    · -- cf1=0, cf2=0.
      have hnu2 : ¬ r.toNat < s1.toNat := fun hh =>
        h2 (BitVec.ult_iff_toNat_lt.mpr hh)
      have hsum_lt : s1.toNat + cin01.toNat < 2^64 := by
        by_contra hge
        push_neg at hge
        rw [hr_toNat] at hnu2
        have heq : s1.toNat + cin01.toNat = 2^64 := by omega
        rw [show s1.toNat + cin01.toNat = 2^64 from heq] at hnu2
        rw [Nat.mod_self] at hnu2
        push_neg at hnu2
        omega
      have hr_eq : r.toNat = s1.toNat + cin01.toNat := by
        rw [hr_toNat, Nat.mod_eq_of_lt hsum_lt]
      simp only [if_neg h1, if_neg h2, BitVec.or_self]
      omega

/-! ## §2. Mathlib BitVec lemmas (re-exported under `bv_to_nat` simp set)

These pull through Mathlib's existing `BitVec.toNat_*` family under
the `@[bv_to_nat]` tag so a `simp [bv_to_nat]` call lifts every
BitVec polynomial fragment. -/

attribute [simp] BitVec.toNat_add BitVec.toNat_mul BitVec.toNat_and
                 BitVec.toNat_or BitVec.toNat_xor
                 BitVec.toNat_shiftLeft BitVec.toNat_ushiftRight

/-! ## §3. Limb-mask: `bzhi a 51` extracts low 51 bits.

For Curve25519's radix-2^51 layout, `bzhi a 51 = a &&& (2^51 - 1)` as
BitVec; in Nat, `(bzhi a 51).toNat = a.toNat % 2^51`. -/

theorem bzhi_toNat_51 (a : BitVec 64) :
    (bzhi a 51).toNat = a.toNat % 2^51 := by
  -- Prove via the simple closed form.
  have hreduced : (bzhi a 51) = a &&& BitVec.ofNat 64 (1 <<< 51 - 1) := by
    simp [bzhi]
  rw [hreduced, BitVec.toNat_and]
  have hmask : ((BitVec.ofNat 64 (1 <<< 51 - 1)).toNat : Nat) = 2^51 - 1 := by
    simp [BitVec.toNat_ofNat]
  rw [hmask]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 51

/-- Defining identity for `mulx`: hi:lo = a · b as Nat. -/
theorem mulx_toNat_decomp (a b : BitVec 64) :
    (mulx a b).1.toNat * 2^64 + (mulx a b).2.toNat
      = a.toNat * b.toNat := by
  unfold mulx
  simp only [BitVec.toNat_ofNat]
  have ha : a.toNat < 2^64 := a.isLt
  have hb : b.toNat < 2^64 := b.isLt
  -- a · b < 2^128.
  have hprod : a.toNat * b.toNat < 2^128 := by
    have h1 : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
      Nat.mul_le_mul (Nat.le_pred_of_lt ha) (Nat.le_pred_of_lt hb)
    have h2 : ((2^64 : Nat) - 1) * (2^64 - 1) < 2^128 := by decide
    omega
  -- (a · b) >>> 64 = (a · b) / 2^64 (ushiftRight semantics on Nat).
  have hshr : (a.toNat * b.toNat) >>> 64 = (a.toNat * b.toNat) / 2^64 := by
    simp [Nat.shiftRight_eq_div_pow]
  rw [hshr]
  -- Goal: ((a·b)/2^64 % 2^64) · 2^64 + (a·b) % 2^64 = a · b.
  have hdiv_lt : (a.toNat * b.toNat) / 2^64 < 2^64 := by
    apply Nat.div_lt_iff_lt_mul (by decide : (2^64 : Nat) > 0) |>.mpr
    have hpow : (2^64 : Nat) * 2^64 = 2^128 := by decide
    omega
  have hmod_id : (a.toNat * b.toNat) / 2^64 % 2^64
              = (a.toNat * b.toNat) / 2^64 :=
    Nat.mod_eq_of_lt hdiv_lt
  rw [hmod_id]
  -- Standard div/mod identity.
  have := Nat.div_add_mod (a.toNat * b.toNat) (2^64)
  omega

/-! ## §4. Layer B: chain-walk through `setReg` cascades

When `bignumExecPlus body s` has been reduced by the BignumStep simp set,
the result is a `some (setReg ⋯ (setReg s …) …)` chain. To lift it to
Nat-level polynomial form, the standard trick is:

1. Project `(setReg-chain s).regs r` to a closed BitVec expression in the
   original `s.regs *` and the operation outputs. The
   `BignumStep.setReg_regs_same` and `BignumStep.setReg_regs_diff` simp
   lemmas already do this — `simp` walks the chain.
2. Apply the Layer A `_toNat_decomp` lemmas to convert each operation's
   output to a Nat polynomial.

No new chain-walk lemmas are needed in BvToNat — the existing BignumStep
projection lemmas, combined with Layer A, are sufficient.

A cross-register memory-disjointness lemma (`load64Mem_storeMem_ne`)
will eventually be needed for the output-readback step in `runMul`, but
the F1 §3 closure path arranges `mkInitMulState`'s pointers so that the
relevant disjointness can be discharged by `decide`. The general lemma
is deferred until a real client materialises. -/

end CatCrypt.Tactics.BvToNat
