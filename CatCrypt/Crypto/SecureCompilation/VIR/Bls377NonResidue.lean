/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add

/-!
# BLS12-377 base-field non-residue leaf

The `bls12_377` quadratic tower `Fp2_377 = FpBLS377[u]/(u² + 5)` is a field
precisely when `-5` is a non-square in the base field `FpBLS377 = ZMod bls377Q`.
This file proves that fact by the Legendre-symbol route, so that
`Fp2_377.fieldOfNonsquare (-5)` in `Bls377TowerFiniteField` becomes an
unconditional `Field Fp2_377` instance (relative to the base-field primality).

`legendreSym bls377Q (-5) = -1` factors through
`legendreSym bls377Q (-5) = legendreSym bls377Q (-1) * legendreSym bls377Q 5`:

* `legendreSym bls377Q (-1) = 1` because `bls377Q ≡ 1 [MOD 4]`
  (`legendreSym.at_neg_one` and `ZMod.χ₄_nat_one_mod_four`).
* `legendreSym bls377Q 5 = -1` by quadratic reciprocity: since `5 ≡ 1 [MOD 4]`,
  `legendreSym bls377Q 5 = legendreSym 5 bls377Q`, which depends only on
  `bls377Q % 5 = 2`, and `2` is a non-residue modulo `5`.

No `decide`/`native_decide` is used on the 377-bit prime: the only decidable
computations are the small residues `bls377Q % 4`, `bls377Q % 5`, and the
Legendre symbol `legendreSym 5 2` over the two-element target.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-- `bls377Q ≡ 1 [MOD 4]`: the low hex digit of the prime is `1`. -/
theorem bls377Q_mod_four : bls377Q % 4 = 1 := by
  unfold bls377Q; norm_num

/-- `bls377Q ≡ 2 [MOD 5]`. -/
theorem bls377Q_mod_five : bls377Q % 5 = 2 := by
  unfold bls377Q; norm_num

/-- `bls377Q ≠ 2` (it is a 377-bit prime). -/
theorem bls377Q_ne_two : bls377Q ≠ 2 := by
  unfold bls377Q; norm_num

/-- `2` is a non-square modulo `5` (the squares mod `5` are `{0, 1, 4}`). -/
theorem two_nonsquare_zmod_five : ¬ IsSquare (((2 : ℕ) : ZMod 5)) := by
  decide

/-- `legendreSym bls377Q 5 = -1` by quadratic reciprocity (`5 ≡ 1 [MOD 4]`),
    reduced to `legendreSym 5 2 = -1` via `bls377Q % 5 = 2`. -/
theorem legendreSym_bls377Q_five [Fact (Nat.Prime bls377Q)] :
    legendreSym bls377Q (5 : ℤ) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hr := legendreSym.quadratic_reciprocity_one_mod_four
    (p := 5) (q := bls377Q) (by norm_num) bls377Q_ne_two
  rw [show ((5 : ℕ) : ℤ) = (5 : ℤ) by norm_num] at hr
  rw [hr, legendreSym.mod]
  have hmod : ((bls377Q : ℤ)) % (5 : ℕ) = 2 := by
    rw [← Int.natCast_mod, bls377Q_mod_five]; norm_num
  rw [hmod]
  have h2 : legendreSym 5 ((2 : ℕ) : ℤ) = -1 :=
    (legendreSym.eq_neg_one_iff' 5 (a := 2)).mpr two_nonsquare_zmod_five
  simpa using h2

/-- `legendreSym bls377Q (-1) = 1` because `bls377Q ≡ 1 [MOD 4]`. -/
theorem legendreSym_bls377Q_neg_one [Fact (Nat.Prime bls377Q)] :
    legendreSym bls377Q (-1 : ℤ) = 1 := by
  rw [legendreSym.at_neg_one bls377Q_ne_two]
  exact ZMod.χ₄_nat_one_mod_four bls377Q_mod_four

/-- `legendreSym bls377Q (-5) = -1`. -/
theorem legendreSym_bls377Q_neg_five [Fact (Nat.Prime bls377Q)] :
    legendreSym bls377Q (-5 : ℤ) = -1 := by
  have he : (-5 : ℤ) = (-1) * 5 := by ring
  rw [he, legendreSym.mul, legendreSym_bls377Q_neg_one, legendreSym_bls377Q_five]
  ring

/-- **`-5` is a non-square in the `bls12_377` base field.** This is the
    number-theoretic leaf that makes `Fp2_377 = FpBLS377[u]/(u² + 5)` a field:
    feeding it to `Fp2_377.fieldOfNonsquare (-5)` yields `Field Fp2_377`. -/
theorem bls377_neg_five_nonsquare [Fact (Nat.Prime bls377Q)] :
    ¬ IsSquare (-5 : ZMod bls377Q) := by
  have hns := (legendreSym.eq_neg_one_iff bls377Q).mp legendreSym_bls377Q_neg_five
  simpa using hns

end CatCrypt.Crypto.SecureCompilation.RelationalFront
