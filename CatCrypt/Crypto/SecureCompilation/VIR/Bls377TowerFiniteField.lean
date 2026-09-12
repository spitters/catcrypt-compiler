/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp12Inv
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp12Inv
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Bls377NonResidue
public import CatCrypt.Crypto.SecureCompilation.VIR.Bls377NonResidue
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.IsField

/-!
# `Fintype` / cardinality / characteristic / field structure for the `bls12_377` tower

`RelationalFrontBls377Fp2` / `RelationalFrontBls377Fp6` build the `bls12_377`
extension tower `Fp2_377 → Fp6_377 → Fp12_377` as plain structures over the base
carrier `FpBLS377 = ZMod bls377Q`, each carrying a parametric `commRing` in the
tower nonresidues. This module adds the finite-field foundation those structures
were missing.

## What this module provides

### Part 1 — finiteness (nonresidue-independent, unconditional)

* `Fintype Fp2_377` / `Fp6_377` / `Fp12_377`, via the coordinate equivalences
  `Fp2_377 ≃ FpBLS377²`, `Fp6_377 ≃ Fp2_377³`, `Fp12_377 ≃ Fp6_377²`.
* `Fp2_377.card` / `Fp6_377.card` / `Fp12_377.card`: the cardinalities are
  `q²`, `q⁶`, `q¹²` with `q = bls377Q`, from `ZMod.card` and `Fintype.card_prod`.
  No primality is used.
* `Fp12_377.charP`: the tower has characteristic `bls377Q` (for any choice of
  tower nonresidues), inherited coordinatewise from `CharP (ZMod bls377Q) _`
  through the `Nat`-cast structure lemmas `natCast_eq`.

### Part 2 — field structure (reduced to non-residuosity)

Each level's `commRing` becomes a `Field` exactly when the relevant norm form is
non-vanishing off `0`. The `IsField` witnesses are built from the
conjugate-over-norm inverses (`Fp2_377.inv` / `Fp6_377.inv6` / `Fp12_377.inv12`):

* `Fp2_377.isField` / `Fp2_377.field` — `IsField`/`Field Fp2_377` given
  `∀ x ≠ 0, norm ξ x ≠ 0`.
* `Fp6_377.isField` / `Fp12_377.isField` — the analogous witnesses one and two
  levels up, gated on the composite tower-norm non-vanishing.
  `IsField.toField` upgrades each to a `Field`.

For `Fp2_377` the hypothesis is reduced to a single clean number-theoretic leaf:
`Fp2_377.normVanish_of_nonsquare` shows `¬ IsSquare ξ → ∀ x ≠ 0, norm ξ x ≠ 0`
(pure field algebra: `norm ξ x = c0² − ξ·c1²`, so a zero norm off `0` exhibits
`ξ = (c0·c1⁻¹)²`). Hence `Fp2_377.fieldOfNonsquare` produces `Field Fp2_377` from
`¬ IsSquare ξ`.

## The remaining number-theoretic obligations (skeleton)

At the concrete `bls12_377` nonresidue `ξ₂ = −5` (so `Fp2 = Fp[u]/(u²+5)`) the one
leaf needed to instantiate `Fp2_377.fieldOfNonsquare` is `¬ IsSquare (−5 : FpBLS377)`
— `−5` is a quadratic non-residue mod `bls377Q`, an Euler-criterion / Legendre-symbol
fact about the 377-bit prime (**not** `decide`/`native_decide`). One level up,
`Fp6`'s and `Fp12`'s norm-non-vanishing hypotheses reduce to `ξ₆ = u` being a
non-cube in `Fp2` and `v` a non-square in `Fp6`. These leaves are stated precisely
in §`Skeleton`; they are the only facts separating the gated witnesses from
unconditional `Field` instances at the concrete parameters.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. `Fintype` and cardinality (nonresidue-independent) -/

namespace Fp2_377

/-- `Fp2_377 ≃ FpBLS377 × FpBLS377`, the coordinate equivalence `c0 + c1·u ↦ (c0, c1)`. -/
def equivProd : Fp2_377 ≃ (FpBLS377 × FpBLS377) where
  toFun x := (x.c0, x.c1)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp2_377` is finite (a product of two copies of `ZMod bls377Q`). -/
instance : Fintype Fp2_377 := Fintype.ofEquiv _ equivProd.symm

/-- `#FpBLS377 = bls377Q`: `ZMod.card` stated at the abbreviation `FpBLS377`, so that a
    rewrite with it matches the goal syntactically. -/
theorem card_base : Fintype.card FpBLS377 = bls377Q := ZMod.card _

/-- `#Fp2_377 = bls377Q²`. -/
theorem card : Fintype.card Fp2_377 = bls377Q ^ 2 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, card_base]
  ring

end Fp2_377

namespace Fp6_377

/-- `Fp6_377 ≃ Fp2_377 × Fp2_377 × Fp2_377`, `c0 + c1·v + c2·v² ↦ (c0, c1, c2)`. -/
def equivProd : Fp6_377 ≃ (Fp2_377 × Fp2_377 × Fp2_377) where
  toFun x := (x.c0, x.c1, x.c2)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp6_377` is finite (three copies of `Fp2_377`). -/
instance : Fintype Fp6_377 := Fintype.ofEquiv _ equivProd.symm

/-- `#Fp6_377 = bls377Q⁶`. -/
theorem card : Fintype.card Fp6_377 = bls377Q ^ 6 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_prod, Fp2_377.card]
  ring

end Fp6_377

namespace Fp12_377

/-- `Fp12_377 ≃ Fp6_377 × Fp6_377`, `c0 + c1·w ↦ (c0, c1)`. -/
def equivProd : Fp12_377 ≃ (Fp6_377 × Fp6_377) where
  toFun x := (x.c0, x.c1)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp12_377` is finite (two copies of `Fp6_377`). -/
instance : Fintype Fp12_377 := Fintype.ofEquiv _ equivProd.symm

/-- `#Fp12_377 = bls377Q¹²`. -/
theorem card : Fintype.card Fp12_377 = bls377Q ^ 12 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fp6_377.card]
  ring

end Fp12_377

/-! ## 2. Characteristic `bls377Q` (inherited coordinatewise)

The `Nat`-cast into each tower level lands entirely in the lowest coordinate,
which is the base-field cast `(n : ZMod bls377Q)`; all other coordinates are `0`.
The three `natCast_eq` lemmas make this precise level by level, and
`Fp12_377.charP` reads the characteristic off the base field. -/

namespace Fp2_377

/-- The `Nat`-cast into `Fp2_377` (under `commRing ξ₂`) is the base cast on `c0`,
    `0` on `c1`. -/
theorem natCast_eq (ξ₂ : FpBLS377) (n : ℕ) :
    letI := commRing ξ₂
    (n : Fp2_377) = ⟨(n : FpBLS377), 0⟩ := by
  letI := commRing ξ₂
  induction n with
  | zero => ext <;> simp
  | succ k ih => rw [Nat.cast_succ, ih]; ext <;> push_cast <;> simp

end Fp2_377

namespace Fp6_377

/-- The `Nat`-cast into `Fp6_377` is the `Fp2_377`-cast on `c0`, `0` on `c1`/`c2`. -/
theorem natCast_eq (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (n : ℕ) :
    letI := commRing ξ₂ ξ₆
    (n : Fp6_377) = ⟨(letI := Fp2_377.commRing ξ₂; (n : Fp2_377)), 0, 0⟩ := by
  letI := Fp2_377.commRing ξ₂
  letI := commRing ξ₂ ξ₆
  induction n with
  | zero => ext <;> simp
  | succ k ih => rw [Nat.cast_succ, ih]; ext <;> push_cast <;> simp

end Fp6_377

namespace Fp12_377

/-- The `Nat`-cast into `Fp12_377` is the `Fp6_377`-cast on `c0`, `0` on `c1`. -/
theorem natCast_eq (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (n : ℕ) :
    letI := commRing ξ₂ ξ₆
    (n : Fp12_377) = ⟨(letI := Fp6_377.commRing ξ₂ ξ₆; (n : Fp6_377)), 0⟩ := by
  letI := Fp2_377.commRing ξ₂
  letI := Fp6_377.commRing ξ₂ ξ₆
  letI := commRing ξ₂ ξ₆
  induction n with
  | zero => ext <;> simp
  | succ k ih => rw [Nat.cast_succ, ih]; ext <;> push_cast <;> simp

/-- `(n : Fp12_377) = 0 ↔ (n : FpBLS377) = 0`: the tower cast vanishes exactly when
    its base-field coordinate does. -/
theorem natCast_eq_zero_iff (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (n : ℕ) :
    letI := commRing ξ₂ ξ₆
    ((n : Fp12_377) = 0 ↔ (n : FpBLS377) = 0) := by
  letI := Fp2_377.commRing ξ₂
  letI := Fp6_377.commRing ξ₂ ξ₆
  letI := commRing ξ₂ ξ₆
  rw [natCast_eq ξ₂ ξ₆ n, Fp6_377.natCast_eq ξ₂ ξ₆ n, Fp2_377.natCast_eq ξ₂ n]
  constructor
  · intro h
    have h3 := congrArg (fun z => ((Fp12_377.c0 z).c0).c0) h
    simpa using h3
  · intro h
    rw [h]
    ext <;> simp

/-- **`Fp12_377` has characteristic `bls377Q`** (for any tower nonresidues), the
    base-field characteristic lifted coordinatewise through `natCast_eq_zero_iff`. -/
theorem charP (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) :
    letI := commRing ξ₂ ξ₆
    CharP Fp12_377 bls377Q := by
  letI := commRing ξ₂ ξ₆
  refine ⟨fun n => ?_⟩
  rw [natCast_eq_zero_iff ξ₂ ξ₆ n]
  exact CharP.cast_eq_zero_iff (ZMod bls377Q) bls377Q n

end Fp12_377

/-! ## 3. Field structure, reduced to non-residuosity

Each level's `commRing` becomes a `Field` given that its norm form is nonzero off
`0`, witnessed as an `IsField` and upgraded via `IsField.toField`. `Fp2_377`'s
hypothesis is reduced to `¬ IsSquare ξ` by `normVanish_of_nonsquare`. -/

namespace Fp2_377

/-- `¬ IsSquare ξ` forces the `Fp2_377` norm to vanish only at `0`. With
    `norm ξ x = c0² − ξ·c1²`, a nonzero `x` with `norm ξ x = 0` and `c1 ≠ 0`
    exhibits `ξ = (c0·c1⁻¹)²`, contradicting `¬ IsSquare ξ`; with `c1 = 0` it
    forces `c0 = 0`, i.e. `x = 0`. Field algebra over `FpBLS377`. -/
theorem normVanish_of_nonsquare [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (hns : ¬ IsSquare ξ) (x : Fp2_377) (hx : x ≠ 0) : norm ξ x ≠ 0 := by
  intro hn
  rw [norm_eq] at hn
  by_cases hc1 : x.c1 = 0
  · apply hx
    rw [hc1] at hn
    have hc0 : x.c0 * x.c0 = 0 := by linear_combination hn
    have hz : x.c0 = 0 := by rcases mul_eq_zero.mp hc0 with h | h <;> exact h
    ext <;> simp [hz, hc1]
  · apply hns
    refine ⟨x.c0 * x.c1⁻¹, ?_⟩
    have hkey : x.c0 * x.c0 = x.c1 * x.c1 * ξ := by linear_combination hn
    have hi : x.c1 * x.c1⁻¹ = 1 := mul_inv_cancel₀ hc1
    calc ξ = ξ * (x.c1 * x.c1⁻¹) * (x.c1 * x.c1⁻¹) := by rw [hi]; ring
      _ = (x.c1 * x.c1 * ξ) * (x.c1⁻¹ * x.c1⁻¹) := by ring
      _ = (x.c0 * x.c0) * (x.c1⁻¹ * x.c1⁻¹) := by rw [hkey]
      _ = x.c0 * x.c1⁻¹ * (x.c0 * x.c1⁻¹) := by ring

/-- **`IsField Fp2_377`** from the norm-non-vanishing hypothesis, with inverses the
    conjugate-over-norm `inv` cancelled by `mul_inv`. -/
theorem isField [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (hnr : ∀ x : Fp2_377, x ≠ 0 → norm ξ x ≠ 0) :
    letI := commRing ξ
    IsField Fp2_377 := by
  letI := commRing ξ
  refine { exists_pair_ne := ⟨0, 1, ?_⟩, mul_comm := fun a b => mul_comm a b,
           mul_inv_cancel := ?_ }
  · intro h
    have := congrArg (fun z => Fp2_377.c0 z) h
    simp at this
  · intro a ha
    exact ⟨inv ξ a, mul_inv ξ a (hnr a ha)⟩

/-- **`Field Fp2_377`** from the norm-non-vanishing hypothesis (`isField` upgraded
    by `IsField.toField`): the `inv` becomes the field `Inv`. -/
noncomputable def field [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (hnr : ∀ x : Fp2_377, x ≠ 0 → norm ξ x ≠ 0) :
    letI := commRing ξ
    Field Fp2_377 :=
  letI := commRing ξ
  (isField ξ hnr).toField

/-- **`Field Fp2_377`** from `¬ IsSquare ξ` — the non-residuosity form combining
    `normVanish_of_nonsquare` with `field`. -/
noncomputable def fieldOfNonsquare [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (hns : ¬ IsSquare ξ) :
    letI := commRing ξ
    Field Fp2_377 :=
  field ξ (normVanish_of_nonsquare ξ hns)

/-- `Field Fp2_377` at the concrete `bls12_377` quadratic nonresidue `ξ₂ = -5`
    (`Fp2 = FpBLS377[u]/(u² + 5)`), discharging the non-residuosity hypothesis of
    `fieldOfNonsquare` with `bls377_neg_five_nonsquare`. -/
noncomputable instance instFieldNegFive [Fact (Nat.Prime bls377Q)] :
    letI := commRing (-5 : FpBLS377)
    Field Fp2_377 :=
  fieldOfNonsquare (-5 : FpBLS377) bls377_neg_five_nonsquare

end Fp2_377

namespace Fp6_377

/-- **`IsField Fp6_377`** from the composite tower-norm non-vanishing hypothesis,
    inverses the conjugate-over-norm `inv6` cancelled by `mul_inv6`.
    `IsField.toField` upgrades this to a `Field`. -/
theorem isField [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (hnr : ∀ x : Fp6_377, x ≠ 0 → Fp2_377.norm ξ₂ (normFp6 ξ₂ ξ₆ x) ≠ 0) :
    letI := commRing ξ₂ ξ₆
    IsField Fp6_377 := by
  letI := commRing ξ₂ ξ₆
  refine { exists_pair_ne := ⟨0, 1, ?_⟩, mul_comm := fun a b => mul_comm a b,
           mul_inv_cancel := ?_ }
  · intro h
    have := congrArg (fun z => (Fp6_377.c0 z).c0) h
    simp at this
  · intro a ha
    exact ⟨inv6 ξ₂ ξ₆ a, mul_inv6 ξ₂ ξ₆ a (hnr a ha)⟩

end Fp6_377

namespace Fp12_377

/-- **`IsField Fp12_377`** from the composite tower-norm non-vanishing hypothesis,
    inverses the conjugate-over-norm `inv12` cancelled by `mul_inv12`.
    `IsField.toField` upgrades this to a `Field`. -/
theorem isField [Fact (Nat.Prime bls377Q)] (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (hnr : ∀ x : Fp12_377, x ≠ 0 →
      Fp2_377.norm ξ₂ (Fp6_377.normFp6 ξ₂ ξ₆ (norm12 ξ₂ ξ₆ x)) ≠ 0) :
    letI := commRing ξ₂ ξ₆
    IsField Fp12_377 := by
  letI := commRing ξ₂ ξ₆
  refine { exists_pair_ne := ⟨0, 1, ?_⟩, mul_comm := fun a b => mul_comm a b,
           mul_inv_cancel := ?_ }
  · intro h
    have := congrArg (fun z => ((Fp12_377.c0 z).c0).c0) h
    simp at this
  · intro a ha
    exact ⟨inv12 ξ₂ ξ₆ a, mul_inv12 ξ₂ ξ₆ a (hnr a ha)⟩

end Fp12_377

/-! ## Skeleton — the concrete `bls12_377` non-residue leaves

The gated witnesses above become unconditional `Field` instances at the concrete
tower parameters `ξ₂ = −5`, `ξ₆ = u`, `w² = v` once the number-theoretic leaves
below are supplied. Each is a statement about the 377-bit prime `bls377Q`,
discharged by Euler-criterion / Legendre-symbol / quadratic-reciprocity tooling
(`ZMod.euler_criterion`, `legendreSym`, `ZMod.exists_sq_eq`), **never** by
`decide`/`native_decide` on the prime.

* **`Fp2` leaf — discharged.** `¬ IsSquare (−5 : FpBLS377)` is proved as
  `bls377_neg_five_nonsquare` (Legendre-symbol route in `Bls377NonResidue`).
  `Fp2_377.instFieldNegFive` feeds it to `Fp2_377.fieldOfNonsquare (−5)`, giving
  `Field Fp2_377` at the true nonresidue (given `Fact (Nat.Prime bls377Q)`).

* **`Fp6` leaf.** `∀ x : Fp6_377, x ≠ 0 → Fp2_377.norm (−5) (normFp6 (−5) u x) ≠ 0`,
  the hypothesis of `Fp6_377.isField (−5) u`. Reduces to `ξ₆ = u` being a non-cube
  in `Fp2_377` (`x³ − u` irreducible over `Fp2`), combined with the `Fp2` leaf.

* **`Fp12` leaf.** `∀ x : Fp12_377, x ≠ 0 →
  Fp2_377.norm (−5) (Fp6_377.normFp6 (−5) u (norm12 (−5) u x)) ≠ 0`, the hypothesis
  of `Fp12_377.isField (−5) u`. Reduces to `v` (the `Fp6` generator) being a
  non-square in `Fp6_377` (`w² − v` irreducible over `Fp6`), combined with the
  `Fp6` leaf.
-/

end CatCrypt.Crypto.SecureCompilation.RelationalFront
