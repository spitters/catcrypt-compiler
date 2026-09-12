/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Bls377TowerFiniteField
public import CatCrypt.Crypto.SecureCompilation.VIR.Bls377TowerFiniteField
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Bls377NonResidue
public import CatCrypt.Crypto.SecureCompilation.VIR.Bls377NonResidue

/-!
# BLS12-377 higher-tower non-residue leaves

`Bls377NonResidue` proves the base-field leaf `¬ IsSquare (-5 : ZMod bls377Q)`
that turns `Fp2_377 = FpBLS377[u]/(u²+5)` into a field. This module handles the
two remaining tower leaves that `Bls377TowerFiniteField` left as obligations at
the concrete parameters `ξ₂ = -5`, `ξ₆ = u = ⟨0,1⟩`, `w² = v`:

* the `Fp6` leaf — `∀ x ≠ 0, Fp2_377.norm (-5) (normFp6 (-5) u x) ≠ 0`, the
  hypothesis of `Fp6_377.isField (-5) u`;
* the `Fp12` leaf — `∀ x ≠ 0, Fp2_377.norm (-5) (normFp6 (-5) u (norm12 (-5) u x)) ≠ 0`,
  the hypothesis of `Fp12_377.isField (-5) u`.

## What is proved here

* `bls377_five_nonsquare` — `¬ IsSquare (5 : ZMod bls377Q)`, symbolically by the
  Legendre route (`5 = (-1)·(-5)`, so `legendreSym bls377Q 5 = -1`; reuses
  `legendreSym_bls377Q_five`). This completes the base-field Legendre triple
  `(-1` a square, `5` a non-square, `-5` a non-square`)`. No `decide` /
  `native_decide` on the 377-bit prime.

* `noncube_of_norm_noncube` — the norm map `Fp2_377 → FpBLS377` sends cubes to
  cubes, so a base element whose value is not a cube in `FpBLS377` is not the
  norm of a cube: `¬(∃ w, w³ = norm ξ g) → ¬(∃ z, z³ = g)`. Reuses
  `Fp2_377.norm_mul`.

* `fp2_u_nonCube_of_fp_five_nonCube` — the concrete instance: since
  `norm (-5) u = 5`, the base cubic fact `FpFiveNonCube` (`5` a non-cube mod
  `bls377Q`) forces `u = ⟨0,1⟩` to be a non-cube in `Fp2_377`. This is the
  algebraic core of the `Fp6` leaf.

* `fp12Leaf_of` — the `Fp12` leaf follows from the `Fp6` leaf together with
  `norm12` being anisotropic (`v` a non-square in `Fp6`): the composite outer
  form of the `Fp12` leaf is the `Fp6`-leaf predicate evaluated at `norm12 x`.

* `fp6Field` / `fp12Field` — the conditional field instances at the concrete
  parameters, given the respective tower leaves (`isField … |>.toField`).

## The two reductions and what mathlib is missing

Fp6 leaf ⟸ `u` non-cube in `Fp2` ⟸ `FpFiveNonCube` (`5` non-cube mod `bls377Q`).
The second `⟸` is `fp2_u_nonCube_of_fp_five_nonCube` (proved). Two facts remain:

* **Cubic-anisotropy of the Fp6 norm form** (`u` non-cube ⟹ Fp6 leaf). This is
  the cubic analogue of `Fp2_377.normVanish_of_nonsquare`: `x³ - u` has no root
  over `Fp2`, hence is irreducible (degree 3), hence the quotient is a domain and
  the cubic norm form is anisotropic. Unlike the quadratic case a zero norm off
  `0` does not exhibit a cube root of `u` by elementary algebra, so this needs
  the polynomial-quotient irreducibility bridge (`AdjoinRoot` / `X^n - C a`
  irreducibility), which the hand-rolled `Fp6_377` structure is not connected to.

* **`FpFiveNonCube`** (`5` a non-cube mod `bls377Q`). Mathlib has `legendreSym`,
  quadratic reciprocity, and `ZMod.euler_criterion` for squares, but no cubic
  residue character / cubic reciprocity (Eisenstein-integer) analogue; the
  Euler-style criterion `5^((q-1)/3) ≠ 1` would require a 377-bit modular
  exponentiation, i.e. `native_decide`, which is excluded here.

Fp12 leaf ⟸ Fp6 leaf ∧ (`norm12` anisotropic). The composition is `fp12Leaf_of`
(proved). The anisotropy `norm12` reduces (quadratic case, like
`Fp2_377.normVanish_of_nonsquare` one level up) to `v` a non-square in `Fp6`,
which reduces through the `Fp6 → Fp` norm to `bls377_five_nonsquare` — the value
`5 = N_{Fp6/Fp}(v)` is a non-square (proved). Assembling this last step needs
multiplicativity of `normFp6` (`Fp6_377.normFp6_mul`), which the codebase proves
for `Fp2_377.norm` and `Fp12_377.norm12` but not yet for `normFp6`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The base-field Legendre leaf `5` is a non-square -/

/-- `5` is a non-square in the `bls12_377` base field. Since `5 = (-1)·(-5)` and
    `legendreSym bls377Q 5 = -1` (`legendreSym_bls377Q_five`), the Legendre
    criterion gives `¬ IsSquare (5 : ZMod bls377Q)`. This is the base-field value
    of the `Fp6 → Fp` norm of the `Fp12` generator `v`, so it drives the `Fp12`
    non-residue branch, and it completes the base-field Legendre triple next to
    `bls377_neg_five_nonsquare`. -/
theorem bls377_five_nonsquare [Fact (Nat.Prime bls377Q)] :
    ¬ IsSquare (5 : ZMod bls377Q) := by
  have hns := (legendreSym.eq_neg_one_iff bls377Q).mp legendreSym_bls377Q_five
  simpa using hns

/-! ## 2. The norm map sends cubes to cubes -/

/-- The `Fp2_377 → FpBLS377` field norm sends cubes to cubes: if `g = z³` then
    `norm ξ g = (norm ξ z)³`, from `Fp2_377.norm_mul`. Contrapositively, if
    `norm ξ g` is not a cube in the base field then `g` is not a cube in
    `Fp2_377`. -/
theorem noncube_of_norm_noncube (ξ : FpBLS377) (g : Fp2_377)
    (h : ¬ ∃ w : FpBLS377, w ^ 3 = Fp2_377.norm ξ g) :
    letI := Fp2_377.commRing ξ
    ¬ ∃ z : Fp2_377, z ^ 3 = g := by
  letI := Fp2_377.commRing ξ
  rintro ⟨z, hz⟩
  apply h
  refine ⟨Fp2_377.norm ξ z, ?_⟩
  have e1 : z ^ 3 = z * z * z := by ring
  have e2 : Fp2_377.norm ξ z ^ 3
      = Fp2_377.norm ξ z * Fp2_377.norm ξ z * Fp2_377.norm ξ z := by ring
  rw [← hz, e1, e2, Fp2_377.norm_mul, Fp2_377.norm_mul]

/-! ## 3. The concrete `Fp6` non-residue core: `u` is a non-cube in `Fp2` -/

/-- The base cubic non-residue leaf: `5` has no cube root modulo `bls377Q`. This
    is the number-theoretic fact underlying `Fp6_377` being a field at the true
    parameters; see the module docstring for the mathlib gap that blocks a
    symbolic proof. -/
abbrev FpFiveNonCube : Prop := ¬ ∃ w : FpBLS377, w ^ 3 = (5 : FpBLS377)

/-- The `Fp2_377` norm of the cubic generator `u = ⟨0,1⟩` at `ξ₂ = -5` is `5`
    (`norm (-5) u = 0² − (-5)·1² = 5`). -/
theorem norm_u_eq_five : Fp2_377.norm (-5 : FpBLS377) ⟨0, 1⟩ = 5 := by
  rw [Fp2_377.norm_eq]
  show (0 : FpBLS377) * 0 - 1 * 1 * (-5) = 5
  ring

/-- At the concrete parameters `ξ₂ = -5`, `u = ⟨0,1⟩`, the base cubic leaf
    `FpFiveNonCube` forces `u` to be a non-cube in `Fp2_377`: a cube root of `u`
    would push down through the norm to a cube root of `norm (-5) u = 5`. This is
    the algebraic core of the `Fp6` non-residue leaf. -/
theorem fp2_u_nonCube_of_fp_five_nonCube (h : FpFiveNonCube) :
    letI := Fp2_377.commRing (-5 : FpBLS377)
    ¬ ∃ z : Fp2_377, z ^ 3 = (⟨0, 1⟩ : Fp2_377) := by
  have hbase : ¬ ∃ w : FpBLS377, w ^ 3 = Fp2_377.norm (-5 : FpBLS377) ⟨0, 1⟩ := by
    rw [norm_u_eq_five]; exact h
  exact noncube_of_norm_noncube (-5) ⟨0, 1⟩ hbase

/-! ## 4. The tower leaves and the conditional field instances -/

/-- The `Fp6` non-residue leaf at the concrete parameters `ξ₂ = -5`, `ξ₆ = u`:
    the composite `Fp6 → Fp` norm form is anisotropic. Equivalent to `u` being a
    non-cube in `Fp2_377` (`x³ - u` irreducible over `Fp2`). Feeds
    `Fp6_377.isField (-5) u`. -/
abbrev Fp6NonResidueLeaf : Prop :=
  ∀ x : Fp6_377, x ≠ 0 →
    Fp2_377.norm (-5 : FpBLS377) (Fp6_377.normFp6 (-5) ⟨0, 1⟩ x) ≠ 0

/-- The `Fp12` non-residue leaf at the concrete parameters `ξ₂ = -5`, `ξ₆ = u`,
    `w² = v`: the full `Fp12 → Fp` norm form is anisotropic. Feeds
    `Fp12_377.isField (-5) u`. -/
abbrev Fp12NonResidueLeaf : Prop :=
  ∀ x : Fp12_377, x ≠ 0 →
    Fp2_377.norm (-5 : FpBLS377)
      (Fp6_377.normFp6 (-5) ⟨0, 1⟩ (Fp12_377.norm12 (-5) ⟨0, 1⟩ x)) ≠ 0

/-- The `Fp12` leaf follows from the `Fp6` leaf and `norm12` anisotropy: the
    outer form of the `Fp12` leaf is the `Fp6`-leaf predicate evaluated at
    `norm12 x`, so it suffices that `norm12 x ≠ 0` for `x ≠ 0` (i.e. `v` is a
    non-square in `Fp6`). -/
theorem fp12Leaf_of (h6 : Fp6NonResidueLeaf)
    (hv : ∀ x : Fp12_377, x ≠ 0 → Fp12_377.norm12 (-5 : FpBLS377) ⟨0, 1⟩ x ≠ 0) :
    Fp12NonResidueLeaf :=
  fun x hx => h6 (Fp12_377.norm12 (-5) ⟨0, 1⟩ x) (hv x hx)

/-- `Field Fp6_377` at the concrete parameters, given the `Fp6` non-residue leaf
    (`Fp6_377.isField` upgraded by `IsField.toField`). -/
noncomputable def fp6Field [Fact (Nat.Prime bls377Q)] (h : Fp6NonResidueLeaf) :
    letI := Fp6_377.commRing (-5 : FpBLS377) ⟨0, 1⟩
    Field Fp6_377 :=
  letI := Fp6_377.commRing (-5 : FpBLS377) ⟨0, 1⟩
  (Fp6_377.isField (-5) ⟨0, 1⟩ h).toField

/-- `Field Fp12_377` at the concrete parameters, given the `Fp12` non-residue
    leaf (`Fp12_377.isField` upgraded by `IsField.toField`). -/
noncomputable def fp12Field [Fact (Nat.Prime bls377Q)] (h : Fp12NonResidueLeaf) :
    letI := Fp12_377.commRing (-5 : FpBLS377) ⟨0, 1⟩
    Field Fp12_377 :=
  letI := Fp12_377.commRing (-5 : FpBLS377) ⟨0, 1⟩
  (Fp12_377.isField (-5) ⟨0, 1⟩ h).toField

end CatCrypt.Crypto.SecureCompilation.RelationalFront
