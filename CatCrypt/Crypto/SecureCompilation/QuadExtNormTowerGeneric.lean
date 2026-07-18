/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.QuadExtConjGeneric

/-!
# Generic norm-tower for `QuadExt K = K[u]/(u² − ξ)` — multiplicativity and composition

`QuadExtConjGeneric` gives the generic quadratic-extension norm
`norm ξ x = (x · conj x).c0 = c0² − ξ·c1²` and proves it lands in the base ring
and is multiplicative (`norm_mul`). This module adds the **norm-tower** layer:
the unit/zero/base values of the norm, its packaging as a `MonoidHom`, and the
**two-level composition** `norm_K (norm_outer x)` that contracts a `2`-level
tower `QuadExt (QuadExt K)` all the way down to the base ring `K`.

This is the foundation of pairing **final-exponentiation** norm chains: the
`bls12_377` `Fp12 → Fp6 → Fp2 → Fp` norm cascade is iterated application of the
single-level `QuadExt` norm at the quadratic steps, and the multiplicativity of
the composed norm is exactly what this module establishes generically.

## What this module proves

* unit/zero/base values: `norm_one`, `norm_zero`, `norm_ofBase` (the norm of a
  base element `ofBase a` is `a²`);
* `norm` packaged as a **multiplicative monoid homomorphism**
  `normMonoidHom : QuadExt K →* K` (carrying `norm_one`, `norm_mul`);
* the **two-level tower contraction** `normTower ξ ζ` from
  `QuadExt (QuadExt K)` to `K`, `x ↦ norm ξ (norm ζ x)`, with its
  multiplicativity `normTower_mul` and unit value `normTower_one`, packaged as a
  `MonoidHom` `normTowerMonoidHom`. This is the `2`-level instance of the
  full pairing norm chain; deeper towers iterate the same composition.

## Honesty boundary

This is the abstract algebra only — the multiplicativity and composition of the
generic `QuadExt` norm. As in `QuadExtConjGeneric`, the inner `commRing`
instance makes `QuadExt K` a `CommRing` (so `QuadExt (QuadExt K)` is again a
`CommRing` and the outer norm is well-typed); we do **not** wire any of this down
to an emitted base kernel — that lift is per-instantiation and deliberately out
of scope here, to keep the generic core focused and sorry-free.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.QuadExtGeneric

namespace QuadExt

variable {K : Type*}

/-! ## 1. Unit, zero, and base values of the norm

The norm sends `1 ↦ 1`, `0 ↦ 0`, and a base-ring element `ofBase a ↦ a²`. All
three are direct evaluations of the closed form `norm ξ x = c0² − ξ·c1²`. -/

/-- **The norm fixes `1`** (`norm ξ 1 = 1`): `1` is `⟨1, 0⟩`, so
    `norm ξ 1 = 1·1 − 0·0·ξ = 1`. -/
theorem norm_one [CommRing K] (ξ : K) :
    letI := commRing ξ
    norm ξ (1 : QuadExt K) = 1 := by
  letI := commRing ξ
  rw [norm_eq]
  simp

/-- **The norm sends `0` to `0`** (`norm ξ 0 = 0`). -/
theorem norm_zero [CommRing K] (ξ : K) :
    letI := commRing ξ
    norm ξ (0 : QuadExt K) = 0 := by
  letI := commRing ξ
  rw [norm_eq]
  simp

/-- **The norm of a base element is its square** (`norm ξ (ofBase a) = a²`):
    `ofBase a = ⟨a, 0⟩`, so `norm ξ (ofBase a) = a·a − 0·0·ξ = a²`. This is the
    quadratic-extension degree showing up — `[QuadExt K : K] = 2`, so the norm of
    a base scalar is `a^[QuadExt K : K] = a²`. -/
theorem norm_ofBase [CommRing K] (ξ a : K) :
    norm ξ (ofBase a) = a ^ 2 := by
  rw [norm_eq]
  simp [ofBase]
  ring

/-! ## 2. The norm as a multiplicative monoid homomorphism `QuadExt K →* K`

Bundling `norm_one` and `norm_mul` packages the norm as a `MonoidHom` from the
multiplicative monoid of `QuadExt K` (under the `commRing ξ` product) to the base
ring `K`. This is the categorical phrasing of "the norm is multiplicative". -/

/-- **The norm as a multiplicative monoid homomorphism** `QuadExt K →* K`, over
    the `commRing ξ` multiplicative structure. Its `toFun` is `norm ξ`,
    `map_one'` is `norm_one`, and `map_mul'` is `norm_mul`. -/
def normMonoidHom [CommRing K] (ξ : K) :
    letI := commRing ξ
    QuadExt K →* K :=
  letI := commRing ξ
  { toFun := norm ξ
    map_one' := norm_one ξ
    map_mul' := fun x y => norm_mul ξ x y }

@[simp] theorem normMonoidHom_apply [CommRing K] (ξ : K) (x : QuadExt K) :
    letI := commRing ξ
    normMonoidHom ξ x = norm ξ x := rfl

/-! ## 3. The two-level tower contraction `QuadExt (QuadExt K) → K`

With the inner `commRing ζ` instance, `QuadExt K` is itself a `CommRing`, so
`QuadExt (QuadExt K)` is a quadratic extension over it for an outer nonresidue
`ξ : QuadExt K`. Its norm lands in `QuadExt K`; composing with the inner norm
`norm ζ` contracts all the way to the base ring `K`. This is the `2`-level step
of a final-exponentiation norm chain. -/

/-- **The two-level tower norm** `QuadExt (QuadExt K) → K`,
    `x ↦ norm ζ (norm ξ x)`: take the norm of `x : QuadExt (QuadExt K)` down to
    `QuadExt K` (outer nonresidue `ξ : QuadExt K`), then the inner norm down to
    `K` (inner nonresidue `ζ : K`). The `bls12_377` `Fp12 → Fp6 → Fp2`-style
    quadratic legs of a pairing norm chain instantiate this. -/
def normTower [CommRing K] (ζ : K) (ξ : QuadExt K) :
    letI := commRing ζ
    QuadExt (QuadExt K) → K :=
  letI := commRing ζ
  fun x => norm ζ (norm ξ x)

@[simp] theorem normTower_apply [CommRing K] (ζ : K) (ξ : QuadExt K)
    (x : QuadExt (QuadExt K)) :
    letI := commRing ζ
    normTower ζ ξ x = norm ζ (norm ξ x) := rfl

/-- **The two-level tower norm is multiplicative**
    (`normTower ζ ξ (x * y) = normTower ζ ξ x * normTower ζ ξ y`): each level's
    norm is multiplicative (`norm_mul`), so the composition is too. This is the
    multiplicativity that a composed final-exponentiation norm chain relies on. -/
theorem normTower_mul [CommRing K] (ζ : K) (ξ : QuadExt K) :
    letI := commRing ζ
    letI := commRing ξ
    ∀ x y : QuadExt (QuadExt K),
      normTower ζ ξ (x * y) = normTower ζ ξ x * normTower ζ ξ y := by
  letI := commRing ζ
  letI := commRing ξ
  intro x y
  show norm ζ (norm ξ (x * y)) = norm ζ (norm ξ x) * norm ζ (norm ξ y)
  rw [norm_mul ξ x y, norm_mul ζ (norm ξ x) (norm ξ y)]

/-- **The two-level tower norm fixes `1`** (`normTower ζ ξ 1 = 1`): both levels
    send `1 ↦ 1` (`norm_one`). -/
theorem normTower_one [CommRing K] (ζ : K) (ξ : QuadExt K) :
    letI := commRing ζ
    letI := commRing ξ
    normTower ζ ξ (1 : QuadExt (QuadExt K)) = 1 := by
  letI := commRing ζ
  letI := commRing ξ
  show norm ζ (norm ξ (1 : QuadExt (QuadExt K))) = 1
  rw [norm_one ξ, norm_one ζ]

/-- **The two-level tower norm as a multiplicative monoid homomorphism**
    `QuadExt (QuadExt K) →* K`, over the inner/outer `commRing` products. Bundles
    `normTower_one` and `normTower_mul` — the categorical statement that a
    `2`-level pairing norm chain is multiplicative. -/
def normTowerMonoidHom [CommRing K] (ζ : K) (ξ : QuadExt K) :
    letI := commRing ζ
    letI := commRing ξ
    QuadExt (QuadExt K) →* K :=
  letI := commRing ζ
  letI := commRing ξ
  { toFun := normTower ζ ξ
    map_one' := normTower_one ζ ξ
    map_mul' := fun x y => normTower_mul ζ ξ x y }

@[simp] theorem normTowerMonoidHom_apply [CommRing K] (ζ : K) (ξ : QuadExt K)
    (x : QuadExt (QuadExt K)) :
    letI := commRing ζ
    letI := commRing ξ
    normTowerMonoidHom ζ ξ x = norm ζ (norm ξ x) := rfl

/-- **The two-level tower norm factors as the composition of the two single-level
    norm homomorphisms** (`normTowerMonoidHom ζ ξ = normMonoidHom ζ ∘ normMonoidHom ξ`):
    the `2`-level pairing norm chain is exactly the composite of the per-level
    `QuadExt` norm `MonoidHom`s. This is the homomorphism-level statement of the
    tower contraction, from which `normTower_mul`/`normTower_one` are corollaries
    (here re-derived, since the bundle wraps the same `norm ζ ∘ norm ξ`). -/
theorem normTowerMonoidHom_eq_comp [CommRing K] (ζ : K) (ξ : QuadExt K) :
    letI := commRing ζ
    letI := commRing ξ
    normTowerMonoidHom ζ ξ = (normMonoidHom ζ).comp (normMonoidHom ξ) := by
  letI := commRing ζ
  letI := commRing ξ
  rfl

end QuadExt

end CatCrypt.Crypto.SecureCompilation.QuadExtGeneric
