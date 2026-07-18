/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Generic short-Weierstrass (`a = 0`) inversion-free Jacobian group law

This module proves the projective→affine elliptic-curve group-law realization **once**,
over an abstract `[Field F]`, so every per-curve EC file (BLS12-377, Pallas, Vesta,
secp256k1, BN254, …) becomes a one-line instantiation rather than a copy of the same
`field_simp; ring` algebra at a fixed prime.

## The fractalyze-style parametric form

`RelationalFrontBls377EC.lean` (and its siblings) carry the `dbl-2009-l` / `add-2007-bl`
coordinate maps and their realization ties hand-inlined at one concrete base field
`ZMod bls377Q`.  The coordinate formulas are field-generic and `b`-agnostic — they are built
only from `*`/`+`/`−`/`⁻¹` and never mention the curve's prime, its `a` (`= 0` here) or its
`b`.  So the only thing the per-curve versions specialize is the field and the nonvanishing of
the small numerals `2, 3, 4, 8` introduced by `dbl-2009-l` and the tangent slope.

This file factors that out.  Over a section `variable {F : Type*} [Field F]` it gives:

* the affine point `ECAffPoint F` and the chord/tangent coordinate maps
  `ecAffineRx`/`ecAffineRy`/`ecAffineAdd`/`ecTangentSlope`/`ecAffineDbl`;
* the Jacobian point `ECJacPoint F` and the inversion-free projective group law
  `ECJacPoint.ofAffine`/`ecJacToAffine`/`ecJacDouble` (`dbl-2009-l`)/`ecJacAddZ1`
  (`add-2007-bl`, `Z = 1` mixed-add chart);
* the two realization ties
  `ec_jacDouble_realizes_affineDbl` and `ec_jacAdd_realizes_affineAdd`.

This is the **canonical parametric form** (`@canonical_parametric` — genuinely parametric over
the base field, as the curve carrier varies per protocol).  A new curve needs **no new EC
proof**: instantiate `@ec_jacDouble_realizes_affineDbl (ZMod p) _ …` and discharge the four
nonvanishing facts `(2,3,4,8 : ZMod p) ≠ 0`, which all follow from `p > 8` (Mathlib infers
`Field (ZMod p)` from `[Fact (Nat.Prime p)]`).  Every per-curve EC file is exactly such an
instance — see the witness at the foot of this module, instantiated at the tiny field
`ZMod 11`.

## The Jacobian group law (`a = 0`)

A Jacobian point `(X, Y, Z)` represents the affine point `(X·Z⁻², Y·Z⁻³)`.

**`dbl-2009-l`** (point double):
```
   S = 4·X·Y² ; M = 3·X² ; X' = M² − 2S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```
**`add-2007-bl`** (point add, `Z₁ = Z₂ = 1` mixed-add chart):
```
   H = X₂ − X₁ ; r = Y₂ − Y₁ ;
   X' = r² − H³ − 2·X₁·H² ; Y' = r·(X₁·H² − X') − Y₁·H³ ; Z' = H
```

## Scope

The ties are the **generic-chart** identities (`Z = 1`, distinct/doubling branches, nonzero
`y`), which hold by `field_simp; ring`.  The exceptional cases (vertical line / point at
infinity) and all-pairs group-law completeness are out of scope — exactly the generic-chart
scope of the per-curve versions.

0 sorries; no custom axioms; the field-algebra ties are unconditional given the field
structure plus the four numeral-nonvanishing hypotheses.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

universe u

variable {F : Type u} [Field F]

/-! ## 1. The affine point and the chord/tangent coordinate maps

The short-Weierstrass affine point-add (distinct points) and point-double (tangent)
coordinate formulas, written field-agnostically (built only from `*`/`+`/`−`/`⁻¹`). -/

/-- An affine `G1` point `(x, y)` over the abstract base field `F`. -/
structure ECAffPoint (F : Type u) where
  /-- Affine `x`-coordinate. -/
  x : F
  /-- Affine `y`-coordinate. -/
  y : F

/-- The short-Weierstrass affine point-add `x`-coordinate map: `x₃ = λ² − x₁ − x₂`. -/
def ecAffineRx (lam x1 x2 : F) : F := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map: `y₃ = λ·(x₁ − x₃) − y₁`. -/
def ecAffineRy (lam x1 x3 y1 : F) : F := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed chord slope `λ`. -/
def ecAffineAdd (lam : F) (P Q : ECAffPoint F) : ECAffPoint F :=
  let x3 := ecAffineRx lam P.x Q.x
  { x := x3, y := ecAffineRy lam P.x x3 P.y }

/-- The short-Weierstrass tangent slope at an affine point `(x, y)` on `y² = x³ + b`
    (`a = 0`): `λ = (3·x²)·(2·y)⁻¹`. -/
def ecTangentSlope (x y : F) : F := (3 * (x * x)) * (2 * y)⁻¹

/-- The full affine point-double coordinate formula, given the precomputed tangent slope `λ`.
    Reuses `ecAffineRx`/`ecAffineRy` with `x₂ = x₁ = x`. -/
def ecAffineDbl (lam : F) (P : ECAffPoint F) : ECAffPoint F :=
  let x3 := ecAffineRx lam P.x P.x
  { x := x3, y := ecAffineRy lam P.x x3 P.y }

/-! ## 2. The Jacobian point and the inversion-free projective group law

A Jacobian point `(X, Y, Z)` represents the affine point `(X·Z⁻², Y·Z⁻³)`.  The
`dbl-2009-l` / `add-2007-bl` formulas for `a = 0` compute the group law with **no inverse**
(only `*`/`+`/`−`); the single inverse is deferred to the final affine conversion
`ecJacToAffine`. -/

/-- A Jacobian projective `G1` point `(X, Y, Z)` over `F`.  Represents the affine point
    `(X·Z⁻², Y·Z⁻³)`; `Z = 0` is the point at infinity. -/
structure ECJacPoint (F : Type u) where
  /-- Jacobian `X`. -/
  X : F
  /-- Jacobian `Y`. -/
  Y : F
  /-- Jacobian `Z` (`Z = 0` ⇒ point at infinity). -/
  Z : F

/-- The affine-embedding of an affine point `(x, y)` as the Jacobian point `(x, y, 1)`. -/
def ECJacPoint.ofAffine (P : ECAffPoint F) : ECJacPoint F := { X := P.x, Y := P.y, Z := 1 }

/-- The **one-inverse** Jacobian→affine conversion `(X, Y, Z) ↦ (X·(Z²)⁻¹, Y·(Z³)⁻¹)`. -/
def ecJacToAffine (J : ECJacPoint F) : ECAffPoint F :=
  { x := J.X * (J.Z ^ 2)⁻¹, y := J.Y * (J.Z ^ 3)⁻¹ }

/-- The `dbl-2009-l` Jacobian point-double for `a = 0`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.** -/
def ecJacDouble (J : ECJacPoint F) : ECJacPoint F :=
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2
  let Xp := M ^ 2 - 2 * S
  { X := Xp, Y := M * (S - Xp) - 8 * J.Y ^ 4, Z := 2 * J.Y * J.Z }

/-- The `add-2007-bl` Jacobian point-add in the `Z = 1` chart (both inputs affine, the
    mixed-add form the windowed / Pippenger loops drive): `H = X₂ − X₁`, `r = Y₂ − Y₁`,
    `X' = r² − H³ − 2X₁H²`, `Y' = r·(X₁H² − X') − Y₁H³`, `Z' = H`.  **No inverse.** -/
def ecJacAddZ1 (J K : ECJacPoint F) : ECJacPoint F :=
  let H := K.X - J.X
  let r := K.Y - J.Y
  let Xp := r ^ 2 - H ^ 3 - 2 * J.X * H ^ 2
  { X := Xp, Y := r * (J.X * H ^ 2 - Xp) - J.Y * H ^ 3, Z := H }

/-! ## 3. The denote-tie to the affine group law (the correctness oracle)

`ecJacToAffine` of the projective double/add, on affine-embedded inputs, equals the affine
`ecAffineDbl`/`ecAffineAdd` at the same chord/tangent slope.  Pure field-algebra identities —
the projective accumulation computes the same group element, with the inverse amortized to the
final conversion. -/

set_option linter.unusedVariables false in
/-- **The projective double realizes the affine double.**  Converting the `dbl-2009-l`
    Jacobian double of the affine-embedded `(x, y)` back to affine (one inverse) yields
    exactly `ecAffineDbl` at the tangent slope — in the generic chart (`y ≠ 0`).  The four
    numeral-nonvanishing hypotheses hold in any field of characteristic `0` or `> 8` (e.g.
    `ZMod p` for any prime `p > 8`).  The four hypotheses are the stable per-curve interface:
    a new curve supplies exactly these (all consequences of `p > 8`), so they are part of the
    signature even where `field_simp` happens to consume only a subset. -/
theorem ec_jacDouble_realizes_affineDbl
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0) (h8 : (8 : F) ≠ 0)
    (P : ECAffPoint F) (hy : P.y ≠ 0) :
    ecJacToAffine (ecJacDouble (ECJacPoint.ofAffine P))
      = ecAffineDbl (ecTangentSlope P.x P.y) P := by
  obtain ⟨x, y⟩ := P
  refine ECAffPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [ecJacDouble, ECJacPoint.ofAffine, ecAffineRx, ecTangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring
  · simp only [ecJacDouble, ECJacPoint.ofAffine, ecAffineRx, ecAffineRy, ecTangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring

/-- **The projective add realizes the affine add (distinct points).**  Converting the
    `add-2007-bl` Jacobian add of two affine-embedded distinct points back to affine (one
    inverse) yields exactly `ecAffineAdd` at the chord slope — generic chart (`x₂ ≠ x₁`).
    No numeral hypotheses are needed: the add formula introduces none. -/
theorem ec_jacAdd_realizes_affineAdd
    (P Q : ECAffPoint F) (hx : Q.x - P.x ≠ 0) :
    ecJacToAffine (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q))
      = ecAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  refine ECAffPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [ecJacAddZ1, ECJacPoint.ofAffine, ecAffineRx]
    field_simp
    ring
  · simp only [ecJacAddZ1, ECJacPoint.ofAffine, ecAffineRx, ecAffineRy]
    field_simp
    ring

/-! ## 4. Consolidation witness: a per-curve file is a one-line instance

Every per-curve EC file specializes `F := ZMod p` for that curve's base-field prime `p` and
supplies the four numeral-nonvanishing facts (which follow from `p > 8`).  We witness the
genericity at the concrete field `ℚ` — where the numerals `2,3,4,8` are nonzero by `norm_num`
and the whole per-curve statement is recovered by `@`-instantiation with **no new algebra**.
The full per-curve modules (`RelationalFrontBls377EC.lean`, Pallas, Vesta, secp256k1, BN254)
instantiate the *same* two theorems at their own `ZMod p`; `ℚ` is used here only because it
carries a `Field` instance without a primality side-hypothesis, keeping the witness
self-contained. -/

section Witness

/-- A per-curve point-double realization at `ℚ`, obtained purely by instantiating the generic
    theorem — no `field_simp`/`ring` here.  This is the shape every per-curve EC file takes:
    `@ec_jacDouble_realizes_affineDbl (ZMod p) _ h2 h3 h4 h8`. -/
example (P : ECAffPoint ℚ) (hy : P.y ≠ 0) :
    ecJacToAffine (ecJacDouble (ECJacPoint.ofAffine P))
      = ecAffineDbl (ecTangentSlope P.x P.y) P :=
  @ec_jacDouble_realizes_affineDbl ℚ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) P hy

/-- A per-curve point-add realization at `ℚ`, again pure `@`-instantiation. -/
example (P Q : ECAffPoint ℚ) (hx : Q.x - P.x ≠ 0) :
    ecJacToAffine (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q))
      = ecAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q :=
  @ec_jacAdd_realizes_affineAdd ℚ _ P Q hx

end Witness

end CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
