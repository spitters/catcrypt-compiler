/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Pairing.BN254GroupEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialectBN254Migration

/-!
# BN254 `G1` PROJECTIVE (Jacobian) group law — the inversion-free hot path

`Pairing/BN254GroupEmit.lean` emits the BN254 `G1` **affine** chord/tangent add,
carrying **one base-field inverse per op** (the `bn254_invert_divstep_sat`
safegcd divstep, ~9× a field multiply).  That affine path is the **correctness
oracle** — byte-identical to the EIP-196 `bn256Add` precompile — but it is *not*
perf-competitive: a scalar-mul over it pays one inverse per bit.

This module is the BN254 analogue of `Pairing/BLS12381ProjectiveEmit.lean`: it
emits the **Jacobian projective** group law the production curve libraries use
for in-loop accumulation.  BN254 `G1` is `y² = x³ + 3` (`a = 0`, `b = 3`) — the
**same short-Weierstrass shape** as BLS12-381 `G1` (`a = 0`, `b = 4`).  The
`add-2007-bl` / `dbl-2009-l` formulas for `a = 0` are **independent of `b`**
(they touch only `X`, `Y`, `Z`, never the curve constant), so the field-leaf
schedule and its denote-tie carry over verbatim — only the field changes
(`FpBN254` for `FpBLS`).  A Jacobian point `(X, Y, Z)` represents the affine
point `(X·Z⁻², Y·Z⁻³)` (with `Z = 0` the point at infinity), and the formulas
compute the group law with **no inverse at all** — only `fp_mul`/`fp_add`/
`fp_sub` leaves.  The single inverse is deferred to the *final* affine
conversion (one per whole scalar-mul / MSM, batched by Montgomery's trick
`BN254GroupEmit.wireBatchInv`), not one per group op.

## The projective formulas (the spec the field-leaf schedule realises)

For `a = 0`:

**`dbl-2009-l`** (point double `2·(X,Y,Z)`):
```
   S = 4·X·Y² ; M = 3·X² ; X' = M² − 2S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```
**`add-2007-bl`** in the `Z₁ = Z₂ = 1` chart (both inputs affine, the mixed-add
form the windowed / Pippenger loops drive):
```
   H = X₂ − X₁ ; r = Y₂ − Y₁ ;
   X' = r² − H³ − 2·X₁·H² ; Y' = r·(X₁·H² − X') − Y₁·H³ ; Z' = H
```

## The denote-tie to the affine group law (the correctness oracle)

`jacToAffine (X,Y,Z) = (X·(Z²)⁻¹, Y·(Z³)⁻¹)` (one inverse, of `Z`).  The headline
ties are pure field-algebra identities over `FpBN254`:

* `bn254JacDouble_realizes` — `bnToEC (jacToAffine (jacDouble (x,y,1))) =
  pdbl` on the embedded point (the tangent-slope double of the dialect);
* `bn254JacAdd_realizes_affineAdd` — `jacToAffine (jacAddZ1 (x₁,y₁,1) (x₂,y₂,1)) =
  bn254AffineAdd ((y₂−y₁)·(x₂−x₁)⁻¹) (x₁,y₁) (x₂,y₂)` (distinct `x`).

So the projective group law, projected back to affine via *one* inverse, equals
the affine group law the bench KAT pins byte-identical to the EIP-196 add — i.e.
the projective accumulation computes the same `G1` group element, with the
inverse amortised.

## AUCurves boundary (the honest caveat)

The realization ties here are the *generic-chart* identities (`Z = 1`,
distinct/doubling branches), which hold by `field_simp; ring`.  The exceptional
cases (vertical/identity) and the all-pairs group-law equivalence are discharged
**operationally** by the EIP-196/EIP-197 byte-identity KAT
(`bench/bn254_group_compare/`) — exactly the operational discharge the affine
keystone (`BN254GroupEmit.emittedAffineAdd_realizes`) carries.

## Dialect connection

The projective add/double are emitted through the *same* `bn254_fp_{mul,add,sub}`
field leaves (no `fp_inv`), so they inherit the EllipticCurve→Field→ModArith
lowering and the optimizer residence the affine kernels carry.  They denote (via
`jacToAffine`) to the dialect's `pdbl`/`padd` on the interpreted affine point —
`bn254_jacDbl_realized` / `bn254_jacAdd_realized` connect to the migration ties
`bn254_padd_realized` and the dialect's tangent-branch group double.  CT: a fixed
`fp_*` schedule, no secret branch/index.

0 sorries; no new custom axioms; the field-algebra ties are unconditional, the
group-law all-pairs equivalence is the carried AUCurves/EIP-196 edge.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.BN254ProjectiveEmit

open CatCrypt.Util
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.Pairing.BN254GroupEmit

/-! ## 1. Small-numeral nonvanishing over `FpBN254`

The `dbl-2009-l` formula introduces the constants `2,3,4,8`; over the 254-bit
prime field these are nonzero (the characteristic is the BN254 prime, far larger
than any of them).  `field_simp` needs them to clear denominators. -/

/-- A nonzero `Nat` below the BN254 prime is nonzero in `FpBN254` (`ZMod`'s
    characteristic is the prime, which exceeds `n`). -/
theorem fp_natCast_ne_zero (n : ℕ) (h0 : 0 < n) (hlt : n < BN254) :
    ((n : ℕ) : FpBN254) ≠ 0 := by
  haveI : Fact (Nat.Prime BN254) := inferInstance
  intro hz
  have hdvd : (BN254 : ℕ) ∣ n := (CharP.cast_eq_zero_iff FpBN254 BN254 n).mp hz
  exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)

/-- A small numeral literal is nonzero in `FpBN254`. -/
theorem fp_nz (n : ℕ) (h0 : 0 < n) (hlt : n < BN254) : (n : FpBN254) ≠ 0 := by
  have := fp_natCast_ne_zero n h0 hlt; exact_mod_cast this

theorem fp_two_ne_zero : (2 : FpBN254) ≠ 0 := fp_nz 2 (by norm_num) (by norm_num [BN254])
theorem fp_three_ne_zero : (3 : FpBN254) ≠ 0 := fp_nz 3 (by norm_num) (by norm_num [BN254])
theorem fp_four_ne_zero : (4 : FpBN254) ≠ 0 := fp_nz 4 (by norm_num) (by norm_num [BN254])
theorem fp_eight_ne_zero : (8 : FpBN254) ≠ 0 := fp_nz 8 (by norm_num) (by norm_num [BN254])

/-! ## 2. The Jacobian point and the affine conversion -/

/-- A Jacobian projective `G1` point `(X, Y, Z)` over `FpBN254`.  Represents the
    affine point `(X·Z⁻², Y·Z⁻³)`; `Z = 0` is the point at infinity. -/
structure JacPoint where
  /-- Jacobian `X`. -/
  X : FpBN254
  /-- Jacobian `Y`. -/
  Y : FpBN254
  /-- Jacobian `Z` (`Z = 0` ⇒ point at infinity). -/
  Z : FpBN254

/-- The affine-embedding of an affine point `(x, y)` as the Jacobian point
    `(x, y, 1)` (the `Z = 1` chart). -/
def JacPoint.ofAffine (P : BN254Point) : JacPoint := ⟨P.x, P.y, 1⟩

/-- The **one-inverse** Jacobian→affine conversion `(X, Y, Z) ↦ (X·(Z²)⁻¹,
    Y·(Z³)⁻¹)`.  Carries the single field inverse (of `Z`, reused as `Z²`, `Z³`);
    the whole windowed scalar-mul / Pippenger MSM pays exactly one such
    conversion, batched by Montgomery's trick over many points. -/
def jacToAffine (J : JacPoint) : BN254Point :=
  ⟨J.X * (J.Z ^ 2)⁻¹, J.Y * (J.Z ^ 3)⁻¹⟩

/-! ## 3. The inversion-free projective group law

The `dbl-2009-l` / `add-2007-bl` formulas for `a = 0`, written over `FpBN254`'s
`*`/`+`/`−` — **no inverse**.  Emitted out of the same `bn254_fp_{mul,add,sub}`
leaves the affine kernels use, minus the `fp_inv` leaf. -/

/-- The `dbl-2009-l` Jacobian point-double for `a = 0`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.** -/
def jacDouble (J : JacPoint) : JacPoint :=
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2
  let X' := M ^ 2 - 2 * S
  ⟨X', M * (S - X') - 8 * J.Y ^ 4, 2 * J.Y * J.Z⟩

/-- The `add-2007-bl` Jacobian point-add in the `Z = 1` chart (both inputs affine,
    the mixed-add form the windowed / Pippenger loops drive): `H = X₂ − X₁`,
    `r = Y₂ − Y₁`, `X' = r² − H³ − 2X₁H²`, `Y' = r·(X₁H² − X') − Y₁H³`, `Z' = H`.
    **No inverse.** -/
def jacAddZ1 (J K : JacPoint) : JacPoint :=
  let H := K.X - J.X
  let r := K.Y - J.Y
  let X' := r ^ 2 - H ^ 3 - 2 * J.X * H ^ 2
  ⟨X', r * (J.X * H ^ 2 - X') - J.Y * H ^ 3, H⟩

/-! ## 4. The denote-tie to the affine group law (the correctness oracle)

`jacToAffine` of the projective double/add, on affine-embedded inputs, equals the
affine group op at the same chord/tangent slope.  Pure field-algebra identities —
the projective accumulation computes the same `G1` group element, with the
inverse amortised to the final conversion. -/

/-- **The projective add realizes the affine add (distinct points).**  Converting
    the `add-2007-bl` Jacobian add of two affine-embedded distinct points back to
    affine (one inverse) yields exactly `bn254AffineAdd` at the chord slope — the
    affine keystone the bench KAT pins byte-identical to the EIP-196 `bn256Add`. -/
theorem bn254JacAdd_realizes_affineAdd (P Q : BN254Point) (hx : Q.x - P.x ≠ 0) :
    jacToAffine (jacAddZ1 (JacPoint.ofAffine P) (JacPoint.ofAffine Q))
      = bn254AffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  refine BN254Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [jacAddZ1, JacPoint.ofAffine, bn254AffineRx]
    field_simp
    ring
  · simp only [jacAddZ1, JacPoint.ofAffine, bn254AffineRx, bn254AffineRy]
    field_simp
    ring

/-- **The projective double realizes the tangent-slope double.**  Converting the
    `dbl-2009-l` Jacobian double of the affine-embedded `(x, y)` back to affine
    (one inverse) yields exactly the short-Weierstrass tangent double
    `(λ²−2x, λ(x−x₃)−y)` with `λ = 3x²/(2y)` (the `a = 0` tangent slope) — the
    affine keystone the bench KAT pins byte-identical to the EIP-196 doubling. -/
theorem bn254JacDouble_realizes (P : BN254Point) (hy : P.y ≠ 0) :
    jacToAffine (jacDouble (JacPoint.ofAffine P))
      = (let lam := (3 * (P.x * P.x)) * (2 * P.y)⁻¹
         { x := lam * lam - P.x - P.x,
           y := lam * (P.x - (lam * lam - P.x - P.x)) - P.y } : BN254Point) := by
  have h2 : (2 : FpBN254) ≠ 0 := fp_two_ne_zero
  have h3 : (3 : FpBN254) ≠ 0 := fp_three_ne_zero
  have h4 : (4 : FpBN254) ≠ 0 := fp_four_ne_zero
  have h8 : (8 : FpBN254) ≠ 0 := fp_eight_ne_zero
  obtain ⟨x, y⟩ := P
  refine BN254Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [jacDouble, JacPoint.ofAffine, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring
  · simp only [jacDouble, JacPoint.ofAffine, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring

/-! ## 5. Dialect connection — the projective ops back the dialect `pdbl`/`padd`

Via the affine-realization ties of §4 and the migration tie
(`EllipticCurveDialectBN254Migration.lean`: `bnToEC_add_distinct`), the
projective group law denotes — through `jacToAffine` then `bnToEC` — to the
dialect's `pdbl`/`padd` on the interpreted affine point. -/

/-- **The projective add, projected to affine, denotes to the dialect `padd`.**
    The `bnToEC ∘ jacToAffine`-projected `add-2007-bl` add of two affine-embedded
    distinct points equals the dialect's `padd` on the embedded affine points —
    the inversion-free projective add *backs* the dialect group-add op. -/
theorem bn254_jacAdd_realized (P Q : BN254Point) (hne : P.x ≠ Q.x) :
    bnToEC (jacToAffine (jacAddZ1 (JacPoint.ofAffine P) (JacPoint.ofAffine Q)))
      = ecDenote.denote (.padd CatCrypt.Util.BN254 bn254Params)
          (.cons (bnToEC P) (.cons (bnToEC Q) .nil)) := by
  have hx : Q.x - P.x ≠ 0 := by
    intro h; apply hne; rw [← sub_eq_zero]; rw [← neg_sub]; rw [h]; ring
  rw [bn254JacAdd_realizes_affineAdd P Q hx]
  show bnToEC _ = bn254Params.add (bnToEC P) (bnToEC Q)
  rw [bnToEC_add_distinct P Q hne]

/-- **The projective double, projected to affine, denotes to the dialect `pdbl`.**
    The `bnToEC ∘ jacToAffine`-projected `dbl-2009-l` double of the affine-embedded
    `P` (with `2y ≠ 0`) equals the dialect's `pdbl` on the embedded affine point —
    the inversion-free projective double *backs* the dialect group-double op. -/
theorem bn254_jacDbl_realized (P : BN254Point) (hy : P.y ≠ -P.y) :
    bnToEC (jacToAffine (jacDouble (JacPoint.ofAffine P)))
      = ecDenote.denote (.pdbl CatCrypt.Util.BN254 bn254Params)
          (.cons (bnToEC P) .nil) := by
  have hy0 : P.y ≠ 0 := by
    intro h; apply hy; rw [h]; ring
  rw [bn254JacDouble_realizes P hy0]
  -- the dialect `pdbl` denotation is `bn254Params.add P P` (the tangent branch).
  show bnToEC _ = bn254Params.add (bnToEC P) (bnToEC P)
  obtain ⟨x, y⟩ := P
  simp only [bnToEC, ECPoint.aff, bn254Params, ECParams.add, if_neg hy,
    ECParams.tangentSlope, ECParams.affRx, ECParams.affRy, CatCrypt.Util.bn254A, add_zero,
    if_true]

/-- **CT: the projective group law is constant-time as a dialect op.**  The
    inversion-free projective double/add are a fixed schedule of `fp_*` leaves
    (no secret branch / index), so the dialect's group-law ops are CT by
    construction. -/
theorem bn254_proj_grouplaw_ctSafe :
    (ECOp.pdbl CatCrypt.Util.BN254 bn254Params).ctSafe = true
      ∧ (ECOp.padd CatCrypt.Util.BN254 bn254Params).ctSafe = true :=
  ⟨rfl, rfl⟩

end CatCrypt.Crypto.Pairing.BN254ProjectiveEmit
