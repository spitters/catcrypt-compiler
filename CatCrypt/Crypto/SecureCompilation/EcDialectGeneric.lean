/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import Mathlib.Algebra.Field.ZMod

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-!
# Generic relational-EC → EllipticCurve-dialect connection (`a = 0`, proved once)

Every per-curve EC-dialect file (`RelationalFrontBls377ECDialect.lean` and its
Pallas/Vesta/secp256k1/BN254 siblings) repeats the *same* proof: embed the bespoke
affine point into the dialect's `ECPoint p`, unfold the dialect's branchy
`ECParams.add` on the generic chart down to the bespoke chord/tangent coordinate
maps, then compose with the projective-realizes-affine ties to denote into the
dialect's `.padd`/`.pdbl`.  That proof is **field-generic** and depends on the curve
only through `params.a = 0` (the short-Weierstrass `a = 0` family the inversion-free
`dbl-2009-l` / `add-2007-bl` Jacobian law covers).

This module factors that connection out **once**, parametric over the prime `p` and a
curve `params : ECParams p` with `params.a = 0`, on top of the generic projective→affine
realization of
`EcRealizationGeneric.lean` (`ECAffPoint`/`ecJacDouble`/`ecJacAddZ1`/
`ec_jacDouble_realizes_affineDbl`/`ec_jacAdd_realizes_affineAdd`, instantiated at
`F = ZMod p`).  Each per-curve EC-dialect file then becomes a one-line
`@ec_jacDbl_realized p curveParams …` instance — a new `a = 0` curve connects to the
dialect with **no new proof**.

## The point embedding and the two dialect-add unfold lemmas

Under the structural embedding

    ecToEC : ECAffPoint (ZMod p) → ECPoint p   (`(x, y) ↦ some (x, y)`)

the generic affine ops map to the dialect's abstract group operation
`ECParams.add params`, scoped to the **generic chart**:

* `ecToEC_add_distinct` — for distinct `x`, `ECParams.add params` on two embedded
  points equals `ecToEC (ecAffineAdd (chord slope) P Q)`;
* `ecToEC_dbl` — for `y ≠ −y` (i.e. `2y ≠ 0`), `ECParams.add params P P` on the
  embedded point equals `ecToEC (ecAffineDbl (tangent slope) P)`.

Both are pure `simp only` definitional unfolds of the dialect's `ECParams.add` /
`chordSlope` / `tangentSlope` / `affRx` / `affRy` against the generic `ecAffineRx` /
`ecAffineRy` / `ecTangentSlope`.  The `tangentSlope` numerator `3·x² + a` collapses to
the generic `3·x²` via the hypothesis `ha : params.a = 0` (this is the *only* place the
curve enters — the formulas are otherwise `b`-agnostic).

## The two realization ties (the headline)

Composing the unfolds with the generic projective→affine ties:

* `ec_jacDbl_realized` — the `ecToEC`-transported projected `dbl-2009-l` double of the
  affine-embedded `P` (`2y ≠ 0`) denotes to the dialect's `.pdbl`;
* `ec_jacAdd_realized` — the `ecToEC`-transported projected `add-2007-bl` add of two
  distinct embedded points denotes to the dialect's `.padd`.

So the inversion-free projective Jacobian group law of `EcRealizationGeneric.lean`
*backs* the dialect's `padd`/`pdbl` on **every** `a = 0` short-Weierstrass curve over a
prime field, with the curve supplied only as `params` + `ha : params.a = 0` + the four
numeral-nonvanishing facts (all consequences of `p > 8`).

## Scope (caveat: the generic chart)

Exactly as the per-curve dialect ties: the connection is the **generic-chart** identity
(distinct points for `padd`; `2y ≠ 0` doubling for `pdbl`).  The exceptional cases
(vertical line / point at infinity) and the all-pairs group-law completeness are not
attempted here — they are the deep EC group theorem the generic MSM carries.

All goals closed; no custom axioms (the base-field structure is the section hypothesis
`[Fact (Nat.Prime p)]`, and `ha : params.a = 0` is a hypothesis on `params`, not an
asserted axiom).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcDialectGeneric

open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-! ## 1. The point embedding `ECAffPoint (ZMod p) → ECPoint p`

The structural map carrying the generic affine point into the dialect's abstract group
element (`(x, y) ↦ some (x, y)`), mirroring `RelationalFrontBls377ECDialect.bls377ToEC`. -/

variable {p : ℕ}

/-- Embed a generic affine `ECAffPoint (ZMod p)` into the EllipticCurve dialect's abstract
    group element (`(x, y) ↦ some (x, y)`). -/
def ecToEC (P : ECAffPoint (ZMod p)) : ECPoint p := ECPoint.aff P.x P.y

@[simp] theorem ecToEC_eq (P : ECAffPoint (ZMod p)) : ecToEC P = some (P.x, P.y) := rfl

/-! ## 2. The dialect group add/double on embedded generic-chart points

The dialect's `ECParams.add params` on an `a = 0` curve, restricted to the generic chart,
unfolds to the generic affine chord/tangent coordinate maps.  These require the base-field
structure (`Fact (Nat.Prime p)`) only to make `ZMod p` a field for the inverse in the
slope; the unfoldings themselves are definitional, plus `ha : params.a = 0` to collapse
the dialect's `3·x² + a` tangent numerator to the generic `3·x²`. -/

section Field

variable [Fact (Nat.Prime p)] (params : ECParams p)

/-- The dialect group add on two embedded **distinct** points equals the generic
    `ecAffineAdd` with the chord slope `(y₂ − y₁)·(x₂ − x₁)⁻¹`.  Mirrors
    `RelationalFrontBls377ECDialect.bls377ToEC_add_distinct`. -/
theorem ecToEC_add_distinct (P Q : ECAffPoint (ZMod p)) (hne : P.x ≠ Q.x) :
    params.add (ecToEC P) (ecToEC Q)
      = ecToEC (ecAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q) := by
  simp only [ecToEC, ECPoint.aff, ECParams.add, ite_eq_right hne,
    ECParams.chordSlope, ECParams.affRx, ECParams.affRy,
    ecAffineAdd, ecAffineRx, ecAffineRy]

/-- The dialect group double on an embedded point with `y ≠ −y` (so `2y ≠ 0`, doubling is
    defined) equals the generic `ecAffineDbl` with the tangent slope
    `ecTangentSlope x y` (the dialect's `3·x² + a` numerator collapses to the generic
    `3·x²` at `params.a = 0`).  Mirrors
    `RelationalFrontBls377ECDialect.bls377ToEC_dbl`. -/
theorem ecToEC_dbl (ha : params.a = 0) (P : ECAffPoint (ZMod p)) (hy : P.y ≠ -P.y) :
    params.add (ecToEC P) (ecToEC P)
      = ecToEC (ecAffineDbl (ecTangentSlope P.x P.y) P) := by
  simp only [ecToEC, ECPoint.aff, ECParams.add, ite_eq_left, ite_eq_right hy,
    ECParams.tangentSlope, ECParams.affRx, ECParams.affRy,
    ecAffineDbl, ecTangentSlope, ecAffineRx, ecAffineRy,
    ha, add_zero]

end Field

/-! ## 3. The projective ops, projected to affine, back the dialect `padd`/`pdbl`

Composing the projective-realizes-affine ties of §3 of `EcRealizationGeneric` with the
generic-chart dialect-add unfoldings of §2: the `ecToEC`-transported inversion-free
projective Jacobian double/add of the affine-embedded points equal the dialect's
`pdbl`/`padd` on the embedded points — so the inversion-free projective group law *backs*
the dialect group ops on **every** `a = 0` curve. -/

section Realization

variable [Fact (Nat.Prime p)] (params : ECParams p)

/-- **The projective double, projected to affine, denotes to the dialect `pdbl`.**
    The `ecJacToAffine`-projected `dbl-2009-l` double of the affine-embedded `P` (with
    `2y ≠ 0`, i.e. `y ≠ −y`) equals the dialect's `pdbl` on the embedded affine point —
    so the inversion-free projective double *backs* the `a = 0` dialect group-double op.
    Mirrors `RelationalFrontBls377ECDialect.bls377_jacDbl_realized`. -/
theorem ec_jacDbl_realized
    (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0) (h4 : (4 : ZMod p) ≠ 0)
    (h8 : (8 : ZMod p) ≠ 0) (ha : params.a = 0) (P : ECAffPoint (ZMod p)) (hy : P.y ≠ -P.y) :
    ecToEC (ecJacToAffine (ecJacDouble (ECJacPoint.ofAffine P)))
      = ecDenote.denote (.pdbl p params) (.cons (ecToEC P) .nil) := by
  have hy0 : P.y ≠ 0 := by
    intro h; apply hy; rw [h]; ring
  rw [ec_jacDouble_realizes_affineDbl h2 h3 h4 h8 P hy0]
  show ecToEC _ = params.add (ecToEC P) (ecToEC P)
  rw [ecToEC_dbl params ha P hy]

/-- **The projective add, projected to affine, denotes to the dialect `padd`.**
    The `ecJacToAffine`-projected `add-2007-bl` add of two affine-embedded **distinct**
    points equals the dialect's `padd` on the embedded affine points — so the
    inversion-free projective add *backs* the `a = 0` dialect group-add op.  Mirrors
    `RelationalFrontBls377ECDialect.bls377_jacAdd_realized`. -/
theorem ec_jacAdd_realized (P Q : ECAffPoint (ZMod p)) (hne : P.x ≠ Q.x) :
    ecToEC (ecJacToAffine
        (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q)))
      = ecDenote.denote (.padd p params)
          (.cons (ecToEC P) (.cons (ecToEC Q) .nil)) := by
  have hx : Q.x - P.x ≠ 0 := by
    intro h; apply hne; rw [← sub_eq_zero]; rw [← neg_sub]; rw [h]; ring
  rw [ec_jacAdd_realizes_affineAdd P Q hx]
  show ecToEC _ = params.add (ecToEC P) (ecToEC Q)
  rw [ecToEC_add_distinct params P Q hne]

end Realization

/-! ## 4. CT: the `a = 0` group law is constant-time as a dialect op

The inversion-free projective double/add are a fixed schedule of base-field `*`/`+`/`−`
leaves (no secret branch / index), so the dialect's group-law ops are CT by construction
— the same `ctSafe = true` flag the per-curve projective kernels carry, here once for
every curve. -/

/-- **CT: the `a = 0` projective group law is constant-time as a dialect op.**  The
    dialect's `padd`/`pdbl` on any `params` are `ctSafe` by construction (a fixed schedule
    of field ops, no secret-addressed access).  Mirrors
    `RelationalFrontBls377ECDialect.bls377_proj_grouplaw_ctSafe`. -/
theorem ec_proj_grouplaw_ctSafe (params : ECParams p) :
    (ECOp.pdbl p params).ctSafe = true
      ∧ (ECOp.padd p params).ctSafe = true :=
  ⟨rfl, rfl⟩

/-! ## 5. Consolidation witness: each per-curve EC-dialect file is a one-line instance

Every per-curve EC-dialect file (`RelationalFrontBls377ECDialect.lean`, and the Pallas /
Vesta / secp256k1 / BN254 siblings) is the `@ec_jacDbl_realized p curveParams …` /
`@ec_jacAdd_realized p curveParams …` instance of the generic ties above, supplying the
concrete prime `p`, the curve `params := ⟨0, b⟩` (so `ha : params.a = 0` is `rfl`), and
the four numeral-nonvanishing facts (consequences of `p > 8`).  We witness this at the
tiny `a = 0` curve `y² = x³ + 1` over `ZMod 11`: the double/add ties are recovered by
pure `@`-instantiation with **no new algebra**. -/

section Witness

/-- `11` is prime (the witness base field is `ZMod 11`), supplied as a local `Fact`
    instance so `ZMod 11` is a field — the per-curve files supply this for their own
    prime as a section hypothesis. -/
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The tiny `a = 0` witness curve `y² = x³ + 1` over `ZMod 11` (`a = 0`, `b = 1`). -/
def witnessCurve : ECParams 11 := ⟨0, 1⟩

/-- A per-curve point-double connection at `ZMod 11`, obtained purely by instantiating the
    generic tie — no `field_simp`/`simp only` algebra here.  This is the shape every
    per-curve EC-dialect file takes:
    `@ec_jacDbl_realized p curveParams h2 h3 h4 h8 rfl P hy`. -/
example (P : ECAffPoint (ZMod 11)) (hy : P.y ≠ -P.y) :
    ecToEC (ecJacToAffine (ecJacDouble (ECJacPoint.ofAffine P)))
      = ecDenote.denote (.pdbl 11 witnessCurve) (.cons (ecToEC P) .nil) :=
  ec_jacDbl_realized witnessCurve (by decide) (by decide) (by decide) (by decide) rfl P hy

/-- A per-curve point-add connection at `ZMod 11`, again pure `@`-instantiation. -/
example (P Q : ECAffPoint (ZMod 11)) (hne : P.x ≠ Q.x) :
    ecToEC (ecJacToAffine
        (ecJacAddZ1 (ECJacPoint.ofAffine P) (ECJacPoint.ofAffine Q)))
      = ecDenote.denote (.padd 11 witnessCurve)
          (.cons (ecToEC P) (.cons (ecToEC Q) .nil)) :=
  ec_jacAdd_realized witnessCurve P Q hne

end Witness

end CatCrypt.Crypto.SecureCompilation.EcDialectGeneric
