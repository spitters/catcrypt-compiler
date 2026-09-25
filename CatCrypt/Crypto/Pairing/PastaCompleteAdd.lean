/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.PallasPrimeCert
public import CatCrypt.Crypto.Util.VestaPrimeCert
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontPallas
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontVesta

/-!
# The complete addition law of `y² = x³ + b`, and the Pasta curves

The Pasta curves Pallas and Vesta are `y² = x³ + 5` over the primes `pallasQ` and
`vestaQ`. This file proves that the complete projective addition of Renes, Costello and
Batina for `a = 0` (their Algorithm 7, `b₃ = 3b`) computes the group law of Mathlib's
`WeierstrassCurve.Affine.Point` on every pair of points, identity and doubling included,
whenever `x³ + b` has no root and `2 ≠ 0`, and it discharges both hypotheses for the two
Pasta base fields.

## Main definitions

* `w0 b` — the curve `y² = x³ + b` as a Mathlib `WeierstrassCurve`.
* `rcb0Add b P Q` — the complete addition on coordinate triples.
* `ProjRep0 b t A` — the triple `t` represents the point `A` projectively.

## Main results

* `rcb0Add_projRep` — on representations of `A` and `B`, `rcb0Add` returns a
  representation of `A + B`.
* `pallas_cubic_no_root`, `vesta_cubic_no_root` — `x³ + 5` has no root modulo `pallasQ`
  and modulo `vestaQ`: with `p − 1 = 3m`, a root `r` would give `(−5)^m = r^(p−1) = 1`,
  and `powMod (p − 5) m p ≠ 1` is checked by kernel evaluation.

The chord, tangent and inverse cases follow the `a = −3` development of the P-256
hash-to-curve suite (`rcbAdd_projRep`) with the `a = 0` formula.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.PastaCompleteAdd

section Rcb0

variable {K : Type} [Field K]

/-- The closed form of `rcb0Add b (x₁, y₁, 1) (x₂, y₂, 1)`. -/
def rcb0Aff (b x1 y1 x2 y2 : K) : K × K × K :=
  ((x1 * y2 + y1 * x2) * (y1 * y2 - 3 * b) - 3 * b * (y1 + y2) * (x1 + x2),
    (y1 * y2 + 3 * b) * (y1 * y2 - 3 * b) + 9 * b * (x1 * x2) * (x1 + x2),
    (y1 + y2) * (y1 * y2 + 3 * b) + 3 * (x1 * x2) * (x1 * y2 + y1 * x2))

/-- The third intersection of `y² = x³ + b` with the line of slope `s` through
`(x₁, y₁)` and `(x₂, y₂)` lies on the curve. -/
theorem chord_on_curve0 {b x1 y1 x2 y2 s : K}
    (e1 : y1 ^ 2 = x1 ^ 3 + b) (e2 : y2 ^ 2 = x2 ^ 3 + b)
    (hs : y2 = y1 + s * (x2 - x1)) (hx : x1 ≠ x2) :
    (s ^ 2 - x1 - x2) ^ 3 + b = (s * ((s ^ 2 - x1 - x2) - x1) + y1) ^ 2 := by
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  apply mul_left_cancel₀ hd
  subst hs
  linear_combination (x2 - (s ^ 2 - x1 - x2)) * e1 + (s ^ 2 - x1 - x2 - x1) * e2

/-- On two affine points with distinct abscissae, the formula returns the projective
representation of the chord sum, with nonzero third coordinate. -/
theorem rcb0Aff_chord {b x1 y1 x2 y2 : K} (hb : ∀ x : K, x ^ 3 + b ≠ 0)
    (e1 : y1 ^ 2 = x1 ^ 3 + b) (e2 : y2 ^ 2 = x2 ^ 3 + b) (hx : x1 ≠ x2) :
    (rcb0Aff b x1 y1 x2 y2).2.2 ≠ 0 ∧
      (rcb0Aff b x1 y1 x2 y2).1
        = (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) * (rcb0Aff b x1 y1 x2 y2).2.2 ∧
      (rcb0Aff b x1 y1 x2 y2).2.1
        = -((y1 - y2) / (x1 - x2) * ((((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) - x1) + y1)
          * (rcb0Aff b x1 y1 x2 y2).2.2 := by
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  simp only [rcb0Aff]
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hS : (y1 + y2) * ((y1 + y2) ^ 2 - (2 * x1 + x2) * (x1 - x2) ^ 2)
        + y1 * (x1 - x2) ^ 3 = 0 := by
      linear_combination hz + (y1 + 2 * y2) * e1 + (2 * y1 + y2) * e2
    apply hb (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2)
    have hw : (y1 + y2) / (x1 - x2) * ((((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) - x1) + y1
        = 0 := by
      field_simp
      linear_combination hS
    have ht : (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) ^ 3 + b
        = ((y1 + y2) / (x1 - x2) * ((((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) - x1) + y1) ^ 2 :=
      chord_on_curve0 (y2 := -y2) e1 (by rw [neg_sq]; exact e2)
        (by field_simp; ring) hx
    rw [ht, hw]; ring
  · field_simp
    grind
  · field_simp
    grind

/-- The third intersection of `y² = x³ + b` with the tangent of slope `s` at `(x, y)` lies
on the curve. -/
theorem tangent_on_curve0 {b x y s : K} (e : y ^ 2 = x ^ 3 + b)
    (hs : 2 * y * s = 3 * x ^ 2) :
    (s ^ 2 - x - x) ^ 3 + b = (s * ((s ^ 2 - x - x) - x) + y) ^ 2 := by
  linear_combination (-1 : K) * e - (s ^ 2 - x - x - x) * hs

/-- On an affine point with nonzero ordinate added to itself, the formula returns the
projective representation of the tangent sum, with nonzero third coordinate. -/
theorem rcb0Aff_tangent {b x y : K} (h2 : (2 : K) ≠ 0)
    (e : y ^ 2 = x ^ 3 + b) (hy : y ≠ 0) :
    (rcb0Aff b x y x y).2.2 ≠ 0 ∧
      (rcb0Aff b x y x y).1
        = (((3 * x ^ 2) / (2 * y)) ^ 2 - x - x) * (rcb0Aff b x y x y).2.2 ∧
      (rcb0Aff b x y x y).2.1
        = -((3 * x ^ 2) / (2 * y) * ((((3 * x ^ 2) / (2 * y)) ^ 2 - x - x) - x) + y)
          * (rcb0Aff b x y x y).2.2 := by
  have hz : (rcb0Aff b x y x y).2.2 = 8 * y ^ 3 := by
    simp only [rcb0Aff]; linear_combination (-6 * y) * e
  rw [hz]
  refine ⟨?_, ?_, ?_⟩
  · have h8 : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [h8]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) (pow_ne_zero 3 hy)
  · simp only [rcb0Aff]; field_simp; grind
  · simp only [rcb0Aff]; field_simp; grind

/-- On an affine point and its negative, the formula returns a representation of the
point at infinity. -/
theorem rcb0Aff_neg {b x y : K} (hb : ∀ x : K, x ^ 3 + b ≠ 0) (h2 : (2 : K) ≠ 0)
    (e : y ^ 2 = x ^ 3 + b) :
    (rcb0Aff b x y x (-y)).2.2 = 0 ∧ (rcb0Aff b x y x (-y)).1 = 0 ∧
      (rcb0Aff b x y x (-y)).2.1 ≠ 0 := by
  have hy : y ≠ 0 := by
    rintro rfl; exact hb x (by linear_combination -e)
  refine ⟨by simp only [rcb0Aff]; ring, by simp only [rcb0Aff]; ring, ?_⟩
  intro h0
  have hD : (3 * x ^ 2) * ((3 * x ^ 2) ^ 2 - 12 * x * y ^ 2) + 8 * y ^ 4 = 0 := by
    simp only [rcb0Aff] at h0; grind
  have h2y : 2 * y ≠ 0 := mul_ne_zero h2 hy
  apply hb (((3 * x ^ 2) / (2 * y)) ^ 2 - x - x)
  rw [tangent_on_curve0 e (by field_simp)]
  have hw : (3 * x ^ 2) / (2 * y) * ((((3 * x ^ 2) / (2 * y)) ^ 2 - x - x) - x) + y
      = 0 := by
    field_simp; linear_combination hD
  rw [hw]; ring

/-- The short Weierstrass curve `y² = x³ + b` as a Mathlib `WeierstrassCurve`. -/
def w0 (b : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := b

/-- The complete projective addition of Renes, Costello and Batina for `a = 0`: the
closed form of their Algorithm 7, with `b₃ = 3b`. -/
def rcb0Add (b : K) (P Q : K × K × K) : K × K × K :=
  let X1 := P.1
  let Y1 := P.2.1
  let Z1 := P.2.2
  let X2 := Q.1
  let Y2 := Q.2.1
  let Z2 := Q.2.2
  ((X1 * Y2 + Y1 * X2) * (Y1 * Y2 - 3 * b * (Z1 * Z2))
      - 3 * b * (Y1 * Z2 + Z1 * Y2) * (X1 * Z2 + Z1 * X2),
    (Y1 * Y2 + 3 * b * (Z1 * Z2)) * (Y1 * Y2 - 3 * b * (Z1 * Z2))
      + 9 * b * (X1 * X2) * (X1 * Z2 + Z1 * X2),
    (Y1 * Z2 + Z1 * Y2) * (Y1 * Y2 + 3 * b * (Z1 * Z2))
      + 3 * (X1 * X2) * (X1 * Y2 + Y1 * X2))

/-- A coordinate triple scaled by `c`. -/
def sc0 (c : K) (t : K × K × K) : K × K × K := (c * t.1, c * t.2.1, c * t.2.2)

/-- `rcb0Add` is homogeneous of degree two in each argument. -/
theorem rcb0Add_sc (b l m : K) (P Q : K × K × K) :
    rcb0Add b (sc0 l P) (sc0 m Q) = sc0 ((l * m) ^ 2) (rcb0Add b P Q) := by
  obtain ⟨X1, Y1, Z1⟩ := P
  obtain ⟨X2, Y2, Z2⟩ := Q
  simp only [rcb0Add, sc0, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- `rcb0Add` on two triples with third coordinate `1` is `rcb0Aff`. -/
theorem rcb0Add_one (b x1 y1 x2 y2 : K) :
    rcb0Add b (x1, y1, 1) (x2, y2, 1) = rcb0Aff b x1 y1 x2 y2 := by
  simp only [rcb0Add, rcb0Aff, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- `rcb0Add` of the point at infinity and an affine triple. -/
theorem rcb0Add_inf_left (b x y : K) :
    rcb0Add b (0, 1, 0) (x, y, 1) = (x * y, y ^ 2, y) := by
  simp only [rcb0Add, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- `rcb0Add` of an affine triple and the point at infinity. -/
theorem rcb0Add_inf_right (b x y : K) :
    rcb0Add b (x, y, 1) (0, 1, 0) = (x * y, y ^ 2, y) := by
  simp only [rcb0Add, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- `rcb0Add` of the point at infinity with itself. -/
theorem rcb0Add_inf_inf (b : K) : rcb0Add b (0, 1, 0) (0, 1, 0) = (0, 1, 0) := by
  simp only [rcb0Add, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The triple `(X, Y, Z)` represents the point `A` of `y² = x³ + b` projectively:
`Z = 0 = X` and `Y ≠ 0` for the point at infinity, and `Z ≠ 0`, `X = xZ`, `Y = yZ` for
the affine point `(x, y)`. -/
def ProjRep0 (b : K) (t : K × K × K) : (w0 b).toAffine.Point → Prop
  | .zero => t.2.2 = 0 ∧ t.1 = 0 ∧ t.2.1 ≠ 0
  | .some x y _ => t.2.2 ≠ 0 ∧ t.1 = x * t.2.2 ∧ t.2.1 = y * t.2.2

/-- The normalized triple of a point: `(0, 1, 0)` for the point at infinity and
`(x, y, 1)` for the affine point `(x, y)`. -/
def ptTriple0 (b : K) : (w0 b).toAffine.Point → K × K × K
  | .zero => (0, 1, 0)
  | .some x y _ => (x, y, 1)

/-- A representation of `A` is a nonzero multiple of the normalized triple of `A`. -/
theorem ProjRep0.eq_sc {b : K} {t : K × K × K} {A : (w0 b).toAffine.Point}
    (h : ProjRep0 b t A) : ∃ c, c ≠ 0 ∧ t = sc0 c (ptTriple0 b A) := by
  obtain ⟨X, Y, Z⟩ := t
  cases A with
  | zero =>
    obtain ⟨hz, hx, hy⟩ := h
    exact ⟨Y, hy, by simp_all [sc0, ptTriple0]⟩
  | some x y _ =>
    obtain ⟨hz, hx, hy⟩ := h
    exact ⟨Z, hz, by simp_all [sc0, ptTriple0, mul_comm]⟩

/-- A nonzero multiple of a representation of `A` represents `A`. -/
theorem projRep0_sc {b c : K} {t : K × K × K} {A : (w0 b).toAffine.Point} (hc : c ≠ 0)
    (h : ProjRep0 b t A) : ProjRep0 b (sc0 c t) A := by
  cases A with
  | zero =>
    obtain ⟨hz, hx, hy⟩ := h
    exact ⟨by simp [sc0, hz], by simp [sc0, hx], by simp [sc0, hc, hy]⟩
  | some x y _ =>
    obtain ⟨hz, hx, hy⟩ := h
    refine ⟨by simp [sc0, hc, hz], ?_, ?_⟩
    · simp only [sc0]; rw [hx]; ring
    · simp only [sc0]; rw [hy]; ring

/-- A nonsingular point of `w0 b` satisfies `y² = x³ + b`. -/
theorem w0_equation {b x y : K} (h : (w0 b).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + b := by
  have := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at this
  simp only [w0] at this
  linear_combination this

/-- When `x³ + b` has no root and `2 ≠ 0`, every solution of `y² = x³ + b` is a
nonsingular point of `w0 b`. -/
theorem w0_nonsingular {b x y : K} (hb : ∀ x : K, x ^ 3 + b ≠ 0) (h2 : (2 : K) ≠ 0)
    (e : y ^ 2 = x ^ 3 + b) : (w0 b).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
  refine ⟨by simp only [w0]; linear_combination e, Or.inr ?_⟩
  simp only [w0]
  intro h
  have hy : y = 0 := by
    have h' : 2 * y = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  apply hb x
  rw [hy] at e
  linear_combination -e

variable [DecidableEq K]

/-- `rcb0Add` on the normalized triples of two points represents their sum in the
Mathlib group law of `w0 b`, when `x³ + b` has no root and `2 ≠ 0`. -/
theorem rcb0Add_ptTriple {b : K} (hb : ∀ x : K, x ^ 3 + b ≠ 0) (h2 : (2 : K) ≠ 0)
    (A B : (w0 b).toAffine.Point) :
    ProjRep0 b (rcb0Add b (ptTriple0 b A) (ptTriple0 b B)) (A + B) := by
  have z0 : (WeierstrassCurve.Affine.Point.zero : (w0 b).toAffine.Point) = 0 := rfl
  cases A with
  | zero =>
    cases B with
    | zero =>
      rw [z0, zero_add]
      simp only [ptTriple0, rcb0Add_inf_inf]
      exact ⟨rfl, rfl, one_ne_zero⟩
    | some x y h =>
      rw [z0, zero_add]
      simp only [ptTriple0, rcb0Add_inf_left]
      have e := w0_equation h
      have hy : y ≠ 0 := by rintro rfl; exact hb x (by linear_combination -e)
      exact ⟨hy, rfl, by ring⟩
  | some x1 y1 h1 =>
    cases B with
    | zero =>
      rw [z0, add_zero]
      simp only [ptTriple0, rcb0Add_inf_right]
      have e := w0_equation h1
      have hy : y1 ≠ 0 := by rintro rfl; exact hb x1 (by linear_combination -e)
      exact ⟨hy, rfl, by ring⟩
    | some x2 y2 h2' =>
      have e1 := w0_equation h1
      have e2 := w0_equation h2'
      simp only [ptTriple0, rcb0Add_one]
      by_cases hx : x1 = x2
      · by_cases hy : y1 = (w0 b).toAffine.negY x2 y2
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          have hy' : y1 = -y2 := by
            rw [hy]; simp [WeierstrassCurve.Affine.negY, w0]
          subst hx
          have hy2 : y2 = -y1 := by rw [hy']; ring
          rw [hy2]
          exact rcb0Aff_neg hb h2 e1
        · have hyy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h1.1 h2'.1 hx hy
          rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy]
          subst hx hyy
          have hy0 : y1 ≠ 0 := by
            intro h0; apply hy; simp [WeierstrassCurve.Affine.negY, w0, h0]
          obtain ⟨t1, t2, t3⟩ := rcb0Aff_tangent h2 e1 hy0
          refine ⟨t1, ?_, ?_⟩
          · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, t2]
            simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, w0]
            congr 1; congr 2; ring
          · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, t3]
            simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
              WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, w0]
            congr 1
            have hs : (3 * x1 ^ 2 + 2 * 0 * x1 + 0 - 0 * y1) / (y1 - (-y1 - 0 * x1 - 0))
                = (3 * x1 ^ 2) / (2 * y1) := by congr 1 <;> ring
            rw [hs]; ring
      · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        obtain ⟨t1, t2, t3⟩ := rcb0Aff_chord hb e1 e2 hx
        refine ⟨t1, ?_, ?_⟩
        · rw [WeierstrassCurve.Affine.slope_of_X_ne hx, t2]
          simp only [WeierstrassCurve.Affine.addX, w0]
          ring
        · rw [WeierstrassCurve.Affine.slope_of_X_ne hx, t3]
          simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
            WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, w0]
          ring

/-- **The complete addition computes the group law.** On representations of `A` and `B`,
`rcb0Add b` returns a representation of `A + B` in the Mathlib group law of `w0 b`, for
every pair of points, when `x³ + b` has no root and `2 ≠ 0`. -/
theorem rcb0Add_projRep {b : K} (hb : ∀ x : K, x ^ 3 + b ≠ 0) (h2 : (2 : K) ≠ 0)
    {P Q : K × K × K} {A B : (w0 b).toAffine.Point} (hP : ProjRep0 b P A)
    (hQ : ProjRep0 b Q B) : ProjRep0 b (rcb0Add b P Q) (A + B) := by
  obtain ⟨c, hc, rfl⟩ := hP.eq_sc
  obtain ⟨d, hd, rfl⟩ := hQ.eq_sc
  rw [rcb0Add_sc]
  exact projRep0_sc (pow_ne_zero 2 (mul_ne_zero hc hd)) (rcb0Add_ptTriple hb h2 A B)

end Rcb0

/-! ## The Pasta base fields: `x³ + 5` has no root -/

section Pasta

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-- If `p − 1 = 3m` and `c^m ≢ 1 (mod p)`, then `c` is not a cube modulo the prime `p`. -/
theorem no_cube_root_of_powMod {p : ℕ} [hp : Fact p.Prime] (c m : ℕ) (hm : p - 1 = 3 * m)
    (hc0 : (c : ZMod p) ≠ 0) (hc : powMod c m p ≠ 1) :
    ∀ x : ZMod p, x ^ 3 ≠ (c : ZMod p) := by
  intro x hx
  have hx0 : x ≠ 0 := by rintro rfl; apply hc0; rw [← hx]; ring
  have h1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  rw [hm, pow_mul, hx, ← powMod_cast] at h1
  have hlt : powMod c m p < p := powMod_lt c m p hp.out.pos
  have h1' : ((powMod c m p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by rw [h1]; simp
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt hp.out.one_lt] at h1'
  exact hc h1'

/-- A positive numeral below `p` is nonzero in `ZMod p`. -/
theorem natCast_ne_zero_of_lt {p n : ℕ} (h0 : 0 < n) (hlt : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

/-- `x³ + 5` has no root modulo the prime `p` when `p − 1 = 3m`, `5 < p` and
`(p − 5)^m ≢ 1 (mod p)`. -/
theorem cubic5_no_root {p : ℕ} [Fact p.Prime] (m : ℕ) (hm : p - 1 = 3 * m) (h5 : 5 < p)
    (hc : powMod (p - 5) m p ≠ 1) : ∀ x : ZMod p, x ^ 3 + 5 ≠ 0 := by
  have hcast : ((p - 5 : ℕ) : ZMod p) = -5 := by
    rw [Nat.cast_sub h5.le, ZMod.natCast_self]; norm_num
  have h5' : ((5 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) h5
  intro x hx
  refine no_cube_root_of_powMod (p - 5) m hm ?_ hc x ?_
  · rw [hcast]; exact neg_ne_zero.mpr (by exact_mod_cast h5')
  · rw [hcast]; linear_combination hx

/-- `Nat.Prime pallasQ`, by the Lucas certificate `PallasPrimeCert.pallaslit_prime`. -/
theorem pallasQ_prime : Nat.Prime pallasQ :=
  CatCrypt.Crypto.Util.PallasPrimeCert.pallaslit_prime

/-- `Nat.Prime vestaQ`, by the Lucas certificate `VestaPrimeCert.vestalit_prime`. -/
theorem vestaQ_prime : Nat.Prime vestaQ :=
  CatCrypt.Crypto.Util.VestaPrimeCert.vestalit_prime

/-- The primality of `pallasQ` as an instance, for the field structure of `ZMod pallasQ`. -/
scoped instance fact_pallasQ_prime : Fact (Nat.Prime pallasQ) := ⟨pallasQ_prime⟩

/-- The primality of `vestaQ` as an instance, for the field structure of `ZMod vestaQ`. -/
scoped instance fact_vestaQ_prime : Fact (Nat.Prime vestaQ) := ⟨vestaQ_prime⟩

/-- `x³ + 5` has no root modulo `pallasQ`: Pallas has no point of order two. -/
theorem pallas_cubic_no_root : ∀ x : ZMod pallasQ, x ^ 3 + 5 ≠ 0 :=
  cubic5_no_root ((pallasQ - 1) / 3) (by unfold pallasQ; norm_num) (by unfold pallasQ; norm_num)
    (by decide +kernel)

/-- `x³ + 5` has no root modulo `vestaQ`: Vesta has no point of order two. -/
theorem vesta_cubic_no_root : ∀ x : ZMod vestaQ, x ^ 3 + 5 ≠ 0 :=
  cubic5_no_root ((vestaQ - 1) / 3) (by unfold vestaQ; norm_num) (by unfold vestaQ; norm_num)
    (by decide +kernel)

/-- `2 ≠ 0` in `ZMod pallasQ`. -/
theorem pallasQ_two_ne_zero : (2 : ZMod pallasQ) ≠ 0 := by
  exact_mod_cast natCast_ne_zero_of_lt (p := pallasQ) (n := 2) (by norm_num)
    (by unfold pallasQ; norm_num)

/-- `2 ≠ 0` in `ZMod vestaQ`. -/
theorem vestaQ_two_ne_zero : (2 : ZMod vestaQ) ≠ 0 := by
  exact_mod_cast natCast_ne_zero_of_lt (p := vestaQ) (n := 2) (by norm_num)
    (by unfold vestaQ; norm_num)

end Pasta

end CatCrypt.Crypto.Pairing.PastaCompleteAdd
