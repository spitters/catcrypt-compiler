/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.Ed25519Spec

/-!
# Ed25519 optimization correctness

Four optimizations of the Ed25519 reference implementation, each stated over
the edwards25519 group `EdPt` of `Ed25519Spec`:

| # | Optimization | Rocq theorem |
|---|---|---|
| 1 | Niels-form precomputed addition | `m1add_precomputed_coordinates_correct` |
| 2 | Readdition with a cached point | `readd_correct` |
| 3 | Addition-chain compilation | `compile_inv` + `exp_by_squaring_correct` |
| 4 | Scalar-field verify path | `sign_verify_correct_25519` |

The Niels-form mixed addition and the readdition are the affine formulas of
their Rocq counterparts; on the Niels and cached forms of a group element they
compute group addition (`ed_madd_niels_eq_add`, `ed_readd_eq_add`). Windowed
fixed-base scalar multiplication folds these mixed additions over a radix-16
digit vector and computes `k·B` (`windowed_eq_direct`). The only axioms used
are the field and scalar interpretation axioms of `Ed25519Spec`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Ed25519Optimizations

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Jasmin.Ed25519
open CatCrypt.Crypto.Jasmin.Ed25519Spec
open CatCrypt.Util (P25519)
open CatCrypt.Crypto.Jasmin.Ed25519Group (EdPt ed25519Curve)
open CatCrypt.Crypto.Jasmin.EdwardsCurve (OnCurveAff EdwardsPointAff)

/-! ## 1. Niels-form precomputed-table addition

Per `Crypto/Curves/Edwards/XYZT/Precomputed.v:31`, a precomputed point
is `(½(y+x), ½(y−x), x·y·d)`. The mixed addition of a group element and a
precomputed point uses the numerators `(y₁+x₁)·½(y₂+x₂) ∓ (y₁−x₁)·½(y₂−x₂)`
and the denominators `1 ± x₁·y₁·(x₂·y₂·d)`; on the Niels form of `Q` these are
the numerators and denominators of the unified addition of `P` and `Q`
(`madd_xy_niels_of`), so the mixed addition is group addition
(`ed_madd_niels_eq_add`). -/

/-- A precomputed Edwards point in Niels form. -/
structure NielsPt where
  /-- `½(y + x)`. -/
  yPlusX : ZMod P25519
  /-- `½(y − x)`. -/
  yMinusX : ZMod P25519
  /-- `x·y·d`. -/
  xyd : ZMod P25519

/-- The Niels form `(½(y+x), ½(y−x), x·y·d)` of a group element. -/
noncomputable def niels_of (P : EdPt) : NielsPt :=
  ⟨(P.y + P.x) / 2, (P.y - P.x) / 2, P.x * P.y * ed25519Curve.d⟩

open Classical in
/-- The group element `(½(y+x) − ½(y−x), ½(y+x) + ½(y−x))` of a Niels-form triple
    when that point lies on the curve, and the identity otherwise. -/
noncomputable def niels_to_pt (N : NielsPt) : EdPt :=
  if h : OnCurveAff ed25519Curve (N.yPlusX - N.yMinusX) (N.yPlusX + N.yMinusX) then
    ⟨N.yPlusX - N.yMinusX, N.yPlusX + N.yMinusX, h⟩
  else 0

/-- The Niels form of a group element lifts back to that element. -/
theorem niels_roundtrip (P : EdPt) : niels_to_pt (niels_of P) = P := by
  have h2 : (2 : ZMod P25519) ≠ 0 := ed25519Curve.two_ne_zero
  have hx : (P.y + P.x) / 2 - (P.y - P.x) / 2 = P.x := by field_simp; ring
  have hy : (P.y + P.x) / 2 + (P.y - P.x) / 2 = P.y := by field_simp; ring
  have hon : OnCurveAff ed25519Curve ((P.y + P.x) / 2 - (P.y - P.x) / 2)
      ((P.y + P.x) / 2 + (P.y - P.x) / 2) := by
    rw [hx, hy]; exact P.on_curve
  unfold niels_to_pt niels_of
  rw [dif_pos hon]
  exact EdwardsPointAff.ext_aff hx hy

/-- The affine coordinates of the Niels-form mixed addition of `P` and `N`. -/
noncomputable def madd_xy (P : EdPt) (N : NielsPt) : ZMod P25519 × ZMod P25519 :=
  (((P.y + P.x) * N.yPlusX - (P.y - P.x) * N.yMinusX) / (1 + P.x * P.y * N.xyd),
   ((P.y + P.x) * N.yPlusX + (P.y - P.x) * N.yMinusX) / (1 - P.x * P.y * N.xyd))

/-- On the Niels form of `Q`, the mixed-addition coordinates are the unified
    addition coordinates of `P` and `Q`. -/
theorem madd_xy_niels_of (P Q : EdPt) :
    madd_xy P (niels_of Q) = EdwardsPointAff.add_xy ed25519Curve P.x P.y Q.x Q.y := by
  have h2 : (2 : ZMod P25519) ≠ 0 := ed25519Curve.two_ne_zero
  have ha : ed25519Curve.a = -1 := rfl
  refine Prod.ext ?_ ?_
  · show ((P.y + P.x) * ((Q.y + Q.x) / 2) - (P.y - P.x) * ((Q.y - Q.x) / 2)) /
        (1 + P.x * P.y * (Q.x * Q.y * ed25519Curve.d)) =
      (P.x * Q.y + Q.x * P.y) / (1 + ed25519Curve.d * P.x * Q.x * P.y * Q.y)
    congr 1
    · field_simp; ring
    · ring
  · show ((P.y + P.x) * ((Q.y + Q.x) / 2) + (P.y - P.x) * ((Q.y - Q.x) / 2)) /
        (1 - P.x * P.y * (Q.x * Q.y * ed25519Curve.d)) =
      (P.y * Q.y - ed25519Curve.a * P.x * Q.x) / (1 - ed25519Curve.d * P.x * Q.x * P.y * Q.y)
    rw [ha]
    congr 1
    · field_simp; ring
    · ring

open Classical in
/-- Mixed addition `EdPt + NielsPt → EdPt` by the Niels-form formula `madd_xy`,
    returning the identity when the formula leaves the curve. -/
noncomputable def ed_madd_niels (P : EdPt) (N : NielsPt) : EdPt :=
  if h : OnCurveAff ed25519Curve (madd_xy P N).1 (madd_xy P N).2 then
    ⟨(madd_xy P N).1, (madd_xy P N).2, h⟩
  else 0

/-- Mixed addition with the Niels form of `Q` is group addition of `Q`. -/
theorem ed_madd_niels_eq_add (P Q : EdPt) : ed_madd_niels P (niels_of Q) = ed_add P Q := by
  have e := madd_xy_niels_of P Q
  have hon : OnCurveAff ed25519Curve (madd_xy P (niels_of Q)).1 (madd_xy P (niels_of Q)).2 := by
    rw [e]; exact (P + Q).on_curve
  unfold ed_madd_niels
  rw [dif_pos hon]
  exact EdwardsPointAff.ext_aff (by show (madd_xy P (niels_of Q)).1 = _; rw [e]; rfl)
    (by show (madd_xy P (niels_of Q)).2 = _; rw [e]; rfl)

/-- On a Niels-form triple that is the Niels form of its lift, mixed addition
    is group addition of the lift. -/
theorem ed_madd_niels_correct (P : EdPt) (N : NielsPt) (hN : niels_of (niels_to_pt N) = N) :
    ed_madd_niels P N = ed_add P (niels_to_pt N) := by
  rw [← hN, ed_madd_niels_eq_add, niels_roundtrip]

/-- Associativity of `ed_add`. -/
theorem ed_add_assoc (A B C : EdPt) :
    ed_add (ed_add A B) C = ed_add A (ed_add B C) :=
  add_assoc A B C

/-- Niels-form mixed addition after a scalar sum: `(a+b)·P + Q = a·P + (b·P + Q)`. -/
theorem ed_madd_niels_smul_distrib (a b : FpL25519) (P Q : EdPt) :
    ed_madd_niels (ed_smul (scalar_add a b) P) (niels_of Q)
      = ed_add (ed_smul a P) (ed_add (ed_smul b P) Q) := by
  rw [ed_madd_niels_eq_add, ed_smul_distrib_add, ed_add_assoc]

/-- Two Niels-form mixed additions in sequence add the sum of the two points. -/
theorem ed_madd_niels_chain (P Q1 Q2 : EdPt) :
    ed_madd_niels (ed_madd_niels P (niels_of Q1)) (niels_of Q2)
      = ed_add P (ed_add Q1 Q2) := by
  rw [ed_madd_niels_eq_add, ed_madd_niels_eq_add, ed_add_assoc]

/-! ## 2. Readdition with a cached point

Per `Crypto/Curves/Edwards/XYZT/Readdition.v:43`, a cached point stores
`(Y+X, Y−X, Z, T·2d)` of an extended-coordinate point. With `Z = 1` the cached
form of `(x, y)` is `(y+x, y−x, 1, 2d·x·y)`, and the readdition formula has
numerators `(y₁+x₁)·(Y₂+X₂) ∓ (y₁−x₁)·(Y₂−X₂)` and denominators
`2·Z₂ ± x₁·y₁·(2d·T₂)`. -/

/-- A cached point `(Y+X, Y−X, Z, 2d·T)`. -/
structure CachedPt where
  /-- `Y + X`. -/
  yPlusX : ZMod P25519
  /-- `Y − X`. -/
  yMinusX : ZMod P25519
  /-- `Z`. -/
  z : ZMod P25519
  /-- `2d·T`. -/
  t2d : ZMod P25519

/-- The cached form `(y+x, y−x, 1, 2d·x·y)` of a group element. -/
def cached_of (P : EdPt) : CachedPt :=
  ⟨P.y + P.x, P.y - P.x, 1, 2 * ed25519Curve.d * (P.x * P.y)⟩

open Classical in
/-- The group element `((Y+X) − (Y−X), (Y+X) + (Y−X)) / (2Z)` of a cached point
    when that point lies on the curve, and the identity otherwise. -/
noncomputable def cached_to_pt (C : CachedPt) : EdPt :=
  if h : OnCurveAff ed25519Curve ((C.yPlusX - C.yMinusX) / (2 * C.z))
      ((C.yPlusX + C.yMinusX) / (2 * C.z)) then
    ⟨(C.yPlusX - C.yMinusX) / (2 * C.z), (C.yPlusX + C.yMinusX) / (2 * C.z), h⟩
  else 0

/-- The cached form of a group element lifts back to that element. -/
theorem cached_roundtrip (P : EdPt) : cached_to_pt (cached_of P) = P := by
  have h2 : (2 : ZMod P25519) ≠ 0 := ed25519Curve.two_ne_zero
  have hx : (P.y + P.x - (P.y - P.x)) / (2 * 1) = P.x := by field_simp; ring
  have hy : (P.y + P.x + (P.y - P.x)) / (2 * 1) = P.y := by field_simp; ring
  have hon : OnCurveAff ed25519Curve ((P.y + P.x - (P.y - P.x)) / (2 * 1))
      ((P.y + P.x + (P.y - P.x)) / (2 * 1)) := by
    rw [hx, hy]; exact P.on_curve
  unfold cached_to_pt cached_of
  rw [dif_pos hon]
  exact EdwardsPointAff.ext_aff hx hy

/-- The affine coordinates of the readdition of `P` and the cached point `C`. -/
noncomputable def readd_xy (P : EdPt) (C : CachedPt) : ZMod P25519 × ZMod P25519 :=
  (((P.y + P.x) * C.yPlusX - (P.y - P.x) * C.yMinusX) / (2 * C.z + P.x * P.y * C.t2d),
   ((P.y + P.x) * C.yPlusX + (P.y - P.x) * C.yMinusX) / (2 * C.z - P.x * P.y * C.t2d))

/-- On the cached form of `Q`, the readdition coordinates are the unified
    addition coordinates of `P` and `Q`. -/
theorem readd_xy_cached_of (P Q : EdPt) :
    readd_xy P (cached_of Q) = EdwardsPointAff.add_xy ed25519Curve P.x P.y Q.x Q.y := by
  have h2 : (2 : ZMod P25519) ≠ 0 := ed25519Curve.two_ne_zero
  have ha : ed25519Curve.a = -1 := rfl
  refine Prod.ext ?_ ?_
  · show ((P.y + P.x) * (Q.y + Q.x) - (P.y - P.x) * (Q.y - Q.x)) /
        (2 * 1 + P.x * P.y * (2 * ed25519Curve.d * (Q.x * Q.y))) =
      (P.x * Q.y + Q.x * P.y) / (1 + ed25519Curve.d * P.x * Q.x * P.y * Q.y)
    rw [show (P.y + P.x) * (Q.y + Q.x) - (P.y - P.x) * (Q.y - Q.x)
          = 2 * (P.x * Q.y + Q.x * P.y) by ring,
      show 2 * 1 + P.x * P.y * (2 * ed25519Curve.d * (Q.x * Q.y))
          = 2 * (1 + ed25519Curve.d * P.x * Q.x * P.y * Q.y) by ring,
      mul_div_mul_left _ _ h2]
  · show ((P.y + P.x) * (Q.y + Q.x) + (P.y - P.x) * (Q.y - Q.x)) /
        (2 * 1 - P.x * P.y * (2 * ed25519Curve.d * (Q.x * Q.y))) =
      (P.y * Q.y - ed25519Curve.a * P.x * Q.x) / (1 - ed25519Curve.d * P.x * Q.x * P.y * Q.y)
    rw [ha, show (P.y + P.x) * (Q.y + Q.x) + (P.y - P.x) * (Q.y - Q.x)
          = 2 * (P.y * Q.y - (-1) * P.x * Q.x) by ring,
      show 2 * 1 - P.x * P.y * (2 * ed25519Curve.d * (Q.x * Q.y))
          = 2 * (1 - ed25519Curve.d * P.x * Q.x * P.y * Q.y) by ring,
      mul_div_mul_left _ _ h2]

open Classical in
/-- Readdition `EdPt + CachedPt → EdPt` by the formula `readd_xy`, returning the
    identity when the formula leaves the curve. -/
noncomputable def ed_readd (P : EdPt) (C : CachedPt) : EdPt :=
  if h : OnCurveAff ed25519Curve (readd_xy P C).1 (readd_xy P C).2 then
    ⟨(readd_xy P C).1, (readd_xy P C).2, h⟩
  else 0

/-- Readdition with the cached form of `Q` is group addition of `Q`. -/
theorem ed_readd_eq_add (P Q : EdPt) : ed_readd P (cached_of Q) = ed_add P Q := by
  have e := readd_xy_cached_of P Q
  have hon : OnCurveAff ed25519Curve (readd_xy P (cached_of Q)).1
      (readd_xy P (cached_of Q)).2 := by
    rw [e]; exact (P + Q).on_curve
  unfold ed_readd
  rw [dif_pos hon]
  exact EdwardsPointAff.ext_aff (by show (readd_xy P (cached_of Q)).1 = _; rw [e]; rfl)
    (by show (readd_xy P (cached_of Q)).2 = _; rw [e]; rfl)

/-- On a cached point that is the cached form of its lift, readdition is group
    addition of the lift. -/
theorem ed_readd_correct (P : EdPt) (C : CachedPt) (hC : cached_of (cached_to_pt C) = C) :
    ed_readd P C = ed_add P (cached_to_pt C) := by
  rw [← hC, ed_readd_eq_add, cached_roundtrip]

/-- Batch readdition: two readditions in sequence add the sum of the two points. -/
theorem ed_readd_batch (P Q R : EdPt) :
    ed_readd (ed_readd P (cached_of Q)) (cached_of R)
      = ed_add P (ed_add Q R) := by
  rw [ed_readd_eq_add, ed_readd_eq_add, ed_add_assoc]

/-! ## 3. Addition-chain compilation correctness

Per `Crypto/Bedrock/Group/AdditionChains.v:626`, the Bedrock2 compilation
of `F.inv` via `exp_by_squaring` is correct: the compiled program
implements the abstract field inverse.

The Lean side sees the chain-correctness axiom `interp_fp_inv_pow`; the
characterization `fp_inv x = x⁻¹` follows from it by Fermat's little
theorem. -/

/-- The abstract Fermat exponent `(p-2)` evaluation. Concrete fact:
    `(interp_fe x)^(p-2) = (interp_fe x)⁻¹` whenever `interp_fe x ≠ 0`,
    by Fermat's little theorem in `ZMod p`. -/
theorem fermat_inv (x : Fp25519) (hx : interp_fe x ≠ 0) :
    (interp_fe x) ^ (fpModulus - 2) = (interp_fe x)⁻¹ := by
  -- For a prime p and nonzero x in ZMod p: x^(p-1) = 1, so x^(p-2) = x⁻¹.
  have hp : fpModulus - 2 + 1 = fpModulus - 1 := by
    unfold fpModulus; decide
  have h_pminus1 : (interp_fe x) ^ (fpModulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (p := fpModulus) hx
  have h_pminus2 : (interp_fe x) ^ (fpModulus - 2) * interp_fe x = 1 := by
    calc (interp_fe x) ^ (fpModulus - 2) * interp_fe x
        = (interp_fe x) ^ ((fpModulus - 2) + 1) := by ring
      _ = (interp_fe x) ^ (fpModulus - 1) := by rw [hp]
      _ = 1 := h_pminus1
  -- From `x^(p-2) * x = 1` and `x ≠ 0`, conclude `x^(p-2) = x⁻¹`.
  field_simp
  linear_combination h_pminus2

/-- The field inverse `fp_inv z` evaluates to `z^(p-2)` (the Fermat exponent),
    the statement of `interp_fp_inv_pow`. The corresponding Rocq result for the
    254-sqr + 11-mul addition chain is `fe_inv_correct` at
    `fiat-crypto/src/Bedrock/Group/AdditionChains.v:626`. -/
theorem fp_inv_via_chain (z : Fp25519) :
    interp_fe (fp_inv z) = (interp_fe z) ^ (fpModulus - 2) :=
  interp_fp_inv_pow z

/-- The field inverse `fp_inv x` evaluates to `(interp_fe x)⁻¹` for nonzero
    `x`, from `fp_inv_via_chain` and Fermat's little theorem. -/
theorem interp_fp_inv_from_chain (x : Fp25519) (hx : interp_fe x ≠ 0) :
    interp_fe (fp_inv x) = (interp_fe x)⁻¹ := by
  rw [fp_inv_via_chain]
  exact fermat_inv x hx

/-! ## 4. Scalar-field Bedrock2 verify path

Per `AUCurves/src/Spec/XEdDSA_Curve25519.v:107`, the Curve25519-specific
sign/verify equation is proved correct. Our `sign_verify_equation` proves
the abstract version; this section stitches in the curve-specific
specialization. -/

/-- **Proved.** Cited Rocq: `sign_verify_correct_25519` at
    `AUCurves/src/Spec/XEdDSA_Curve25519.v:107`. The Curve25519-specialized
    version of `sign_verify_equation`. The `M` parameter is unused at
    the algebraic level (the message contributes only via `interp s` /
    the precondition `h_s`), but kept in the signature for parity with
    the Rocq statement which passes it through.

    Since our abstract `sign_verify_equation` already proves the exact
    same conclusion under the same hypothesis, the curve-specialized
    form is just `sign_verify_equation` re-applied. -/
theorem sign_verify_correct_25519
    (a r k : FpL25519) (_M : ByteBuf)
    (s : FpL25519)
    (h_s : interp s = interp r + interp k * interp a) :
    ed_smul s ed_B
      = ed_add (ed_smul r ed_B) (ed_smul k (ed_smul a ed_B)) :=
  sign_verify_equation r a k s h_s

/-- **Proved.** `sign_verify_correct_25519` *is* `sign_verify_equation`
    by definition. The two statements are interchangeable in any
    downstream proof. -/
theorem sign_verify_curve25519_eq_abstract
    (a r k s : FpL25519) (M : ByteBuf)
    (h_s : interp s = interp r + interp k * interp a) :
    sign_verify_correct_25519 a r k M s h_s =
      sign_verify_equation r a k s h_s := by
  rfl

/-! ## 5. Windowed fixed-base scalar multiplication

A scalar is decomposed into 64 radix-16 digits `dᵢ`; the table entry of window
`i` for digit `d` is `(d·16^i)·B`, and the windowed scalar multiplication adds
the 64 selected entries, each in Niels form with one mixed addition. -/

/-- A radix-16 digit vector: 64 integer digits `dᵢ`. -/
abbrev Radix16Digits : Type := Fin 64 → ℤ

/-- The scalar `Σ dᵢ·16^i` of a digit vector, in `ZMod L`. Any integer digits are
    accepted, including the signed digits `dᵢ ∈ [−8, 8]` of the recoded form. -/
def radix16_recompose (d : Radix16Digits) : ZMod L :=
  ∑ i, (d i : ZMod L) * 16 ^ (i : ℕ)

/-- The unsigned radix-16 digits `dᵢ = ⌊n / 16^i⌋ mod 16` of the canonical residue
    `n` of `interp k`. -/
noncomputable def radix16_decompose (k : FpL25519) : Radix16Digits :=
  fun i => (((interp k).val / 16 ^ (i : ℕ)) % 16 : ℕ)

/-- The first `m` radix-16 digits of `n` recompose to `n mod 16^m`. -/
theorem sum_radix16_digits (n : ℕ) : ∀ m : ℕ,
    ∑ i ∈ Finset.range m, (n / 16 ^ i % 16) * 16 ^ i = n % 16 ^ m
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_radix16_digits n m, Nat.mod_pow_succ]
    ring

/-- Decomposing a scalar into radix-16 digits and recomposing them gives its
    interpretation in `ZMod L`. -/
theorem radix16_roundtrip (k : FpL25519) :
    radix16_recompose (radix16_decompose k) = interp k := by
  have hlt : (interp k).val < 16 ^ 64 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by unfold L; norm_num)
  have hsum := sum_radix16_digits (interp k).val 64
  rw [Nat.mod_eq_of_lt hlt] at hsum
  unfold radix16_recompose radix16_decompose
  conv_rhs => rw [← ZMod.natCast_zmod_val (interp k), ← hsum]
  push_cast
  exact Fin.sum_univ_eq_sum_range
    (fun i => (((interp k).val / 16 ^ i % 16 : ℕ) : ZMod L) * 16 ^ i) 64

/-- The table entry of window `i` for digit `d`: `(d·16^i)·B`. -/
noncomputable def windowTableEntry (i : Fin 64) (d : ℤ) : EdPt :=
  lsmul ((d : ZMod L) * 16 ^ (i : ℕ)) ed_B

/-- Windowed fixed-base scalar multiplication: starting from the identity, add the
    table entry of each of the 64 windows in Niels form by one mixed addition. -/
noncomputable def windowed_scalarmult_base (digits : Radix16Digits) : EdPt :=
  (List.finRange 64).foldl
    (fun acc i => ed_madd_niels acc (niels_of (windowTableEntry i (digits i)))) ed_identity

/-- A run of windowed mixed additions adds the scalar multiple of `B` by the sum of
    the windows' contributions. -/
theorem foldl_madd_table (digits : Radix16Digits) : ∀ (l : List (Fin 64)) (acc : EdPt),
    l.foldl (fun acc i => ed_madd_niels acc (niels_of (windowTableEntry i (digits i)))) acc
      = acc + lsmul (l.map (fun i => (digits i : ZMod L) * 16 ^ (i : ℕ))).sum ed_B
  | [], acc => by simp [lsmul_zero]
  | i :: l, acc => by
    rw [List.foldl_cons, foldl_madd_table digits l, ed_madd_niels_eq_add, List.map_cons,
      List.sum_cons, lsmul_add, ed_add_eq, windowTableEntry, add_assoc]

/-- The windowed scalar multiplication computes `k·B` for the recomposed scalar `k`
    of its digits. -/
theorem windowed_scalarmult_base_correct (digits : Radix16Digits) :
    windowed_scalarmult_base digits = lsmul (radix16_recompose digits) ed_B := by
  rw [windowed_scalarmult_base, foldl_madd_table, ed_identity_eq, zero_add,
    radix16_recompose, Fin.sum_univ_def]

/-- Windowed scalar multiplication on the radix-16 digits of `k` is `k·B`. -/
theorem windowed_eq_direct (k : FpL25519) :
    windowed_scalarmult_base (radix16_decompose k) = ed_smul k ed_B := by
  rw [windowed_scalarmult_base_correct, radix16_roundtrip]
  rfl

/-- The composite optimization (Niels-form table + radix-16 decomposition) used in
    `ed_sign_fast` computes `a·B`. -/
theorem ed_sign_fast_scalarmult_correct (a : FpL25519) :
    windowed_scalarmult_base (radix16_decompose a) = ed_smul a ed_B :=
  windowed_eq_direct a

/-! ## 6. Group-theoretic chains -/

/-- Three Niels-form mixed additions in sequence. -/
theorem ed_madd_niels_three (P Q1 Q2 Q3 : EdPt) :
    ed_madd_niels (ed_madd_niels (ed_madd_niels P (niels_of Q1)) (niels_of Q2)) (niels_of Q3)
      = ed_add P (ed_add Q1 (ed_add Q2 Q3)) := by
  rw [ed_madd_niels_eq_add, ed_madd_niels_eq_add, ed_madd_niels_eq_add,
      ed_add_assoc, ed_add_assoc]

/-- Three readditions in sequence. -/
theorem ed_readd_three (P Q1 Q2 Q3 : EdPt) :
    ed_readd (ed_readd (ed_readd P (cached_of Q1)) (cached_of Q2)) (cached_of Q3)
      = ed_add P (ed_add Q1 (ed_add Q2 Q3)) := by
  rw [ed_readd_eq_add, ed_readd_eq_add, ed_readd_eq_add,
      ed_add_assoc, ed_add_assoc]

/-- A Niels-form mixed addition after a readdition. -/
theorem ed_mixed_chain (P Q R : EdPt) :
    ed_madd_niels (ed_readd P (cached_of Q)) (niels_of R)
      = ed_add P (ed_add Q R) := by
  rw [ed_madd_niels_eq_add, ed_readd_eq_add, ed_add_assoc]

/-- Scalar multiplication of the lift of a cached form. -/
theorem ed_smul_cached (k : FpL25519) (P : EdPt) :
    ed_smul k (cached_to_pt (cached_of P)) = ed_smul k P := by
  rw [cached_roundtrip]

/-- Scalar multiplication of the lift of a Niels form. -/
theorem ed_smul_niels (k : FpL25519) (P : EdPt) :
    ed_smul k (niels_to_pt (niels_of P)) = ed_smul k P := by
  rw [niels_roundtrip]

/-! ## 7. Commutativity and identity -/

/-- Commutativity of `ed_add`. -/
theorem ed_add_comm (A B : EdPt) : ed_add A B = ed_add B A := add_comm A B

/-- Left identity of `ed_add`. -/
theorem ed_add_left_id (P : EdPt) : ed_add ed_identity P = P := zero_add P

/-- Right identity of `ed_add`. -/
theorem ed_add_right_id (P : EdPt) : ed_add P ed_identity = P := add_zero P

/-- `(−k)·P + k·P` is the identity. -/
theorem ed_smul_neg_inv_left (k : FpL25519) (P : EdPt) :
    ed_add (ed_smul (scalar_neg k) P) (ed_smul k P) = ed_identity := by
  rw [ed_add_comm]; exact ed_smul_neg_inv k P

/-! ## 8. Derived Z-module identities -/

/-- Scalar action commutes through itself: `a·(b·P) = b·(a·P)`. -/
theorem ed_smul_swap (a b : FpL25519) (P : EdPt) :
    ed_smul a (ed_smul b P) = ed_smul b (ed_smul a P) := by
  rw [← ed_smul_assoc_left, ← ed_smul_assoc_left]
  apply ed_smul_resp_interp
  rw [interp_scalar_mul, interp_scalar_mul, mul_comm]

/-- Cancellation: `(P + (−k)·P) + k·P = P`. -/
theorem ed_add_neg_smul_cancel (k : FpL25519) (P : EdPt) :
    ed_add (ed_add P (ed_smul (scalar_neg k) P)) (ed_smul k P) = P := by
  rw [ed_add_assoc, ed_smul_neg_inv_left, ed_add_right_id]

/-- Cancellation: `(P + k·P) + (−k)·P = P`. -/
theorem ed_add_sub_cancel (k : FpL25519) (P : EdPt) :
    ed_add (ed_add P (ed_smul k P)) (ed_smul (scalar_neg k) P) = P := by
  rw [ed_add_assoc, ed_smul_neg_inv, ed_add_right_id]

/-- `(a + a·b)·P = a·P + a·(b·P)`. -/
theorem ed_smul_distrib_smul (a b : FpL25519) (P : EdPt) :
    ed_smul (scalar_add a (scalar_mul a b)) P
      = ed_add (ed_smul a P) (ed_smul a (ed_smul b P)) := by
  rw [ed_smul_distrib_add, ed_smul_assoc_left]

/-- Mixed addition with the Niels form of the identity is the identity map. -/
theorem ed_madd_niels_identity (P : EdPt) :
    ed_madd_niels P (niels_of ed_identity) = P := by
  rw [ed_madd_niels_eq_add, ed_add_right_id]

/-- Readdition with the cached form of the identity is the identity map. -/
theorem ed_readd_identity (P : EdPt) :
    ed_readd P (cached_of ed_identity) = P := by
  rw [ed_readd_eq_add, ed_add_right_id]

/-! ## 9. Verify-side rearrangements

The Ed25519 verify routine accepts when `s·B = R + k·A`;
`bench_ed25519_sign.c::ed_verify` computes `(s·B − k·A) − R`. -/

/-- `s·B = R + k·A` implies `s·B + (−k)·A = R`. -/
theorem sign_verify_equation_subform
    (s k : FpL25519) (R A : EdPt)
    (h : ed_smul s ed_B = ed_add R (ed_smul k A)) :
    ed_add (ed_smul s ed_B) (ed_smul (scalar_neg k) A) = R := by
  rw [h, ed_add_assoc, ed_smul_neg_inv, ed_add_right_id]

/-- `s·B + (−k)·A = R` implies `s·B = R + k·A`. -/
theorem sign_verify_equation_subform_reverse
    (s k : FpL25519) (R A : EdPt)
    (h : ed_add (ed_smul s ed_B) (ed_smul (scalar_neg k) A) = R) :
    ed_smul s ed_B = ed_add R (ed_smul k A) := by
  rw [← h, ed_add_assoc, ed_smul_neg_inv_left, ed_add_right_id]

/-- The two verify-form statements are equivalent. -/
theorem sign_verify_equation_iff
    (s k : FpL25519) (R A : EdPt) :
    (ed_smul s ed_B = ed_add R (ed_smul k A))
      ↔ (ed_add (ed_smul s ed_B) (ed_smul (scalar_neg k) A) = R) :=
  ⟨sign_verify_equation_subform s k R A,
   sign_verify_equation_subform_reverse s k R A⟩

/-- Triple form of the verify check: `s·B − k·A − R` is the identity. -/
theorem sign_verify_equation_triple_form
    (s k : FpL25519) (r : FpL25519) (A : EdPt)
    (h : ed_smul s ed_B = ed_add (ed_smul r ed_B) (ed_smul k A)) :
    ed_add (ed_add (ed_smul s ed_B) (ed_smul (scalar_neg k) A))
           (ed_smul (scalar_neg r) ed_B) = ed_identity := by
  rw [sign_verify_equation_subform s k (ed_smul r ed_B) A h,
      ed_smul_neg_inv]

/-- `(r + k·a)·B = r·B + k·(a·B)`. -/
theorem sign_response_rewrite
    (r k a : FpL25519) :
    ed_smul (scalar_add r (scalar_mul k a)) ed_B
      = ed_add (ed_smul r ed_B) (ed_smul k (ed_smul a ed_B)) := by
  rw [ed_smul_distrib_add, ed_smul_assoc_left]

end CatCrypt.Crypto.Jasmin.Ed25519Optimizations
