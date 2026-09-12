/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Tactic.NormNum.LegendreSymbol
public meta import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
public meta import CatCrypt.Crypto.Jasmin.EdwardsCurve
public import CatCrypt.Crypto.Jasmin.EdwardsCurve
public meta import CatCrypt.Crypto.Util.X25519Verified
public import CatCrypt.Crypto.Util.X25519Verified

/-!
# The twisted-Edwards curve points of the dialect carrier and their group law

The EllipticCurve dialect carries points as `ECPoint p = Option (ZMod p × ZMod p)`,
the whole affine plane together with a formal identity `none`, and
`EdwardsParams.add` — the unified twisted-Edwards law — is defined on all of it.
The unified law is branch-free but not inverse-free: its two denominators
`1 ± d·x₁·x₂·y₁·y₂` vanish somewhere on the affine plane, and there the Lean
convention `(0 : ZMod p)⁻¹ = 0` drops a coordinate to `0`.  A statement
quantified over the whole carrier — `EdAssoc` of `EdDSA/Ed25519ScalarMulSmul.lean`
— is therefore false at every nondegenerate parameter, Ed25519 included
(`X86Backend/EdAssocAudit.not_edAssoc`).

`IsEdPoint C v` is the predicate cutting the carrier down to the curve: `v` is
the formal identity `none`, or an affine point satisfying `EdwardsParams.onCurve`.
The `none` disjunct is what the abstract folds need: `EdwardsParams.smul` is a
left fold seeded at `ECPoint.zero = none`, while the affine identity of the
twisted-Edwards group is `(0, 1)`, so both live in the predicate.

Mathlib has no twisted-Edwards curve type, so the group law comes from
`Jasmin/EdwardsCurve.lean`: `OnCurveAff`, the subtype `EdwardsPointAff`, its
`add_closure`, `add_comm` and `add_assoc`.  `IsEdCurve C` records the six
conditions that file's `EdwardsParams` record carries — four nondegeneracy
conditions plus the two completeness conditions `∃ s, s² = a` and `∀ x, x² ≠ d`
that the addition-formula denominators need — so a consumer holding a dialect
parameter pair reaches the subtype through `IsEdCurve.toCurve`.

## Axiom cost

Sections 1 to 4 are axiom-free over Mathlib.  Section 5 carries the axioms the
constant `CatCrypt.Util.ed25519D` already has on its own: the `native_decide`
axioms of the nested Lucas/Pratt certificate `Util/P25519PrimeCert.lean` behind
`Fact (Nat.Prime P25519)`.

## Main results

* `IsEdPoint` — the carrier values that are points of the curve.
* `IsEdCurve` — the nondegeneracy and completeness conditions on a dialect
  parameter pair, and `IsEdCurve.toCurve`, the
  `Jasmin.EdwardsCurve.EdwardsParams` record it determines.
* `toECPoint`, `toECPoint_add` — the on-curve subtype `EdwardsPointAff` embedded
  in the carrier, carrying `EdwardsPointAff.add` to the dialect
  `EdwardsParams.add`.
* `edAssoc_onCurve`, `edComm_onCurve` — associativity and commutativity of the
  dialect `EdwardsParams.add` on the embedded subtype.
* `isEdPoint_zero`, `isEdPoint_affIdentity`, `isEdPoint_affOrderTwo`,
  `isEdPoint_aff`, `onCurve_of_isEdPoint` — the identity, the affine identity
  `(0, 1)`, the point `(0, −1)`, and the correspondence with
  `EdwardsParams.onCurve`.
* `isEdPoint_iff` — a curve point is `none` or the image of a point of the
  on-curve subtype.
* `isEdPoint_add`, `isEdPoint_assoc`, `isEdPoint_add_comm`, `isEdPoint_smul`,
  `isEdPoint_foldl` — closure of the curve points under the group law, the
  scalar-mul fold and an arbitrary group fold, and the group axioms at two and
  three curve points.
* `foldl_add_seed` — a group fold of curve points from a curve-point seed splits
  as the seed plus the identity-seeded fold.
* `edSmul_one`, `edSmul_add`, `edSmul_double`, `edSmul_mul` — the scalar-mul
  fold at a curve base point: unit scalar, additivity and multiplicativity in
  the exponent, and the doubling step.
* `neg_one_square_p25519`, `legendreSym_ed25519D`, `ed25519D_nonsquare` — the
  two completeness conditions at the Ed25519 base field.
* `isEdCurve_of_ed25519_constants` — the Ed25519 constants `a = −1`,
  `d = ed25519D` satisfy `IsEdCurve` over `ZMod P25519`, so the toolkit applies
  at `ed25519EdParams`.
* `affIdentity_ne_affOrderTwo` — `(0, 1)` and `(0, −1)` are distinct curve
  points over `ZMod P25519`.
* `toyEdParams`, `isEdCurve_toy`, `isEdPoint_toyWitness`, `isEdPoint_toy_double`,
  `toy_smul_four` — a decidable toy curve `a = 1`, `d = 2` over `ZMod 11` at
  which `IsEdCurve`, a curve point, its group-law closure and the order-`4`
  scalar-mul value `4 · (1, 0) = (0, 1)` hold by `decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EdPointOnCurve

open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.Jasmin.EdwardsCurve hiding EdwardsParams

variable {p : Nat}

/-! ## 1. The curve points of the carrier -/

/-- A dialect carrier value that is a point of the twisted-Edwards curve: the
    formal identity `none`, or an affine point satisfying
    `EdwardsParams.onCurve`. -/
def IsEdPoint (C : EdwardsParams p) (v : ECPoint p) : Prop :=
  v = ECPoint.zero ∨ ∃ x y : ZMod p, v = ECPoint.aff x y ∧ C.onCurve x y

/-- The formal identity of the carrier is a curve point. -/
theorem isEdPoint_zero (C : EdwardsParams p) : IsEdPoint C ECPoint.zero :=
  Or.inl rfl

/-- An affine point satisfying the on-curve predicate is a curve point. -/
theorem isEdPoint_aff (C : EdwardsParams p) {x y : ZMod p} (h : C.onCurve x y) :
    IsEdPoint C (ECPoint.aff x y) :=
  Or.inr ⟨x, y, rfl, h⟩

/-- An affine curve point satisfies the on-curve predicate. -/
theorem onCurve_of_isEdPoint (C : EdwardsParams p) {x y : ZMod p}
    (h : IsEdPoint C (ECPoint.aff x y)) : C.onCurve x y := by
  rcases h with hz | ⟨x', y', heq, hoc⟩
  · simp only [ECPoint.aff, ECPoint.zero, reduceCtorEq] at hz
  · simp only [ECPoint.aff, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨hx, hy⟩ := heq
    subst hx; subst hy
    exact hoc

/-- The affine identity `(0, 1)` of the twisted-Edwards group is a curve
    point. -/
theorem isEdPoint_affIdentity (C : EdwardsParams p) : IsEdPoint C (ECPoint.aff 0 1) :=
  isEdPoint_aff C (by simp only [EdwardsParams.onCurve]; ring)

/-- The point `(0, −1)` is a curve point. -/
theorem isEdPoint_affOrderTwo (C : EdwardsParams p) : IsEdPoint C (ECPoint.aff 0 (-1)) :=
  isEdPoint_aff C (by simp only [EdwardsParams.onCurve]; ring)

/-- The nondegeneracy conditions of a complete twisted-Edwards curve, as a
    predicate on a dialect parameter pair.  The fields are those of
    `Jasmin.EdwardsCurve.EdwardsParams`. -/
structure IsEdCurve (C : EdwardsParams p) : Prop where
  /-- The curve coefficient `a` is nonzero. -/
  a_ne_zero : C.a ≠ 0
  /-- The curve coefficient `d` is nonzero. -/
  d_ne_zero : C.d ≠ 0
  /-- The two curve coefficients are distinct. -/
  a_ne_d : C.a ≠ C.d
  /-- The base field has characteristic other than `2`. -/
  two_ne_zero : (2 : ZMod p) ≠ 0
  /-- The curve coefficient `a` is a square. -/
  square_a : ∃ s : ZMod p, s ^ 2 = C.a
  /-- The curve coefficient `d` is not a square. -/
  nonsquare_d : ∀ x : ZMod p, x ^ 2 ≠ C.d

/-! ## 2. The bridge to the on-curve subtype -/

section Bridge

variable [Fact (Nat.Prime p)]

/-- The dialect parameter pair of a complete twisted-Edwards curve. -/
def dialectParams (E : CatCrypt.Crypto.Jasmin.EdwardsCurve.EdwardsParams (ZMod p)) :
    EdwardsParams p :=
  ⟨E.a, E.d⟩

variable {E : CatCrypt.Crypto.Jasmin.EdwardsCurve.EdwardsParams (ZMod p)}

@[simp] theorem dialectParams_a : (dialectParams E).a = E.a := rfl

@[simp] theorem dialectParams_d : (dialectParams E).d = E.d := rfl

/-- The dialect on-curve predicate at `dialectParams E` is `OnCurveAff E`. -/
theorem onCurve_iff (x y : ZMod p) : (dialectParams E).onCurve x y ↔ OnCurveAff E x y := by
  simp only [EdwardsParams.onCurve, OnCurveAff, dialectParams]
  constructor <;> intro h <;> linear_combination h

/-- Embed a point of the on-curve subtype as a dialect carrier value. -/
def toECPoint (P : EdwardsPointAff E) : ECPoint p :=
  ECPoint.aff P.x P.y

/-- `toECPoint` carries the on-curve twisted-Edwards addition to the dialect
    `EdwardsParams.add`. -/
theorem toECPoint_add (P Q : EdwardsPointAff E) :
    (dialectParams E).add (toECPoint P) (toECPoint Q)
      = toECPoint (EdwardsPointAff.add P Q) := by
  simp only [toECPoint]
  rw [EdwardsParams.add_aff]
  simp only [dialectParams, EdwardsParams.affRx, EdwardsParams.affRy, EdwardsParams.addT,
    EdwardsParams.addXNum, EdwardsParams.addYNum, EdwardsPointAff.add, EdwardsPointAff.add_xy,
    ECPoint.aff, Option.some.injEq, Prod.mk.injEq, div_eq_mul_inv]
  refine ⟨?_, ?_⟩ <;> ring

/-- **The dialect twisted-Edwards `add` is associative on the on-curve
    subtype.**  The restriction of `EdAssoc` that has a model, as a theorem. -/
theorem edAssoc_onCurve (P Q R : EdwardsPointAff E) :
    (dialectParams E).add ((dialectParams E).add (toECPoint P) (toECPoint Q)) (toECPoint R)
      = (dialectParams E).add (toECPoint P)
          ((dialectParams E).add (toECPoint Q) (toECPoint R)) := by
  rw [toECPoint_add, toECPoint_add, toECPoint_add, toECPoint_add, EdwardsPointAff.add_assoc]

/-- The dialect twisted-Edwards `add` is commutative on the on-curve subtype. -/
theorem edComm_onCurve (P Q : EdwardsPointAff E) :
    (dialectParams E).add (toECPoint P) (toECPoint Q)
      = (dialectParams E).add (toECPoint Q) (toECPoint P) := by
  rw [toECPoint_add, toECPoint_add, EdwardsPointAff.add_comm]

/-- The `Jasmin.EdwardsCurve.EdwardsParams` record determined by a nondegenerate
    dialect parameter pair. -/
def IsEdCurve.toCurve {C : EdwardsParams p} (h : IsEdCurve C) :
    CatCrypt.Crypto.Jasmin.EdwardsCurve.EdwardsParams (ZMod p) :=
  ⟨C.a, C.d, h.a_ne_zero, h.d_ne_zero, h.a_ne_d, h.two_ne_zero, h.square_a, h.nonsquare_d⟩

@[simp] theorem dialectParams_toCurve {C : EdwardsParams p} (h : IsEdCurve C) :
    dialectParams h.toCurve = C := rfl

/-! ## 3. Closure and the group axioms on the curve points -/

variable {C : EdwardsParams p}

/-- A curve point is the formal identity or the image of a point of the on-curve
    subtype. -/
theorem isEdPoint_iff (hC : IsEdCurve C) (v : ECPoint p) :
    IsEdPoint C v ↔ v = ECPoint.zero ∨ ∃ P : EdwardsPointAff hC.toCurve, toECPoint P = v := by
  constructor
  · rintro (rfl | ⟨x, y, rfl, hoc⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨x, y, (onCurve_iff (E := hC.toCurve) x y).mp hoc⟩, rfl⟩
  · rintro (rfl | ⟨P, rfl⟩)
    · exact Or.inl rfl
    · exact isEdPoint_aff C ((onCurve_iff (E := hC.toCurve) P.x P.y).mpr P.on_curve)

/-- The image of a point of the on-curve subtype is a curve point. -/
theorem isEdPoint_toECPoint (hC : IsEdCurve C) (P : EdwardsPointAff hC.toCurve) :
    IsEdPoint C (toECPoint P) :=
  (isEdPoint_iff hC _).mpr (Or.inr ⟨P, rfl⟩)

/-- **The curve points are closed under the dialect group law.** -/
theorem isEdPoint_add (hC : IsEdCurve C) {u v : ECPoint p}
    (hu : IsEdPoint C u) (hv : IsEdPoint C v) : IsEdPoint C (C.add u v) := by
  rcases (isEdPoint_iff hC u).mp hu with rfl | ⟨P, rfl⟩
  · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_left]
    exact hv
  · rcases (isEdPoint_iff hC v).mp hv with rfl | ⟨Q, rfl⟩
    · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_right]
      exact isEdPoint_toECPoint hC P
    · show IsEdPoint C ((dialectParams hC.toCurve).add (toECPoint P) (toECPoint Q))
      rw [toECPoint_add]
      exact isEdPoint_toECPoint hC _

/-- **The dialect group law is associative on the curve points.**  The on-curve
    replacement for the hypothesis `EdAssoc C`. -/
theorem isEdPoint_assoc (hC : IsEdCurve C) {u v w : ECPoint p}
    (hu : IsEdPoint C u) (hv : IsEdPoint C v) (hw : IsEdPoint C w) :
    C.add (C.add u v) w = C.add u (C.add v w) := by
  rcases (isEdPoint_iff hC u).mp hu with rfl | ⟨P, rfl⟩
  · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_left,
      EdwardsParams.add_none_left]
  · rcases (isEdPoint_iff hC v).mp hv with rfl | ⟨Q, rfl⟩
    · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_right,
        EdwardsParams.add_none_left]
    · rcases (isEdPoint_iff hC w).mp hw with rfl | ⟨R, rfl⟩
      · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_right,
          EdwardsParams.add_none_right]
      · exact edAssoc_onCurve P Q R

/-- The dialect group law is commutative on the curve points. -/
theorem isEdPoint_add_comm (hC : IsEdCurve C) {u v : ECPoint p}
    (hu : IsEdPoint C u) (hv : IsEdPoint C v) : C.add u v = C.add v u := by
  rcases (isEdPoint_iff hC u).mp hu with rfl | ⟨P, rfl⟩
  · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_left,
      EdwardsParams.add_none_right]
  · rcases (isEdPoint_iff hC v).mp hv with rfl | ⟨Q, rfl⟩
    · rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_left,
        EdwardsParams.add_none_right]
    · exact edComm_onCurve P Q

/-! ## 4. Iterated sums and the scalar-mul fold -/

/-- **The group fold of a list of curve points from a curve-point seed stays a
    curve point.** -/
theorem isEdPoint_foldl (hC : IsEdCurve C) (Ps : List (ECPoint p)) :
    ∀ {acc : ECPoint p}, IsEdPoint C acc → (∀ v ∈ Ps, IsEdPoint C v) →
      IsEdPoint C (Ps.foldl C.add acc) := by
  induction Ps with
  | nil => intro acc hacc _; exact hacc
  | cons v Ps ih =>
    intro acc hacc hmem
    simp only [List.foldl_cons]
    exact ih (isEdPoint_add hC hacc (hmem v (by simp)))
      (fun w hw => hmem w (by simp [hw]))

/-- The curve points are closed under the abstract scalar-mul fold. -/
theorem isEdPoint_smul (hC : IsEdCurve C) {v : ECPoint p} (h : IsEdPoint C v) (m : Nat) :
    IsEdPoint C (C.smul m v) := by
  simp only [EdwardsParams.smul]
  exact isEdPoint_foldl hC _ (isEdPoint_zero C)
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact h)

/-- **A group fold of curve points from a curve-point seed splits as the seed
    plus the identity-seeded fold.**  The lemma the exponent laws run on. -/
theorem foldl_add_seed (hC : IsEdCurve C) :
    ∀ (Ps : List (ECPoint p)), (∀ v ∈ Ps, IsEdPoint C v) →
      ∀ {acc : ECPoint p}, IsEdPoint C acc →
        Ps.foldl C.add acc = C.add acc (Ps.foldl C.add ECPoint.zero) := by
  intro Ps
  induction Ps with
  | nil =>
    intro _ acc _
    simp only [List.foldl_nil]
    rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_right]
  | cons v Ps ih =>
    intro hmem acc hacc
    have hv : IsEdPoint C v := hmem v (by simp)
    have htail : ∀ w ∈ Ps, IsEdPoint C w := fun w hw => hmem w (by simp [hw])
    have hS : IsEdPoint C (Ps.foldl C.add ECPoint.zero) :=
      isEdPoint_foldl hC Ps (isEdPoint_zero C) htail
    simp only [List.foldl_cons]
    rw [ih htail (isEdPoint_add hC hacc hv),
      show C.add ECPoint.zero v = v from rfl, ih htail hv]
    exact isEdPoint_assoc hC hacc hv hS

omit [Fact (Nat.Prime p)] in
/-- The unit scalar multiple of any carrier value is that value. -/
theorem edSmul_one (D : EdwardsParams p) (P : ECPoint p) : D.smul 1 P = P := by
  simp only [EdwardsParams.smul, List.replicate_one, List.foldl_cons, List.foldl_nil]
  rw [show (ECPoint.zero : ECPoint p) = none from rfl, EdwardsParams.add_none_left]

/-- **`EdwardsParams.smul` is additive in the exponent at a curve point.** -/
theorem edSmul_add (hC : IsEdCurve C) {P : ECPoint p} (hP : IsEdPoint C P) (m n : Nat) :
    C.smul (m + n) P = C.add (C.smul m P) (C.smul n P) := by
  simp only [EdwardsParams.smul, List.replicate_add, List.foldl_append]
  exact foldl_add_seed hC (List.replicate n P)
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact hP)
    (isEdPoint_smul hC hP m)

/-- The doubling step of the exponent at a curve point. -/
theorem edSmul_double (hC : IsEdCurve C) {P : ECPoint p} (hP : IsEdPoint C P) (k : Nat) :
    C.smul (2 * k) P = C.add (C.smul k P) (C.smul k P) := by
  rw [two_mul, edSmul_add hC hP]

/-- **`EdwardsParams.smul` is multiplicative in the exponent at a curve
    point.** -/
theorem edSmul_mul (hC : IsEdCurve C) {P : ECPoint p} (hP : IsEdPoint C P) (m n : Nat) :
    C.smul (m * n) P = C.smul m (C.smul n P) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hQ : IsEdPoint C (C.smul n P) := isEdPoint_smul hC hP n
    rw [Nat.succ_mul, edSmul_add hC hP, ih, edSmul_add hC hQ m 1, edSmul_one]

end Bridge

/-! ## 5. The Ed25519 parameters -/

section Ed25519

open CatCrypt.Util (P25519 ed25519D)

/-- A positive natural number below the modulus is nonzero in `ZMod p`. -/
theorem natCast_ne_zero_of_lt {n : Nat} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨by omega⟩
  intro hc
  have hv := ZMod.val_cast_of_lt hnp
  rw [hc, ZMod.val_zero] at hv
  omega

/-- A natural number whose successor is below the modulus is not `−1` in
    `ZMod p`. -/
theorem natCast_ne_neg_one_of_lt {n : Nat} (hnp : n + 1 < p) : (n : ZMod p) ≠ -1 := by
  haveI : NeZero p := ⟨by omega⟩
  intro hc
  have h1 : ((n + 1 : Nat) : ZMod p) = 0 := by push_cast; rw [hc]; ring
  have hv := ZMod.val_cast_of_lt hnp
  rw [h1, ZMod.val_zero] at hv
  omega

/-- The Ed25519 curve constant is nonzero. -/
theorem ed25519D_ne_zero : ed25519D ≠ 0 :=
  natCast_ne_zero_of_lt (p := P25519)
    (n := 37095705934669439343138083508754565189542113879843219016388785533085940283555)
    (by norm_num) (by norm_num [P25519])

/-- The Ed25519 curve constant is not `−1`. -/
theorem ed25519D_ne_neg_one : ed25519D ≠ -1 :=
  natCast_ne_neg_one_of_lt (p := P25519)
    (n := 37095705934669439343138083508754565189542113879843219016388785533085940283555)
    (by norm_num [P25519])

/-- The Curve25519 base field has characteristic other than `2`. -/
theorem two_ne_zero_p25519 : (2 : ZMod P25519) ≠ 0 := by
  simpa using natCast_ne_zero_of_lt (p := P25519) (n := 2) (by norm_num)
    (by norm_num [P25519])

/-- `−1` is a square in the Ed25519 base field, since `P25519 ≡ 1 [MOD 4]`.  The
    witness is `2 ^ ((P25519 − 1) / 4)`. -/
theorem neg_one_square_p25519 : ∃ s : ZMod P25519, s ^ 2 = -1 :=
  ⟨(19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ),
    by decide⟩

/-- The quadratic character of the Ed25519 curve constant at `P25519`.  The
    `norm_num` extension for the Jacobi symbol evaluates it by reciprocity. -/
theorem legendreSym_ed25519D :
    legendreSym P25519
      (37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℤ)
      = -1 := by
  norm_num [P25519]

/-- **The Ed25519 curve constant is not a square.**  The completeness condition
    on `d` behind `EdwardsPointAff.affine_denom_nonsquare`. -/
theorem ed25519D_nonsquare : ∀ x : ZMod P25519, x ^ 2 ≠ ed25519D := by
  have h := (legendreSym.eq_neg_one_iff P25519).mp legendreSym_ed25519D
  have hd : ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : ℤ)
      : ZMod P25519) = ed25519D := by
    rw [ed25519D]; push_cast; ring
  rw [hd] at h
  intro x hx
  exact h ⟨x, by rw [← hx]; ring⟩

/-- **The Ed25519 parameters are a complete twisted-Edwards curve.**  Any dialect
    parameter pair over `ZMod P25519` carrying `a = −1` and `d = ed25519D` —
    `ed25519EdParams` of `VIR/EllipticCurveDialectEd25519Migration.lean` is one —
    satisfies the nondegeneracy and completeness conditions, so the closure and
    associativity results apply to it. -/
theorem isEdCurve_of_ed25519_constants {C : EdwardsParams P25519}
    (ha : C.a = -1) (hd : C.d = ed25519D) : IsEdCurve C where
  a_ne_zero := by rw [ha]; exact neg_ne_zero.mpr one_ne_zero
  d_ne_zero := by rw [hd]; exact ed25519D_ne_zero
  a_ne_d := by rw [ha, hd]; exact fun h => ed25519D_ne_neg_one h.symm
  two_ne_zero := two_ne_zero_p25519
  square_a := by rw [ha]; exact neg_one_square_p25519
  nonsquare_d := by rw [hd]; exact ed25519D_nonsquare

/-- The affine identity `(0, 1)` and the point `(0, −1)` are distinct curve
    points over `ZMod P25519`, so the curve points of the Ed25519 carrier are
    more than the identity alone. -/
theorem affIdentity_ne_affOrderTwo :
    (ECPoint.aff (0 : ZMod P25519) 1) ≠ ECPoint.aff 0 (-1) := by
  intro h
  simp only [ECPoint.aff, Option.some.injEq, Prod.mk.injEq] at h
  exact two_ne_zero_p25519 (by linear_combination h.2)

end Ed25519

/-! ## 6. A small complete twisted-Edwards curve witness

A decidable toy curve at which every `IsEdCurve` field, a curve point, its
group-law closure and a scalar-mul value are discharged by `decide` over a base
field small enough to evaluate.  The predicate and the closure lemmas are thus
inhabited independently of the `native_decide` prime certificate of §5. -/

section SmallWitness

/-- The twisted-Edwards parameter pair `a = 1`, `d = 2` over `ZMod 11`: `a` is a
    square and `d` a nonsquare, so the curve is complete. -/
def toyEdParams : EdwardsParams 11 := ⟨1, 2⟩

/-- The toy parameters are a complete twisted-Edwards curve. -/
theorem isEdCurve_toy : IsEdCurve toyEdParams where
  a_ne_zero := by decide
  d_ne_zero := by decide
  a_ne_d := by decide
  two_ne_zero := by decide
  square_a := ⟨1, by decide⟩
  nonsquare_d := by decide

/-- `(1, 0)` is a point of the toy curve. -/
theorem isEdPoint_toyWitness : IsEdPoint toyEdParams (ECPoint.aff 1 0) :=
  isEdPoint_aff toyEdParams (by simp only [EdwardsParams.onCurve, toyEdParams]; ring)

/-- The sum of the toy witness with itself is a curve point, via `isEdPoint_add`
    with no associativity hypothesis. -/
theorem isEdPoint_toy_double :
    IsEdPoint toyEdParams (toyEdParams.add (ECPoint.aff 1 0) (ECPoint.aff 1 0)) :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  isEdPoint_add isEdCurve_toy isEdPoint_toyWitness isEdPoint_toyWitness

/-- The toy base point `(1, 0)` has order `4`: `4 · (1, 0)` is the affine identity
    `(0, 1)`. -/
theorem toy_smul_four :
    toyEdParams.smul 4 (ECPoint.aff 1 0) = ECPoint.aff 0 1 := by decide +kernel

end SmallWitness

end CatCrypt.Crypto.SecureCompilation.VIR.EdPointOnCurve
