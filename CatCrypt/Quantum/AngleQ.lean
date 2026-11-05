/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.QasmAngle

/-!
# Computable rotation angles for the Clifford+T gate set

`Gate.Rz` carries a real angle, so any pass that manipulates angles is
noncomputable and no angle predicate reduces in the kernel. Every angle the
Clifford+T gate set contributes is a rational multiple of `π` (`T = rz(π/4)`,
`S = rz(π/2)`, `Z = rz(π)`), and sums of such angles stay in that set.

`AngleQ` is the angle type of that set: the rational `q` denotes the angle
`q · π` in radians. It is the type `QasmAngle` already used at the OpenQASM I/O
boundary, so an angle carried through an optimizer pass is emittable without
conversion. `AngleQ` has `DecidableEq` and its operations evaluate, so `#guard`
and `decide` apply to angle facts.

## Main results

* `AngleQ.toReal` — the embedding `q ↦ q · π` into the real angle of `Gate.Rz`,
  with its additive compatibility lemmas.
* `QCircuit.rzGate_add_two_pi` and `QCircuit.rzGate_add_int_mul_two_pi` —
  periodicity of the `Rz` matrix, and the `AngleQ` forms
  `AngleQ.rzGate_toReal_add_two` / `AngleQ.rzGate_toReal_add_int_two`.
* `AngleQ.isTrivial` — a decidable test for `q · π` being a whole number of
  turns, characterised by `AngleQ.isTrivial_iff` as `rzGate (toReal q) = 1`.
* `AngleQ.reduceMod2` — the representative of `q` modulo `2` in `[0, 2)`,
  semantics-preserving by `AngleQ.rzGate_toReal_reduceMod2`.

The embedding is injective but not surjective: `AngleQ` reaches exactly the
rational multiples of `π`, so a variational circuit's angle stays on the real
`Gate.Rz`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum

open scoped Real

/-! ## Periodicity of the `Rz` matrix -/

namespace QCircuit

/-- The `Rz` matrix is `2π`-periodic in its angle. -/
theorem rzGate_add_two_pi (θ : ℝ) : rzGate (θ + 2 * Real.pi) = rzGate θ := by
  have h : Complex.exp (Complex.I * ((θ : ℂ) + 2 * Real.pi))
      = Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [mul_add, Complex.exp_add]
    rw [show Complex.I * (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I by ring]
    rw [Complex.exp_two_pi_mul_I, mul_one]
  simp only [rzGate]
  push_cast
  rw [h]

/-- The `Rz` matrix is invariant under adding any integer number of turns. -/
theorem rzGate_add_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    rzGate (θ + k * (2 * Real.pi)) = rzGate θ := by
  have h : Complex.exp (Complex.I * ((θ : ℂ) + (k : ℂ) * (2 * Real.pi)))
      = Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [mul_add, Complex.exp_add]
    rw [show Complex.I * ((k : ℂ) * (2 * (Real.pi : ℂ)))
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]
  simp only [rzGate]
  push_cast
  rw [h]

/-- The `Rz` matrix at angle `θ` is the identity exactly when `e^{iθ} = 1`. -/
theorem rzGate_eq_one_iff (θ : ℝ) :
    rzGate θ = 1 ↔ Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
  constructor
  · intro h
    have := congrArg (fun M => M 1 1) h
    simpa [rzGate, Matrix.one_apply] using this
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rzGate, h]

end QCircuit

/-! ## The angle type -/

/-- A rotation angle stored as the rational `q` denoting `q · π` radians. -/
abbrev AngleQ : Type := QasmAngle

namespace AngleQ

/-- The real angle `q · π` denoted by `q`. -/
noncomputable abbrev toReal (q : AngleQ) : ℝ := QasmAngle.toReal q

@[simp] theorem toReal_zero : toReal 0 = 0 := QasmAngle.toReal_zero

@[simp] theorem toReal_one : toReal 1 = Real.pi := QasmAngle.toReal_one

@[simp] theorem toReal_add (p q : AngleQ) : toReal (p + q) = toReal p + toReal q := by
  simp [QasmAngle.toReal, add_mul]

@[simp] theorem toReal_neg (q : AngleQ) : toReal (-q) = -toReal q := by
  simp [QasmAngle.toReal]

@[simp] theorem toReal_sub (p q : AngleQ) : toReal (p - q) = toReal p - toReal q := by
  simp [QasmAngle.toReal, sub_mul]

/-- `toReal` is injective: `q · π` determines `q`. -/
theorem toReal_injective : Function.Injective toReal := by
  intro p q h
  simp only [QasmAngle.toReal] at h
  have : (p : ℝ) = (q : ℝ) := mul_right_cancel₀ Real.pi_ne_zero h
  exact_mod_cast this

/-- Two turns in `AngleQ` is `2π` radians. -/
theorem toReal_two : toReal 2 = 2 * Real.pi := by
  simp [QasmAngle.toReal]

/-! ## Periodicity in `AngleQ` -/

/-- Adding `2` to an `AngleQ` leaves the `Rz` matrix unchanged. -/
theorem rzGate_toReal_add_two (q : AngleQ) :
    QCircuit.rzGate (toReal (q + 2)) = QCircuit.rzGate (toReal q) := by
  rw [toReal_add, toReal_two, QCircuit.rzGate_add_two_pi]

/-- Adding any even integer to an `AngleQ` leaves the `Rz` matrix unchanged. -/
theorem rzGate_toReal_add_int_two (q : AngleQ) (k : ℤ) :
    QCircuit.rzGate (toReal (q + 2 * (k : ℚ))) = QCircuit.rzGate (toReal q) := by
  have h : toReal (q + 2 * (k : ℚ)) = toReal q + k * (2 * Real.pi) := by
    simp only [QasmAngle.toReal]
    push_cast
    ring
  rw [h, QCircuit.rzGate_add_int_mul_two_pi]

/-! ## Deciding a whole number of turns -/

/-- Whether `q · π` is a whole number of turns, i.e. `q` is an even integer.

`ℚ` carries the `EuclideanDomain` modulus of a field, for which `q % 2 = 0`
holds of every `q`; the test is stated on the numerator and denominator of the
reduced fraction instead. -/
def isTrivial (q : AngleQ) : Bool := q.den == 1 && q.num % 2 == 0

/-- `isTrivial` holds exactly of the even integers. -/
theorem isTrivial_iff_exists_int (q : AngleQ) :
    isTrivial q = true ↔ ∃ k : ℤ, q = 2 * (k : ℚ) := by
  constructor
  · intro h
    simp only [isTrivial, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hden, hnum⟩ := h
    refine ⟨q.num / 2, ?_⟩
    have hq : (q.num : ℚ) = q := by
      conv_rhs => rw [← Rat.num_div_den q]
      rw [hden]
      simp
    rw [← hq]
    have hd2 : q.num = 2 * (q.num / 2) :=
      (Int.mul_ediv_add_emod q.num 2).symm.trans (by rw [hnum, add_zero])
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hd2
  · rintro ⟨k, rfl⟩
    have hk : (2 * (k : ℚ)) = ((2 * k : ℤ) : ℚ) := by push_cast; ring
    simp only [isTrivial, hk, Rat.den_intCast, Rat.num_intCast, beq_iff_eq,
      Bool.and_eq_true]
    exact ⟨trivial, by omega⟩

/-- `isTrivial q` holds exactly when the rotation by `q · π` is the identity. -/
theorem isTrivial_iff (q : AngleQ) :
    isTrivial q = true ↔ QCircuit.rzGate (toReal q) = 1 := by
  rw [isTrivial_iff_exists_int, QCircuit.rzGate_eq_one_iff, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp only [QasmAngle.toReal]
    push_cast
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only [QasmAngle.toReal] at hk
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h1 : Complex.I * ((q : ℂ) * ((Real.pi : ℝ) : ℂ))
        = Complex.I * (2 * (k : ℂ) * ((Real.pi : ℝ) : ℂ)) := by
      push_cast at hk ⊢
      linear_combination hk
    have h2 := mul_left_cancel₀ Complex.I_ne_zero h1
    have h3 := mul_right_cancel₀ hpi h2
    exact_mod_cast h3

instance : DecidablePred (fun q : AngleQ => QCircuit.rzGate (toReal q) = 1) :=
  fun q => decidable_of_iff (isTrivial q = true) (isTrivial_iff q)

/-! ## Reduction modulo two turns -/

/-- The representative of `q` modulo `2`, lying in `[0, 2)`. -/
def reduceMod2 (q : AngleQ) : AngleQ := ((q.num % (2 * q.den) : ℤ) : ℚ) / (q.den : ℚ)

/-- `q` differs from its reduced representative by an even integer. -/
theorem reduceMod2_add (q : AngleQ) :
    q = reduceMod2 q + 2 * ((q.num / (2 * q.den) : ℤ) : ℚ) := by
  have hd : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hn : (2 * (q.den : ℤ)) * (q.num / (2 * q.den)) + q.num % (2 * q.den) = q.num :=
    Int.mul_ediv_add_emod _ _
  have hn' : ((q.num % (2 * (q.den : ℤ)) : ℤ) : ℚ)
      + 2 * (q.den : ℚ) * ((q.num / (2 * (q.den : ℤ)) : ℤ) : ℚ) = (q.num : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hn
    push_cast at this
    linarith
  rw [reduceMod2]
  conv_lhs => rw [← Rat.num_div_den q]
  field_simp
  linarith [hn']

/-- The reduced representative is nonnegative. -/
theorem reduceMod2_nonneg (q : AngleQ) : 0 ≤ reduceMod2 q := by
  have hdz : ((q.den : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr q.den_nz
  have h2d : (2 * (q.den : ℤ)) ≠ 0 := mul_ne_zero two_ne_zero hdz
  have hnum : (0 : ℤ) ≤ q.num % (2 * q.den) := Int.emod_nonneg _ h2d
  have hd : (0 : ℚ) ≤ (q.den : ℚ) := by positivity
  exact div_nonneg (by exact_mod_cast hnum) hd

/-- The reduced representative is below two turns. -/
theorem reduceMod2_lt_two (q : AngleQ) : reduceMod2 q < 2 := by
  have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have h2d : (0 : ℤ) < 2 * q.den := by
    have := q.den_pos
    omega
  have hlt : q.num % (2 * (q.den : ℤ)) < 2 * q.den := Int.emod_lt_of_pos _ h2d
  have hltq : ((q.num % (2 * (q.den : ℤ)) : ℤ) : ℚ) < ((2 * (q.den : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast hlt
  rw [reduceMod2, div_lt_iff₀ hd]
  push_cast at hltq
  linarith

/-- Reducing an angle modulo two turns preserves the `Rz` matrix. -/
theorem rzGate_toReal_reduceMod2 (q : AngleQ) :
    QCircuit.rzGate (toReal (reduceMod2 q)) = QCircuit.rzGate (toReal q) := by
  conv_rhs => rw [reduceMod2_add q]
  rw [rzGate_toReal_add_int_two]

/-! ## Clifford+T angles -/

/-- The `T` gate angle, `π/4`. -/
def tAngle : AngleQ := 1 / 4

/-- The `S` gate angle, `π/2`. -/
def sAngle : AngleQ := 1 / 2

/-- The `Z` gate angle, `π`. -/
def zAngle : AngleQ := 1

#guard tAngle + tAngle == sAngle
#guard sAngle + sAngle == zAngle
#guard zAngle + zAngle == (2 : AngleQ)
#guard isTrivial (tAngle + tAngle + tAngle + tAngle + tAngle + tAngle + tAngle + tAngle)
#guard !isTrivial tAngle
#guard !isTrivial zAngle
#guard isTrivial (zAngle + zAngle)
#guard isTrivial (tAngle + (-tAngle))
#guard reduceMod2 (zAngle + zAngle + tAngle) == tAngle
#guard reduceMod2 (-tAngle) == 7 / 4

/-! ## The T-cost of an angle -/

/-- The number of `T` gates an exact Clifford+T realisation of `Rz (toReal q)`
    costs, and `none` for an angle outside the fragment.

    A rational `q` is in lowest terms, so the denominator classifies the angle:
    `1` and `2` are integer and half-integer multiples of `π`, the Clifford
    rotations `Z`, `S` and their inverses, which cost no `T`; `4` is an odd
    multiple of `π/4`, one `T` or `T†`. Any other denominator is not a
    Clifford+T rotation at all — it has no exact realisation, only an
    approximation whose cost grows with the accuracy demanded — so the cost is
    `none` rather than a number.

    This is what `TCountOpt.tCount` does not measure: that function tests the
    syntactic head, so `Rz` of any angle scores zero, including `toReal tAngle`,
    which is a `T` gate written differently. -/
def tCost (q : AngleQ) : Option ℕ :=
  if q.den = 1 || q.den = 2 then some 0
  else if q.den = 4 then some 1
  else none

@[simp] theorem tCost_tAngle : tCost tAngle = some 1 := by simp [tCost, tAngle]

@[simp] theorem tCost_sAngle : tCost sAngle = some 0 := by simp [tCost, sAngle]

@[simp] theorem tCost_zAngle : tCost zAngle = some 0 := by decide

@[simp] theorem tCost_zero : tCost 0 = some 0 := by decide

/-- An angle the fragment realises exactly. -/
def IsCliffordT (q : AngleQ) : Prop := (tCost q).isSome

/-- Whether `q · π` is a Clifford rotation — an integer or half-integer
    multiple of `π`, i.e. a power of `S`. Stated as `2 * q` being an integer,
    the form under which the fragment is visibly closed under composition. -/
def isClifford (q : AngleQ) : Bool := (2 * q).den == 1

/-- The Clifford angles are the half-integers. -/
theorem isClifford_iff_exists_int (q : AngleQ) :
    isClifford q = true ↔ ∃ k : ℤ, 2 * q = (k : ℚ) := by
  simp only [isClifford, beq_iff_eq]
  constructor
  · intro h
    exact ⟨(2 * q).num, ((Rat.den_eq_one_iff _).mp h).symm⟩
  · rintro ⟨k, hk⟩
    rw [hk, Rat.den_intCast]

/-- Composing two Clifford rotations gives a Clifford rotation: the fragment is
    closed under the angle addition that rotation merging performs. -/
theorem isClifford_add {p q : AngleQ} (hp : isClifford p = true)
    (hq : isClifford q = true) : isClifford (p + q) = true := by
  obtain ⟨a, ha⟩ := (isClifford_iff_exists_int p).mp hp
  obtain ⟨b, hb⟩ := (isClifford_iff_exists_int q).mp hq
  refine (isClifford_iff_exists_int _).mpr ⟨a + b, ?_⟩
  push_cast
  linarith

/-- Negating a Clifford rotation gives a Clifford rotation. -/
theorem isClifford_neg {q : AngleQ} (hq : isClifford q = true) :
    isClifford (-q) = true := by
  obtain ⟨a, ha⟩ := (isClifford_iff_exists_int q).mp hq
  refine (isClifford_iff_exists_int _).mpr ⟨-a, ?_⟩
  push_cast
  linarith

theorem isCliffordT_tAngle : IsCliffordT tAngle := by
  simp [IsCliffordT, tCost, tAngle]

/-- A trivial angle costs no `T`: `isTrivial` forces denominator `1`. -/
theorem tCost_of_isTrivial {q : AngleQ} (h : isTrivial q = true) :
    tCost q = some 0 := by
  have hden : q.den = 1 := by
    simpa using (Bool.and_eq_true_iff.mp h).1
  simp [tCost, hden]

/-- The `T` angle is `π/4` radians. -/
theorem toReal_tAngle : toReal tAngle = Real.pi / 4 := by
  simp only [QasmAngle.toReal, tAngle]
  push_cast
  ring

/-- Rotating by the `T` angle is the `T` gate. The two matrices are the same
    `diag (1, e^{iθ})` at the same `θ`, so `Rz` at a Clifford+T angle is that
    gate under another name — which is what `TCountOpt.tCount`, testing the
    syntactic head, cannot see. -/
theorem rzGate_tAngle : QCircuit.rzGate (toReal tAngle) = Programs.Qubit.tGate := by
  rw [toReal_tAngle]
  rfl

/-- A Clifford angle has denominator one or two. -/
theorem den_le_two_of_isClifford {q : AngleQ} (h : isClifford q = true) :
    q.den = 1 ∨ q.den = 2 := by
  obtain ⟨k, hk⟩ := (isClifford_iff_exists_int q).mp h
  have hq : q = Rat.divInt k 2 := by rw [Rat.divInt_eq_div]; push_cast; linarith
  have hdvd : ((q.den : ℤ)) ∣ (2 : ℤ) := by rw [hq]; exact Rat.den_dvd _ _
  have hle : ((q.den : ℤ)) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < q.den := q.den_pos
  omega

/-- The Clifford angles are exactly the ones of zero `T` cost. -/
theorem isClifford_iff_tCost_zero (q : AngleQ) :
    isClifford q = true ↔ tCost q = some 0 := by
  constructor
  · intro h
    rcases den_le_two_of_isClifford h with hd | hd <;> simp [tCost, hd]
  · intro h
    refine (isClifford_iff_exists_int q).mpr ?_
    simp only [tCost] at h
    by_cases h1 : q.den = 1
    · exact ⟨2 * q.num, by
        conv_lhs => rw [← Rat.num_div_den q]
        rw [h1]; push_cast; ring⟩
    · by_cases h2 : q.den = 2
      · exact ⟨q.num, by
          conv_lhs => rw [← Rat.num_div_den q]
          rw [h2]; push_cast; ring⟩
      · exfalso; by_cases h4 : q.den = 4 <;> simp_all

#guard isClifford zAngle
#guard isClifford sAngle
#guard !isClifford tAngle
#guard isClifford (sAngle + sAngle)
#guard !isClifford (tAngle + sAngle)

#guard tCost tAngle == some 1
#guard tCost (tAngle + tAngle) == some 0
#guard tCost (1 / 8 : AngleQ) == none
#guard tCost (3 / 4 : AngleQ) == some 1
#guard tCost (-tAngle) == some 1

end AngleQ

end CatCrypt.Quantum
