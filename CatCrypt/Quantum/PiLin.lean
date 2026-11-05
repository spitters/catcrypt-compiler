/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QasmAngle
public import Transfer.Statements.ParamTransferTac
public import Transfer.Base.RelatedOn
public import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Exact angles `a + b·π`

`PiLin` is the pair `(a, b)` of rationals read as the real angle `a + b·π`. It
contains the angles `q·π` of `QasmAngle` (`PiLin.ofPi`) and the rational
radians a decimal OpenQASM literal denotes, and it is closed under addition and
negation. Since `π` is irrational, `PiLin.toReal` is injective, so equality of
angles, being a whole number of turns and being a multiple of `π/4` are decided
on the two rationals.

## Numerals and the coercion from `QasmAngle`

A numeral and a cast of a natural number, an integer or a `QasmAngle` denote
multiples of `π`: `(1 : PiLin) = ofPi 1` is `π`, and the coercion
`QasmAngle → PiLin` is `ofPi`. Division `p / q` divides both parts of `p` by
the `π`-coefficient of `q`, so on the image of `ofPi` it is the division of
`QasmAngle` (`ofPi_div_ofPi`), and division by a numeral `n` divides the real
angle by `n` (`toReal_div_ofPi`). An expression such as `1 / 4`, `-(1 / 2)` or
`a / 2` with `a : QasmAngle`, written where a `PiLin` is expected, therefore
denotes the same angle `q·π` it denoted as a `QasmAngle`, and `simp` rewrites
it to `ofPi q`.

## Transfer

The real angle is related to its `PiLin` representation by `toReal p = θ`. The
relation is registered as a ParamTransfer domain, so `piLinForallTransfer`
carries a statement about every real angle to one about every `PiLin`, and the
squares `RelatedBinOp`, `RelatedUnOp`, `Related` and `RelatedRelOn` state that
addition, negation, `ofPi` and the congruence modulo `2π` agree on both sides.

## Main definitions

* `PiLin`, `PiLin.toReal`, `PiLin.ofPi`.
* `PiLin.isTrivial` — a whole number of turns; `PiLin.isPiQuarterMul` — a
  multiple of `π/4`; `PiLin.tCost` — the `T` count of a phase.
* `piLinDom`, `instTransferDomPiLin` — the transfer domain `ℝ ⇀ PiLin`.

## Main results

* `PiLin.toReal_injective`, from `irrational_pi`.
* `PiLin.isTrivial_iff`, `PiLin.isPiQuarterMul_iff`.
* `piLinForallTransfer`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum

open Transfer Transfer.Param

/-- An angle `a + b·π` with rational `a` (radians) and `b` (multiples of `π`). -/
@[ext]
structure PiLin where
  /-- The rational part, in radians. -/
  a : ℚ
  /-- The coefficient of `π`. -/
  b : ℚ
  deriving DecidableEq, Repr

namespace PiLin

/-- The real angle `a + b·π`. -/
noncomputable def toReal (p : PiLin) : ℝ := (p.a : ℝ) + (p.b : ℝ) * Real.pi

/-- The angle `q·π`, the reading of a `QasmAngle`. -/
@[coe] def ofPi (q : QasmAngle) : PiLin := ⟨0, q⟩

/-- A `QasmAngle` `q` is the angle `q·π`. -/
instance : Coe QasmAngle PiLin := ⟨ofPi⟩

instance : Zero PiLin := ⟨⟨0, 0⟩⟩
instance : One PiLin := ⟨ofPi 1⟩
instance : NatCast PiLin := ⟨fun n => ofPi n⟩
instance : IntCast PiLin := ⟨fun k => ofPi k⟩
instance (n : ℕ) [n.AtLeastTwo] : OfNat PiLin n := ⟨ofPi (OfNat.ofNat n)⟩
instance : Add PiLin := ⟨fun p q => ⟨p.a + q.a, p.b + q.b⟩⟩
instance : Neg PiLin := ⟨fun p => ⟨-p.a, -p.b⟩⟩
instance : Sub PiLin := ⟨fun p q => ⟨p.a - q.a, p.b - q.b⟩⟩
/-- Division by the `π`-coefficient of the divisor. -/
instance : Div PiLin := ⟨fun p q => ⟨p.a / q.b, p.b / q.b⟩⟩

@[simp] theorem zero_a : (0 : PiLin).a = 0 := rfl
@[simp] theorem zero_b : (0 : PiLin).b = 0 := rfl
@[simp] theorem add_a (p q : PiLin) : (p + q).a = p.a + q.a := rfl
@[simp] theorem add_b (p q : PiLin) : (p + q).b = p.b + q.b := rfl
@[simp] theorem neg_a (p : PiLin) : (-p).a = -p.a := rfl
@[simp] theorem neg_b (p : PiLin) : (-p).b = -p.b := rfl
@[simp] theorem sub_a (p q : PiLin) : (p - q).a = p.a - q.a := rfl
@[simp] theorem sub_b (p q : PiLin) : (p - q).b = p.b - q.b := rfl
@[simp] theorem div_a (p q : PiLin) : (p / q).a = p.a / q.b := rfl
@[simp] theorem div_b (p q : PiLin) : (p / q).b = p.b / q.b := rfl
@[simp] theorem ofPi_a (q : QasmAngle) : (ofPi q).a = 0 := rfl
@[simp] theorem ofPi_b (q : QasmAngle) : (ofPi q).b = q := rfl

/-! The simp lemmas below rewrite a numeral expression of `PiLin` to `ofPi q`, with
`q` the `QasmAngle` the expression denotes. -/

/-- The numeral `1` is the angle `π`. -/
@[simp] theorem one_eq_ofPi : (1 : PiLin) = ofPi 1 := rfl

/-- A numeral `n ≥ 2` is the angle `n·π`. -/
@[simp] theorem ofNat_eq_ofPi (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : PiLin) = ofPi (OfNat.ofNat n) := rfl

/-- The cast of a natural number `n` is the angle `n·π`. -/
@[simp] theorem natCast_eq_ofPi (n : ℕ) : (n : PiLin) = ofPi n := rfl

/-- The cast of an integer `k` is the angle `k·π`. -/
@[simp] theorem intCast_eq_ofPi (k : ℤ) : (k : PiLin) = ofPi k := rfl

/-- `ofPi` commutes with addition. -/
@[simp] theorem ofPi_add_ofPi (x y : QasmAngle) : ofPi x + ofPi y = ofPi (x + y) := by
  ext <;> simp

/-- `ofPi` commutes with negation. -/
@[simp] theorem neg_ofPi (x : QasmAngle) : -ofPi x = ofPi (-x) := by
  ext <;> simp

/-- `ofPi` commutes with subtraction. -/
@[simp] theorem ofPi_sub_ofPi (x y : QasmAngle) : ofPi x - ofPi y = ofPi (x - y) := by
  ext <;> simp

/-- On the image of `ofPi`, division is the division of `QasmAngle`. -/
@[simp] theorem ofPi_div_ofPi (x y : QasmAngle) : ofPi x / ofPi y = ofPi (x / y) := by
  ext <;> simp

@[simp] theorem toReal_zero : toReal 0 = 0 := by simp [toReal]

@[simp] theorem toReal_add (p q : PiLin) : toReal (p + q) = toReal p + toReal q := by
  simp only [toReal, add_a, add_b]; push_cast; ring

@[simp] theorem toReal_neg (p : PiLin) : toReal (-p) = -toReal p := by
  simp only [toReal, neg_a, neg_b]; push_cast; ring

@[simp] theorem toReal_sub (p q : PiLin) : toReal (p - q) = toReal p - toReal q := by
  simp only [toReal, sub_a, sub_b]; push_cast; ring

@[simp] theorem toReal_ofPi (q : QasmAngle) : toReal (ofPi q) = (q : ℝ) * Real.pi := by
  simp [toReal]

/-- Division by the angle `y·π` divides the real angle by `y`. -/
theorem toReal_div_ofPi (p : PiLin) (y : QasmAngle) :
    toReal (p / ofPi y) = toReal p / y := by
  simp only [toReal, div_a, div_b, ofPi_b]; push_cast; ring

/-- `ofPi` agrees with the real reading of `QasmAngle`. -/
theorem toReal_ofPi_eq_qasm (q : QasmAngle) : toReal (ofPi q) = QasmAngle.toReal q := by
  simp [QasmAngle.toReal]

/-- A rational combination `a + b·π` vanishes only when both rationals do. -/
theorem eq_zero_of_toReal_eq_zero {p : PiLin} (h : toReal p = 0) : p = 0 := by
  have hb : p.b = 0 := by
    by_contra hb
    exact ((irrational_pi.ratCast_mul hb).ratCast_add (q := p.a)).ne_zero h
  have ha : p.a = 0 := by
    simpa [toReal, hb] using h
  ext <;> simp [ha, hb]

/-- `toReal` is injective: `a + b·π` determines `a` and `b`. -/
theorem toReal_injective : Function.Injective toReal := by
  intro p q h
  have h0 : p - q = 0 := eq_zero_of_toReal_eq_zero (by rw [toReal_sub, h, sub_self])
  ext
  · have := congrArg PiLin.a h0; simp only [sub_a, zero_a] at this; linarith
  · have := congrArg PiLin.b h0; simp only [sub_b, zero_b] at this; linarith

/-! ## Decidable angle tests -/

/-- Whether `a + b·π` is a whole number of turns: `a = 0` and `b / 2` an integer. -/
def isTrivial (p : PiLin) : Bool := p.a == 0 && (p.b / 2).den == 1

/-- `isTrivial` decides membership in `2πℤ`. -/
theorem isTrivial_iff (p : PiLin) :
    isTrivial p = true ↔ ∃ k : ℤ, toReal p = 2 * Real.pi * k := by
  simp only [isTrivial, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨ha, hd⟩
    refine ⟨(p.b / 2).num, ?_⟩
    have hq : (((p.b / 2).num : ℤ) : ℝ) = (p.b : ℝ) / 2 := by
      have h := Rat.coe_int_num_of_den_eq_one hd
      exact_mod_cast h
    rw [hq]; simp [toReal, ha]; ring
  · rintro ⟨k, hk⟩
    have hp : p = ofPi (2 * k) := toReal_injective (by rw [hk, toReal_ofPi]; push_cast; ring)
    refine ⟨by rw [hp]; rfl, ?_⟩
    rw [hp, ofPi_b, show (2 : ℚ) * k / 2 = (k : ℚ) by ring]
    exact Rat.den_intCast k

/-- Whether `a + b·π` is a multiple of `π/4`: `a = 0` and `4b` an integer. -/
def isPiQuarterMul (p : PiLin) : Bool := p.a == 0 && (4 * p.b).den == 1

/-- `isPiQuarterMul` decides membership in `(π/4)ℤ`. -/
theorem isPiQuarterMul_iff (p : PiLin) :
    isPiQuarterMul p = true ↔ ∃ k : ℤ, toReal p = k * (Real.pi / 4) := by
  simp only [isPiQuarterMul, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨ha, hd⟩
    refine ⟨(4 * p.b).num, ?_⟩
    have hq : (((4 * p.b).num : ℤ) : ℝ) = 4 * (p.b : ℝ) := by
      have h := Rat.coe_int_num_of_den_eq_one hd
      exact_mod_cast h
    rw [hq]; simp [toReal, ha]; ring
  · rintro ⟨k, hk⟩
    have hp : p = ofPi (k / 4) := toReal_injective (by rw [hk, toReal_ofPi]; push_cast; ring)
    refine ⟨by rw [hp]; rfl, ?_⟩
    rw [hp, ofPi_b, show (4 : ℚ) * (k / 4) = (k : ℚ) by ring]
    exact Rat.den_intCast k

/-- The `T` count of a phase, as `TCountOpt.gateTCost` counts `T` and `Tdg`: one
    for an odd multiple of `π/4`, zero otherwise. -/
def tCost (p : PiLin) : ℕ := if p.a = 0 ∧ p.b.den = 4 then 1 else 0

end PiLin

/-! ## The transfer domain -/

/-- The representation change `ℝ ⇀ PiLin` at the level `forallTransfer` consumes:
    a real `θ` and `p` are related when `toReal p = θ`. Forward is nothing, since
    most reals have no `PiLin` form; backward is `toReal`. -/
noncomputable def piLinDom : Param .map0 .map2a ℝ PiLin where
  R θ p := PiLin.toReal p = θ
  fwd := ⟨⟩
  bwd := ⟨PiLin.toReal, fun _ _ h => by subst h; rfl⟩

/-- The `PiLin` representation change resolves for `param_transfer`. -/
noncomputable instance instTransferDomPiLin : TransferDom ℝ PiLin where
  dom := piLinDom

/-- A statement about every real angle transfers to one about every `PiLin`. -/
theorem piLinForallTransfer {P : ℝ → Prop} {P' : PiLin → Prop}
    (PB : ∀ (θ : ℝ) (p : PiLin), PiLin.toReal p = θ → (P θ → P' p)) :
    (∀ θ : ℝ, P θ) → (∀ p : PiLin, P' p) :=
  forallTransfer piLinDom PB

/-- Addition of `PiLin` realizes real addition along `toReal`. -/
instance PiLin.relatedAdd : RelatedBinOp PiLin.toReal (· + ·) (· + ·) where
  comm := PiLin.toReal_add

/-- Negation of `PiLin` realizes real negation along `toReal`. -/
instance PiLin.relatedNeg : RelatedUnOp PiLin.toReal Neg.neg Neg.neg where
  comm := PiLin.toReal_neg

/-- `ofPi q` encodes the real angle `q·π`. -/
instance PiLin.relatedOfPi (q : QasmAngle) :
    Related PiLin.toReal (PiLin.ofPi q) ((q : ℝ) * Real.pi) where
  rel := PiLin.toReal_ofPi q

/-- Congruence modulo two turns, decided by `isTrivial` of the difference, agrees
    with congruence of the real angles modulo `2πℤ`. -/
instance PiLin.relatedCongrTwoPi :
    RelatedRelOn PiLin.toReal (fun _ _ => True)
      (fun p q => PiLin.isTrivial (p - q) = true)
      (fun θ φ => ∃ k : ℤ, θ - φ = 2 * Real.pi * k) where
  iff x y _ := by rw [PiLin.isTrivial_iff, PiLin.toReal_sub]

end CatCrypt.Quantum
