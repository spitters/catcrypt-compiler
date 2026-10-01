/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.EcPointGroup
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveAddGeneric
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA

/-!
# EllipticCurve lowering at the Jacobian representation

The lowering of the short-Weierstrass group ops `ECOp.padd` and `ECOp.pdbl` of
`EllipticCurveDialect` to `fieldDialect` programs at the point representation
`PointRepr.jacobian`, generic in the prime `p` and the curve record `C : ECParams p`.
`EllipticCurveLowering` lowers the same ops at the affine representation, with one
field inverse per op; the programs here contain no inverse, so they are covered by the
Montgomery and the Solinas limb lowerings alike.

A Jacobian triple `(X, Y, Z)` represents the point `jacToPoint (X, Y, Z)`: the point at
infinity when `Z = 0`, and the affine point `(X·(Z²)⁻¹, Y·(Z³)⁻¹)` otherwise.

* `jacAddProg p i` is the `add-2007-bl` addition of two general-`Z` triples, returning
  coordinate `i` of `EcProjectiveGeneric.jacAddGen`.
* `jacDblProg p a i` is the `dbl-2007-bl` doubling with curve coefficient `a` entered as
  a field constant, returning coordinate `i` of `EcProjectiveGenericA.jacDoubleGenA a`.

The three programs `i = 0, 1, 2` of each op share one chain of bindings and differ in
the returned variable. Every binding is an addition, subtraction, multiplication,
squaring, doubling or constant, which both limb lowerings cover.

## Value theorems and their preconditions

The op denotation of `padd` is the full group law `ECParams.add`, which equals Mathlib's
`WeierstrassCurve.Affine.Point` addition through `toECPoint_add`.

* Doubling is complete: `pdbl_lowers_to_jacobian` holds for every triple when `p` is an
  odd prime, including triples with `Z = 0` and points of order two, and needs no
  on-curve hypothesis.
* Addition is the incomplete `add-2007-bl` formula. `padd_lowers_to_jacobian` assumes
  both inputs are affine (`Z₁ ≠ 0`, `Z₂ ≠ 0`), on the curve, and represent distinct
  points. Opposite inputs are covered: the output has `Z₃ = 0`. Equal inputs and inputs at
  infinity are outside the precondition; a caller dispatches them to `jacDblProg` or to
  the other operand.

## Main definitions

* `jacToPoint`: the point a Jacobian triple represents.
* `inCtxt6`, `jacVal2`, `inCtxt3`, `jacVal1`: the input contexts and valuations.
* `jacAddBody`, `jacAddProg`: the twenty-three bindings of the addition.
* `jacDblBody`, `jacDblProg`: the twenty-four bindings of the doubling.

## Main results

* `jacAddProg_denote`, `jacDblProg_denote`: coordinate `i` of each program is coordinate
  `i` of `jacAddGen` and `jacDoubleGenA`.
* `padd_lowers_to_jacobian`: under the precondition above, the output triple represents
  `ECParams.add` of the two represented points, the denotation of `ECOp.padd`.
* `pdbl_lowers_to_jacobian`: the output triple of the doubling represents
  `ECParams.add P P`, the denotation of `ECOp.pdbl`.
* `jacAdd_toECPoint`, `jacDbl_toECPoint`: the same statements against Mathlib's point
  addition on `toW C`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric (jacAddGen jacToAffineGen
  jacAddGen_realizes)
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA (jacDoubleGenA)
open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric (ECAffPoint ecAffineAdd
  ecAffineRx ecAffineRy)

variable {p : Nat}

/-! ## 1. The point a Jacobian triple represents -/

/-- The point represented by a Jacobian triple `(X, Y, Z)`: the point at infinity when
    `Z = 0`, and `(X·(Z²)⁻¹, Y·(Z³)⁻¹)` otherwise. -/
def jacToPoint (J : ZMod p × ZMod p × ZMod p) : ECPoint p :=
  if J.2.2 = 0 then none else ECPoint.aff (J.1 * (J.2.2 ^ 2)⁻¹) (J.2.1 * (J.2.2 ^ 3)⁻¹)

theorem jacToPoint_of_eq_zero {J : ZMod p × ZMod p × ZMod p} (h : J.2.2 = 0) :
    jacToPoint J = none := if_pos h

theorem jacToPoint_of_ne_zero {J : ZMod p × ZMod p × ZMod p} (h : J.2.2 ≠ 0) :
    jacToPoint J = ECPoint.aff (J.1 * (J.2.2 ^ 2)⁻¹) (J.2.1 * (J.2.2 ^ 3)⁻¹) := if_neg h

/-! ## 2. Inputs, variables and bindings -/

/-- The input context of the addition: `X₁, Y₁, Z₁, X₂, Y₂, Z₂`, the first at the head. -/
abbrev inCtxt6 (p : Nat) : Ctxt fieldDialect := List.replicate 6 (FieldTy.fp p)

/-- The input context of the doubling: `X, Y, Z`, the first at the head. -/
abbrev inCtxt3 (p : Nat) : Ctxt fieldDialect := List.replicate 3 (FieldTy.fp p)

/-- The valuation of two Jacobian triples. -/
def jacVal2 (J1 J2 : ZMod p × ZMod p × ZMod p) : Valuation (inCtxt6 p) :=
  .cons J1.1 (.cons J1.2.1 (.cons J1.2.2 (.cons J2.1 (.cons J2.2.1 (.cons J2.2.2 .nil)))))

/-- The valuation of one Jacobian triple. -/
def jacVal1 (J : ZMod p × ZMod p × ZMod p) : Valuation (inCtxt3 p) :=
  .cons J.1 (.cons J.2.1 (.cons J.2.2 .nil))

namespace JacLower

/-- The variable `n` bindings from the top of a context of field elements at `p`. -/
def vAt (p : Nat) : (n : Nat) → {Γ : Ctxt fieldDialect} →
    @Var fieldDialect (List.replicate (n + 1) (FieldTy.fp p) ++ Γ) (FieldTy.fp p)
  | 0, _ => .here
  | n + 1, _ => (vAt p n).there

variable {Γ : Ctxt fieldDialect}

/-- The binding `a + b`. -/
def eAdd (a b : Var Γ (FieldTy.fp p)) : Expr fieldDialect Γ (FieldTy.fp p) :=
  ⟨.fAdd p, rfl, .cons a (.cons b .nil)⟩

/-- The binding `a − b`. -/
def eSub (a b : Var Γ (FieldTy.fp p)) : Expr fieldDialect Γ (FieldTy.fp p) :=
  ⟨.fSub p, rfl, .cons a (.cons b .nil)⟩

/-- The binding `a · b`. -/
def eMul (a b : Var Γ (FieldTy.fp p)) : Expr fieldDialect Γ (FieldTy.fp p) :=
  ⟨.fMul p, rfl, .cons a (.cons b .nil)⟩

/-- The binding `a · a`. -/
def eSq (a : Var Γ (FieldTy.fp p)) : Expr fieldDialect Γ (FieldTy.fp p) :=
  ⟨.fieldSquare p, rfl, .cons a .nil⟩

/-- The binding `a + a`. -/
def eDbl (a : Var Γ (FieldTy.fp p)) : Expr fieldDialect Γ (FieldTy.fp p) :=
  ⟨.fieldDouble p, rfl, .cons a .nil⟩

/-- The binding of the constant `c`. -/
def eConst (c : ZMod p) : Expr fieldDialect Γ (FieldTy.fp p) :=
  ⟨.fConst p c, rfl, .nil⟩

end JacLower

open JacLower

/-! ## 3. The addition `add-2007-bl` -/

/-- The context after the twenty-three bindings of the addition. -/
abbrev addOutCtxt (p : Nat) : Ctxt fieldDialect :=
  List.replicate 23 (FieldTy.fp p) ++ inCtxt6 p

/-- The twenty-three bindings of the `add-2007-bl` addition, followed by the
    continuation `k`: `Z₁²`, `Z₂²`, `U₁`, `U₂`, `Z₂³`, `S₁`, `Z₁³`, `S₂`, `H`, `r`, `H²`,
    `H³`, `V`, `r²`, `r² − H³`, `2V`, `X₃`, `V − X₃`, `r·(V − X₃)`, `S₁·H³`, `Y₃`,
    `Z₁·Z₂`, `Z₃`. -/
def jacAddBody (p : Nat) {s : FieldTy} (k : Com fieldDialect (addOutCtxt p) s) :
    Com fieldDialect (inCtxt6 p) s :=
  .var (eSq (vAt p 2)) <|
  .var (eSq (vAt p 6)) <|
  .var (eMul (vAt p 2) (vAt p 0)) <|
  .var (eMul (vAt p 6) (vAt p 2)) <|
  .var (eMul (vAt p 9) (vAt p 2)) <|
  .var (eMul (vAt p 6) (vAt p 0)) <|
  .var (eMul (vAt p 8) (vAt p 5)) <|
  .var (eMul (vAt p 11) (vAt p 0)) <|
  .var (eSub (vAt p 4) (vAt p 5)) <|
  .var (eSub (vAt p 1) (vAt p 3)) <|
  .var (eSq (vAt p 1)) <|
  .var (eMul (vAt p 2) (vAt p 0)) <|
  .var (eMul (vAt p 9) (vAt p 1)) <|
  .var (eSq (vAt p 3)) <|
  .var (eSub (vAt p 0) (vAt p 2)) <|
  .var (eDbl (vAt p 2)) <|
  .var (eSub (vAt p 1) (vAt p 0)) <|
  .var (eSub (vAt p 4) (vAt p 0)) <|
  .var (eMul (vAt p 8) (vAt p 0)) <|
  .var (eMul (vAt p 13) (vAt p 7)) <|
  .var (eSub (vAt p 1) (vAt p 0)) <|
  .var (eMul (vAt p 23) (vAt p 26)) <|
  .var (eMul (vAt p 0) (vAt p 13)) <|
  k

/-- The variable of output coordinate `i` of the addition: the bindings `X₃`, `Y₃`,
    `Z₃`. -/
def addOutVar (p : Nat) : Fin 3 → Var (addOutCtxt p) (FieldTy.fp p)
  | 0 => vAt p 6
  | 1 => vAt p 2
  | 2 => vAt p 0

/-- The `add-2007-bl` addition of two Jacobian triples, returning coordinate `i` of
    `X₃, Y₃, Z₃`. -/
def jacAddProg (p : Nat) (i : Fin 3) : Com fieldDialect (inCtxt6 p) (FieldTy.fp p) :=
  jacAddBody p (.ret (addOutVar p i))

/-- Coordinate `i` of a triple. -/
def coord {α : Type} (T : α × α × α) : Fin 3 → α
  | 0 => T.1
  | 1 => T.2.1
  | 2 => T.2.2

/-- The output of the addition, binding by binding. -/
def jacAddOps (J1 J2 : ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p :=
  let z1z1 := J1.2.2 * J1.2.2
  let z2z2 := J2.2.2 * J2.2.2
  let u1 := J1.1 * z2z2
  let u2 := J2.1 * z1z1
  let z2c := J2.2.2 * z2z2
  let s1 := J1.2.1 * z2c
  let z1c := J1.2.2 * z1z1
  let s2 := J2.2.1 * z1c
  let h := u2 - u1
  let r := s2 - s1
  let hh := h * h
  let hhh := h * hh
  let v := u1 * hh
  let rr := r * r
  let t1 := rr - hhh
  let v2 := v + v
  let x3 := t1 - v2
  let t2 := v - x3
  let t3 := r * t2
  let t4 := s1 * hhh
  let y3 := t3 - t4
  let t5 := J1.2.2 * J2.2.2
  (x3, y3, t5 * h)

theorem jacAddProg_denote_ops (J1 J2 : ZMod p × ZMod p × ZMod p) (i : Fin 3) :
    (jacAddProg p i).denote (jacVal2 J1 J2) = coord (jacAddOps J1 J2) i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem jacAddOps_eq [Fact p.Prime] (J1 J2 : ZMod p × ZMod p × ZMod p) :
    jacAddOps J1 J2 = jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2 := by
  simp only [jacAddOps, jacAddGen, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- **Value of the addition program.** Coordinate `i` of `jacAddProg p i` is coordinate
    `i` of the `add-2007-bl` formula `jacAddGen`. -/
theorem jacAddProg_denote [Fact p.Prime] (J1 J2 : ZMod p × ZMod p × ZMod p) (i : Fin 3) :
    (jacAddProg p i).denote (jacVal2 J1 J2)
      = coord (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2) i := by
  rw [jacAddProg_denote_ops, jacAddOps_eq]

/-! ## 4. The doubling `dbl-2007-bl` -/

/-- The context after the twenty-four bindings of the doubling. -/
abbrev dblOutCtxt (p : Nat) : Ctxt fieldDialect :=
  List.replicate 24 (FieldTy.fp p) ++ inCtxt3 p

/-- The twenty-four bindings of the `dbl-2007-bl` doubling with curve coefficient `a`,
    followed by the continuation `k`: `X²`, `Y²`, `Y⁴`, `Z²`, `Z⁴`, `a`, `a·Z⁴`, `2X²`,
    `3X²`, `M`, `X·Y²`, `2X·Y²`, `S`, `M²`, `2S`, `X'`, `S − X'`, `M·(S − X')`, `2Y⁴`,
    `4Y⁴`, `8Y⁴`, `Y'`, `Y·Z`, `Z'`. -/
def jacDblBody (p : Nat) (a : ZMod p) {s : FieldTy} (k : Com fieldDialect (dblOutCtxt p) s) :
    Com fieldDialect (inCtxt3 p) s :=
  .var (eSq (vAt p 0)) <|
  .var (eSq (vAt p 2)) <|
  .var (eSq (vAt p 0)) <|
  .var (eSq (vAt p 5)) <|
  .var (eSq (vAt p 0)) <|
  .var (eConst a) <|
  .var (eMul (vAt p 0) (vAt p 1)) <|
  .var (eDbl (vAt p 6)) <|
  .var (eAdd (vAt p 0) (vAt p 7)) <|
  .var (eAdd (vAt p 0) (vAt p 2)) <|
  .var (eMul (vAt p 10) (vAt p 8)) <|
  .var (eDbl (vAt p 0)) <|
  .var (eDbl (vAt p 0)) <|
  .var (eSq (vAt p 3)) <|
  .var (eDbl (vAt p 1)) <|
  .var (eSub (vAt p 1) (vAt p 0)) <|
  .var (eSub (vAt p 3) (vAt p 0)) <|
  .var (eMul (vAt p 7) (vAt p 0)) <|
  .var (eDbl (vAt p 15)) <|
  .var (eDbl (vAt p 0)) <|
  .var (eDbl (vAt p 0)) <|
  .var (eSub (vAt p 3) (vAt p 0)) <|
  .var (eMul (vAt p 23) (vAt p 24)) <|
  .var (eDbl (vAt p 0)) <|
  k

/-- The variable of output coordinate `i` of the doubling: the bindings `X'`, `Y'`,
    `Z'`. -/
def dblOutVar (p : Nat) : Fin 3 → Var (dblOutCtxt p) (FieldTy.fp p)
  | 0 => vAt p 8
  | 1 => vAt p 2
  | 2 => vAt p 0

/-- The `dbl-2007-bl` doubling of a Jacobian triple at curve coefficient `a`, returning
    coordinate `i` of `X', Y', Z'`. -/
def jacDblProg (p : Nat) (a : ZMod p) (i : Fin 3) :
    Com fieldDialect (inCtxt3 p) (FieldTy.fp p) :=
  jacDblBody p a (.ret (dblOutVar p i))

/-- The output of the doubling, binding by binding. -/
def jacDblOps (a : ZMod p) (J : ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p :=
  let xx := J.1 * J.1
  let yy := J.2.1 * J.2.1
  let yyyy := yy * yy
  let zz := J.2.2 * J.2.2
  let z4 := zz * zz
  let az4 := a * z4
  let xx2 := xx + xx
  let xx3 := xx2 + xx
  let m := xx3 + az4
  let xyy := J.1 * yy
  let s2 := xyy + xyy
  let s := s2 + s2
  let mm := m * m
  let s2x := s + s
  let x3 := mm - s2x
  let d := s - x3
  let md := m * d
  let y2 := yyyy + yyyy
  let y4 := y2 + y2
  let y8 := y4 + y4
  let yz := J.2.1 * J.2.2
  (x3, md - y8, yz + yz)

theorem jacDblProg_denote_ops (a : ZMod p) (J : ZMod p × ZMod p × ZMod p) (i : Fin 3) :
    (jacDblProg p a i).denote (jacVal1 J) = coord (jacDblOps a J) i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem jacDblOps_eq [Fact p.Prime] (a : ZMod p) (J : ZMod p × ZMod p × ZMod p) :
    jacDblOps a J = jacDoubleGenA a J.1 J.2.1 J.2.2 := by
  simp only [jacDblOps, jacDoubleGenA, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- **Value of the doubling program.** Coordinate `i` of `jacDblProg p a i` is
    coordinate `i` of the `dbl-2007-bl` formula `jacDoubleGenA a`. -/
theorem jacDblProg_denote [Fact p.Prime] (a : ZMod p) (J : ZMod p × ZMod p × ZMod p) (i : Fin 3) :
    (jacDblProg p a i).denote (jacVal1 J) = coord (jacDoubleGenA a J.1 J.2.1 J.2.2) i := by
  rw [jacDblProg_denote_ops, jacDblOps_eq]

/-! ## 5. The group law -/

section GroupLaw

variable [hp : Fact p.Prime]

/-- **The doubling lowers `pdbl`.** For an odd prime `p` and every Jacobian triple `J`,
    the output of `dbl-2007-bl` at `a = C.a` represents `C.add P P`, the denotation of
    `ECOp.pdbl` at the represented point `P`. The statement has no exceptional case. -/
theorem pdbl_lowers_to_jacobian (hp2 : p ≠ 2) (C : ECParams p)
    (J : ZMod p × ZMod p × ZMod p) :
    jacToPoint (jacDoubleGenA C.a J.1 J.2.1 J.2.2) = pdblF C (jacToPoint J) := by
  obtain ⟨X, Y, Z⟩ := J
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  by_cases hZ : Z = 0
  · rw [jacToPoint_of_eq_zero (J := (X, Y, Z)) hZ, jacToPoint_of_eq_zero]
    · rfl
    · simp [jacDoubleGenA, hZ]
  rw [jacToPoint_of_ne_zero (J := (X, Y, Z)) hZ]
  simp only [pdblF, ECPoint.aff, ECParams.add, if_true]
  by_cases hY : Y = 0
  · rw [jacToPoint_of_eq_zero (by simp [jacDoubleGenA, hY]), if_pos (by simp [hY])]
  have hyy : ¬ (Y * (Z ^ 3)⁻¹ = -(Y * (Z ^ 3)⁻¹)) := by
    intro h
    have h' : (2 : ZMod p) * (Y * (Z ^ 3)⁻¹) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h2 h''
    · exact hY (by simpa [hZ] using h'')
  rw [if_neg hyy, jacToPoint_of_ne_zero (by simp [jacDoubleGenA, h2, hY, hZ])]
  simp only [ECPoint.aff, ECParams.tangentSlope, ECParams.affRx, ECParams.affRy,
    jacDoubleGenA, Option.some.injEq, Prod.mk.injEq]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **The addition lowers `padd`.** For affine triples `J₁`, `J₂` (`Z₁ ≠ 0`, `Z₂ ≠ 0`)
    whose represented points are on the curve and distinct, the output of `add-2007-bl`
    represents `C.add P₁ P₂`, the denotation of `ECOp.padd`. Opposite inputs give an
    output with `Z₃ = 0`, which represents the point at infinity. -/
theorem padd_lowers_to_jacobian (C : ECParams p) (J1 J2 : ZMod p × ZMod p × ZMod p)
    (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : C.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : C.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) :
    jacToPoint (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2)
      = paddF C (jacToPoint J1) (jacToPoint J2) := by
  obtain ⟨X1, Y1, Z1⟩ := J1
  obtain ⟨X2, Y2, Z2⟩ := J2
  simp only at hZ1 hZ2 hC1 hC2
  rw [jacToPoint_of_ne_zero (J := (X1, Y1, Z1)) hZ1,
    jacToPoint_of_ne_zero (J := (X2, Y2, Z2)) hZ2] at hne ⊢
  simp only [paddF, ECPoint.aff, ECParams.add]
  simp only [ECPoint.aff, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and] at hne
  by_cases hx : X1 * (Z1 ^ 2)⁻¹ = X2 * (Z2 ^ 2)⁻¹
  · -- Equal abscissae: the points are opposite, and `H = 0` gives `Z₃ = 0`.
    have hy : Y1 * (Z1 ^ 3)⁻¹ = -(Y2 * (Z2 ^ 3)⁻¹) := by
      have hne' := hne hx
      have hsq : (Y1 * (Z1 ^ 3)⁻¹ - Y2 * (Z2 ^ 3)⁻¹)
          * (Y1 * (Z1 ^ 3)⁻¹ + Y2 * (Z2 ^ 3)⁻¹) = 0 := by
        unfold ECParams.onCurve at hC1 hC2
        rw [hx] at hC1
        linear_combination hC1 - hC2
      rcases mul_eq_zero.mp hsq with h | h
      · exact absurd (sub_eq_zero.mp h) hne'
      · exact eq_neg_of_add_eq_zero_left h
    rw [if_pos hx, if_pos hy, jacToPoint_of_eq_zero]
    have hH : X2 * Z1 ^ 2 - X1 * Z2 ^ 2 = 0 := by
      field_simp at hx
      linear_combination -hx
    simp only [jacAddGen]
    rw [hH, mul_zero]
  · -- Distinct abscissae: the chord branch.
    have hH : X2 * Z1 ^ 2 - X1 * Z2 ^ 2 ≠ 0 := by
      intro h
      apply hx
      field_simp
      linear_combination -h
    have hZ3 : (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 ≠ 0 := by
      simp only [jacAddGen]
      exact mul_ne_zero (mul_ne_zero hZ1 hZ2) hH
    have hr := jacAddGen_realizes X1 Y1 Z1 X2 Y2 Z2 hZ1 hZ2 hH hZ3
    rw [if_neg hx, jacToPoint_of_ne_zero hZ3]
    have hrx := congrArg ECAffPoint.x hr
    have hry := congrArg ECAffPoint.y hr
    simp only [jacToAffineGen, ecAffineAdd, ecAffineRx, ecAffineRy] at hrx hry
    simp only [ECPoint.aff, ECParams.chordSlope, ECParams.affRx, ECParams.affRy,
      Option.some.injEq, Prod.mk.injEq]
    exact ⟨hrx, hry⟩

/-- The doubling against Mathlib's point addition: if `J` represents the Mathlib point
    `P` of `toW C`, the output of `dbl-2007-bl` represents `P + P`. -/
theorem jacDbl_toECPoint (hp2 : p ≠ 2) (C : ECParams p) (J : ZMod p × ZMod p × ZMod p)
    (P : (toW C).toAffine.Point) (hP : jacToPoint J = toECPoint C P) :
    jacToPoint (jacDoubleGenA C.a J.1 J.2.1 J.2.2) = toECPoint C (P + P) := by
  rw [pdbl_lowers_to_jacobian hp2 C J, toECPoint_add, hP]

/-- The addition against Mathlib's point addition: if affine triples `J₁`, `J₂` represent
    distinct Mathlib points `P`, `Q` of `toW C`, the output of `add-2007-bl` represents
    `P + Q`. -/
theorem jacAdd_toECPoint (C : ECParams p) (J1 J2 : ZMod p × ZMod p × ZMod p)
    (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0) (P Q : (toW C).toAffine.Point)
    (hP : jacToPoint J1 = toECPoint C P) (hQ : jacToPoint J2 = toECPoint C Q)
    (hPQ : P ≠ Q) :
    jacToPoint (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2) = toECPoint C (P + Q) := by
  have hon : ∀ (J : ZMod p × ZMod p × ZMod p) (R : (toW C).toAffine.Point), J.2.2 ≠ 0 →
      jacToPoint J = toECPoint C R →
      C.onCurve (J.1 * (J.2.2 ^ 2)⁻¹) (J.2.1 * (J.2.2 ^ 3)⁻¹) := by
    intro J R hZ hR
    rw [jacToPoint_of_ne_zero hZ] at hR
    cases R with
    | zero => exact absurd hR (Option.some_ne_none _)
    | @some x y h =>
      simp only [toECPoint_some, ECPoint.aff, Option.some.injEq, Prod.mk.injEq] at hR
      rw [hR.1, hR.2]
      exact onCurve_of_nonsingular C h
  have hne : jacToPoint J1 ≠ jacToPoint J2 := by
    rw [hP, hQ]
    exact fun h => hPQ (toECPoint_injective C h)
  rw [padd_lowers_to_jacobian C J1 J2 hZ1 hZ2 (hon J1 P hZ1 hP) (hon J2 Q hZ2 hQ) hne,
    toECPoint_add, hP, hQ]

end GroupLaw

end CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
