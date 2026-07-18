/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp6
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377EC

/-!
# The `bls12_377` Miller-loop LINE FUNCTION, valued in the `Fp12` tower

`RelationalFrontBls377Fp6` closes the `bls12_377` tower fields
`Fp2_377 ⊂ Fp6_377 ⊂ Fp12_377` (each with a `CommRing` and a
Karatsuba-equals-schoolbook multiply). `RelationalFrontBls377EC` carries the
`G1` affine short-Weierstrass arithmetic — the chord/tangent slope maps and the
affine point-add/double — over the `bls12_377` base field `FpBLS377 = ZMod
bls377Q`. The next building block toward the **optimal-Ate pairing** is the
per-step *line function* the Miller loop accumulates: at each doubling (or
addition) step the loop multiplies the running pairing value by the value of the
line through the current accumulator point, evaluated at the other input point,
and that value lives in the pairing field `Fp12_377`.

This module builds that line-function value as a well-defined `Fp12_377` element,
plus the per-step Miller update `f ← f² · ℓ`, and proves the one structural
algebraic fact that closes cleanly: **the line through `R` vanishes at `R`**
(`lineTangent` / `lineChord` evaluated at the defining point is `0 : Fp12_377`).

## The base-field-into-`Fp12` embedding `ofBase`

A `G1` point and the optimal-Ate base-field model both have base-field
coordinates; the line value lives in `Fp12_377`. We embed a base-field scalar
`t : FpBLS377` as the `Fp12_377` element `t + 0·u + 0·v + 0·w` via `ofBase`. We
prove `ofBase` preserves `0`, `1`, `+`, `-`, and `*` (`ofBase_zero`,
`ofBase_one`, `ofBase_add`, `ofBase_sub`, `ofBase_mul`) — i.e. it is a ring
homomorphism into the `Fp12_377` `CommRing`. (`ofBase_mul` is the one that needs
the tower `CommRing` in scope; the others are componentwise and `ξ`-independent.)

## The line functions (tangent / chord), parameterized by the slope

Mirroring `RelationalFrontBls377EC`'s `bls377AffineAdd`/`bls377AffineDbl`, which
take the precomputed slope `λ : FpBLS377` as a parameter (so no field inverse
appears in the algebra), the line functions take the slope as a base-field
parameter:

* `lineTangent λ R (x, y)` — the value of the tangent line at `R` (slope `λ =
  3xR²/(2yR)`) evaluated at the affine point `(x, y)`:
  `ℓ_R(x,y) = (y − yR) − λ·(x − xR)`, every coordinate embedded by `ofBase`.
* `lineChord λ P Q (x, y)` — the value of the chord through `P` and `Q` (slope
  `λ = (yQ − yP)/(xQ − xP)`) evaluated at `(x, y)`:
  `ℓ_{P,Q}(x,y) = (y − yP) − λ·(x − xP)`.

Both are honest `Fp12_377` elements (the value the Miller loop multiplies in).
The slope is the *same* `λ : FpBLS377` the EC module computes — so this is the
genuine pairing line function, not a re-encoding.

## The Miller per-step update

`millerStep f ℓ = f · f · ℓ` is the doubling step `f ← f²·ℓ` of the
doubling-and-add Miller loop, over the `Fp12_377` `CommRing` multiply. We give it
as a definition and prove a basic well-definedness law (`millerStep_one_left`:
the line value of the unit accumulator is `ℓ`, i.e. `millerStep 1 ℓ = ℓ`).

## Honesty boundary

This is the pairing line-function **computation skeleton** — the per-step value
and the per-step accumulator update — over the `bls12_377` `Fp12` tower. It does
**not** run the full Miller loop (the doubling-and-add accumulation over the
loop parameter / the BLS optimal-Ate seed), and it does **not** prove pairing
correctness: **bilinearity** and **non-degeneracy** are the Weil/Tate divisor
theory, which Mathlib has no formalization of (no `WeilPairing` over a general
curve), exactly as the `AUCurvesPort` / `PairingAxioms` layer defers them. The
`vanishes-at-R` facts below are the structural sanity checks that the line
function is the right object; the loop and the bilinearity/non-degeneracy
theory are deliberately out of scope here.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

namespace Fp12_377

/-! ## 1. The base-field-into-`Fp12_377` embedding `ofBase`

`ofBase t = t + 0·u + 0·v + 0·w`: the base scalar sits in the `c0.c0.c0`
coordinate of the `Fp12 → Fp6 → Fp2 → Fp` tower, all other coordinates `0`. -/

/-- Embed a base-field scalar `t : FpBLS377` into the `Fp2_377` quadratic
    extension as `t + 0·u`. -/
def Fp2ofBase (t : FpBLS377) : Fp2_377 := ⟨t, 0⟩

/-- Embed a base-field scalar `t : FpBLS377` into the `Fp6_377` cubic extension
    as `(t + 0·u) + 0·v + 0·v²`. -/
def Fp6ofBase (t : FpBLS377) : Fp6_377 := ⟨Fp2ofBase t, 0, 0⟩

/-- Embed a base-field scalar `t : FpBLS377` into the pairing field `Fp12_377`
    as `t + 0·u + 0·v + 0·w` (`t` in the `c0.c0.c0` coordinate). This is the map
    that lifts a `G1` base-field coordinate to the line-value field. -/
def ofBase (t : FpBLS377) : Fp12_377 := ⟨Fp6ofBase t, 0⟩

@[simp] theorem ofBase_zero : ofBase 0 = 0 := rfl
@[simp] theorem ofBase_one : ofBase 1 = 1 := rfl

/-- `ofBase` is additive. -/
@[simp] theorem ofBase_add (s t : FpBLS377) :
    ofBase (s + t) = ofBase s + ofBase t := by
  ext <;> simp [ofBase, Fp6ofBase, Fp2ofBase]

/-- `ofBase` respects subtraction. -/
@[simp] theorem ofBase_sub (s t : FpBLS377) :
    ofBase (s - t) = ofBase s - ofBase t := by
  ext <;> simp [ofBase, Fp6ofBase, Fp2ofBase]

/-- `ofBase` respects multiplication, over the `Fp12_377` `CommRing` at any
    base / cubic nonresidues `ξ₂, ξ₆`. The product of two base-embedded scalars
    has its single nonzero coordinate equal to the base product `s·t`; the tower
    multiply's `ξ`-folds all hit `0` coordinates. -/
theorem ofBase_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (s t : FpBLS377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    ofBase (s * t) = ofBase s * ofBase t := by
  letI := Fp2_377.commRing ξ₂
  letI := Fp6_377.commRing ξ₂ ξ₆
  letI := Fp12_377.commRing ξ₂ ξ₆
  show ofBase (s * t) = Fp12_377.mulSchoolbook ξ₂ ξ₆ (ofBase s) (ofBase t)
  ext <;>
    simp [Fp12_377.mulSchoolbook, Fp12_377.mul₆, Fp6_377.mulSchoolbook,
      Fp6_377.mul₂, Fp6_377.mulByV, ofBase, Fp6ofBase, Fp2ofBase,
      Fp2_377.mulSchoolbook]

end Fp12_377

/-! ## 2. The Miller line functions (tangent / chord), valued in `Fp12_377`

The line value the Miller loop multiplies in. The defining slope `λ : FpBLS377`
is the *same* base-field slope `RelationalFrontBls377EC` computes
(`bls377TangentSlope` for doubling, the chord slope for addition); we take it as
a parameter so no field inverse appears in the `Fp12` algebra (mirroring
`bls377AffineDbl`/`bls377AffineAdd`). The line is `(y − yR) − λ·(x − xR)`, every
base coordinate embedded by `Fp12_377.ofBase`. -/

open Fp12_377 (ofBase)

/-- **The tangent line function value.** Given the precomputed tangent slope
    `λ : FpBLS377` at `R = (xR, yR)`, the value of the tangent line at `R`
    evaluated at the affine point `(x, y)`:
    `ℓ_R(x, y) = (y − yR) − λ·(x − xR) : Fp12_377`. The tower nonresidues
    `ξ₂, ξ₆` fix the `Fp12_377` multiply used for the `λ·(x − xR)` product. -/
def lineTangent (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (lam xR yR x y : FpBLS377) :
    Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  ofBase (y - yR) - ofBase lam * ofBase (x - xR)

/-- **The chord line function value.** Given the precomputed chord slope
    `λ : FpBLS377` through `P = (xP, yP)` and `Q`, the value of the line at
    `(x, y)`: `ℓ_{P,Q}(x, y) = (y − yP) − λ·(x − xP) : Fp12_377`.
    (Same shape as `lineTangent`; the two differ only in which slope/anchor the
    Miller loop feeds in — tangent at the doubling step, chord at the add step.) -/
def lineChord (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (lam xP yP x y : FpBLS377) :
    Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  ofBase (y - yP) - ofBase lam * ofBase (x - xP)

/-! ## 3. The line vanishes at its defining point (the structural sanity check)

The defining algebraic property of a line function: the tangent line at `R`
passes through `R` (and the chord through `P, Q` passes through `P`). Evaluated
at the anchor, both differences `x − xR` and `y − yR` are `0`, so the value is
`ofBase 0 − ofBase λ · ofBase 0 = 0`. This is the `Fp12_377`-level honesty check
that the line function is the right object — it needs the `Fp12_377` `CommRing`
(for `ofBase_mul` / `mul_zero`), parameterized by the tower nonresidues. -/

/-- **The tangent line through `R` vanishes at `R`.** Over the `Fp12_377`
    `CommRing` at any tower nonresidues `ξ₂, ξ₆`, `lineTangent λ xR yR xR yR = 0`:
    both coordinate differences are `0`, and `ofBase` carries the base-field
    identity `(yR − yR) − λ·(xR − xR) = 0` into `Fp12_377`. -/
theorem lineTangent_vanishes_at_anchor (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (lam xR yR : FpBLS377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    lineTangent ξ₂ ξ₆ lam xR yR xR yR = 0 := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  show ofBase (yR - yR) - ofBase lam * ofBase (xR - xR) = 0
  rw [sub_self, sub_self, Fp12_377.ofBase_zero, mul_zero, sub_zero]

/-- **The chord through `P` vanishes at `P`.** Same structural fact for the
    addition-step line: `lineChord λ xP yP xP yP = 0`. -/
theorem lineChord_vanishes_at_anchor (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (lam xP yP : FpBLS377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    lineChord ξ₂ ξ₆ lam xP yP xP yP = 0 := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  show ofBase (yP - yP) - ofBase lam * ofBase (xP - xP) = 0
  rw [sub_self, sub_self, Fp12_377.ofBase_zero, mul_zero, sub_zero]

/-! ## 4. The Miller per-step accumulator update `f ← f²·ℓ`

The doubling step of the doubling-and-add Miller loop: square the running
pairing value and multiply by the line value. Over the `Fp12_377` `CommRing`. -/

/-- **The Miller doubling-step update** `f ← f² · ℓ`, written `f · f · ℓ` over the
    `Fp12_377` `CommRing` at tower nonresidues `ξ₂, ξ₆`. -/
def millerStep (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f ℓ : Fp12_377) : Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  f * f * ℓ

/-- **The Miller step on the unit accumulator returns the line value**:
    `millerStep 1 ℓ = ℓ`. (`1² · ℓ = ℓ` over the `Fp12_377` `CommRing`.) The
    well-definedness check that the first Miller step seeds the accumulator with
    exactly the first line value. -/
theorem millerStep_one_left (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (ℓ : Fp12_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    millerStep ξ₂ ξ₆ 1 ℓ = ℓ := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  show (1 : Fp12_377) * 1 * ℓ = ℓ
  rw [mul_one, one_mul]

/-- **The Miller step is multiplicative in the line value**: accumulating a
    product of two line values in one step equals the product of the two
    single-line step values divided by the extra square — concretely,
    `millerStep f (ℓ₁ · ℓ₂) = millerStep f ℓ₁ · ℓ₂` (the line factors commute
    out). A handle on how consecutive line values compose in the loop. -/
theorem millerStep_mul_line (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f ℓ₁ ℓ₂ : Fp12_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    millerStep ξ₂ ξ₆ f (ℓ₁ * ℓ₂) = millerStep ξ₂ ξ₆ f ℓ₁ * ℓ₂ := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  show f * f * (ℓ₁ * ℓ₂) = f * f * ℓ₁ * ℓ₂
  rw [mul_assoc (f * f)]

/-! ## 5. A worked example: the line value at a concrete point, and a Miller step

Concrete base-field operands, exercising `lineTangent` and the vanishing law and
one `millerStep`. We use the tower nonresidues `ξ₂ = 5`, `ξ₆ = 2 + 3u` (the same
witnesses the `Fp6`/`Fp12` worked examples use). -/

/-- **Worked example — the tangent line vanishes at its anchor**, a concrete
    instance of `lineTangent_vanishes_at_anchor` with `λ = 4`, `R = (2, 3)`. -/
theorem example_lineTangent_vanishes :
    letI := Fp12_377.commRing 5 ⟨2, 3⟩
    lineTangent 5 ⟨2, 3⟩ 4 2 3 2 3 = 0 :=
  lineTangent_vanishes_at_anchor 5 ⟨2, 3⟩ 4 2 3

/-- **Worked example — a Miller step on the unit accumulator** returns the line
    value, here the concrete line `lineTangent 4 2 3 7 11`. -/
theorem example_millerStep_one :
    letI := Fp12_377.commRing 5 ⟨2, 3⟩
    millerStep 5 ⟨2, 3⟩ 1 (lineTangent 5 ⟨2, 3⟩ 4 2 3 7 11)
      = lineTangent 5 ⟨2, 3⟩ 4 2 3 7 11 :=
  millerStep_one_left 5 ⟨2, 3⟩ (lineTangent 5 ⟨2, 3⟩ 4 2 3 7 11)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
