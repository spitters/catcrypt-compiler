/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377G2Affine
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377MillerLine

/-!
# The twisted-`G2` Miller producer and the sparse twisted line function

`RelationalFrontBls377G2Affine` carries the realized `bls12_377` `G2` twist
group law over `Fp2_377`: the affine tangent-double `g2AffineDbl ξ x y` (slope
`λ = 3x²·inv(2y)`), the affine chord-add `g2AffineAdd ξ x₁ y₁ x₂ y₂`
(slope `λ = (y₂−y₁)·inv(x₂−x₁)`), and their realization ties to the Jacobian
group law (`bls377G2_affine_double_realizes` / `_add_realizes`).

`RelationalFrontBls377MillerLine` carries the base-field line placeholder
(`lineTangent` / `lineChord`), which embeds every coordinate into `Fp12_377`'s
`c0.c0.c0` slot through `Fp12_377.ofBase` — a same-field stand-in, not the twist.

This module builds the two twist-native objects that stand-in replaces:

* `g2MillerSteps ξ P bits` threads the **real** `G2` accumulator `T` (all
  coordinates in `Fp2_377`) over the realized twist double/add group law,
  emitting the per-step tuple `(bit, λ_dbl, λ_add, T.x, T.y)` — the twist
  analogue of the base-field `VIR.Bls377MillerSteps.millerSteps`.  The
  accumulator advances by `g2AffineDbl` (doubling) then, on a set bit,
  `g2AffineAdd` (double-and-add).  Instantiated at the loop-bit list
  `VIR.Bls377MillerSteps.bls377AteSeedBits` (curve seed `0x8508c00000000001`).

* `make_line ξ₂ λ Tx Ty Px Py` is the sparse twisted line at the `G2`
  accumulator `(Tx, Ty)` (`Fp2` coordinates, `Fp2` slope `λ`), evaluated at the
  `G1` point `(Px, Py)` (`Fp` coordinates), landing three `Fp2` coefficients in
  the M-type twist tower slots of `Fp12_377 = Fp6[w]/(w²−v)`,
  `Fp6 = Fp2[v]/(v³−ξ₆)`:
  `l00` (the constant `c0.c0` slot, Fp12 basis position `1`),
  `l01` (the `v` slot `c0.c1`, position `v`), and
  `l11` (the `w·v` slot `c1.c1`, position `w·v`).  This is the D/M-type
  `mul_by_014` sparse pattern (nonzero at Fp12 basis positions `{1, v, w·v}`).

* `g2LineEvals ξ₂ ξ P Px Py bits` maps `make_line` (at the per-step doubling
  slope) over `g2MillerSteps`.

## Constructed vs. deferred

`g2MillerSteps`, `make_line`, and `g2LineEvals` are total (`make_line`
computable, the two producers `noncomputable` through the `Fp2_377` inverse in
the slopes).  The twist accumulator advances by the *realized* group law
(`g2AffineDbl` / `g2AffineAdd`), and the line places the tangent-line
coefficients `(Ty − λ·Tx, λ·Px, −Py)` in the M-type slots.

Their algebraic **correctness** is deferred, exactly as the `AUCurvesPort` /
`PairingAxioms` layer and `VIR.Bls377MillerSteps` defer it: that `make_line`
equals the RELIC `pp_dbl_k12` sparse line, and that the resulting Miller fold is
**bilinear / non-degenerate**, is Weil/Tate divisor theory Mathlib has no
formalization of.  Those facts are the `concretePairing_bilinear_*` /
`concretePairing_nondeg` assumptions of `VIR.Bls377MillerSteps`; this module does
**not** re-prove or fabricate them.  What is proved here is structural: the
producer's empty-loop base case, the accumulator-advance identities, and the
line-list length.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377

/-! ## 1. The twist slopes (the doubling tangent slope and the chord slope)

The slopes are the local `λ` of `g2AffineDbl` / `g2AffineAdd` exposed as
standalone maps, so the producer can emit them alongside the anchor.  Both are
`Fp2_377` values over `commRing ξ`, using the explicit conjugate-over-norm
inverse `Fp2_377.inv`. -/

/-- The **twist tangent (doubling) slope** at `(x, y)` on the `bls12_377` `G2`
    twist: `λ = 3x²·inv(2y)`.  This is the local `λ` inside `g2AffineDbl ξ x y`. -/
noncomputable def g2TangentSlope [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (x y : Fp2_377) : Fp2_377 :=
  letI := Fp2_377.commRing ξ
  (3 * (x * x)) * Fp2_377.inv ξ (2 * y)

/-- The **twist chord slope** between `(x₁, y₁)` and `(x₂, y₂)` on the `G2`
    twist: `λ = (y₂−y₁)·inv(x₂−x₁)`.  This is the local `λ` inside
    `g2AffineAdd ξ x₁ y₁ x₂ y₂`. -/
noncomputable def g2ChordSlope [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (x1 y1 x2 y2 : Fp2_377) : Fp2_377 :=
  letI := Fp2_377.commRing ξ
  (y2 - y1) * Fp2_377.inv ξ (x2 - x1)

/-! ## 2. The per-step accumulator advance (double-and-add over the realized law) -/

/-- The **`G2` Miller accumulator advance** for one loop bit: double the
    accumulator `T` by the realized tangent-double `g2AffineDbl`, then — iff the
    bit is set — chord-add the base point `P` by the realized `g2AffineAdd`.
    This is the twist analogue of `T ← 2T` then `T ← T + P` in the base-field
    `VIR.Bls377MillerSteps.millerSteps`, over the realized twist group law. -/
noncomputable def g2Accum [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (P T : Bls377G2Point) (b : Bool) : Bls377G2Point :=
  let T2 := g2AffineDbl ξ T.x T.y
  if b then g2AffineAdd ξ T2.x T2.y P.x P.y else T2

/-- On a clear bit the accumulator advances by exactly the realized tangent
    double `g2AffineDbl`. -/
@[simp] theorem g2Accum_false [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (P T : Bls377G2Point) :
    g2Accum ξ P T false = g2AffineDbl ξ T.x T.y := by
  simp [g2Accum]

/-- On a set bit the accumulator advances by the realized double-then-add:
    `g2AffineAdd` applied to the doubled point and the base point `P`. -/
@[simp] theorem g2Accum_true [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (P T : Bls377G2Point) :
    g2Accum ξ P T true
      = g2AffineAdd ξ (g2AffineDbl ξ T.x T.y).x (g2AffineDbl ξ T.x T.y).y P.x P.y := by
  simp [g2Accum]

/-! ## 3. The twist Miller producer `g2MillerSteps`

Threads the `G2` accumulator `T` (seeded at `P`) over the loop bits through
`g2Accum`, emitting per step the tuple `(bit, λ_dbl, λ_add, T.x, T.y)`: the
doubling (tangent) slope at `T`, the chord slope between `T` and `P`, and the
accumulator anchor `(T.x, T.y)`.  This is the `(bit, λ_dbl, λ_add, xT, yT)` shape
the committed Miller loop consumes, one tower level up from the base field: every
coordinate and slope is `Fp2_377`. -/

/-- **The twist `G2` Miller-loop line-list producer.**  Fold over the loop bits,
    threading the accumulator `T` (seeded at `P`) by the realized twist group law
    `g2Accum`, emitting at each step `(bit, g2TangentSlope T, g2ChordSlope T P,
    T.x, T.y)`.  The twist analogue of `VIR.Bls377MillerSteps.millerSteps`; the
    accumulator is an `Fp2_377` `G2` point advancing by the realized
    double/add. -/
noncomputable def g2MillerSteps [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (P : Bls377G2Point) (bits : List Bool) :
    List (Bool × Fp2_377 × Fp2_377 × Fp2_377 × Fp2_377) :=
  (bits.foldl
      (fun (st : Bls377G2Point ×
              List (Bool × Fp2_377 × Fp2_377 × Fp2_377 × Fp2_377)) (b : Bool) =>
        let T := st.1
        (g2Accum ξ P T b,
          st.2 ++ [(b, g2TangentSlope ξ T.x T.y, g2ChordSlope ξ T.x T.y P.x P.y,
                    T.x, T.y)]))
      (P, [])).2

/-- **The empty-loop line list is empty.**  Structural base case: no loop bits
    emit no steps. -/
@[simp] theorem g2MillerSteps_nil [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (P : Bls377G2Point) :
    g2MillerSteps ξ P [] = [] := rfl

/-- **The line list has one entry per loop bit.**  The producer emits exactly
    `bits.length` steps: the fold appends one tuple per bit, threading the
    accumulator. -/
theorem g2MillerSteps_length [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (P : Bls377G2Point) (bits : List Bool) :
    (g2MillerSteps ξ P bits).length = bits.length := by
  suffices h : ∀ (bits : List Bool)
      (st : Bls377G2Point × List (Bool × Fp2_377 × Fp2_377 × Fp2_377 × Fp2_377)),
      (bits.foldl
          (fun st b =>
            let T := st.1
            (g2Accum ξ P T b,
              st.2 ++ [(b, g2TangentSlope ξ T.x T.y, g2ChordSlope ξ T.x T.y P.x P.y,
                        T.x, T.y)]))
          st).2.length = st.2.length + bits.length by
    simpa [g2MillerSteps] using h bits (P, [])
  intro bits
  induction bits with
  | nil => intro st; simp
  | cons b bs ih =>
    intro st
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! ## 4. The sparse twisted line function `make_line`

The line at the `G2` accumulator `(Tx, Ty)` with `Fp2` slope `λ`, evaluated at
the `G1` point `(Px, Py)`, valued in `Fp12_377`.  The affine tangent line to the
twist curve at `(Tx, Ty)` is `λ·X − Y + (Ty − λ·Tx) = 0`; its untwisted
evaluation places three `Fp2` coefficients in the M-type `mul_by_014` slots
(Fp12 basis positions `{1, v, w·v}`):

* `l00 = Ty − λ·Tx`     (constant term, `c0.c0`);
* `l01 = λ·Px`          (`X`-coefficient scaled by `Px`, `c0.c1`);
* `l11 = −Py`           (`Y`-coefficient `−1` scaled by `Py`, `c1.c1`);

with `Px, Py : FpBLS377` embedded into `Fp2_377` by `Fp12_377.Fp2ofBase`.  The
`Fp2` product `λ·Tx` / `λ·Px` is the schoolbook multiply `Fp2_377.mulSchoolbook
ξ₂`; the additions / negation are the componentwise `Fp2_377` instances, so
`make_line` is a total computable `def`. -/

/-- **The sparse twisted line element** `ℓ = make_line ξ₂ λ Tx Ty Px Py :
    Fp12_377`.  Places the three tangent-line coefficients `(Ty − λ·Tx, λ·Px,
    −Py)` in the M-type twist slots `l00 = c0.c0`, `l01 = c0.c1`, `l11 = c1.c1`
    (Fp12 basis positions `{1, v, w·v}`), all other slots `0`.  The `Fp2`
    products use the base nonresidue `ξ₂`; `Px, Py` embed by `Fp2ofBase`. -/
def make_line (ξ₂ : FpBLS377) (lam Tx Ty : Fp2_377) (Px Py : FpBLS377) : Fp12_377 :=
  let l00 : Fp2_377 := Ty - Fp2_377.mulSchoolbook ξ₂ lam Tx
  let l01 : Fp2_377 := Fp2_377.mulSchoolbook ξ₂ lam (Fp12_377.Fp2ofBase Px)
  let l11 : Fp2_377 := -(Fp12_377.Fp2ofBase Py)
  Fp12_377.mk (Fp6_377.mk l00 l01 0) (Fp6_377.mk 0 l11 0)

/-- The line's `c0.c0` slot is `l00 = Ty − λ·Tx` (Fp12 basis position `1`). -/
@[simp] theorem make_line_c0c0 (ξ₂ : FpBLS377) (lam Tx Ty : Fp2_377)
    (Px Py : FpBLS377) :
    (make_line ξ₂ lam Tx Ty Px Py).c0.c0 = Ty - Fp2_377.mulSchoolbook ξ₂ lam Tx :=
  rfl

/-- The line's `c0.c1` slot is `l01 = λ·Px` (Fp12 basis position `v`). -/
@[simp] theorem make_line_c0c1 (ξ₂ : FpBLS377) (lam Tx Ty : Fp2_377)
    (Px Py : FpBLS377) :
    (make_line ξ₂ lam Tx Ty Px Py).c0.c1
      = Fp2_377.mulSchoolbook ξ₂ lam (Fp12_377.Fp2ofBase Px) := rfl

/-- The line's `c1.c1` slot is `l11 = −Py` (Fp12 basis position `w·v`). -/
@[simp] theorem make_line_c1c1 (ξ₂ : FpBLS377) (lam Tx Ty : Fp2_377)
    (Px Py : FpBLS377) :
    (make_line ξ₂ lam Tx Ty Px Py).c1.c1 = -(Fp12_377.Fp2ofBase Py) := rfl

/-- The three remaining tower slots of the sparse line vanish (`c0.c2`, `c1.c0`,
    `c1.c2` — Fp12 basis positions `{v², w, w·v²}`). -/
@[simp] theorem make_line_sparse (ξ₂ : FpBLS377) (lam Tx Ty : Fp2_377)
    (Px Py : FpBLS377) :
    (make_line ξ₂ lam Tx Ty Px Py).c0.c2 = 0
      ∧ (make_line ξ₂ lam Tx Ty Px Py).c1.c0 = 0
      ∧ (make_line ξ₂ lam Tx Ty Px Py).c1.c2 = 0 :=
  ⟨rfl, rfl, rfl⟩

/-! ## 5. The twist line-value list `g2LineEvals`

Maps the sparse twisted `make_line` (at each step's doubling slope `λ_dbl` and
anchor `(T.x, T.y)`) over the `g2MillerSteps` producer, evaluated at the fixed
`G1` point `(Px, Py)`.  The `Fp12_377` line-value list the Miller fold
multiplies in. -/

/-- **The twist Miller line-value list.**  `make_line` evaluated at each
    `g2MillerSteps` step's doubling slope and accumulator anchor, at the `G1`
    point `(Px, Py)`.  The addition-step line is the analogous `make_line ξ₂
    s.λ_add s.Tx s.Ty Px Py`; this list carries the doubling line per step. -/
noncomputable def g2LineEvals [Fact (Nat.Prime bls377Q)] (ξ₂ ξ : FpBLS377)
    (P : Bls377G2Point) (Px Py : FpBLS377) (bits : List Bool) : List Fp12_377 :=
  (g2MillerSteps ξ P bits).map (fun s =>
    make_line ξ₂ s.2.1 s.2.2.2.1 s.2.2.2.2 Px Py)

/-- **The line-value list has one entry per loop bit.**  Immediate from
    `g2MillerSteps_length` and `List.length_map`. -/
theorem g2LineEvals_length [Fact (Nat.Prime bls377Q)] (ξ₂ ξ : FpBLS377)
    (P : Bls377G2Point) (Px Py : FpBLS377) (bits : List Bool) :
    (g2LineEvals ξ₂ ξ P Px Py bits).length = bits.length := by
  rw [g2LineEvals, List.length_map, g2MillerSteps_length]

/-- **The empty-loop line-value list is empty.** -/
@[simp] theorem g2LineEvals_nil [Fact (Nat.Prime bls377Q)] (ξ₂ ξ : FpBLS377)
    (P : Bls377G2Point) (Px Py : FpBLS377) :
    g2LineEvals ξ₂ ξ P Px Py [] = [] := rfl

end CatCrypt.Crypto.SecureCompilation.RelationalFront
