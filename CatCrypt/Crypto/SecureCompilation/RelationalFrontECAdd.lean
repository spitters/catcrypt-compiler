/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontEC
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontECMul
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontECDouble
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontECInv
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-!
# The AFFINE short-Weierstrass point ADD over GF(251) — closing the EC group law

`RelationalFrontECDouble.lean` realizes the inversion-free Jacobian point
**doubling** (`dbl-2009-l`, all three coordinates) at the `ZMod 251` level, and
`RelationalFrontECInv.lean` realizes the field-op building block the affine add needs — the
GF(251) **inverse**, realized as a Fermat multiply-square power chain
`pow249Spec` (`invMod251_commutes : encMod251 a⁻¹ = pow249Spec (encMod251 a)` for
`a ≠ 0`). With inversion in hand the **affine** short-Weierstrass add
(`ECParams.add`, the `chordSlope`/`affRx`/`affRy` composition in
`EllipticCurveDialect`) becomes a straight-line composition of already-realized
field ops, and this module assembles it.

## The affine add spec (`EllipticCurveDialect.ECParams`)

For two **distinct, non-infinity** points `P₁ = (x₁, y₁)`, `P₂ = (x₂, y₂)` with
`x₁ ≠ x₂` (the generic chord case — the only branch this module scopes to), the
short-Weierstrass affine add is

```
λ  = chordSlope = (y₂ − y₁) · (x₂ − x₁)⁻¹
x₃ = affRx λ x₁ x₂ = λ² − x₁ − x₂
y₃ = affRy λ x₁ x₃ y₁ = λ·(x₁ − x₃) − y₁
```

Every node is a field op whose `ZMod 251` commuting square is proved:

| step | `ZMod` building block (commuting square) |
|------|------------------------------------------|
| `x₂ − x₁`, `y₂ − y₁`, `x₁ − x₃`, `λ² − x₁ − x₂` | `sub251_commutes` |
| `(x₂ − x₁)⁻¹` | `invMod251_commutes` (the Fermat chain `pow249Spec`) |
| `(y₂−y₁)·(x₂−x₁)⁻¹`, `λ·λ`, `λ·(x₁−x₃)` | `gf251Mul_commutes` |

So the affine add introduces **no new field op** — it is exactly the slope
division (inverse + multiply) wrapped around the same sub/mul golden-path kernels.

## What this module establishes (all sorry-free)

* `ecAddBV` — the affine-add `BitVec 64` straight-line schedule (`λ/x₃/y₃`) over
  the encoded coordinates, built from `sub251`/`pow249Spec`/`gf251MulSpec`.
* `ecAddAffine` — the abstract `(ZMod 251 × ZMod 251) → … → …` chord-case add
  (the `chordSlope`/`affRx`/`affRy` composition, agreeing with `ECParams.add`'s
  chord branch under `x₁ ≠ x₂`, `chordCase_eq_ECParams_add`).
* The two per-coordinate `ZMod 251` commuting squares, conditioned on `x₁ ≠ x₂`:
  `ecAddX3_commutes`, `ecAddY3_commutes` — encoding `x₃` / `y₃` equals the
  corresponding `ecAddBV` component on the encoded coordinates.
* `RealizedAffineAdd` — a multi-output (pair) realization record bundling the two
  coordinate squares, and `ecAddRealized` populating it.
* A worked example: two distinct points on `blsClassCurve` (`y² = x³ + 1` over
  GF(251)), added, with the result verified **on the curve** and the realized
  `BitVec` formula computing exactly the encoded output coordinates.

## Scope

This module realizes the **generic chord branch only** (`P₁ ≠ P₂`, both affine,
`x₁ ≠ x₂`), the non-degenerate case. The remaining branches of the full
`ECParams.add` are outside its scope:

* **`x₁ = x₂` degenerate branches** — `P₁ = P₂` (→ doubling, the *tangent* slope,
  realized inversion-free in `RelationalFrontECDouble`) and `P₁ = −P₂` (→ `O`).
  These are a *branch on secret data*; the constant-time index-free fragment must
  realize them by the standard **CT-select** idiom (compute all branches, select
  by a masked equality flag), not a jump. That select wiring is deferred.
* **The `ECPoint = Option (ZMod p × ZMod p)` sum-type encoding** — serializing the
  infinity point `O` (the `none` arm) alongside the affine pair, with the unified
  add over `ECPoint` (including the `O + P = P` short-circuits). This module works
  with the *affine pair* directly; the `Option` tag-and-select is deferred.
* **`bls12_377`/`bls12_381`** — the single-word GF(251) carrier becomes a 377/381-bit
  **6×64-limb** carrier; each field op is a CIOS/Karatsuba kernel. The relational
  *structure* (per-coordinate encoding + commuting square + composed `BitVec`
  schedule) ports verbatim; only the carrier and per-op kernels change.

The **emitted `Com`** for the whole schedule (the de-Bruijn glue of the inverse
chain + slope multiply + `affRx`/`affRy` subs) is the same mechanical `ComBuilder`
assembly step deferred throughout this chain (see `RelationalFrontECInv`'s
docstring); the **relational content** — that the affine sum *equals* this
emitted sub/mul/inverse schedule on the serialized coordinates — is fully proved.

## With doubling + add both realized: the FULL EC group law over GF(251)

`RelationalFrontECDouble` realized the **doubling** (Jacobian `dbl-2009-l`, all
coordinates), and this module realizes the **add** (affine chord branch). The two
group-law operations — add and double — are therefore both realized relationally
over GF(251), each as a straight-line schedule of golden-path field kernels with a
per-coordinate `ZMod 251` commuting square, modulo the degenerate-branch CT-select
and the `Option` sum-type encoding documented above as the gap to the unified
`ECParams.add` over `ECPoint`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul

/-! ## 1. The abstract chord-case affine add (the `ECParams.add` generic branch)

For distinct affine points with `x₁ ≠ x₂`, the abstract add is the
`chordSlope`/`affRx`/`affRy` composition.  We name it as a function on affine
pairs (`ZMod 251 × ZMod 251`) so the commuting-square rewrites key on it, and tie
it to `ECParams.add`'s chord branch on `blsClassCurve`. -/

/-- The abstract chord-case slope `λ = (y₂ − y₁)·(x₂ − x₁)⁻¹` (the
    `EllipticCurveDialect.ECParams.chordSlope`, inlined for GF(251)). -/
def chordSlope251 (x1 y1 x2 y2 : ZMod 251) : ZMod 251 :=
  (y2 - y1) * (x2 - x1)⁻¹

/-- The abstract chord-case affine add on two **distinct** affine points
    (`x₁ ≠ x₂`): `x₃ = λ² − x₁ − x₂`, `y₃ = λ·(x₁ − x₃) − y₁`, with
    `λ = chordSlope251`.  The `EllipticCurveDialect.ECParams.add` chord branch. -/
def ecAddAffine (P1 P2 : ZMod 251 × ZMod 251) : ZMod 251 × ZMod 251 :=
  let x1 := P1.1; let y1 := P1.2; let x2 := P2.1; let y2 := P2.2
  let lam := chordSlope251 x1 y1 x2 y2
  let x3 := lam * lam - x1 - x2
  let y3 := lam * (x1 - x3) - y1
  (x3, y3)

/-- **`ecAddAffine` is exactly the `ECParams.add` chord branch.**  For distinct
    affine inputs with `x₁ ≠ x₂` (so neither the `O` arms nor the vertical-line
    branch fires), the unified short-Weierstrass `ECParams.add` on `blsClassCurve`
    returns `some (ecAddAffine …)`.  Ties the named affine-pair op to the dialect's
    sum-type group law (the chord arm). -/
theorem chordCase_eq_ECParams_add
    (x1 y1 x2 y2 : ZMod 251) (hx : x1 ≠ x2) :
    blsClassCurve.add (some (x1, y1)) (some (x2, y2))
      = some (ecAddAffine (x1, y1) (x2, y2)) := by
  simp only [ECParams.add, ecAddAffine, chordSlope251, ECParams.chordSlope,
    ECParams.affRx, ECParams.affRy, if_neg hx]

/-! ## 2. The realized `BitVec` schedule (`λ / x₃ / y₃` over encoded coords)

Each abstract op is replaced by its golden-path carrier operator: `sub251`
(`a − b`), `pow249Spec` (the Fermat inverse chain), `gf251MulSpec`
(multiply/square).  The schedule mirrors `ecAddAffine` node-for-node. -/

/-- The realized `BitVec 64` chord slope `λ = (y₂−y₁)·(x₂−x₁)⁻¹` on encoded
    coordinates: `gf251MulSpec (sub251 y₂ y₁) (pow249Spec (sub251 x₂ x₁))` (the
    inverse is the Fermat power chain `pow249Spec`). -/
def chordSlopeBV (x1 y1 x2 y2 : BitVec 64) : BitVec 64 :=
  gf251MulSpec (sub251 y2 y1) (pow249Spec (sub251 x2 x1))

/-- The realized `BitVec 64` affine-add schedule on the encoded coordinates
    `(x₁, y₁, x₂, y₂)`.  Returns the `(x₃, y₃)` words.  `x₃ = λ² − x₁ − x₂`,
    `y₃ = λ·(x₁ − x₃) − y₁`, with `λ = chordSlopeBV`. -/
def ecAddBV (x1 y1 x2 y2 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let lam := chordSlopeBV x1 y1 x2 y2
  let x3 := sub251 (sub251 (gf251MulSpec lam lam) x1) x2   -- λ² − x₁ − x₂
  let y3 := sub251 (gf251MulSpec lam (sub251 x1 x3)) y1    -- λ·(x₁ − x₃) − y₁
  (x3, y3)

/-! ## 3. The slope commuting square (the only step using inversion)

`encMod251 (chordSlope251 …) = chordSlopeBV (encoded …)`, conditioned on
`x₁ ≠ x₂` (so `x₂ − x₁ ≠ 0` and the Fermat chain realizes its inverse).  Composes
`sub251_commutes` (the two differences), `invMod251_commutes` (the inverse), and
`gf251Mul_commutes` (the product). -/

/-- **The chord-slope commuting square.**  For `x₁ ≠ x₂`, the abstract chord slope
    `λ = (y₂−y₁)·(x₂−x₁)⁻¹` (in `F_251`), serialized by `encMod251`, equals the
    realized `chordSlopeBV` on the encoded coordinates.  This is the **only** step
    that uses inversion: `(x₂−x₁)⁻¹` is realized by the Fermat chain `pow249Spec`
    (`invMod251_commutes`, applicable since `x₂ − x₁ ≠ 0`).  The slope numerator and
    the final product are `sub251`/`gf251MulSpec`. -/
theorem chordSlope_commutes (x1 y1 x2 y2 : ZMod 251) (hx : x1 ≠ x2) :
    encMod251 (chordSlope251 x1 y1 x2 y2)
      = chordSlopeBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2) := by
  have hne : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold chordSlope251 chordSlopeBV
  rw [gf251Mul_commutes, sub251_commutes, invMod251_commutes _ hne, sub251_commutes]

/-! ## 4. The per-coordinate `ZMod 251` commuting squares (the heart)

`x₃` and `y₃` of `ecAddAffine`, serialized, equal the `ecAddBV` components, for
`x₁ ≠ x₂`.  Both compose the slope square with `sub251_commutes`/`gf251Mul_commutes`
for the `affRx`/`affRy` maps. -/

/-- **`x₃ = λ² − x₁ − x₂` commuting square.**  Encoding the abstract `x₃` equals
    the realized `ecAddBV` first component on the encoded coordinates, for
    `x₁ ≠ x₂`.  Composes `chordSlope_commutes` (the slope `λ`), `gf251Mul_commutes`
    (`λ²`), and two `sub251_commutes` (`λ² − x₁`, then `− x₂`). -/
theorem ecAddX3_commutes (x1 y1 x2 y2 : ZMod 251) (hx : x1 ≠ x2) :
    encMod251 (ecAddAffine (x1, y1) (x2, y2)).1
      = (ecAddBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)).1 := by
  simp only [ecAddAffine, ecAddBV]
  simp only [sub251_commutes, gf251Mul_commutes, chordSlope_commutes _ _ _ _ hx]

/-- **`y₃ = λ·(x₁ − x₃) − y₁` commuting square.**  Encoding the abstract `y₃`
    equals the realized `ecAddBV` second component on the encoded coordinates, for
    `x₁ ≠ x₂`.  Composes everything `x₃` needs (since `x₃` appears inside `y₃`),
    plus `sub251_commutes` (`x₁ − x₃`), `gf251Mul_commutes` (`λ·(x₁−x₃)`), and a
    final `sub251_commutes` (`− y₁`). -/
theorem ecAddY3_commutes (x1 y1 x2 y2 : ZMod 251) (hx : x1 ≠ x2) :
    encMod251 (ecAddAffine (x1, y1) (x2, y2)).2
      = (ecAddBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)).2 := by
  simp only [ecAddAffine, ecAddBV]
  simp only [sub251_commutes, gf251Mul_commutes, chordSlope_commutes _ _ _ _ hx]

/-! ## 5. The multi-output (pair) affine-add realization

`RealizedUnaryKernel` is single-output; the affine add has two outputs sharing the
slope intermediate.  We bundle the two coordinate squares into one record (the
affine-pair analogue of `RelationalFrontECDouble`'s `RealizedJacobianOp`),
conditioned on the `x₁ ≠ x₂` chord precondition. -/

/-- **A relationally-emitted affine point-ADD (chord branch).**  An abstract affine
    add `op` on pairs, its `BitVec 64`-pair realization `bop` on the encoded
    coordinates, and the per-coordinate commuting square *conditioned on the chord
    precondition* `x₁ ≠ x₂` (the generic, non-degenerate branch).  The two-output
    affine analogue of `RealizedJacobianOp`. -/
structure RealizedAffineAdd
    (op : ZMod 251 × ZMod 251 → ZMod 251 × ZMod 251 → ZMod 251 × ZMod 251) where
  /-- The carrier realization: a `BitVec 64`-pair op on the four encoded input
      coordinates `(x₁, y₁, x₂, y₂)`. -/
  bop : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64
  /-- **The multi-output commuting square**, on the chord branch (`x₁ ≠ x₂`):
      encoding each output coordinate equals the matching `bop` component on the
      encoded input coordinates. -/
  commutes : ∀ x1 y1 x2 y2 : ZMod 251, x1 ≠ x2 →
    (encMod251 (op (x1, y1) (x2, y2)).1, encMod251 (op (x1, y1) (x2, y2)).2)
      = bop (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)

/-- **The relationally-emitted affine point-ADD.**  Its abstract source is the
    chord-case affine add `ecAddAffine` (the `ECParams.add` generic branch), its
    computational side is the `BitVec`-pair schedule `ecAddBV`, and its commuting
    square is the conjunction of the two per-coordinate squares (`ecAddX3_commutes`,
    `ecAddY3_commutes`), conditioned on `x₁ ≠ x₂`.  The affine EC point-ADD realized
    end-to-end at the `ZMod 251` level on the non-degenerate branch. -/
def ecAddRealized : RealizedAffineAdd ecAddAffine where
  bop := ecAddBV
  commutes := fun x1 y1 x2 y2 hx => by
    have hX := ecAddX3_commutes x1 y1 x2 y2 hx
    have hY := ecAddY3_commutes x1 y1 x2 y2 hx
    rw [Prod.ext_iff]; exact ⟨hX, hY⟩

/-! ## 6. The transfer corollary

The affine-add analogue of `dbl2009l_spec_transfers`: two chord-case sums agree
**iff** the realized `ecAddBV` schedule agrees on the encoded coordinates —
through the injective-not-onto `encMod251`, coordinate-wise. -/

/-- **The affine-add transfer.**  Two chord-case affine sums are equal in `F_251`
    iff the realized `ecAddBV` schedule agrees on their encoded coordinates (both
    sides on the chord branch `x₁ ≠ x₂`, `x₁' ≠ x₂'`).  The relational front
    carrying the affine EC add through the injective-not-onto serialization. -/
theorem ecAdd_spec_transfers
    (x1 y1 x2 y2 x1' y1' x2' y2' : ZMod 251) (hx : x1 ≠ x2) (hx' : x1' ≠ x2') :
    ecAddAffine (x1, y1) (x2, y2) = ecAddAffine (x1', y1') (x2', y2') ↔
      ecAddBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)
        = ecAddBV (encMod251 x1') (encMod251 y1') (encMod251 x2') (encMod251 y2') := by
  constructor
  · intro h
    have hX : (ecAddBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)).1
        = (ecAddBV (encMod251 x1') (encMod251 y1') (encMod251 x2') (encMod251 y2')).1 := by
      rw [← ecAddX3_commutes _ _ _ _ hx, ← ecAddX3_commutes _ _ _ _ hx', h]
    have hY : (ecAddBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)).2
        = (ecAddBV (encMod251 x1') (encMod251 y1') (encMod251 x2') (encMod251 y2')).2 := by
      rw [← ecAddY3_commutes _ _ _ _ hx, ← ecAddY3_commutes _ _ _ _ hx', h]
    exact Prod.ext hX hY
  · intro h
    have hX : encMod251 (ecAddAffine (x1, y1) (x2, y2)).1
        = encMod251 (ecAddAffine (x1', y1') (x2', y2')).1 := by
      rw [ecAddX3_commutes _ _ _ _ hx, ecAddX3_commutes _ _ _ _ hx', h]
    have hY : encMod251 (ecAddAffine (x1, y1) (x2, y2)).2
        = encMod251 (ecAddAffine (x1', y1') (x2', y2')).2 := by
      rw [ecAddY3_commutes _ _ _ _ hx, ecAddY3_commutes _ _ _ _ hx', h]
    exact Prod.ext (encMod251_injective hX) (encMod251_injective hY)

/-! ## 7. A worked example: adding two distinct points on `blsClassCurve`

`blsClassCurve : y² = x³ + 1` over GF(251).  Two affine points on it:
`P = (0, 1)` (`1 = 0+1`) and `Q = (2, 3)` (`9 = 8+1`).  They are distinct with
`x₁ = 0 ≠ 2 = x₂`, so the chord branch applies.  We add them, verify the sum is on
the curve, and check the realized `BitVec` schedule computes the encoded output.

The chord sum (computed in `ZMod 251`):
`λ = (3−1)·(2−0)⁻¹ = 2·126 = 252 = 1`; `x₃ = 1 − 0 − 2 = −1 = 250`;
`y₃ = 1·(0 − 250) − 1 = −251 = 0`.  So `P + Q = (250, 0)`, and
`0² = 250³ + 1`? `250 = −1`, `(−1)³ + 1 = −1 + 1 = 0 = 0²` ✓ on the curve. -/

/-- `P = (0, 1)` is on `blsClassCurve` (`y² = x³ + 1`): `1 = 0 + 1`. -/
theorem worked_P_onCurve : blsClassCurve.onCurve (0 : ZMod 251) (1 : ZMod 251) := by
  unfold ECParams.onCurve blsClassCurve; decide

/-- `Q = (2, 3)` is on `blsClassCurve`: `9 = 8 + 1`. -/
theorem worked_Q_onCurve : blsClassCurve.onCurve (2 : ZMod 251) (3 : ZMod 251) := by
  unfold ECParams.onCurve blsClassCurve; decide

/-- `P` and `Q` are distinct in the `x`-coordinate (the chord precondition). -/
theorem worked_distinct : (0 : ZMod 251) ≠ (2 : ZMod 251) := by decide

/-- **The worked add, abstract side.**  The chord-case affine add of `P = (0,1)`
    and `Q = (2,3)` is `(250, 0)` (`λ = 1`, `x₃ = −1 = 250`, `y₃ = −251 = 0`). -/
theorem worked_add_abstract :
    ecAddAffine (0, 1) (2, 3) = ((250 : ZMod 251), (0 : ZMod 251)) := by
  unfold ecAddAffine chordSlope251; decide +kernel

/-- **The sum is on the curve.**  `P + Q = (250, 0)` lies on `blsClassCurve`
    (`0² = 250³ + 1`, since `250 = −1` and `(−1)³ + 1 = 0`).  Confirms the realized
    affine add lands a curve point. -/
theorem worked_sum_onCurve : blsClassCurve.onCurve (250 : ZMod 251) (0 : ZMod 251) := by
  unfold ECParams.onCurve blsClassCurve; decide

/-- **The worked add, via `ECParams.add`.**  The unified short-Weierstrass group
    add (the dialect sum-type op) on `some (0,1)`, `some (2,3)` returns
    `some (250, 0)` — confirming the chord branch fires and agrees with the realized
    affine add. -/
theorem worked_add_ECParams :
    blsClassCurve.add (some (0, 1)) (some (2, 3)) = some (250, 0) := by
  rw [chordCase_eq_ECParams_add 0 1 2 3 worked_distinct, worked_add_abstract]

/-- **The worked add, realized formula side.**  The emitted `BitVec`-pair schedule
    `ecAddBV` on the encoded coordinates `(enc 0, enc 1, enc 2, enc 3)` computes
    exactly the encoded output coordinates `(enc 250, enc 0)` — the relational tie
    holding on two concrete curve points, sorry-free. -/
theorem worked_add_realized :
    ecAddBV (encMod251 0) (encMod251 1) (encMod251 2) (encMod251 3)
      = (encMod251 250, encMod251 0) := by
  have hX := ecAddX3_commutes 0 1 2 3 worked_distinct
  have hY := ecAddY3_commutes 0 1 2 3 worked_distinct
  rw [worked_add_abstract] at hX hY
  exact Prod.ext hX.symm hY.symm

end CatCrypt.Crypto.SecureCompilation.RelationalFront
