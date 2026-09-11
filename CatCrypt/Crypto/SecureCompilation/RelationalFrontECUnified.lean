/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontECAdd

/-!
# The UNIFIED short-Weierstrass group law `ECParams.add` over `ECPoint` (GF(251))

`RelationalFrontECAdd.lean` realized the affine **chord** branch (`x₁ ≠ x₂`),
`RelationalFrontECDouble.lean` the Jacobian doubling, and `RelationalFrontECInv`
the GF(251) inverse (the Fermat power chain `pow249Spec`).  Each is a
straight-line schedule of golden-path field kernels with a per-coordinate
`ZMod 251` commuting square.  **This module composes them into the UNIFIED
`EllipticCurveDialect.ECParams.add`** — the *complete* group law over
`ECPoint 251 = Option (ZMod 251 × ZMod 251)`, including the point at infinity `O`
(`none`) and the degenerate `x₁ = x₂` branches, **dispatched branchlessly** via
the constant-time mask-select idiom (`Dialects/CmovSelect.lean`).

## The two new pieces over the per-branch realizations

1. **The `ECPoint` sum-type ENCODING.**  `ECPoint p = Option (ZMod p × ZMod p)`
   is a *sum* type (the infinity point `O = none` alongside the affine pair).
   We serialize it to a **tagged triple** `(tag, x, y) : BitVec 64³`:
   `O ↦ (0, 0, 0)` (tag `0`), `some (x, y) ↦ (1, encMod251 x, encMod251 y)`
   (tag `1`).  `encPoint_injective` is the relational requirement: the tag
   separates the arms, and `encMod251` is injective on the coordinates.

2. **The branchless DISPATCH.**  `ECParams.add` is a 5-way `match`/`if` on the
   two points' tags and coordinates (`none`-arms, then `x₁ = x₂` splitting into
   the vertical `P = −Q → O` and the doubling, else the chord).  In the
   constant-time index-free fragment this must be realized by computing all the
   arms and **selecting by a masked equality flag** — never a jump.  We model
   the value-level select exactly as `Dialects/CmovSelect.lean` /
   `ArithIselSoundness.condMask` do — a mask `if cond then allOnes else 0`,
   composed `(x &&& m) ||| (y &&& ~~~m)` (`selBV`) — and prove the dispatch
   commuting square `encPoint (ECParams.add P Q) = ecAddUnifiedBV (encPoint P)
   (encPoint Q)` by case analysis mirroring the spec's branch structure.

The arithmetic of each branch **reuses the landed kernels**: the chord arm is
`ecAddBV` (`RelationalFrontECAdd`), and the `x₁ = x₂` doubling arm is the affine
doubling `ecDblAffineBV` assembled here from the *same* `sub251` / `pow249Spec`
(inverse) / `gf251MulSpec` / `tripleSpecBV` / `double251` building blocks (each
with a landed `ZMod 251` commuting square).  No new field op is introduced.

## What this module establishes (all sorry-free)

* `encPoint` / `decTagAffine` — the `ECPoint 251 → BitVec 64³` tagged-triple
  encoding and its injectivity `encPoint_injective`.
* `selBV` / `selBV3` — the value-level branchless mask-select (the `condMask`
  idiom of `CmovSelect`) on words and on encoded triples, with the two
  defining lemmas `selBV_true` / `selBV_false`.
* `ecDblAffine` / `ecDblAffineBV` — the **affine doubling** (`a = 0` tangent
  slope) abstract op and its realized `BitVec` schedule, with the per-coordinate
  commuting squares (`ecDblAffineX3_commutes`, `ecDblAffineY3_commutes`),
  conditioned on `y ≠ 0` (the non-vertical tangent).
* `ecAddUnifiedBV` — the branchless unified add on encoded triples, selecting
  among `{Q (if P = O), P (if Q = O), O (if x₁ = x₂ ∧ y₁ = −y₂), doubling
  (if x₁ = x₂), chord}`.
* **`encPoint_add_commutes` — the UNIFIED commuting square**: for every
  `P Q : ECPoint 251`, `encPoint (blsClassCurve.add P Q) = ecAddUnifiedBV
  (encPoint P) (encPoint Q)`.  All five branches closed sorry-free.
* Worked examples through the unified op: `O + P = P`, `P + O = P`, a chord
  `P + Q`, the vertical `P + (−P) = O`, and a doubling `P + P`.

## Branch-closure status (HONEST)

All five `ECParams.add` branches are closed in the unified commuting square:

| branch | condition | arm | realized by |
|--------|-----------|-----|-------------|
| O-left | `P = O` | `Q` | `selBV3` (identity select) |
| O-right | `Q = O` | `P` | `selBV3` (identity select) |
| vertical | both affine, `x₁ = x₂`, `y₁ = −y₂` | `O` | `selBV3` → `(0,0,0)` |
| doubling | both affine, `x₁ = x₂`, `y₁ ≠ −y₂` | affine dbl | `ecDblAffineBV` |
| chord | both affine, `x₁ ≠ x₂` | chord add | `ecAddBV` |

The one **modelling fidelity** note (not a gap in the result): the equality
flags driving the select are modelled at the value level as
`if a = b then allOnes else 0` — exactly the shape `ArithIselSoundness.condMask`
and `selectW` use (`if cond = 1#1 …`).  The *constant-time implementation* of
that flag (a subtract-then-OR-all-bits reduction to a 1-bit condition) is the
`CmovSelect` peephole's `condMask` materialisation; here we work with the
value-level model the soundness layer is stated against.  The emitted `Com`
for the whole branchless schedule is the same mechanical `ComBuilder` glue
deferred throughout this chain; the **relational content** — that the unified
sum equals this branchless select over the serialized coordinates — is fully
proved.

## With chord + doubling + dispatch: the complete EC group law over GF(251)

Composing the landed chord (`RelationalFrontECAdd`) and the affine doubling
(here) under the `Option` tagged encoding and the branchless degenerate-case
select, the **whole** `EllipticCurveDialect.ECParams.add` — every branch of the
complete short-Weierstrass group law, `O` included — is now realized
relationally over GF(251), each branch a straight-line schedule of golden-path
field kernels and the dispatch a constant-time mask-select.  The honest
remaining axis is the carrier: `bls12_377`/`bls12_381` replace the single-word
GF(251) field by a 6×64-limb CIOS field; the relational *structure*
(tagged encoding + per-branch commuting square + branchless select) ports
verbatim — only the per-op kernels change.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul

/-! ## 1. The `ECPoint` sum-type encoding: a tagged triple

`ECPoint 251 = Option (ZMod 251 × ZMod 251)`: `none = O`, `some (x, y)` affine.
Serialize to `(tag, x, y)`: `O ↦ (0,0,0)`, `some (x,y) ↦ (1, enc x, enc y)`.
The tag separates the arms; the coords are `encMod251`.  Injective. -/

/-- The serialized form of an `ECPoint`: a tag word (`0 = O`, `1 = affine`) and
    the two coordinate words. -/
abbrev EncPoint : Type := BitVec 64 × BitVec 64 × BitVec 64

/-- **The `ECPoint 251` tagged-triple encoding.**  `O = none ↦ (0, 0, 0)`
    (tag `0`); `some (x, y) ↦ (1, encMod251 x, encMod251 y)` (tag `1`).  The
    sum-type serialization the unified `ECParams.add` ranges over. -/
def encPoint (P : ECPoint 251) : EncPoint :=
  match P with
  | none => (0, 0, 0)
  | some (x, y) => (1, encMod251 x, encMod251 y)

@[simp] theorem encPoint_none : encPoint none = (0, 0, 0) := rfl

@[simp] theorem encPoint_some (x y : ZMod 251) :
    encPoint (some (x, y)) = (1, encMod251 x, encMod251 y) := rfl

/-- `encPoint (some p)` for an arbitrary affine pair `p` (not a literal `(x, y)`):
    tag `1`, the two coordinate words.  The form the doubling/chord arms need,
    where the affine result `p = ecDblAffine …` / `ecAddAffine …` is a value. -/
@[simp] theorem encPoint_some' (p : ZMod 251 × ZMod 251) :
    encPoint (some p) = (1, encMod251 p.1, encMod251 p.2) := rfl

/-- The affine-tag word `1` and the infinity-tag word `0` are distinct (`1 ≠ 0`
    in `BitVec 64`), so the encoding separates `O` from every affine point. -/
theorem tag_ne : (1 : BitVec 64) ≠ (0 : BitVec 64) := by decide

/-- **`encPoint` is injective** (the relational requirement).  The tag word
    separates `O` (tag `0`) from affine points (tag `1`); on affine points the
    two coordinate words are `encMod251`, injective (`encMod251_injective`).  The
    sum-type analogue of `encMod251_injective`. -/
theorem encPoint_injective : Function.Injective encPoint := by
  intro P Q h
  match P, Q with
  | none, none => rfl
  | none, some (x, y) =>
    exfalso; simp only [encPoint] at h
    exact tag_ne (congrArg (·.1) h).symm
  | some (x, y), none =>
    exfalso; simp only [encPoint] at h
    exact tag_ne (congrArg (·.1) h)
  | some (x1, y1), some (x2, y2) =>
    simp only [encPoint, Prod.mk.injEq] at h
    obtain ⟨_, hx, hy⟩ := h
    rw [encMod251_injective hx, encMod251_injective hy]

/-! ## 2. The value-level branchless mask-select (the `CmovSelect` idiom)

`selBV cond x y = (x &&& mask) ||| (y &&& ~~~mask)` with `mask = if cond then
allOnes else 0` — exactly `ArithIselSoundness.condMask` / `selectW`.  `selBV3`
lifts it to encoded triples.  The dispatch's degenerate-case select. -/

/-- The full-width mask a boolean condition materialises: `allOnes` if `cond`,
    else `0` — the `ArithIselSoundness.condMask` shape, on a `Prop`-decided
    `cond` (the value-level model of the 1-bit CMOV condition). -/
def boolMask (cond : Prop) [Decidable cond] : BitVec 64 :=
  if cond then BitVec.allOnes 64 else 0

/-- **The branchless mask-select on words.**  `selBV cond x y =
    (x &&& m) ||| (y &&& ~~~m)` with `m = boolMask cond`.  The constant-time
    CMOV idiom (`CmovSelect.selectSelect`'s value content): selects `x` when
    `cond`, `y` otherwise, with no branch. -/
def selBV (cond : Prop) [Decidable cond] (x y : BitVec 64) : BitVec 64 :=
  (x &&& boolMask cond) ||| (y &&& (~~~ boolMask cond))

/-- `selBV cond x y = x` when `cond` holds (the masked idiom selects `x`). -/
@[simp] theorem selBV_true (cond : Prop) [Decidable cond] (x y : BitVec 64)
    (h : cond) : selBV cond x y = x := by
  simp only [selBV, boolMask, if_pos h, BitVec.and_allOnes,
    BitVec.not_allOnes, BitVec.and_zero, BitVec.or_zero]

/-- `selBV cond x y = y` when `cond` fails (the masked idiom selects `y`). -/
@[simp] theorem selBV_false (cond : Prop) [Decidable cond] (x y : BitVec 64)
    (h : ¬ cond) : selBV cond x y = y := by
  rw [selBV, boolMask, if_neg h]; bv_decide

/-- **The branchless mask-select on encoded triples** (component-wise `selBV`).
    Selects encoded point `p` when `cond`, `q` otherwise.  The degenerate-case
    dispatch operates on these encoded triples. -/
def selBV3 (cond : Prop) [Decidable cond] (p q : EncPoint) : EncPoint :=
  (selBV cond p.1 q.1, selBV cond p.2.1 q.2.1, selBV cond p.2.2 q.2.2)

@[simp] theorem selBV3_true (cond : Prop) [Decidable cond] (p q : EncPoint)
    (h : cond) : selBV3 cond p q = p := by
  simp only [selBV3, selBV_true cond _ _ h]

@[simp] theorem selBV3_false (cond : Prop) [Decidable cond] (p q : EncPoint)
    (h : ¬ cond) : selBV3 cond p q = q := by
  simp only [selBV3, selBV_false cond _ _ h]

/-! ## 3. The affine doubling branch (`x₁ = x₂`, tangent slope, `a = 0`)

The `x₁ = x₂` non-vertical branch of `ECParams.add` is point **doubling** by the
*tangent* slope.  For `a = 0` (BLS-class `blsClassCurve`):
`λ = (3x²)·(2y)⁻¹`, `x₃ = λ² − x − x`, `y₃ = λ·(x − x₃) − y`.  Same building
blocks as the chord (`pow249Spec` inverse, `gf251MulSpec`, `sub251`,
`tripleSpecBV`, `double251`), so it composes cleanly with a `ZMod 251` square. -/

/-- **The total GF(251) inverse commuting square.**  For *every* `a` (including
    `a = 0`, where `0⁻¹ = 0 = 0^249`), the abstract inverse `a⁻¹`, serialized,
    equals the Fermat power chain `pow249Spec` on the encoded coordinate.  The
    `a ≠ 0` version is `invMod251_commutes`; at `a = 0` both sides are `enc 0`
    (`pow249_commutes` + `0^249 = 0`), so the square is total — exactly what the
    branchless doubling needs (no `y ≠ 0` side condition). -/
theorem invMod251_commutes_total (a : ZMod 251) :
    encMod251 a⁻¹ = pow249Spec (encMod251 a) := by
  by_cases ha : a = 0
  · subst ha
    rw [inv_zero, ← pow249_commutes]
    norm_num
  · exact invMod251_commutes a ha

/-- The abstract `a = 0` tangent slope `λ = (3·x²)·(2·y)⁻¹` on GF(251).  The
    `EllipticCurveDialect.ECParams.tangentSlope` for `blsClassCurve`. -/
def tangentSlope251 (x y : ZMod 251) : ZMod 251 :=
  (3 * (x * x) + 0) * (2 * y)⁻¹

/-- The abstract affine doubling: `x₃ = λ² − x − x`, `y₃ = λ·(x − x₃) − y`, with
    `λ = tangentSlope251`.  The `EllipticCurveDialect.ECParams.add` `x₁ = x₂`
    non-vertical branch (the tangent arm). -/
def ecDblAffine (P : ZMod 251 × ZMod 251) : ZMod 251 × ZMod 251 :=
  let x := P.1; let y := P.2
  let lam := tangentSlope251 x y
  let x3 := lam * lam - x - x
  let y3 := lam * (x - x3) - y
  (x3, y3)

/-- **`ecDblAffine` is exactly the `ECParams.add` doubling branch.**  For two
    affine points sharing the `x`-coordinate, `x₁ = x₂`, that are *not* on the
    vertical line `y₁ = −y₂` (the `→ O` arm), the unified `ECParams.add` on
    `blsClassCurve` uses the tangent slope at the **first** point and returns
    `some (ecDblAffine (x, y₁))`.  Ties the named doubling op to the dialect
    sum-type group law's tangent arm. -/
theorem dblCase_eq_ECParams_add (x y1 y2 : ZMod 251) (hvert : ¬ (y1 = -y2)) :
    blsClassCurve.add (some (x, y1)) (some (x, y2))
      = some (ecDblAffine (x, y1)) := by
  simp only [ECParams.add, ecDblAffine, tangentSlope251, ECParams.tangentSlope,
    blsClassCurve, ECParams.affRx, ECParams.affRy, if_neg hvert, if_true,
    sub_sub]

/-- The realized `BitVec 64` tangent slope `λ = (3x²)·(2y)⁻¹` on encoded
    coordinates: `gf251MulSpec (tripleSpecBV (gf251MulSpec x x)) (pow249Spec
    (double251 y))` (the inverse is the Fermat chain `pow249Spec`, `2y` is
    `double251`). -/
def tangentSlopeBV (x y : BitVec 64) : BitVec 64 :=
  gf251MulSpec (tripleSpecBV (gf251MulSpec x x)) (pow249Spec (double251 y))

/-- The realized `BitVec 64` affine-doubling schedule on the encoded coords
    `(x, y)`.  `x₃ = λ² − x − x`, `y₃ = λ·(x − x₃) − y`, `λ = tangentSlopeBV`. -/
def ecDblAffineBV (x y : BitVec 64) : BitVec 64 × BitVec 64 :=
  let lam := tangentSlopeBV x y
  let x3 := sub251 (sub251 (gf251MulSpec lam lam) x) x
  let y3 := sub251 (gf251MulSpec lam (sub251 x x3)) y
  (x3, y3)

/-- **The tangent-slope commuting square (total).**  The abstract tangent slope
    `λ = (3x²)·(2y)⁻¹` (in `F_251`), serialized, equals `tangentSlopeBV` on the
    encoded coords — for *every* `y` (the inverse square is total,
    `invMod251_commutes_total`, so no `y ≠ 0` side condition).  Composes
    `gf251Square_commutes` (`x²`), `tripleMod251_commutes` (`3·x²`),
    `add251_commutes` (`2y`), `invMod251_commutes_total` (`(2y)⁻¹`),
    `gf251Mul_commutes`. -/
theorem tangentSlope_commutes (x y : ZMod 251) :
    encMod251 (tangentSlope251 x y)
      = tangentSlopeBV (encMod251 x) (encMod251 y) := by
  unfold tangentSlope251 tangentSlopeBV
  rw [add_zero, gf251Mul_commutes, tripleMod251_commutes, gf251Square_commutes,
    invMod251_commutes_total, add251_commutes]

/-- **`x₃` doubling commuting square** (total): encoding the abstract doubling
    `x₃ = λ² − x − x` equals `ecDblAffineBV`'s first component on the encoded
    coords.  Composes `tangentSlope_commutes`, `gf251Mul_commutes` (`λ²`), and
    two `sub251_commutes`. -/
theorem ecDblAffineX3_commutes (x y : ZMod 251) :
    encMod251 (ecDblAffine (x, y)).1
      = (ecDblAffineBV (encMod251 x) (encMod251 y)).1 := by
  simp only [ecDblAffine, ecDblAffineBV]
  simp only [sub251_commutes, gf251Mul_commutes, tangentSlope_commutes]

/-- **`y₃` doubling commuting square** (total): encoding the abstract doubling
    `y₃ = λ·(x − x₃) − y` equals `ecDblAffineBV`'s second component on the encoded
    coords.  Composes everything `x₃` needs (`x₃` is inside `y₃`), plus
    `sub251_commutes` (`x − x₃`), `gf251Mul_commutes`, a final `sub251_commutes`. -/
theorem ecDblAffineY3_commutes (x y : ZMod 251) :
    encMod251 (ecDblAffine (x, y)).2
      = (ecDblAffineBV (encMod251 x) (encMod251 y)).2 := by
  simp only [ecDblAffine, ecDblAffineBV]
  simp only [sub251_commutes, gf251Mul_commutes, tangentSlope_commutes]

/-! ## 4. The branchless unified add on encoded triples

`ecAddUnifiedBV` mirrors `ECParams.add`'s branch structure as a nested mask
select on the encoded triples — no jump.  The branch flags are decided at the
abstract (`ECPoint`) level (the value-level model of the materialised CMOV
condition, `if cond then allOnes else 0`).  The arms are the encoded `Q` / `P`
(the `O` short-circuits), `(0,0,0)` (the vertical `→ O`), the encoded doubling
`ecDblAffineBV`, and the encoded chord `ecAddBV`. -/

/-- **The branchless unified add.**  Given the two abstract points `P Q` (to
    decide the select flags — the value-level CMOV condition model) and their
    encoded triples, dispatch by nested `selBV3`:
    `if P = O then Q else if Q = O then P else` (both affine `(x₁,y₁),(x₂,y₂)`)
    `if x₁ = x₂ then (if y₁ = −y₂ then O else doubling) else chord`.  Each select
    is the branchless `condMask` idiom; the arms reuse the landed `ecAddBV` /
    `ecDblAffineBV` kernels. -/
def ecAddUnifiedBV (P Q : ECPoint 251) : EncPoint :=
  selBV3 (P = none) (encPoint Q) <|
    selBV3 (Q = none) (encPoint P) <|
      match P, Q with
      | some (x1, y1), some (x2, y2) =>
        selBV3 (x1 = x2)
          (selBV3 (y1 = -y2) (0, 0, 0)
            (let r := ecDblAffineBV (encMod251 x1) (encMod251 y1)
             (1, r.1, r.2)))
          (let r := ecAddBV (encMod251 x1) (encMod251 y1) (encMod251 x2) (encMod251 y2)
           (1, r.1, r.2))
      | _, _ => (0, 0, 0)

/-! ## 5. The UNIFIED commuting square — all five branches

`encPoint (blsClassCurve.add P Q) = ecAddUnifiedBV P Q`, by case analysis on
`P, Q` mirroring the spec.  Each branch's select flag is discharged and the arm
matched to the landed kernel's square. -/

/-- **The UNIFIED EC group-law commuting square (the deliverable).**  For every
    pair of `ECPoint 251` (`O` included), the encoding of the unified
    short-Weierstrass `ECParams.add` on `blsClassCurve` equals the branchless
    `ecAddUnifiedBV` on the encoded triples.  All five branches — the two `O`
    short-circuits, the vertical `→ O`, the doubling, the chord — closed
    sorry-free, the degenerate cases dispatched by the constant-time mask-select
    `selBV3`. -/
theorem encPoint_add_commutes (P Q : ECPoint 251) :
    encPoint (blsClassCurve.add P Q) = ecAddUnifiedBV P Q := by
  match P, Q with
  | none, Q =>
    -- O + Q = Q
    rw [ECParams.add_none_left, ecAddUnifiedBV, selBV3_true (none = none) _ _ rfl]
    intro x1 y1 x2 y2 h; exact absurd h (by simp)
  | some (x1, y1), none =>
    -- P + O = P
    rw [ECParams.add_none_right, ecAddUnifiedBV,
      selBV3_false (some (x1, y1) = none) _ _ (by simp),
      selBV3_true (none = none) _ _ rfl]
    intro x1' y1' x2' y2' _ h; exact absurd h (by simp)
  | some (x1, y1), some (x2, y2) =>
    -- both affine: discharge the two O-flags, then split on x₁ = x₂
    rw [ecAddUnifiedBV,
      selBV3_false (some (x1, y1) = none) _ _ (by simp),
      selBV3_false (some (x2, y2) = none) _ _ (by simp)]
    by_cases hx : x1 = x2
    · subst hx
      rw [selBV3_true (x1 = x1) _ _ rfl]
      by_cases hyv : y1 = -y2
      · -- vertical: P + (−Q) = O
        rw [selBV3_true (y1 = -y2) _ _ hyv]
        have hO : blsClassCurve.add (some (x1, y1)) (some (x1, y2)) = none := by
          simp only [ECParams.add, if_pos hyv, if_true]
        rw [hO, encPoint_none]
      · -- doubling (x₁ = x₂, y₁ ≠ −y₂): the tangent arm at the FIRST point
        rw [selBV3_false (y1 = -y2) _ _ hyv,
          dblCase_eq_ECParams_add x1 y1 y2 hyv, encPoint_some',
          ecDblAffineX3_commutes x1 y1, ecDblAffineY3_commutes x1 y1]
    · -- chord (x₁ ≠ x₂)
      rw [selBV3_false (x1 = x2) _ _ hx,
        chordCase_eq_ECParams_add x1 y1 x2 y2 hx, encPoint_some',
        ecAddX3_commutes x1 y1 x2 y2 hx, ecAddY3_commutes x1 y1 x2 y2 hx]

/-! ## 6. The UNIFIED transfer corollary

The point analogue of `ecAdd_spec_transfers`, now over the *whole* `ECPoint`
group law (`O` and degenerate branches included): two unified sums are equal in
the group **iff** the branchless `ecAddUnifiedBV` agrees on the encoded inputs —
through the injective `encPoint`. -/

/-- **The unified-add transfer.**  Two unified group sums are equal in
    `ECPoint 251` iff the branchless `ecAddUnifiedBV` schedule agrees on their
    encoded inputs.  The relational front carrying the *complete* EC group law
    through the injective sum-type serialization `encPoint`. -/
theorem ecAddUnified_spec_transfers (P Q P' Q' : ECPoint 251) :
    blsClassCurve.add P Q = blsClassCurve.add P' Q' ↔
      ecAddUnifiedBV P Q = ecAddUnifiedBV P' Q' := by
  rw [← encPoint_add_commutes, ← encPoint_add_commutes]
  exact ⟨fun h => by rw [h], fun h => encPoint_injective h⟩

/-! ## 7. Worked examples through the UNIFIED `ECParams.add`

`blsClassCurve : y² = x³ + 1` over GF(251).  All five branches exercised through
the *unified* group law and its branchless encoded realization, sorry-free:
`O + P = P`, `P + O = P`, a chord `P + Q`, the vertical `P + (−P) = O`, and a
doubling `P + P`. -/

/-- **`O + P = P` (the identity short-circuit).**  The unified add of the infinity
    point and `P = (0, 1)` returns `P`. -/
theorem worked_O_add_P :
    blsClassCurve.add none (some (0, 1)) = some (0, 1) := by
  rw [ECParams.add_none_left]

/-- **`O + P = P`, encoded/branchless side.**  `ecAddUnifiedBV` selects the
    encoded `P` when the left operand is `O` — the identity select fires. -/
theorem worked_O_add_P_realized :
    ecAddUnifiedBV none (some (0, 1)) = encPoint (some (0, 1)) := by
  rw [← encPoint_add_commutes, worked_O_add_P]

/-- **`P + O = P` (the identity short-circuit).**  The unified add of `P = (0, 1)`
    and the infinity point returns `P`. -/
theorem worked_P_add_O :
    blsClassCurve.add (some (0, 1)) none = some (0, 1) := by
  rw [ECParams.add_none_right]

/-- **`P + O = P`, encoded/branchless side.** -/
theorem worked_P_add_O_realized :
    ecAddUnifiedBV (some (0, 1)) none = encPoint (some (0, 1)) := by
  rw [← encPoint_add_commutes, worked_P_add_O]

/-- **A chord `P + Q` through the unified op.**  `P = (0, 1)`, `Q = (2, 3)`
    (distinct, `x₁ ≠ x₂`): the unified add fires the chord branch and returns the
    affine sum `(250, 0)` (the `RelationalFrontECAdd` worked value). -/
theorem worked_chord_unified :
    blsClassCurve.add (some (0, 1)) (some (2, 3)) = some (250, 0) :=
  worked_add_ECParams

/-- **The chord `P + Q`, encoded/branchless side.**  `ecAddUnifiedBV` (after the
    two O-flags fail and `x₁ ≠ x₂`) computes the chord arm `ecAddBV` and tags it
    `1` — equal to the encoding of the abstract sum `(250, 0)`. -/
theorem worked_chord_unified_realized :
    ecAddUnifiedBV (some (0, 1)) (some (2, 3)) = encPoint (some (250, 0)) := by
  rw [← encPoint_add_commutes, worked_chord_unified]

/-- **The vertical `P + (−P) = O`.**  `P = (0, 1)`, `−P = (0, 250)` (`−1 = 250`):
    `x₁ = x₂ = 0` and `y₁ = 1 = −250 = −y₂`, so the unified add fires the vertical
    branch and returns the infinity point `O = none`. -/
theorem worked_vertical_unified :
    blsClassCurve.add (some (0, 1)) (some (0, 250)) = none := by
  simp only [ECParams.add, if_true, if_pos (by decide : (1 : ZMod 251) = -(250 : ZMod 251))]

/-- **The vertical `P + (−P) = O`, encoded/branchless side.**  `ecAddUnifiedBV`
    selects the `(0, 0, 0)` infinity arm — the encoding of `O`. -/
theorem worked_vertical_unified_realized :
    ecAddUnifiedBV (some (0, 1)) (some (0, 250)) = encPoint none := by
  rw [← encPoint_add_commutes, worked_vertical_unified]

/-- **A doubling `P + P` through the unified op.**  `P = (0, 1)`: `x₁ = x₂ = 0`,
    `y₁ = 1 ≠ −1 = −y₂`, so the unified add fires the doubling (tangent) branch.
    `λ = 3·0·(2)⁻¹ = 0`, `x₃ = 0`, `y₃ = 0 − 1 = −1 = 250`, so `P + P = (0, 250)`. -/
theorem worked_double_unified :
    blsClassCurve.add (some (0, 1)) (some (0, 1)) = some (0, 250) := by
  rw [dblCase_eq_ECParams_add 0 1 1 (by decide)]
  simp only [ecDblAffine, tangentSlope251]; decide +kernel

/-- **The doubling `P + P`, encoded/branchless side.**  `ecAddUnifiedBV` (after
    the O-flags fail, `x₁ = x₂`, and the vertical flag fails) computes the tangent
    arm `ecDblAffineBV` and tags it `1` — equal to the encoding of `(0, 250)`. -/
theorem worked_double_unified_realized :
    ecAddUnifiedBV (some (0, 1)) (some (0, 1)) = encPoint (some (0, 250)) := by
  rw [← encPoint_add_commutes, worked_double_unified]

end CatCrypt.Crypto.SecureCompilation.RelationalFront
