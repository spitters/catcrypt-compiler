/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp2

/-!
# The `bls12_377` cubic tower `Fp6 = Fp2[v]/(v³ − ξ₆)` and dodecic `Fp12`, KARATSUBA mul

`RelationalFrontBls377Fp2` closes the `bls12_377` quadratic extension `Fp2` over
the relational 6×64-bit base carrier, with its Karatsuba-equals-schoolbook mul
and a `CommRing` structure. The pairing-field carrier needs two more tower
levels: the **cubic** extension `Fp6 = Fp2[v]/(v³ − ξ₆)` and the **dodecic**
extension `Fp12 = Fp6[w]/(w² − v)`. This module builds both over the relational
`Fp2_377`, mirroring `Pairing/Fp6Fp12TowerImport.lean`'s cubic / quadratic tower
schedules, and proves each Karatsuba multiply equals its schoolbook denotation.

## What this module proves

### Fp6 (cubic) — Karatsuba over Fp2 (6 Fp2 muls vs schoolbook's 9)

With `v³ = ξ₆` (`ξ₆ : Fp2_377` a nonresidue, kept parametric), the schoolbook
product of `a = a₀ + a₁v + a₂v²` and `b = b₀ + b₁v + b₂v²` is the nine-`Fp2`-mul
expansion reduced by `v³ = ξ₆`. The Karatsuba (Toom-3 cross-term) schedule
computes the three "diagonal" products `a₀b₀, a₁b₁, a₂b₂` and the three
cross terms via `(aᵢ+aⱼ)(bᵢ+bⱼ) − aᵢbᵢ − aⱼbⱼ` — six `Fp2` muls — and recovers
each output coordinate with the `mul_xi`-by-`ξ₆` nonresidue folds. This matches
the `CubicFieldExtensions.Fp6_mul` schedule the tower importer pins.

`fp6_mulKaratsuba_eq_schoolbook`: the two agree for any nonresidue `ξ₆` — `ext`
then `ring` over the `Fp2_377` `CommRing`. This is the correctness
fact for emitting a 6-mul `Fp6` multiply.

### Fp12 (dodecic) — Karatsuba over Fp6 (3 Fp6 muls vs schoolbook's 4)

With `w² = v` (the `Fp12` nonresidue is the `Fp6` generator `v`, realized by the
`mulByV` map `Fp6 → Fp6`, the dodecic analogue of `Fp2`'s `mul_xi`), the
quadratic-extension Karatsuba over `Fp6` mirrors the `Fp2` layer one level up:
`v0 = a₀b₀`, `v1 = a₁b₁`, `mid = (a₀+a₁)(b₀+b₁)`; `c0 = v0 + mulByV v1`,
`c1 = mid − v0 − v1`. `fp12_mulKaratsuba_eq_schoolbook` closes it the same way.

## Honesty boundary

This is the abstract `Fp6` / `Fp12` tower algebra over the relational `bls12_377`
base carrier and the Karatsuba optimizations' correctness. It does **not** wire
the tower multiplies down to emitted base kernels (the `BaseSubstrate` lift), nor
does it prove `Fp6` / `Fp12` are *fields* (that needs `ξ₆` / `v` non-residuosity,
a number-theoretic fact about the concrete `bls12_377` twist parameters). It is
the field-algebra gateway above the `Fp2` layer (`RelationalFrontBls377Fp2`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 0. The `Fp2_377` `CommRing` as a local instance (parametric in `ξ₂`)

`RelationalFrontBls377Fp2` exposes `Fp2_377.commRing ξ₂ : CommRing Fp2_377` as a
`@[reducible] def` (not a global instance, since it carries the nonresidue
`ξ₂`). The `Fp6` / `Fp12` tower over `Fp2_377` needs that `CommRing` in scope so
`ring` can normalize the cubic / quadratic expansions; we attach it locally per
definition / proof via `letI`. -/

/-! ## 1. The cubic extension `Fp6_377 = Fp2_377[v]/(v³ − ξ₆)`

`Fp6_377` is three `Fp2_377` coordinates `c0 + c1·v + c2·v²`, with `v³ = ξ₆` for
a nonresidue parameter `ξ₆ : Fp2_377`. The layout matches the AUCurves /
`Fp6Fp12TowerImport` cubic component order (`c0`/`c1`/`c2`). -/

/-- An element of the `bls12_377` cubic extension `Fp6_377 = Fp2[v]/(v³ − ξ₆)`:
    `c0 + c1·v + c2·v²`, with `c0, c1, c2 : Fp2_377`. -/
@[ext]
structure Fp6_377 where
  /-- The `1`-component `c0` of `c0 + c1·v + c2·v²`. -/
  c0 : Fp2_377
  /-- The `v`-component `c1`. -/
  c1 : Fp2_377
  /-- The `v²`-component `c2`. -/
  c2 : Fp2_377

namespace Fp6_377

/-! ## 2. Componentwise zero / one / add / neg / sub (`ξ`-independent)

These mirror the `Fp2_377` componentwise instances, one tower level up: the
`Fp2_377` componentwise `Zero/One/Add/Neg/Sub` (global instances in the `Fp2`
file) lift coordinatewise to `Fp6_377`. None depend on either nonresidue. -/

/-- Zero of `Fp6_377` (`0 + 0·v + 0·v²`). -/
instance : Zero Fp6_377 := ⟨⟨0, 0, 0⟩⟩
/-- One of `Fp6_377` (`1 + 0·v + 0·v²`). -/
instance : One Fp6_377 := ⟨⟨1, 0, 0⟩⟩
/-- Componentwise `Fp6_377` addition. -/
instance : Add Fp6_377 := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
/-- Componentwise `Fp6_377` negation. -/
instance : Neg Fp6_377 := ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩
/-- Componentwise `Fp6_377` subtraction. -/
instance : Sub Fp6_377 := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2⟩⟩

@[simp] theorem zero_c0 : (0 : Fp6_377).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp6_377).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp6_377).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp6_377).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp6_377).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp6_377).c2 = 0 := rfl
@[simp] theorem add_c0 (x y : Fp6_377) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : Fp6_377) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem add_c2 (x y : Fp6_377) : (x + y).c2 = x.c2 + y.c2 := rfl
@[simp] theorem neg_c0 (x : Fp6_377) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : Fp6_377) : (-x).c1 = -x.c1 := rfl
@[simp] theorem neg_c2 (x : Fp6_377) : (-x).c2 = -x.c2 := rfl
@[simp] theorem sub_c0 (x y : Fp6_377) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : Fp6_377) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem sub_c2 (x y : Fp6_377) : (x - y).c2 = x.c2 - y.c2 := rfl

/-! ## 3. The two cubic multiplications

Both multiplies are parametric in the base nonresidue `ξ₂` (the `Fp2` multiply's
parameter) and the cubic nonresidue `ξ₆ : Fp2_377` (`v³ = ξ₆`). We abbreviate the
base `Fp2` schoolbook product as `mul₂` for readability. The `Fp2` multiply is
schoolbook (the field's canonical denotation); `Fp2` add/sub are the global
componentwise instances. -/

/-- The base-field (`Fp2_377`) schoolbook product at nonresidue `ξ₂`. -/
abbrev mul₂ (ξ₂ : FpBLS377) (a b : Fp2_377) : Fp2_377 := Fp2_377.mulSchoolbook ξ₂ a b

/-- **Schoolbook `Fp6_377` multiply** (9 `Fp2` muls): the full
    `(a₀+a₁v+a₂v²)(b₀+b₁v+b₂v²)` expansion reduced by `v³ = ξ₆`:

    `c0 = a₀b₀ + ξ₆(a₁b₂ + a₂b₁)`
    `c1 = a₀b₁ + a₁b₀ + ξ₆ a₂b₂`
    `c2 = a₀b₂ + a₁b₁ + a₂b₀`. -/
def mulSchoolbook (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp6_377) : Fp6_377 :=
  letI := Fp2_377.commRing ξ₂
  Fp6_377.mk
    (mul₂ ξ₂ x.c0 y.c0
      + mul₂ ξ₂ ξ₆ (mul₂ ξ₂ x.c1 y.c2 + mul₂ ξ₂ x.c2 y.c1))
    (mul₂ ξ₂ x.c0 y.c1 + mul₂ ξ₂ x.c1 y.c0
      + mul₂ ξ₂ ξ₆ (mul₂ ξ₂ x.c2 y.c2))
    (mul₂ ξ₂ x.c0 y.c2 + mul₂ ξ₂ x.c1 y.c1 + mul₂ ξ₂ x.c2 y.c0)

/-- **Karatsuba / Toom-3 `Fp6_377` multiply** (6 `Fp2` muls): the three diagonal
    products `v0 = a₀b₀`, `v1 = a₁b₁`, `v2 = a₂b₂`, and three cross terms recovered
    by `(aᵢ+aⱼ)(bᵢ+bⱼ) − aᵢbᵢ − aⱼbⱼ`:

    `c12 = (a₁+a₂)(b₁+b₂) − v1 − v2  (= a₁b₂ + a₂b₁)`
    `c01 = (a₀+a₁)(b₀+b₁) − v0 − v1  (= a₀b₁ + a₁b₀)`
    `c02 = (a₀+a₂)(b₀+b₂) − v0 − v2  (= a₀b₂ + a₂b₀)`

    then `c0 = v0 + ξ₆ c12`, `c1 = c01 + ξ₆ v2`, `c2 = c02 + v1`. Six `Fp2` muls
    (three diagonal + three cross) instead of schoolbook's nine. -/
def mulKaratsuba (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp6_377) : Fp6_377 :=
  letI := Fp2_377.commRing ξ₂
  let v0 := mul₂ ξ₂ x.c0 y.c0
  let v1 := mul₂ ξ₂ x.c1 y.c1
  let v2 := mul₂ ξ₂ x.c2 y.c2
  let c12 := mul₂ ξ₂ (x.c1 + x.c2) (y.c1 + y.c2) - v1 - v2
  let c01 := mul₂ ξ₂ (x.c0 + x.c1) (y.c0 + y.c1) - v0 - v1
  let c02 := mul₂ ξ₂ (x.c0 + x.c2) (y.c0 + y.c2) - v0 - v2
  Fp6_377.mk
    (v0 + mul₂ ξ₂ ξ₆ c12)
    (c01 + mul₂ ξ₂ ξ₆ v2)
    (c02 + v1)

/-! ## 4. **Fp6 Karatsuba = schoolbook** — the semantics-preserving optimization -/

/-- **The Karatsuba `Fp6_377` multiply equals the schoolbook multiply** for any
    base nonresidue `ξ₂` and cubic nonresidue `ξ₆`. The Toom-3 cross-term recovery
    of `a₁b₂+a₂b₁`, `a₀b₁+a₁b₀`, `a₀b₂+a₂b₀` is denotation-preserving: each output
    coordinate agrees over the `Fp2_377` `CommRing` by `ring`. Used for a
    6-mul `Fp6` multiply. -/
theorem mulKaratsuba_eq_schoolbook (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp6_377) :
    mulKaratsuba ξ₂ ξ₆ x y = mulSchoolbook ξ₂ ξ₆ x y := by
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  ext <;> · simp only [mulKaratsuba, mulSchoolbook, hm] <;> ring

/-! ## 5. The `CommRing` structure on `Fp6_377` (schoolbook mul)

`Fp6_377 ξ₂ ξ₆` is a commutative ring: componentwise add/sub/neg and the
schoolbook cubic mul with the `v³ = ξ₆` reduction. Every axiom reduces to a
componentwise `Fp2_377`-identity, closed by `ext` then `ring` over the `Fp2_377`
`CommRing`. -/

/-- **`Fp6_377` is a commutative ring** (`Fp2_377[v]/(v³ − ξ₆)`) for any base
    nonresidue `ξ₂` and cubic nonresidue `ξ₆`. Every axiom is a componentwise
    `Fp2_377`-identity after the `v³ = ξ₆` reduction; `ext` then `ring` closes
    each. -/
@[reducible] def commRing (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) : CommRing Fp6_377 :=
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  { add := (· + ·)
    add_assoc := fun a b c => by ext <;> simp only [add_c0, add_c1, add_c2] <;> ring
    zero := 0
    zero_add := fun a => by ext <;> simp only [add_c0, add_c1, add_c2, zero_c0, zero_c1, zero_c2] <;> ring
    add_zero := fun a => by ext <;> simp only [add_c0, add_c1, add_c2, zero_c0, zero_c1, zero_c2] <;> ring
    nsmul := nsmulRec
    add_comm := fun a b => by ext <;> simp only [add_c0, add_c1, add_c2] <;> ring
    mul := mulSchoolbook ξ₂ ξ₆
    left_distrib := fun a b c => by
      show mulSchoolbook ξ₂ ξ₆ a (b + c)
        = mulSchoolbook ξ₂ ξ₆ a b + mulSchoolbook ξ₂ ξ₆ a c
      ext <;> · simp only [mulSchoolbook, hm, add_c0, add_c1, add_c2] <;> ring
    right_distrib := fun a b c => by
      show mulSchoolbook ξ₂ ξ₆ (a + b) c
        = mulSchoolbook ξ₂ ξ₆ a c + mulSchoolbook ξ₂ ξ₆ b c
      ext <;> · simp only [mulSchoolbook, hm, add_c0, add_c1, add_c2] <;> ring
    zero_mul := fun a => by
      show mulSchoolbook ξ₂ ξ₆ 0 a = 0
      ext <;> · simp only [mulSchoolbook, hm, zero_c0, zero_c1, zero_c2] <;> ring
    mul_zero := fun a => by
      show mulSchoolbook ξ₂ ξ₆ a 0 = 0
      ext <;> · simp only [mulSchoolbook, hm, zero_c0, zero_c1, zero_c2] <;> ring
    mul_assoc := fun a b c => by
      show mulSchoolbook ξ₂ ξ₆ (mulSchoolbook ξ₂ ξ₆ a b) c
        = mulSchoolbook ξ₂ ξ₆ a (mulSchoolbook ξ₂ ξ₆ b c)
      ext <;> · simp only [mulSchoolbook, hm] <;> ring
    one := 1
    one_mul := fun a => by
      show mulSchoolbook ξ₂ ξ₆ 1 a = a
      ext <;> · simp only [mulSchoolbook, hm, one_c0, one_c1, one_c2] <;> ring
    mul_one := fun a => by
      show mulSchoolbook ξ₂ ξ₆ a 1 = a
      ext <;> · simp only [mulSchoolbook, hm, one_c0, one_c1, one_c2] <;> ring
    neg := Neg.neg
    zsmul := zsmulRec
    sub_eq_add_neg := fun a b => by ext <;> simp only [sub_c0, sub_c1, sub_c2, add_c0, add_c1, add_c2, neg_c0, neg_c1, neg_c2] <;> ring
    neg_add_cancel := fun a => by ext <;> simp only [add_c0, add_c1, add_c2, neg_c0, neg_c1, neg_c2, zero_c0, zero_c1, zero_c2] <;> ring
    mul_comm := fun a b => by
      show mulSchoolbook ξ₂ ξ₆ a b = mulSchoolbook ξ₂ ξ₆ b a
      ext <;> · simp only [mulSchoolbook, hm] <;> ring }

/-- **Schoolbook `Fp6_377` multiply is commutative.** -/
theorem mulSchoolbook_comm (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp6_377) :
    mulSchoolbook ξ₂ ξ₆ x y = mulSchoolbook ξ₂ ξ₆ y x := by
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  ext <;> · simp only [mulSchoolbook, hm] <;> ring

/-- **Karatsuba `Fp6_377` multiply is commutative** — immediate from
    `mulKaratsuba_eq_schoolbook` and `mulSchoolbook_comm`. -/
theorem mulKaratsuba_comm (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp6_377) :
    mulKaratsuba ξ₂ ξ₆ x y = mulKaratsuba ξ₂ ξ₆ y x := by
  rw [mulKaratsuba_eq_schoolbook, mulKaratsuba_eq_schoolbook, mulSchoolbook_comm]

/-! ## 6. The Fp6 nonresidue multiply `mulByV` (`× v`)

`Fp12 = Fp6[w]/(w² − v)` uses the `Fp6` generator `v` as its quadratic
nonresidue. Multiplying `a₀ + a₁v + a₂v²` by `v` gives `a₂ξ₆ + a₀v + a₁v²` (the
`v³ = ξ₆` reduction folds the top coordinate back down). This is the dodecic
analogue of `Fp2`'s `mul_xi`. -/

/-- **Multiply an `Fp6_377` element by the generator `v`**: with `v³ = ξ₆`,
    `(a₀+a₁v+a₂v²)·v = a₂ξ₆ + a₀v + a₁v²`. -/
def mulByV (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) : Fp6_377 :=
  Fp6_377.mk (mul₂ ξ₂ x.c2 ξ₆) x.c0 x.c1

@[simp] theorem mulByV_c0 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) :
    (mulByV ξ₂ ξ₆ x).c0 = mul₂ ξ₂ x.c2 ξ₆ := rfl
@[simp] theorem mulByV_c1 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) :
    (mulByV ξ₂ ξ₆ x).c1 = x.c0 := rfl
@[simp] theorem mulByV_c2 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) :
    (mulByV ξ₂ ξ₆ x).c2 = x.c1 := rfl

/-- **`mulByV` is additive** — `(x + y)·v = x·v + y·v`. The `c0` coordinate
    distributes (`(x.c2 + y.c2)·ξ₆ = x.c2·ξ₆ + y.c2·ξ₆` over the `Fp2_377`
    `CommRing`); the `c1`/`c2` coordinates are componentwise adds. Lets `ring`
    treat the dodecic non-residue fold as a linear atom in the `Fp12` proofs. -/
@[simp] theorem mulByV_add (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp6_377) :
    mulByV ξ₂ ξ₆ (x + y) = mulByV ξ₂ ξ₆ x + mulByV ξ₂ ξ₆ y := by
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  ext <;> · simp only [mulByV, add_c0, add_c1, add_c2, hm] <;> ring

/-- **`mulByV` kills zero** — `0·v = 0`. -/
@[simp] theorem mulByV_zero (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) :
    mulByV ξ₂ ξ₆ 0 = 0 := by
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  ext <;> · simp only [mulByV, zero_c0, zero_c1, zero_c2, hm] <;> ring

/-- The cubic generator `v = 0 + 1·v + 0·v²` as an `Fp6_377` element. -/
def vGen : Fp6_377 := ⟨0, 1, 0⟩

/-- **`mulByV` is left-multiplication by the generator `v`** in the `Fp6_377`
    `CommRing`: `x·v = vGen · x`. With this the `Fp12` non-residue fold is a
    `Fp6` ring multiply, so the `Fp12` ring axioms (including
    associativity) reduce to `Fp6`-ring identities `ring` proves with the cubic
    multiply kept opaque. -/
theorem mulByV_eq_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x : Fp6_377) :
    mulByV ξ₂ ξ₆ x = mulSchoolbook ξ₂ ξ₆ vGen x := by
  letI := Fp2_377.commRing ξ₂
  have hm : ∀ a b : Fp2_377, mul₂ ξ₂ a b = a * b := fun _ _ => rfl
  ext <;> · simp only [mulByV, mulSchoolbook, vGen, hm] <;> ring

/-! ## 7. A worked example: Fp6 Karatsuba = schoolbook on concrete small inputs -/

/-- A concrete `Fp6_377` element `(1+2u) + (3+4u)v + (5+6u)v²`. -/
def example_x : Fp6_377 := ⟨⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩⟩
/-- A concrete `Fp6_377` element `(7+8u) + (9+10u)v + (11+12u)v²`. -/
def example_y : Fp6_377 := ⟨⟨7, 8⟩, ⟨9, 10⟩, ⟨11, 12⟩⟩

/-- **Worked example — Fp6.** On the concrete operands with base nonresidue
    `ξ₂ = 5` and cubic nonresidue `ξ₆ = 2 + 3u`, the Karatsuba multiply agrees
    with the schoolbook multiply — an instance of `mulKaratsuba_eq_schoolbook`. -/
theorem example_karatsuba_eq_schoolbook :
    mulKaratsuba 5 ⟨2, 3⟩ example_x example_y
      = mulSchoolbook 5 ⟨2, 3⟩ example_x example_y :=
  mulKaratsuba_eq_schoolbook 5 ⟨2, 3⟩ example_x example_y

end Fp6_377

/-! ## 8. The dodecic extension `Fp12_377 = Fp6_377[w]/(w² − v)`

`Fp12_377` is two `Fp6_377` coordinates `c0 + c1·w`, with `w² = v` (the `Fp6`
generator, applied via `Fp6_377.mulByV`). This mirrors the `Fp2` quadratic layer
one tower level up: the Karatsuba multiply does three `Fp6` muls (vs schoolbook's
four), recovering the off-diagonal via the same `(a+b)(c+d) − ac − bd` trick. -/

/-- An element of the `bls12_377` dodecic extension `Fp12_377 = Fp6[w]/(w² − v)`:
    `c0 + c1·w`, with `c0, c1 : Fp6_377`. -/
@[ext]
structure Fp12_377 where
  /-- The `1`-component `c0` of `c0 + c1·w`. -/
  c0 : Fp6_377
  /-- The `w`-component `c1`. -/
  c1 : Fp6_377

namespace Fp12_377

/-! ## 9. Componentwise zero / one / add / neg / sub -/

/-- Zero of `Fp12_377` (`0 + 0·w`). -/
instance : Zero Fp12_377 := ⟨⟨0, 0⟩⟩
/-- One of `Fp12_377` (`1 + 0·w`). -/
instance : One Fp12_377 := ⟨⟨1, 0⟩⟩
/-- Componentwise `Fp12_377` addition. -/
instance : Add Fp12_377 := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
/-- Componentwise `Fp12_377` negation. -/
instance : Neg Fp12_377 := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
/-- Componentwise `Fp12_377` subtraction. -/
instance : Sub Fp12_377 := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩

@[simp] theorem zero_c0 : (0 : Fp12_377).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp12_377).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp12_377).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp12_377).c1 = 0 := rfl
@[simp] theorem add_c0 (x y : Fp12_377) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : Fp12_377) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem neg_c0 (x : Fp12_377) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : Fp12_377) : (-x).c1 = -x.c1 := rfl
@[simp] theorem sub_c0 (x y : Fp12_377) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : Fp12_377) : (x - y).c1 = x.c1 - y.c1 := rfl

/-! ## 10. The two dodecic multiplications

The `Fp6` schoolbook product `mul₆` is the base multiply; `w² = v` is realized by
`Fp6_377.mulByV`. With `a = a₀ + a₁w`, `b = b₀ + b₁w`:

* schoolbook: `c0 = a₀b₀ + v·(a₁b₁)`, `c1 = a₀b₁ + a₁b₀` (4 `Fp6` muls);
* Karatsuba: `v0 = a₀b₀`, `v1 = a₁b₁`, `mid = (a₀+a₁)(b₀+b₁)`;
  `c0 = v0 + mulByV v1`, `c1 = mid − v0 − v1` (3 `Fp6` muls). -/

/-- The base-field (`Fp6_377`) schoolbook product. -/
abbrev mul₆ (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (a b : Fp6_377) : Fp6_377 :=
  Fp6_377.mulSchoolbook ξ₂ ξ₆ a b

/-- **Schoolbook `Fp12_377` multiply** (4 `Fp6` muls): `(a₀+a₁w)(b₀+b₁w) =
    (a₀b₀ + v·a₁b₁) + (a₀b₁ + a₁b₀)·w`, with `v·(·)` the `mulByV` nonresidue fold. -/
def mulSchoolbook (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp12_377) : Fp12_377 :=
  letI := Fp6_377.commRing ξ₂ ξ₆
  Fp12_377.mk
    (mul₆ ξ₂ ξ₆ x.c0 y.c0 + Fp6_377.mulByV ξ₂ ξ₆ (mul₆ ξ₂ ξ₆ x.c1 y.c1))
    (mul₆ ξ₂ ξ₆ x.c0 y.c1 + mul₆ ξ₂ ξ₆ x.c1 y.c0)

/-- **Karatsuba `Fp12_377` multiply** (3 `Fp6` muls): `v0 = a₀b₀`, `v1 = a₁b₁`,
    `mid = (a₀+a₁)(b₀+b₁)`; `c0 = v0 + mulByV v1`, `c1 = mid − v0 − v1`. One fewer
    `Fp6` multiply than schoolbook. -/
def mulKaratsuba (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp12_377) : Fp12_377 :=
  letI := Fp6_377.commRing ξ₂ ξ₆
  let v0 := mul₆ ξ₂ ξ₆ x.c0 y.c0
  let v1 := mul₆ ξ₂ ξ₆ x.c1 y.c1
  let mid := mul₆ ξ₂ ξ₆ (x.c0 + x.c1) (y.c0 + y.c1)
  Fp12_377.mk
    (v0 + Fp6_377.mulByV ξ₂ ξ₆ v1)
    (mid - v0 - v1)

/-! ## 11. **Fp12 Karatsuba = schoolbook** -/

/-- **The Karatsuba `Fp12_377` multiply equals the schoolbook multiply** for any
    base / cubic nonresidues `ξ₂, ξ₆`. The `c0` coordinates are syntactically
    equal; the `c1` coordinates agree by `ring` over the `Fp6_377` `CommRing`
    (`(a₀+a₁)(b₀+b₁) − a₀b₀ − a₁b₁ = a₀b₁ + a₁b₀`). -/
theorem mulKaratsuba_eq_schoolbook (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp12_377) :
    mulKaratsuba ξ₂ ξ₆ x y = mulSchoolbook ξ₂ ξ₆ x y := by
  letI := Fp6_377.commRing ξ₂ ξ₆
  have hm : ∀ a b : Fp6_377, mul₆ ξ₂ ξ₆ a b = a * b := fun _ _ => rfl
  refine Fp12_377.ext ?_ ?_ <;> · simp only [mulKaratsuba, mulSchoolbook, hm] <;> ring

/-! ## 12. The `CommRing` structure on `Fp12_377` (schoolbook mul) -/

/-- **`Fp12_377` is a commutative ring** (`Fp6_377[w]/(w² − v)`) for any base /
    cubic nonresidues `ξ₂, ξ₆`. Every axiom reduces to a componentwise
    `Fp6_377`-identity after the `w² = v` reduction; `ext` then `ring` over the
    `Fp6_377` `CommRing` closes each. -/
@[reducible] def commRing (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) : CommRing Fp12_377 :=
  letI := Fp6_377.commRing ξ₂ ξ₆
  have hm : ∀ a b : Fp6_377, mul₆ ξ₂ ξ₆ a b = a * b := fun _ _ => rfl
  have hv : ∀ x : Fp6_377, Fp6_377.mulByV ξ₂ ξ₆ x = Fp6_377.vGen * x := fun x => by
    rw [Fp6_377.mulByV_eq_mul]; rfl
  { add := (· + ·)
    add_assoc := fun a b c => by refine Fp12_377.ext ?_ ?_ <;> · simp only [add_c0, add_c1] <;> ring
    zero := 0
    zero_add := fun a => by refine Fp12_377.ext ?_ ?_ <;> · simp only [add_c0, add_c1, zero_c0, zero_c1] <;> ring
    add_zero := fun a => by refine Fp12_377.ext ?_ ?_ <;> · simp only [add_c0, add_c1, zero_c0, zero_c1] <;> ring
    nsmul := nsmulRec
    add_comm := fun a b => by refine Fp12_377.ext ?_ ?_ <;> · simp only [add_c0, add_c1] <;> ring
    mul := mulSchoolbook ξ₂ ξ₆
    left_distrib := fun a b c => by
      show mulSchoolbook ξ₂ ξ₆ a (b + c)
        = mulSchoolbook ξ₂ ξ₆ a b + mulSchoolbook ξ₂ ξ₆ a c
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv, add_c0, add_c1] <;> generalize Fp6_377.vGen = v <;> ring
    right_distrib := fun a b c => by
      show mulSchoolbook ξ₂ ξ₆ (a + b) c
        = mulSchoolbook ξ₂ ξ₆ a c + mulSchoolbook ξ₂ ξ₆ b c
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv, add_c0, add_c1] <;> generalize Fp6_377.vGen = v <;> ring
    zero_mul := fun a => by
      show mulSchoolbook ξ₂ ξ₆ 0 a = 0
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv, zero_c0, zero_c1] <;> generalize Fp6_377.vGen = v <;> ring
    mul_zero := fun a => by
      show mulSchoolbook ξ₂ ξ₆ a 0 = 0
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv, zero_c0, zero_c1] <;> generalize Fp6_377.vGen = v <;> ring
    mul_assoc := fun a b c => by
      show mulSchoolbook ξ₂ ξ₆ (mulSchoolbook ξ₂ ξ₆ a b) c
        = mulSchoolbook ξ₂ ξ₆ a (mulSchoolbook ξ₂ ξ₆ b c)
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv] <;> generalize Fp6_377.vGen = v <;> ring
    one := 1
    one_mul := fun a => by
      show mulSchoolbook ξ₂ ξ₆ 1 a = a
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv, one_c0, one_c1] <;> generalize Fp6_377.vGen = v <;> ring
    mul_one := fun a => by
      show mulSchoolbook ξ₂ ξ₆ a 1 = a
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv, one_c0, one_c1] <;> generalize Fp6_377.vGen = v <;> ring
    neg := Neg.neg
    zsmul := zsmulRec
    sub_eq_add_neg := fun a b => by refine Fp12_377.ext ?_ ?_ <;> · simp only [sub_c0, sub_c1, add_c0, add_c1, neg_c0, neg_c1] <;> ring
    neg_add_cancel := fun a => by refine Fp12_377.ext ?_ ?_ <;> · simp only [add_c0, add_c1, neg_c0, neg_c1, zero_c0, zero_c1] <;> ring
    mul_comm := fun a b => by
      show mulSchoolbook ξ₂ ξ₆ a b = mulSchoolbook ξ₂ ξ₆ b a
      refine Fp12_377.ext ?_ ?_ <;>
        · simp only [mulSchoolbook, hm, hv] <;> generalize Fp6_377.vGen = v <;> ring }

/-! ## 13. A worked example: Fp12 Karatsuba = schoolbook on concrete small inputs -/

/-- A concrete `Fp12_377` element `Fp6_377.example_x + Fp6_377.example_y · w`. -/
def example_x : Fp12_377 := ⟨Fp6_377.example_x, Fp6_377.example_y⟩
/-- A concrete `Fp12_377` element `Fp6_377.example_y + Fp6_377.example_x · w`. -/
def example_y : Fp12_377 := ⟨Fp6_377.example_y, Fp6_377.example_x⟩

/-- **Worked example — Fp12.** On the concrete operands with base nonresidue
    `ξ₂ = 5` and cubic nonresidue `ξ₆ = 2 + 3u`, the Karatsuba multiply agrees
    with the schoolbook multiply — an instance of `mulKaratsuba_eq_schoolbook`. -/
theorem example_karatsuba_eq_schoolbook :
    mulKaratsuba 5 ⟨2, 3⟩ example_x example_y
      = mulSchoolbook 5 ⟨2, 3⟩ example_x example_y :=
  mulKaratsuba_eq_schoolbook 5 ⟨2, 3⟩ example_x example_y

end Fp12_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
