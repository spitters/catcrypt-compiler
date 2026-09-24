/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# The generic cubic field extension `K[v]/(v³ − ξ)`, with TOOM-3/KARATSUBA mul

This module is the **generic core** of the cubic-extension construction that the
relational-front `Fp6` tower instantiates. Over an *abstract* commutative base
ring `K` with a nonresidue parameter `ξ : K` (`v³ = ξ`), it builds
`CubExt K = K × K × K` written `c0 + c1·v + c2·v²`, proves the
**Toom-3/Karatsuba-equals-schoolbook** correctness (6 base muls = 9), and gives a
`CommRing (CubExt K)` instance.

It is the cubic sibling of `QuadExtGeneric.lean`'s `QuadExt K = K[u]/(u² − ξ)`:
where the quadratic layer trades 4 base muls for 3, the cubic layer trades 9 for
6 via the three Toom-3 cross terms.

`RelationalFrontBls377Fp6.lean`'s `Fp6_377 = CubExt Fp2_377` is the special case
`K = Fp2_377` (the relational `bls12_377` degree-2 base field); this module
abstracts the base ring away. Factoring the construction through `CubExt` means
the Toom-3 optimization and the cubic ring axioms are proved **once**,
generically, instead of per-tower-level.

## What this module proves

The headline is the **Toom-3-equals-schoolbook** correctness. With `v³ = ξ` the
product of `a = a₀ + a₁v + a₂v²` and `b = b₀ + b₁v + b₂v²` is

```
   c0 = a₀b₀ + ξ(a₁b₂ + a₂b₁)
   c1 = a₀b₁ + a₁b₀ + ξ·a₂b₂
   c2 = a₀b₂ + a₁b₁ + a₂b₀
```

the schoolbook form computing the nine base products directly. The Toom-3 form
computes the three diagonal products `v0 = a₀b₀, v1 = a₁b₁, v2 = a₂b₂` and the
three off-diagonal sums via the cross-term trick
`(aᵢ+aⱼ)(bᵢ+bⱼ) − aᵢbᵢ − aⱼbⱼ`:

```
   c12 = (a₁+a₂)(b₁+b₂) − v1 − v2   (= a₁b₂ + a₂b₁)
   c01 = (a₀+a₁)(b₀+b₁) − v0 − v1   (= a₀b₁ + a₁b₀)
   c02 = (a₀+a₂)(b₀+b₂) − v0 − v2   (= a₀b₂ + a₂b₀)
```

then `c0 = v0 + ξ·c12`, `c1 = c01 + ξ·v2`, `c2 = c02 + v1` — six base multiplies
(three diagonal + three cross) instead of nine. Trading the off-diagonal base
products for the cross-term recoveries is **semantics-preserving**
(`mulKaratsuba_eq_schoolbook`) — `ext` then `ring` on each component. Because the
base `K` is an abstract `CommRing`, `ring` closes the component identities
**directly**: there is no opaque-multiply dance (no `simp`-then-`ring` on an
uninterpreted `mul`), unlike a `Fp2`-specialized phrasing where the base
operations are a concrete schoolbook product.

The nonresidue `ξ` is kept a **parameter** (`v³ = ξ`); the Toom-3 identity and all
ring axioms hold for *any* `ξ : K`, so we do not pin its value.

We also give `CubExt K` a `CommRing` instance (schoolbook mul, componentwise
add/sub/neg): every axiom is a componentwise `K`-identity closed by `ext`/`ring`.

## Honesty boundary

This is the abstract algebra only — the construction `K[v]/(v³ − ξ)` and the
Toom-3 optimization's correctness. It does **not** wire the multiply down to any
emitted base kernel; that lift is per-instantiation
(`RelationalFrontBls377Fp6`-style) and deliberately out of scope here, to keep
the generic core focused and sorry-free. It also does not prove `CubExt K` is a
*field* (that needs `ξ` non-residuosity, a number-theoretic fact about the
concrete base).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CubExtGeneric

variable {K : Type*}

/-! ## 1. The cubic extension `CubExt K = K[v]/(v³ − ξ)`

`CubExt K` is `K × K × K` written `c0 + c1·v + c2·v²`, with `v³ = ξ` for a
nonresidue parameter `ξ`. The field layout (`c0`, `c1`, `c2`) matches the
tower-level `Fp6` shape (`{ c0, c1, c2 }`). -/

/-- An element of the cubic extension `CubExt K = K[v]/(v³ − ξ)`:
    `c0 + c1·v + c2·v²`, with `c0, c1, c2 : K`. -/
@[ext]
structure CubExt (K : Type*) where
  /-- The `1`-component `c0` of `c0 + c1·v + c2·v²`. -/
  c0 : K
  /-- The `v`-component `c1`. -/
  c1 : K
  /-- The `v²`-component `c2`. -/
  c2 : K

namespace CubExt

/-! ## 2. Componentwise zero / one / add / neg / sub (the ξ-independent operations)

These do not depend on the nonresidue `ξ`, so we register them as instances over
any base ring `K` with the relevant operation. Only multiplication carries `ξ`,
so it stays a parameterized definition (§3). -/

/-- Zero of `CubExt K` (`0 + 0·v + 0·v²`). -/
instance [Zero K] : Zero (CubExt K) := ⟨⟨0, 0, 0⟩⟩
/-- One of `CubExt K` (`1 + 0·v + 0·v²`). -/
instance [Zero K] [One K] : One (CubExt K) := ⟨⟨1, 0, 0⟩⟩
/-- Componentwise `CubExt K` addition. -/
instance [Add K] : Add (CubExt K) :=
  ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
/-- Componentwise `CubExt K` negation. -/
instance [Neg K] : Neg (CubExt K) := ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩
/-- Componentwise `CubExt K` subtraction. -/
instance [Sub K] : Sub (CubExt K) :=
  ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2⟩⟩

@[simp] theorem zero_c0 [Zero K] : (0 : CubExt K).c0 = 0 := rfl
@[simp] theorem zero_c1 [Zero K] : (0 : CubExt K).c1 = 0 := rfl
@[simp] theorem zero_c2 [Zero K] : (0 : CubExt K).c2 = 0 := rfl
@[simp] theorem one_c0 [Zero K] [One K] : (1 : CubExt K).c0 = 1 := rfl
@[simp] theorem one_c1 [Zero K] [One K] : (1 : CubExt K).c1 = 0 := rfl
@[simp] theorem one_c2 [Zero K] [One K] : (1 : CubExt K).c2 = 0 := rfl
@[simp] theorem add_c0 [Add K] (x y : CubExt K) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 [Add K] (x y : CubExt K) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem add_c2 [Add K] (x y : CubExt K) : (x + y).c2 = x.c2 + y.c2 := rfl
@[simp] theorem neg_c0 [Neg K] (x : CubExt K) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 [Neg K] (x : CubExt K) : (-x).c1 = -x.c1 := rfl
@[simp] theorem neg_c2 [Neg K] (x : CubExt K) : (-x).c2 = -x.c2 := rfl
@[simp] theorem sub_c0 [Sub K] (x y : CubExt K) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 [Sub K] (x y : CubExt K) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem sub_c2 [Sub K] (x y : CubExt K) : (x - y).c2 = x.c2 - y.c2 := rfl

/-! ## 3. The two multiplications: schoolbook (9 muls) and Toom-3/Karatsuba (6 muls)

The `v³ = ξ` reduction gives the schoolbook coordinates below; the Toom-3 form
computes three diagonal products and three cross terms. Both are over the
abstract base ring `K`. -/

/-- **Schoolbook `CubExt K` multiply** (9 base muls): with `v³ = ξ`, the full
    `(a₀+a₁v+a₂v²)(b₀+b₁v+b₂v²)` expansion reduced by `v³ = ξ`:

    `c0 = a₀b₀ + ξ(a₁b₂ + a₂b₁)`
    `c1 = a₀b₁ + a₁b₀ + ξ·a₂b₂`
    `c2 = a₀b₂ + a₁b₁ + a₂b₀`. -/
def mulSchoolbook [Mul K] [Add K] (ξ : K) (x y : CubExt K) : CubExt K :=
  CubExt.mk
    (x.c0 * y.c0 + ξ * (x.c1 * y.c2 + x.c2 * y.c1))
    (x.c0 * y.c1 + x.c1 * y.c0 + ξ * (x.c2 * y.c2))
    (x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0)

/-- **Toom-3 / Karatsuba `CubExt K` multiply** (6 base muls): the three diagonal
    products `v0 = a₀b₀`, `v1 = a₁b₁`, `v2 = a₂b₂`, and three cross terms recovered
    by `(aᵢ+aⱼ)(bᵢ+bⱼ) − aᵢbᵢ − aⱼbⱼ`:

    `c12 = (a₁+a₂)(b₁+b₂) − v1 − v2  (= a₁b₂ + a₂b₁)`
    `c01 = (a₀+a₁)(b₀+b₁) − v0 − v1  (= a₀b₁ + a₁b₀)`
    `c02 = (a₀+a₂)(b₀+b₂) − v0 − v2  (= a₀b₂ + a₂b₀)`

    then `c0 = v0 + ξ·c12`, `c1 = c01 + ξ·v2`, `c2 = c02 + v1`. Six base muls
    (three diagonal + three cross) instead of schoolbook's nine. -/
def mulKaratsuba [Mul K] [Add K] [Sub K] (ξ : K) (x y : CubExt K) : CubExt K :=
  let v0 := x.c0 * y.c0
  let v1 := x.c1 * y.c1
  let v2 := x.c2 * y.c2
  let c12 := (x.c1 + x.c2) * (y.c1 + y.c2) - v1 - v2
  let c01 := (x.c0 + x.c1) * (y.c0 + y.c1) - v0 - v1
  let c02 := (x.c0 + x.c2) * (y.c0 + y.c2) - v0 - v2
  CubExt.mk
    (v0 + ξ * c12)
    (c01 + ξ * v2)
    (c02 + v1)

@[simp] theorem mulSchoolbook_c0 [Mul K] [Add K] (ξ : K) (x y : CubExt K) :
    (mulSchoolbook ξ x y).c0 = x.c0 * y.c0 + ξ * (x.c1 * y.c2 + x.c2 * y.c1) := rfl
@[simp] theorem mulSchoolbook_c1 [Mul K] [Add K] (ξ : K) (x y : CubExt K) :
    (mulSchoolbook ξ x y).c1 = x.c0 * y.c1 + x.c1 * y.c0 + ξ * (x.c2 * y.c2) := rfl
@[simp] theorem mulSchoolbook_c2 [Mul K] [Add K] (ξ : K) (x y : CubExt K) :
    (mulSchoolbook ξ x y).c2 = x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 := rfl

/-! ## 4. **Toom-3 = schoolbook** — the semantics-preserving optimization

Because `K` is an abstract `CommRing`, `ring` closes all three component
identities directly. -/

/-- **The Toom-3/Karatsuba `CubExt K` multiply equals the schoolbook multiply.**
    Trading the off-diagonal base products `a₁b₂+a₂b₁`, `a₀b₁+a₁b₀`, `a₀b₂+a₂b₀`
    for the cross-term recoveries `(aᵢ+aⱼ)(bᵢ+bⱼ) − aᵢbᵢ − aⱼbⱼ` is
    denotation-preserving for any nonresidue `ξ` over any `CommRing K`: each output
    coordinate agrees by `ring`. This is the key correctness fact for
    emitting a 6-mul cubic-extension multiply. -/
theorem mulKaratsuba_eq_schoolbook [CommRing K] (ξ : K) (x y : CubExt K) :
    mulKaratsuba ξ x y = mulSchoolbook ξ x y := by
  ext <;> · simp only [mulKaratsuba, mulSchoolbook]; ring

/-! ## 5. The `CommRing` structure on `CubExt K` (schoolbook mul)

`CubExt K` is a commutative ring: componentwise add/sub/neg and the schoolbook
cubic mul with the `v³ = ξ` reduction. Every axiom is a componentwise
`K`-identity, closed by `ext` then `ring`. We bundle it parameterically in `ξ`. -/

/-- **`CubExt K` is a commutative ring** (`K[v]/(v³ − ξ)`) for any nonresidue
    parameter `ξ` over any `CommRing K`. Every axiom reduces to the componentwise
    `K`-identity after the `v³ = ξ` reduction; `ext` then `ring` on each component
    closes them. -/
@[reducible] def commRing [CommRing K] (ξ : K) : CommRing (CubExt K) where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp <;> ring
  zero := 0
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp <;> ring
  mul := mulSchoolbook ξ
  left_distrib a b c := by
    show mulSchoolbook ξ a (b + c) = mulSchoolbook ξ a b + mulSchoolbook ξ a c
    ext <;> · simp [mulSchoolbook]; ring
  right_distrib a b c := by
    show mulSchoolbook ξ (a + b) c = mulSchoolbook ξ a c + mulSchoolbook ξ b c
    ext <;> · simp [mulSchoolbook]; ring
  zero_mul a := by
    show mulSchoolbook ξ 0 a = 0
    ext <;> · simp [mulSchoolbook]
  mul_zero a := by
    show mulSchoolbook ξ a 0 = 0
    ext <;> · simp [mulSchoolbook]
  mul_assoc a b c := by
    show mulSchoolbook ξ (mulSchoolbook ξ a b) c
      = mulSchoolbook ξ a (mulSchoolbook ξ b c)
    ext <;> · simp [mulSchoolbook]; ring
  one := 1
  one_mul a := by
    show mulSchoolbook ξ 1 a = a
    ext <;> · simp [mulSchoolbook]
  mul_one a := by
    show mulSchoolbook ξ a 1 = a
    ext <;> · simp [mulSchoolbook]
  neg := Neg.neg
  zsmul := zsmulRec
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_comm a b := by
    show mulSchoolbook ξ a b = mulSchoolbook ξ b a
    ext <;> · simp [mulSchoolbook]; ring

/-- **Schoolbook `CubExt K` multiply is commutative** (extracted directly,
    without going through the `CommRing` bundle). -/
theorem mulSchoolbook_comm [CommRing K] (ξ : K) (x y : CubExt K) :
    mulSchoolbook ξ x y = mulSchoolbook ξ y x := by
  ext <;> · simp [mulSchoolbook]; ring

/-- **Toom-3/Karatsuba `CubExt K` multiply is commutative** — immediate from
    `mulKaratsuba_eq_schoolbook` and `mulSchoolbook_comm`. -/
theorem mulKaratsuba_comm [CommRing K] (ξ : K) (x y : CubExt K) :
    mulKaratsuba ξ x y = mulKaratsuba ξ y x := by
  rw [mulKaratsuba_eq_schoolbook, mulKaratsuba_eq_schoolbook, mulSchoolbook_comm]

/-! ## 6. A worked example over `ℤ`

`CubExt ℤ` is the cubic extension `ℤ[v]/(v³ − ξ)`. We exercise the
Toom-3-equals-schoolbook identity on concrete operands with a nonzero nonresidue
`ξ`. (The equality holds for *any* `ξ` over *any* `CommRing`; we pick `K = ℤ`,
`ξ = 5` to make the worked example concrete and computable.) -/

/-- A concrete `CubExt ℤ` element `2 + 3·v + 4·v²`. -/
def example_x : CubExt ℤ := ⟨2, 3, 4⟩
/-- A concrete `CubExt ℤ` element `7 + 11·v + 13·v²`. -/
def example_y : CubExt ℤ := ⟨7, 11, 13⟩

/-- **Worked example.** On the concrete operands `2 + 3·v + 4·v²` and
    `7 + 11·v + 13·v²` over `ℤ` with the concrete nonresidue `ξ = 5`, the Toom-3
    multiply agrees with the schoolbook multiply — an instance of
    `mulKaratsuba_eq_schoolbook`. -/
theorem example_karatsuba_eq_schoolbook :
    mulKaratsuba (5 : ℤ) example_x example_y
      = mulSchoolbook (5 : ℤ) example_x example_y :=
  mulKaratsuba_eq_schoolbook 5 example_x example_y

/-- **Worked example, evaluated.** The schoolbook product of `2 + 3·v + 4·v²` and
    `7 + 11·v + 13·v²` over `ℤ` with `ξ = 5` is

    `c0 = 2·7 + 5·(3·13 + 4·11) = 14 + 5·83 = 429`
    `c1 = 2·11 + 3·7 + 5·(4·13) = 43 + 260 = 303`
    `c2 = 2·13 + 3·11 + 4·7 = 26 + 33 + 28 = 87`. -/
theorem example_mulSchoolbook_value :
    mulSchoolbook (5 : ℤ) example_x example_y = ⟨429, 303, 87⟩ := by
  ext <;> simp [example_x, example_y]

end CubExt

end CatCrypt.Crypto.SecureCompilation.CubExtGeneric
