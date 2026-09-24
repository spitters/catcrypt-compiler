/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# The generic quadratic field extension `K[u]/(u² − ξ)`, with KARATSUBA mul

This module is the **generic core** of the quadratic-extension construction that
the relational-front `Fp2`/`Fp12` towers all instantiate. Over an *abstract*
commutative base ring `K` with a nonresidue parameter `ξ : K` (`u² = ξ`), it
builds `QuadExt K = K × K` written `c0 + c1·u`, proves the
**Karatsuba-equals-schoolbook** correctness (3 base muls = 4), and gives a
`CommRing (QuadExt K)` instance.

`RelationalFrontBls377Fp2.lean`'s `Fp2_377` is the special case `K = ZMod
bls377Q`; this module abstracts the base ring away. The two
quadratic-on-quadratic instantiations are functor applications of this one
construction:

* `Fp2_377  = QuadExt (ZMod bls377Q)`   — base field over the 377-bit prime,
* `Fp12_377 = QuadExt Fp6_377`          — `Fp12 = Fp6[w]/(w² − v)`, the degree-2
                                          step at the top of the `2·3·2`
                                          `bls12_377` pairing tower.

Both are quadratic extensions `B[u]/(u² − ξ)`; the only difference is the base
ring `B` (a prime field vs. a degree-6 extension). Factoring the construction
through `QuadExt` means the Karatsuba optimization and the ring axioms are
proved **once**, generically, instead of per-tower-level.

## What this module proves

The headline is the **Karatsuba-equals-schoolbook** correctness:

```
   (a + bu)(c + du) = (ac + bd·ξ) + (ad + bc)·u        -- schoolbook, 4 base muls
                    = (v0 + v1·ξ) + (mid − v0 − v1)·u  -- Karatsuba,  3 base muls
```

where `v0 = ac`, `v1 = bd`, `mid = (a+b)(c+d)`. Trading the fourth base multiply
for an extra add (`ad + bc = (a+b)(c+d) − ac − bd`) is **semantics-preserving**
(`mulKaratsuba_eq_schoolbook`) — `ext` then `ring` on each component. Because the
base `K` is an abstract `CommRing`, `ring` closes the component identities
**directly**: there is no opaque-multiply dance (no `simp`-then-`ring` on an
uninterpreted `mul`), unlike a `ZMod`-specialized phrasing where the base
operations are concrete.

The nonresidue `ξ` is kept a **parameter** (`u² = ξ`); the Karatsuba identity and
all ring axioms hold for *any* `ξ : K`, so we do not pin its value.

We also give `QuadExt K` a `CommRing` instance (schoolbook mul, componentwise
add/sub/neg): every axiom is a componentwise `K`-identity closed by `ext`/`ring`.

## Scope

This is the abstract algebra only — the construction `K[u]/(u² − ξ)` and the
Karatsuba optimization's correctness. It does **not** wire the multiply down to
any emitted base kernel; that lift is per-instantiation
(`RelationalFrontBls377Fp2`-style) and deliberately out of scope here, to keep
the generic core focused and sorry-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.QuadExtGeneric

variable {K : Type*}

/-! ## 1. The quadratic extension `QuadExt K = K[u]/(u² − ξ)`

`QuadExt K` is `K × K` written `c0 + c1·u`, with `u² = ξ` for a nonresidue
parameter `ξ`. The field layout (`c0`, `c1`) matches the tower-level `Fp2`/`Fp12`
shape (`{ c0, c1 }`). -/

/-- An element of the quadratic extension `QuadExt K = K[u]/(u² − ξ)`:
    `c0 + c1·u`, with `c0, c1 : K`. -/
@[ext]
structure QuadExt (K : Type*) where
  /-- The `1`-component `c0` of `c0 + c1·u`. -/
  c0 : K
  /-- The `u`-component `c1` of `c0 + c1·u`. -/
  c1 : K

namespace QuadExt

/-! ## 2. Componentwise zero / one / add / neg / sub (the ξ-independent operations)

These do not depend on the nonresidue `ξ`, so we register them as instances over
any base ring `K` with the relevant operation. Only multiplication carries `ξ`,
so it stays a parameterized definition (§3). -/

/-- Zero of `QuadExt K` (`0 + 0·u`). -/
instance [Zero K] : Zero (QuadExt K) := ⟨⟨0, 0⟩⟩
/-- One of `QuadExt K` (`1 + 0·u`). -/
instance [Zero K] [One K] : One (QuadExt K) := ⟨⟨1, 0⟩⟩
/-- Componentwise `QuadExt K` addition. -/
instance [Add K] : Add (QuadExt K) := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
/-- Componentwise `QuadExt K` negation. -/
instance [Neg K] : Neg (QuadExt K) := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
/-- Componentwise `QuadExt K` subtraction. -/
instance [Sub K] : Sub (QuadExt K) := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩

@[simp] theorem zero_c0 [Zero K] : (0 : QuadExt K).c0 = 0 := rfl
@[simp] theorem zero_c1 [Zero K] : (0 : QuadExt K).c1 = 0 := rfl
@[simp] theorem one_c0 [Zero K] [One K] : (1 : QuadExt K).c0 = 1 := rfl
@[simp] theorem one_c1 [Zero K] [One K] : (1 : QuadExt K).c1 = 0 := rfl
@[simp] theorem add_c0 [Add K] (x y : QuadExt K) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 [Add K] (x y : QuadExt K) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem neg_c0 [Neg K] (x : QuadExt K) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 [Neg K] (x : QuadExt K) : (-x).c1 = -x.c1 := rfl
@[simp] theorem sub_c0 [Sub K] (x y : QuadExt K) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 [Sub K] (x y : QuadExt K) : (x - y).c1 = x.c1 - y.c1 := rfl

/-! ## 3. The two multiplications: schoolbook (4 muls) and Karatsuba (3 muls)

The `u² = ξ` reduction gives `(a+bu)(c+du) = (ac + bd·ξ) + (ad+bc)·u`. The
schoolbook form does the four base products `ac, bd, ad, bc` directly; the
Karatsuba form does three (`ac`, `bd`, `(a+b)(c+d)`) and recovers `ad + bc` as
`(a+b)(c+d) − ac − bd`. Both are over the abstract base ring `K`. -/

/-- **Schoolbook `QuadExt K` multiply** (4 base muls): with `u² = ξ`,
    `(a+bu)(c+du) = (ac + bd·ξ) + (ad+bc)·u`. -/
def mulSchoolbook [Mul K] [Add K] (ξ : K) (x y : QuadExt K) : QuadExt K :=
  ⟨x.c0 * y.c0 + ξ * (x.c1 * y.c1), x.c0 * y.c1 + x.c1 * y.c0⟩

/-- **Karatsuba `QuadExt K` multiply** (3 base muls): `v0 = ac`, `v1 = bd`,
    `mid = (a+b)(c+d)`; then `real = v0 + ξ·v1`, `imag = mid − v0 − v1`
    (`= ad + bc`). One fewer base multiply than `mulSchoolbook`. -/
def mulKaratsuba [Mul K] [Add K] [Sub K] (ξ : K) (x y : QuadExt K) : QuadExt K :=
  QuadExt.mk
    (x.c0 * y.c0 + ξ * (x.c1 * y.c1))
    ((x.c0 + x.c1) * (y.c0 + y.c1) - x.c0 * y.c0 - x.c1 * y.c1)

@[simp] theorem mulSchoolbook_c0 [Mul K] [Add K] (ξ : K) (x y : QuadExt K) :
    (mulSchoolbook ξ x y).c0 = x.c0 * y.c0 + ξ * (x.c1 * y.c1) := rfl
@[simp] theorem mulSchoolbook_c1 [Mul K] [Add K] (ξ : K) (x y : QuadExt K) :
    (mulSchoolbook ξ x y).c1 = x.c0 * y.c1 + x.c1 * y.c0 := rfl
@[simp] theorem mulKaratsuba_c0 [Mul K] [Add K] [Sub K] (ξ : K) (x y : QuadExt K) :
    (mulKaratsuba ξ x y).c0 = x.c0 * y.c0 + ξ * (x.c1 * y.c1) := rfl
@[simp] theorem mulKaratsuba_c1 [Mul K] [Add K] [Sub K] (ξ : K) (x y : QuadExt K) :
    (mulKaratsuba ξ x y).c1
      = (x.c0 + x.c1) * (y.c0 + y.c1) - x.c0 * y.c0 - x.c1 * y.c1 := rfl

/-! ## 4. **Karatsuba = schoolbook** — the semantics-preserving optimization

Because `K` is an abstract `CommRing`, `ring` closes both component identities
directly. -/

/-- **The Karatsuba `QuadExt K` multiply equals the schoolbook multiply.** Trading
    the fourth base product `ad + bc` for `(a+b)(c+d) − ac − bd` is
    denotation-preserving for any nonresidue `ξ` over any `CommRing K`. The `c0`
    components are syntactically equal; the `c1` components agree by `ring`
    (`(a+b)(c+d) − ac − bd = ad + bc`). This is the correctness fact
    for emitting a 3-mul quadratic-extension multiply. -/
theorem mulKaratsuba_eq_schoolbook [CommRing K] (ξ : K) (x y : QuadExt K) :
    mulKaratsuba ξ x y = mulSchoolbook ξ x y := by
  ext
  · simp
  · simp; ring

/-! ## 5. The `CommRing` structure on `QuadExt K` (schoolbook mul)

`QuadExt K` is a commutative ring: componentwise add/sub/neg and the schoolbook
mul with the `u² = ξ` reduction. Every axiom is a componentwise `K`-identity,
closed by `ext` then `ring`. We bundle it parameterically in `ξ`. -/

/-- **`QuadExt K` is a commutative ring** (`K[u]/(u² − ξ)`) for any nonresidue
    parameter `ξ` over any `CommRing K`. Every axiom reduces to the componentwise
    `K`-identity after the `u² = ξ` reduction; `ext` then `ring` on each component
    closes them. -/
@[reducible] def commRing [CommRing K] (ξ : K) : CommRing (QuadExt K) where
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
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]; ring
  right_distrib a b c := by
    show mulSchoolbook ξ (a + b) c = mulSchoolbook ξ a c + mulSchoolbook ξ b c
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]; ring
  zero_mul a := by
    show mulSchoolbook ξ 0 a = 0
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]
  mul_zero a := by
    show mulSchoolbook ξ a 0 = 0
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]
  mul_assoc a b c := by
    show mulSchoolbook ξ (mulSchoolbook ξ a b) c = mulSchoolbook ξ a (mulSchoolbook ξ b c)
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]; ring
  one := 1
  one_mul a := by
    show mulSchoolbook ξ 1 a = a
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]
  mul_one a := by
    show mulSchoolbook ξ a 1 = a
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]
  neg := Neg.neg
  zsmul := zsmulRec
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_comm a b := by
    show mulSchoolbook ξ a b = mulSchoolbook ξ b a
    refine QuadExt.ext ?_ ?_ <;> · simp [mulSchoolbook]; ring

/-- **Schoolbook `QuadExt K` multiply is commutative** (extracted directly,
    without going through the `CommRing` bundle). -/
theorem mulSchoolbook_comm [CommRing K] (ξ : K) (x y : QuadExt K) :
    mulSchoolbook ξ x y = mulSchoolbook ξ y x := by
  ext <;> simp <;> ring

/-- **Karatsuba `QuadExt K` multiply is commutative** — immediate from
    `mulKaratsuba_eq_schoolbook` and `mulSchoolbook_comm`. -/
theorem mulKaratsuba_comm [CommRing K] (ξ : K) (x y : QuadExt K) :
    mulKaratsuba ξ x y = mulKaratsuba ξ y x := by
  rw [mulKaratsuba_eq_schoolbook, mulKaratsuba_eq_schoolbook, mulSchoolbook_comm]

/-! ## 6. A worked example over `ℤ`

`QuadExt ℤ` is the Gaussian-integer-shaped quadratic extension `ℤ[u]/(u² − ξ)`.
We exercise the Karatsuba-equals-schoolbook identity on concrete operands with a
nonzero nonresidue `ξ`. (The equality holds for *any* `ξ` over *any* `CommRing`;
we pick `K = ℤ`, `ξ = 5` to make the worked example concrete and computable.) -/

/-- A concrete `QuadExt ℤ` element `2 + 3·u`. -/
def example_x : QuadExt ℤ := ⟨2, 3⟩
/-- A concrete `QuadExt ℤ` element `7 + 11·u`. -/
def example_y : QuadExt ℤ := ⟨7, 11⟩

/-- **Worked example.** On the concrete operands `2 + 3·u` and `7 + 11·u` over `ℤ`
    with the concrete nonresidue `ξ = 5`, the Karatsuba multiply agrees with the
    schoolbook multiply — an instance of `mulKaratsuba_eq_schoolbook`. -/
theorem example_karatsuba_eq_schoolbook :
    mulKaratsuba (5 : ℤ) example_x example_y = mulSchoolbook (5 : ℤ) example_x example_y :=
  mulKaratsuba_eq_schoolbook 5 example_x example_y

/-- **Worked example, evaluated.** The schoolbook product of `2 + 3·u` and
    `7 + 11·u` over `ℤ` with `ξ = 5` is
    `(2·7 + 5·(3·11)) + (2·11 + 3·7)·u = 179 + 43·u`. -/
theorem example_mulSchoolbook_value :
    mulSchoolbook (5 : ℤ) example_x example_y = ⟨179, 43⟩ := by
  ext <;> simp [example_x, example_y]

end QuadExt

end CatCrypt.Crypto.SecureCompilation.QuadExtGeneric
