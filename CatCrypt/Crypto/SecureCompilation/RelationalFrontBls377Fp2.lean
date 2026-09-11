/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import Mathlib.Data.ZMod.Basic

/-!
# The `bls12_377` quadratic extension `Fp2 = Fp[u]/(u² − ξ)`, with KARATSUBA mul

`RelationalFrontBls377Add` closes the `bls12_377` base-field **ADD** relationally
over the 6×64-bit carrier (`bls377Q = ZMod`'s modulus, the 377-bit
Zexe/Aleo prime). The *next* gateway toward `bls12_377` pairings is the quadratic
extension field `Fp2` over that base field — `Fp[u]/(u² − ξ)` for a nonresidue
`ξ` (`u² = ξ`). This module builds that `Fp2`, mirroring `Pairing/Fp2Tower.lean`'s
`Fp2` shape (3 base muls via Karatsuba, componentwise add/sub), but over the
**relational `bls12_377` base carrier** `FpBLS377 = ZMod bls377Q`.

## What this module proves

The headline is the **Karatsuba-equals-schoolbook** correctness:

```
   (a + bu)(c + du) = (ac + bd·ξ) + (ad + bc)·u        -- schoolbook, 4 base muls
                    = (v0 + v1·ξ) + (mid − v0 − v1)·u  -- Karatsuba,  3 base muls
```

where `v0 = ac`, `v1 = bd`, `mid = (a+b)(c+d)`. The optimization that trades the
fourth base multiply for an extra add (`ad + bc = (a+b)(c+d) − ac − bd`) is
**semantics-preserving** (`mulKaratsuba_eq_schoolbook`) — `ext` then `ring` on
each component. This is the fact for emitting a 3-mul `Fp2` multiply
without changing the field's denotation.

We keep the nonresidue `ξ` a **parameter** (`u² = ξ`); the `bls12_377`
quadratic-twist nonresidue is a concrete base-field element, but the Karatsuba
identity holds for *any* `ξ`, so we do not pin its value here (mirroring
`Fp2Tower`'s generic-over-base-ring shape, here generic over the nonresidue).

We also give `Fp2_377` a `CommRing` structure (schoolbook mul, componentwise
add/sub/neg), so the extension field is a commutative ring — every axiom
is a componentwise `ZMod bls377Q`-identity closed by `ext`/`ring`. When `ξ` is a
non-square (stated as a hypothesis, **not** proved here — non-squareness of the
`bls12_377` twist nonresidue is a number-theoretic fact about the concrete `ξ`),
`Fp2_377 ξ` is a field; we expose the algebraic facts (`mul_comm`, distributivity)
that the schoolbook form satisfies.

## Honesty boundary

This is the abstract `Fp2` field over the relational `bls12_377` base carrier and
the Karatsuba optimization's correctness. It does **not** wire `Fp2` multiply down
to the emitted 6-limb base kernels (that is the `Fp2Tower`-style `BaseSubstrate`
lift, one further step, deliberately not attempted here to keep the pass focused
and sorry-free). The base-field ADD relational tie lives in
`RelationalFrontBls377Add`; this module is the field-algebra gateway above it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 0. The `bls12_377` base field as a `ZMod` carrier

`bls377Q` is the 377-bit `bls12_377` base-field prime (defined in
`RelationalFrontBls377Add`). We register its `NeZero` so `ZMod bls377Q` is a
residue ring, and abbreviate the base field. -/

/-- `bls377Q` is nonzero (the 377-bit prime is positive). -/
instance : NeZero bls377Q := ⟨by unfold bls377Q; norm_num⟩

/-- The `bls12_377` base field `FpBLS377 = ZMod bls377Q` (the relational carrier). -/
abbrev FpBLS377 : Type := ZMod bls377Q

/-! ## 1. The quadratic extension `Fp2_377 = FpBLS377[u]/(u² − ξ)`

`Fp2_377` is `FpBLS377 × FpBLS377` written `c0 + c1·u`, with `u² = ξ` for a
nonresidue parameter `ξ`. The field layout (`c0`, `c1`) matches the
`Fp2Tower` / AUCurves `Fp2 { c0, c1 }`. -/

/-- An element of the `bls12_377` quadratic extension `Fp2_377 = Fp[u]/(u² − ξ)`:
    `c0 + c1·u`, with `c0, c1 : FpBLS377`. -/
@[ext]
structure Fp2_377 where
  /-- The `1`-component `c0` of `c0 + c1·u`. -/
  c0 : FpBLS377
  /-- The `u`-component `c1` of `c0 + c1·u`. -/
  c1 : FpBLS377

namespace Fp2_377

/-! ## 2. Componentwise zero / one / add / neg / sub (the ξ-independent operations)

These do not depend on the nonresidue `ξ`, so we register them as global
instances (mirroring `Fp2Tower`'s `Zero`/`One`/`Add`/`Neg`/`Sub` instances).
Only multiplication carries `ξ`, so it stays a parameterized definition (§3). -/

/-- Zero of `Fp2_377` (`0 + 0·u`). -/
instance : Zero Fp2_377 := ⟨⟨0, 0⟩⟩
/-- One of `Fp2_377` (`1 + 0·u`). -/
instance : One Fp2_377 := ⟨⟨1, 0⟩⟩
/-- Componentwise `Fp2_377` addition. -/
instance : Add Fp2_377 := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
/-- Componentwise `Fp2_377` negation. -/
instance : Neg Fp2_377 := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
/-- Componentwise `Fp2_377` subtraction. -/
instance : Sub Fp2_377 := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩

@[simp] theorem zero_c0 : (0 : Fp2_377).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2_377).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2_377).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2_377).c1 = 0 := rfl
@[simp] theorem add_c0 (x y : Fp2_377) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : Fp2_377) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem neg_c0 (x : Fp2_377) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : Fp2_377) : (-x).c1 = -x.c1 := rfl
@[simp] theorem sub_c0 (x y : Fp2_377) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : Fp2_377) : (x - y).c1 = x.c1 - y.c1 := rfl

/-! ## 3. The two multiplications: schoolbook (4 muls) and Karatsuba (3 muls)

The `u² = ξ` reduction gives `(a+bu)(c+du) = (ac + bd·ξ) + (ad+bc)·u`. The
schoolbook form does the four base products `ac, bd, ad, bc` directly; the
Karatsuba form does three (`ac`, `bd`, `(a+b)(c+d)`) and recovers `ad + bc` as
`(a+b)(c+d) − ac − bd`. -/

/-- **Schoolbook `Fp2_377` multiply** (4 base muls): with `u² = ξ`,
    `(a+bu)(c+du) = (ac + bd·ξ) + (ad+bc)·u`. -/
def mulSchoolbook (ξ : FpBLS377) (x y : Fp2_377) : Fp2_377 :=
  ⟨x.c0 * y.c0 + x.c1 * y.c1 * ξ, x.c0 * y.c1 + x.c1 * y.c0⟩

/-- **Karatsuba `Fp2_377` multiply** (3 base muls): `v0 = ac`, `v1 = bd`,
    `mid = (a+b)(c+d)`; then `real = v0 + v1·ξ`, `imag = mid − v0 − v1`
    (`= ad + bc`). One fewer base multiply than `mulSchoolbook`. -/
def mulKaratsuba (ξ : FpBLS377) (x y : Fp2_377) : Fp2_377 :=
  Fp2_377.mk
    (x.c0 * y.c0 + (x.c1 * y.c1) * ξ)
    ((x.c0 + x.c1) * (y.c0 + y.c1) - x.c0 * y.c0 - x.c1 * y.c1)

@[simp] theorem mulSchoolbook_c0 (ξ : FpBLS377) (x y : Fp2_377) :
    (mulSchoolbook ξ x y).c0 = x.c0 * y.c0 + x.c1 * y.c1 * ξ := rfl
@[simp] theorem mulSchoolbook_c1 (ξ : FpBLS377) (x y : Fp2_377) :
    (mulSchoolbook ξ x y).c1 = x.c0 * y.c1 + x.c1 * y.c0 := rfl
@[simp] theorem mulKaratsuba_c0 (ξ : FpBLS377) (x y : Fp2_377) :
    (mulKaratsuba ξ x y).c0 = x.c0 * y.c0 + x.c1 * y.c1 * ξ := rfl
@[simp] theorem mulKaratsuba_c1 (ξ : FpBLS377) (x y : Fp2_377) :
    (mulKaratsuba ξ x y).c1
      = (x.c0 + x.c1) * (y.c0 + y.c1) - x.c0 * y.c0 - x.c1 * y.c1 := rfl

/-! ## 4. **Karatsuba = schoolbook** — the semantics-preserving optimization -/

/-- **The Karatsuba `Fp2_377` multiply equals the schoolbook multiply.** Trading
    the fourth base product `ad + bc` for `(a+b)(c+d) − ac − bd` is
    denotation-preserving for any nonresidue `ξ`. The `c0` components are
    syntactically equal; the `c1` components agree by `ring`
    (`(a+b)(c+d) − ac − bd = ad + bc`). This is the correctness fact
    for emitting a 3-mul `Fp2` multiply. -/
theorem mulKaratsuba_eq_schoolbook (ξ : FpBLS377) (x y : Fp2_377) :
    mulKaratsuba ξ x y = mulSchoolbook ξ x y := by
  ext <;>
    simp only [mulKaratsuba_c0, mulKaratsuba_c1, mulSchoolbook_c0, mulSchoolbook_c1] <;> ring

/-! ## 5. The `CommRing` structure on `Fp2_377` (schoolbook mul)

`Fp2_377 ξ` is a commutative ring: componentwise add/sub/neg and the schoolbook
mul with the `u² = ξ` reduction. Every axiom is a componentwise `ZMod bls377Q`
identity, closed by `ext` then `ring`. We bundle it parameterically in `ξ`. -/

/-- **`Fp2_377` is a commutative ring** (`FpBLS377[u]/(u² − ξ)`) for any
    nonresidue parameter `ξ`. Every axiom reduces to the componentwise
    `FpBLS377`-identity after the `u² = ξ` reduction; `ext` then `ring` on each
    component closes them. -/
@[reducible] def commRing (ξ : FpBLS377) : CommRing Fp2_377 where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp only [add_c0, add_c1] <;> ring
  zero := 0
  zero_add a := by ext <;> simp only [add_c0, add_c1, zero_c0, zero_c1] <;> ring
  add_zero a := by ext <;> simp only [add_c0, add_c1, zero_c0, zero_c1] <;> ring
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp only [add_c0, add_c1] <;> ring
  mul := mulSchoolbook ξ
  left_distrib a b c := by
    show mulSchoolbook ξ a (b + c) = mulSchoolbook ξ a b + mulSchoolbook ξ a c
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1, add_c0, add_c1]; ring
  right_distrib a b c := by
    show mulSchoolbook ξ (a + b) c = mulSchoolbook ξ a c + mulSchoolbook ξ b c
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1, add_c0, add_c1]; ring
  zero_mul a := by
    show mulSchoolbook ξ 0 a = 0
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1, zero_c0, zero_c1]; ring
  mul_zero a := by
    show mulSchoolbook ξ a 0 = 0
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1, zero_c0, zero_c1]; ring
  mul_assoc a b c := by
    show mulSchoolbook ξ (mulSchoolbook ξ a b) c = mulSchoolbook ξ a (mulSchoolbook ξ b c)
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1]; ring
  one := 1
  one_mul a := by
    show mulSchoolbook ξ 1 a = a
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1, one_c0, one_c1]; ring
  mul_one a := by
    show mulSchoolbook ξ a 1 = a
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1, one_c0, one_c1]; ring
  neg := Neg.neg
  zsmul := zsmulRec
  sub_eq_add_neg a b := by ext <;> simp only [sub_c0, sub_c1, add_c0, add_c1, neg_c0, neg_c1] <;> ring
  neg_add_cancel a := by ext <;> simp only [add_c0, add_c1, neg_c0, neg_c1, zero_c0, zero_c1] <;> ring
  mul_comm a b := by
    show mulSchoolbook ξ a b = mulSchoolbook ξ b a
    refine Fp2_377.ext ?_ ?_ <;> · simp only [mulSchoolbook_c0, mulSchoolbook_c1]; ring

/-- **Schoolbook `Fp2_377` multiply is commutative** (extracted directly, without
    going through the `CommRing` bundle). -/
theorem mulSchoolbook_comm (ξ : FpBLS377) (x y : Fp2_377) :
    mulSchoolbook ξ x y = mulSchoolbook ξ y x := by
  ext <;> simp only [mulSchoolbook_c0, mulSchoolbook_c1] <;> ring

/-- **Karatsuba `Fp2_377` multiply is commutative** — immediate from
    `mulKaratsuba_eq_schoolbook` and `mulSchoolbook_comm`. -/
theorem mulKaratsuba_comm (ξ : FpBLS377) (x y : Fp2_377) :
    mulKaratsuba ξ x y = mulKaratsuba ξ y x := by
  rw [mulKaratsuba_eq_schoolbook, mulKaratsuba_eq_schoolbook, mulSchoolbook_comm]

/-! ## 6. A worked example: Karatsuba = schoolbook on concrete small inputs

Concrete `Fp2_377` operands with small residues, exercising the
Karatsuba-equals-schoolbook identity on a nonzero nonresidue `ξ`. (The equality
holds for *any* `ξ`; we pick `ξ = 5` to make the worked example concrete.) -/

/-- A concrete `Fp2_377` element `2 + 3·u`. -/
def example_x : Fp2_377 := ⟨2, 3⟩
/-- A concrete `Fp2_377` element `7 + 11·u`. -/
def example_y : Fp2_377 := ⟨7, 11⟩

/-- **Worked example.** On the concrete operands `2 + 3·u` and `7 + 11·u` with the
    concrete nonresidue `ξ = 5`, the Karatsuba multiply agrees with the schoolbook
    multiply — an instance of `mulKaratsuba_eq_schoolbook`. -/
theorem example_karatsuba_eq_schoolbook :
    mulKaratsuba 5 example_x example_y = mulSchoolbook 5 example_x example_y :=
  mulKaratsuba_eq_schoolbook 5 example_x example_y

/-- **Worked example, evaluated.** The schoolbook product of `2 + 3·u` and
    `7 + 11·u` with `ξ = 5` is `(2·7 + 3·11·5) + (2·11 + 3·7)·u = 179 + 43·u`
    (over `ZMod bls377Q`, where these small residues do not wrap). -/
theorem example_mulSchoolbook_value :
    mulSchoolbook 5 example_x example_y = ⟨179, 43⟩ := by
  ext <;> simp only [mulSchoolbook_c0, mulSchoolbook_c1, example_x, example_y] <;> ring

end Fp2_377

end CatCrypt.Crypto.SecureCompilation.RelationalFront
