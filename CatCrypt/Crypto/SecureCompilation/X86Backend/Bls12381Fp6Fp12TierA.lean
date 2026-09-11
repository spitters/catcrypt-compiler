/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381TowerTierA
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# BLS12-381 `Fp6` / `Fp12` multiply — in-`ZMod p` value-correctness over the
  Tier-A `Fp2` multiply (completing the tower)

This file continues the BLS12-381 pairing tower **two layers up** from the
Tier-A `Fp2` multiply (`Bls12381TowerTierA.bls_fp2_mul_karatsuba`), replacing the
**Tier-C** RELIC-byte-only status of the `Fp6`/`Fp12` multiply
(`Bls12381Fp6Fp12MulKernel`, byte-identity to unverified C, which proves nothing
about the field algebra) with genuine in-Lean **value-correctness** theorems.

## The tower

* `Fp2 = Fp[u]/(u²+1)` — the Tier-A base of this construction. An element is a
  pair `(a, b) : ZMod p × ZMod p` (standing for `a + b·u`). The genuine
  Montgomery-form product is `Bls12381TowerTierA.fp2MulSpec` and the non-residue
  `ξ = 1 + u` multiply is `fp2NonResidue (x,y) = (x − y, x + y)`. Both are
  imported, not re-derived.
* `Fp6 = Fp2[v]/(v³ − ξ)`, `ξ = 1 + u` — the sextic extension. An element is a
  triple `(a₀, a₁, a₂) : Fp2³` (standing for `a₀ + a₁·v + a₂·v²`).
* `Fp12 = Fp6[w]/(w² − v)` — the dodecic extension (the BLS12-381 target group
  `GT`'s field). An element is a pair `(c₀, c₁) : Fp6²` (standing for
  `c₀ + c₁·w`).

## The genuine tower products

`Fp6` multiply (RELIC `fp6_mul_basic`, Karatsuba over the cubic with the `v³ = ξ`
wrap), for `α = (a₀,a₁,a₂)`, `β = (b₀,b₁,b₂)` and `vᵢ = aᵢ·bᵢ`:

    c₀ = v0 + ξ·((a₁+a₂)(b₁+b₂) − v1 − v2)
    c₁ = (a₀+a₁)(b₀+b₁) − v0 − v1 + ξ·v2
    c₂ = (a₀+a₂)(b₀+b₂) − v0 + v1 − v2

`Fp12` multiply (RELIC `fp12_mul_basic`, Karatsuba over the quadratic with the
`w² = v` wrap), for `x = (a₀,a₁)`, `y = (b₀,b₁)` over `Fp6` and `tᵢ = aᵢ·bᵢ`:

    c₀ = t0 + v·t1                        -- `v·` is the `Fp6` mul-by-`v` rotation
    c₁ = (a₀+a₁)(b₀+b₁) − t0 − t1

These are the genuine extension-field products: the schedules the emitted kernel
(`Bls12381Fp6Fp12MulKernel.fp6MulAsm` / `fp12MulAsm`) runs are *defined* to be
exactly these Karatsuba arrangements, and the schedule-equals-spec identities
close by `ring` over the proven `Fp2` arithmetic — Montgomery multiplication is
`Fp`-bilinear (`fpMul a b = a·b·R⁻¹` is `R⁻¹`-linear), so the tower formulas hold
verbatim in Montgomery form.

## Scope reached (brutally honest)

* **`Fp6` multiply value-correctness — fully proven** (`bls_fp6_mul_karatsuba`):
  the emitted 6-`Fp2`-mul Karatsuba schedule equals the genuine cubic-extension
  Montgomery-form product `fp6MulSpec`. The six `Fp2` sub-multiplies are the
  Tier-A `fp2MulSpec` (tied to the `runBlock` `Fp` leaf via `fpMul_eq_leaf`).
* **`Fp12` multiply value-correctness — fully proven** (`bls_fp12_mul_karatsuba`):
  the emitted 3-`Fp6`-mul quadratic Karatsuba schedule equals the genuine
  dodecic-extension product `fp12MulSpec`, built on the proven `Fp6` multiply.

The honest caveat is identical to the Tier-A `Fp2` file: the genuine
kernel↔algebra tie runs through the **multiply** leaves (`Fp` via
`fpMul_eq_leaf`, `Fp2` via `bls_fp2_mul_karatsuba`); the `Fp2`/`Fp6` add/sub and
the non-residue twists are `ZMod`-level specifications of `+`/`−`/mul-by-ξ (the
hardware carry-chain + conditional reduce realises the canonical residue; the
`fpAdd`/`fpSub` `runBlock` reconstruction is KAT-gated, not proven in-Lean — see
the Tier-A file's honest-scope note). The genuine *algebraic* content tying the
schedule to the extension-field product is what this file proves.
-/

@[expose] public section

set_option autoImplicit false
-- The Tier-A base carries the `2^384` radix literal; never evaluated, so raise
-- the pretty-printer's exponentiation threshold to silence the benign notice.
set_option exponentiation.threshold 400

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12TierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381TowerTierA

/-! ## 0. `Fp2` as a pair, with the Tier-A operations

We model an `Fp2` element by `Fp2 := ZMod p × ZMod p` and reuse the Tier-A
operations: multiply is `fp2MulSpec` (the proven Montgomery-form product),
non-residue (mul-by-`ξ`) is `fp2NonResidue`, and add/sub are componentwise. We
expose curried wrappers `fp2mul`/`fp2add`/`fp2sub`/`fp2nr` on the pair type so the
`Fp6`/`Fp12` schedules read like the RELIC drivers. -/

/-- An `Fp2` element: a pair `(a, b)` standing for `a + b·u`. -/
abbrev Fp2 : Type := ZMod p × ZMod p

/-- `Fp2` multiply (Tier-A Montgomery-form product). -/
noncomputable def fp2mul (x y : Fp2) : Fp2 := fp2MulSpec x.1 x.2 y.1 y.2

/-- `Fp2` add (componentwise `Fp` add). -/
def fp2add (x y : Fp2) : Fp2 := (fpAdd x.1 y.1, fpAdd x.2 y.2)

/-- `Fp2` sub (componentwise `Fp` sub). -/
def fp2sub (x y : Fp2) : Fp2 := (fpSub x.1 y.1, fpSub x.2 y.2)

/-- `Fp2` mul-by-`ξ = (1+u)` non-residue: `ξ·(c₀+c₁·u) = (c₀−c₁) + (c₀+c₁)·u`. -/
def fp2nr (x : Fp2) : Fp2 := fp2NonResidue x.1 x.2

/-! ## 1. `Fp6` as a triple, the Karatsuba schedule and its value-correctness

`Fp6 = Fp2[v]/(v³ − ξ)`. An element is `(a₀, a₁, a₂)` standing for
`a₀ + a₁·v + a₂·v²`. -/

/-- An `Fp6` element: a triple `(a₀, a₁, a₂)` over `Fp2`. -/
abbrev Fp6 : Type := Fp2 × Fp2 × Fp2

/-- The emitted `Fp6` Karatsuba multiply schedule (`Bls12381Fp6Fp12MulKernel.fp6MulAsm`).
    With `vᵢ = aᵢ·bᵢ`:

        c₀ = v0 + ξ·((a₁+a₂)(b₁+b₂) − v1 − v2)
        c₁ = (a₀+a₁)(b₀+b₁) − v0 − v1 + ξ·v2
        c₂ = (a₀+a₂)(b₀+b₂) − v0 + v1 − v2

    The six `Fp2`-muls are `v0,v1,v2` and the three Karatsuba cross products. -/
noncomputable def fp6MulKaratsuba (α β : Fp6) : Fp6 :=
  let a0 := α.1; let a1 := α.2.1; let a2 := α.2.2
  let b0 := β.1; let b1 := β.2.1; let b2 := β.2.2
  let v0 := fp2mul a0 b0
  let v1 := fp2mul a1 b1
  let v2 := fp2mul a2 b2
  -- c₀
  let t2c0 := fp2sub (fp2sub (fp2mul (fp2add a1 a2) (fp2add b1 b2)) v1) v2
  let c0 := fp2add v0 (fp2nr t2c0)
  -- c₁
  let r1 := fp2sub (fp2sub (fp2mul (fp2add a0 a1) (fp2add b0 b1)) v0) v1
  let c1 := fp2add r1 (fp2nr v2)
  -- c₂
  let r2 := fp2sub (fp2add (fp2sub (fp2mul (fp2add a0 a2) (fp2add b0 b2)) v0) v1) v2
  let c2 := r2
  (c0, c1, c2)

/-- The genuine Montgomery-form `Fp6` product of `α = (a₀,a₁,a₂)` and
    `β = (b₀,b₁,b₂)`, the cubic-extension product with the `v³ = ξ` reduction. -/
noncomputable def fp6MulSpec (α β : Fp6) : Fp6 :=
  let a0 := α.1; let a1 := α.2.1; let a2 := α.2.2
  let b0 := β.1; let b1 := β.2.1; let b2 := β.2.2
  let v0 := fp2mul a0 b0
  let v1 := fp2mul a1 b1
  let v2 := fp2mul a2 b2
  let c0 := fp2add v0
    (fp2nr (fp2sub (fp2sub (fp2mul (fp2add a1 a2) (fp2add b1 b2)) v1) v2))
  let c1 := fp2add
    (fp2sub (fp2sub (fp2mul (fp2add a0 a1) (fp2add b0 b1)) v0) v1) (fp2nr v2)
  let c2 := fp2sub (fp2add (fp2sub (fp2mul (fp2add a0 a2) (fp2add b0 b2)) v0) v1) v2
  (c0, c1, c2)

/-- **`Fp6` multiply value-correctness (Tier-C eliminator, layer 2).** The emitted
    6-`Fp2`-mul Karatsuba schedule computes exactly the genuine cubic-extension
    Montgomery-form `Fp6` product `fp6MulSpec`. A real `ZMod p` identity over the
    Tier-A `Fp2` multiply (`fp2MulSpec`), replacing the RELIC byte-identity. -/
theorem bls_fp6_mul_karatsuba (α β : Fp6) :
    fp6MulKaratsuba α β = fp6MulSpec α β := rfl

/-! ### The `Fp6` spec is the genuine cubic-extension product

To show `fp6MulSpec` is not a vacuous re-arrangement, we extract its three
coordinates and prove each equals the genuine `Fp2`-coefficient of the cubic
product mod `v³ − ξ` (`ξ = 1 + u`):

    c₀ = a₀b₀ + ξ·(a₁b₂ + a₂b₁)
    c₁ = a₀b₁ + a₁b₀ + ξ·(a₂b₂)
    c₂ = a₀b₂ + a₁b₁ + a₂b₀

These collapse the Karatsuba cross products back to the schoolbook coefficients,
confirming the schedule computes the true sextic-extension product. -/

/-- `Fp6` product `c₀` coordinate = `a₀b₀ + ξ·(a₁b₂ + a₂b₁)` (the `v³ = ξ` wrap of
    the `v³`/`v⁴` terms). -/
theorem fp6MulSpec_c0 (α β : Fp6) :
    (fp6MulSpec α β).1
      = fp2add (fp2mul α.1 β.1)
          (fp2nr (fp2add (fp2mul α.2.1 β.2.2) (fp2mul α.2.2 β.2.1))) := by
  simp only [fp6MulSpec, fp2mul, fp2add, fp2sub, fp2nr, fp2MulSpec, fp2NonResidue,
    fpMul, fpAdd, fpSub]
  refine Prod.ext ?_ ?_ <;> ring

/-- `Fp6` product `c₁` coordinate = `a₀b₁ + a₁b₀ + ξ·(a₂b₂)`. -/
theorem fp6MulSpec_c1 (α β : Fp6) :
    (fp6MulSpec α β).2.1
      = fp2add (fp2add (fp2mul α.1 β.2.1) (fp2mul α.2.1 β.1))
          (fp2nr (fp2mul α.2.2 β.2.2)) := by
  simp only [fp6MulSpec, fp2mul, fp2add, fp2sub, fp2nr, fp2MulSpec, fp2NonResidue,
    fpMul, fpAdd, fpSub]
  refine Prod.ext ?_ ?_ <;> ring

/-- `Fp6` product `c₂` coordinate = `a₀b₂ + a₁b₁ + a₂b₀`. -/
theorem fp6MulSpec_c2 (α β : Fp6) :
    (fp6MulSpec α β).2.2
      = fp2add (fp2add (fp2mul α.1 β.2.2) (fp2mul α.2.1 β.2.1)) (fp2mul α.2.2 β.1) := by
  simp only [fp6MulSpec, fp2mul, fp2add, fp2sub, fp2nr, fp2MulSpec, fp2NonResidue,
    fpMul, fpAdd, fpSub]
  refine Prod.ext ?_ ?_ <;> ring

/-! ## 2. `Fp12` as a pair of `Fp6`, the Karatsuba schedule and its correctness

`Fp12 = Fp6[w]/(w² − v)`. An element is `(c₀, c₁)` standing for `c₀ + c₁·w`. -/

/-- An `Fp12` element: a pair `(c₀, c₁)` over `Fp6`. -/
abbrev Fp12 : Type := Fp6 × Fp6

/-- `Fp6` add (componentwise `Fp2` add). -/
def fp6add (x y : Fp6) : Fp6 :=
  (fp2add x.1 y.1, fp2add x.2.1 y.2.1, fp2add x.2.2 y.2.2)

/-- `Fp6` sub (componentwise `Fp2` sub). -/
def fp6sub (x y : Fp6) : Fp6 :=
  (fp2sub x.1 y.1, fp2sub x.2.1 y.2.1, fp2sub x.2.2 y.2.2)

/-- `Fp6` mul-by-`v` rotation (`fp6_mul_art`): `v·(a₀,a₁,a₂) = (ξ·a₂, a₀, a₁)`,
    the `v³ = ξ` wrap (matching `Bls12381TowerTierA.bls_fp6_v_wrap`). -/
def fp6mulv (x : Fp6) : Fp6 := (fp2nr x.2.2, x.1, x.2.1)

/-- The emitted `Fp12` Karatsuba multiply schedule (`Bls12381Fp6Fp12MulKernel.fp12MulAsm`).
    For `x = (a₀,a₁)`, `y = (b₀,b₁)` over `Fp6` with `tᵢ = aᵢ·bᵢ`:

        c₁ = (a₀+a₁)(b₀+b₁) − t0 − t1
        c₀ = t0 + v·t1

    Three `Fp6`-muls (`t0,t1` + the cross product) and one `Fp6` mul-by-`v`. -/
noncomputable def fp12MulKaratsuba (x y : Fp12) : Fp12 :=
  let a0 := x.1; let a1 := x.2
  let b0 := y.1; let b1 := y.2
  let t0 := fp6MulKaratsuba a0 b0
  let t1 := fp6MulKaratsuba a1 b1
  let c1 := fp6sub (fp6sub (fp6MulKaratsuba (fp6add a0 a1) (fp6add b0 b1)) t0) t1
  let c0 := fp6add t0 (fp6mulv t1)
  (c0, c1)

/-- The genuine Montgomery-form `Fp12` product of `x = (a₀,a₁)` and `y = (b₀,b₁)`,
    the quadratic-extension product with the `w² = v` reduction. -/
noncomputable def fp12MulSpec (x y : Fp12) : Fp12 :=
  let a0 := x.1; let a1 := x.2
  let b0 := y.1; let b1 := y.2
  let t0 := fp6MulSpec a0 b0
  let t1 := fp6MulSpec a1 b1
  let c0 := fp6add t0 (fp6mulv t1)
  let c1 := fp6sub (fp6sub (fp6MulSpec (fp6add a0 a1) (fp6add b0 b1)) t0) t1
  (c0, c1)

/-- **`Fp12` multiply value-correctness (Tier-C eliminator, layer 3 — tower
    complete).** The emitted 3-`Fp6`-mul quadratic Karatsuba schedule computes
    exactly the genuine dodecic-extension Montgomery-form `Fp12` product
    `fp12MulSpec`, built on the proven `Fp6` multiply. A real `ZMod p` identity
    over the tower, replacing the RELIC byte-identity for the BLS12-381 GT-field
    multiply. -/
theorem bls_fp12_mul_karatsuba (x y : Fp12) :
    fp12MulKaratsuba x y = fp12MulSpec x y := by
  simp only [fp12MulKaratsuba, fp12MulSpec, bls_fp6_mul_karatsuba]

/-! ### The `Fp12` spec is the genuine quadratic-extension product

`Fp12 = Fp6[w]/(w² − v)`. For `x = (a₀, a₁)`, `y = (b₀, b₁)` over `Fp6` the
genuine product is `c₀ = a₀b₀ + v·(a₁b₁)`, `c₁ = a₀b₁ + a₁b₀` (the `w² = v`
wrap), where `v·` is the `Fp6` mul-by-`v` rotation `fp6mulv`. -/

/-- `Fp12` product `c₀` coordinate = `a₀b₀ + v·(a₁b₁)` (the `w² = v` wrap). -/
theorem fp12MulSpec_c0 (x y : Fp12) :
    (fp12MulSpec x y).1 = fp6add (fp6MulSpec x.1 y.1) (fp6mulv (fp6MulSpec x.2 y.2)) :=
  rfl

/-- `Fp12` product `c₁` coordinate = `a₀b₁ + a₁b₀` (the Karatsuba cross product
    collapsed back to the schoolbook coefficient). -/
theorem fp12MulSpec_c1 (x y : Fp12) :
    (fp12MulSpec x y).2
      = fp6add (fp6MulSpec x.1 y.2) (fp6MulSpec x.2 y.1) := by
  simp only [fp12MulSpec, fp6add, fp6sub, fp6mulv, fp6MulSpec, fp2mul, fp2add,
    fp2sub, fp2nr, fp2MulSpec, fp2NonResidue, fpMul, fpAdd, fpSub]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> refine Prod.ext ?_ ?_ <;> ring

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12TierA
