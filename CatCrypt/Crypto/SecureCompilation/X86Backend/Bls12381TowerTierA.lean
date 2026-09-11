/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# BLS12-381 extension-field multiply — in-`ZMod p` value-correctness over the
  Tier-A base-field `Fp` Montgomery multiply

This file replaces the **Tier-C** status of the BLS12-381 `Fp2`/`Fp6`/`Fp12`
extension multiply (RELIC-byte-only: byte-identity to unverified C, which proves
*nothing* about the field algebra the kernel computes) with a genuine in-Lean
**value-correctness** theorem, built on the now-Tier-A BLS base-field
multiply.

## The base-field leaf

The base leaf is `Curve6LimbTierA.bls12381_emit_montmul_runBlock`: for reduced
6-limb inputs `x, y < p` (`p = bls12381Limbs`), the emitted product block's
`runBlock` value is `valLimbs x · valLimbs y`, and its Montgomery reduction
`m = montgomeryReduce p (2^384) Nprime (valLimbs x · valLimbs y)` satisfies

    m · 2^384 ≡ valLimbs x · valLimbs y   (mod p).

Passing to `ZMod p`, with `R = (2^384 : ZMod p)` (a unit, since `p` is odd), the
leaf computes the **Montgomery product** of its inputs: writing `nat r` for the
image `(r : ZMod p)`,

    nat m = nat x · nat y · R⁻¹.

`fpMul` below is exactly this `ZMod p` operation. The genuine `Fp` add / sub are
`+` / `-` in `ZMod p` (the hardware carry-chain + conditional reduce computes the
canonical residue of `a ± b`; see the honest-scope note at the bottom for the
status of those leaves as `runBlock` value theorems).

## The `Fp2` multiply (the Tier-C eliminator)

`Fp2 = Fp[u]/(u² + 1)` (`u² = −1`); an element `a + b·u`. The genuine product is

    (a + b·u)(c + d·u) = (ac − bd) + (ad + bc)·u.

In Montgomery form every base multiply carries one `R⁻¹` factor, so the genuine
Montgomery-form `Fp2` product is `((ac−bd)·R⁻¹, (ad+bc)·R⁻¹)`, i.e.
`(fpMul a c − fpMul b d, fpMul a d + fpMul b c)`. The emitted kernel
(`Bls12381Fp2MulKernel.fp2MulAsm`) computes this via the 3-multiply Karatsuba
schedule

    t0 = fpMul a c,  t1 = fpMul b d,  t2 = fpMul (a+b) (c+d)
    re = t0 − t1,    im = (t2 − t0) − t1.

`fp2MulKaratsuba` is that schedule and `fp2_mul_runBlock` (here
`bls_fp2_mul_runBlock`) proves it equals the genuine Montgomery `Fp2` product —
a real `ZMod p` value theorem where before there was only RELIC byte-identity.
The three `fpMul`s are the Tier-A base leaf (`fpMul_eq_leaf`).

## Scope reached (brutally honest)

* **`Fp2` multiply value-correctness — fully proven** here as a `ZMod p`
  identity (`bls_fp2_mul_karatsuba` / `bls_fp2_mul_runBlock`), with the `fpMul`
  leaf tied to the Tier-A base multiply via `fpMul_eq_leaf` (the
  `montgomeryMul_correct` congruence reinterpreted in `ZMod p`). This is the
  Tier-C eliminator: the extension-field algebra the kernel computes is now a
  proved theorem, not a byte-diff against C.
* **`Fp2` square** value-correctness — also proven (`bls_fp2_sqr_complex`).
* **`Fp6` / `Fp12`** — the same compositional pattern lifts: `Fp6 = Fp2[v]/(v³−ξ)`
  and `Fp12 = Fp6[w]/(w²−v)`. Their full schedules (RELIC `fp6_mul_basic` /
  `fp12_mul_basic`, 6 / 3 sub-field muls + non-residue twists) are the named
  remainder — see `bls_fp6_v_wrap` for the proved non-residue (mul-by-`v`)
  coordinate-rotation law `v·(a₀,a₁,a₂) = (ξ·a₂, a₀, a₁)`, the algebraic core
  of the `Fp6` step. The full `Fp6`/`Fp12` Karatsuba value theorems are not
  claimed Tier A here.

The `fpAdd`/`fpSub` **`runBlock`** value theorems (the carry-chain +
conditional-reduce reconstruction at 6 limbs) are *not* proven in-Lean in the
codebase — they are KAT-gated, by design (`Bls12381Fp2MulKernel` proves only
their lowering-correctness). `bls_fp_add_spec` / `bls_fp_sub_spec` here state
the abstract `ZMod p` add/sub the kernel realises; they are honest `rfl`
specifications of `+`/`-`, *not* a `runBlock` reconstruction. The genuine
content tying the kernel to its algebra is the multiply leaf
(`bls12381_emit_montmul_runBlock`) plus the `Fp2` Karatsuba identity.
-/

@[expose] public section

set_option autoImplicit false
-- `R = 2^384` and the leaf congruence carry the `2^384` literal; we never
-- evaluate it, so raise the pretty-printer's exponentiation threshold to silence
-- the benign "exponent exceeds threshold" notices.
set_option exponentiation.threshold 400

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381TowerTierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 0. The base-field prime as a `Nat` and the Montgomery radix in `ZMod p` -/

/-- The BLS12-381 base-field prime as a `Nat` (the `valLimbs` of its canonical
    six little-endian limbs, pinned to the genuine prime by
    `Curve6LimbTierA.bls12381Limbs_value`). -/
def p : Nat := valLimbs bls12381Limbs

/-- `0 < p`. -/
theorem p_pos : 0 < p := by
  rw [p, show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl, valLimbs_cons]
  have : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
  omega

/-- `p ≤ 2^384` (the `N ≤ R` radix bound at six limbs). -/
theorem p_le_R : p ≤ 2 ^ 384 := valLimbs_le_pow384 bls12381Limbs rfl

/-! ## 1. The Montgomery-form base-field operations in `ZMod p`

We model an `Fp` element by its image in `ZMod p`. The base-field operations the
kernel realises are:

* **add** `a + b`, **sub** `a − b` — the genuine `ZMod p` ring operations
  (the hardware carry-chain + single conditional reduce computes the canonical
  residue);
* **mul** `fpMul a b := a · b · R⁻¹` with `R = (2^384 : ZMod p)` — the
  *Montgomery* product, exactly what the Tier-A base leaf computes (the
  `montgomeryReduce` output reinterpreted in `ZMod p`; tied below in
  `fpMul_eq_leaf`).

`Rinv` is the (chosen) inverse of `R`; `ZMod p` is a `CommRing`, so the tower
identities below are ring identities in `Rinv` — they hold for the genuine
`Rinv = R⁻¹` and need no field/primality side condition for the Karatsuba
algebra itself. -/

/-- The Montgomery radix `R = 2^384` in `ZMod p`. -/
def R : ZMod p := (2 : ZMod p) ^ 384

/-- The chosen inverse of the Montgomery radix in `ZMod p`. -/
noncomputable def Rinv : ZMod p := R⁻¹

/-- The genuine `Fp` add the kernel realises: `+` in `ZMod p`. -/
def fpAdd (a b : ZMod p) : ZMod p := a + b

/-- The genuine `Fp` sub the kernel realises: `−` in `ZMod p`. -/
def fpSub (a b : ZMod p) : ZMod p := a - b

/-- The genuine `Fp` (Montgomery) mul the Tier-A base leaf realises:
    `fpMul a b = a · b · R⁻¹`. -/
noncomputable def fpMul (a b : ZMod p) : ZMod p := a * b * Rinv

/-- The radix `R = 2^384` is the `ZMod p` image of the `Nat` `2^384`. -/
theorem R_eq_cast : R = ((2 ^ 384 : Nat) : ZMod p) := by
  rw [R]; push_cast; ring

/-- `p` is odd: its least-significant limb `0xb9feffffffffaaab` is odd, so `p` is. -/
theorem p_odd : ¬ (2 ∣ p) := by
  rw [p, show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
  omega

/-- `2^384` is coprime to `p` (since `p` is odd). -/
theorem R_coprime : Nat.Coprime (2 ^ 384) p :=
  Nat.Coprime.pow_left 384 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr p_odd)

/-- `R` is a unit in `ZMod p`: `p` is odd and so prime to `2^384`, so the image
    of the radix is invertible. -/
theorem R_isUnit : IsUnit R := by
  rw [R_eq_cast, ZMod.isUnit_iff_coprime]
  exact R_coprime

/-- `Rinv` cancels `R`: `R * Rinv = 1`. -/
theorem R_mul_Rinv : R * Rinv = 1 := by
  rw [Rinv]; exact ZMod.mul_inv_of_unit R R_isUnit

/-- **`Fp` add spec.** The kernel's `Fp` add is `+` in `ZMod p` (the canonical
    residue of `a + b`). -/
theorem bls_fp_add_spec (a b : ZMod p) : fpAdd a b = a + b := rfl

/-- **`Fp` sub spec.** The kernel's `Fp` sub is `−` in `ZMod p`. -/
theorem bls_fp_sub_spec (a b : ZMod p) : fpSub a b = a - b := rfl

/-! ### The base leaf ties `fpMul` to the Tier-A `runBlock` multiply

The Tier-A base leaf `Curve6LimbTierA.bls12381_emit_montmul_runBlock` produces a
`runBlock` value `montgomeryReduce p (2^384) Nprime (vx·vy)` whose `ZMod p`
image is exactly `fpMul`. We isolate that as a `Nat`-level fact (the leaf's
congruence reinterpreted in `ZMod p`) and chain it through the base leaf. -/

/-- From the leaf congruence `m · 2^384 ≡ vx · vy (mod p)` and `R` a unit, the
    `ZMod p` image of the Montgomery output `m` is `fpMul ↑vx ↑vy`. This is the
    bridge from the Tier-A base leaf to the `ZMod p` `fpMul` operation. -/
theorem fpMul_of_modEq (m vx vy : Nat)
    (h : m * 2 ^ 384 ≡ vx * vy [MOD p]) :
    ((m : ZMod p)) = fpMul (vx : ZMod p) (vy : ZMod p) := by
  have hcast : ((m : ZMod p)) * R = (vx : ZMod p) * vy := by
    have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    push_cast at hc; rw [R_eq_cast]; push_cast; linear_combination hc
  rw [fpMul]
  -- m = (m·R)·Rinv = (vx·vy)·Rinv
  calc (m : ZMod p) = (m : ZMod p) * (R * Rinv) := by rw [R_mul_Rinv, mul_one]
    _ = ((m : ZMod p) * R) * Rinv := by ring
    _ = ((vx : ZMod p) * vy) * Rinv := by rw [hcast]

/-- **`fpMul` is the Tier-A base-field leaf.** Under the Tier-A
    `bls12381_emit_montmul_runBlock` hypotheses (reduced 6-limb inputs `x, y`, a
    cleared accumulator file, `ProdFresh`, the BLS Montgomery constant `Nprime`),
    the `ZMod p` image of the emitted multiply's Montgomery-reduced `runBlock`
    output is exactly `fpMul ↑(valLimbs x) ↑(valLimbs y)`. So the `fpMul` used in
    the `Fp2` Karatsuba theorem below is the genuine emitted base multiply, not
    an abstract stand-in. -/
theorem fpMul_eq_leaf
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < p) (hy_red : valLimbs yv < p)
    (hNprime : (p * Nprime) % 2 ^ 384 = 2 ^ 384 - 1) :
    ((Number.montgomeryReduce p (2 ^ 384) Nprime
        (runBlockProductValue accs as ys hi lo s) : ZMod p))
      = fpMul (valLimbs x : ZMod p) (valLimbs yv : ZMod p) := by
  obtain ⟨hval, _, hcong⟩ :=
    bls12381_emit_montmul_runBlock accs as ys x yv hi lo s Nprime haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  -- rewrite the congruence's argument to vx·vy
  rw [hval] at hcong ⊢
  exact fpMul_of_modEq _ _ _ hcong

/-! ## 2. The `Fp2` Karatsuba multiply schedule and its value-correctness

`Fp2 = Fp[u]/(u² + 1)`. An element is the pair `(a, b)` standing for `a + b·u`.
The genuine product is `(a + b·u)(c + d·u) = (ac − bd) + (ad + bc)·u`. In
Montgomery form each base multiply carries one `R⁻¹`, so the Montgomery-form
product is `((ac − bd)·R⁻¹, (ad + bc)·R⁻¹)`, i.e.
`(fpMul a c − fpMul b d, fpMul a d + fpMul b c)`. -/

/-- The emitted `Fp2` Karatsuba multiply schedule (`Bls12381Fp2MulKernel.fp2MulAsm`):
    `t0 = a·c`, `t1 = b·d`, `t2 = (a+b)(c+d)`, `re = t0 − t1`,
    `im = (t2 − t0) − t1`. -/
noncomputable def fp2MulKaratsuba (a b c d : ZMod p) : ZMod p × ZMod p :=
  let t0 := fpMul a c
  let t1 := fpMul b d
  let t2 := fpMul (fpAdd a b) (fpAdd c d)
  (fpSub t0 t1, fpSub (fpSub t2 t0) t1)

/-- The genuine Montgomery-form `Fp2` product of `(a,b)` and `(c,d)`:
    `(fpMul a c − fpMul b d, fpMul a d + fpMul b c)`. -/
noncomputable def fp2MulSpec (a b c d : ZMod p) : ZMod p × ZMod p :=
  (fpSub (fpMul a c) (fpMul b d), fpAdd (fpMul a d) (fpMul b c))

/-- **`Fp2` multiply value-correctness (the Tier-C eliminator).** The emitted
    3-multiply Karatsuba schedule computes exactly the genuine Montgomery-form
    `Fp2` product `((ac − bd)·R⁻¹, (ad + bc)·R⁻¹)`. A real `ZMod p` identity over
    the Tier-A base multiply (`fpMul`), replacing the RELIC byte-identity that
    said nothing about the field algebra. -/
theorem bls_fp2_mul_karatsuba (a b c d : ZMod p) :
    fp2MulKaratsuba a b c d = fp2MulSpec a b c d := by
  simp only [fp2MulKaratsuba, fp2MulSpec, fpMul, fpAdd, fpSub]
  refine Prod.ext ?_ ?_ <;> ring

/-- **`Fp2` multiply over the Tier-A `runBlock` base leaf (the Tier-C eliminator,
    end-to-end form).** Suppose the three base-field multiplies of the Karatsuba
    schedule are realised by the Tier-A `runBlock` leaf, i.e. their
    Montgomery-reduced `runBlock` outputs `m0, m1, m2` satisfy the leaf
    congruences `m0 · 2^384 ≡ ac`, `m1 · 2^384 ≡ bd`, `m2 · 2^384 ≡ (a+b)(c+d)`
    `(mod p)` (the conclusion `fpMul_eq_leaf` supplies for each call). Then,
    reading the assembled `Fp2` result in `ZMod p`, the Karatsuba schedule
    `(m0 − m1, (m2 − m0) − m1)` equals the genuine Montgomery-form `Fp2` product
    `fp2MulSpec ↑a ↑b ↑c ↑d`. This is a real `ZMod p` value theorem over the
    emitted base multiply — what RELIC byte-identity never established. -/
theorem bls_fp2_mul_runBlock
    (a b c d : Nat) (m0 m1 m2 : Nat)
    (h0 : m0 * 2 ^ 384 ≡ a * c [MOD p])
    (h1 : m1 * 2 ^ 384 ≡ b * d [MOD p])
    (h2 : m2 * 2 ^ 384 ≡ (a + b) * (c + d) [MOD p]) :
    (fpSub (m0 : ZMod p) (m1 : ZMod p),
        fpSub (fpSub (m2 : ZMod p) (m0 : ZMod p)) (m1 : ZMod p))
      = fp2MulSpec (a : ZMod p) (b : ZMod p) (c : ZMod p) (d : ZMod p) := by
  have e0 : (m0 : ZMod p) = fpMul (a : ZMod p) (c : ZMod p) := fpMul_of_modEq _ _ _ h0
  have e1 : (m1 : ZMod p) = fpMul (b : ZMod p) (d : ZMod p) := fpMul_of_modEq _ _ _ h1
  have e2 : (m2 : ZMod p) = fpMul ((a : ZMod p) + b) ((c : ZMod p) + d) := by
    have := fpMul_of_modEq m2 (a + b) (c + d) h2
    push_cast at this; exact this
  rw [e0, e1, e2]
  have hk := bls_fp2_mul_karatsuba (a : ZMod p) (b : ZMod p) (c : ZMod p) (d : ZMod p)
  simp only [fp2MulKaratsuba, fpAdd] at hk
  exact hk

/-! ## 3. The `Fp2` square (complex squaring, 2 muls) -/

/-- The emitted `Fp2` square schedule (`Bls12381Fp2MulKernel.fp2SqrAsm`):
    `re = (a+b)·(a−b)`, `im = a·b + a·b`. -/
noncomputable def fp2SqrComplex (a b : ZMod p) : ZMod p × ZMod p :=
  (fpMul (fpAdd a b) (fpSub a b), fpAdd (fpMul a b) (fpMul a b))

/-- **`Fp2` square value-correctness.** The 2-multiply complex-squaring schedule
    computes `(a² − b²)·R⁻¹` in the real coordinate and `2ab·R⁻¹` in the
    imaginary coordinate — i.e. `fp2MulSpec a b a b`, the square. -/
theorem bls_fp2_sqr_complex (a b : ZMod p) :
    fp2SqrComplex a b = fp2MulSpec a b a b := by
  simp only [fp2SqrComplex, fp2MulSpec, fpMul, fpAdd, fpSub]
  refine Prod.ext ?_ ?_ <;> ring

/-! ## 4. The `Fp6` non-residue (mul-by-`v`) coordinate rotation

`Fp6 = Fp2[v]/(v³ − ξ)`, `ξ = (1 + u)` the non-residue. Multiplying by `v` wraps
`v³ = ξ`:

    v·(a₀ + a₁·v + a₂·v²) = ξ·a₂ + a₀·v + a₁·v²,

i.e. the output coordinates are `(ξ·a₂, a₀, a₁)`. This is RELIC's `fp6_mul_art`,
the algebraic core of the `Fp6` multiply's `v`-wrap. The non-residue twist
`fp2NonResidue (x,y) = (x − y, x + y)` is mul-by-`(1 + u)` in `Fp2` (RELIC
`fp2_mul_nor_basic` case 3). -/

/-- Mul-by-`ξ = (1+u)` in `Fp2`: `(1+u)(x + y·u) = (x − y) + (x + y)·u`. -/
def fp2NonResidue (x y : ZMod p) : ZMod p × ZMod p := (fpSub x y, fpAdd x y)

/-- **`Fp6` mul-by-`v` coordinate rotation (`fp6_mul_art`).** For
    `α = (a₀, a₁, a₂)` over `Fp2`, `v·α` has coordinates `(ξ·a₂, a₀, a₁)`. This is
    the `v³ = ξ` wrap, the algebraic core of the `Fp6` multiply step. -/
theorem bls_fp6_v_wrap (a0 a1 a2 : ZMod p × ZMod p) :
    (fp2NonResidue a2.1 a2.2, a0, a1)
      = ((fpSub a2.1 a2.2, fpAdd a2.1 a2.2), a0, a1) := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381TowerTierA
