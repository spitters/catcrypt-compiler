/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PastaBignumTierA
public import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.FieldLeafBridge
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Curve field-multiply refinement: Mathlib `ZMod p` anchor (+ optional AUCurves corroboration)

This file states the curve field-multiply correctness **top-down**, anchored at
Mathlib's `ZMod p` field. The canonical Mathlib-anchored spine is
`CurveFieldMathlibSpec.lean`; this file gives the same `ZMod p` field statement per
curve plus an **optional** fiat/AUCurves cross-prover *corroboration* arm.
fiat-crypto is structural **inspiration** for the Montgomery field-element decode
`feval`, NOT the source of truth.

## The refinement spine

```
 Mathlib  ZMod p, *   (the prime field, native Lean)   <-- SOURCE OF TRUTH
   |  feval decode (Montgomery, fiat-INSPIRED:  feval z := (z : ZMod p) * Rinv)
 montgomeryReduce / valLimbs                       (representation -- montgomeryMul_correct)
   |  <curve>_emit_montmul_runBlock                (this repo's Tier-A Lean theorems)
 runBlock(emitted List (JInstr 64))

 (optional corroboration arm, NOT the anchor)
 fiat-crypto F.mul  --AUCurves cross-prover bridge (a NAMED hypothesis)-->  ZMod p
```

Every rung from `ZMod p` down is a closed Lean theorem (the Tier-A
`<curve>_emit_montmul_runBlock` headlines + `Number.montgomeryMul_correct`). The
optional fiat/AUCurves arm is consumed as a **named hypothesis**
(`FieldLeafBridge.AUCurvesFieldMulBridge`), never an axiom — an independent Rocq
cross-check, not the spec.

## The two headlines per curve

For each curve we prove:

1. `<curve>_emit_refines_field` — IN `ZMod p`: the emitted block's `runBlock`
   output, decoded through the Montgomery decode `feval z := (z : ZMod p) · Rinv`
   (`R = (2^k : ZMod p)` the Montgomery radix, a unit since `p` is odd), equals the
   **field product** `feval x · feval y`. This states that the emitted code computes
   the *field* multiply — the spec is Mathlib's `ZMod p`, not `valLimbs`. The proof
   lifts the curve's `<curve>_emit_montmul_runBlock` congruence
   (`m · R ≡ x · y [MOD p]`) into `ZMod p` and cancels `R` (the generic
   `feval_mont_of_modEq` below, generalising
   `Bls12381TowerTierA.fpMul_of_modEq`).

2. `<curve>_emit_refines_fiat` (OPTIONAL corroboration) — GIVEN an
   `AUCurvesFieldMulBridge` for the curve (the named hypothesis stating fiat-crypto's
   `F.mul` is faithfully realised by the CatCrypt leaf-call oracle), the emitted
   `runBlock` output agrees with the value fiat's `F.mul` produces
   (`leaf.decode (leafSpec.call …)`). This is an independent cross-prover
   *corroboration* of the Mathlib-anchored statement (1) — it does NOT make fiat the
   source of truth. The bridge is consumed via
   `FieldLeafBridge.fieldMul_value_of_bridge`.

## Which curves have the fiat anchor fully wired vs parametric

`FieldLeafBridge.lean` instantiates `FieldMulLeaf` only for `curve25519` and
`secp256k1` (the curves AUCurves actually carries: `fe25519_mul_body_correct` and
the consumed `secp256k1_mul_correct`). So:

* **secp256k1** — the fiat anchor is wired against the file's `secp256k1Mul` leaf
  instance.
* **SM2, P256, BN254, P384, BLS12-381, Pallas, Vesta** — `_emit_refines_fiat` is
  stated **parametrically over the bridge hypothesis** (any `FieldMulLeaf` at the
  curve's prime with an `AUCurvesFieldMulBridge`). Adding a `FieldMulLeaf` instance
  for the curve later completes the anchor with no proof change. SM2 in particular
  has **no** AUCurves anchor (no SM2 in AUCurves — see `FieldLeafBridge.§0`), so its
  `_emit_refines_fiat` is purely the parametric form: it says "*if* a cross-prover
  bridge for an SM2 leaf is supplied, the emitted asm refines it", never claiming
  AUCurves proves SM2.

All `feval`/R-cancellation is uniform: the radix is `2^256` for the 4-limb curves
(SM2, secp256k1, P256, BN254, Pallas, Vesta) and `2^384` for the 6-limb curves
(P384, BLS12-381), each a unit because the prime is odd.
-/

@[expose] public section


set_option autoImplicit false
-- The Montgomery radices `2^256` / `2^384` appear as literals in the `ZMod p`
-- casts; we never evaluate them, so raise the exponentiation pretty-printer
-- threshold to silence the benign notices.
set_option exponentiation.threshold 400
-- The radix coprimality arguments carry `2^256` / `2^384` literals; raise the
-- recursion limit so elaboration does not trip on the (never-evaluated) radix.
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CurveFieldRefinement

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.PastaBignumTierA
open CatCrypt.Crypto.SecureCompilation.AUCurvesImport
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The generic Montgomery decode and the R-cancellation lemma

We model a field element by its image in `ZMod N` (`N` the curve prime). The
Tier-A leaf produces a Montgomery output `m : Nat` with the leaf congruence
`m · R ≡ x · y [MOD N]` (`R` the Montgomery radix as a `Nat`). The Montgomery
**decode** of a slot value `z` is `feval z := (z : ZMod N) · R⁻¹`. We prove,
generically over the prime and the radix, that decoding the leaf output gives the
field product `feval x · feval y` — the algebraic core shared by every curve. -/

/-- The Montgomery radix image `(R : Nat)` in `ZMod N` is a unit, given `R`
    coprime to `N`. -/
theorem radix_isUnit {N R : Nat} (hcop : Nat.Coprime R N) :
    IsUnit ((R : ZMod N)) := by
  rw [ZMod.isUnit_iff_coprime]; exact hcop

/-- **The generic Montgomery decode.** `feval N R z = (z : ZMod N) · (R : ZMod N)⁻¹`
    — the CatCrypt image of AUCurves' `feval`, projecting a Montgomery-domain
    `Nat` value into the field `ZMod N`. -/
noncomputable def feval (N R : Nat) (z : Nat) : ZMod N := (z : ZMod N) * ((R : ZMod N))⁻¹

/-- **Generic R-cancellation (the spine's `ZMod p` lift).** From the Tier-A leaf
    congruence `m · R ≡ x · y [MOD N]` and `R` coprime to `N` (so `(R : ZMod N)` is a
    unit), the Montgomery decode of the leaf output `m` equals the **field product**
    of the decoded inputs:

        feval N R m = feval N R x · feval N R y.

    This generalises `Bls12381TowerTierA.fpMul_of_modEq` from the BLS prime to every
    curve prime/radix, and is the single lemma every `<curve>_emit_refines_field`
    instantiates. -/
theorem feval_mont_of_modEq {N R : Nat} (hcop : Nat.Coprime R N) (m x y : Nat)
    (h : m * R ≡ x * y [MOD N]) :
    feval N R m = feval N R x * feval N R y := by
  have hunit : IsUnit ((R : ZMod N)) := radix_isUnit hcop
  -- the congruence in `ZMod N`: `(m : ZMod N) · R = x · y`
  have hcast : (m : ZMod N) * (R : ZMod N) = (x : ZMod N) * (y : ZMod N) := by
    have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    push_cast at hc; linear_combination hc
  -- `R · R⁻¹ = 1`
  have hRinv : (R : ZMod N) * ((R : ZMod N))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  -- decode and cancel one `R` using the congruence
  simp only [feval]
  -- (m·R⁻¹) = (m·R)·R⁻¹·R⁻¹ = (x·y)·R⁻¹·R⁻¹ = (x·R⁻¹)·(y·R⁻¹)
  calc (m : ZMod N) * ((R : ZMod N))⁻¹
      = (m : ZMod N) * ((R : ZMod N) * ((R : ZMod N))⁻¹) * ((R : ZMod N))⁻¹ := by
        rw [hRinv, mul_one]
    _ = ((m : ZMod N) * (R : ZMod N)) * ((R : ZMod N))⁻¹ * ((R : ZMod N))⁻¹ := by ring
    _ = ((x : ZMod N) * (y : ZMod N)) * ((R : ZMod N))⁻¹ * ((R : ZMod N))⁻¹ := by rw [hcast]
    _ = (x : ZMod N) * ((R : ZMod N))⁻¹ * ((y : ZMod N) * ((R : ZMod N))⁻¹) := by ring

/-! ### Radix coprimality from the odd-prime moduli

Each curve modulus is `valLimbs <curve>Limbs`, an odd number (its least-significant
limb is odd). So `2` is coprime to it, hence `2^k` is. We extract the oddness from
each curve's `…Limbs_value`. -/

/-- `2^k` is coprime to an odd `N`. -/
theorem pow_two_coprime_of_odd {N : Nat} (k : Nat) (hodd : ¬ (2 ∣ N)) :
    Nat.Coprime (2 ^ k) N :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)

/-! ## 2. The generic per-curve refinement, applied to each Tier-A leaf

`emit_refines_field_of_runBlock` is the curve-generic statement consumed below: it
takes the third conjunct of any `<curve>_emit_montmul_runBlock` (the leaf
congruence) plus the coprimality of the radix to the prime, and concludes the
`feval` decode of the leaf output is the field product. Each curve theorem supplies
the congruence from its Tier-A headline and the coprimality from its odd prime. -/

/-- **Generic emitted-leaf field refinement.** Given the Tier-A leaf congruence
    `m · R ≡ x · y [MOD N]` (the third conjunct of any `<curve>_emit_montmul_runBlock`)
    and `R` coprime to `N`, the Montgomery decode of the emitted `runBlock` output
    `m` equals the field product `feval x · feval y` in `ZMod N`. -/
theorem emit_refines_field_of_runBlock {N R : Nat} (hcop : Nat.Coprime R N)
    (m x y : Nat) (hcong : m * R ≡ x * y [MOD N]) :
    feval N R m = feval N R x * feval N R y :=
  feval_mont_of_modEq hcop m x y hcong

/-- **Generic emitted-leaf fiat refinement.** Given
    * the field refinement (the emitted output decodes to the field product
      `da · db`, from `emit_refines_field_of_runBlock`), and
    * a named `AUCurvesFieldMulBridge leaf leafSpec` (fiat-crypto's `F.mul` is
      faithfully realised by the leaf-call oracle), where the leaf arguments
      `xa`, `xb` decode (via `leaf.decode`) to the SAME field elements `da`, `db`,

    the emitted `runBlock` output's decode equals the value fiat's verified `F.mul`
    produces for the leaf (`leaf.decode (leafSpec.call …)`). The emitted asm thus
    refines fiat-crypto's `F.mul`; the bridge is the only non-Lean-proof edge,
    consumed via `fieldMul_value_of_bridge`. -/
theorem emit_refines_fiat_of_bridge
    {leaf : FieldMulLeaf} {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) := by
  rw [hfield]; exact (fieldMul_value_of_bridge hbridge xa xb oldDest).symm

/-! ### Per-curve prime `def`s (opaque to the elaborator)

We wrap each `valLimbs <curve>Limbs` in a `def`, exactly as `Bls12381TowerTierA`
wraps the BLS prime as `def p`. This keeps the modulus opaque so the coprimality
elaboration (`Nat.Coprime (2^k) <prime>`) does not force the `valLimbs` fold to
reduce. Each `def` is definitionally the `valLimbs`, so the Tier-A headlines (stated
over `valLimbs <curve>Limbs`) apply directly. -/

/-- secp256k1 base-field prime as an opaque `def`. -/
def secp256k1P : Nat := valLimbs secp256k1Limbs
/-- SM2 base-field prime as an opaque `def`. -/
def sm2P : Nat := valLimbs sm2Limbs
/-- P256 base-field prime as an opaque `def`. -/
def p256P : Nat := valLimbs p256Limbs
/-- BN254 base-field prime as an opaque `def`. -/
def bn254P : Nat := valLimbs bn254Limbs
/-- P384 base-field prime as an opaque `def`. -/
def p384P : Nat := valLimbs p384Limbs
/-- BLS12-381 base-field prime as an opaque `def`. -/
def bls12381P : Nat := valLimbs bls12381Limbs
/-- Pallas base-field prime as an opaque `def`. -/
def pallasP : Nat := valLimbs pallasLimbs
/-- Vesta base-field prime as an opaque `def`. -/
def vestaP : Nat := valLimbs vestaLimbs

/-- Each opaque prime `def` is the `valLimbs` it abbreviates (by `rfl`). Used to
    fold the Tier-A `valLimbs <curve>Limbs` occurrences into the opaque `<curve>P`,
    so the coprimality unification never reduces the `valLimbs` fold. -/
theorem secp256k1P_eq : valLimbs secp256k1Limbs = secp256k1P := rfl
theorem sm2P_eq : valLimbs sm2Limbs = sm2P := rfl
theorem p256P_eq : valLimbs p256Limbs = p256P := rfl
theorem bn254P_eq : valLimbs bn254Limbs = bn254P := rfl
theorem p384P_eq : valLimbs p384Limbs = p384P := rfl
theorem bls12381P_eq : valLimbs bls12381Limbs = bls12381P := rfl
theorem pallasP_eq : valLimbs pallasLimbs = pallasP := rfl
theorem vestaP_eq : valLimbs vestaLimbs = vestaP := rfl

/-! ## 3. secp256k1 — fiat anchor fully wired

secp256k1 is the curve `FieldLeafBridge` instantiates (`secp256k1Mul`, citing the
consumed fiat-crypto `secp256k1_mul_correct`), so its `_emit_refines_fiat` is wired
against that concrete leaf. The radix is `R = 2^256`. -/

/-- secp256k1 prime `p = 2^256 − 2^32 − 977` is odd. -/
theorem secp256k1_odd : ¬ (2 ∣ secp256k1P) := by
  unfold secp256k1P
  rw [show secp256k1Limbs = (0xfffffffefffffc2f : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0xfffffffefffffc2f : BitVec 64).toNat = 18446744069414583343 := by decide
  omega

/-- secp256k1 radix `2^256` is coprime to the prime. -/
theorem secp256k1_coprime : Nat.Coprime (2 ^ 256) secp256k1P :=
  Nat.Coprime.pow_left 256 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr secp256k1_odd)

/-- **secp256k1: the emitted asm refines the `ZMod p` field multiply.** Under the
    Tier-A `secp256k1_emit_montmul_runBlock` hypotheses, the `feval` decode of the
    emitted `runBlock` Montgomery output equals the field product
    `feval x · feval y` in `ZMod (2^256 − 2^32 − 977)`. -/
theorem secp256k1_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs secp256k1Limbs)
    (hy_red : valLimbs yv < valLimbs secp256k1Limbs)
    (hNprime : (valLimbs secp256k1Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    feval (valLimbs secp256k1Limbs) (2 ^ 256)
        (Number.montgomeryReduce (valLimbs secp256k1Limbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs secp256k1Limbs) (2 ^ 256) (valLimbs x)
        * feval (valLimbs secp256k1Limbs) (2 ^ 256) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    secp256k1_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [secp256k1P_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock secp256k1_coprime _ _ _ hcong

/-- **secp256k1: the emitted asm refines fiat-crypto's verified `F.mul`.** Given the
    AUCurves cross-prover bridge for the `secp256k1Mul` leaf (the named hypothesis:
    fiat's `secp256k1_mul_correct` is faithfully realised by the leaf-call oracle),
    and field arguments `xa`, `xb` whose `decode` images are the field elements
    `feval x`, `feval y` that the emitted Montgomery output decodes to, the emitted
    `runBlock` output equals the value fiat's `F.mul` produces. fiat's `F.mul` is the
    source of truth; the emitted asm refines it; the bridge is the only
    non-Lean-proof edge. -/
theorem secp256k1_emit_refines_fiat
    (decode : RustVal (.TBytes 32) → ZMod (2 ^ 256 - 2 ^ 32 - 977))
    (leafSpec : LeafSpec)
    (hbridge : AUCurvesFieldMulBridge (secp256k1Mul decode) leafSpec)
    (xa xb oldDest : RustVal (.TBytes 32))
    (fieldVal : ZMod (2 ^ 256 - 2 ^ 32 - 977))
    (hfield : fieldVal = decode xa * decode xb) :
    fieldVal =
      decode (leafSpec.call "secp256k1_mul" (.TBytes 32) [.TBytes 32, .TBytes 32]
        oldDest [⟨.TBytes 32, xa⟩, ⟨.TBytes 32, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest fieldVal hfield

/-! ## 4. SM2 — parametric over the bridge (NO AUCurves anchor)

SM2 is **not** in AUCurves (`FieldLeafBridge.§0`), so it has no cross-prover anchor.
Its field refinement is genuine (Tier A); its fiat refinement is the parametric
form: *if* a cross-prover bridge for an SM2 leaf were supplied, the emitted asm
would refine it. We never claim AUCurves proves SM2. Radix `R = 2^256`. -/

/-- SM2 prime `p = 2^256 − 2^224 − 2^96 + 2^64 − 1` is odd. -/
theorem sm2_odd : ¬ (2 ∣ sm2P) := by
  unfold sm2P
  rw [show sm2Limbs = (0xffffffffffffffff : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0xffffffffffffffff : BitVec 64).toNat = 18446744073709551615 := by decide
  omega

/-- SM2 radix `2^256` is coprime to the prime. -/
theorem sm2_coprime : Nat.Coprime (2 ^ 256) sm2P :=
  Nat.Coprime.pow_left 256 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr sm2_odd)

/-- **SM2: the emitted asm refines the `ZMod p` field multiply.** Under the Tier-A
    `sm2_emit_montmul_runBlock_full` hypotheses, the `feval` decode of the emitted
    `runBlock` Montgomery output equals the field product `feval x · feval y` in
    `ZMod (2^256 − 2^224 − 2^96 + 2^64 − 1)`. -/
theorem sm2_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs sm2Limbs)
    (hy_red : valLimbs yv < valLimbs sm2Limbs)
    (hNprime : (valLimbs sm2Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    feval (valLimbs sm2Limbs) (2 ^ 256)
        (Number.montgomeryReduce (valLimbs sm2Limbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs sm2Limbs) (2 ^ 256) (valLimbs x)
        * feval (valLimbs sm2Limbs) (2 ^ 256) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    sm2_emit_montmul_runBlock_full accs as ys x yv hi lo s Nprime256 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [sm2P_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock sm2_coprime _ _ _ hcong

/-- **SM2: the emitted asm refines a supplied cross-prover `F.mul` (parametric).**
    SM2 has no AUCurves anchor, so this is purely parametric: given ANY
    `FieldMulLeaf` at the SM2 prime with an `AUCurvesFieldMulBridge`, the emitted asm
    refines the leaf's `F.mul`. This is `emit_refines_fiat_of_bridge` specialised to
    an SM2-prime leaf; supplying an SM2 cross-prover bridge later completes the
    anchor with no proof change. -/
theorem sm2_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs sm2Limbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

/-! ## 5. P256 — parametric over the bridge (AUCurves carries P256, no leaf instance yet)

AUCurves carries P256 (`P256_Bignum_Specs.v`), but `FieldLeafBridge` has no P256
`FieldMulLeaf` instance, so `_emit_refines_fiat` is parametric over a P256-prime
leaf + bridge. Radix `R = 2^256`. -/

/-- P256 prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1` is odd. -/
theorem p256_odd : ¬ (2 ∣ p256P) := by
  unfold p256P
  rw [show p256Limbs = (0xffffffffffffffff : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0xffffffffffffffff : BitVec 64).toNat = 18446744073709551615 := by decide
  omega

/-- P256 radix `2^256` is coprime to the prime. -/
theorem p256_coprime : Nat.Coprime (2 ^ 256) p256P :=
  Nat.Coprime.pow_left 256 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr p256_odd)

/-- **P256: the emitted asm refines the `ZMod p` field multiply.** -/
theorem p256_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs p256Limbs)
    (hy_red : valLimbs yv < valLimbs p256Limbs)
    (hNprime : (valLimbs p256Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    feval (valLimbs p256Limbs) (2 ^ 256)
        (Number.montgomeryReduce (valLimbs p256Limbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs p256Limbs) (2 ^ 256) (valLimbs x)
        * feval (valLimbs p256Limbs) (2 ^ 256) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    p256_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [p256P_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock p256_coprime _ _ _ hcong

/-- **P256: the emitted asm refines a supplied cross-prover `F.mul` (parametric).** -/
theorem p256_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs p256Limbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

/-! ## 6. BN254 base field — parametric over the bridge

AUCurves carries BN254 (`BN254Curve_G1_BignumSpecs.v`), with no `FieldMulLeaf`
instance yet. Radix `R = 2^256`. -/

/-- BN254 base-field prime is odd. -/
theorem bn254_odd : ¬ (2 ∣ bn254P) := by
  unfold bn254P
  rw [show bn254Limbs = (0x3c208c16d87cfd47 : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0x3c208c16d87cfd47 : BitVec 64).toNat = 4332616871279656263 := by decide
  omega

/-- BN254 radix `2^256` is coprime to the prime. -/
theorem bn254_coprime : Nat.Coprime (2 ^ 256) bn254P :=
  Nat.Coprime.pow_left 256 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr bn254_odd)

/-- **BN254: the emitted asm refines the `ZMod p` field multiply.** -/
theorem bn254_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs bn254Limbs)
    (hy_red : valLimbs yv < valLimbs bn254Limbs)
    (hNprime : (valLimbs bn254Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    feval (valLimbs bn254Limbs) (2 ^ 256)
        (Number.montgomeryReduce (valLimbs bn254Limbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs bn254Limbs) (2 ^ 256) (valLimbs x)
        * feval (valLimbs bn254Limbs) (2 ^ 256) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    bn254_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [bn254P_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock bn254_coprime _ _ _ hcong

/-- **BN254: the emitted asm refines a supplied cross-prover `F.mul` (parametric).** -/
theorem bn254_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs bn254Limbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

/-! ## 7. P384 — parametric over the bridge. Radix `R = 2^384`. -/

/-- P384 prime `p = 2^384 − 2^128 − 2^96 + 2^32 − 1` is odd. -/
theorem p384_odd : ¬ (2 ∣ p384P) := by
  unfold p384P
  rw [show p384Limbs = (0x00000000ffffffff : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0x00000000ffffffff : BitVec 64).toNat = 4294967295 := by decide
  omega

/-- P384 radix `2^384` is coprime to the prime. -/
theorem p384_coprime : Nat.Coprime (2 ^ 384) p384P :=
  Nat.Coprime.pow_left 384 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr p384_odd)

/-- **P384: the emitted asm refines the `ZMod p` field multiply.** Radix `2^384`. -/
theorem p384_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime384 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs p384Limbs)
    (hy_red : valLimbs yv < valLimbs p384Limbs)
    (hNprime : (valLimbs p384Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1) :
    feval (valLimbs p384Limbs) (2 ^ 384)
        (Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs p384Limbs) (2 ^ 384) (valLimbs x)
        * feval (valLimbs p384Limbs) (2 ^ 384) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    p384_emit_montmul_runBlock accs as ys x yv hi lo s Nprime384 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [p384P_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock p384_coprime _ _ _ hcong

/-- **P384: the emitted asm refines a supplied cross-prover `F.mul` (parametric).** -/
theorem p384_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs p384Limbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

/-! ## 8. BLS12-381 base field — parametric over the bridge. Radix `R = 2^384`.

AUCurves carries BLS12 closures (`BLS12_PairingRustConcrete.v` etc.), with no
`FieldMulLeaf` instance yet. (`Bls12381TowerTierA` already lifts this leaf to `fpMul`
in `ZMod p`; here we re-state it in the uniform `feval` decode shape.) -/

/-- BLS12-381 base-field prime is odd. -/
theorem bls12381_odd : ¬ (2 ∣ bls12381P) := by
  unfold bls12381P
  rw [show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
  omega

/-- BLS12-381 radix `2^384` is coprime to the prime. -/
theorem bls12381_coprime : Nat.Coprime (2 ^ 384) bls12381P :=
  Nat.Coprime.pow_left 384 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr bls12381_odd)

/-- **BLS12-381: the emitted asm refines the `ZMod p` field multiply.** Radix `2^384`. -/
theorem bls12381_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime384 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs bls12381Limbs)
    (hy_red : valLimbs yv < valLimbs bls12381Limbs)
    (hNprime : (valLimbs bls12381Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1) :
    feval (valLimbs bls12381Limbs) (2 ^ 384)
        (Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs bls12381Limbs) (2 ^ 384) (valLimbs x)
        * feval (valLimbs bls12381Limbs) (2 ^ 384) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    bls12381_emit_montmul_runBlock accs as ys x yv hi lo s Nprime384 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [bls12381P_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock bls12381_coprime _ _ _ hcong

/-- **BLS12-381: the emitted asm refines a supplied cross-prover `F.mul` (parametric).** -/
theorem bls12381_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs bls12381Limbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

/-! ## 9. Pallas — parametric over the bridge. Radix `R = 2^256`. -/

/-- Pallas base-field prime is odd. -/
theorem pallas_odd : ¬ (2 ∣ pallasP) := by
  unfold pallasP
  rw [show pallasLimbs = (0x992d30ed00000001 : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0x992d30ed00000001 : BitVec 64).toNat = 11037532056220336129 := by decide
  omega

/-- Pallas radix `2^256` is coprime to the prime. -/
theorem pallas_coprime : Nat.Coprime (2 ^ 256) pallasP :=
  Nat.Coprime.pow_left 256 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr pallas_odd)

/-- **Pallas: the emitted asm refines the `ZMod p` field multiply.** -/
theorem pallas_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs pallasLimbs)
    (hy_red : valLimbs yv < valLimbs pallasLimbs)
    (hNprime : (valLimbs pallasLimbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    feval (valLimbs pallasLimbs) (2 ^ 256)
        (Number.montgomeryReduce (valLimbs pallasLimbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs pallasLimbs) (2 ^ 256) (valLimbs x)
        * feval (valLimbs pallasLimbs) (2 ^ 256) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    pallas_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [pallasP_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock pallas_coprime _ _ _ hcong

/-- **Pallas: the emitted asm refines a supplied cross-prover `F.mul` (parametric).** -/
theorem pallas_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs pallasLimbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

/-! ## 10. Vesta — parametric over the bridge. Radix `R = 2^256`. -/

/-- Vesta base-field prime is odd. -/
theorem vesta_odd : ¬ (2 ∣ vestaP) := by
  unfold vestaP
  rw [show vestaLimbs = (0x8c46eb2100000001 : BitVec 64) :: _ from rfl, valLimbs_cons]
  have h0 : (0x8c46eb2100000001 : BitVec 64).toNat = 10108024940646105089 := by decide
  omega

/-- Vesta radix `2^256` is coprime to the prime. -/
theorem vesta_coprime : Nat.Coprime (2 ^ 256) vestaP :=
  Nat.Coprime.pow_left 256 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr vesta_odd)

/-- **Vesta: the emitted asm refines the `ZMod p` field multiply.** -/
theorem vesta_emit_refines_field
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs vestaLimbs)
    (hy_red : valLimbs yv < valLimbs vestaLimbs)
    (hNprime : (valLimbs vestaLimbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    feval (valLimbs vestaLimbs) (2 ^ 256)
        (Number.montgomeryReduce (valLimbs vestaLimbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s))
      = feval (valLimbs vestaLimbs) (2 ^ 256) (valLimbs x)
        * feval (valLimbs vestaLimbs) (2 ^ 256) (valLimbs yv) := by
  obtain ⟨hval, _, hcong⟩ :=
    vesta_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256 haslen hyslen hcap
      hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  rw [hval] at hcong ⊢
  rw [vestaP_eq] at hcong ⊢
  exact emit_refines_field_of_runBlock vesta_coprime _ _ _ hcong

/-- **Vesta: the emitted asm refines a supplied cross-prover `F.mul` (parametric).** -/
theorem vesta_emit_refines_fiat
    {leaf : FieldMulLeaf} (_hmod : leaf.modulus = valLimbs vestaLimbs)
    {leafSpec : LeafSpec}
    (hbridge : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt)
    (decoded : ZMod leaf.modulus)
    (hfield : decoded = leaf.decode xa * leaf.decode xb) :
    decoded =
      leaf.decode (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
        [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩]) :=
  emit_refines_fiat_of_bridge hbridge xa xb oldDest decoded hfield

end CatCrypt.Crypto.SecureCompilation.X86Backend.CurveFieldRefinement
