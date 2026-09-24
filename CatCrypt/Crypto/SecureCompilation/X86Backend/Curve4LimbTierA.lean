/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-!
# Tier-A Montgomery multiply over `runBlock` for the 4-limb curves

`SchoolbookProductRunBlock.lean` proves the
`runBlock(emitted product block) = valLimbs x · valLimbs y`
(`emitProductBlock_runBlock_value`, axiom-clean, general `N`) and feeds it to
the proven prime-parametric Montgomery reduction
(`Number.montgomeryMul`/`montgomeryReduce` at the full radix `R = 2^256`) to
obtain the SM2 Tier-A headline `sm2_emit_montmul_runBlock_full(4)`:
`runBlock(emitted) = SM2 mont-mul spec`.

This file *instantiates* that exact template for the remaining 4-limb curves:

* **secp256k1** — `p = 2^256 − (2^32 + 977)` (the limbs already live in
  `Cios4LimbProven.secp256k1Limbs`; reused here);
* **P256 / secp256r1** — `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`;
* **BN254** base field — `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
  (`= 0x30644e72…d87cfd47`).

For each curve we give

1. `<curve>Limbs` + `<curve>Limbs_value` — the canonical little-endian 4-limb
   representation of the modulus, pinned by `native_decide` to the
   prime (secp256k1 reuses the existing `Cios4LimbProven` definition);
2. `<curve>_emit_montmul_runBlock(4)` — the curve analogue of
   `sm2_emit_montmul_runBlock_full(4)`: with reduced 4-limb inputs and the
   curve's full-radix Montgomery constant `Nprime256` (hypothesis
   `(p · Nprime256) % 2^256 = 2^256 − 1`), the `runBlock` product value of the
   emitted block is `valLimbs x · valLimbs y` and its
   `montgomeryReduce`/`montgomeryMul` at `R = 2^256` lands `< 2·p` and
   `· 2^256 ≡ valLimbs x · valLimbs y (mod p)`. This is
   `runBlock(emitted) = <curve> mont-mul spec` — Tier A for that curve.

## Scope

These are **flag-resetting** Tier-A instantiations of the SM2 template (each
emitted schoolbook row re-enters `CF = OF = 0`). The persistent-flag / full-ILP
ADX schedule (no per-column reset, marginally faster) is a separate
*perf-equivalence* increment; it does not change the value spec proven here.

The full-radix Montgomery constant `Nprime256` is threaded as a parameter with
the hypothesis `(p · Nprime256) % 2^256 = 2^256 − 1` (exactly as in the SM2
headline `sm2_emit_montmul_runBlock_full`); the reduction law is the
prime-parametric `Number.montgomeryMul_correct` instantiated at each curve's
canonical prime. Only the modulus + reduced-input bounds are curve-specific, so
the same proof skeleton closes all three. The only `native_decide` step per
curve is the constant pin `<curve>Limbs_value` against its prime.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-! ## 1. secp256k1

The limbs already exist as `Cios4LimbProven.secp256k1Limbs`
(`p = 2^256 − (2^32 + 977)`, `secp256k1Limbs_value`); reused directly. -/

/-- **secp256k1 full Montgomery-multiply over `runBlock` (Tier A).** With reduced
    4-limb inputs (`valLimbs x, valLimbs y < p_secp256k1`), a cleared accumulator
    file, the `ProdFresh` register layout, matching lengths, and the full-radix
    secp256k1 Montgomery constant `Nprime256` (`p · Nprime256 ≡ −1 mod 2^256`):

    * the emitted product block's `runBlock` value is exactly
      `valLimbs x · valLimbs y` (`emitProductBlock_runBlock_value`); and
    * `montgomeryReduce p_secp256k1 (2^256) Nprime256` of that `runBlock`
      value (= `montgomeryMul …`) lies in `[0, 2·p)` and
      `· 2^256 ≡ valLimbs x · valLimbs y (mod p_secp256k1)`.

    The full `runBlock(emitted) = secp256k1 mont-mul spec` — Tier A. The exact
    secp256k1 instance of `sm2_emit_montmul_runBlock_full`. -/
theorem secp256k1_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs secp256k1Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs secp256k1Limbs ∧
    (Number.montgomeryReduce (valLimbs secp256k1Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs secp256k1Limbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs secp256k1Limbs := by rw [secp256k1Limbs_value]; norm_num
    have hNleR : valLimbs secp256k1Limbs ≤ 2 ^ 256 := by rw [secp256k1Limbs_value]; norm_num
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs secp256k1Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs secp256k1Limbs := by rw [secp256k1Limbs_value]; norm_num
    have hNleR : valLimbs secp256k1Limbs ≤ 2 ^ 256 := by rw [secp256k1Limbs_value]; norm_num
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs secp256k1Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **secp256k1 Tier-A headline, 4-limb instance.** The concrete 4-limb shape of
    `secp256k1_emit_montmul_runBlock` over `emitProductBlock4`. -/
theorem secp256k1_emit_montmul_runBlock4
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs secp256k1Limbs)
    (hy_red : valLimbs yv < valLimbs secp256k1Limbs)
    (hNprime : (valLimbs secp256k1Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs secp256k1Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))
        < 2 * valLimbs secp256k1Limbs ∧
    (Number.montgomeryReduce (valLimbs secp256k1Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs secp256k1Limbs] := by
  have := secp256k1_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock4, runBlockProductValue] using this

/-! ## 2. P256 (secp256r1)

`p256 = 2^256 − 2^224 + 2^192 + 2^96 − 1`, little-endian limbs
`0xffffffffffffffff, 0x00000000ffffffff, 0, 0xffffffff00000001`
(matching `P256FieldKernel.p256Limbs`, here as `BitVec 64`). -/

/-- The P256 base-field prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as the
    `valLimbs` of its four little-endian limbs (matching
    `P256FieldKernel.p256Limbs`). -/
def p256Limbs : List (BitVec 64) :=
  [ 0xffffffffffffffff, 0x00000000ffffffff, 0x0000000000000000, 0xffffffff00000001 ]

theorem p256Limbs_value :
    valLimbs p256Limbs = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1 := by
  native_decide

/-- **P256 full Montgomery-multiply over `runBlock` (Tier A).** As
    `secp256k1_emit_montmul_runBlock`, at the canonical P256 prime
    (`p256Limbs`). The full `runBlock(emitted) = P256 mont-mul spec`. -/
theorem p256_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs p256Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs p256Limbs ∧
    (Number.montgomeryReduce (valLimbs p256Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs p256Limbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs p256Limbs := by rw [p256Limbs_value]; norm_num
    have hNleR : valLimbs p256Limbs ≤ 2 ^ 256 := by rw [p256Limbs_value]; norm_num
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs p256Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs p256Limbs := by rw [p256Limbs_value]; norm_num
    have hNleR : valLimbs p256Limbs ≤ 2 ^ 256 := by rw [p256Limbs_value]; norm_num
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs p256Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **P256 Tier-A headline, 4-limb instance.** The concrete 4-limb shape of
    `p256_emit_montmul_runBlock` over `emitProductBlock4`. -/
theorem p256_emit_montmul_runBlock4
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs p256Limbs)
    (hy_red : valLimbs yv < valLimbs p256Limbs)
    (hNprime : (valLimbs p256Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs p256Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))
        < 2 * valLimbs p256Limbs ∧
    (Number.montgomeryReduce (valLimbs p256Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs p256Limbs] := by
  have := p256_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock4, runBlockProductValue] using this

/-! ## 3. BN254 base field

`p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
`= 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`,
little-endian limbs
`0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029`. -/

/-- The BN254 base-field prime
    `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`,
    as the `valLimbs` of its four little-endian limbs. -/
def bn254Limbs : List (BitVec 64) :=
  [ 0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029 ]

theorem bn254Limbs_value :
    valLimbs bn254Limbs
      = 21888242871839275222246405745257275088696311157297823662689037894645226208583 := by
  native_decide

/-- **BN254 base-field full Montgomery-multiply over `runBlock` (Tier A).** As
    `secp256k1_emit_montmul_runBlock`, at the canonical BN254 base-field prime
    (`bn254Limbs`). The full `runBlock(emitted) = BN254 mont-mul spec`. -/
theorem bn254_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs bn254Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs bn254Limbs ∧
    (Number.montgomeryReduce (valLimbs bn254Limbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs bn254Limbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs bn254Limbs := by rw [bn254Limbs_value]; norm_num
    have hNleR : valLimbs bn254Limbs ≤ 2 ^ 256 := by rw [bn254Limbs_value]; norm_num
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs bn254Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs bn254Limbs := by rw [bn254Limbs_value]; norm_num
    have hNleR : valLimbs bn254Limbs ≤ 2 ^ 256 := by rw [bn254Limbs_value]; norm_num
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs bn254Limbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **BN254 Tier-A headline, 4-limb instance.** The concrete 4-limb shape of
    `bn254_emit_montmul_runBlock` over `emitProductBlock4`. -/
theorem bn254_emit_montmul_runBlock4
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs bn254Limbs)
    (hy_red : valLimbs yv < valLimbs bn254Limbs)
    (hNprime : (valLimbs bn254Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs bn254Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))
        < 2 * valLimbs bn254Limbs ∧
    (Number.montgomeryReduce (valLimbs bn254Limbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs bn254Limbs] := by
  have := bn254_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock4, runBlockProductValue] using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
