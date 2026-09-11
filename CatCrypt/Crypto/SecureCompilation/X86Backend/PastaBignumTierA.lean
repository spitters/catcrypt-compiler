/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA

/-!
# Tier-A: the Pasta curves' Montgomery multiply + the bare `bignum_mul_4_8` product

Two Tier-A completions reusing the proven 4-limb `runBlock` product template of
`SchoolbookProductRunBlock`/`Curve4LimbTierA`:

1. **Pasta (Pallas / Vesta) full Montgomery multiply over `runBlock`.** The exact
   `Curve4LimbTierA.secp256k1_emit_montmul_runBlock` template, instantiated at the
   two Pasta-cycle base-field primes:

   * **Pallas** base field `p = 2²⁵⁴ + 0x224698fc094cf91b992d30ed00000001`;
   * **Vesta** base field `q = 2²⁵⁴ + 0x224698fc0994a8dd8c46eb2100000001`.

   (Pallas and Vesta form a cycle: each one's base field is the other's scalar
   field.) The emitted schoolbook product over `runBlock`
   (`emitProductBlock_runBlock_value`, axiom-clean) is fed to the proven
   prime-parametric Montgomery reduction (`Number.montgomeryReduce`/
   `montgomeryMul` at the full radix `R = 2^256` with the curve `Nprime256`),
   giving `runBlock(emitted) = <curve> mont-mul spec`: `< 2·p` and
   `· 2^256 ≡ valLimbs x · valLimbs y (mod p)`. Tier A.

2. **`bignum_mul_4_8`: the bare 256×256→512 product over `runBlock`.** This is the
   s2n-bignum `bignum_mul_4_8` (and GMP-overlap) spec: the *full* 8-word product
   `valLimbs x · valLimbs y` with **no** Montgomery reduction step. It is a direct
   restatement of `SchoolbookProductRunBlock.emitProductBlock_runBlock_value` /
   `emitProductBlock_runBlock_mulLimbs` at four limbs — the product half of the
   curve headline, with the reduction dropped.

## The moduli are canonical (NOT fabricated)

The 4-limb little-endian moduli are pinned by `native_decide` to the genuine
Pasta primes, and match the limb constants in
`PastaFieldAddSubKernel.{pallasLimbs, vestaLimbs}` (the AUCurves
`pallas_modulus` / `vesta_modulus`):

* `pallasLimbs = [0x992d30ed00000001, 0x224698fc094cf91b, 0, 0x4000000000000000]`
  recombines to `2²⁵⁴ + 0x224698fc094cf91b992d30ed00000001`;
* `vestaLimbs  = [0x8c46eb2100000001, 0x224698fc0994a8dd, 0, 0x4000000000000000]`
  recombines to `2²⁵⁴ + 0x224698fc0994a8dd8c46eb2100000001`.

(The `PastaFieldAddSubKernel`/`PastaMontMulKernel` limbs are `List Nat`; here we
take the `BitVec 64` form required by `valLimbs`, with identical word values.)

## Scope (honest)

These are **flag-resetting** Tier-A instantiations of the proven SM2/secp256k1
template (each emitted schoolbook row re-enters `CF = OF = 0`). The persistent-flag
/ full-ILP ADX schedule is a separate *perf-equivalence* increment; it does not
change the value spec proven here. The full-radix Montgomery constant `Nprime256`
is threaded as a parameter with the hypothesis `(p · Nprime256) % 2^256 = 2^256 − 1`
(exactly as in the SM2/secp256k1 headlines). The only `native_decide` step per
curve is the constant pin `<curve>Limbs_value` against its genuine prime.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PastaBignumTierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-! ## 1. The Pasta moduli (canonical, `native_decide`-pinned) -/

/-- The Pallas base-field prime `p = 2²⁵⁴ + 0x224698fc094cf91b992d30ed00000001`,
    as the `valLimbs` of its four little-endian limbs. Identical word values to
    `PastaFieldAddSubKernel.pallasLimbs` (the AUCurves `pallas_modulus`). -/
def pallasLimbs : List (BitVec 64) :=
  [ 0x992d30ed00000001, 0x224698fc094cf91b, 0x0000000000000000, 0x4000000000000000 ]

theorem pallasLimbs_value :
    valLimbs pallasLimbs
      = 2 ^ 254 + 0x224698fc094cf91b992d30ed00000001 := by
  native_decide

/-- The Vesta base-field prime `q = 2²⁵⁴ + 0x224698fc0994a8dd8c46eb2100000001`,
    as the `valLimbs` of its four little-endian limbs. Identical word values to
    `PastaFieldAddSubKernel.vestaLimbs` (the AUCurves `vesta_modulus`). -/
def vestaLimbs : List (BitVec 64) :=
  [ 0x8c46eb2100000001, 0x224698fc0994a8dd, 0x0000000000000000, 0x4000000000000000 ]

theorem vestaLimbs_value :
    valLimbs vestaLimbs
      = 2 ^ 254 + 0x224698fc0994a8dd8c46eb2100000001 := by
  native_decide

/-! ## 2. Pallas full Montgomery-multiply over `runBlock` (Tier A) -/

/-- **Pallas full Montgomery-multiply over `runBlock` (Tier A).** With reduced
    4-limb inputs (`valLimbs x, valLimbs y < p_pallas`), a cleared accumulator
    file, the `ProdFresh` register layout, matching lengths, and the full-radix
    Pallas Montgomery constant `Nprime256` (`p · Nprime256 ≡ −1 mod 2^256`):

    * the emitted product block's `runBlock` value is exactly
      `valLimbs x · valLimbs y` (`emitProductBlock_runBlock_value`); and
    * `montgomeryReduce p_pallas (2^256) Nprime256` of that genuine `runBlock`
      value (= `montgomeryMul …`) lies in `[0, 2·p)` and
      `· 2^256 ≡ valLimbs x · valLimbs y (mod p_pallas)`.

    The full `runBlock(emitted) = Pallas mont-mul spec` — Tier A. The exact Pallas
    instance of `Curve4LimbTierA.secp256k1_emit_montmul_runBlock`. -/
theorem pallas_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs pallasLimbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs pallasLimbs ∧
    (Number.montgomeryReduce (valLimbs pallasLimbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs pallasLimbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs pallasLimbs := by rw [pallasLimbs_value]; norm_num
    have hNleR : valLimbs pallasLimbs ≤ 2 ^ 256 := by rw [pallasLimbs_value]; norm_num
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs pallasLimbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs pallasLimbs := by rw [pallasLimbs_value]; norm_num
    have hNleR : valLimbs pallasLimbs ≤ 2 ^ 256 := by rw [pallasLimbs_value]; norm_num
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs pallasLimbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **Pallas Tier-A headline, 4-limb instance.** The concrete 4-limb shape of
    `pallas_emit_montmul_runBlock` over `emitProductBlock4`. -/
theorem pallas_emit_montmul_runBlock4
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs pallasLimbs)
    (hy_red : valLimbs yv < valLimbs pallasLimbs)
    (hNprime : (valLimbs pallasLimbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs pallasLimbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))
        < 2 * valLimbs pallasLimbs ∧
    (Number.montgomeryReduce (valLimbs pallasLimbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs pallasLimbs] := by
  have := pallas_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock4, runBlockProductValue] using this

/-! ## 3. Vesta full Montgomery-multiply over `runBlock` (Tier A) -/

/-- **Vesta full Montgomery-multiply over `runBlock` (Tier A).** As
    `pallas_emit_montmul_runBlock`, at the canonical Vesta base-field prime
    (`vestaLimbs`). The full `runBlock(emitted) = Vesta mont-mul spec`. -/
theorem vesta_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs vestaLimbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs vestaLimbs ∧
    (Number.montgomeryReduce (valLimbs vestaLimbs) (2 ^ 256) Nprime256
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs vestaLimbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs vestaLimbs := by rw [vestaLimbs_value]; norm_num
    have hNleR : valLimbs vestaLimbs ≤ 2 ^ 256 := by rw [vestaLimbs_value]; norm_num
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs vestaLimbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs vestaLimbs := by rw [vestaLimbs_value]; norm_num
    have hNleR : valLimbs vestaLimbs ≤ 2 ^ 256 := by rw [vestaLimbs_value]; norm_num
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs vestaLimbs) (2 ^ 256)
      Nprime256 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **Vesta Tier-A headline, 4-limb instance.** The concrete 4-limb shape of
    `vesta_emit_montmul_runBlock` over `emitProductBlock4`. -/
theorem vesta_emit_montmul_runBlock4
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs vestaLimbs)
    (hy_red : valLimbs yv < valLimbs vestaLimbs)
    (hNprime : (valLimbs vestaLimbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs vestaLimbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))
        < 2 * valLimbs vestaLimbs ∧
    (Number.montgomeryReduce (valLimbs vestaLimbs) (2 ^ 256) Nprime256
        (valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get))) * 2 ^ 256
      ≡ valLimbs x * valLimbs yv [MOD valLimbs vestaLimbs] := by
  have := vesta_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock4, runBlockProductValue] using this

/-! ## 4. `bignum_mul_4_8`: the bare 256×256→512 product over `runBlock`

The s2n-bignum `bignum_mul_4_8(z, x, y)` (and GMP-overlap) spec is the *full*
8-word product `z = x · y`, with **no** modular reduction. This is exactly
`emitProductBlock_runBlock_value` at four limbs / 8 accumulator words — the
product half of the curve headlines above, with the Montgomery reduction step
dropped. No new proof obligation: the bare product was already the genuine
`runBlock(emitted) = valLimbs x · valLimbs y` from `SchoolbookProductRunBlock`. -/

/-- **`bignum_mul_4_8` over `runBlock` (Tier A).** The emitted 4-limb (256×256)
    schoolbook product (`emitProductBlock4`, 4 `x`-limbs, 4 `y`-limbs, 8-word
    accumulator file), starting from a cleared accumulator file and the
    `ProdFresh` register layout with both carry flags clear, leaves the
    accumulator registers holding the full 512-bit product `valLimbs x · valLimbs y`,
    read out over `runBlock`. This is the s2n-bignum `bignum_mul_4_8` / GMP-overlap
    spec — the *bare* 256×256→512 product, no reduction. A direct restatement of
    `SchoolbookProductRunBlock.emitProductBlock_runBlock_value` at four limbs. -/
theorem bignum_mul_4_8_runBlock
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
      = valLimbs x * valLimbs yv := by
  have := emitProductBlock_runBlock_value accs as ys x yv hi lo s
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof
  simpa only [emitProductBlock4, runBlockProductValue] using this

/-- **`bignum_mul_4_8` over `runBlock`, recombined to `mulLimbs` (Tier A).** The
    same emitted 4-limb product, stated against the proven `Cios4LimbProven`
    schoolbook `mulLimbs x yv` (the canonical limb-product), via
    `mulLimbs_reconstruct`. Direct from
    `SchoolbookProductRunBlock.emitProductBlock_runBlock_mulLimbs`. -/
theorem bignum_mul_4_8_runBlock_mulLimbs
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (hxlen : x.length = 4) (hylen : yv.length = 4)
    (haslen : as.length = 4) (hyslen : ys.length = 4)
    (hacclen : accs.length = 8)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    valLimbs (accs.map (runBlock s (emitProductBlock4 accs as ys hi lo)).get)
      = valLimbs (mulLimbs x yv) := by
  have hyne : yv ≠ [] := by
    intro h; rw [h] at hylen; simp at hylen
  have := emitProductBlock_runBlock_mulLimbs accs as ys x yv hi lo s
    (by omega) (by omega) (by omega) hfresh hx hy hyne hacc0 hcf hof
  simpa only [emitProductBlock4, runBlockProductValue] using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.PastaBignumTierA
