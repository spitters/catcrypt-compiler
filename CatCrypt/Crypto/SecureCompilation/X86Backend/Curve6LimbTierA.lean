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
# Tier-A Montgomery multiply over `runBlock` for the 6-limb curves

This file instantiates the proven Tier-A template — the
`runBlock(emitted product block) = valLimbs x · valLimbs y` over a real emitted
`List (JInstr 64)` (`SchoolbookProductRunBlock.emitProductBlock_runBlock_value`,
axiom-clean, *general `N`*), fed to the prime-parametric Montgomery reduction
(`Number.montgomeryMul`/`montgomeryReduce`, `Number.montgomeryMul_correct`) — at
the **6-limb radix `R = 2^384`** for the two 6-limb curves:

* **P384 / secp384r1** — `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`;
* **BLS12-381** base field — the standard 381-bit BLS prime
  `p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624`
  `1eabfffeb153ffffb9feffffffffaaab`.

Both `emitProductBlock_runBlock_value` (the multiply over `runBlock`) and
`Number.montgomeryMul_correct` (the reduction law) are radix-parametric: the
radix `R` is a free `Nat` parameter constrained only by `0 < R`, `N ≤ R`, and
`(N · Nprime) % R = R − 1`. So `R = 2^384` works identically to the 4-limb
`R = 2^256` — no new multiply proof and no new reduction proof is needed; only
the modulus and the reduced-input bounds are curve-specific. The single
`native_decide` step per curve is the constant pin `<curve>Limbs_value` against
its prime; the `R = 2^384` Montgomery path is `native_decide`-free
(exactly as at `R = 2^256`).

For each curve we give

1. `<curve>Limbs` + `<curve>Limbs_value` — the canonical little-endian 6-limb
   representation of the modulus, pinned by `native_decide` to the prime;
2. `<curve>_emit_montmul_runBlock` — the 6-limb analogue of the SM2/4-limb
   headline `sm2_emit_montmul_runBlock_full`: with reduced 6-limb inputs and the
   curve's full-radix Montgomery constant `Nprime384` (hypothesis
   `(p · Nprime384) % 2^384 = 2^384 − 1`), the `runBlock` product value of the
   emitted block is `valLimbs x · valLimbs y` and its
   `montgomeryReduce`/`montgomeryMul` at `R = 2^384` lands `< 2·p` and
   `· 2^384 ≡ valLimbs x · valLimbs y (mod p)`. This is
   `runBlock(emitted) = <curve> mont-mul spec` — Tier A for that curve;
3. `<curve>_emit_montmul_runBlock6` — the concrete 6-limb shape of (2) over
   `emitProductBlock6` (6 `x`-limbs, 6 `y`-limbs, a 12-word accumulator file).

## Scope

These are **flag-resetting** Tier-A instantiations of the same template (each
emitted schoolbook row re-enters `CF = OF = 0`). The persistent-flag / full-ILP
ADX schedule (no per-column reset, marginally faster) is a separate
*perf-equivalence* increment; it does not change the value spec proven here.

The full-radix Montgomery constant `Nprime384` is threaded as a parameter with
the hypothesis `(p · Nprime384) % 2^384 = 2^384 − 1` (exactly as `Nprime256` in
the 4-limb headlines); the reduction law is the prime-parametric
`Number.montgomeryMul_correct` instantiated at each curve's canonical prime.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-! ## A. Structural `valLimbs` bound at 6 limbs

The modulus facts `0 < N` and `N ≤ R = 2^384` feed
`Number.montgomeryMul_correct`. Rather than expand the 384-bit prime to a
decimal literal (`norm_num` will not evaluate `2^384`), bound `valLimbs`
structurally: each `BitVec 64` limb is `< 2^64`, so a list of `n` limbs has
`valLimbs < (2^64)^n`, and `(2^64)^6 = 2^384`. -/

/-- `valLimbs l < (2^64)^|l|`: the little-endian value of a `BitVec 64` limb
    list is strictly below the radix to the limb count. -/
theorem valLimbs_lt_pow (l : List (BitVec 64)) : valLimbs l < (2 ^ 64) ^ l.length := by
  induction l with
  | nil => simp [valLimbs_nil]
  | cons w ws ih =>
    rw [valLimbs_cons, List.length_cons, pow_succ]
    have hw : (w.toNat) < 2 ^ 64 := w.isLt
    calc w.toNat + 2 ^ 64 * valLimbs ws
        < 2 ^ 64 + 2 ^ 64 * valLimbs ws := by omega
      _ ≤ 2 ^ 64 + 2 ^ 64 * ((2 ^ 64) ^ ws.length - 1) := by
            have : valLimbs ws ≤ (2 ^ 64) ^ ws.length - 1 := by omega
            gcongr
      _ = (2 ^ 64) ^ ws.length * 2 ^ 64 := by
            have hpos : 0 < (2 ^ 64) ^ ws.length := by positivity
            cases h : (2 ^ 64) ^ ws.length with
            | zero => omega
            | succ m => ring_nf; omega

/-- A 6-limb list has `valLimbs ≤ 2^384` (the `N ≤ R` hypothesis at `R = 2^384`). -/
theorem valLimbs_le_pow384 (l : List (BitVec 64)) (h : l.length = 6) :
    valLimbs l ≤ 2 ^ 384 := by
  have hlt := valLimbs_lt_pow l
  rw [h] at hlt
  have h2 : ((2 : ℕ) ^ 64) ^ 6 = 2 ^ 384 := by rw [← pow_mul]
  omega

/-! ## 0. The 6-limb (384×384) emitted product

`emitProductBlock` is general over the limb count; `emitProductBlock6` names the
6-limb instance: 12 accumulator words (`accs`), 6 `x`-limb sources (`as`), 6
`y`-limb scalars (`ys`), scratch `hi`/`lo`. A thin alias of `emitProductBlock`,
the 6-limb analogue of `emitProductBlock4`. The general-`N`
`emitProductBlock_runBlock_value` applies directly at this arity. -/

/-- The 6-limb (384×384) emitted schoolbook product: 12 accumulator words
    (`accs`), 6 `x`-limb sources (`as`), 6 `y`-limb scalars (`ys`), scratch
    `hi`/`lo`. A thin instance of `emitProductBlock`. -/
def emitProductBlock6 (accs as ys : List String) (hi lo : String) : List (JInstr 64) :=
  emitProductBlock accs as ys hi lo

/-! ## 1. P384 (secp384r1)

`p384 = 2^384 − 2^128 − 2^96 + 2^32 − 1`, little-endian limbs
`0x00000000ffffffff, 0xffffffff00000000, 0xfffffffffffffffe,
 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff`
(matching `P384FieldKernel.p384Limbs`, here as `BitVec 64`). -/

/-- The P384 base-field prime `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`, as the
    `valLimbs` of its six little-endian limbs (matching
    `P384FieldKernel.p384Limbs`). -/
def p384Limbs : List (BitVec 64) :=
  [ 0x00000000ffffffff, 0xffffffff00000000, 0xfffffffffffffffe
  , 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff ]

theorem p384Limbs_value :
    valLimbs p384Limbs = 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1 := by
  native_decide

/-- **P384 full Montgomery-multiply over `runBlock` (Tier A).** With reduced
    6-limb inputs (`valLimbs x, valLimbs y < p384`), a cleared accumulator file,
    the `ProdFresh` register layout, matching lengths, and the full-radix P384
    Montgomery constant `Nprime384` (`p384 · Nprime384 ≡ −1 mod 2^384`):

    * the emitted product block's `runBlock` value is exactly
      `valLimbs x · valLimbs y` (`emitProductBlock_runBlock_value` at 6 limbs); and
    * `montgomeryReduce p384 (2^384) Nprime384` of that `runBlock` value
      (= `montgomeryMul …`) lies in `[0, 2·p384)` and
      `· 2^384 ≡ valLimbs x · valLimbs y (mod p384)`.

    The full `runBlock(emitted) = P384 mont-mul spec` — Tier A. The 6-limb,
    `R = 2^384` instance of `sm2_emit_montmul_runBlock_full`. -/
theorem p384_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs p384Limbs ∧
    (Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 384
      ≡ valLimbs x * valLimbs yv [MOD valLimbs p384Limbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs p384Limbs := by
      rw [show p384Limbs = (0x00000000ffffffff : BitVec 64) :: _ from rfl, valLimbs_cons]
      have : (0x00000000ffffffff : BitVec 64).toNat = 4294967295 := by decide
      omega
    have hNleR : valLimbs p384Limbs ≤ 2 ^ 384 := valLimbs_le_pow384 p384Limbs rfl
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs p384Limbs) (2 ^ 384)
      Nprime384 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs p384Limbs := by
      rw [show p384Limbs = (0x00000000ffffffff : BitVec 64) :: _ from rfl, valLimbs_cons]
      have : (0x00000000ffffffff : BitVec 64).toNat = 4294967295 := by decide
      omega
    have hNleR : valLimbs p384Limbs ≤ 2 ^ 384 := valLimbs_le_pow384 p384Limbs rfl
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs p384Limbs) (2 ^ 384)
      Nprime384 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **P384 Tier-A headline, 6-limb instance.** The concrete 6-limb shape of
    `p384_emit_montmul_runBlock` over `emitProductBlock6` (6 `x`-limbs, 6
    `y`-limbs, 12-word accumulator file). -/
theorem p384_emit_montmul_runBlock6
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime384 : Nat)
    (hxlen : x.length = 6) (hylen : yv.length = 6)
    (haslen : as.length = 6) (hyslen : ys.length = 6)
    (hacclen : accs.length = 12)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs p384Limbs)
    (hy_red : valLimbs yv < valLimbs p384Limbs)
    (hNprime : (valLimbs p384Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock6 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
        (valLimbs (accs.map (runBlock s (emitProductBlock6 accs as ys hi lo)).get))
        < 2 * valLimbs p384Limbs ∧
    (Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
        (valLimbs (accs.map (runBlock s (emitProductBlock6 accs as ys hi lo)).get))) * 2 ^ 384
      ≡ valLimbs x * valLimbs yv [MOD valLimbs p384Limbs] := by
  have := p384_emit_montmul_runBlock accs as ys x yv hi lo s Nprime384
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock6, runBlockProductValue] using this

/-! ## 2. BLS12-381 base field

The standard 381-bit BLS prime
`p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624`
`1eabfffeb153ffffb9feffffffffaaab`, little-endian limbs
`0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624,
 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a`
(matching `Bls12381MontMulKernel.pLimbs`, here as `BitVec 64`). -/

/-- The BLS12-381 base-field prime
    `p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624`
    `1eabfffeb153ffffb9feffffffffaaab`, as the `valLimbs` of its six
    little-endian limbs (matching `Bls12381MontMulKernel.pLimbs`). -/
def bls12381Limbs : List (BitVec 64) :=
  [ 0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624
  , 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a ]

theorem bls12381Limbs_value :
    valLimbs bls12381Limbs
      = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab := by
  native_decide

/-- **BLS12-381 base-field full Montgomery-multiply over `runBlock` (Tier A).**
    As `p384_emit_montmul_runBlock`, at the canonical BLS12-381 base-field prime
    (`bls12381Limbs`) and `R = 2^384`. With reduced 6-limb inputs, a cleared
    accumulator file, `ProdFresh`, matching lengths, and the full-radix Montgomery
    constant `Nprime384` (`p · Nprime384 ≡ −1 mod 2^384`), the emitted product's
    `runBlock` value is `valLimbs x · valLimbs y` and its
    `montgomeryReduce`/`montgomeryMul` lands `< 2·p` with
    `· 2^384 ≡ valLimbs x · valLimbs y (mod p)`. The full
    `runBlock(emitted) = BLS12-381 mont-mul spec` — Tier A. -/
theorem bls12381_emit_montmul_runBlock
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
    runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
        (runBlockProductValue accs as ys hi lo s) < 2 * valLimbs bls12381Limbs ∧
    (Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
        (runBlockProductValue accs as ys hi lo s)) * 2 ^ 384
      ≡ valLimbs x * valLimbs yv [MOD valLimbs bls12381Limbs] := by
  have hval : runBlockProductValue accs as ys hi lo s = valLimbs x * valLimbs yv :=
    emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof
  refine ⟨hval, ?_, ?_⟩
  · have hN : 0 < valLimbs bls12381Limbs := by
      rw [show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl, valLimbs_cons]
      have : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
      omega
    have hNleR : valLimbs bls12381Limbs ≤ 2 ^ 384 := valLimbs_le_pow384 bls12381Limbs rfl
    obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct (valLimbs bls12381Limbs) (2 ^ 384)
      Nprime384 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hrange
  · have hN : 0 < valLimbs bls12381Limbs := by
      rw [show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl, valLimbs_cons]
      have : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
      omega
    have hNleR : valLimbs bls12381Limbs ≤ 2 ^ 384 := valLimbs_le_pow384 bls12381Limbs rfl
    obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct (valLimbs bls12381Limbs) (2 ^ 384)
      Nprime384 (valLimbs x) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    rw [hval]
    simpa only [Number.montgomeryMul] using hcong

/-- **BLS12-381 Tier-A headline, 6-limb instance.** The concrete 6-limb shape of
    `bls12381_emit_montmul_runBlock` over `emitProductBlock6`. -/
theorem bls12381_emit_montmul_runBlock6
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime384 : Nat)
    (hxlen : x.length = 6) (hylen : yv.length = 6)
    (haslen : as.length = 6) (hyslen : ys.length = 6)
    (hacclen : accs.length = 12)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs bls12381Limbs)
    (hy_red : valLimbs yv < valLimbs bls12381Limbs)
    (hNprime : (valLimbs bls12381Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1) :
    valLimbs (accs.map (runBlock s (emitProductBlock6 accs as ys hi lo)).get)
        = valLimbs x * valLimbs yv ∧
    Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
        (valLimbs (accs.map (runBlock s (emitProductBlock6 accs as ys hi lo)).get))
        < 2 * valLimbs bls12381Limbs ∧
    (Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
        (valLimbs (accs.map (runBlock s (emitProductBlock6 accs as ys hi lo)).get))) * 2 ^ 384
      ≡ valLimbs x * valLimbs yv [MOD valLimbs bls12381Limbs] := by
  have := bls12381_emit_montmul_runBlock accs as ys x yv hi lo s Nprime384
    (by omega) (by omega) (by omega) hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  simpa only [emitProductBlock6, runBlockProductValue] using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
