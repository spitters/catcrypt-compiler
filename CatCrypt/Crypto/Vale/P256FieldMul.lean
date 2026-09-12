/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
public meta import CatCrypt.Crypto.Number.MontgomeryReduction
public import CatCrypt.Crypto.Number.MontgomeryReduction

@[expose] public section

set_option autoImplicit false

/-!
# fiat-crypto WordByWordMontgomery field-multiply leaf over `Fp_{P-256}`

This module supplies the fiat-crypto synthesized word-by-word-Montgomery
(CIOS) field multiply for the NIST P-256 base prime
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as a leaf for CatCrypt's verified
front (the extCall pattern `Jasmin.LowCT` `RCall`, the field-multiply leaf
shape of `Vale/BN254.lean`).

`Pairing/P256GroupEmit.lean` routes the P-256 point-add field leaves to the
fiat-crypto `fiat_p256_mul` / `fiat_p256_sub` / `fiat_p256_add` names, and
`SecureCompilation/AUCurvesImport/FieldLeafBridge.lean` records the P-256 WBW
mul in its §0 catalog. This module states the field-multiply VALUE as
`x · y · R⁻¹ mod p` (`R = 2^256`) and grounds it in the proven emitted
4-limb Montgomery multiply of
`SecureCompilation/X86Backend/Curve4LimbTierA.lean`
(`p256_emit_montmul_runBlock`).

## Representation

A P-256 `Fp` element is a 32-byte value (4×u64 saturated little-endian,
Montgomery form); its `Nat` value is the little-endian `valLimbs` of that
buffer, in `[0, 2^256)`. `P256Fp` is that `Nat` value; the multiply is
`Number.montgomeryReduce` at the full radix `R = 2^256` with the P-256
Montgomery constant.

## Value grounding

* `P256_fmul_denote_spec`: on reduced inputs the leaf computes the Montgomery
  product — `denote x y < 2·p` and `(denote x y) · 2^256 ≡ x · y (mod p)`,
  i.e. `x · y · R⁻¹ mod p`, the conclusion of `Number.montgomeryMul_correct`
  at the P-256 prime.
* `P256_fmul_denote_runBlock`: the leaf value on limb-valued inputs equals
  `Number.montgomeryReduce` of the `runBlock` value of the emitted
  256×256→512 product block, via
  `Curve4LimbTierA.p256_emit_montmul_runBlock`. The trust delta is that
  emit proof and `Number.montgomeryMul_correct` — the reduction-correctness
  core of fiat-crypto's `WordByWordMontgomery.mulmod_correct` at the P-256
  prime — not a standalone value axiom.

## Leaf C signature

```c
extern void p256_fp_mul(uint64_t out[4], const uint64_t x[4], const uint64_t y[4]);
```

That is: `out = x · y · R⁻¹ mod p_{P-256}`, `R = 2^256`, over
Montgomery-form 4×u64 saturated LE buffers (32 bytes per operand). At link
time the C symbol binds to the fiat-crypto-generated `fiat_p256_mul` (via
`p256_fp_mul` in the `p256-safe-rust` staticlib); this is standard C-linker
trust.
-/

namespace CatCrypt.Crypto.Vale.P256FieldMul

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## §1. Surface type and P-256 constants -/

/-- A NIST P-256 `Fp` element: the little-endian `Nat` value of its
    Montgomery-form 4×u64 saturated buffer, in `[0, 2^256)`. -/
abbrev P256Fp : Type := Nat

/-- The P-256 base-field prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as the
    `valLimbs` of the canonical little-endian limbs used by the emitted
    Montgomery multiply. -/
def p256Prime : Nat :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven.valLimbs
    CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA.p256Limbs

/-- The full-radix P-256 Montgomery constant: the unique `N' < 2^256` with
    `p · N' ≡ −1 (mod 2^256)`. -/
def p256Nprime256 : Nat :=
  115792089210356248768974548684794254293921932838497980611635986753331132366849

/-- The full-radix Montgomery-constant pin `p · N' ≡ −1 (mod 2^256)`. Closed by
    kernel evaluation (GMP-accelerated `Nat` multiply/mod), so this module carries
    no `native_decide`. -/
theorem p256Nprime256_pin :
    (p256Prime * p256Nprime256) % 2 ^ 256 = 2 ^ 256 - 1 := by
  decide

/-! ## §2. The leaf denotation (grounded, no value axiom) -/

/-- **Denotation**: the fiat-crypto `fiat_p256_mul` leaf computes the P-256
    base-field Montgomery multiplication `out = (x · y · R⁻¹) mod p`,
    `R = 2^256`. The value is `Number.montgomeryReduce` of the product `x · y`
    at the full radix. -/
def P256_fmul_denote (x y : P256Fp) : P256Fp :=
  CatCrypt.Crypto.Number.montgomeryReduce p256Prime (2 ^ 256) p256Nprime256 (x * y)

/-- **Value spec**: on reduced inputs (`x, y < p`) the leaf computes the
    Montgomery product — it lies in `[0, 2·p)` and
    `(denote x y) · 2^256 ≡ x · y (mod p)`, i.e. `x · y · R⁻¹ mod p`. The
    conclusion of `Number.montgomeryMul_correct` at the P-256 prime, the
    reduction-correctness core of fiat-crypto's
    `WordByWordMontgomery.mulmod_correct`. -/
theorem P256_fmul_denote_spec (x y : P256Fp) (hx : x < p256Prime) (hy : y < p256Prime) :
    P256_fmul_denote x y < 2 * p256Prime ∧
    (P256_fmul_denote x y) * 2 ^ 256 ≡ x * y [MOD p256Prime] := by
  have hN : 0 < p256Prime := by
    rw [p256Prime, CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA.p256Limbs_value]
    norm_num
  have hNleR : p256Prime ≤ 2 ^ 256 := by
    rw [p256Prime, CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA.p256Limbs_value]
    norm_num
  have hmm := CatCrypt.Crypto.Number.montgomeryMul_correct p256Prime (2 ^ 256) p256Nprime256
    x y hN (by positivity) hNleR p256Nprime256_pin hx hy
  simpa only [P256_fmul_denote, CatCrypt.Crypto.Number.montgomeryMul] using hmm

/-! ## §3. Bridge to the proven emitted `runBlock` value -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-- **Emit bridge**: on limb-valued inputs meeting the emitted product block's
    entry conditions, the leaf value equals `Number.montgomeryReduce` of the
    `runBlock` value of the emitted 256×256→512 product block. That
    `runBlock` product value is `valLimbs x · valLimbs y`
    (`Curve4LimbTierA.p256_emit_montmul_runBlock`), so the leaf denotes the
    Montgomery reduction of exactly what the emitted machine code computes. -/
theorem P256_fmul_denote_runBlock
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x <
      valLimbs CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA.p256Limbs)
    (hy_red : valLimbs yv <
      valLimbs CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA.p256Limbs) :
    P256_fmul_denote (valLimbs x) (valLimbs yv)
      = CatCrypt.Crypto.Number.montgomeryReduce p256Prime (2 ^ 256) p256Nprime256
          (runBlockProductValue accs as ys hi lo s) := by
  have h :=
    (CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA.p256_emit_montmul_runBlock
      accs as ys x yv hi lo s p256Nprime256 haslen hyslen hcap hfresh hx hy hacc0 hcf hof
      hx_red hy_red p256Nprime256_pin).1
  simp only [P256_fmul_denote, p256Prime, h]

/-! ## §4. `@[rust_cmd_pattern]` registration -/

/-- Register `P256_fmul_denote` → leaf `p256_fp_mul` (the C symbol exporting
    `fiat_p256_mul`). -/
@[rust_cmd_pattern]
def p256FmulPattern : LowCTPattern where
  name      := "p256_fp_mul"
  fnHead    := ``P256_fmul_denote
  arity     := 2
  towerType := .TBytes 32   -- 32-byte P-256 Fp Montgomery buffer (4×u64)

/-! ## §5. Tower-type abbreviation -/

/-- Tower type of a NIST P-256 Fp element (`TBytes 32`, 4×u64 saturated
    Montgomery form). -/
def p256FpTowerType : TowerType := .TBytes 32

/-! ## §6. `LeafSig` entry -/

/-- Per-leaf signature for `p256_fp_mul`: no aliasing permitted (out / x / y
    distinct in the Rust signature). -/
def p256FmulLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "p256_fp_mul"
  destAliasOk := []

/-! ## §7. Pure-Lean wrapper -/

/-- One NIST P-256 `Fp` Montgomery-multiply invocation. -/
def p256FmulLean (x y : P256Fp) : P256Fp :=
  P256_fmul_denote x y

/-! ## §8. Hand-built `LowCT` body (front-end input) -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `p256FmulLean`. Shape:
    `RSeq RSkip (RCall "p256_fp_mul" __result [x, y])`. -/
def p256FmulBody : LowCT :=
  let x_l      := loc "x"        p256FpTowerType
  let y_l      := loc "y"        p256FpTowerType
  let result_l := loc "__result" p256FpTowerType
  .RSeq .RSkip
    (.RCall "p256_fp_mul" result_l [x_l, y_l])

/-- `ReifiedFunc` bundle for the fiat-crypto P-256 field-multiply leaf. -/
def p256FmulReified : ReifiedFunc :=
  { args    := [("x", p256FpTowerType), ("y", p256FpTowerType)]
    body    := p256FmulBody
    retName := "__result" }

/-! ## §9. Inspection -/

#eval p256FmulReified.args.map Prod.fst     -- [x, y]
#eval p256FmulReified.args.length           -- 2
#eval p256FmulReified.retName               -- __result

end CatCrypt.Crypto.Vale.P256FieldMul
