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
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA

@[expose] public section

set_option autoImplicit false

/-!
# fiat-crypto WordByWordMontgomery field-multiply leaf over `Fp_{BLS12-381}`

This module declares the word-by-word-Montgomery (CIOS) field multiply for
the BLS12-381 base prime
`p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`
(381 bits) as a leaf for CatCrypt's verified front, following the extCall
pattern (`Jasmin.LowCT` `RCall`) and the field-multiply leaf shape of
`Vale/P384FieldMul.lean` (both 6×u64 = 48-byte).

The base-field element is modelled as `ZMod p` and the leaf denotation is
the Montgomery product `x · y · R⁻¹`, `R = 2^384`. That value is grounded
in the proven emitted 6-limb Montgomery multiply
`Curve6LimbTierA.bls12381_emit_montmul_runBlock`: the `runBlock` of the
emitted schoolbook product is `valLimbs x · valLimbs y`, and its
`montgomeryReduce` at `R = 2^384` satisfies
`redc · 2^384 ≡ valLimbs x · valLimbs y (mod p)`. Cast to `ZMod p` this is
exactly `Bls12381_fmul_denote`. The reduction law is the prime-parametric
`Number.montgomeryReduce_correct`, so the value holds at the BLS12-381 base
prime with the pinned modulus `Curve6LimbTierA.bls12381Limbs`.

## Leaf C signature (Rust `extern "C"` shape)

```c
extern void bls12_381_fp_mul(uint64_t out[6], const uint64_t x[6], const uint64_t y[6]);
```

That is: `out = x · y · R⁻¹ mod p_{BLS12-381}`, `R = 2^384`, over
Montgomery-form 6×u64 saturated LE buffers (48 bytes per operand).

## Provenance and link-time trust

* **fiat-rust source**: `fiat_bls12_381_mul`, fiat-crypto codegen
  (`word_by_word_montgomery --lang Rust bls12_381 64 '<p>'`), C export
  `bls12_381_fp_mul`. (AUCurves' `bls12-381-safe-rust` routes `fp_mul`
  through a Bedrock2 tower; that is a separate implementation, not this
  leaf's reference.)
* **Symbol identity at link time**: the C symbol our jasmin/C-bridge calls
  is the fiat-crypto-generated `fiat_bls12_381_mul`. Standard C-linker trust.
-/

namespace CatCrypt.Crypto.Vale.Bls12381FieldMul

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA

/-! ## §1. Surface type and modulus

The BLS12-381 base prime as the little-endian `valLimbs` of the pinned
six-limb modulus `bls12381Limbs`, and the base field `ZMod p`. -/

/-- The BLS12-381 base prime, as the `valLimbs` of the pinned six-limb
    modulus `bls12381Limbs`. -/
def bls12381Prime : Nat := valLimbs bls12381Limbs

/-- `0 < bls12381Prime`. -/
theorem bls12381Prime_pos : 0 < bls12381Prime := by
  rw [bls12381Prime, show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl,
    valLimbs_cons]
  have : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
  omega

instance : NeZero bls12381Prime := ⟨by have := bls12381Prime_pos; omega⟩

/-- A BLS12-381 `Fp` field element (Montgomery-form residue, 6×u64 = 48
    bytes on the wire). -/
abbrev Bls12381Fp : Type := ZMod bls12381Prime

/-! ## §2. Montgomery radix and the leaf denotation -/

/-- The Montgomery radix `R = 2^384` as an element of `ZMod bls12381Prime`. -/
noncomputable def bls12381MontR : Bls12381Fp := ((2 ^ 384 : ℕ) : ZMod bls12381Prime)

/-- `R = 2^384` is a unit in `ZMod bls12381Prime` (it is coprime to the odd
    modulus `bls12381Prime`). -/
theorem bls12381MontR_isUnit : IsUnit bls12381MontR := by
  have hodd : ¬ (2 ∣ bls12381Prime) := by
    rw [bls12381Prime, show bls12381Limbs = (0xb9feffffffffaaab : BitVec 64) :: _ from rfl,
      valLimbs_cons]
    have : (0xb9feffffffffaaab : BitVec 64).toNat = 13402431016077863595 := by decide
    omega
  have h2 : Nat.Coprime 2 bls12381Prime := (Nat.prime_two.coprime_iff_not_dvd).mpr hodd
  have hpow : Nat.Coprime (2 ^ 384) bls12381Prime := h2.pow_left 384
  exact (ZMod.isUnit_iff_coprime (2 ^ 384) bls12381Prime).mpr hpow

/-- **Leaf denotation**: the BLS12-381 Montgomery product `x · y · R⁻¹`,
    `R = 2^384`, on Montgomery-form residues. Grounded in the proven
    emitted 6-limb Montgomery multiply by
    `bls12381_fmul_denote_grounds_runBlock`. -/
noncomputable def Bls12381_fmul_denote (x y : Bls12381Fp) : Bls12381Fp := x * y * bls12381MontR⁻¹

/-- The leaf denotation unfolds to the Montgomery product `x · y · R⁻¹`. -/
theorem bls12381_fmul_denote_spec (x y : Bls12381Fp) :
    Bls12381_fmul_denote x y = x * y * bls12381MontR⁻¹ := rfl

/-! ## §2b. Grounding in the proven emitted 6-limb multiply

`bls12381_emit_montmul_runBlock` (`Curve6LimbTierA`) proves, for reduced
6-limb inputs and the full-radix Montgomery constant `Nprime384`, that the
emitted schoolbook product's `runBlock` value is `valLimbs x · valLimbs y`
and that its `montgomeryReduce` `redc` satisfies
`redc · 2^384 ≡ valLimbs x · valLimbs y (mod p)`. Cast to `ZMod p`, `redc`
is `Bls12381_fmul_denote`. -/

/-- The `montgomeryReduce` value of the emitted 6-limb product block — the
    proven `runBlock` value of `Curve6LimbTierA.bls12381_emit_montmul_runBlock`
    — casts in `ZMod bls12381Prime` to the leaf denotation
    `Bls12381_fmul_denote`. -/
theorem bls12381_fmul_denote_grounds_runBlock
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
    ((Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
        (runBlockProductValue accs as ys hi lo s) : ℕ) : Bls12381Fp)
      = Bls12381_fmul_denote (valLimbs x : Bls12381Fp) (valLimbs yv : Bls12381Fp) := by
  obtain ⟨_, _, hcong⟩ := bls12381_emit_montmul_runBlock accs as ys x yv hi lo s Nprime384
    haslen hyslen hcap hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime
  set redc := Number.montgomeryReduce (valLimbs bls12381Limbs) (2 ^ 384) Nprime384
    (runBlockProductValue accs as ys hi lo s)
  have hcast : (redc : Bls12381Fp) * bls12381MontR
      = (valLimbs x : Bls12381Fp) * (valLimbs yv : Bls12381Fp) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcong
    rw [Nat.cast_mul, Nat.cast_mul] at h
    exact h
  have hRR : bls12381MontR * bls12381MontR⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ bls12381MontR_isUnit
  show (redc : Bls12381Fp)
      = (valLimbs x : Bls12381Fp) * (valLimbs yv : Bls12381Fp) * bls12381MontR⁻¹
  calc (redc : Bls12381Fp)
      = (redc : Bls12381Fp) * (bls12381MontR * bls12381MontR⁻¹) := by rw [hRR, mul_one]
    _ = (redc : Bls12381Fp) * bls12381MontR * bls12381MontR⁻¹ := by ring
    _ = (valLimbs x : Bls12381Fp) * (valLimbs yv : Bls12381Fp) * bls12381MontR⁻¹ := by rw [hcast]

/-! ## §3. `@[rust_cmd_pattern]` registration -/

/-- Register `Bls12381_fmul_denote` → leaf `bls12_381_fp_mul` (the C symbol
    exporting `fiat_bls12_381_mul`). Argument shape `2 × TBytes 48`
    (two BLS12-381 Fp elements). -/
@[rust_cmd_pattern]
def bls12381FmulPattern : LowCTPattern where
  name      := "bls12_381_fp_mul"
  fnHead    := ``Bls12381_fmul_denote
  arity     := 2
  towerType := .TBytes 48   -- 48-byte BLS12-381 Fp Montgomery buffer (6×u64)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a BLS12-381 Fp element (`TBytes 48`, 6×u64 saturated
    Montgomery form). -/
def bls12381FpTowerType : TowerType := .TBytes 48

/-! ## §5. `LeafSig` entry

The fiat-crypto leaf is non-aliasing: `out`, `x`, `y` are distinct buffers
in the Rust signature. `destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `bls12_381_fp_mul`: no aliasing permitted. -/
def bls12381FmulLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "bls12_381_fp_mul"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

The body is the single cross-prover-cited leaf call. -/

/-- One BLS12-381 `Fp` Montgomery-multiply invocation. -/
noncomputable def bls12381FmulLean (x y : Bls12381Fp) : Bls12381Fp :=
  Bls12381_fmul_denote x y

/-! ## §7. Hand-built `LowCT` body (front-end input)

The front-end `reifyLowCT%` macro reads `knownOps` only, so we hand-build
the single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `bls12381FmulLean`. Shape:
    `RSeq RSkip (RCall "bls12_381_fp_mul" __result [x, y])`. -/
def bls12381FmulBody : LowCT :=
  let x_l      := loc "x"        bls12381FpTowerType
  let y_l      := loc "y"        bls12381FpTowerType
  let result_l := loc "__result" bls12381FpTowerType
  .RSeq .RSkip
    (.RCall "bls12_381_fp_mul" result_l [x_l, y_l])

/-- `ReifiedFunc` bundle for the fiat-crypto BLS12-381 field-multiply leaf. -/
def bls12381FmulReified : ReifiedFunc :=
  { args    := [("x", bls12381FpTowerType), ("y", bls12381FpTowerType)]
    body    := bls12381FmulBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval bls12381FmulReified.args.map Prod.fst    -- [x, y]
#eval bls12381FmulReified.args.length          -- 2
#eval bls12381FmulReified.retName              -- __result

end CatCrypt.Crypto.Vale.Bls12381FieldMul
