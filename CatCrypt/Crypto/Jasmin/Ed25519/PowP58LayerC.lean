/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Ed25519.PowP58Algo
import CatCrypt.Crypto.Jasmin.BignumHoare.Sqr4Algebra
import Mathlib.Data.ZMod.Basic

/-!
# Layer C: `Fp25519 ↔ Nat` bridge for chain output

Connects the 4-limb radix-2⁶⁴ Nat output of `bignumExec`-evaluated
chains to the abstract `ZMod (2²⁵⁵ − 19)` field.  Shared between
`bignum_inv_p25519` and `bignum_pow_p25519_p58` (both use the same
4-limb representation).

## Architecture

```
Chain output (4 limbs of BitVec 64 in memory)
        ↓ toNat_concat_4limbs (Sqr4Algebra.lean — already in tree)
Nat (256-bit value)
        ↓ this file: Layer C bridge
Fp25519 (opaque, via interp_fe and ZMod fpModulus)
        ↓ Mathlib ZMod power exponent
(interp_fe x) ^ exponent
```

## Status

This file aggregates the bridge **at the abstract level**.  The
concrete bridge requires:

1. A `Fp25519 ↔ Vector UInt8 32` byte-encoding bridge (already
   axiomatised via `interp_fe`).
2. A `Vector UInt8 32 ↔ 4-limb BitVec 64` bridge (a byte-rearrangement
   that's purely mechanical).
3. The Layer A chain correctness from `PowP58Algo.lean`.

(1) is the existing axiomatised opaque interface;
(2) is structural / `decide`;
(3) is in tree (Layer A).

The aggregate theorem here is the *interface* a future
discharge of `interp_fp_pow_p58` would consume.

## Trust set delta

This file adds **0 new axioms**.  All used bridges (`toNat_concat_4limbs`,
`interp_fe`) are already in tree.

## Usage

The headline lemma `chain_output_interp_eq_pow_p58` consumed by the
discharge would say: if `bignumExec` of the pow chain on inputs
(a₀, a₁, a₂, a₃) produces output (o₀, o₁, o₂, o₃), then
`interp_fe (limbsToFp25519 o) = (interp_fe (limbsToFp25519 a))^((p−5)/8)`
in `ZMod fpModulus`.

The proof composes Layer A + Layer B + Layer C.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.PowP58LayerC

open CatCrypt.Crypto.Jasmin.Ed25519.PowP58Algo
open CatCrypt.Crypto.Jasmin.BignumHoare
open scoped ENNReal

/-! ## §1  4-limb-Nat ↔ Fp25519-via-ZMod bridge

The 4-limb radix-2⁶⁴ Nat representation is the canonical
input/output format of `bignum_*_p25519` chains.  We need to lift
this to `ZMod (2²⁵⁵ − 19)` to apply Mathlib's `pow_card_sub_one`
and friends.

This section provides the bridge at the `Nat → ZMod` level; the
`ZMod ↔ Fp25519` step (via `interp_fe`) is axiomatic. -/

/-- The 4-limb radix-2⁶⁴ Nat reduction modulo p25519.  This is
    the canonical "interpretation" of a 4-limb chain output as an
    element of `ZMod p25519`. -/
def limbs4ToZmod (a0 a1 a2 a3 : Nat) : ZMod p25519 :=
  ((a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192 : Nat) : ZMod p25519)

/-- The 4-limb radix-2⁶⁴ Nat reduction matches the
    `toNat_concat_4limbs` BitVec representation under coercion to
    `ZMod p25519`. -/
theorem limbs4ToZmod_eq_concat
    (a0 a1 a2 a3 : BitVec 64) :
    limbs4ToZmod a0.toNat a1.toNat a2.toNat a3.toNat =
      ((a3 ++ a2 ++ a1 ++ a0 : BitVec 256).toNat : ZMod p25519) := by
  unfold limbs4ToZmod
  rw [CatCrypt.Crypto.Jasmin.BignumHoare.toNat_concat_4limbs]

/-! ## §2  Power preservation under the bridge

The cornerstone identity: if a Nat-level operation computes
`a^k mod p`, then under coercion to `ZMod p`, the result equals
`(a-coerced)^k`. -/

/-- Coercion preserves modular exponentiation: `(a^k mod p : ZMod p)
    = ((a : ZMod p))^k`.  Standard Mathlib fact. -/
theorem zmod_pow_natMod (a k : Nat) :
    ((a^k % p25519 : Nat) : ZMod p25519) = ((a : ZMod p25519))^k := by
  rw [ZMod.natCast_mod, Nat.cast_pow]

/-- The full Layer C bridge: when the chain's Nat-level refSem
    matches a power expression, the corresponding `ZMod p25519`
    coercion of the chain output equals the `ZMod p25519`-level
    power. -/
theorem chain_zmod_eq_pow
    (a0 a1 a2 a3 : Nat) (k : Nat) (out_a : Nat)
    (h_chain :
      out_a =
        Nat.pow (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192) k % p25519) :
    (out_a : ZMod p25519) =
      (limbs4ToZmod a0 a1 a2 a3) ^ k := by
  unfold limbs4ToZmod
  rw [h_chain]
  exact zmod_pow_natMod _ k

/-! ## §3  Connection to the chain's intent

Composing Layer A (`chainFinalExponent_eq_p58`) with this Layer C
bridge gives the final algebraic statement: under the chain's
intended `(p − 5) / 8` exponent, the chain output's `ZMod p25519`
interpretation equals the input's `ZMod p25519`-power. -/

/-- **Layer C × Layer A composition**: the chain's `ZMod p25519`
    output equals the input raised to the `chainFinalExponent` =
    `(p − 5) / 8` exponent. -/
theorem chain_zmod_eq_pow_p58
    (a0 a1 a2 a3 : Nat) (out_a : Nat)
    (h_chain :
      out_a =
        Nat.pow (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192)
                chainFinalExponent % p25519) :
    (out_a : ZMod p25519) =
      (limbs4ToZmod a0 a1 a2 a3) ^ ((p25519 - 5) / 8) := by
  rw [chainFinalExponent_eq_p58.symm]
  exact chain_zmod_eq_pow a0 a1 a2 a3 chainFinalExponent out_a h_chain

/-! ## §4  What's still axiomatic

The Layer C bridge above operates at `ZMod p25519`.  To plug into
`interp_fp_pow_p58`'s `Fp25519`-shaped statement, you need the
`Fp25519 ↔ ZMod p25519` bridge — which is the existing axiomatised
`interp_fe` (per `Ed25519Spec.lean`).  That bridge is *outside* the
bignum pipeline and is the cited-from-Rocq trust boundary.

Once `interp_fe` is plugged in (as a non-axiomatic definition via
the canonical 4-limb-byte encoding of `Fp25519`), the full
`interp_fp_pow_p58` discharge follows by composing:

```
interp_fe (limbsToFp25519 out_a)            -- by interp_fe defn
  = (out_a : ZMod p25519)                   -- canonical coercion
  = (limbs4ToZmod a) ^ ((p − 5) / 8)        -- Layer C × Layer A
  = (interp_fe (limbsToFp25519 a))^((p−5)/8) -- by interp_fe defn (other dir)
```

The remaining piece is making `interp_fe`'s definition transparent
through the 4-limb byte encoding — a separate file under
`Ed25519/InterpFeViaLimbs.lean` (not in this commit).
-/

end CatCrypt.Crypto.Jasmin.Ed25519.PowP58LayerC
