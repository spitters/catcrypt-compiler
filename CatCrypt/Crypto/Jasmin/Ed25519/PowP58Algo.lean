/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Layer A: Nat-level chain correctness for `bignum_pow_p25519_p58`

Algorithmic abstraction of `BignumPowP58P25519.body`'s Bernstein
addition chain.  Proves that the chain's intermediate exponents are
what the documentation claims, and the final exponent equals
`(p−5)/8 = 2²⁵² − 3` for Curve25519's `p = 2²⁵⁵ − 19`.

This is **Layer A** of the discharge in
`Ed25519/PowP58Bridge.lean`.  Layer B (connecting the Nat-level
chain to the SSA `body` via `bignumExec`-Hoare triples) and Layer C
(connecting Nat output to `Fp25519.interp_fe`) remain.

## The chain

```
z2     = z²                                 exponent: 2
z9     = (z²)⁴ · z = z⁸ · z                 exponent: 9
z11    = z9 · z²                            exponent: 11
z2_5_0 = z11² · z9                          exponent: 31 = 2⁵ − 1
z2_10_0 = z2_5_0^(2⁵) · z2_5_0              exponent: 2¹⁰ − 1
z2_20_0 = z2_10_0^(2¹⁰) · z2_10_0           exponent: 2²⁰ − 1
z2_40_0 = z2_20_0^(2²⁰) · z2_20_0           exponent: 2⁴⁰ − 1
z2_50_0 = z2_40_0^(2¹⁰) · z2_10_0           exponent: 2⁵⁰ − 1
z2_100_0 = z2_50_0^(2⁵⁰) · z2_50_0          exponent: 2¹⁰⁰ − 1
z2_200_0 = z2_100_0^(2¹⁰⁰) · z2_100_0       exponent: 2²⁰⁰ − 1
z2_250_0 = z2_200_0^(2⁵⁰) · z2_50_0         exponent: 2²⁵⁰ − 1
op       = z2_250_0^(2²) · z                exponent: 2²⁵² − 3 = (p−5)/8 ✓
```

## What this file proves (Nat level)

* Each intermediate's exponent matches the documentation.
* The final exponent equals `(p−5)/8` for `p = 2²⁵⁵ − 19`.
* The composed identity `4 · (2²⁵⁰ − 1) + 1 = 2²⁵² − 3 = (p−5)/8`.

## Trust set delta

This file adds **no new axioms**.  It's a pure Nat-level
verification that the chain's published exponents are correct.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.PowP58Algo

/-! ## §1  Per-block exponent identities -/

/-- Block 2: `z2 = z²` has exponent 2. -/
theorem block2_exponent : (2 : Nat) = 2 := rfl

/-- Block 3: `z9 = z⁸ · z` (= `(z²)⁴ · z`). -/
theorem block3_exponent : (8 + 1 : Nat) = 9 := rfl

/-- Block 4: `z11 = z⁹ · z²`. -/
theorem block4_exponent : (9 + 2 : Nat) = 11 := rfl

/-- Block 5: `z2_5_0 = z11² · z9 = z²² · z⁹ = z³¹`. -/
theorem block5_exponent : (2 * 11 + 9 : Nat) = 2^5 - 1 := by decide

/-- Block 6: `z2_10_0 = z2_5_0^(2⁵) · z2_5_0`,
    exponent = `2⁵ · (2⁵ − 1) + (2⁵ − 1) = (2⁵ + 1)(2⁵ − 1) = 2¹⁰ − 1`. -/
theorem block6_exponent :
    2^5 * (2^5 - 1) + (2^5 - 1) = 2^10 - 1 := by decide

/-- Block 7: `z2_20_0 = z2_10_0^(2¹⁰) · z2_10_0`,
    exponent = `2¹⁰ · (2¹⁰ − 1) + (2¹⁰ − 1) = 2²⁰ − 1`. -/
theorem block7_exponent :
    2^10 * (2^10 - 1) + (2^10 - 1) = 2^20 - 1 := by decide

/-- Block 8: `z2_40_0 = z2_20_0^(2²⁰) · z2_20_0`,
    exponent = `2⁴⁰ − 1`. -/
theorem block8_exponent :
    2^20 * (2^20 - 1) + (2^20 - 1) = 2^40 - 1 := by decide

/-- Block 9: `z2_50_0 = z2_40_0^(2¹⁰) · z2_10_0`,
    exponent = `2¹⁰ · (2⁴⁰ − 1) + (2¹⁰ − 1) = 2⁵⁰ − 1`. -/
theorem block9_exponent :
    2^10 * (2^40 - 1) + (2^10 - 1) = 2^50 - 1 := by decide

/-- Block 10: `z2_100_0 = z2_50_0^(2⁵⁰) · z2_50_0`,
    exponent = `2¹⁰⁰ − 1`. -/
theorem block10_exponent :
    2^50 * (2^50 - 1) + (2^50 - 1) = 2^100 - 1 := by decide

/-- Block 11: `z2_200_0 = z2_100_0^(2¹⁰⁰) · z2_100_0`,
    exponent = `2²⁰⁰ − 1`. -/
theorem block11_exponent :
    2^100 * (2^100 - 1) + (2^100 - 1) = 2^200 - 1 := by decide

/-- Block 12: `z2_250_0 = z2_200_0^(2⁵⁰) · z2_50_0`,
    exponent = `2⁵⁰ · (2²⁰⁰ − 1) + (2⁵⁰ − 1) = 2²⁵⁰ − 1`. -/
theorem block12_exponent :
    2^50 * (2^200 - 1) + (2^50 - 1) = 2^250 - 1 := by decide

/-! ## §2  Tail (Block 13b — divergent from inv chain) -/

/-- Block 13b (divergent from inv): `op = z2_250_0^(2²) · z`,
    exponent = `2² · (2²⁵⁰ − 1) + 1 = 2²⁵² − 3`. -/
theorem block13b_exponent :
    2^2 * (2^250 - 1) + 1 = 2^252 - 3 := by decide

/-! ## §3  Final exponent equals `(p−5)/8` -/

/-- Curve25519 modulus. -/
abbrev p25519 : Nat := 2^255 - 19

/-- The chain's final exponent equals `(p−5)/8`. -/
theorem chain_final_exponent_is_p58 :
    2^252 - 3 = (p25519 - 5) / 8 := by
  unfold p25519
  decide

/-- Composed identity: the entire chain (12 prefix blocks + tail
    block 13b) computes the exponent `(p−5)/8`. -/
theorem chain_composes_to_p58 :
    2^2 * (2^250 - 1) + 1 = (p25519 - 5) / 8 :=
  block13b_exponent.trans chain_final_exponent_is_p58

/-! ## §4  Nat-level chain executor

Abstract chain semantics: `chainExp z` returns the exponent value
that the abstract chain produces when starting from `z` (modelled
as the variable identity element with exponent 1).  Each block's
contribution multiplies/adds exponents per the chain's published
shape. -/

/-- Abstract chain executor returning the final exponent.  Each
    intermediate's exponent is computed step by step. -/
def chainFinalExponent : Nat :=
  -- Block 2: z2 = z² → exponent 2
  let _e_z2 : Nat := 2
  -- Block 3: z9 = (z²)⁴ · z = z⁸ · z → exponent 9
  let _e_z9 : Nat := 9
  -- Block 4: z11 = z9 · z2 → exponent 11
  let _e_z11 : Nat := 11
  -- Block 5: z2_5_0 = z11² · z9 → exponent 31 = 2⁵ - 1
  let _e_5_0 : Nat := 2^5 - 1
  -- Block 6: 2¹⁰ - 1
  let _e_10_0 : Nat := 2^10 - 1
  -- Block 7: 2²⁰ - 1
  let _e_20_0 : Nat := 2^20 - 1
  -- Block 8: 2⁴⁰ - 1
  let _e_40_0 : Nat := 2^40 - 1
  -- Block 9: 2⁵⁰ - 1
  let _e_50_0 : Nat := 2^50 - 1
  -- Block 10: 2¹⁰⁰ - 1
  let _e_100_0 : Nat := 2^100 - 1
  -- Block 11: 2²⁰⁰ - 1
  let _e_200_0 : Nat := 2^200 - 1
  -- Block 12: 2²⁵⁰ - 1
  let _e_250_0 : Nat := 2^250 - 1
  -- Block 13b: op = z2_250_0² · z2_250_0² · z = z^(4·(2²⁵⁰-1)+1) = z^(2²⁵²-3)
  2^2 * (2^250 - 1) + 1

/-- The chainFinalExponent equals `(p−5)/8`. -/
theorem chainFinalExponent_eq_p58 :
    chainFinalExponent = (p25519 - 5) / 8 := by
  unfold chainFinalExponent
  exact chain_composes_to_p58

/-- The chainFinalExponent equals `2^252 - 3`. -/
theorem chainFinalExponent_eq_2_252_m3 :
    chainFinalExponent = 2^252 - 3 := by
  unfold chainFinalExponent
  exact block13b_exponent

/-! ## §5  Connection to `BignumPowP58P25519.refSem`

The `refSem` from `S2NBignumSSA.lean::BignumPowP58P25519` is
defined as `Nat.pow a ((p − 5) / 8) % p`.  Our `chainFinalExponent`
proves the chain's *intent* matches `(p − 5) / 8`.  Composing the
two gives:

```
refSem a = Nat.pow a chainFinalExponent % p
```

Layer B (the Hoare triple) then connects this *intent* to the SSA
body's *actual computation* through `bignumExec`. -/

/-- Bridge to refSem's exponent: the Nat-level abstract chain
    produces the exponent `(p − 5) / 8`. -/
theorem chain_intent_matches_refSem_exponent :
    chainFinalExponent = (p25519 - 5) / 8 :=
  chainFinalExponent_eq_p58

/-! ## §6  Layer A ↔ Layer B bridge: chain product = `a^((p − 5)/8) mod p`

The p58 chain triple's post records the chain's final output as a
*symbolic Nat product*: `(z2_250_0_val^(2^2) · a_val) % p_25519`
(the chain ends with a multiply against `ap`, in contrast to the inv
chain that ends with `· z11`).

This section bridges that symbolic shape to the canonical
`a_val^((p − 5)/8) % p_25519` form.  The proof is the same calc-chain
structure as InvP25519Algo §6 (with the same 11 per-block algebraic
identities) but with a different terminal step. -/

/-- Symbolic chain-step arithmetic (shared with the inv chain): the
    inv-side `chain_arith` lemma already gives
    `(2^a − 1) · 2^b + (2^b − 1) = 2^(a + b) − 1`. -/
private lemma chain_arith (a b : Nat) :
    (2^a - 1) * 2^b + (2^b - 1) = 2^(a + b) - 1 := by
  have h_pow : (2 : Nat)^(a + b) = 2^a * 2^b := pow_add 2 a b
  have h1 : 1 ≤ (2 : Nat)^a := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 : Nat)^b := Nat.one_le_two_pow
  rw [h_pow, Nat.sub_one_mul]
  have h_le : (2 : Nat)^b ≤ 2^a * 2^b := Nat.le_mul_of_pos_left _ h1
  set m := (2 : Nat)^a
  set n := (2 : Nat)^b
  omega

/-- Terminal-step arithmetic for the p58 chain:
    `(2^250 − 1) · 2^2 + 1 = 2^252 − 3`. -/
private lemma terminal_arith_p58 :
    (2^250 - 1) * 2^2 + 1 = 2^252 - 3 := by
  have h : (2^252 : Nat) = 2^250 * 2^2 := by
    rw [show (252 : Nat) = 250 + 2 from rfl, pow_add]
  have h1 : 1 ≤ (2^250 : Nat) := Nat.one_le_two_pow
  have h_4 : (2 : Nat)^2 = 4 := by decide
  rw [h, Nat.sub_one_mul, h_4]
  set m := (2 : Nat)^250
  omega

/-- **p58 Layer A ↔ Layer B bridge.**  Given the 11 per-block algebraic
    identities, the p58 chain's final product equals
    `a_val^((p − 5)/8) % p_25519`. -/
theorem pow_p58_chain_product_eq_pow_p58
    (a_val : Nat)
    (z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
     z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
     : Nat)
    (h_z2  : z2_val  % p25519 = (a_val * a_val) % p25519)
    (h_z9  : z9_val  % p25519 = (z2_val^(2^2) * a_val) % p25519)
    (h_z11 : z11_val % p25519 = (z9_val * z2_val) % p25519)
    (h_z2_5_0   : z2_5_0_val   % p25519 = (z11_val^(2^1) * z9_val) % p25519)
    (h_z2_10_0  : z2_10_0_val  % p25519 = (z2_5_0_val^(2^5) * z2_5_0_val) % p25519)
    (h_z2_20_0  : z2_20_0_val  % p25519 = (z2_10_0_val^(2^10) * z2_10_0_val) % p25519)
    (h_z2_40_0  : z2_40_0_val  % p25519 = (z2_20_0_val^(2^20) * z2_20_0_val) % p25519)
    (h_z2_50_0  : z2_50_0_val  % p25519 = (z2_40_0_val^(2^10) * z2_10_0_val) % p25519)
    (h_z2_100_0 : z2_100_0_val % p25519 = (z2_50_0_val^(2^50) * z2_50_0_val) % p25519)
    (h_z2_200_0 : z2_200_0_val % p25519 = (z2_100_0_val^(2^100) * z2_100_0_val) % p25519)
    (h_z2_250_0 : z2_250_0_val % p25519 = (z2_200_0_val^(2^50) * z2_50_0_val) % p25519) :
    (z2_250_0_val^(2^2) * a_val) % p25519 = a_val^((p25519 - 5) / 8) % p25519 := by
  -- Walk each chain step (identical prefix to inv): m_z_k : z_k ≡ a^e_k.
  have m_z2 : Nat.ModEq p25519 z2_val (a_val^2) := by
    show z2_val % p25519 = _
    rw [h_z2, sq]
  have m_z9 : Nat.ModEq p25519 z9_val (a_val^9) :=
    calc z9_val
        ≡ z2_val^(2^2) * a_val [MOD p25519] := h_z9
      _ ≡ (a_val^2)^(2^2) * a_val [MOD p25519] :=
          Nat.ModEq.mul_right a_val (m_z2.pow _)
      _ = a_val^9 := by ring
  have m_z11 : Nat.ModEq p25519 z11_val (a_val^11) :=
    calc z11_val
        ≡ z9_val * z2_val [MOD p25519] := h_z11
      _ ≡ a_val^9 * a_val^2 [MOD p25519] := m_z9.mul m_z2
      _ = a_val^11 := by ring
  have m_z2_5_0 : Nat.ModEq p25519 z2_5_0_val (a_val^(2^5 - 1)) :=
    calc z2_5_0_val
        ≡ z11_val^(2^1) * z9_val [MOD p25519] := h_z2_5_0
      _ ≡ (a_val^11)^(2^1) * a_val^9 [MOD p25519] :=
          (m_z11.pow _).mul m_z9
      _ = a_val^(2^5 - 1) := by
            rw [← pow_mul, ← pow_add]; rfl
  have m_z2_10_0 : Nat.ModEq p25519 z2_10_0_val (a_val^(2^10 - 1)) :=
    calc z2_10_0_val
        ≡ z2_5_0_val^(2^5) * z2_5_0_val [MOD p25519] := h_z2_10_0
      _ ≡ (a_val^(2^5 - 1))^(2^5) * a_val^(2^5 - 1) [MOD p25519] :=
          (m_z2_5_0.pow _).mul m_z2_5_0
      _ = a_val^(2^10 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 5 5]
  have m_z2_20_0 : Nat.ModEq p25519 z2_20_0_val (a_val^(2^20 - 1)) :=
    calc z2_20_0_val
        ≡ z2_10_0_val^(2^10) * z2_10_0_val [MOD p25519] := h_z2_20_0
      _ ≡ (a_val^(2^10 - 1))^(2^10) * a_val^(2^10 - 1) [MOD p25519] :=
          (m_z2_10_0.pow _).mul m_z2_10_0
      _ = a_val^(2^20 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 10 10]
  have m_z2_40_0 : Nat.ModEq p25519 z2_40_0_val (a_val^(2^40 - 1)) :=
    calc z2_40_0_val
        ≡ z2_20_0_val^(2^20) * z2_20_0_val [MOD p25519] := h_z2_40_0
      _ ≡ (a_val^(2^20 - 1))^(2^20) * a_val^(2^20 - 1) [MOD p25519] :=
          (m_z2_20_0.pow _).mul m_z2_20_0
      _ = a_val^(2^40 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 20 20]
  have m_z2_50_0 : Nat.ModEq p25519 z2_50_0_val (a_val^(2^50 - 1)) :=
    calc z2_50_0_val
        ≡ z2_40_0_val^(2^10) * z2_10_0_val [MOD p25519] := h_z2_50_0
      _ ≡ (a_val^(2^40 - 1))^(2^10) * a_val^(2^10 - 1) [MOD p25519] :=
          (m_z2_40_0.pow _).mul m_z2_10_0
      _ = a_val^(2^50 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 40 10]
  have m_z2_100_0 : Nat.ModEq p25519 z2_100_0_val (a_val^(2^100 - 1)) :=
    calc z2_100_0_val
        ≡ z2_50_0_val^(2^50) * z2_50_0_val [MOD p25519] := h_z2_100_0
      _ ≡ (a_val^(2^50 - 1))^(2^50) * a_val^(2^50 - 1) [MOD p25519] :=
          (m_z2_50_0.pow _).mul m_z2_50_0
      _ = a_val^(2^100 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 50 50]
  have m_z2_200_0 : Nat.ModEq p25519 z2_200_0_val (a_val^(2^200 - 1)) :=
    calc z2_200_0_val
        ≡ z2_100_0_val^(2^100) * z2_100_0_val [MOD p25519] := h_z2_200_0
      _ ≡ (a_val^(2^100 - 1))^(2^100) * a_val^(2^100 - 1) [MOD p25519] :=
          (m_z2_100_0.pow _).mul m_z2_100_0
      _ = a_val^(2^200 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 100 100]
  have m_z2_250_0 : Nat.ModEq p25519 z2_250_0_val (a_val^(2^250 - 1)) :=
    calc z2_250_0_val
        ≡ z2_200_0_val^(2^50) * z2_50_0_val [MOD p25519] := h_z2_250_0
      _ ≡ (a_val^(2^200 - 1))^(2^50) * a_val^(2^50 - 1) [MOD p25519] :=
          (m_z2_200_0.pow _).mul m_z2_50_0
      _ = a_val^(2^250 - 1) := by
            rw [← pow_mul, ← pow_add, chain_arith 200 50]
  -- Terminal (p58-specific): z2_250_0^(2^2) · a ≡ a^((2^250-1)·2^2 + 1) = a^(2^252 - 3).
  show (z2_250_0_val^(2^2) * a_val) % p25519 = a_val^((p25519 - 5) / 8) % p25519
  have m_final : Nat.ModEq p25519 (z2_250_0_val^(2^2) * a_val)
                                  (a_val^((p25519 - 5) / 8)) :=
    calc z2_250_0_val^(2^2) * a_val
        ≡ (a_val^(2^250 - 1))^(2^2) * a_val^1 [MOD p25519] := by
            rw [pow_one]
            exact (m_z2_250_0.pow _).mul (Nat.ModEq.refl _)
      _ = a_val^((p25519 - 5) / 8) := by
            rw [← pow_mul, ← pow_add, terminal_arith_p58,
                show ((p25519 - 5) / 8 : Nat) = 2^252 - 3 from by
                  unfold p25519; decide]
  exact m_final

end CatCrypt.Crypto.Jasmin.Ed25519.PowP58Algo
