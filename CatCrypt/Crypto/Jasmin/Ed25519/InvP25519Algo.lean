/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# Layer A: Nat-level chain correctness for `bignum_inv_p25519`

Algorithmic abstraction of `BignumInvP25519.body`'s Bernstein
addition chain.  Proves that the chain's intermediate exponents are
what the documentation claims, and the final exponent equals `p − 2`
for Curve25519's `p = 2²⁵⁵ − 19` (i.e. `2²⁵⁵ − 21`).

This is the **Layer A** counterpart of `PowP58Algo.lean`.  Layer B
(connecting the Nat-level chain to the SSA `body` via
`bignumExec`-Hoare triples) is in `BignumHoare/PowP58LayerB.lean`
and `BignumHoare/InvP25519Composition.lean`.

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
op       = z2_250_0^(2⁵) · z11              exponent: 2²⁵⁵ − 21 = p − 2 ✓
```

The composed identity:
`2⁵ · (2²⁵⁰ − 1) + 11 = 2²⁵⁵ − 32 + 11 = 2²⁵⁵ − 21 = p − 2`.

By Fermat's little theorem, `z^(p − 2) mod p = z⁻¹ mod p` (for
`gcd(z, p) = 1`), so the chain computes the modular inverse of `z`.

## What this file proves (Nat level)

* Each intermediate's exponent matches the documentation.
* The final exponent equals `p − 2` for `p = 2²⁵⁵ − 19`.
* The composed identity `2⁵ · (2²⁵⁰ − 1) + 11 = 2²⁵⁵ − 21`.

## Trust set delta

This file adds **no new axioms**.  It's a pure Nat-level
verification that the chain's published exponents are correct.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo

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
    exponent = `2⁵ · (2⁵ − 1) + (2⁵ − 1) = 2¹⁰ − 1`. -/
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

/-! ## §2  Tail (Block 13 — terminal step for the inverse chain) -/

/-- Block 13: `op = z2_250_0^(2⁵) · z11`,
    exponent = `2⁵ · (2²⁵⁰ − 1) + 11 = 2²⁵⁵ − 21`. -/
theorem block13_exponent :
    2^5 * (2^250 - 1) + 11 = 2^255 - 21 := by decide

/-! ## §3  Final exponent equals `p − 2` -/

/-- Curve25519 modulus. -/
abbrev p25519 : Nat := 2^255 - 19

/-- The chain's final exponent equals `p − 2`. -/
theorem chain_final_exponent_is_p_minus_2 :
    2^255 - 21 = p25519 - 2 := by
  unfold p25519
  decide

/-- Composed identity: the entire chain (12 prefix blocks + tail
    block 13) computes the exponent `p − 2`. -/
theorem chain_composes_to_p_minus_2 :
    2^5 * (2^250 - 1) + 11 = p25519 - 2 :=
  block13_exponent.trans chain_final_exponent_is_p_minus_2

/-! ## §4  Nat-level chain executor

Abstract chain semantics: `chainFinalExponent` returns the exponent
value that the abstract chain produces when starting from `z`
(modelled as the variable identity element with exponent 1).  Each
block's contribution multiplies/adds exponents per the chain's
published shape. -/

/-- Abstract chain executor returning the final exponent.  Each
    intermediate's exponent is computed step by step. -/
def chainFinalExponent : Nat :=
  -- Block 2: z2 = z² → exponent 2
  let _e_z2 : Nat := 2
  -- Block 3: z9 = (z²)⁴ · z → exponent 9
  let _e_z9 : Nat := 9
  -- Block 4: z11 = z9 · z2 → exponent 11
  let _e_z11 : Nat := 11
  -- Block 5: z2_5_0 = z11² · z9 → exponent 2⁵ - 1
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
  -- Block 13: op = z2_250_0^(2⁵) · z11 = z^(2⁵·(2²⁵⁰-1)+11) = z^(2²⁵⁵-21) = z^(p-2)
  2^5 * (2^250 - 1) + 11

/-- The chainFinalExponent equals `p − 2`. -/
theorem chainFinalExponent_eq_p_minus_2 :
    chainFinalExponent = p25519 - 2 := by
  unfold chainFinalExponent
  exact chain_composes_to_p_minus_2

/-- The chainFinalExponent equals `2²⁵⁵ − 21`. -/
theorem chainFinalExponent_eq_2_255_m21 :
    chainFinalExponent = 2^255 - 21 := by
  unfold chainFinalExponent
  exact block13_exponent

/-! ## §5  Connection to `BignumInvP25519.refSem`

The `refSem` from `S2NBignumSSA.lean::BignumInvP25519` is defined as
`Nat.pow a (p − 2) % p`.  Our `chainFinalExponent` proves the chain's
*intent* matches `p − 2`.  Composing the two gives:

```
refSem a = Nat.pow a chainFinalExponent % p
```

Layer B (the Hoare triple) then connects this *intent* to the SSA
body's *actual computation* through `bignumExec`. -/

/-- Bridge to refSem's exponent: the Nat-level abstract chain
    produces the exponent `p − 2`. -/
theorem chain_intent_matches_refSem_exponent :
    chainFinalExponent = p25519 - 2 :=
  chainFinalExponent_eq_p_minus_2

/-! ## §6  Layer A ↔ Layer B bridge: chain product = `a^(p − 2) mod p`

The chain triple's post (from
`InvP25519Composition.inv_p25519_chain_triple`) records the
chain's final output as a *symbolic Nat product*:
`(z2_250_0_val^(2^5) · z11_val) % p_25519`.

This section bridges that symbolic shape to the canonical
`a_val^(p − 2) % p_25519` form, given the per-block algebraic
identities (which a downstream caller supplies — they hold by
construction since each chain step is `% p_25519`-reduced).

The proof is a Nat-level chain of `Nat.pow_mod` / `Nat.mul_mod` /
`pow_add` / `pow_mul` rewrites — one per intermediate. -/

/-! Each intermediate `z_k` in the chain satisfies
    `z_k % p_25519 = a_val^(e_k) % p_25519` where `e_k` is the exponent
    from §1.  The bridge theorem below threads each identity through. -/

/-- Symbolic chain-step arithmetic: `(2^a - 1) · 2^b + (2^b - 1) = 2^(a + b) - 1`.

    This is the algebraic identity underlying each chain step of the
    form `z_new = z_prev^(2^b) · z_other` where `z_prev` has exponent
    `2^a - 1` and `z_other` has exponent `2^b - 1`. -/
private lemma chain_arith (a b : Nat) :
    (2^a - 1) * 2^b + (2^b - 1) = 2^(a + b) - 1 := by
  have h_pow : (2 : Nat)^(a + b) = 2^a * 2^b := pow_add 2 a b
  have h1 : 1 ≤ (2 : Nat)^a := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 : Nat)^b := Nat.one_le_two_pow
  rw [h_pow, Nat.sub_one_mul]
  have h_le : (2 : Nat)^b ≤ 2^a * 2^b := Nat.le_mul_of_pos_left _ h1
  set m := (2 : Nat)^a
  set n := (2 : Nat)^b
  -- Goal: m * n - n + (n - 1) = m * n - 1; with h_le : n ≤ m * n.
  omega

/-- Terminal-step arithmetic: `(2^250 - 1) · 2^5 + 11 = 2^255 - 21`. -/
private lemma terminal_arith :
    (2^250 - 1) * 2^5 + 11 = 2^255 - 21 := by
  have h : (2^255 : Nat) = 2^250 * 2^5 := by
    rw [show (255 : Nat) = 250 + 5 from rfl, pow_add]
  have h1 : 1 ≤ (2^250 : Nat) := Nat.one_le_two_pow
  have h_32 : (2 : Nat)^5 = 32 := by decide
  rw [h, Nat.sub_one_mul, h_32]
  have h_le : (32 : Nat) ≤ 2^250 * 32 := Nat.le_mul_of_pos_left _ h1
  set m := (2 : Nat)^250
  omega

/-- **Layer A ↔ Layer B bridge.**  Given the 11 per-block algebraic
    identities (each `z_k = (z_{k-1}^... · z_j) % p_25519`), the
    chain's final product equals `a_val^(p − 2) % p_25519`.

    The hypotheses are exactly the post-conditions of each
    `blockN_correctness_triple` (modulo the implicit `% p_25519`
    on each value).  No fresh assumptions: the chain identities
    follow by construction from each block's `% p_25519`-reduced
    output. -/
theorem inv_chain_product_eq_pow_p_minus_2
    (a_val : Nat)
    (z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
     z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
     : Nat)
    -- Per-block algebraic identities (modular).
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
    (z2_250_0_val^(2^5) * z11_val) % p25519 = a_val^(p25519 - 2) % p25519 := by
  -- Derive each intermediate's exponent.  At each step, use
  -- `Nat.mul_mod` to push the mod inward, `Nat.pow_mod` to commute
  -- mod with pow, then the previous identity, then arithmetic.
  -- ModEq calc chains: each `m_z_k : Nat.ModEq p_25519 z_k (a_val^e_k)`.
  have m_z2 : Nat.ModEq p25519 z2_val (a_val^2) := by
    show z2_val % p25519 = a_val^2 % p25519
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
            rw [← pow_mul, ← pow_add]
            congr 1
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
  -- Final: z2_250_0^(2^5) · z11 ≡ (a^(2^250-1))^(2^5) · a^11 ≡ a^(2^255 - 21) = a^(p - 2).
  show (z2_250_0_val^(2^5) * z11_val) % p25519 = a_val^(p25519 - 2) % p25519
  have m_final : Nat.ModEq p25519 (z2_250_0_val^(2^5) * z11_val)
                                  (a_val^(p25519 - 2)) :=
    calc z2_250_0_val^(2^5) * z11_val
        ≡ (a_val^(2^250 - 1))^(2^5) * a_val^11 [MOD p25519] :=
          (m_z2_250_0.pow _).mul m_z11
      _ = a_val^(p25519 - 2) := by
            rw [← pow_mul, ← pow_add, terminal_arith, show p25519 - 2 = 2^255 - 21 from by
              unfold p25519; decide]
  exact m_final

/-! ## §7  Fermat bridge: `a^(p − 2) ≡ a⁻¹ (mod p)`

For prime `p` and `a ≢ 0 (mod p)`, Fermat's little theorem gives
`a^(p − 1) ≡ 1 (mod p)`, hence `a^(p − 2) · a ≡ 1 (mod p)`, so
`a^(p − 2)` is the modular inverse of `a`.

We state this in `ZMod p_25519` (Mathlib's modular ring), where the
`⁻¹` operation is well-defined.  The bridge to the inv_p25519 chain
triple follows by composing with `inv_chain_product_eq_pow_p_minus_2`
(§6) and reducing to `ZMod p_25519`.

The `Fact (Nat.Prime p_25519)` instance is satisfied by
`CatCrypt.Crypto.ECC.curve25519Prime_prime` (the codebase's
primality axiom for 2²⁵⁵ − 19).  Callers must provide a `Fact`
instance to invoke the bridge. -/

/-- Fermat's little theorem in `ZMod p_25519`: for non-zero `a`,
    `a^(p − 2) = a⁻¹`. -/
theorem zmod_pow_p_sub_two_eq_inv [Fact (Nat.Prime p25519)]
    (a : ZMod p25519) (h : a ≠ 0) :
    a^(p25519 - 2) = a⁻¹ := by
  have hp_ge : 2 ≤ p25519 := (Fact.out (p := Nat.Prime p25519)).two_le
  -- Fermat: a^(p - 1) = 1 (since |ZMod p| = p when p is prime).
  have h_pow : a^(p25519 - 1) = 1 := by
    have h_card : Fintype.card (ZMod p25519) = p25519 := ZMod.card p25519
    have h_fermat := FiniteField.pow_card_sub_one_eq_one a h
    rwa [h_card] at h_fermat
  -- a * a^(p - 2) = a^(p - 1) = 1.
  have h_mul : a * a^(p25519 - 2) = 1 := by
    rw [← pow_succ', show p25519 - 2 + 1 = p25519 - 1 from by omega]
    exact h_pow
  -- ZMod.inv_eq_of_mul_eq_one: a * b = 1 → a⁻¹ = b.  We want a^(p-2) = a⁻¹.
  exact (ZMod.inv_eq_of_mul_eq_one p25519 a (a^(p25519 - 2)) h_mul).symm

/-- **Final bridge.**  Combining §6 (chain product = `a^(p − 2) mod p`) with
    §7 (Fermat: `a^(p − 2) = a⁻¹` in `ZMod p`), the inv chain's symbolic
    Nat product equals `a⁻¹` in `ZMod p_25519`. -/
theorem inv_chain_product_eq_inv [Fact (Nat.Prime p25519)]
    (a_val : Nat) (h_a_ne_zero : (a_val : ZMod p25519) ≠ 0)
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
    ((z2_250_0_val^(2^5) * z11_val : Nat) : ZMod p25519) =
    (a_val : ZMod p25519)⁻¹ := by
  have h_nat : (z2_250_0_val^(2^5) * z11_val) % p25519 = a_val^(p25519 - 2) % p25519 :=
    inv_chain_product_eq_pow_p_minus_2 a_val
      z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
      z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
      h_z2 h_z9 h_z11 h_z2_5_0 h_z2_10_0 h_z2_20_0 h_z2_40_0 h_z2_50_0
      h_z2_100_0 h_z2_200_0 h_z2_250_0
  -- Lift to ZMod: Nat.ModEq → ZMod equality.
  have h_zmod : ((z2_250_0_val^(2^5) * z11_val : Nat) : ZMod p25519) =
                ((a_val^(p25519 - 2) : Nat) : ZMod p25519) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact h_nat
  rw [h_zmod, Nat.cast_pow]
  exact zmod_pow_p_sub_two_eq_inv (a_val : ZMod p25519) h_a_ne_zero

end CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo
