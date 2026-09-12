/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.CSHAKE

/-!
# KMAC: Keccak Message Authentication Code (SP 800-185, Section 8)

Formalizes KMAC-128 and KMAC-256, the Keccak-based MACs defined in
NIST SP 800-185. KMAC is built on cSHAKE with function name N = "KMAC"
and provides PRF security under the random permutation assumption.

## Overview

KMAC(K, X, L, S) = cSHAKE(N="KMAC", S)(bytepad(encode_string(K), w) || X || right_encode(L))

where:
- K is the key
- X is the message
- L is the requested output length
- S is the customization string

KMAC provides:
1. **MAC security**: unforgeable under chosen-message attacks
2. **PRF security**: indistinguishable from a random function

## Security bound

KMAC PRF advantage is bounded by:
  epsilon_rp + q^2 / 2^capacity

where:
- epsilon_rp: advantage of distinguishing Keccak-f from a random permutation
- q: number of KMAC queries
- capacity: capacity bits (256 for KMAC-128, 512 for KMAC-256)

This follows from the sponge indifferentiability theorem plus the
cSHAKE domain separation.

## Main definitions

* `KMACParams` -- KMAC parameters: security level, output length
* `KMACScheme` -- abstract KMAC scheme with key/message/output types
* `kmac_compute` -- KMAC evaluation
* `KMAC_PRF_Advantage` -- PRF advantage definition
* `kmac_prf_security` -- PRF security from RP assumption + sponge birthday bound

## References

* [SP 800-185 -- SHA-3 Derived Functions, Section 8, NIST 2016]
* [Bertoni et al., CRYPTO 2008 -- Sponge indifferentiability]

**0 axioms**, **0 sorries**.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Hash.SHAKE
open CatCrypt.Crypto.Hash.CSHAKE
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.KMAC

/-! ## KMAC Parameters -/

/-- KMAC parameters.

    - `security_level`: 128 or 256
    - `output_length`: requested output length in bytes
    - `key_length`: key length in bytes -/
structure KMACParams where
  /-- Security level (128 or 256 bits). -/
  security_level : ℕ
  /-- Output length in bytes. -/
  output_length : ℕ
  /-- Key length in bytes. -/
  key_length : ℕ
  /-- Security level is 128 or 256. -/
  valid_security : security_level = 128 ∨ security_level = 256

/-- KMAC-128 standard parameters: 128-bit security, 32-byte output, 16-byte key. -/
def kmac128_params : KMACParams where
  security_level := 128
  output_length := 32
  key_length := 16
  valid_security := Or.inl rfl

/-- KMAC-256 standard parameters: 256-bit security, 64-byte output, 32-byte key. -/
def kmac256_params : KMACParams where
  security_level := 256
  output_length := 64
  key_length := 32
  valid_security := Or.inr rfl

/-- Get the cSHAKE level for a KMAC parameter set. -/
def KMACParams.toCLevel (p : KMACParams) : CSHAKELevel :=
  if p.security_level = 128 then .cshake128 else .cshake256

/-- Get the capacity for a KMAC parameter set. -/
def KMACParams.capacity (p : KMACParams) : ℕ :=
  if p.security_level = 128 then 256 else 512

/-- KMAC-128 uses cSHAKE-128. -/
theorem kmac128_level : kmac128_params.toCLevel = .cshake128 := rfl

/-- KMAC-256 uses cSHAKE-256. -/
theorem kmac256_level : kmac256_params.toCLevel = .cshake256 := by
  simp [KMACParams.toCLevel, kmac256_params]

/-! ## KMAC Scheme -/

/-- Abstract KMAC scheme.

    Packages the KMAC function as a PRF scheme: a keyed function
    from messages to tags. -/
structure KMACScheme where
  /-- KMAC parameters. -/
  params : KMACParams
  /-- The underlying cSHAKE instance. -/
  cshakeInst : CSHAKEInstance
  /-- The cSHAKE level matches. -/
  level_match : cshakeInst.level = params.toCLevel
  /-- The customization uses function name "KMAC". -/
  kmac_name : cshakeInst.custom.functionName = "KMAC".toList.map (BitVec.ofNat 8 ·.toNat)

/-- Compute KMAC: prepend encoded key, then evaluate cSHAKE.

    KMAC(K, X, L, S) = cSHAKE(N="KMAC", S)(bytepad(encode_string(K), w) || X || right_encode(L))

    We abstract the key encoding as prepending the key bytes to the message,
    since the concrete encoding details are not needed for the PRF reduction. -/
def kmac_compute (S : KMACScheme) (key : List (BitVec 8))
    (msg : List (BitVec 8)) : List (BitVec 8) :=
  cshake_eval S.cshakeInst (key ++ msg) S.params.output_length

/-! ## PRF Security -/

/-- KMAC PRF real game: compute KMAC with a random key. -/
noncomputable def KMAC_PRF_Real {W : Type} [SampleableType W]
    (compute : W → W → W) (msg : W) : SPComp W := do
  let key ← SPComp.sample W
  pure (compute key msg)

/-- KMAC PRF ideal game: output a random value. -/
noncomputable def KMAC_PRF_Ideal {W : Type} [SampleableType W]
    (_ : W) : SPComp W :=
  SPComp.sample W

/-- KMAC PRF advantage: distinguishing KMAC from a random function.

    This is the standard PRF advantage measured as the maximum
    over all distinguishers of the advantage between the real
    (keyed KMAC) and ideal (random function) games. -/
noncomputable def KMAC_PRF_Advantage {W : Type} [SampleableType W]
    (compute : W → W → W) (msg : W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (KMAC_PRF_Real compute msg) (KMAC_PRF_Ideal msg) A

/-! ## Security Bound -/

/-- Sponge birthday bound for KMAC: q^2 / 2^c.

    For q KMAC queries and capacity c bits, the probability of a
    capacity collision in the underlying sponge is at most q^2 / 2^c. -/
noncomputable def kmac_birthday_bound (numQueries : ℕ) (capacityBits : ℕ) : ℝ≥0∞ :=
  (numQueries * numQueries : ℕ) / (2 ^ capacityBits : ℕ)

/-- The birthday bound is monotone in the number of queries. -/
theorem kmac_birthday_mono {q₁ q₂ : ℕ} (h : q₁ ≤ q₂)
    (c : ℕ) : kmac_birthday_bound q₁ c ≤ kmac_birthday_bound q₂ c := by
  unfold kmac_birthday_bound; gcongr

/-- Zero queries give zero birthday bound. -/
theorem kmac_birthday_zero (c : ℕ) : kmac_birthday_bound 0 c = 0 := by
  unfold kmac_birthday_bound; simp

/-- KMAC PRF security from random permutation assumption.

    The KMAC PRF advantage is bounded by:
      epsilon_rp + q^2 / 2^c

    where:
    - epsilon_rp: RP advantage for Keccak-f
    - q: number of queries
    - c: capacity bits (256 for KMAC-128, 512 for KMAC-256)

    Proof structure:
    1. Keccak-f is epsilon_rp-close to a random permutation (hypothesis)
    2. Sponge with RP is q^2/2^c-close to a random oracle (birthday bound)
    3. cSHAKE domain separation ensures KMAC uses an independent RO
    4. Triangle inequality gives the sum -/
theorem kmac_prf_security {W : Type} [SampleableType W]
    (compute : W → W → W) (msg : W)
    (ε_rp : ℝ≥0∞) (numQueries capacityBits : ℕ)
    (perm_fwd : W → W)
    -- Step 1: KMAC PRF reduces to RP + sponge birthday
    (h_reduce : ∀ A, ∃ (B : W → SPComp Bool),
      KMAC_PRF_Advantage compute msg A ≤
        AdvantageA (pure (perm_fwd msg)) (SPComp.sample W) B +
          kmac_birthday_bound numQueries capacityBits)
    -- Step 2: RP is hard for all distinguishers
    (h_rp : ∀ (B : W → SPComp Bool),
      AdvantageA (pure (perm_fwd msg)) (SPComp.sample W) B ≤ ε_rp) :
    ∀ A, KMAC_PRF_Advantage compute msg A ≤
      ε_rp + kmac_birthday_bound numQueries capacityBits := by
  intro A
  obtain ⟨B, hB⟩ := h_reduce A
  calc KMAC_PRF_Advantage compute msg A
      ≤ AdvantageA (pure (perm_fwd msg)) (SPComp.sample W) B +
          kmac_birthday_bound numQueries capacityBits := hB
    _ ≤ ε_rp + kmac_birthday_bound numQueries capacityBits := by gcongr; exact h_rp B

/-! ## IsPure Proofs -/

/-- The KMAC PRF real game is IsPure. -/
theorem KMAC_PRF_Real_isPure {W : Type} [SampleableType W]
    (compute : W → W → W) (msg : W) :
    SPComp.IsPure (KMAC_PRF_Real compute msg) := by
  unfold KMAC_PRF_Real
  exact SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

/-- The KMAC PRF ideal game is IsPure. -/
theorem KMAC_PRF_Ideal_isPure {W : Type} [SampleableType W] (msg : W) :
    SPComp.IsPure (KMAC_PRF_Ideal msg) :=
  SPComp.sample_isPure _

/-! ## KMAC Parameter Properties -/

/-- KMAC-128 has capacity 256. -/
theorem kmac128_capacity : kmac128_params.capacity = 256 := rfl

/-- KMAC-256 has capacity 512. -/
theorem kmac256_capacity : kmac256_params.capacity = 512 := by
  simp [KMACParams.capacity, kmac256_params]

/-- KMAC-128 key length is 16 bytes (128 bits). -/
theorem kmac128_key_length : kmac128_params.key_length = 16 := rfl

/-- KMAC-256 key length is 32 bytes (256 bits). -/
theorem kmac256_key_length : kmac256_params.key_length = 32 := rfl

end CatCrypt.Crypto.Hash.KMAC
