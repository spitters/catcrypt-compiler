/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.Keccak

/-!
# SHAKE Extendable-Output Functions (FIPS 202)

Formalizes SHAKE-128 and SHAKE-256 as extendable-output functions (XOFs)
built on the Keccak sponge construction. These are the primary hash
primitives used throughout NIST post-quantum cryptography standards.

## Overview

SHAKE (Secure Hash Algorithm KECCAK) provides variable-length output:
- **SHAKE-128**: rate = 1344, capacity = 256, 128-bit security
- **SHAKE-256**: rate = 1088, capacity = 512, 256-bit security

The sponge construction has two phases:
1. **Absorb**: XOR message blocks into the rate portion, apply Keccak-f
2. **Squeeze**: Extract rate portion as output, apply Keccak-f, repeat

## Main definitions

* `SHAKEParams` -- XOF parameters: rate, capacity, security level
* `shake128_params`, `shake256_params` -- concrete SHAKE instances
* `shake_absorb` -- sponge absorb phase (abstract)
* `shake_squeeze` -- sponge squeeze phase (abstract)
* `shake_xof` -- full XOF: absorb then squeeze
* `XOFDef` -- abstract extendable-output function definition
* `shake128_xof`, `shake256_xof` -- SHAKE XOF instances

## References

* [FIPS 202 -- SHA-3 Standard, Sections 6.2-6.3, NIST 2015]
* [SP 800-185 -- SHA-3 Derived Functions, NIST 2016]

**0 axioms**, **all goals closed**.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Keccak
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.SHAKE

/-! ## SHAKE Parameters -/

/-- SHAKE extendable-output function parameters.

    Captures the rate/capacity split and the claimed security level. -/
structure SHAKEParams where
  /-- Rate in bits. -/
  rate : ℕ
  /-- Capacity in bits. -/
  capacity : ℕ
  /-- Security level in bits (half the capacity for XOFs). -/
  security_level : ℕ
  /-- Well-formedness: rate + capacity = 1600. -/
  wf : rate + capacity = 1600
  /-- Security level is at most half the capacity. -/
  security_bound : security_level ≤ capacity / 2

/-- SHAKE-128 parameters: rate = 1344, capacity = 256, security = 128. -/
def shake128_params : SHAKEParams where
  rate := 1344
  capacity := 256
  security_level := 128
  wf := by omega
  security_bound := by omega

/-- SHAKE-256 parameters: rate = 1088, capacity = 512, security = 256. -/
def shake256_params : SHAKEParams where
  rate := 1088
  capacity := 512
  security_level := 256
  wf := by omega
  security_bound := by omega

/-! ## Sponge Phases (Abstract) -/

/-- Abstract sponge absorb phase.

    Processes a list of message bytes by XORing them into the rate
    portion of the state and applying the permutation after each
    rate-sized block. The concrete bit manipulation is abstracted
    away since security proofs only need the sponge structure. -/
structure SpongeAbsorb where
  /-- Absorb message bytes into the Keccak state. -/
  absorb : KeccakState → List (BitVec 8) → KeccakState

/-- Abstract sponge squeeze phase.

    Extracts output bytes from the rate portion of the state,
    applying the permutation between each rate-sized output block. -/
structure SpongeSqueeze where
  /-- Squeeze n output bytes from the Keccak state. -/
  squeeze : KeccakState → ℕ → List (BitVec 8)

/-! ## SHAKE XOF -/

/-- A SHAKE instance bundles parameters with absorb/squeeze functions. -/
structure SHAKEInstance where
  /-- The SHAKE parameters. -/
  params : SHAKEParams
  /-- The absorb function. -/
  absorber : SpongeAbsorb
  /-- The squeeze function. -/
  squeezer : SpongeSqueeze

/-- Compute a SHAKE XOF output.

    Full XOF computation: pad the input, absorb into the sponge,
    then squeeze the requested number of output bytes.

    The domain separation suffix for SHAKE is `1111` (0x1F). -/
def shake_xof (inst : SHAKEInstance) (input : List (BitVec 8))
    (outputBytes : ℕ) : List (BitVec 8) :=
  let initialState : KeccakState := 0
  let absorbed := inst.absorber.absorb initialState input
  inst.squeezer.squeeze absorbed outputBytes

/-! ## Abstract XOF Definition -/

/-- Abstract extendable-output function (XOF).

    A generic interface for variable-length hash functions. Any XOF
    takes an arbitrary-length input and produces an arbitrary-length
    output. -/
structure XOFDef where
  /-- The XOF name (for domain separation). -/
  name : String
  /-- The claimed security level in bits. -/
  security : ℕ
  /-- The XOF evaluation function. -/
  eval : List (BitVec 8) → ℕ → List (BitVec 8)

/-- SHAKE-128 as an abstract XOF. -/
def shake128_xof (inst : SHAKEInstance) (_ : inst.params = shake128_params) :
    XOFDef where
  name := "SHAKE128"
  security := 128
  eval := shake_xof inst

/-- SHAKE-256 as an abstract XOF. -/
def shake256_xof (inst : SHAKEInstance) (_ : inst.params = shake256_params) :
    XOFDef where
  name := "SHAKE256"
  security := 256
  eval := shake_xof inst

/-! ## Properties -/

/-- SHAKE-128 has 128-bit security. -/
theorem shake128_security_level : shake128_params.security_level = 128 := rfl

/-- SHAKE-256 has 256-bit security. -/
theorem shake256_security_level : shake256_params.security_level = 256 := rfl

/-- SHAKE-128 rate is 1344 bits (168 bytes). -/
theorem shake128_rate : shake128_params.rate = 1344 := rfl

/-- SHAKE-256 rate is 1088 bits (136 bytes). -/
theorem shake256_rate : shake256_params.rate = 1088 := rfl

/-- SHAKE-128 capacity is 256 bits. -/
theorem shake128_capacity : shake128_params.capacity = 256 := rfl

/-- SHAKE-256 capacity is 512 bits. -/
theorem shake256_capacity : shake256_params.capacity = 512 := rfl

/-- SHAKE-128 and SHAKE-256 have different rates. -/
theorem shake128_neq_shake256 : shake128_params ≠ shake256_params := by
  intro h
  have := congrArg SHAKEParams.rate h
  simp [shake128_params, shake256_params] at this

/-- SHAKE-128 XOF output is computed from the absorb/squeeze pipeline. -/
theorem shake128_xof_eval (inst : SHAKEInstance) (hp : inst.params = shake128_params)
    (input : List (BitVec 8)) (n : ℕ) :
    (shake128_xof inst hp).eval input n = shake_xof inst input n := rfl

/-- SHAKE-256 XOF output is computed from the absorb/squeeze pipeline. -/
theorem shake256_xof_eval (inst : SHAKEInstance) (hp : inst.params = shake256_params)
    (input : List (BitVec 8)) (n : ℕ) :
    (shake256_xof inst hp).eval input n = shake_xof inst input n := rfl

end CatCrypt.Crypto.Hash.SHAKE
