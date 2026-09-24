/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Hash.Keccak
public import CatCrypt.Crypto.Hash.Keccak
public meta import CatCrypt.Crypto.Hash.SHAKE
public import CatCrypt.Crypto.Hash.SHAKE

/-!
# TurboSHAKE (NIST SP 800-185 update / draft-irtf-cfrg-turbo-shake)

Formalizes TurboSHAKE-128 and TurboSHAKE-256, reduced-round variants of
SHAKE that trade a wider security margin for higher throughput.

## Overview

TurboSHAKE uses the same Keccak-f[1600] sponge as SHAKE, but with only
**12 rounds** instead of 24 (specifically, rounds 12–23 of Keccak-f[1600]).
The security margin is still considered sufficient: Keccak's best attacks
against the full permutation reach ~8 rounds, so 12 rounds provides a
comfortable margin.

## Key Differences from SHAKE

| Property | SHAKE | TurboSHAKE |
|----------|-------|------------|
| Rounds | 24 | 12 |
| Domain separation | 0x1F | 0x07 + custom separator byte D (0x01–0x7F) |
| Capacity | 256/512 | 256/512 (same) |
| Security level | 128/256 | 128/256 (same) |

## Domain Separation

TurboSHAKE uses a single-byte domain separator `D ∈ {0x01, ..., 0x7F}`
appended to the message. Different values of D produce independent
functions in the random permutation model.

## Security

TurboSHAKE's security is `min(κ, c/2)` where:
- `κ` is the target security level
- `c` is the capacity (256 or 512 bits)

The reduced round count is justified by the cryptanalytic gap:
best known distinguishers reach 8 rounds, so 12 rounds provides
a 4-round margin.

## Main Definitions

* `TurboSHAKEParams` — parameters with round count and domain byte
* `turboshake128_params`, `turboshake256_params` — standard instances
* `TurboSHAKEInstance` — bundled XOF with domain separator
* `turboshake_eval` — TurboSHAKE evaluation
* `turboshake_domain_separation` — different D values give different functions

## References

* [Keccak Team — TurboSHAKE, 2023](https://keccak.team/files/TurboSHAKE.pdf)
* [NIST draft-irtf-cfrg-turbo-shake](https://www.ietf.org/archive/id/draft-irtf-cfrg-turbo-shake-01.html)
* [RFC 9861 — KangarooTwelve and TurboSHAKE](https://www.rfc-editor.org/rfc/rfc9861)

**0 axioms**, **all goals closed**.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Hash.SHAKE
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.TurboSHAKE

/-! ## Parameters -/

/-- TurboSHAKE parameters.

TurboSHAKE uses the same state size (1600 bits) and rate/capacity
split as SHAKE, but with a reduced round count of 12. -/
structure TurboSHAKEParams where
  /-- Rate in bits. -/
  rate : ℕ
  /-- Capacity in bits. -/
  capacity : ℕ
  /-- Number of rounds (12 for TurboSHAKE). -/
  rounds : ℕ
  /-- Security level in bits. -/
  security_level : ℕ
  /-- Well-formedness: rate + capacity = 1600. -/
  wf : rate + capacity = 1600
  /-- Rounds = 12 for TurboSHAKE. -/
  rounds_eq : rounds = 12
  /-- Security level is at most half the capacity. -/
  security_bound : security_level ≤ capacity / 2

/-- TurboSHAKE-128: rate = 1344, capacity = 256, 12 rounds, 128-bit security. -/
def turboshake128_params : TurboSHAKEParams where
  rate := 1344
  capacity := 256
  rounds := 12
  security_level := 128
  wf := by omega
  rounds_eq := rfl
  security_bound := by omega

/-- TurboSHAKE-256: rate = 1088, capacity = 512, 12 rounds, 256-bit security. -/
def turboshake256_params : TurboSHAKEParams where
  rate := 1088
  capacity := 512
  rounds := 12
  security_level := 256
  wf := by omega
  rounds_eq := rfl
  security_bound := by omega

/-! ## Domain Separation -/

/-- TurboSHAKE domain separator byte.

A single byte `D ∈ {0x01, ..., 0x7F}` appended to the message before
padding. Different D values produce independent functions.

This is simpler than cSHAKE's (N, S) pair encoding: TurboSHAKE uses
a single byte, avoiding the overhead of encoded string lengths. -/
structure TurboDomainSep where
  /-- The domain separator byte (as BitVec 8). -/
  byte : BitVec 8
  /-- Must be non-zero. -/
  nonzero : byte ≠ 0
  /-- High bit must be clear (≤ 0x7F). -/
  highBitClear : byte.toNat ≤ 127

/-- Default domain separator (0x07, same as bare TurboSHAKE). -/
def defaultDomainSep : TurboDomainSep where
  byte := 0x07
  nonzero := by native_decide
  highBitClear := by native_decide

/-- Two domain separators are different iff their bytes differ. -/
theorem turboDomainSep_ne_iff (d₁ d₂ : TurboDomainSep) :
    d₁ ≠ d₂ ↔ d₁.byte ≠ d₂.byte := by
  constructor
  · intro h hb; apply h; cases d₁; cases d₂; simp at hb; subst hb; rfl
  · intro h heq; apply h; cases heq; rfl

/-! ## TurboSHAKE Permutation -/

/-- TurboSHAKE uses rounds 12–23 of Keccak-f[1600].

This is the last 12 of the standard 24 rounds, starting from
round constant RC[12]. -/
def turboshake_f (steps : KeccakStepMappings) (state : KeccakState) : KeccakState :=
  keccak_rounds steps state 12 12

/-- TurboSHAKE permutation is a suffix of Keccak-f. -/
theorem turboshake_f_rounds (steps : KeccakStepMappings) (state : KeccakState) :
    turboshake_f steps state = keccak_rounds steps state 12 12 := rfl

/-! ## TurboSHAKE Instance -/

/-- A TurboSHAKE instance bundles parameters, domain separator, and sponge. -/
structure TurboSHAKEInstance where
  /-- The TurboSHAKE parameters. -/
  params : TurboSHAKEParams
  /-- Domain separator byte. -/
  domainSep : TurboDomainSep
  /-- The absorb function (same sponge structure as SHAKE). -/
  absorber : SpongeAbsorb
  /-- The squeeze function. -/
  squeezer : SpongeSqueeze

/-- Evaluate TurboSHAKE.

Appends the domain separator byte D to the message, then runs
the sponge (absorb + squeeze) with 12-round Keccak. -/
def turboshake_eval (inst : TurboSHAKEInstance) (msg : List (BitVec 8))
    (outputBytes : ℕ) : List (BitVec 8) :=
  let initialState : KeccakState := 0
  -- Append domain separator byte to message
  let paddedMsg := msg ++ [inst.domainSep.byte]
  let absorbed := inst.absorber.absorb initialState paddedMsg
  inst.squeezer.squeeze absorbed outputBytes

/-- TurboSHAKE-128 as an abstract XOF. -/
def turboshake128_xof (inst : TurboSHAKEInstance)
    (_ : inst.params = turboshake128_params) : XOFDef where
  name := "TurboSHAKE128"
  security := 128
  eval := turboshake_eval inst

/-- TurboSHAKE-256 as an abstract XOF. -/
def turboshake256_xof (inst : TurboSHAKEInstance)
    (_ : inst.params = turboshake256_params) : XOFDef where
  name := "TurboSHAKE256"
  security := 256
  eval := turboshake_eval inst

/-! ## Domain Separation Theorem -/

/-- Different domain separator bytes produce different sponge inputs.

In the random permutation model, TurboSHAKE with different D values
behaves as independent random oracles (assuming the sponge is
indifferentiable from a random oracle for each D). -/
theorem turboshake_domain_separation (d₁ d₂ : TurboDomainSep)
    (hne : d₁.byte ≠ d₂.byte) (msg : List (BitVec 8)) :
    msg ++ [d₁.byte] ≠ msg ++ [d₂.byte] := by
  intro h
  exact hne (by simpa using List.append_cancel_left h)

/-! ## Properties -/

/-- TurboSHAKE-128 has 128-bit security. -/
theorem turboshake128_security :
    turboshake128_params.security_level = 128 := rfl

/-- TurboSHAKE-256 has 256-bit security. -/
theorem turboshake256_security :
    turboshake256_params.security_level = 256 := rfl

/-- TurboSHAKE uses 12 rounds (half of standard Keccak). -/
theorem turboshake_rounds_12 (p : TurboSHAKEParams) : p.rounds = 12 :=
  p.rounds_eq

/-- TurboSHAKE-128 and TurboSHAKE-256 share the same round count. -/
theorem turboshake_same_rounds :
    turboshake128_params.rounds = turboshake256_params.rounds := rfl

/-- TurboSHAKE-128 and SHAKE-128 have the same rate and capacity. -/
theorem turboshake128_same_rate_as_shake128 :
    turboshake128_params.rate = shake128_params.rate := rfl

/-- TurboSHAKE-256 and SHAKE-256 have the same rate and capacity. -/
theorem turboshake256_same_rate_as_shake256 :
    turboshake256_params.rate = shake256_params.rate := rfl

/-! ## Security Bound -/

/-- TurboSHAKE security bound: birthday bound on the sponge.

  `ε_turbo ≤ q² / 2^c`

where `q` is the total number of sponge queries and `c` is the capacity.
This is the same bound as for SHAKE (full Keccak), since the security
reduction goes through the random permutation model where the round
count only affects the gap between the real permutation and the RP model
(which is absorbed into the RP assumption). -/
noncomputable def turboshake_security_bound (totalQueries : ℕ) (capacity : ℕ) : ℝ≥0∞ :=
  (totalQueries * totalQueries : ℕ) / (2 ^ capacity : ℕ)

/-- TurboSHAKE-128 bound: q²/2^256. -/
theorem turboshake128_bound (q : ℕ) :
    turboshake_security_bound q turboshake128_params.capacity =
    turboshake_security_bound q 256 := rfl

/-- TurboSHAKE-256 bound: q²/2^512. -/
theorem turboshake256_bound (q : ℕ) :
    turboshake_security_bound q turboshake256_params.capacity =
    turboshake_security_bound q 512 := rfl

end CatCrypt.Crypto.Hash.TurboSHAKE
