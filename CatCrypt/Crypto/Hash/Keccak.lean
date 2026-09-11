/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CryptoWord

/-!
# Keccak Permutation (FIPS 202)

Formalizes the Keccak-f[1600] permutation used as the core primitive in SHA-3.
The permutation operates on a 5x5x64-bit state (1600 bits total) and applies
24 rounds of the five step mappings: theta, rho, pi, chi, iota.

## Architecture

The formalization is parameterized over the state type and permutation functions.
Concrete Keccak round constants are provided, but the step mapping implementations
are kept abstract since the security proofs only depend on the permutation being
a good pseudorandom permutation, not on its internal structure.

## Main definitions

* `KeccakState` -- the 1600-bit permutation state
* `KeccakParams` -- parameters: rate, capacity, rounds
* `keccak_round_constant` -- the 24 iota round constants (RC[i])
* `KeccakStepMappings` -- the five step mappings: theta, rho, pi, chi, iota
* `keccak_round` -- single round: theta >> rho >> pi >> chi >> iota
* `keccak_f` -- full 24-round permutation
* `KeccakPermutation` -- bundled permutation with inverse and correctness

## Security model

The security of SHA-3 constructions relies on Keccak-f being modeled as a
random permutation. The `RPAssumption` in `Security.lean` captures this.

## References

* [FIPS 202 -- SHA-3 Standard, NIST 2015]
* [Keccak Reference, Bertoni-Daemen-Peeters-Van Assche, 2011]

**0 axioms**, **0 sorries**.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.Keccak

/-! ## State Type -/

/-- The Keccak-f[1600] state: 1600 bits organized as 5 x 5 lanes of 64 bits. -/
abbrev KeccakState := BitVec 1600

/-! ## Parameters -/

/-- Keccak sponge parameters.

    - `rate`: number of bits absorbed per block
    - `capacity`: number of capacity bits (security parameter)
    - `rounds`: number of permutation rounds (24 for Keccak-f[1600])
    - `wf`: well-formedness: rate + capacity = 1600 -/
structure KeccakParams where
  /-- Rate in bits. -/
  rate : ℕ
  /-- Capacity in bits. -/
  capacity : ℕ
  /-- Number of rounds. -/
  rounds : ℕ
  /-- Well-formedness: rate + capacity = 1600. -/
  wf : rate + capacity = 1600

/-! ## Round Constants -/

/-- The 24 Keccak iota round constants RC[i] from FIPS 202 Table 2.

    Derived from a linear feedback shift register over GF(2). -/
def keccak_round_constant (i : Fin 24) : BitVec 64 :=
  match i.val with
  |  0 => 0x0000000000000001 |  1 => 0x0000000000008082
  |  2 => 0x800000000000808A |  3 => 0x8000000080008000
  |  4 => 0x000000000000808B |  5 => 0x0000000080000001
  |  6 => 0x8000000080008081 |  7 => 0x8000000000008009
  |  8 => 0x000000000000008A |  9 => 0x0000000000000088
  | 10 => 0x0000000080008009 | 11 => 0x000000008000000A
  | 12 => 0x000000008000808B | 13 => 0x800000000000008B
  | 14 => 0x8000000000008089 | 15 => 0x8000000000008003
  | 16 => 0x8000000000008002 | 17 => 0x8000000000000080
  | 18 => 0x000000000000800A | 19 => 0x800000008000000A
  | 20 => 0x8000000080008081 | 21 => 0x8000000000008080
  | 22 => 0x0000000080000001 | 23 => 0x8000000080008008
  |  _ => 0

/-! ## Abstract Step Mappings -/

/-- Abstract Keccak step mapping bundle.

    The five step mappings are bundled as abstract functions on `KeccakState`.
    This allows security proofs to work without concrete bit-manipulation. -/
structure KeccakStepMappings where
  /-- Theta step: XOR each bit with parity of two neighboring columns. -/
  theta : KeccakState → KeccakState
  /-- Rho step: rotate each lane by a fixed offset. -/
  rho : KeccakState → KeccakState
  /-- Pi step: rearrange positions of the 25 lanes. -/
  pi : KeccakState → KeccakState
  /-- Chi step: nonlinear mapping applied row-by-row. -/
  chi : KeccakState → KeccakState
  /-- Iota step: XOR round constant into lane (0,0). -/
  iota : KeccakState → Fin 24 → KeccakState

/-! ## Round and Full Permutation -/

/-- A single Keccak round: apply the five step mappings in order. -/
def keccak_round (steps : KeccakStepMappings) (state : KeccakState)
    (roundIdx : Fin 24) : KeccakState :=
  steps.iota (steps.chi (steps.pi (steps.rho (steps.theta state)))) roundIdx

/-- Apply n rounds of Keccak starting from round index `start`. -/
def keccak_rounds (steps : KeccakStepMappings) (state : KeccakState)
    (start : ℕ) : ℕ → KeccakState
  | 0 => state
  | n + 1 =>
    if h : start < 24 then
      keccak_rounds steps (keccak_round steps state ⟨start, h⟩) (start + 1) n
    else state

/-- The full Keccak-f[1600] permutation: 24 rounds. -/
def keccak_f (steps : KeccakStepMappings) (state : KeccakState) : KeccakState :=
  keccak_rounds steps state 0 24

/-! ## Bundled Permutation -/

/-- Abstract permutation on KeccakState with forward and inverse. -/
structure KeccakPerm where
  fwd : KeccakState → KeccakState
  inv : KeccakState → KeccakState

/-- Correctness: inv is the two-sided inverse of fwd. -/
def KeccakPerm.Correct (P : KeccakPerm) : Prop :=
  (∀ s, P.inv (P.fwd s) = s) ∧ (∀ s, P.fwd (P.inv s) = s)

/-- A Keccak permutation bundled with step mappings and correctness. -/
structure KeccakPermutation where
  steps : KeccakStepMappings
  inv : KeccakState → KeccakState
  inv_left : ∀ s, inv (keccak_f steps s) = s
  inv_right : ∀ s, keccak_f steps (inv s) = s

/-- Convert to KeccakPerm. -/
def KeccakPermutation.toPerm (K : KeccakPermutation) : KeccakPerm where
  fwd := keccak_f K.steps
  inv := K.inv

/-- The permutation from a KeccakPermutation is correct. -/
theorem KeccakPermutation.correct (K : KeccakPermutation) :
    K.toPerm.Correct :=
  ⟨K.inv_left, K.inv_right⟩

/-! ## Standard Parameter Sets -/

/-- SHA3-256 parameters: rate = 1088, capacity = 512, 24 rounds. -/
def sha3_256_params : KeccakParams where
  rate := 1088; capacity := 512; rounds := 24; wf := by omega

/-- SHA3-512 parameters: rate = 576, capacity = 1024, 24 rounds. -/
def sha3_512_params : KeccakParams where
  rate := 576; capacity := 1024; rounds := 24; wf := by omega

/-- SHAKE-128 Keccak parameters: rate = 1344, capacity = 256, 24 rounds. -/
def shake128_keccak_params : KeccakParams where
  rate := 1344; capacity := 256; rounds := 24; wf := by omega

/-- SHAKE-256 Keccak parameters: rate = 1088, capacity = 512, 24 rounds. -/
def shake256_keccak_params : KeccakParams where
  rate := 1088; capacity := 512; rounds := 24; wf := by omega

/-! ## Basic Properties -/

theorem sha3_256_rate_pos : (1088 : ℕ) = sha3_256_params.rate := by
  simp [sha3_256_params]

theorem sha3_256_capacity_pos : (512 : ℕ) = sha3_256_params.capacity := by
  simp [sha3_256_params]

/-- Round function applied 0 times is the identity. -/
theorem keccak_rounds_zero (steps : KeccakStepMappings) (state : KeccakState)
    (start : ℕ) : keccak_rounds steps state start 0 = state := rfl

/-- SHA3-256 and SHA3-512 have different rates. -/
theorem sha3_256_neq_512 : sha3_256_params.rate ≠ sha3_512_params.rate := by
  simp [sha3_256_params, sha3_512_params]

/-- SHAKE-128 and SHAKE-256 have different capacities. -/
theorem shake128_neq_256_capacity :
    shake128_keccak_params.capacity ≠ shake256_keccak_params.capacity := by
  simp [shake128_keccak_params, shake256_keccak_params]

end CatCrypt.Crypto.Hash.Keccak
