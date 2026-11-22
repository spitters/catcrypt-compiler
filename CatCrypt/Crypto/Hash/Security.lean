/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.KMAC
public import CatCryptCore.Crypto.UC

/-!
# SHAKE: capacities and birthday expressions

The expression `ε_rp + q^2/2^c` at the capacities 256 and 512 of SHAKE-128 and
SHAKE-256, the arithmetic of `q^2/2^c`, and the SHAKE parameters that the NIST
PQC standards use.

The theorems are about numbers and parameters. They contain no game: `ε_rp` is
a free number, and no theorem in this file relates SHAKE, Keccak-f or a
sponge to a random oracle or states a security property of a hash function.

## Main definitions

* `sponge_indiff_bound` -- the number `q^2/2^c`
* `shake128_rom_bound`, `shake256_rom_bound` -- the expression at each capacity
* `PQCHashUsage` -- the SHAKE parameters of a PQC scheme, per role

## References

* [FIPS 202 -- SHA-3 Standard, NIST 2015]
* [Bertoni, Daemen, Peeters, Van Assche -- CRYPTO 2008]
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Hash.SHAKE
open CatCrypt.Crypto.Hash.CSHAKE
open CatCrypt.Crypto.Hash.KMAC
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.Security

/-! ## Capacity birthday expression -/

/-- The number `q^2 / 2^c`, for `q` queries and `c` capacity bits.

    It has the shape of the sponge indifferentiability bound of Bertoni et al.
    (CRYPTO 2008). No theorem in this package relates it to a sponge game. -/
noncomputable def sponge_indiff_bound (numQueries : ℕ) (capacityBits : ℕ) : ℝ≥0∞ :=
  (numQueries * numQueries : ℕ) / (2 ^ capacityBits : ℕ)

/-- The indifferentiability bound is monotone in queries. -/
theorem sponge_indiff_bound_mono {q₁ q₂ : ℕ} (h : q₁ ≤ q₂) (c : ℕ) :
    sponge_indiff_bound q₁ c ≤ sponge_indiff_bound q₂ c := by
  unfold sponge_indiff_bound; gcongr

/-- Zero queries give zero indifferentiability bound. -/
theorem sponge_indiff_bound_zero (c : ℕ) :
    sponge_indiff_bound 0 c = 0 := by
  unfold sponge_indiff_bound; simp

/-- The indifferentiability bound is anti-monotone in capacity. -/
theorem sponge_indiff_bound_capacity_mono {c₁ c₂ : ℕ} (hle : c₁ ≤ c₂) (q : ℕ) :
    sponge_indiff_bound q c₂ ≤ sponge_indiff_bound q c₁ := by
  unfold sponge_indiff_bound
  apply ENNReal.div_le_div_left
  exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hle

/-! ## The expression at the SHAKE capacities -/

/-- The number `ε_rp + q^2 / 2^256`, at the capacity of SHAKE-128. The
    parameter `ε_rp` is a free number. -/
noncomputable def shake128_rom_bound (ε_rp : ℝ≥0∞) (numQueries : ℕ) : ℝ≥0∞ :=
  ε_rp + sponge_indiff_bound numQueries 256

/-- The number `ε_rp + q^2 / 2^512`, at the capacity of SHAKE-256. The
    parameter `ε_rp` is a free number. -/
noncomputable def shake256_rom_bound (ε_rp : ℝ≥0∞) (numQueries : ℕ) : ℝ≥0∞ :=
  ε_rp + sponge_indiff_bound numQueries 512

/-- The expression at capacity 512 is at most the expression at capacity 256. -/
theorem shake256_stronger_than_128 (ε_rp : ℝ≥0∞) (q : ℕ) :
    shake256_rom_bound ε_rp q ≤ shake128_rom_bound ε_rp q := by
  unfold shake256_rom_bound shake128_rom_bound
  gcongr
  exact sponge_indiff_bound_capacity_mono (by omega) q

/-! ## Interface record -/

/-- A `UCSpec` record with byte strings at the honest, output, leak and
    simulator interfaces. This file defines no protocol and no functionality
    over it. -/
noncomputable def HashUCSpec (V : Type) : UCSpec where
  hon := List (BitVec 8)
  out := List (BitVec 8)
  leak := List (BitVec 8)
  sim_if := List (BitVec 8)
  view := V

/-! ## PQC Hash Instantiation -/

/-- PQC hash usage specification.

    Records which SHAKE variant is used for each role in a PQC scheme. -/
structure PQCHashUsage where
  /-- Primary hash function (e.g., H in ML-KEM). -/
  primaryHash : SHAKEParams
  /-- Key derivation / PRF function (e.g., G in ML-KEM). -/
  kdfHash : SHAKEParams
  /-- XOF for matrix expansion (e.g., XOF in ML-KEM). -/
  xofHash : SHAKEParams

/-- ML-KEM hash instantiation (FIPS 203).

    - H (primary hash): SHAKE-128 (Section 4.1)
    - G (key derivation): SHAKE-256 (Section 4.1)
    - XOF (matrix expansion): SHAKE-128 (Section 4.1)
    - PRF: SHAKE-256 (Section 4.1) -/
def mlkem_hash_usage : PQCHashUsage where
  primaryHash := shake128_params
  kdfHash := shake256_params
  xofHash := shake128_params

/-- ML-DSA hash instantiation (FIPS 204).

    ML-DSA uses SHAKE-256 for all hash functions:
    - H (challenge hash): SHAKE-256
    - ExpandA: SHAKE-128
    - ExpandS / ExpandMask: SHAKE-256 -/
def mldsa_hash_usage : PQCHashUsage where
  primaryHash := shake256_params
  kdfHash := shake256_params
  xofHash := shake128_params

/-- SLH-DSA hash instantiation (FIPS 205).

    SLH-DSA uses SHAKE-256 for all internal functions. -/
def slhdsa_hash_usage : PQCHashUsage where
  primaryHash := shake256_params
  kdfHash := shake256_params
  xofHash := shake256_params

/-- ML-KEM minimum capacity is 256 (from SHAKE-128). -/
theorem mlkem_min_capacity :
    min (min mlkem_hash_usage.primaryHash.capacity
             mlkem_hash_usage.kdfHash.capacity)
        mlkem_hash_usage.xofHash.capacity = 256 := by
  simp [mlkem_hash_usage, shake128_params, shake256_params]

/-- ML-DSA minimum capacity is 256 (from SHAKE-128 in ExpandA). -/
theorem mldsa_min_capacity :
    min (min mldsa_hash_usage.primaryHash.capacity
             mldsa_hash_usage.kdfHash.capacity)
        mldsa_hash_usage.xofHash.capacity = 256 := by
  simp [mldsa_hash_usage, shake128_params, shake256_params]

/-- SLH-DSA minimum capacity is 512 (all SHAKE-256). -/
theorem slhdsa_min_capacity :
    min (min slhdsa_hash_usage.primaryHash.capacity
             slhdsa_hash_usage.kdfHash.capacity)
        slhdsa_hash_usage.xofHash.capacity = 512 := by
  simp [slhdsa_hash_usage, shake256_params]

end CatCrypt.Crypto.Hash.Security
