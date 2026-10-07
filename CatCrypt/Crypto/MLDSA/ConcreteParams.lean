/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete ML-DSA parameter sets (FIPS 204)

The numerical constants of the three ML-DSA parameter sets of FIPS 204, Table 1, and
the polynomial ring `Rq_dsa = (ZMod 8380417)[X] / (X^256 + 1)` they share.

| Parameter Set | n   | k | l | q       | d  | eta | gamma1 | gamma2   | tau | lambda | beta | omega | Security |
|---------------|-----|---|---|---------|----|-----|--------|----------|-----|--------|------|-------|----------|
| ML-DSA-44     | 256 | 4 | 4 | 8380417 | 13 | 2   | 2^17   | (q-1)/88 | 39  | 128    | 78   | 80    | Cat 2    |
| ML-DSA-65     | 256 | 6 | 5 | 8380417 | 13 | 4   | 2^19   | (q-1)/32 | 49  | 192    | 196  | 55    | Cat 3    |
| ML-DSA-87     | 256 | 8 | 7 | 8380417 | 13 | 2   | 2^19   | (q-1)/32 | 60  | 256    | 120  | 75    | Cat 5    |

## Main definitions

* `NISTParams` — the record of the constants of one parameter set (FIPS 204,
  Table 1).
* `MLDSA44Params`, `MLDSA65Params`, `MLDSA87Params` — the three parameter sets.
* `q_dsa`, `mldsa_poly`, `Rq_dsa` — the modulus `8380417`, the polynomial
  `X^256 + 1` over `ZMod q_dsa`, and the quotient ring, built with Mathlib's
  `AdjoinRoot`.
* `DsaVec`, `DsaVecL`, `DsaMat`, `dsa_mat_vecL_mul` — vectors and matrices over
  `Rq_dsa` and the matrix-vector product.
* `pk_size`, `sk_size`, `sig_size` — byte sizes of the public key, the secret key
  and the signature, by the output lengths of `pkEncode`, `skEncode` and `sigEncode`
  (FIPS 204, Algorithms 22, 24 and 26).

## Main results

* `mldsa_q_prime` — `8380417` is prime.
* `mldsa_q_ntt_friendly` — `8380417 ≡ 1 (mod 512)`.
* `mldsa44_beta_correct`, `mldsa65_beta_correct`, `mldsa87_beta_correct` —
  `beta = tau * eta` in each parameter set.
* `mldsa44_gamma2_correct`, `mldsa65_gamma2_correct`, `mldsa87_gamma2_correct` —
  `gamma2 = (q - 1) / 88` for ML-DSA-44 and `(q - 1) / 32` for the other two.
* `mldsa44_pk_size`, `mldsa65_pk_size`, `mldsa87_pk_size` — the public keys have
  1312, 1952 and 2592 bytes.
* `mldsa44_sk_size`, `mldsa65_sk_size`, `mldsa87_sk_size` — the secret keys have
  2560, 4032 and 4896 bytes.
* `mldsa44_sig_size`, `mldsa65_sig_size`, `mldsa87_sig_size` — the signatures have
  2420, 3309 and 4627 bytes.

## References
* NIST FIPS 204 (2024), Tables 1 and 2
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.ConcreteParams

open Polynomial

/-! ## NIST Parameter Record

A plain data structure holding the numerical constants of an ML-DSA parameter set. -/

/-- Record of NIST ML-DSA parameters (FIPS 204, Table 1).

    Captures the numerical constants for each security level. -/
structure NISTParams where
  /-- Polynomial degree (always 256) -/
  n : ℕ
  /-- Module rank for public key (rows of A) -/
  k : ℕ
  /-- Module rank for secret key (columns of A) -/
  l : ℕ
  /-- Modulus -/
  q : ℕ
  /-- Secret key coefficient bound -/
  eta : ℕ
  /-- Masking vector coefficient bound (power of 2) -/
  gamma1 : ℕ
  /-- Low-order rounding range: gamma2 = (q-1)/alpha for some alpha -/
  gamma2 : ℕ
  /-- Number of nonzero challenge coefficients -/
  tau : ℕ
  /-- Signing bound: beta = tau * eta -/
  beta : ℕ
  /-- Maximum number of 1s in hint -/
  omega : ℕ
  /-- Number of bits dropped from `t` by `Power2Round` -/
  d : ℕ
  /-- Collision strength of the commitment hash `c_tilde`, in bits -/
  lambda : ℕ

/-! ## ML-DSA-44 (NIST Security Category 2) -/

/-- ML-DSA-44 parameter set (FIPS 204, Table 1).

    Security Category 2 (at least as hard as SHA-256 collision search). -/
def MLDSA44Params : NISTParams where
  n := 256
  k := 4
  l := 4
  q := 8380417
  eta := 2
  gamma1 := 2 ^ 17   -- 131072
  gamma2 := 95232     -- (q-1)/88
  tau := 39
  beta := 78          -- tau * eta = 39 * 2
  omega := 80
  d := 13
  lambda := 128

/-! ## ML-DSA-65 (NIST Security Category 3) -/

/-- ML-DSA-65 parameter set (FIPS 204, Table 1).

    Security Category 3 (at least as hard as AES-192 key search). -/
def MLDSA65Params : NISTParams where
  n := 256
  k := 6
  l := 5
  q := 8380417
  eta := 4
  gamma1 := 2 ^ 19   -- 524288
  gamma2 := 261888    -- (q-1)/32
  tau := 49
  beta := 196         -- tau * eta = 49 * 4
  omega := 55
  d := 13
  lambda := 192

/-! ## ML-DSA-87 (NIST Security Category 5) -/

/-- ML-DSA-87 parameter set (FIPS 204, Table 1).

    Security Category 5 (at least as hard as AES-256 key search). -/
def MLDSA87Params : NISTParams where
  n := 256
  k := 8
  l := 7
  q := 8380417
  eta := 2
  gamma1 := 2 ^ 19   -- 524288
  gamma2 := 261888    -- (q-1)/32
  tau := 60
  beta := 120         -- tau * eta = 60 * 2
  omega := 75
  d := 13
  lambda := 256

/-! ## Verified Arithmetic Properties -/

/-- The ML-DSA modulus 8380417 is prime. -/
theorem mldsa_q_prime : Nat.Prime 8380417 := by norm_num

/-- 8380417 is NTT-friendly: 8380417 = 1 (mod 512). -/
theorem mldsa_q_ntt_friendly : 8380417 % 512 = 1 := by decide

/-- 256 divides q - 1 (required for NTT). -/
theorem mldsa_n_divides_q_minus_one : (8380417 - 1) % 256 = 0 := by decide

/-- The polynomial degree 256 is a power of two. -/
theorem mldsa_n_power_of_two : 256 = 2 ^ 8 := by decide

/-- All three parameter sets share the same modulus. -/
theorem all_same_q :
    MLDSA44Params.q = 8380417 ∧ MLDSA65Params.q = 8380417 ∧ MLDSA87Params.q = 8380417 :=
  ⟨rfl, rfl, rfl⟩

/-- All three parameter sets share the same polynomial degree. -/
theorem all_same_n :
    MLDSA44Params.n = 256 ∧ MLDSA65Params.n = 256 ∧ MLDSA87Params.n = 256 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Beta = Tau * Eta Consistency -/

/-- ML-DSA-44: beta = tau * eta. -/
theorem mldsa44_beta_correct : MLDSA44Params.beta = MLDSA44Params.tau * MLDSA44Params.eta := by
  decide

/-- ML-DSA-65: beta = tau * eta. -/
theorem mldsa65_beta_correct : MLDSA65Params.beta = MLDSA65Params.tau * MLDSA65Params.eta := by
  decide

/-- ML-DSA-87: beta = tau * eta. -/
theorem mldsa87_beta_correct : MLDSA87Params.beta = MLDSA87Params.tau * MLDSA87Params.eta := by
  decide

/-! ## Gamma2 Consistency

gamma2 = (q-1)/alpha where alpha is a small even integer.
For ML-DSA-44: alpha = 88, so gamma2 = (8380417-1)/88 = 95232.
For ML-DSA-65/87: alpha = 32, so gamma2 = (8380417-1)/32 = 261888. -/

/-- ML-DSA-44: gamma2 = (q-1)/88. -/
theorem mldsa44_gamma2_correct :
    MLDSA44Params.gamma2 * 88 = MLDSA44Params.q - 1 := by decide

/-- ML-DSA-65: gamma2 = (q-1)/32. -/
theorem mldsa65_gamma2_correct :
    MLDSA65Params.gamma2 * 32 = MLDSA65Params.q - 1 := by decide

/-- ML-DSA-87: gamma2 = (q-1)/32. -/
theorem mldsa87_gamma2_correct :
    MLDSA87Params.gamma2 * 32 = MLDSA87Params.q - 1 := by decide

/-! ## Norm Bound Checks

The signing algorithm rejects if ||z||_infty >= gamma1 - beta. In every parameter
set `gamma1 - beta > 0` and `gamma2 > beta`. -/

/-- ML-DSA-44: gamma1 - beta > 0 (signing can succeed). -/
theorem mldsa44_signing_margin : MLDSA44Params.gamma1 > MLDSA44Params.beta := by decide

/-- ML-DSA-65: gamma1 - beta > 0. -/
theorem mldsa65_signing_margin : MLDSA65Params.gamma1 > MLDSA65Params.beta := by decide

/-- ML-DSA-87: gamma1 - beta > 0. -/
theorem mldsa87_signing_margin : MLDSA87Params.gamma1 > MLDSA87Params.beta := by decide

/-- ML-DSA-44: gamma2 > beta (low bits check can pass). -/
theorem mldsa44_lowbits_margin : MLDSA44Params.gamma2 > MLDSA44Params.beta := by decide

/-- ML-DSA-65: gamma2 > beta. -/
theorem mldsa65_lowbits_margin : MLDSA65Params.gamma2 > MLDSA65Params.beta := by decide

/-- ML-DSA-87: gamma2 > beta. -/
theorem mldsa87_lowbits_margin : MLDSA87Params.gamma2 > MLDSA87Params.beta := by decide

/-! ## Concrete Ring Rq_dsa

The ML-DSA polynomial ring: `Rq_dsa = (ZMod 8380417)[X] / (X^256 + 1)`. -/

/-- The ML-DSA modulus as a natural number. -/
abbrev q_dsa : ℕ := 8380417

instance : Fact (Nat.Prime q_dsa) := ⟨mldsa_q_prime⟩

/-- The polynomial `X^256 + 1` over `ZMod q_dsa`. -/
noncomputable def mldsa_poly : (ZMod q_dsa)[X] := X ^ 256 + 1

/-- `mldsa_poly` is monic. -/
lemma mldsa_poly_monic : mldsa_poly.Monic := by
  unfold mldsa_poly
  have : (1 : (ZMod q_dsa)[X]) = C 1 := by simp
  rw [this]
  exact monic_X_pow_add_C (1 : ZMod q_dsa) (by simp)

/-- `Rq_dsa = (ZMod 8380417)[X] / (X^256 + 1)`: the ML-DSA polynomial ring. -/
noncomputable abbrev Rq_dsa := AdjoinRoot mldsa_poly

-- Algebraic instances
noncomputable instance : CommRing Rq_dsa := AdjoinRoot.instCommRing _
noncomputable instance : DecidableEq Rq_dsa := AdjoinRoot.instDecidableEq _

-- Finiteness
instance : Module.Finite (ZMod q_dsa) Rq_dsa := mldsa_poly_monic.finite_adjoinRoot
instance : Finite Rq_dsa := Module.finite_of_finite (ZMod q_dsa)
noncomputable instance : Fintype Rq_dsa := Fintype.ofFinite Rq_dsa
instance : Nonempty Rq_dsa := ⟨0⟩

/-! ## Concrete Vector and Matrix Types -/

/-- k-dimensional vector over Rq_dsa. -/
abbrev DsaVec (k : ℕ) := Fin k → Rq_dsa

/-- l-dimensional vector over Rq_dsa. -/
abbrev DsaVecL (l : ℕ) := Fin l → Rq_dsa

/-- k x l matrix over Rq_dsa. -/
abbrev DsaMat (k l : ℕ) := Fin k → Fin l → Rq_dsa

/-! ## Concrete Operations -/

/-- Matrix-vector multiplication for ML-DSA: A (k x l) * v (l) -> w (k). -/
noncomputable def dsa_mat_vecL_mul (k l : ℕ) (A : DsaMat k l) (v : DsaVecL l) : DsaVec k :=
  fun i => ∑ j, A i j * v j

/-- k-vector addition. -/
noncomputable def dsa_vec_add (k : ℕ) (u v : DsaVec k) : DsaVec k :=
  fun i => u i + v i

/-- k-vector subtraction. -/
noncomputable def dsa_vec_sub (k : ℕ) (u v : DsaVec k) : DsaVec k :=
  fun i => u i - v i

/-- l-vector addition. -/
noncomputable def dsa_vecL_add (l : ℕ) (u v : DsaVecL l) : DsaVecL l :=
  fun i => u i + v i

/-! ## Signature and Key Sizes

Sizes in bytes. Each formula is the output length that FIPS 204 states for the
corresponding encoding algorithm: `pkEncode` (Algorithm 22), `skEncode` (Algorithm 24)
and `sigEncode` (Algorithm 26). The theorems below evaluate each formula at the three
parameter sets and obtain the entries of FIPS 204, Table 2, which are the check of the
formulas. The bit length `bitlen a` of the standard is `Nat.size a`. -/

/-- Public key size in bytes, the output length of `pkEncode` (FIPS 204, Algorithm 22):
the 32-byte seed `rho` and the `k` polynomials of `t1`, each of 256 coefficients of
`bitlen (q - 1) - d` bits. -/
def pk_size (p : NISTParams) : ℕ := 32 + 32 * p.k * (Nat.size (p.q - 1) - p.d)

/-- Secret key size in bytes, the output length of `skEncode` (FIPS 204, Algorithm 24):
`rho` (32 bytes), `K` (32 bytes), `tr` (64 bytes), the `l + k` polynomials of `s1` and
`s2` with `bitlen (2 * eta)` bits per coefficient, and the `k` polynomials of `t0` with
`d` bits per coefficient. -/
def sk_size (p : NISTParams) : ℕ :=
  32 + 32 + 64 + 32 * ((p.l + p.k) * Nat.size (2 * p.eta) + p.d * p.k)

/-- Signature size in bytes, the output length of `sigEncode` (FIPS 204, Algorithm 26):
the commitment hash `c_tilde` of `lambda / 4` bytes, the `l` polynomials of `z` with
`1 + bitlen (gamma1 - 1)` bits per coefficient, and the hint encoding of `omega + k`
bytes. -/
def sig_size (p : NISTParams) : ℕ :=
  p.lambda / 4 + p.l * 32 * (1 + Nat.size (p.gamma1 - 1)) + p.omega + p.k

/-- ML-DSA-44 public key is 1312 bytes. -/
theorem mldsa44_pk_size : pk_size MLDSA44Params = 1312 := by decide

/-- ML-DSA-65 public key is 1952 bytes. -/
theorem mldsa65_pk_size : pk_size MLDSA65Params = 1952 := by decide

/-- ML-DSA-87 public key is 2592 bytes. -/
theorem mldsa87_pk_size : pk_size MLDSA87Params = 2592 := by decide

/-- ML-DSA-44 secret key is 2560 bytes. -/
theorem mldsa44_sk_size : sk_size MLDSA44Params = 2560 := by decide

/-- ML-DSA-65 secret key is 4032 bytes. -/
theorem mldsa65_sk_size : sk_size MLDSA65Params = 4032 := by decide

/-- ML-DSA-87 secret key is 4896 bytes. -/
theorem mldsa87_sk_size : sk_size MLDSA87Params = 4896 := by decide

/-- ML-DSA-44 signature is 2420 bytes. -/
theorem mldsa44_sig_size : sig_size MLDSA44Params = 2420 := by decide

/-- ML-DSA-65 signature is 3309 bytes. -/
theorem mldsa65_sig_size : sig_size MLDSA65Params = 3309 := by decide

/-- ML-DSA-87 signature is 4627 bytes. -/
theorem mldsa87_sig_size : sig_size MLDSA87Params = 4627 := by decide

end CatCrypt.Crypto.MLDSA.ConcreteParams
