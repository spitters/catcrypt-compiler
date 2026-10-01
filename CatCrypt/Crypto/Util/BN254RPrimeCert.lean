/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BN254 scalar-field order `r`

`Nat.Prime bn254Rlit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). The scalar-field prime is
`r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`
(alt-bn128 / EIP-196 `Fr`, 2-adicity 28). Nested nodes certify the prime factors
of `r - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.BN254RPrimeCert

open CatCrypt.PrattCertificate

/-- The certified prime `21888242871839275222246405745257275088548364400416034343698204186575808495617`
    (`254`-bit), the BN254 scalar-field order `r` (definitionally equal to
    `CatCrypt.Crypto.ECDSA.BN254GroupParam.BN254R`).
    `N - 1 = 2^28 · 3^2 · 13 · 29 · 983 · 11003 · 237073 · 405928799 · 1670836401704629 · 13818364434197438864469338081`. -/
def bn254Rlit : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- `Nat.Prime bn254Rlit`, by a Pratt certificate with root witness `5`. -/
theorem bn254Rlit_prime : Nat.Prime bn254Rlit := by
  pratt_prime
    .node bn254Rlit 5
        [2, 3, 13, 29, 983, 11003, 237073,
        .node 405928799 22 [2, 11, 3691, 4999],
        .node 1670836401704629 2
          [2, 3,
          .node 5156902474397 2
            [2, 107,
            .node 12048837557 2 [2, 7, 661, 93001]]],
        .node 13818364434197438864469338081 3
          [2, 5, 823,
          .node 1593227 2 [2, 19, 41927],
          .node 65865678001877903 5
            [2, 83, 379, 1637,
            .node 639533339 2 [2, 229, 853, 1637]]]]

end CatCrypt.Crypto.Util.BN254RPrimeCert
