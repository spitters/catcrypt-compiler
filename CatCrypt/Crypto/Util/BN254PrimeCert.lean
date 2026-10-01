/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BN254 (alt-bn128) base-field prime

`Nat.Prime bn254lit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). The base-field prime is
`p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`
(EIP-196 / EIP-197 alt-bn128, `y² = x³ + 3`). Nested nodes certify the prime
factors of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by
trial division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.BN254PrimeCert

open CatCrypt.PrattCertificate

/-- The certified prime `21888242871839275222246405745257275088696311157297823662689037894645226208583`
    (`254`-bit), the BN254 base-field modulus (definitionally equal to
    `CatCrypt.Util.BN254`).
    `N - 1 = 2 · 3^2 · 13 · 29 · 67 · 229 · 311 · 983 · 11003 · 405928799 · 11465965001 · 13427688667394608761327070753331941386769`. -/
def bn254lit : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- `Nat.Prime bn254lit`, by a Pratt certificate with root witness `3`. -/
theorem bn254lit_prime : Nat.Prime bn254lit := by
  pratt_prime
    .node bn254lit 3
        [2, 3, 13, 29, 67, 229, 311, 983, 11003,
        .node 405928799 22 [2, 11, 3691, 4999],
        .node 11465965001 3 [2, 5, 7, 327599],
        .node 13427688667394608761327070753331941386769 17
          [2, 3, 7, 11,
          .node 1853641 17 [2, 3, 5, 19, 271],
          .node 4562087 5 [2, 17, 109, 1231],
          .node 173171039 13 [2, 73, 89, 13327],
          .node 2480874801745591 6
            [2, 3, 5, 19, 41,
            .node 35385462869 2
              [2, 7,
              .node 1263766531 10 [2, 3, 5, 13, 911, 3557]]]]]

end CatCrypt.Crypto.Util.BN254PrimeCert
