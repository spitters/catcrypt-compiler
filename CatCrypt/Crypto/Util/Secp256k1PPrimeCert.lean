/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the secp256k1 base-field prime

`Nat.Prime secp256k1Plit` for `p = 2^256 - 2^32 - 977` from an inline Pratt
certificate tree checked by kernel reduction (`PrattCertificate.pratt_prime`).
Nested nodes certify the prime factors of `p - 1` above `2^20`; the factors below
`2^20` are leaves checked by trial division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.Secp256k1PPrimeCert

open CatCrypt.PrattCertificate

/-- The secp256k1 base-field prime `p = 2^256 - 2^32 - 977`, as a literal
    (definitionally equal to `Util.Secp256k1P`). -/
def secp256k1Plit : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- `Nat.Prime secp256k1Plit`, by a Pratt certificate with root witness `3`. -/
theorem secp256k1Plit_prime : Nat.Prime secp256k1Plit := by
  pratt_prime
    .node secp256k1Plit 3
        [2, 3, 7, 13441,
        .node 205115282021455665897114700593932402728804164701536103180137503955397371 10
          [2, 3, 5, 29, 31, 7723,
          .node 132896956044521568488119 6
            [2, 3,
            .node 22149492674086928081353 5
              [2, 3, 5323,
              .node 173378833005251801 6
                [2, 5, 2621, 24809,
                .node 13331831 13 [2, 5, 971, 1373]]]],
          .node 255515944373312847190720520512484175977 3
            [2, 7, 11, 1627, 2657, 4423, 41201, 96557,
            .node 7240687 3
              [2, 3,
              .node 1206781 10 [2, 3, 5, 20113]],
            .node 107590001 3 [2, 5, 7, 29, 53]]]]

end CatCrypt.Crypto.Util.Secp256k1PPrimeCert
