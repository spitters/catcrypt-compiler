/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the secp256k1 group order

`Nat.Prime secp256k1Nlit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `n - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.Secp256k1NPrimeCert

open CatCrypt.PrattCertificate

/-- The secp256k1 group order `n`, as a literal (definitionally equal to
    `Util.Secp256k1N`). -/
def secp256k1Nlit : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- `Nat.Prime secp256k1Nlit`, by a Pratt certificate with root witness `7`. -/
theorem secp256k1Nlit_prime : Nat.Prime secp256k1Nlit := by
  pratt_prime
    .node secp256k1Nlit 7
        [2, 3, 149, 631,
        .node 107361793816595537 3
          [2, 16699, 85831,
          .node 4681609 23 [2, 3, 97, 2011]],
        .node 174723607534414371449 3
          [2, 17, 59, 4051, 120233,
          .node 44706919 6 [2, 3, 797, 9349]],
        .node 341948486974166000522343609283189 2
          [2, 3, 109,
          .node 29047611873442575647497758179 2
            [2, 293, 305873,
            .node 545358713 5 [2, 41, 59, 28181],
            .node 297159362677 2
              [2, 3, 11, 461,
              .node 1627771 3 [2, 3, 5, 29, 1871]]]]]

end CatCrypt.Crypto.Util.Secp256k1NPrimeCert
