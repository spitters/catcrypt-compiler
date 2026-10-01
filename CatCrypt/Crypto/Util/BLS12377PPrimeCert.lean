/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BLS12-377 base-field prime `p`

`Nat.Prime bls12377Plit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division. The AUCurves Coqprime `bls12_377_prime_certif.v` is a partial
Pocklington certificate; the Lucas criterion needs the complete factorization of
`p - 1`, including its 226-bit prime factor, which the tree below certifies.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.BLS12377PPrimeCert

open CatCrypt.PrattCertificate

/-- The BLS12-377 base-field prime `p`, as a literal (definitionally equal to
    `CatCrypt.Crypto.Pairing.BLS12377PairingTowerEmit.BLS377Prime`). -/
def bls12377Plit : Nat :=
  258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177

/-- `Nat.Prime bls12377Plit`, by a Pratt certificate with root witness `15`. -/
theorem bls12377Plit_prime : Nat.Prime bls12377Plit := by
  pratt_prime
    .node bls12377Plit 15
        [2, 3, 7, 13, 53, 409, 499, 2557,
        .node 6633514200929891813 2
          [2, 19, 25537, 47521,
          .node 71924131 2 [2, 3, 5, 317, 2521]],
        .node 73387170334035996766247648424745786170238574695861388454532790956181 3
          [2, 5, 11, 23,
          .node 494527005853 5
            [2, 3, 11, 167,
            .node 22433633 3 [2, 13, 53927]],
          .node 3721412928183745004194199 13
            [2, 19,
            .node 97931919162730131689321 3
              [2, 5, 11,
              .node 222572543551659390203 2
                [2,
                .node 111286271775829695101 2
                  [2, 5, 73, 8263,
                  .node 1844934619849 14
                    [2, 3,
                    .node 76872275827 2 [2, 3, 17, 19, 23, 229, 443]]]]]],
          .node 7880826209898991662826602799 21
            [2, 3, 53,
            .node 4777599223 3 [2, 3, 11, 59, 408971],
            .node 5187222954756607 3
              [2, 3, 19,
              .node 5301089 3 [2, 13, 12743],
              .node 8583511 6 [2, 3, 5, 13, 1693]]]]]

end CatCrypt.Crypto.Util.BLS12377PPrimeCert
