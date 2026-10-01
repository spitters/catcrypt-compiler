/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BLS12-381 base-field prime `p`

`Nat.Prime bls12381Plit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.BLS12381PPrimeCert

open CatCrypt.PrattCertificate

/-- The BLS12-381 `G1` base-field prime `p`, as a literal (definitionally equal to
    `CatCrypt.Util.BLS12381`). -/
def bls12381Plit : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- `Nat.Prime bls12381Plit`, by a Pratt certificate with root witness `2`. -/
theorem bls12381Plit_prime : Nat.Prime bls12381Plit := by
  pratt_prime
    .node bls12381Plit 2
        [2, 3, 11, 23, 47, 10177, 859267,
        .node 52437899 2 [2, 43, 609743],
        .node 2584487767265781317813 2
          [2, 89,
          .node 7259797099061183477 2
            [2, 941,
            .node 1928745244171409 3
              [2, 13,
              .node 9272813673901 2 [2, 3, 5, 7, 7577, 582767]]]],
        .node 15778400344354997994418419698270088123916926905054652752758194827714659 2
          [2, 3, 53,
          .node 475709467 2
            [2, 3, 47,
            .node 1686913 10 [2, 3, 23, 191]],
          .node 92691255082156974996979 3
            [2, 3, 31, 467, 16447,
            .node 64881703735777 5
              [2, 3,
              .node 927093389 3 [2, 13, 409, 43591]]],
          .node 1125266252156850182658904441386709967 5
            [2, 3373,
            .node 43670061551 7
              [2, 5, 17,
              .node 51376543 3 [2, 3, 7, 151, 8101]],
            .node 3819663927398918131021 6
              [2, 3, 5, 19, 113, 755057,
              .node 13090036741 10 [2, 3, 5, 11, 47, 421987]]]]]

end CatCrypt.Crypto.Util.BLS12381PPrimeCert
