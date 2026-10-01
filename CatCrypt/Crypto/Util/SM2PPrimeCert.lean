/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the SM2 base-field prime

`Nat.Prime sm2Plit`, where `sm2Plit` is the SM2 base-field prime
`2^256 - 2^224 - 2^96 + 2^64 - 1` (GB/T 32918.5), from an inline Pratt certificate
tree checked by kernel reduction (`PrattCertificate.pratt_prime`). Nested nodes
certify the prime factors of `p - 1` above `2^20`; the factors below `2^20` are
leaves checked by trial division.

## Main results

* `sm2Plit_prime`: `Nat.Prime sm2Plit`.
* `sm2Plit_eq`: `sm2Plit = 2^256 - 2^224 - 2^96 + 2^64 - 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.SM2PPrimeCert

open CatCrypt.PrattCertificate

/-- The SM2 base-field prime `2^256 - 2^224 - 2^96 + 2^64 - 1`, as a literal. -/
def sm2Plit : Nat :=
  0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF

/-- The literal `sm2Plit` is the SM2 base-prime expression. -/
theorem sm2Plit_eq : sm2Plit = 2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1 := by decide

/-- `Nat.Prime sm2Plit`, by a Pratt certificate with root witness `13`. -/
theorem sm2Plit_prime : Nat.Prime sm2Plit := by
  pratt_prime
    .node sm2Plit 13
        [2, 43, 30223,
        .node 348253387243 3 [2, 3, 61, 5303, 179429],
        .node 4641351449027 2
          [2, 769,
          .node 3017783777 3 [2, 7, 337, 5711]],
        .node 417514796639753 3
          [2, 7, 367, 2473,
          .node 8214737 3 [2, 67, 79, 97]],
        .node 66013261729388519804782124120027 2
          [2, 13, 1213, 71209,
          .node 6158099 2
            [2,
            .node 3079049 3 [2, 7, 54983]],
          .node 4773264379806847 3 [2, 3, 7, 11, 823, 34511, 363761]]]

end CatCrypt.Crypto.Util.SM2PPrimeCert
