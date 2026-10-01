/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BLS12-381 scalar-field order

`Nat.Prime bls12381Rlit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`), with root witness `7` and
`r - 1 = 2^32 · 3 · 11 · 19 · 10177 · 125527 · 859267 · 906349^2 · 2508409
· 2529403 · 52437899 · 254760293^2`. Factors below `2^20` are leaves checked by
trial division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.Bls12381RPrimeCert

open CatCrypt.PrattCertificate

/-- The BLS12-381 G1 subgroup order / scalar-field prime `r`, as a literal
    (definitionally equal to `Bls12381G1GroupParam.Bls12381R`). -/
def bls12381Rlit : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- `Nat.Prime bls12381Rlit`, by a Pratt certificate with root witness `7`. -/
theorem bls12381Rlit_prime : Nat.Prime bls12381Rlit := by
  pratt_prime
    .node bls12381Rlit 7
        [2, 3, 11, 19, 10177, 125527, 859267, 906349,
        .node 2508409 11 [2, 3, 7, 79],
        .node 2529403 2 [2, 3, 23, 18329],
        .node 52437899 2 [2, 43, 609743],
        .node 254760293 2
          [2,
          .node 63690073 7
            [2, 3,
            .node 2653753 5 [2, 3, 110573]]]]

end CatCrypt.Crypto.Util.Bls12381RPrimeCert
