/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the NIST P-384 group order

`Nat.Prime p384Nlit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `n - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.P384NPrimeCert

open CatCrypt.PrattCertificate

/-- The NIST P-384 group order `n` (definitionally equal to
    `P384GroupParam.P384N`). -/
def p384Nlit : Nat :=
  39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

/-- `Nat.Prime p384Nlit`, by a Pratt certificate with root witness `2`. -/
theorem p384Nlit_prime : Nat.Prime p384Nlit := by
  pratt_prime
    .node p384Nlit 2
        [2, 3, 7, 13,
        .node 1124679999981664229965379347 2
          [2, 3, 1553,
          .node 120699720968197491947347 3
            [2, 3, 13, 34429,
            .node 154950581 2 [2, 5, 17, 455737],
            .node 290064143 5 [2, 79, 491, 3739]]],
        .node 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471 12
          [2, 3, 5, 151, 347,
          .node 1276987 2 [2, 3, 29, 41, 179],
          .node 1436833069313 3 [2, 16979, 330563],
          .node 1059392654943455286185473617842338478315215895509773412096307 2
            [2, 251, 248431,
            .node 8463023 5 [2, 113, 37447],
            .node 55942463741690639 7
              [2, 7, 107,
              .node 37344768852931 3
                [2, 3, 5, 7, 11, 149,
                .node 9863677 5 [2, 3, 311, 881]]],
            .node 17942392077136950785977011829 6
              [2, 3,
              .node 1495199339761412565498084319 6
                [2, 3, 64901,
                .node 426632512014427833817 11
                  [2, 3, 13, 89, 659,
                  .node 23314383343543 3
                    [2, 3, 17,
                    .node 228572385721 23
                      [2, 3, 5, 7,
                      .node 272109983 5 [2, 19, 73, 233, 421]]]]]]]]]

end CatCrypt.Crypto.Util.P384NPrimeCert
