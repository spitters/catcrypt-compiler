/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the Pasta Vesta base-field prime

`Nat.Prime vestalit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.VestaPrimeCert

open CatCrypt.PrattCertificate

/-- The Pasta Vesta base-field prime, as a literal (definitionally equal to
    `RelationalFront.vestaQ` / `Util.PallasN`). -/
def vestalit : Nat :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- `Nat.Prime vestalit`, by a Pratt certificate with root witness `5`. -/
theorem vestalit_prime : Nat.Prime vestalit := by
  pratt_prime
    .node vestalit 5
        [2, 3, 1709, 24859,
        .node 1690502597179744445941507 2
          [2, 3, 13,
          .node 4129989133 5 [2, 3, 359, 958679],
          .node 5247740253619 2
            [2, 3, 17, 71,
            .node 80513981 2
              [2, 5,
              .node 4025699 2
                [2,
                .node 2012849 3 [2, 125803]]]]],
        .node 10427374428728808478656897599072717 2
          [2, 294793,
          .node 4229279 13 [2, 827, 2557],
          .node 399082391 7
            [2, 5, 7,
            .node 5701177 7 [2, 3, 13, 6091]],
          .node 5239247429827 2 [2, 3, 757, 12149, 31649]]]

end CatCrypt.Crypto.Util.VestaPrimeCert
