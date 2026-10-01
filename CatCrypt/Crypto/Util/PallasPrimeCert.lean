/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the Pasta Pallas base-field prime

`Nat.Prime pallaslit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.PallasPrimeCert

open CatCrypt.PrattCertificate

/-- The Pasta Pallas base-field prime, as a literal (definitionally equal to
    `RelationalFront.pallasQ`). -/
def pallaslit : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- `Nat.Prime pallaslit`, by a Pratt certificate with root witness `5`. -/
theorem pallaslit_prime : Nat.Prime pallaslit := by
  pratt_prime
    .node pallaslit 5
        [2, 3, 463,
        .node 539204044132271846773 5
          [2, 3, 89, 14923,
          .node 417677162933 2 [2, 59, 1973, 897019]],
        .node 8999194758858563409123804352480028797519453 2
          [2, 3, 11, 2531, 115603,
          .node 1197907 3 [2, 3, 53, 3767],
          .node 22160661629 3
            [2, 7, 19,
            .node 41655379 2
              [2, 3,
              .node 6942563 2 [2, 11, 17, 19, 977]]],
          .node 325086459374267 2 [2, 509, 413527, 772231]]]

end CatCrypt.Crypto.Util.PallasPrimeCert
