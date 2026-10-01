/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the NIST P-256 group order

`Nat.Prime p256Nlit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `n - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.P256NPrimeCert

open CatCrypt.PrattCertificate

/-- The NIST P-256 group order `n` (FIPS 186-4), as a literal (definitionally
    equal to `CatCrypt.Util.P256N`). -/
def p256Nlit : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- `Nat.Prime p256Nlit`, by a Pratt certificate with root witness `7`. -/
theorem p256Nlit_prime : Nat.Prime p256Nlit := by
  pratt_prime
    .node p256Nlit 7
        [2, 3, 71, 131, 373, 3407, 17449, 38189,
        .node 187019741 2
          [2, 5,
          .node 9350987 2 [2, 17, 229, 1201]],
        .node 622491383 5
          [2,
          .node 311245691 2 [2, 5, 7, 17, 29, 311]],
        .node 1002328039319 19
          [2, 126241,
          .node 3969899 2 [2, 19, 104471]],
        .node 2624747550333869278416773953 7
          [2, 3, 1297, 16879,
          .node 208150935158385979 2
            [2, 3, 11, 43, 127, 3023,
            .node 191039911 3 [2, 3, 5, 41, 155317]]]]

end CatCrypt.Crypto.Util.P256NPrimeCert
