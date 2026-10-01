/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the NIST P-256 base-field prime

`Nat.Prime p256lit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.P256PrimeCert

open CatCrypt.PrattCertificate

/-- The NIST P-256 base-field prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as a
    literal (definitionally equal to `CatCrypt.Util.P256`). -/
def p256lit : Nat :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- `Nat.Prime p256lit`, by a Pratt certificate with root witness `6`. -/
theorem p256lit_prime : Nat.Prime p256lit := by
  pratt_prime
    .node p256lit 6
        [2, 3, 5, 17, 257, 641, 1531, 65537, 490463,
        .node 6700417 5 [2, 3, 17449],
        .node 835945042244614951780389953367877943453916927241 11
          [2, 3, 5,
          .node 774023187263532362759620327192479577272145303 3
            [2, 3, 2411,
            .node 34282281433 17
              [2, 3, 7,
              .node 204061199 11 [2, 11, 23, 107, 3769]],
            .node 11290956913871 13
              [2, 5, 17,
              .node 66417393611 6 [2, 5, 53, 173, 197, 3677]],
            .node 46076956964474543 5 [2, 23, 18169, 78283, 704251]]]]

end CatCrypt.Crypto.Util.P256PrimeCert
