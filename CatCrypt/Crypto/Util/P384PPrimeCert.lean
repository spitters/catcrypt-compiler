/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the NIST P-384 base-field prime

`Nat.Prime p384Plit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). Nested nodes certify the prime factors
of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by trial
division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.P384PPrimeCert

open CatCrypt.PrattCertificate

/-- The NIST P-384 base-field prime `2^384 - 2^128 - 2^96 + 2^32 - 1`
    (definitionally equal to `RelationalFront.p384Q` / `P384EndToEnd.p384BaseQ`). -/
def p384Plit : Nat :=
  39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- `Nat.Prime p384Plit`, by a Pratt certificate with root witness `19`. -/
theorem p384Plit_prime : Nat.Prime p384Plit := by
  pratt_prime
    .node p384Plit 19
        [2, 19, 67,
        .node 807145746439 3
          [2, 3, 47,
          .node 2862218959 3 [2, 3, 157, 1373, 2213]],
        .node 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 3
          [2, 11, 8389, 38557, 312289,
          .node 1357291859799823621 2
            [2, 3, 5, 67, 6317,
            .node 53448597593 3
              [2, 13,
              .node 513928823 5 [2, 11, 59, 599, 661]]],
          .node 529709925838459440593 3
            [2, 7, 181,
            .node 105957871 3 [2, 3, 5, 19, 211, 881],
            .node 246608641 19 [2, 3, 5, 21407]],
          .node 12397338596863679689524759770405177749801411 2
            [2, 3, 5,
            .node 413244619895455989650825325680172591660047 5
              [2, 17, 97,
              .node 6051631 6 [2, 3, 5, 13, 59, 263],
              .node 20705423504133292078628634597817 5
                [2, 3,
                .node 862725979338887169942859774909 2
                  [2, 3,
                  .node 23964610537191310276190549303 5
                    [2, 336757,
                    .node 35581458644053887931343 5
                      [2, 17, 41, 568151,
                      .node 44925942675193 5
                        [2, 3, 3517,
                        .node 532247449 7 [2, 3, 61, 363557]]]]]]]]]]

end CatCrypt.Crypto.Util.P384PPrimeCert
