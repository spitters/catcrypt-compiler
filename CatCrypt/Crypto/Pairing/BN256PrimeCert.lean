/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BN256 (Cloudflare bn256) base-field prime

`Nat.Prime bn256lit` from an inline Pratt certificate tree checked by kernel
reduction (`PrattCertificate.pratt_prime`). The base-field prime is
`p = 0x8fb501e34aa387f9aa6fecb86184dc21ee5b88d120b5b59e185cac6c5e089667`
(BN seed `u = 0x5A76AE9AEC588301`, `y² = x³ + 3`). Nested nodes certify the prime
factors of `p - 1` above `2^20`; the factors below `2^20` are leaves checked by
trial division. Factor data corroborated against AUCurves `bn256_prime_certif.v`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.BN256PrimeCert

open CatCrypt.PrattCertificate

/-- The certified prime `65000549695646603732796438742359905742825358107623003571877145026864184071783`
    (`256`-bit), the BN256 base-field modulus (definitionally equal to
    `CatCrypt.Crypto.Pairing.BN256PairingTowerEmit.BN256Prime`).
    `N - 1 = 2 · 3^2 · 151 · 500393 · 1868033^3 · 5332323573263718838033 · 1374947842730272154058024133`. -/
def bn256lit : Nat := 65000549695646603732796438742359905742825358107623003571877145026864184071783

/-- `Nat.Prime bn256lit`, by a Pratt certificate with root witness `3`. -/
theorem bn256lit_prime : Nat.Prime bn256lit := by
  pratt_prime
    .node bn256lit 3
        [2, 3, 151, 500393,
        .node 1868033 3 [2, 7297],
        .node 5332323573263718838033 7
          [2, 3, 97,
          .node 1145258499412310747 2
            [2,
            .node 572629249706155373 2
              [2, 10259,
              .node 13954314497177 3
                [2, 73, 4159,
                .node 5745221 3 [2, 5, 13, 19, 1163]]]]],
        .node 1374947842730272154058024133 2
          [2, 3, 79, 1187, 3593, 4159,
          .node 81767558454161 3
            [2, 5, 151573,
            .node 6743249 3 [2, 421453]]]]

end CatCrypt.Crypto.Pairing.BN256PrimeCert
