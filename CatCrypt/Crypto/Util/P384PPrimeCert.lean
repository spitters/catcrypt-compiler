/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeA
public import CatCrypt.Crypto.Util.P384P.NodeQ

/-!
# Machine-checked primality of the NIST P-384 base-field prime

`Nat.Prime p384Plit` via a Lucas/Pratt certificate, where `p384Plit` is the
NIST P-384 (secp384r1) base-field prime
`2^384 - 2^128 - 2^96 + 2^32 - 1`
`= 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`
(FIPS 186-5 D.1.2.4 / SEC 2 v2 §2.5.1); it is the value `p384Q` / `p384BaseQ`.

The factorization is
`p384Plit - 1 = 2 · 19 · 67 · 807145746439 · Q`, with witness `19`, where
`Q = 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097`
is a 334-bit prime. Because `Q - 1` again has a large prime factor, the certificate
is a chain of nested Lucas certificates (depth 8): every factor exceeding `2^32` is
proved prime by its own sub-certificate. The subordinate nodes live in
`CatCrypt/Crypto/Util/P384P/`, one module each so the kernel `decide` checks
compile independently:

```
p384Plit - 1 = 2·19·67·p7qAlit·p7qQlit                       (witness 19)  ← this file
  807145746439 = p7qAlit                                     (witness 3)   NodeA
  Q = p7qQlit,  Q - 1 = 2⁴·11³·8389·38557·312289·p7qDlit·p7qClit·p7qFlit  NodeQ
    p7qDlit = 1357291859799823621                                          NodeD
      p7qElit = 53448597593                                                NodeE
    p7qClit = 529709925838459440593                                       NodeC
    p7qFlit = 12397338596863679689524759770405177749801411               NodeF
      p7qGlit → p7qHlit → p7qIlit → p7qJlit → p7qKlit → p7qLlit           NodeG…NodeL
```

The `p - 1` factorization is factordb-corroborated; the sub-factor tree is
machine-generated.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384PPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeA
open CatCrypt.Crypto.Util.P384P.NodeQ

/-- The NIST P-384 base-field prime `2^384 - 2^128 - 2^96 + 2^32 - 1`
    (definitionally equal to `RelationalFront.p384Q` / `P384EndToEnd.p384BaseQ`). -/
def p384Plit : Nat :=
  39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- All prime factors of `p384Plit - 1`; `p7qAlit` and `p7qQlit` exceed `2^32` and
    are proved prime by `p7qA_prime` / `p7qQ_prime`. -/
def p384PFactors : List Nat := [2, 19, 67, p7qAlit, p7qQlit]
theorem p384P_prod : p384PFactors.prod = p384Plit - 1 := by decide
theorem p384P_factors_prime : ∀ q ∈ p384PFactors, Nat.Prime q := by
  intro q hq
  simp only [p384PFactors] at hq
  fin_cases hq <;> first | exact p7qA_prime | exact p7qQ_prime | norm_num
theorem p384P_fermat : powMod 19 (p384Plit - 1) p384Plit = 1 := by decide
theorem p384P_witness :
    ∀ q ∈ p384PFactors, powMod 19 ((p384Plit - 1) / q) p384Plit ≠ 1 := by decide

/-- `Nat.Prime p384Plit`, machine-checked by a Lucas certificate. -/
theorem p384Plit_prime : Nat.Prime p384Plit :=
  lucas_of_certificate p384Plit (by decide) 19 p384PFactors
    p384P_prod p384P_factors_prime p384P_fermat p384P_witness

end CatCrypt.Crypto.Util.P384PPrimeCert
