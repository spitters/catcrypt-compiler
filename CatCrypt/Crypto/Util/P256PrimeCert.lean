/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P256.NodeL

/-!
# Machine-checked primality of the NIST P-256 base-field prime

`Nat.Prime p256lit` for `p = 2^256 − 2^224 + 2^192 + 2^96 − 1` via a Lucas/Pratt
certificate. The Lucas criterion needs the *full* factorization of `p − 1`; the
smooth part is Fermat-smooth but `p − 1` also carries a 160-bit prime cofactor,
so the certificate is a tree of nested Lucas certificates. The subordinate nodes
live in `CatCrypt/Crypto/Util/P256/`, deepest first:

```
p − 1 = 2·3·5²·17·257·641·1531·65537·490463·6700417·L        (witness 6)  ← this file
  L = 835945042244614951780389953367877943453916927241        (witness 11)  NodeL
  L − 1 = 2³·3³·5·M
    M = 774023187263532362759620327192479577272145303          (witness 3)   NodeM
    M − 1 = 2·3²·2411·F1·F2·F3
      F1 = 34282281433,  F1 − 1 = 2³·3·7·204061199             (witness 17)  NodeF1
      F2 = 11290956913871,  F2 − 1 = 2·5·17·G                  (witness 13)  NodeF2
        G = 66417393611,  G − 1 = 2·5·53·173·197·3677          (witness 6)   NodeG
      F3 = 46076956964474543,  F3 − 1 = 2·23·18169·78283·704251 (witness 5)   NodeF3
```

Each node is its own module so the kernel `decide` Fermat/witness checks compile
independently under a bounded memory budget.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256PrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P256.NodeL

/-- The NIST P-256 base-field prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as a
    literal (definitionally equal to `CatCrypt.Util.P256`). -/
def p256lit : Nat :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- The prime factors of `p − 1`, with multiplicity; product is `p − 1`. -/
def p256Factors : List Nat :=
  [2, 3, 5, 5, 17, 257, 641, 1531, 65537, 490463, 6700417, p256Llit]

theorem p256Factors_prod : p256Factors.prod = p256lit - 1 := by decide
theorem p256Factors_prime : ∀ q ∈ p256Factors, Nat.Prime q := by
  intro q hq
  simp only [p256Factors] at hq
  fin_cases hq <;> first | exact p256Llit_prime | norm_num
theorem p256Fermat : powMod 6 (p256lit - 1) p256lit = 1 := by decide
theorem p256Witness :
    ∀ q ∈ p256Factors, powMod 6 ((p256lit - 1) / q) p256lit ≠ 1 := by decide

/-- `Nat.Prime p256lit`, machine-checked by a Lucas certificate. -/
theorem p256lit_prime : Nat.Prime p256lit :=
  lucas_of_certificate p256lit (by decide) 6 p256Factors
    p256Factors_prod p256Factors_prime p256Fermat p256Witness

end CatCrypt.Crypto.Util.P256PrimeCert
