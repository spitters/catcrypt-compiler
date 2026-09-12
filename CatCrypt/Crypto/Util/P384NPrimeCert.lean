/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeHint
public import CatCrypt.Crypto.Util.P384N.NodeB

/-!
# Machine-checked primality of the NIST P-384 group order

`Nat.Prime p384Nlit` via a Lucas/Pratt certificate, where `p384Nlit` is the NIST
P-384 (secp384r1) group order `n`
`= 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643`
(FIPS 186-5 D.1.2.4 / SEC 2 v2 §2.5.1); it is the value `P384GroupParam.P384N`.

The factorization is
`p384Nlit - 1 = 2 · 3^2 · 7^2 · 13 · 1124679999981664229965379347 · B`, with witness `2`,
where `B = 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471`
is a 281-bit prime. `B - 1` again has large prime factors, so the certificate is a
chain of nested Lucas certificates (depth 8): every factor exceeding `2^32` is
proved prime by its own sub-certificate. The subordinate nodes live in
`CatCrypt/Crypto/Util/P384N/`, one module each so the kernel `decide` checks
compile independently:

```
p384Nlit - 1 = 2·3²·7²·13·p8hintlit·p8Blit                    (witness 2)  ← this file
  p8hintlit = 1124679999981664229965379347                    (witness 2)  NodeHint
    p8h1lit = 120699720968197491947347                        (witness 3)  NodeH1
  B = p8Blit,  B - 1 = 2·3·5·151·347·1276987·p8b1lit·p8C2lit               NodeB
    p8b1lit = 1436833069313                                                NodeB1
    p8C2lit = 1059392654943455286185473617842338478315215895509773412096307  NodeC2
      p8m3alit → p8n1lit                                                   NodeM3a, NodeN1
      p8m3blit → p8m4lit → p8m5lit → p8m6lit → p8m7lit                     NodeM3b…NodeM7
```

The `n - 1` factorization is factordb-corroborated; the sub-factor tree is
machine-generated.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384NPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeHint
open CatCrypt.Crypto.Util.P384N.NodeB

/-- The NIST P-384 group order `n` (definitionally equal to
    `P384GroupParam.P384N`). -/
def p384Nlit : Nat :=
  39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

/-- All prime factors of `p384Nlit - 1`; `p8hintlit` and `p8Blit` exceed `2^32`
    and are proved prime by `p8hint_prime` / `p8B_prime`. -/
def p384NFactors : List Nat := [2, 3, 3, 7, 7, 13, p8hintlit, p8Blit]
theorem p384N_prod : p384NFactors.prod = p384Nlit - 1 := by decide
theorem p384N_factors_prime : ∀ q ∈ p384NFactors, Nat.Prime q := by
  intro q hq
  simp only [p384NFactors] at hq
  fin_cases hq <;> first | exact p8hint_prime | exact p8B_prime | norm_num
theorem p384N_fermat : powMod 2 (p384Nlit - 1) p384Nlit = 1 := by decide
theorem p384N_witness :
    ∀ q ∈ p384NFactors, powMod 2 ((p384Nlit - 1) / q) p384Nlit ≠ 1 := by decide

/-- `Nat.Prime p384Nlit`, machine-checked by a Lucas certificate. -/
theorem p384Nlit_prime : Nat.Prime p384Nlit :=
  lucas_of_certificate p384Nlit (by decide) 2 p384NFactors
    p384N_prod p384N_factors_prime p384N_fermat p384N_witness

end CatCrypt.Crypto.Util.P384NPrimeCert
