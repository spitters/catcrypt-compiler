/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P256N.NodeA
public import CatCrypt.Crypto.Util.P256N.NodeB

/-!
# Machine-checked primality of the NIST P-256 group order

`Nat.Prime p256Nlit` for the FIPS 186-4 P-256 order `n` via a Lucas/Pratt
certificate. The full factorization of `n − 1` carries two prime cofactors above
`2^32`, so the certificate is a tree of nested Lucas certificates. The subordinate
nodes live in `CatCrypt/Crypto/Util/P256N/`, deepest first:

```
n − 1 = 2⁴·3·71·131·373·3407·17449·38189·187019741·622491383·A·B   (witness 7)  ← this file
  A = 1002328039319,  A − 1 = 2·126241·3969899                     (witness 19)  NodeA
  B = 2624747550333869278416773953,  B − 1 = 2⁶·3²·1297·16879·C    (witness 7)   NodeB
    C = 208150935158385979,  C − 1 = 2·3·11·43·127·3023·191039911  (witness 2)   NodeC
```

Each node is its own module so the kernel `decide` Fermat/witness checks compile
independently under a bounded memory budget.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256NPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P256N.NodeA
open CatCrypt.Crypto.Util.P256N.NodeB

/-- The NIST P-256 group order `n` (FIPS 186-4), as a literal (definitionally
    equal to `CatCrypt.Util.P256N`). -/
def p256Nlit : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- The prime factors of `n − 1`, with multiplicity; product is `n − 1`. -/
def p256NFactors : List Nat :=
  [2, 2, 2, 2, 3, 71, 131, 373, 3407, 17449, 38189, 187019741, 622491383,
   p256nAlit, p256nBlit]

theorem p256NFactors_prod : p256NFactors.prod = p256Nlit - 1 := by decide
theorem p256NFactors_prime : ∀ q ∈ p256NFactors, Nat.Prime q := by
  intro q hq
  simp only [p256NFactors] at hq
  fin_cases hq <;>
    first
      | exact p256nAlit_prime
      | exact p256nBlit_prime
      | norm_num
theorem p256NFermat : powMod 7 (p256Nlit - 1) p256Nlit = 1 := by decide
theorem p256NWitness :
    ∀ q ∈ p256NFactors, powMod 7 ((p256Nlit - 1) / q) p256Nlit ≠ 1 := by decide

/-- `Nat.Prime p256Nlit`, machine-checked by a Lucas certificate. -/
theorem p256Nlit_prime : Nat.Prime p256Nlit :=
  lucas_of_certificate p256Nlit (by decide) 7 p256NFactors
    p256NFactors_prod p256NFactors_prime p256NFermat p256NWitness

end CatCrypt.Crypto.Util.P256NPrimeCert
