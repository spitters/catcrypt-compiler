/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeD
public import CatCrypt.Crypto.Util.P384P.NodeC
public import CatCrypt.Crypto.Util.P384P.NodeF

/-!
# Lucas certificate node `Q`, the 334-bit factor of `p384Plit - 1`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qQlit` with
`p7qQlit - 1 = 2⁴·11³·8389·38557·312289·p7qDlit·p7qClit·p7qFlit` and witness
`3`, using the child nodes `D`, `C`, `F`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeQ

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeD
open CatCrypt.Crypto.Util.P384P.NodeC
open CatCrypt.Crypto.Util.P384P.NodeF

def p7qQlit : Nat :=
  19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097
def p7qQFactors : List Nat :=
  [2, 2, 2, 2, 11, 11, 11, 8389, 38557, 312289, p7qDlit, p7qClit, p7qFlit]
theorem p7qQ_prod : p7qQFactors.prod = p7qQlit - 1 := by decide
theorem p7qQ_factors_prime : ∀ q ∈ p7qQFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qQFactors] at hq
  fin_cases hq <;>
    first
      | exact p7qD_prime
      | exact p7qC_prime
      | exact p7qF_prime
      | norm_num
theorem p7qQ_fermat : powMod 3 (p7qQlit - 1) p7qQlit = 1 := by decide
theorem p7qQ_witness :
    ∀ q ∈ p7qQFactors, powMod 3 ((p7qQlit - 1) / q) p7qQlit ≠ 1 := by decide
theorem p7qQ_prime : Nat.Prime p7qQlit :=
  lucas_of_certificate p7qQlit (by decide) 3 p7qQFactors
    p7qQ_prod p7qQ_factors_prime p7qQ_fermat p7qQ_witness

end CatCrypt.Crypto.Util.P384P.NodeQ
