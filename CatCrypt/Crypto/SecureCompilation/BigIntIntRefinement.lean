/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigInt

@[expose] public section

set_option autoImplicit false

/-!
# Int-level refinement of the signed BigInt carrier

The signed carrier operations (`BigInt.add`, `BigInt.sub`, `BigInt.mul`,
`BigInt.smul`) operate on `BigInt`. A caller that starts from an `Int` marshals
it in with `BigInt.ofInt`, runs the operation, and reads the result back with
`BigInt.intVal`. This module proves that the round trip equals the corresponding
`Int` operation.

The refinements compose the per-operation value specs (`BigInt.add_val`,
`BigInt.sub_val`, `BigInt.mul_val`, `BigInt.smul_val`) with the round-trip lemma
`BigInt.intVal_ofInt`.

## Main results

* `BigIntIntRefinement.add_ofInt` — `intVal (add (ofInt a) (ofInt b)) = a + b`.
* `BigIntIntRefinement.sub_ofInt` — `intVal (sub (ofInt a) (ofInt b)) = a - b`.
* `BigIntIntRefinement.mul_ofInt` — `intVal (mul (ofInt a) (ofInt b)) = a * b`.
* `BigIntIntRefinement.smul_ofInt` — `intVal (smul c (ofInt x)) = c * x`.
-/

namespace CatCrypt.Crypto.SecureCompilation.BigIntIntRefinement

open CatCrypt.Crypto.SecureCompilation

/-- Signed addition, marshalled through `Int`, computes `a + b`. -/
theorem add_ofInt (a b : Int) :
    BigInt.intVal (BigInt.add (BigInt.ofInt a) (BigInt.ofInt b)) = a + b := by
  rw [BigInt.add_val, BigInt.intVal_ofInt, BigInt.intVal_ofInt]

/-- Signed subtraction, marshalled through `Int`, computes `a - b`. -/
theorem sub_ofInt (a b : Int) :
    BigInt.intVal (BigInt.sub (BigInt.ofInt a) (BigInt.ofInt b)) = a - b := by
  rw [BigInt.sub_val, BigInt.intVal_ofInt, BigInt.intVal_ofInt]

/-- Signed multiplication, marshalled through `Int`, computes `a * b`. -/
theorem mul_ofInt (a b : Int) :
    BigInt.intVal (BigInt.mul (BigInt.ofInt a) (BigInt.ofInt b)) = a * b := by
  rw [BigInt.mul_val, BigInt.intVal_ofInt, BigInt.intVal_ofInt]

/-- Scalar multiplication by an `Int` constant, with the operand marshalled
    through `Int`, computes `c * x`. -/
theorem smul_ofInt (c x : Int) :
    BigInt.intVal (BigInt.smul c (BigInt.ofInt x)) = c * x := by
  rw [BigInt.smul_val, BigInt.intVal_ofInt]

end CatCrypt.Crypto.SecureCompilation.BigIntIntRefinement
