/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.OpInfo

/-!
# The operation traits of `catCryptDialect`

The record `catTraits : OpTraits catCryptDialect` and the predicates it is built from:
the cost `AegraphCat.catCost` (in units of a bit-vector addition), the merge predicate
`AegraphCat.catPure` (every operation other than the sampling leaves, the external
call and the fresh zero array), every operation speculatable (the denotation of `catCryptDialect` is a total
function), and the constant predicate `catConstLike` (`bvConst`, `constBit`,
`constUnit`).

## Main definitions

* `AegraphCat.catCost`, `AegraphCat.catPure`, `catConstLike`
* `catTraits`

## Main results

* `catTraits_constLaw`: a constant-like catCrypt operation has the empty signature
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-- The cost of a catCrypt operation in units of a bit-vector addition: a full or high
    multiplication costs four, every other operation one. -/
def catCost : CatCryptOp → Nat
  | .bvMul _ | .bvMulHi _ => 4
  | _ => 1

/-- The catCrypt operations whose bindings the node table may merge: every operation other
    than the sampling leaves `sampleBit`, `sampleBv`, the external call `extCall` and the
    fresh zero array `memrefZero`. Two `memrefZero n` bindings lower to two `stackZero`
    arrays, each a separate root of the array coalescing, so the table keeps them apart. -/
def catPure : CatCryptOp → Bool
  | .sampleBit | .sampleBv _ | .extCall _ _ _ | .memrefZero _ => false
  | _ => true

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCryptDialect

/-- The constants `bvConst w v`, `constBit v` and `constUnit` of `catCryptDialect`. -/
def catConstLike : CatCryptOp → Bool
  | .bvConst _ _ | .constBit _ | .constUnit => true
  | _ => false

/-- The operation traits of `catCryptDialect`. -/
def catTraits : OpTraits catCryptDialect where
  pure := Optimizer.Rewrite.AegraphCat.catPure
  speculatable _ := true
  constLike := catConstLike
  cost := Optimizer.Rewrite.AegraphCat.catCost

/-- A constant-like catCrypt operation has the empty signature. -/
theorem catTraits_constLaw : ConstLaw catTraits := by
  intro op h
  cases op <;> first | rfl | exact absurd h Bool.false_ne_true

end CatCrypt.Crypto.SecureCompilation.VIR
