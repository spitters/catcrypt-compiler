/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.OpInfo

/-!
# The operation traits of `fieldDialect`

The record `fieldTraits : OpTraits fieldDialect` and the predicates it is built from: the
cost `AegraphField.fieldCost` (in units of a base-field addition), the merge predicate
`AegraphField.fieldPure` (every operation other than the output copy `fCopy`), every
operation speculatable (the denotation of `fieldDialect` is a total function), and the
constant predicate `fieldConstLike` (the constants `fConst`).

## Main definitions

* `AegraphField.fieldCost`, `AegraphField.fieldPure`, `fieldConstLike`
* `fieldTraits`

## Main results

* `fieldTraits_constLaw`: a constant-like field operation has the empty signature
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphField

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-- The cost of a field operation in units of a base-field addition: a multiplication or
    squaring costs four, an inversion sixty-four, an extension-field multiplication four
    per base-field multiplication of its schoolbook form; every other operation costs
    one. -/
def fieldCost : FieldOp → Nat
  | .fMul _ | .fieldSquare _ => 4
  | .fInv _ => 64
  | .ext2Mul _ => 16
  | .ext6Mul _ _ => 144
  | .ext12Mul _ _ => 576
  | _ => 1

/-- The field operations whose bindings the node table may merge: every operation other
    than the designated-output copy `fCopy`, whose bindings stage distinct output lanes. -/
def fieldPure : FieldOp → Bool
  | .fCopy _ => false
  | _ => true

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphField

namespace CatCrypt.Crypto.SecureCompilation.VIR

open FieldDialect

/-- The constants `fConst p c` of `fieldDialect`. -/
def fieldConstLike : FieldOp → Bool
  | .fConst _ _ => true
  | _ => false

/-- The operation traits of `fieldDialect`. -/
def fieldTraits : OpTraits fieldDialect where
  pure := Optimizer.Rewrite.AegraphField.fieldPure
  speculatable _ := true
  constLike := fieldConstLike
  cost := Optimizer.Rewrite.AegraphField.fieldCost

/-- A constant-like field operation has the empty signature. -/
theorem fieldTraits_constLaw : ConstLaw fieldTraits := by
  intro op h
  cases op <;> first | rfl | exact absurd h Bool.false_ne_true

end CatCrypt.Crypto.SecureCompilation.VIR
