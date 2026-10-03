/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.OpInfo

/-!
# The operation traits of `jasminDialect`

The record `jasminTraits : OpTraits jasminDialect` and the predicates it is built from:
the cost `Egraph.opCost` (a multiply weighs four, every other operation one), the merge
predicate `ComGVN.gvnPure` (every operation other than the stack accesses, the calls and
the operations of the instruction pairs of the x86 lowering, `ComGVN.pairedOp`), the
speculation predicate `jasminSpeculatable` (every operation other than the calls), and
the constant predicate `jasminConstLike` (the constants `regConst`).

## Main definitions

* `Egraph.opCost`, `ComGVN.pairLowOp`, `ComGVN.pairedOp`, `ComGVN.gvnPure`,
  `jasminSpeculatable`, `jasminConstLike`
* `jasminTraits`

## Main results

* `jasminTraits_constLaw`: a constant-like jasmin operation has the empty signature
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.Egraph

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- Cost of one op: `mul` is the expensive arm; everything else is cheap. -/
def opCost : JasminOp → Nat
  | .regArith .mul _ => 4
  | .regArith _ _    => 1
  | _                => 1

end CatCrypt.Crypto.Optimizer.Rewrite.Egraph

namespace CatCrypt.Crypto.Optimizer.Rewrite.ComGVN

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The low halves of the instruction pairs of the x86 lowering: the multiply
    `regArith .mul w`, whose `MUL` the `MULX` fusion pairs with the `MULXHI` of `mulhi w`
    on the same sources, and the carry-chain add `addCarryLo w`, whose `ADCX` sets the
    carry flag that the `setc` of the paired `addCarryHi w` reads. -/
def pairLowOp : JasminOp → Bool
  | .regArith .mul _ | .addCarryLo _ => true
  | _ => false

/-- The operations of the instruction pairs of the x86 lowering: the low halves
    (`pairLowOp`) and the high halves `mulhi w` and `addCarryHi w`. -/
def pairedOp : JasminOp → Bool
  | .mulhi _ | .addCarryHi _ => true
  | op => pairLowOp op

/-- The operations whose bindings the pass may merge: every operation other than a stack
    load or store, an external call, a multi-result call and an operation of an
    instruction pair of the x86 lowering (`pairedOp`). -/
def gvnPure : JasminOp → Bool
  | .stackLoad _ _ | .stackStore _ _ | .extCall _ _ _ | .callN _ _ _ => false
  | op => !pairedOp op

end CatCrypt.Crypto.Optimizer.Rewrite.ComGVN

namespace CatCrypt.Crypto.SecureCompilation.VIR

open JasminDialect

/-- The ops of `jasminDialect` other than the calls `extCall` and `callN`. -/
def jasminSpeculatable : JasminOp → Bool
  | .extCall .. => false
  | .callN .. => false
  | _ => true

/-- The constants `regConst w n` of `jasminDialect`. -/
def jasminConstLike : JasminOp → Bool
  | .regConst _ _ => true
  | _ => false

/-- The operation traits of `jasminDialect`. -/
def jasminTraits : OpTraits jasminDialect where
  pure := Optimizer.Rewrite.ComGVN.gvnPure
  speculatable := jasminSpeculatable
  constLike := jasminConstLike
  cost := Optimizer.Rewrite.Egraph.opCost

/-- A constant-like jasmin operation has the empty signature. -/
theorem jasminTraits_constLaw : ConstLaw jasminTraits := by
  intro op h
  cases op <;> first | rfl | exact absurd h Bool.false_ne_true

end CatCrypt.Crypto.SecureCompilation.VIR
