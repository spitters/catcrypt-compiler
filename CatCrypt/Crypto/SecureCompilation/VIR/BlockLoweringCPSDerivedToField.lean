/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
public import CatCrypt.Crypto.SecureCompilation.VIR.DerivedToFieldLowering

/-!
# `derivedDialect → fieldDialect` through the continuation-passing block lowering

The instance of `BlockLoweringCPS` at the `DerivedToField` lowering: the
derived field ops (`field.double`, `field.square` and the others of
`FieldDerivedOps`) expand into `fieldDialect` blocks, and `blockLowerComK` emits the
lowered program with each block renamed once.

## Main results

* `DerivedToFieldCPS.lowerDerivedToFieldK_denote`: `derivedDialect → fieldDialect`
  through `blockLowerComK` preserves denotation for every program.
* `DerivedToFieldCPS.lowerDoubleSquareK_denote`: the gated instance for programs
  built from `field.double` and `field.square` alone.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

namespace DerivedToFieldCPS

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
open CatCrypt.Crypto.SecureCompilation.VIR.DerivedToField

/-- **`derivedDialect → fieldDialect` through `blockLowerComK` preserves denotation
    for every program.** The leaves are those of `DerivedToField`; coverage holds
    under the predicate that accepts every expression. -/
theorem lowerDerivedToFieldK_denote {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) (V : Valuation Γ) :
    (lowering.blockLowerComK c).denote (mapVal V) = transTy (c.denote V) :=
  lowering.blockLowerComK_denote_on transTy mapVal (fun _ => True) varTransports
    (fun e _ V => blockOpTransports e V) mapValExtends c
    (coveredCom_of_forall _ (fun _ => trivial) c) V

/-- An expression of `derivedDialect` whose op is `field.double` or `field.square`. -/
def DoubleOrSquare {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (e : Expr derivedDialect Γ t) : Prop :=
  (∃ p, e.op = .fieldDouble p) ∨ (∃ p, e.op = .fieldSquare p)

/-- **Gated instance.** A program built from `field.double` and `field.square`
    alone lowers through `blockLowerComK` to a denotation-preserving field
    program. -/
theorem lowerDoubleSquareK_denote {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) (hc : CoveredCom DoubleOrSquare c) (V : Valuation Γ) :
    (lowering.blockLowerComK c).denote (mapVal V) = transTy (c.denote V) :=
  lowering.blockLowerComK_denote_on transTy mapVal DoubleOrSquare varTransports
    (fun e _ V => blockOpTransports e V) mapValExtends c hc V

end DerivedToFieldCPS

end CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
