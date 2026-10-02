/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend
public import CatCrypt.Crypto.SecureCompilation.VIR.DerivedToFieldLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering

/-!
# A program over field operations and prime-field arithmetic

The lowering `DerivedToField.lowering` of the derived field operations
(`field.double`, `field.square`, `field.powui`) to `fieldDialect` is extended by
the identity (`BlockLoweringData.extendId`, `VIR/BlockLoweringExtend.lean`) on the
prime-field arithmetic dialect `fpDialect` (`VIR/FieldToModArithLowering.lean`).
`fpDialect` has its own type alphabet `FpTy`; it is re-typed into `DerivedTy` and
into `FieldTy` along the embeddings `fp p ↦ fp p`, so the source dialect is the
operation sum of `derivedDialect` with `fpDialect` over `DerivedTy`, and the target
dialect is the operation sum of `fieldDialect` with `fpDialect` over `FieldTy`.

## Main definitions

* `Witness.lowering`, `Witness.chain`: the extended lowering and its one-step driver.
* `Witness.prog`: a three-binding program over both operation families.

## Main results

* `Witness.lowered_denote`, `Witness.lowered_denote_eq`: the program lowered on the
  field operations only keeps its denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

namespace Witness

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect (FieldTy fieldDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
  (DerivedTy DerivedOp derivedDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering (FpTy FpOp fpDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum (retypeSignature retypeDenote)

/-- The embedding of `FpTy` into `DerivedTy`: `fp p ↦ fp p`, both denoting
    `ZMod p`. -/
def fpToDerived : TyEmbedding FpTy DerivedTy where
  map | .fp p => .fp p
  trans {t} x := match t, x with | .fp _, x => x
  untrans {t} x := match t, x with | .fp _, x => x
  untrans_trans {t} _ := by cases t; rfl

/-- The embedding of `FpTy` into `FieldTy`: `fp p ↦ fp p`, both denoting
    `ZMod p`. -/
def fpToField : TyEmbedding FpTy FieldTy where
  map | .fp p => .fp p
  trans {t} x := match t, x with | .fp _, x => x
  untrans {t} x := match t, x with | .fp _, x => x
  untrans_trans {t} _ := by cases t; rfl

/-- The signature of `fpDialect` over `DerivedTy`. -/
instance fpOverDerivedSig : DialectSignature (⟨FpOp, DerivedTy⟩ : Dialect) :=
  retypeSignature (d := fpDialect) fpToDerived.map

/-- The denotation of `fpDialect` over `DerivedTy`. -/
instance fpOverDerivedDenote : DialectDenote (⟨FpOp, DerivedTy⟩ : Dialect) :=
  retypeDenote (d := fpDialect) fpToDerived

/-- The signature of `fpDialect` over `FieldTy`. -/
instance fpOverFieldSig : DialectSignature (⟨FpOp, FieldTy⟩ : Dialect) :=
  retypeSignature (d := fpDialect) fpToField.map

/-- The denotation of `fpDialect` over `FieldTy`. -/
instance fpOverFieldDenote : DialectDenote (⟨FpOp, FieldTy⟩ : Dialect) :=
  retypeDenote (d := fpDialect) fpToField

/-- The source dialect: derived field operations and prime-field arithmetic over
    `DerivedTy`. -/
@[reducible] def srcDialect : Dialect := Dialect.opSum derivedDialect ⟨FpOp, DerivedTy⟩

/-- The target dialect: `fieldDialect` and prime-field arithmetic over `FieldTy`. -/
@[reducible] def tgtDialect : Dialect := Dialect.opSum fieldDialect ⟨FpOp, FieldTy⟩

/-- The type map of `DerivedToField.lowering` carries the signatures of
    `fpDialect` over `DerivedTy` to those over `FieldTy`. -/
theorem sigMaps : SigMaps FpOp DerivedToField.lowering.mapTy :=
  ⟨fun o => by cases o <;> rfl, fun o => by cases o <;> rfl⟩

/-- The operations of `fpDialect` commute with the value transport of
    `DerivedToField.lowering`, which is the identity on `ZMod p`. -/
theorem opsCommute :
    OpsCommute DerivedToField.lowering.mapTy sigMaps DerivedToField.transTy
      (fun _ => True) := by
  intro o _ xs
  cases o <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> rfl

/-- The extended lowering: the derived field operations are lowered to
    `fieldDialect`, the prime-field operations are kept. -/
def lowering : BlockLoweringData srcDialect tgtDialect :=
  DerivedToField.lowering.extendId sigMaps

/-- The one-step driver applying `lowering`. -/
def chain : LowerChain ⟨srcDialect⟩ ⟨tgtDialect⟩ :=
  .cons (LowerStep.extendId DerivedToField.lowering sigMaps DerivedToField.transTy
    DerivedToField.mapVal DerivedToField.varTransports DerivedToField.blockOpTransports
    DerivedToField.mapValExtends opsCommute) (.nil _)

/-- A three-binding program with one input `x : fp p`:

    ```
    let y = inr (fpAdd p) x x
    let z = inl (fieldSquare p) y
    let w = inr (fpMul p) z x
    ret w
    ``` -/
def prog (p : Nat) : Com srcDialect [DerivedTy.fp p] (DerivedTy.fp p) :=
  .var (t := DerivedTy.fp p) ⟨.inr (.fpAdd p), rfl, .cons .here (.cons .here .nil)⟩
    (.var (t := DerivedTy.fp p) ⟨.inl (.fieldSquare p), rfl, .cons .here .nil⟩
      (.var (t := DerivedTy.fp p)
          ⟨.inr (.fpMul p), rfl, .cons .here (.cons (.there (.there .here)) .nil)⟩
        (.ret .here)))

/-- `prog p` denotes `(x + x) * (x + x) * x`. -/
theorem prog_denote (p : Nat) (x : ZMod p) :
    (prog p).denote (.cons x .nil) = (x + x) * (x + x) * x := rfl

/-- **The program lowered on the field operations only keeps its denotation.** -/
theorem lowered_denote (p : Nat) (V : Valuation (d := srcDialect) [DerivedTy.fp p]) :
    (chain.run (prog p)).denote (chain.mapVal V) = chain.transTy ((prog p).denote V) :=
  chain.run_denote (prog p) V

/-- The lowered program, over `fieldDialect` and `fpDialect`, denotes
    `(x + x) * (x + x) * x`. -/
theorem lowered_denote_eq (p : Nat) (x : ZMod p) :
    (chain.run (prog p)).denote
        (chain.mapVal (Γ := [DerivedTy.fp p]) (.cons x .nil)) = (x + x) * (x + x) * x :=
  (lowered_denote p (.cons x .nil)).trans (congrArg (chain.transTy (t := .fp p))
    (prog_denote p x))

end Witness

end CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend
