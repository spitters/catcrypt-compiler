/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFFieldSum
public import CatCrypt.Crypto.Hax.NFToCatLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproductLeak

/-!
# The leakage of `fieldDialect` and of `nfDialect ⊕ fieldDialect`

`fieldLeakModel` is the leakage model of `fieldDialect`: addition, subtraction, negation,
multiplication, doubling, squaring, constants and copies emit no event, and inversion
leaks its argument as that of a variable-time leaf call. A value of a prime field reads as
its least natural representative; a value of an extension field reads as `0`.

The quiet class of the eight operations is a modelling choice of the source level. It
stands for the property that the limb template of each operation emits events that do not
depend on the limbs: the template reads and writes its word arrays at constant indices and
has no branch. The lowering `FieldToJasminLimbs.fieldCom` has no leakage theorem in this
module; a consumer of the model states that property of the template as a hypothesis on
the events of `fieldCom` at the leakage model of `jasminDialect`.

`nfFieldLeakModel` is the coproduct model `sumLeak nfLeakModel fieldLeakModel` of
`nfFieldDialect`, and `nfFieldLeakRun` the leakage run of a program of `nfFieldDialect`
over the leaf table of a builtin table. A leaf call that `nfToSum` keeps in the left
summand has the class `nfKind` gives it; a field entry that `nfToSum` moves to the right
summand has the class of its field operation.

## Main definitions

* `fieldKind`, `fieldValNat`, `fieldLeakModel` — the leakage model of `fieldDialect`.
* `nfFieldLeakModel`, `nfFieldLeakRun` — the leakage model and the leakage run of
  `nfFieldDialect`.

## Main results

* `fieldKind_quiet_of_ne_inv` — every operation other than inversion is quiet.
* `nfFieldLeakModel_kind_inl`, `nfFieldLeakModel_kind_inr` — the event class of an
  operation of each summand.
* `nfField_opLeak_inr` — a field operation other than inversion emits no event in the
  coproduct.
* `nfField_nfCTRel_of_levelCheck'` — a program of `nfFieldDialect` the level checker
  accepts is constant time relative to its runs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFFieldSum

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFToCat (nfLeakModel nfKind)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf)
open Ctxt (Var Valuation)

/-! ## 1. The leakage model of `fieldDialect` -/

/-- The event class of an operation of `fieldDialect`: inversion is a variable-time leaf
    call on its argument, and every other operation is quiet. The match lists every
    constructor of `FieldOp`. -/
def fieldKind : FieldOp → LeakKind
  | .fInv _ => .vtCall "field.inv"
  | .fAdd _ | .fSub _ | .fNeg _ | .fMul _ | .fConst _ _ | .fCopy _ | .fieldDouble _
  | .fieldSquare _ => .quiet

/-- The natural-number reading of a value of `fieldDialect`: an element of a prime field by
    its least natural representative, an element of an extension field as `0`. -/
def fieldValNat : (t : FieldTy) → ⟦t⟧ → Nat
  | .fp _, x => ZMod.val x
  | .fp2 _, _ => 0
  | .fp6 _, _ => 0
  | .fp12 _, _ => 0

/-- The leakage model of `fieldDialect`. -/
def fieldLeakModel : LeakModel fieldDialect where
  kind := fieldKind
  valNat := fieldValNat

/-- Every operation of `fieldDialect` other than inversion is quiet. -/
theorem fieldKind_quiet_of_ne_inv (op : FieldOp) (h : ∀ p, op ≠ .fInv p) :
    fieldKind op = .quiet := by
  cases op <;> first | rfl | exact absurd rfl (h _)

/-! ## 2. The leakage model of the coproduct -/

/-- The leakage model of `nfFieldDialect`: the coproduct of `nfLeakModel` and
    `fieldLeakModel`. -/
def nfFieldLeakModel : LeakModel nfFieldDialect :=
  sumLeak nfLeakModel fieldLeakModel

/-- An operation of the left summand has the class `nfKind` gives it. -/
@[simp] theorem nfFieldLeakModel_kind_inl (op : NfOp) :
    nfFieldLeakModel.kind (.inl op) = nfKind op := rfl

/-- An operation of the right summand has the class `fieldKind` gives it. -/
@[simp] theorem nfFieldLeakModel_kind_inr (op : FieldOp) :
    nfFieldLeakModel.kind (.inr op) = fieldKind op := rfl

/-- A field operation other than inversion emits no event in the coproduct. -/
theorem nfField_opLeak_inr (op : FieldOp) (h : ∀ p, op ≠ .fInv p)
    (vals : HVector (fun t => ⟦t⟧)
      ((DialectSignature.sig (d := fieldDialect) op).map (Sum.inr (α := NfTy)))) :
    opLeak nfFieldLeakModel (.inr op) vals = [] :=
  opLeak_inr_quiet nfLeakModel fieldLeakModel op (fieldKind_quiet_of_ne_inv op h) vals

/-- The leakage run of a program of `nfFieldDialect` over the leaf table of the builtin
    table `bi`. -/
abbrev nfFieldLeakRun (bi : _root_.Hax.Builtins) (fuel : Nat) {Γ : Ctxt nfFieldDialect}
    {ts : List nfFieldDialect.Ty} (p : NFProg nfFieldDialect Γ ts) (V : Valuation Γ) :
    Option (Valuation ts × List CTLeak) :=
  @NFProg.leakRunM nfFieldDialect _ _ _ _ (nfFieldDenote (tableOf bi)) nfFieldLeakModel fuel
    _ _ p V

/-- **The level checker on `nfFieldDialect`.** A program the checker `levelCheck'` accepts
    at `nfFieldLeakModel` for the entry labels `L` is constant time for `L` relative to the
    runs that succeed, over every leaf table. -/
theorem nfField_nfCTRel_of_levelCheck' (T : NfLeafTable) (fuel : Nat)
    {Γ : Ctxt nfFieldDialect} {ts : List nfFieldDialect.Ty} (p : NFProg nfFieldDialect Γ ts)
    (L : Labels Γ) (h : (NFProg.levelCheck' nfFieldLeakModel p L).isSome) :
    @NFCTRel nfFieldDialect _ _ _ _ (nfFieldDenote T) nfFieldLeakModel Γ ts L fuel p :=
  @NFProg.nfCTRel_of_levelCheck' nfFieldDialect _ _ _ _ (nfFieldDenote T) nfFieldLeakModel
    fuel Γ ts p L h

end CatCrypt.Crypto.Hax.NFFieldSum
