/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse
public import CatCrypt.Crypto.SecureCompilation.VIR.PrimeIrStructuralOps

/-!
# Agreement between folded ops and their originating dialects' leaves

Seven ops that were carried by three single-purpose dialects — `montInverse`
(`montInverseDialect`), `polyToTensor` / `polyFromTensor` / `residueEncode` /
`residueDecode` (`structDialect`), and `fieldDouble` / `fieldSquare`
(`derivedDialect`) — are also constructors of the two dialects that already
carry traffic and reach bytes: `modArithDialect` and `fieldDialect`.  This
module states, one theorem per folded op, that the receiving dialect's
denotation is the originating dialect's leaf function.

## Why the ops were folded rather than kept in their own dialects

`Com` is indexed by a single `Dialect` (`VIR/Core.lean`), so an op living in a
dialect of its own can never appear in a program beside an op from another
dialect: a `montInverse` could not sit next to a `modMul`, and a `fieldSquare`
could not sit next to an `fMul`.  The alternative to folding was a dialect
coproduct — `modArithDialect ⊕ montInverseDialect` and
`fieldDialect ⊕ derivedDialect`, with an injection per summand and a matching
`DialectSignature` / `DialectDenote` by cases.  Folding was chosen because the
value types already coincide: `MontInverseTy.fp p`, `StructTy.residue p` and
`ModArithTy.fp p` all denote `ZMod p`; `StructTy.poly q n`, `StructTy.tensor q n`
and `ModArithTy.fpVec q n` all denote `Fin n → ZMod q`; `StructTy.bits w` and
`ModArithTy.word w` both denote `BitVec w`; and `DerivedTy.fp p` and
`FieldTy.fp p` both denote `ZMod p`.  With coinciding carriers the coproduct's
injection would be the identity on values, so it would add a layer of
constructors without adding an inhabitant.

`fieldPow` is not folded: it expands to a multiply chain, and
`FieldDescent.fieldFpDescent` is a single-`Expr` `LoweringData` that cannot host
a multi-op expansion.  It stays in `derivedDialect` with the lowering in
`DerivedToFieldLowering.lean`.

## Main results

* `montInverse_agrees` — `modArithDialect`'s `montInverse` denotes to
  `ModArithMontInverse.montInverseF`.
* `polyToTensor_agrees`, `polyFromTensor_agrees` — the coefficient-vector
  reinterprets denote to `PrimeIrStructuralOps.polyToTensorF` /
  `polyFromTensorF`.
* `residueEncode_agrees`, `residueDecode_agrees` — the bitcast reinterprets
  denote to `PrimeIrStructuralOps.residueEncodeF` / `residueDecodeF`.
* `fieldDouble_agrees`, `fieldSquare_agrees` — `fieldDialect`'s doubling and
  squaring denote to `FieldDerivedOps.fieldDoubleF` / `fieldSquareF`.

Every one holds by `rfl`: each receiving-dialect denotation is definitionally
the originating dialect's leaf, so the correctness lemmas already proved about
those leaves (`montInverse_spec`, `residueDecode_residueEncode`,
`fieldSquare_eq_pow`, …) transfer to the folded ops by rewriting with these
equalities.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FoldedOpAgreement

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect (modArithDenote)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect (fieldDenote)

/-! ## 1. Folded into `modArithDialect` -/

/-- The `modArithDialect` Montgomery-domain inverse denotes to
    `montInverseDialect`'s leaf `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹`. -/
theorem montInverse_agrees (p : Nat) (rInv x : ZMod p) :
    modArithDenote.denote (.montInverse p rInv) (.cons x .nil)
      = ModArithMontInverse.montInverseF rInv x := rfl

/-- The `modArithDialect` coefficient-vector-to-tensor reinterpret denotes to
    `structDialect`'s `poly.to_tensor` leaf. -/
theorem polyToTensor_agrees (q n : Nat) (v : Fin n → ZMod q) :
    modArithDenote.denote (.polyToTensor q n) (.cons v .nil)
      = PrimeIrStructuralOps.polyToTensorF q n v := rfl

/-- The `modArithDialect` tensor-to-coefficient-vector reinterpret denotes to
    `structDialect`'s `poly.from_tensor` leaf. -/
theorem polyFromTensor_agrees (q n : Nat) (v : Fin n → ZMod q) :
    modArithDenote.denote (.polyFromTensor q n) (.cons v .nil)
      = PrimeIrStructuralOps.polyFromTensorF q n v := rfl

/-- The `modArithDialect` residue-to-bits reinterpret denotes to
    `structDialect`'s bitcast-encode leaf. -/
theorem residueEncode_agrees (p w : Nat) (a : ZMod p) :
    modArithDenote.denote (.residueEncode p w) (.cons a .nil)
      = PrimeIrStructuralOps.residueEncodeF p w a := rfl

/-- The `modArithDialect` bits-to-residue reinterpret denotes to
    `structDialect`'s bitcast-decode leaf. -/
theorem residueDecode_agrees (p w : Nat) (b : BitVec w) :
    modArithDenote.denote (.residueDecode p w) (.cons b .nil)
      = PrimeIrStructuralOps.residueDecodeF p w b := rfl

/-! ## 2. Folded into `fieldDialect` -/

/-- The `fieldDialect` doubling denotes to `derivedDialect`'s `field.double`
    leaf `a ↦ a + a`. -/
theorem fieldDouble_agrees (p : Nat) (a : ZMod p) :
    fieldDenote.denote (.fieldDouble p) (.cons a .nil)
      = FieldDerivedOps.fieldDoubleF p a := rfl

/-- The `fieldDialect` squaring denotes to `derivedDialect`'s `field.square`
    leaf `a ↦ a * a`. -/
theorem fieldSquare_agrees (p : Nat) (a : ZMod p) :
    fieldDenote.denote (.fieldSquare p) (.cons a .nil)
      = FieldDerivedOps.fieldSquareF p a := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.FoldedOpAgreement
