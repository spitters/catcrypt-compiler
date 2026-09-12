/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DerivedToFieldLowering
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
public import Mathlib.Data.ZMod.Basic

/-!
# Front recognizer: `primeir-hax` `Field::double` / `square` / `pow` → `derivedDialect`

The `primeir-hax` `Field` trait (`primeir-hax/src/lib.rs`; extracted class
`Primeir_hax.Field`) carries `square`, `double` and `pow` alongside the four
arithmetic slots. `CompileFromHaxPrimeIrField.recognizeFieldOp` keys the
arithmetic slots onto `fieldDialect`; the three derived slots are keyed here onto
`derivedDialect`, which is where prime-ir's `field.square` / `field.double` /
`field.powui` are factored.

The recognized leaf reaches bytes through
`DerivedToField.lowerDerivedToField` into `fieldDialect` and then the existing
`fieldComToJasmin`, so each tie below is stated twice: once at the recognized
`derivedDialect` leaf, and once at its `fieldDialect` image.

`Field::pow` takes its exponent as little-endian `u64` limbs
(`pow (self) : Self -> RustSlice u64 -> RustM Self`). `DerivedOp.fieldPow` takes
the exponent as a `Nat`, so the recognizer takes the resolved exponent as a
parameter; resolving limbs to a `Nat` is the caller's step, as with the
Montgomery parameters in `CompileFromHaxPrimeIrMontMul`.

## Main definitions

* `recognizeDerivedOp`: `Field::double` / `Field::square` → `DerivedOp`.
* `recognizeFieldPowOp`: `Field::pow` at a resolved exponent → `DerivedOp`.
* `fieldDoubleLeaf` / `fieldSquareLeaf` / `fieldPowLeaf`: the single-op
  `Com derivedDialect` leaves.

## Main results

* `primeir_field_double_recognized_denote` and its `square` / `pow` siblings:
  each leaf denotes to the field operation the trait method names.
* `primeir_field_double_lowers_to_field` and its siblings: the same value after
  lowering to `fieldDialect`.
* `primeir_field_derived_recognized`: recognition, emit and both ties together.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrDerived

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
open CatCrypt.Crypto.SecureCompilation.VIR.DerivedToField

/-! ## 1. The recognition entries -/

/-- Recognize a resolved `primeir-hax` `Field::double` or `Field::square`
    trait-method name as the `DerivedOp` at modulus `p`. Fail-closed: any other
    head returns `none`. Both the fully-qualified `Primeir_hax.Field.<m>` and the
    bare `Field.<m>` forms are accepted, matching `recognizeFieldOp`. -/
def recognizeDerivedOp (name : String) (p : Nat) : Option DerivedOp :=
  if name = "Primeir_hax.Field.double" ∨ name = "Field.double" then
    some (.fieldDouble p)
  else if name = "Primeir_hax.Field.square" ∨ name = "Field.square" then
    some (.fieldSquare p)
  else none

/-- Recognize a resolved `primeir-hax` `Field::pow` trait-method name as
    `DerivedOp.fieldPow` at modulus `p` and resolved exponent `k`. Separate from
    `recognizeDerivedOp` because the op carries the exponent, which the head name
    does not supply. -/
def recognizeFieldPowOp (name : String) (p k : Nat) : Option DerivedOp :=
  if name = "Primeir_hax.Field.pow" ∨ name = "Field.pow" then
    some (.fieldPow p k)
  else none

@[simp] theorem recognize_double (p : Nat) :
    recognizeDerivedOp "Primeir_hax.Field.double" p = some (.fieldDouble p) := rfl

@[simp] theorem recognize_double_bare (p : Nat) :
    recognizeDerivedOp "Field.double" p = some (.fieldDouble p) := rfl

@[simp] theorem recognize_square (p : Nat) :
    recognizeDerivedOp "Primeir_hax.Field.square" p = some (.fieldSquare p) := rfl

@[simp] theorem recognize_square_bare (p : Nat) :
    recognizeDerivedOp "Field.square" p = some (.fieldSquare p) := rfl

@[simp] theorem recognize_pow (p k : Nat) :
    recognizeFieldPowOp "Primeir_hax.Field.pow" p k = some (.fieldPow p k) := rfl

/-- An arithmetic-slot head is rejected here: those are keyed by
    `CompileFromHaxPrimeIrField.recognizeFieldOp` onto `fieldDialect`. -/
theorem recognize_unknown (p : Nat) :
    recognizeDerivedOp "Primeir_hax.Field.mul" p = none := rfl

/-- `pow` is not recognized by the double/square entry. -/
theorem recognize_pow_not_derived (p : Nat) :
    recognizeDerivedOp "Primeir_hax.Field.pow" p = none := rfl

/-! ## 2. Emit: the recognized op as a single-op `Com derivedDialect` leaf

Every derived op is unary `fp p → fp p`, so each leaf takes one context variable
and returns the applied op, mirroring the unary field leaves (`fNegLeaf`,
`fInvLeaf`) in `CompileFromHaxPrimeIrField.lean`. -/

/-- The `double` emit leaf: `let c = fieldDouble a; ret c` over `[fp p]`. -/
def fieldDoubleLeaf (p : Nat) :
    Com derivedDialect [DerivedTy.fp p] (DerivedTy.fp p) :=
  .var (.mk (.fieldDouble p) rfl (.cons .here .nil)) (.ret .here)

/-- The `square` emit leaf. -/
def fieldSquareLeaf (p : Nat) :
    Com derivedDialect [DerivedTy.fp p] (DerivedTy.fp p) :=
  .var (.mk (.fieldSquare p) rfl (.cons .here .nil)) (.ret .here)

/-- The `pow` emit leaf at resolved exponent `k`. -/
def fieldPowLeaf (p k : Nat) :
    Com derivedDialect [DerivedTy.fp p] (DerivedTy.fp p) :=
  .var (.mk (.fieldPow p k) rfl (.cons .here .nil)) (.ret .here)

/-! ## 3. The value tie at the recognized leaf -/

/-- The recognized `Field::double` call denotes to `a + a`. -/
theorem primeir_field_double_recognized_denote (p : Nat) (a : ZMod p) :
    (fieldDoubleLeaf p).denote (.cons a .nil) = a + a := rfl

/-- The recognized `Field::square` call denotes to `a * a`. -/
theorem primeir_field_square_recognized_denote (p : Nat) (a : ZMod p) :
    (fieldSquareLeaf p).denote (.cons a .nil) = a * a := rfl

/-- The recognized `Field::pow` call denotes to `a ^ k`. -/
theorem primeir_field_pow_recognized_denote (p k : Nat) (a : ZMod p) :
    (fieldPowLeaf p k).denote (.cons a .nil) = a ^ k := rfl

/-! ## 4. The value tie after lowering to `fieldDialect`

`fieldDialect` is the dialect that reaches bytes, so these are the statements
that connect a recognized `primeir-hax` call to the emit spine. Each follows
from `lowerDerivedToField_denote` — the whole-program lowering theorem — applied
at the one-op leaf. -/

/-- The lowered `Field::double` leaf denotes to `a + a` in `fieldDialect`. -/
theorem primeir_field_double_lowers_to_field (p : Nat) (a : ZMod p) :
    (lowerDerivedToField (fieldDoubleLeaf p)).denote (mapVal (.cons a .nil))
      = a + a := by
  rw [lowerDerivedToField_denote]
  rfl

/-- The lowered `Field::square` leaf denotes to `a * a` in `fieldDialect`. -/
theorem primeir_field_square_lowers_to_field (p : Nat) (a : ZMod p) :
    (lowerDerivedToField (fieldSquareLeaf p)).denote (mapVal (.cons a .nil))
      = a * a := by
  rw [lowerDerivedToField_denote]
  rfl

/-- The lowered `Field::pow` leaf denotes to `a ^ k` in `fieldDialect`, with the
    exponent expanded to a multiplication chain. -/
theorem primeir_field_pow_lowers_to_field (p k : Nat) (a : ZMod p) :
    (lowerDerivedToField (fieldPowLeaf p k)).denote (mapVal (.cons a .nil))
      = a ^ k := by
  rw [lowerDerivedToField_denote]
  rfl

/-! ## 5. Recognition, emit and both ties together -/

/-- **The `Field::double` slot, end to end.** The recognizer accepts the name,
    the leaf carrying the returned op denotes to `a + a`, and so does its
    `fieldDialect` image. -/
theorem primeir_field_derived_recognized (p : Nat) (a : ZMod p) :
    recognizeDerivedOp "Primeir_hax.Field.double" p = some (.fieldDouble p) ∧
    (fieldDoubleLeaf p).denote (.cons a .nil) = a + a ∧
    (lowerDerivedToField (fieldDoubleLeaf p)).denote (mapVal (.cons a .nil))
      = a + a :=
  ⟨rfl, rfl, primeir_field_double_lowers_to_field p a⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrDerived
