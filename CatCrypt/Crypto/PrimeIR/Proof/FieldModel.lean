/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.PrimeIR.Extraction.Fp256Mont_haxpipe
public import CatCrypt.Crypto.Bridges.Transfer.HaxIntTransfer

/-!
# Field models of the emitted `primeir-hax` field classes

The hax extraction of `primeir-hax` emits the Rust traits `Field` and `CtField` as
the classes `Primeir.Field` and `Primeir.CtField`, with operations and no laws.
A `FieldModel Self K` interprets an instance of `Primeir.Field Self` as the field
`K` along a valuation `val : Self → K`, on the representations a predicate `Valid`
admits: each method computes the corresponding operation of `K` on the represented
values and preserves `Valid`. `CtFieldModel` adds the constant-time selection and
the zero test of `Primeir.CtField`.

A theorem about extracted code generic in `[Primeir.Field F]` is proved once over
a `FieldModel F K` and holds at every instance that carries one; for a prime field
`K` is `ZMod p`.

## Main definitions

* `FieldModel` — the laws of a `Primeir.Field` instance along a valuation into `K`.
* `CtFieldModel` — a `FieldModel` of a `Primeir.CtField` instance with the laws of
  `ct_select` and `is_zero`.
* `CtFieldModel.toBounded` — on the carrier `Array Int`, the `BoundedFieldModel` whose
  operations are the class methods.

## Main results

* `FieldModel.field_demo_spec` — the extracted generic `field_demo x y` represents
  `x * y + x` at every instance with a field model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PrimeIR

/-- A field `K` realized by an instance of the emitted class `Primeir.Field Self`: a
valuation `val`, a predicate `Valid`, and for each arithmetic method the law that it
computes the operation of `K` on the represented values and preserves `Valid`. The
byte methods `from_bytes` and `to_bytes` and the exponentiation `pow` are not
constrained. -/
structure FieldModel (Self : Type) [Primeir.Field Self] (K : Type) [Field K] where
  /-- The field element a representation stands for. -/
  val : Self → K
  /-- The representations on which the laws below hold. -/
  Valid : Self → Prop
  /-- `ZERO` represents `0`. -/
  zero_eq : val Primeir.Field.ZERO = 0
  /-- `ZERO` is valid. -/
  zero_valid : Valid Primeir.Field.ZERO
  /-- `ONE` represents `1`. -/
  one_eq : val Primeir.Field.ONE = 1
  /-- `ONE` is valid. -/
  one_valid : Valid Primeir.Field.ONE
  /-- `add` is the field sum. -/
  add_eq : ∀ a b, Valid a → Valid b → val (Primeir.Field.add a b) = val a + val b
  /-- `add` preserves `Valid`. -/
  add_valid : ∀ a b, Valid a → Valid b → Valid (Primeir.Field.add a b)
  /-- `sub` is the field difference. -/
  sub_eq : ∀ a b, Valid a → Valid b → val (Primeir.Field.sub a b) = val a - val b
  /-- `sub` preserves `Valid`. -/
  sub_valid : ∀ a b, Valid a → Valid b → Valid (Primeir.Field.sub a b)
  /-- `mul` is the field product. -/
  mul_eq : ∀ a b, Valid a → Valid b → val (Primeir.Field.mul a b) = val a * val b
  /-- `mul` preserves `Valid`. -/
  mul_valid : ∀ a b, Valid a → Valid b → Valid (Primeir.Field.mul a b)
  /-- `neg` is the field negation. -/
  neg_eq : ∀ a, Valid a → val (Primeir.Field.neg a) = - val a
  /-- `neg` preserves `Valid`. -/
  neg_valid : ∀ a, Valid a → Valid (Primeir.Field.neg a)
  /-- `square` is the field square. -/
  square_eq : ∀ a, Valid a → val (Primeir.Field.square a) = val a ^ 2
  /-- `square` preserves `Valid`. -/
  square_valid : ∀ a, Valid a → Valid (Primeir.Field.square a)
  /-- `double` is the field double. -/
  double_eq : ∀ a, Valid a → val (Primeir.Field.double a) = 2 * val a
  /-- `double` preserves `Valid`. -/
  double_valid : ∀ a, Valid a → Valid (Primeir.Field.double a)
  /-- `inv` is the field inverse at a nonzero argument. -/
  inv_eq : ∀ a, Valid a → val a ≠ 0 → val (Primeir.Field.inv a) = (val a)⁻¹
  /-- `inv` preserves `Valid`. -/
  inv_valid : ∀ a, Valid a → Valid (Primeir.Field.inv a)

/-- A field model of a `Primeir.CtField` instance: the laws of its `Primeir.Field`
methods, and the laws of the bit selection `ct_select` and the zero indicator
`is_zero`. -/
structure CtFieldModel (Self : Type) [Primeir.CtField Self] (K : Type) [Field K]
    [DecidableEq K] extends FieldModel Self K where
  /-- `ct_select` on a bit selects the first argument on `1`. -/
  ct_select_eq : ∀ (c : Int) (a b : Self), c = 0 ∨ c = 1 → Valid a → Valid b →
    val (Primeir.CtField.ct_select c a b) = if c = 1 then val a else val b
  /-- `ct_select` preserves `Valid`. -/
  ct_select_valid : ∀ (c : Int) (a b : Self), c = 0 ∨ c = 1 → Valid a → Valid b →
    Valid (Primeir.CtField.ct_select c a b)
  /-- `is_zero` is the indicator of `0`. -/
  is_zero_eq : ∀ a, Valid a →
    Primeir.CtField.is_zero a = if val a = 0 then 1 else 0

namespace FieldModel

variable {F : Type} [Primeir.Field F] {K : Type} [Field K] (M : FieldModel F K)

/-- The extracted generic `field_demo x y` is valid on valid arguments and represents
`x * y + x`. -/
theorem field_demo_spec [Inhabited F] {x y : F} (hx : M.Valid x) (hy : M.Valid y) :
    M.Valid (Primeir.field_demo x y) ∧
      M.val (Primeir.field_demo x y) = M.val x * M.val y + M.val x := by
  unfold Primeir.field_demo
  exact ⟨M.add_valid _ _ (M.mul_valid _ _ hx hy) hx,
    by rw [M.add_eq _ _ (M.mul_valid _ _ hx hy) hx, M.mul_eq _ _ hx hy]⟩

end FieldModel

namespace CtFieldModel

open CatCrypt.Crypto.Bridges.Transfer.HaxInt (BoundedFieldModel)

-- The extraction declares instances on `Fp256Mont_T`, which unfolds to `Array Int`;
-- they are erased here so that the class methods below are those of the variable.
attribute [-instance] Primeir.instFieldFp256Mont_T Primeir.instModArithFp256Mont_T
  Primeir.instCtFieldFp256Mont_T Primeir.instSqrtRatioFp256Mont_T

variable [Primeir.CtField (Array Int)] {K : Type} [Field K] [DecidableEq K]

/-- A field model of a `Primeir.CtField` instance on `Array Int` as a
`BoundedFieldModel`, with the class methods as the operations. -/
def toBounded (M : CtFieldModel (Array Int) K) : BoundedFieldModel K where
  mul := Primeir.Field.mul
  square := Primeir.Field.square
  add := Primeir.Field.add
  sub := Primeir.Field.sub
  neg := Primeir.Field.neg
  inv := Primeir.Field.inv
  ct_select := Primeir.CtField.ct_select
  is_zero := Primeir.CtField.is_zero
  ONE := Primeir.Field.ONE
  ZERO := Primeir.Field.ZERO
  val := M.val
  Valid := M.Valid
  mul_eq := M.mul_eq
  mul_valid := M.mul_valid
  square_eq := M.square_eq
  square_valid := M.square_valid
  add_eq := M.add_eq
  add_valid := M.add_valid
  sub_eq := M.sub_eq
  sub_valid := M.sub_valid
  neg_eq := M.neg_eq
  neg_valid := M.neg_valid
  inv_eq := M.inv_eq
  inv_valid := M.inv_valid
  one_eq := M.one_eq
  one_valid := M.one_valid
  zero_eq := M.zero_eq
  zero_valid := M.zero_valid
  is_zero_eq := M.is_zero_eq
  ct_select_eq := M.ct_select_eq
  ct_select_valid := M.ct_select_valid

end CtFieldModel

end CatCrypt.Crypto.PrimeIR
