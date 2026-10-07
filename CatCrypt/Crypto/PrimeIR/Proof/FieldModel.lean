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

## Which operations each structure constrains

* `FieldModel` — `ZERO`, `ONE`, `add`, `sub`, `mul`, `neg`, `square`, `double`, `inv`.
  It states nothing about `pow`, `from_bytes` and `to_bytes`.
* `CtFieldModel` — those of `FieldModel`, and `ct_select` and `is_zero`.
* `FieldModel.PowLaws M` — `pow`: on an exponent given as little-endian 64-bit limbs,
  the power of the represented value to the natural number the limbs encode.
* `FieldModel.ByteLaws M len` — `from_bytes` and `to_bytes`: `from_bytes` of a byte array
  of any length represents its little-endian natural number cast to `K` (for `ZMod p`,
  reduced modulo `p`); `to_bytes` returns `len` bytes whose little-endian natural number
  casts to the represented value and which depend only on that value.

`PowLaws` and `ByteLaws` are propositions about a model, stated separately from
`FieldModel` so that a model is given before these three methods are specified.

A theorem about extracted code generic in `[Primeir.Field F]` is proved once over
a `FieldModel F K` and holds at every instance that carries one; for a prime field
`K` is `ZMod p`.

## Main definitions

* `FieldModel` — the laws of a `Primeir.Field` instance along a valuation into `K`.
* `CtFieldModel` — a `FieldModel` of a `Primeir.CtField` instance with the laws of
  `ct_select` and `is_zero`.
* `CtFieldModel.toBounded` — on the carrier `Array Int`, the `BoundedFieldModel` whose
  operations are the class methods.
* `leValue w xs` — the natural number with little-endian digits `xs` in base `2 ^ w`.
* `IsDigits w xs` — every entry of `xs` lies in `[0, 2 ^ w)`.
* `FieldModel.PowLaws`, `FieldModel.ByteLaws` — the laws of `pow`, and of `from_bytes`
  and `to_bytes`, of a field model.

## Main results

* `FieldModel.field_demo_spec` — the extracted generic `field_demo x y` represents
  `x * y + x` at every instance with a field model.
* `FieldModel.ByteLaws.from_bytes_to_bytes` — for a model with `ByteLaws`, decoding the
  encoding of a valid representation gives a valid representation of the same value.
* `FieldModel.ByteLaws.to_bytes_eq_iff` — for a model with `ByteLaws`, two valid
  representations have the same encoding exactly when they represent the same value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PrimeIR

/-- A field `K` realized by an instance of the emitted class `Primeir.Field Self`: a
valuation `val`, a predicate `Valid`, and for each arithmetic method the law that it
computes the operation of `K` on the represented values and preserves `Valid`. The
byte methods `from_bytes` and `to_bytes` and the exponentiation `pow` are constrained
by `FieldModel.ByteLaws` and `FieldModel.PowLaws`, not by this structure. -/
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

/-! ## Exponentiation and byte conversion -/

/-- The natural number whose little-endian digits in base `2 ^ w` are the entries of
`xs`: the first entry is the least significant digit. -/
def leValue (w : ℕ) (xs : Array Int) : ℕ :=
  xs.toList.foldr (fun x acc => x.toNat + 2 ^ w * acc) 0

/-- Every entry of `xs` is a digit in base `2 ^ w`: it lies in `[0, 2 ^ w)`. -/
def IsDigits (w : ℕ) (xs : Array Int) : Prop :=
  ∀ x ∈ xs.toList, 0 ≤ x ∧ x < 2 ^ w

namespace FieldModel

variable {F : Type} [Primeir.Field F] {K : Type} [Field K]

/-- The law of `pow` for a field model: on a valid representation and an exponent
given as little-endian 64-bit limbs, `pow` is valid and represents the power of the
represented value to the natural number the limbs encode. -/
structure PowLaws (M : FieldModel F K) : Prop where
  /-- `pow` is the power to the exponent the limbs encode. -/
  pow_eq : ∀ (a : F) (e : Array Int), M.Valid a → IsDigits 64 e →
    M.val (Primeir.Field.pow a e) = M.val a ^ leValue 64 e
  /-- `pow` preserves `Valid`. -/
  pow_valid : ∀ (a : F) (e : Array Int), M.Valid a → IsDigits 64 e →
    M.Valid (Primeir.Field.pow a e)

/-- The laws of `from_bytes` and `to_bytes` for a field model with encodings of `len`
bytes. `from_bytes` of a byte array of any length is valid and represents the
little-endian natural number of the bytes, cast to `K`. `to_bytes` of a valid
representation is an array of `len` bytes whose little-endian natural number casts to
the represented value, and it is the same array for two representations of one value. -/
structure ByteLaws (M : FieldModel F K) (len : ℕ) : Prop where
  /-- `from_bytes` represents the little-endian natural number of the bytes. -/
  from_bytes_eq : ∀ bs : Array Int, IsDigits 8 bs →
    M.val (Primeir.Field.from_bytes bs) = (leValue 8 bs : K)
  /-- `from_bytes` returns a valid representation. -/
  from_bytes_valid : ∀ bs : Array Int, IsDigits 8 bs →
    M.Valid (Primeir.Field.from_bytes bs : F)
  /-- `to_bytes` returns `len` entries. -/
  to_bytes_size : ∀ a : F, M.Valid a → (Primeir.Field.to_bytes a).size = len
  /-- `to_bytes` returns bytes. -/
  to_bytes_isDigits : ∀ a : F, M.Valid a → IsDigits 8 (Primeir.Field.to_bytes a)
  /-- The little-endian natural number of `to_bytes a` casts to the value of `a`. -/
  to_bytes_eq : ∀ a : F, M.Valid a → (leValue 8 (Primeir.Field.to_bytes a) : K) = M.val a
  /-- `to_bytes` depends only on the represented value. -/
  to_bytes_canonical : ∀ a b : F, M.Valid a → M.Valid b → M.val a = M.val b →
    Primeir.Field.to_bytes a = Primeir.Field.to_bytes b

namespace ByteLaws

variable {M : FieldModel F K} {len : ℕ}

/-- Decoding the encoding of a valid representation gives a valid representation of the
same value. -/
theorem from_bytes_to_bytes (B : M.ByteLaws len) {a : F} (ha : M.Valid a) :
    M.Valid (Primeir.Field.from_bytes (Primeir.Field.to_bytes a) : F) ∧
      M.val (Primeir.Field.from_bytes (Primeir.Field.to_bytes a) : F) = M.val a :=
  ⟨B.from_bytes_valid _ (B.to_bytes_isDigits a ha),
    (B.from_bytes_eq _ (B.to_bytes_isDigits a ha)).trans (B.to_bytes_eq a ha)⟩

/-- Two valid representations have the same encoding exactly when they represent the
same value. -/
theorem to_bytes_eq_iff (B : M.ByteLaws len) {a b : F} (ha : M.Valid a) (hb : M.Valid b) :
    Primeir.Field.to_bytes a = Primeir.Field.to_bytes b ↔ M.val a = M.val b :=
  ⟨fun h => by rw [← B.to_bytes_eq a ha, ← B.to_bytes_eq b hb, h],
    B.to_bytes_canonical a b ha hb⟩

end ByteLaws

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
