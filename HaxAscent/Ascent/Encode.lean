/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF

/-!
# Encoding surface values as `Hax.Value`

`HaxEnc α` maps a value of the surface type `α` of a haxpipeT extraction to the untyped
runtime value `Hax.Value` that `denote'` computes for it:

| surface type | value |
|---|---|
| `Int` | `.int n` |
| `Bool` | `.bool b` |
| `Unit` | `.unit` |
| `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize` | `.uint w x.toNat` |
| `Int8`, `Int16`, `Int32`, `Int64`, `ISize` | `.sint w x.toInt` |
| `Array α` | `.array (xs.toList.map enc)` |
| `Option α` | `.option (o.map enc)` |
| `α₀ × α₁ × … × αₙ` | `.tuple [enc a₀, enc a₁, …, enc aₙ]` |
| a `ControlFlow` `Break b` / `Continue c` | `.controlFlow true (enc b)` / `.controlFlow false (enc c)` |

## Products

The printer renders an `n`-field struct as the right-nested product
`A₀ × (A₁ × (… × Aₙ))` (`structTupleType`, `projPath`: field `i < n - 1` is `.2`
repeated `i` times then `.1`, the last field is `.2` repeated `n - 1` times), while the
literal builds a struct as one flat `.tuple` of arity `n` and reads a field with
`Value.projIdx i`. The encoding is therefore flat: a right-nested product encodes as a
single tuple of all its components (`HaxTupleEnc`), and `projIdx_enc_prod_zero`,
`projIdx_enc_prod_succ` and `projIdx_tuple_single` state that `projIdx i` of the
encoding is the encoding of the component the printer's path selects. A product whose
last component is itself a product is flattened as well; the two readings of
`A × (B × C)` are the same Lean type, so the encoding picks the flat one.

## `ControlFlow`

The runtime's `ControlFlow B C` is not imported here; `encCF` encodes its sum view
`B ⊕ C` (`Sum.inl b` is `Break b`).

## Main definitions

* `HaxEnc`, `HaxEnc.Plain` (the encoding is never a top-level control-flow value)
* `HaxTupleEnc`, `encCF`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- An encoding of the surface type `α` into runtime values. -/
class HaxEnc (α : Type) where
  /-- The runtime value of a surface value. -/
  enc : α → Value

export HaxEnc (enc)

/-- The encoding never produces a top-level control-flow value. -/
class HaxEnc.Plain (α : Type) [HaxEnc α] : Prop where
  not_cf : ∀ a : α, (enc a).isControlFlow = false

instance : HaxEnc Int := ⟨.int⟩
instance : HaxEnc Bool := ⟨.bool⟩
instance : HaxEnc Unit := ⟨fun _ => .unit⟩
instance : HaxEnc UInt8 := ⟨fun x => .uint .w8 x.toNat⟩
instance : HaxEnc UInt16 := ⟨fun x => .uint .w16 x.toNat⟩
instance : HaxEnc UInt32 := ⟨fun x => .uint .w32 x.toNat⟩
instance : HaxEnc UInt64 := ⟨fun x => .uint .w64 x.toNat⟩
instance : HaxEnc USize := ⟨fun x => .uint .wsize x.toNat⟩
instance : HaxEnc Int8 := ⟨fun x => .sint .w8 x.toInt⟩
instance : HaxEnc Int16 := ⟨fun x => .sint .w16 x.toInt⟩
instance : HaxEnc Int32 := ⟨fun x => .sint .w32 x.toInt⟩
instance : HaxEnc Int64 := ⟨fun x => .sint .w64 x.toInt⟩
instance : HaxEnc ISize := ⟨fun x => .sint .wsize x.toInt⟩

instance {α : Type} [HaxEnc α] : HaxEnc (Array α) := ⟨fun xs => .array (xs.toList.map enc)⟩
instance {α : Type} [HaxEnc α] : HaxEnc (Option α) := ⟨fun o => .option (o.map enc)⟩

/-- The components of a right-nested product, each encoded. -/
class HaxTupleEnc (α : Type) where
  /-- The encoded components, outermost first. -/
  encList : α → List Value

/-- A type that is not a product is a single component. -/
instance (priority := low) HaxTupleEnc.single {α : Type} [HaxEnc α] : HaxTupleEnc α :=
  ⟨fun a => [enc a]⟩

/-- A product contributes its first component and the components of its second. -/
instance HaxTupleEnc.prod {α β : Type} [HaxEnc α] [HaxTupleEnc β] : HaxTupleEnc (α × β) :=
  ⟨fun p => enc p.1 :: HaxTupleEnc.encList p.2⟩

/-- A product encodes as the flat tuple of its components. -/
instance {α β : Type} [HaxEnc α] [HaxTupleEnc β] : HaxEnc (α × β) :=
  ⟨fun p => .tuple (HaxTupleEnc.encList p)⟩

/-- The encoding of a `ControlFlow`, through its sum view: `Sum.inl b` is `Break b`,
    `Sum.inr c` is `Continue c`. -/
def encCF {B C : Type} [HaxEnc B] [HaxEnc C] : B ⊕ C → Value
  | .inl b => .controlFlow true (enc b)
  | .inr c => .controlFlow false (enc c)

section Lemmas

variable {α β : Type}

@[simp] theorem enc_int (n : Int) : enc n = .int n := rfl
@[simp] theorem enc_bool (b : Bool) : enc b = .bool b := rfl
@[simp] theorem enc_unit (u : Unit) : enc u = .unit := rfl
@[simp] theorem enc_array [HaxEnc α] (xs : Array α) : enc xs = .array (xs.toList.map enc) := rfl
@[simp] theorem enc_option [HaxEnc α] (o : Option α) : enc o = .option (o.map enc) := rfl

@[simp] theorem enc_prod [HaxEnc α] [HaxTupleEnc β] (a : α) (b : β) :
    enc (a, b) = .tuple (enc a :: HaxTupleEnc.encList b) := rfl

@[simp] theorem encList_single [HaxEnc α] (a : α) :
    (HaxTupleEnc.single (α := α)).encList a = [enc a] := rfl

/-- The first component of a product is at index `0`. -/
@[simp] theorem projIdx_enc_prod_zero [HaxEnc α] [HaxTupleEnc β] (a : α) (b : β) :
    (enc (a, b)).projIdx 0 = some (enc a) := rfl

/-- Index `i + 1` of a product is index `i` of the tuple of its second component. -/
theorem projIdx_enc_prod_succ [HaxEnc α] [HaxTupleEnc β] (a : α) (b : β) (i : Nat) :
    (enc (a, b)).projIdx (i + 1) = (Value.tuple (HaxTupleEnc.encList b)).projIdx i := rfl

/-- The last component of a flat tuple is the single component at index `0`. -/
@[simp] theorem projIdx_tuple_single [HaxEnc α] (a : α) :
    (Value.tuple ((HaxTupleEnc.single (α := α)).encList a)).projIdx 0 = some (enc a) := rfl

theorem projIdx_tuple_prod_zero [HaxEnc α] [HaxTupleEnc β] (a : α) (b : β) :
    (Value.tuple (HaxTupleEnc.encList (a, b))).projIdx 0 = some (enc a) := rfl

theorem projIdx_tuple_prod_succ [HaxEnc α] [HaxTupleEnc β] (a : α) (b : β) (i : Nat) :
    (Value.tuple (HaxTupleEnc.encList (a, b))).projIdx (i + 1) =
      (Value.tuple (HaxTupleEnc.encList b)).projIdx i := rfl

/-- **Projections commute with the encoding.** Field `i` of a flat tuple encoding of
    a right-nested product is the `i`-th encoded component. -/
theorem projIdx_enc_tuple [HaxTupleEnc α] (p : α) (i : Nat) :
    (Value.tuple (HaxTupleEnc.encList p)).projIdx i = (HaxTupleEnc.encList p)[i]? := rfl

instance : HaxEnc.Plain Int := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain Bool := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain Unit := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain UInt8 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain UInt16 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain UInt32 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain UInt64 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain USize := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain Int8 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain Int16 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain Int32 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain Int64 := ⟨fun _ => rfl⟩
instance : HaxEnc.Plain ISize := ⟨fun _ => rfl⟩
instance [HaxEnc α] : HaxEnc.Plain (Array α) := ⟨fun _ => rfl⟩
instance [HaxEnc α] : HaxEnc.Plain (Option α) := ⟨fun _ => rfl⟩
instance [HaxEnc α] [HaxTupleEnc β] : HaxEnc.Plain (α × β) := ⟨fun _ => rfl⟩

/-- A three-field product encodes as one flat tuple of arity three. This `rfl` is a
    static check that instance resolution picks the flattening product instance. -/
example : enc ((1 : Int), true, ()) = .tuple [.int 1, .bool true, .unit] := rfl

end Lemmas

end Hax.Ascent
