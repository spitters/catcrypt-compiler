/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Builtins

/-!
# Leaves for struct constructors, projections and updates

The printer renders an `n`-field struct `S` as the right-nested product
`abbrev S_T := T₀ × T₁ × … × Tₙ₋₁`, with a constructor `def S … := (f₀, …, fₙ₋₁)`,
projections `def «.f» (x : S_T)` or `def «S.f» (x : S_T)` along the path `projPath i n`,
and the update `struct_update#S#i#n` rendered as a nest of `Hax.struct_update_snd`
around one `Hax.struct_update_fst` (the last field: around one `struct_update_snd`).
A one-field struct is the field itself, with identity projection and update. The
literal calls the same names with `.app`. `HaxEnc` encodes a right-nested product as
one flat `.tuple`, so the leaves act on flat tuples:

| literal | leaf | transport |
|---|---|---|
| `.app "S" [a₀, …]` | `ctorLeaf n` | `ctorLeaf_prod`, `ctorLeaf_one` |
| `.app ".f" [s]`, `.app "S.f" [s]` | `projLeaf i n` | `projLeaf_prod`, `projLeaf_one` |
| `.app "struct_update#S#i#n" [s, v]` | `updateLeaf i n` | `updateLeaf_prod`, `updateLeaf_one` |

`HaxField α i β` is field `i` of the right-nested product `α`: its `get` is the
printer's projection path and its `set` the printer's update nest, both up to
definitional unfolding. `HaxField.Lawful` states that they commute with the flat
encoding; its instances cover every right-nested product whose last component is not
itself a product. A struct whose last field has a product type is outside the
encoding: the flat encoding splits that field into components, while the literal
builds it as one nested tuple.

A `StructSpec` lists a struct's constructor name, field count and the projection names
its literal uses; `StructSpec.table` is its constructor, projection and update leaves,
the update names built by `structUpdateHead`.

## Main definitions

* `ctorLeaf`, `projLeaf`, `updateLeaf`
* `HaxField`, `fieldGet`, `fieldSet`, `HaxField.Lawful`
* `StructSpec`, `StructSpec.table`, `structsTable`

## Main results

* `ctorLeaf_prod`, `projLeaf_prod`, `updateLeaf_prod` — the `corres_app` equations of the
  three leaves on encoded products
* `ctorLeaf_one`, `projLeaf_one`, `updateLeaf_one` — the same for a one-field struct
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ### Leaves -/

/-- The constructor leaf of an `n`-field struct: the flat tuple of the arguments, and
    the argument itself for a one-field struct. -/
def ctorLeaf (n : Nat) : Leaf := fun vs =>
  if vs.length = n then (if n = 1 then vs.head? else some (.tuple vs)) else none

/-- The projection leaf of field `i` of an `n`-field struct: index `i` of the tuple, and
    the value itself for a one-field struct. -/
def projLeaf (i n : Nat) : Leaf
  | [v] =>
    if n ≤ 1 then some v
    else match v with
      | .tuple vs => vs[i]?
      | _ => none
  | _ => none

/-- The update leaf `struct_update#S#i#n`: the tuple with index `i` replaced, and the new
    value itself for a one-field struct. -/
def updateLeaf (i n : Nat) : Leaf
  | [s, v] =>
    if n ≤ 1 then some v
    else match s with
      | .tuple vs => if i < vs.length then some (.tuple (vs.set i v)) else none
      | _ => none
  | _ => none

/-! ### Fields of right-nested products -/

/-- Field `i` of the right-nested product `α`, of type `β`: field `0` of `α × γ` is the
    first component, field `i + 1` is field `i` of the second, and a type that is not a
    product is its own field `0`. -/
class HaxField (α : Type) (i : Nat) (β : outParam Type) where
  /-- Read the field. -/
  get : α → β
  /-- Replace the field. -/
  set : α → β → α

/-- Read field `i`. -/
def fieldGet (i : Nat) {α β : Type} [HaxField α i β] : α → β := HaxField.get i

/-- Replace field `i`. -/
def fieldSet (i : Nat) {α β : Type} [HaxField α i β] : α → β → α := HaxField.set i

instance HaxField.head {α γ : Type} : HaxField (α × γ) 0 α := ⟨Prod.fst, fun p v => (v, p.2)⟩

instance HaxField.tail {α γ β : Type} {i : Nat} [HaxField γ i β] :
    HaxField (α × γ) (i + 1) β :=
  ⟨fun p => fieldGet i p.2, fun p v => (p.1, fieldSet i p.2 v)⟩

instance (priority := low) HaxField.last {α : Type} : HaxField α 0 α := ⟨id, fun _ v => v⟩

/-- The field agrees with the flat encoding: index `i` of the component list is the
    encoded field, and replacing index `i` is the encoding of the updated product. -/
class HaxField.Lawful (α : Type) (i : Nat) (β : Type) [HaxField α i β] [HaxTupleEnc α]
    [HaxEnc β] : Prop where
  get_enc : ∀ p : α, (HaxTupleEnc.encList p)[i]? = some (enc (fieldGet i p))
  set_enc : ∀ (p : α) (v : β),
    (HaxTupleEnc.encList p).set i (enc v) = HaxTupleEnc.encList (fieldSet i p v)

instance {α γ : Type} [HaxEnc α] [HaxTupleEnc γ] : HaxField.Lawful (α × γ) 0 α :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

instance {α γ β : Type} {i : Nat} [HaxEnc α] [HaxTupleEnc γ] [HaxField γ i β] [HaxEnc β]
    [HaxField.Lawful γ i β] : HaxField.Lawful (α × γ) (i + 1) β :=
  ⟨fun p => HaxField.Lawful.get_enc (i := i) p.2,
   fun p v => congrArg (enc p.1 :: ·) (HaxField.Lawful.set_enc (i := i) p.2 v)⟩

instance (priority := low) {α : Type} [HaxEnc α] :
    @HaxField.Lawful α 0 α HaxField.last HaxTupleEnc.single _ :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-! ### Transport -/

section Transport

variable {α γ β : Type} [HaxEnc α] [HaxTupleEnc γ]

/-- **Constructor.** The constructor leaf maps the components of a product to its
    encoding. -/
theorem ctorLeaf_prod (p : α × γ) {n : Nat} (hlen : (HaxTupleEnc.encList p).length = n)
    (hn : 2 ≤ n) : ctorLeaf n (HaxTupleEnc.encList p) = some (enc p) := by
  simp only [ctorLeaf, hlen, if_true, if_neg (show n ≠ 1 by omega)]
  rfl

theorem ctorLeaf_one (a : α) : ctorLeaf 1 [enc a] = some (enc a) := rfl

/-- **Projection.** The projection leaf of field `i` maps the encoding of a product to
    the encoding of the field. -/
theorem projLeaf_prod {i : Nat} [HaxField (α × γ) i β] [HaxEnc β]
    [HaxField.Lawful (α × γ) i β] (p : α × γ) {n : Nat} (hn : 2 ≤ n) :
    projLeaf i n [enc p] = some (enc (fieldGet i p)) := by
  simp only [projLeaf, if_neg (show ¬n ≤ 1 by omega)]
  exact HaxField.Lawful.get_enc p

theorem projLeaf_one (a : α) : projLeaf 0 1 [enc a] = some (enc a) := rfl

/-- **Update.** The update leaf of field `i` maps the encodings of a product and a value
    to the encoding of the product with the field replaced. -/
theorem updateLeaf_prod {i : Nat} [HaxField (α × γ) i β] [HaxEnc β]
    [HaxField.Lawful (α × γ) i β] (p : α × γ) (v : β) {n : Nat} (hn : 2 ≤ n) :
    updateLeaf i n [enc p, enc v] = some (enc (fieldSet i p v)) := by
  have hi : i < (HaxTupleEnc.encList p).length :=
    (List.getElem?_eq_some_iff.mp (HaxField.Lawful.get_enc (β := β) p)).1
  simp only [updateLeaf, if_neg (show ¬n ≤ 1 by omega)]
  change (if i < (HaxTupleEnc.encList p).length then
    some (Value.tuple ((HaxTupleEnc.encList p).set i (enc v))) else none) = _
  rw [if_pos hi, HaxField.Lawful.set_enc]
  rfl

theorem updateLeaf_one (a b : α) : updateLeaf 0 1 [enc a, enc b] = some (enc b) := rfl

end Transport

/-! ### The table of a struct -/

/-- A struct of an extraction: its constructor name, its field count, and the names the
    literal uses for its projections with their field indices. -/
structure StructSpec where
  /-- The constructor name. -/
  name : String
  /-- The field count. -/
  arity : Nat
  /-- The projection names of the literal (`.f` or `S.f`) and their field indices. -/
  projs : List (String × Nat)

/-- The leaves of a struct: the constructor, the projections, and the update of every
    field under its name `struct_update#S#i#n`. -/
def StructSpec.table (s : StructSpec) : Table :=
  (s.name, ctorLeaf s.arity) :: (s.projs.map fun p => (p.1, projLeaf p.2 s.arity)) ++
    (List.range s.arity).map fun i => (structUpdateHead s.name i s.arity, updateLeaf i s.arity)

/-- The leaves of the structs of an extraction. -/
def structsTable (ss : List StructSpec) : Table := ss.flatMap StructSpec.table

end Hax.Ascent
