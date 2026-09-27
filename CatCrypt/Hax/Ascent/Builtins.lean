/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Corres

/-!
# Builtin tables from named leaves

`denote'` interprets a call `.app f args` by the builtin table `bi : Builtins`, and
`corres_app` asks for the equation `bi f (Vs σ) = some (V σ)`. This file builds tables
from named leaves and states that equation once for every leaf obtained from a Lean
function.

A `Leaf` is a partial function on argument values and a `Table` a list of named leaves.
`Table.over t base` interprets a name by its **first** entry in `t`, and a name with no
entry in `t` by `base`; entries of `t` take precedence over `base`, and an earlier entry
over a later one with the same name. A name with an entry whose leaf returns `none` on
the arguments is `none`; it does not fall through to `base`.

A leaf of a Lean function `g : A → B` is `liftFn g`: on the encoding of an argument `a`
it returns the encoding of `g a`. The argument tuple is encoded by `HaxArgs`, a list
encoding with one value per argument (`α₁ × (α₂ × … × Unit)`), which is injective when
each argument encoding is (`HaxEnc.Inj`); injectivity makes `liftFn` well defined
without a decoder.

## Main definitions

* `Leaf`, `Table`, `Table.over`, `Table.toBuiltins`
* the encoding `HaxEnc String`, which erases a string to `.unit`
* `HaxEnc.Inj`, `HaxTupleEnc.Inj`, `HaxArgs`
* `liftFn`, `leaf0`, `leaf1`, `leaf2`, `leaf3`, `leaf4`

## Main results

* `Table.over_of_lookup`, `Table.over_of_lookup_none` — reading a table
* `liftFn_encArgs` — the leaf of `g` maps the encoding of `a` to the encoding of `g a`
* `leaf0_apply` … `leaf4_apply` — the same for curried functions of up to four arguments
* `Table.over_leaf1` … `Table.over_leaf3` — the `corres_app` equation from a lookup
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- A leaf: the partial function a builtin table applies to the argument values of a
    call. -/
abbrev Leaf := List Value → Option Value

/-- A table of named leaves. -/
abbrev Table := List (String × Leaf)

namespace Table

/-- The builtin table of `t` over `base`: a name with an entry in `t` is interpreted by
    its first entry, every other name by `base`. -/
def over (t : Table) (base : Builtins) : Builtins := fun f vs =>
  match t.lookup f with
  | some g => g vs
  | none => base f vs

/-- The builtin table of `t` alone: a name with no entry is `none`. -/
def toBuiltins (t : Table) : Builtins := t.over fun _ _ => none

theorem over_of_lookup {t : Table} {base : Builtins} {f : String} {g : Leaf}
    (h : t.lookup f = some g) (vs : List Value) : t.over base f vs = g vs := by
  simp only [over, h]

theorem over_of_lookup_none {t : Table} {base : Builtins} {f : String}
    (h : t.lookup f = none) (vs : List Value) : t.over base f vs = base f vs := by
  simp only [over, h]

theorem toBuiltins_of_lookup {t : Table} {f : String} {g : Leaf}
    (h : t.lookup f = some g) (vs : List Value) : t.toBuiltins f vs = g vs :=
  over_of_lookup h vs

theorem lookup_cons_self (f : String) (g : Leaf) (t : Table) :
    List.lookup f ((f, g) :: t) = some g := by
  simp [List.lookup]

theorem lookup_cons_of_ne {f f' : String} (g : Leaf) (t : Table) (h : f ≠ f') :
    List.lookup f ((f', g) :: t) = List.lookup f t := by
  have hb : (f == f') = false := by simpa using h
  simp [List.lookup, hb]

theorem lookup_append_of_some {t₁ t₂ : Table} {f : String} {g : Leaf}
    (h : List.lookup f t₁ = some g) : List.lookup f (t₁ ++ t₂) = some g := by
  induction t₁ with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨f', g'⟩ := p
    by_cases hf : f = f'
    · subst hf
      simp only [List.cons_append, lookup_cons_self] at h ⊢
      exact h
    · simp only [List.cons_append, lookup_cons_of_ne _ _ hf] at h ⊢
      exact ih h

theorem lookup_append_of_none {t₁ t₂ : Table} {f : String}
    (h : List.lookup f t₁ = none) : List.lookup f (t₁ ++ t₂) = List.lookup f t₂ := by
  induction t₁ with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨f', g'⟩ := p
    by_cases hf : f = f'
    · subst hf
      simp at h
    · simp only [List.cons_append, lookup_cons_of_ne _ _ hf] at h ⊢
      exact ih h

/-- A name absent from the keys of a table has no entry. -/
theorem lookup_eq_none_of_not_mem {t : Table} {f : String} (h : f ∉ t.map Prod.fst) :
    List.lookup f t = none := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨f', g'⟩ := p
    have hf : f ≠ f' := fun e => h (by simp [e])
    rw [lookup_cons_of_ne _ _ hf]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

end Table

/-! ## Strings -/

/-- The encoding of a string: `.unit`. `Value` has no string constructor; a `&str` of an
    extraction is produced only by the opaque calls of the base table and is never read
    by a literal, so the encoding erases it. It is not injective, and a leaf that takes a
    string argument has no `liftFn`. -/
instance : HaxEnc String := ⟨fun _ => .unit⟩

instance : HaxEnc.Plain String := ⟨fun _ => rfl⟩

/-! ## Injective encodings -/

/-- The encoding of `α` is injective. -/
class HaxEnc.Inj (α : Type) [HaxEnc α] : Prop where
  inj : Function.Injective (enc : α → Value)

/-- The component list of a right-nested product is injective. -/
class HaxTupleEnc.Inj (α : Type) [HaxTupleEnc α] : Prop where
  inj : Function.Injective (HaxTupleEnc.encList : α → List Value)

section Inj

variable {α β : Type}

instance : HaxEnc.Inj Int := ⟨fun _ _ h => Value.int.inj h⟩
instance : HaxEnc.Inj Bool := ⟨fun _ _ h => Value.bool.inj h⟩
instance : HaxEnc.Inj Unit := ⟨fun _ _ _ => rfl⟩
instance : HaxEnc.Inj UInt8 := ⟨fun _ _ h => UInt8.toNat_inj.mp (Value.uint.inj h).2⟩
instance : HaxEnc.Inj UInt16 := ⟨fun _ _ h => UInt16.toNat_inj.mp (Value.uint.inj h).2⟩
instance : HaxEnc.Inj UInt32 := ⟨fun _ _ h => UInt32.toNat_inj.mp (Value.uint.inj h).2⟩
instance : HaxEnc.Inj UInt64 := ⟨fun _ _ h => UInt64.toNat_inj.mp (Value.uint.inj h).2⟩
instance : HaxEnc.Inj USize := ⟨fun _ _ h => USize.toNat_inj.mp (Value.uint.inj h).2⟩
instance : HaxEnc.Inj Int8 := ⟨fun _ _ h => Int8.toInt_inj.mp (Value.sint.inj h).2⟩
instance : HaxEnc.Inj Int16 := ⟨fun _ _ h => Int16.toInt_inj.mp (Value.sint.inj h).2⟩
instance : HaxEnc.Inj Int32 := ⟨fun _ _ h => Int32.toInt_inj.mp (Value.sint.inj h).2⟩
instance : HaxEnc.Inj Int64 := ⟨fun _ _ h => Int64.toInt_inj.mp (Value.sint.inj h).2⟩
instance : HaxEnc.Inj ISize := ⟨fun _ _ h => ISize.toInt_inj.mp (Value.sint.inj h).2⟩

instance [HaxEnc α] [HaxEnc.Inj α] : HaxEnc.Inj (Array α) :=
  ⟨fun _ _ h => Array.toList_inj.mp
    ((List.map_inj_right fun _ _ e => HaxEnc.Inj.inj e).mp (Value.array.inj h))⟩

instance [HaxEnc α] [HaxEnc.Inj α] : HaxEnc.Inj (Option α) :=
  ⟨fun _ _ h => Option.map_injective HaxEnc.Inj.inj (Value.option.inj h)⟩

instance (priority := low) HaxTupleEnc.Inj.single [HaxEnc α] [HaxEnc.Inj α] :
    @HaxTupleEnc.Inj α HaxTupleEnc.single :=
  ⟨fun _ _ h => HaxEnc.Inj.inj (List.cons.inj h).1⟩

instance HaxTupleEnc.Inj.prod [HaxEnc α] [HaxEnc.Inj α] [HaxTupleEnc β] [HaxTupleEnc.Inj β] :
    HaxTupleEnc.Inj (α × β) :=
  ⟨fun p q h => by
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact Prod.ext (HaxEnc.Inj.inj h1) (HaxTupleEnc.Inj.inj h2)⟩

instance HaxEnc.Inj.prod [HaxEnc α] [HaxEnc.Inj α] [HaxTupleEnc β] [HaxTupleEnc.Inj β] :
    HaxEnc.Inj (α × β) :=
  ⟨fun _ _ h => HaxTupleEnc.Inj.inj (α := α × β) (Value.tuple.inj h)⟩

end Inj

/-! ## Argument tuples -/

/-- An encoding of an argument tuple as the list of argument values of a call. The tuple
    `α₁ × (α₂ × … × (αₙ × Unit))` encodes as `[enc a₁, …, enc aₙ]`. -/
class HaxArgs (A : Type) where
  /-- The argument values. -/
  encArgs : A → List Value
  /-- The argument encoding is injective. -/
  inj : Function.Injective encArgs

export HaxArgs (encArgs)

instance : HaxArgs Unit := ⟨fun _ => [], fun _ _ _ => rfl⟩

instance HaxArgs.prod {α β : Type} [HaxEnc α] [HaxEnc.Inj α] [HaxArgs β] : HaxArgs (α × β) :=
  ⟨fun p => enc p.1 :: encArgs p.2, fun p q h => by
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact Prod.ext (HaxEnc.Inj.inj h1) (HaxArgs.inj h2)⟩

@[simp] theorem encArgs_unit (u : Unit) : encArgs u = [] := rfl

@[simp] theorem encArgs_prod {α β : Type} [HaxEnc α] [HaxEnc.Inj α] [HaxArgs β]
    (a : α) (b : β) : encArgs (a, b) = enc a :: encArgs b := rfl

/-! ## Leaves of Lean functions -/

/-- The leaf of `g : A → B`: on the encoding of an argument tuple `a` it returns the
    encoding of `g a`, and on a list that encodes no argument tuple it returns `none`. -/
noncomputable def liftFn {A B : Type} [HaxArgs A] [HaxEnc B] (g : A → B) : Leaf := fun vs =>
  open Classical in
  if h : ∃ a : A, encArgs a = vs then some (enc (g h.choose)) else none

/-- **Transport for a function leaf.** The leaf of `g` maps the encoding of `a` to the
    encoding of `g a`. -/
theorem liftFn_encArgs {A B : Type} [HaxArgs A] [HaxEnc B] (g : A → B) (a : A) :
    liftFn g (encArgs a) = some (enc (g a)) := by
  have hex : ∃ a' : A, encArgs a' = encArgs a := ⟨a, rfl⟩
  unfold liftFn
  rw [dif_pos hex, HaxArgs.inj hex.choose_spec]

section Curried

variable {α₁ α₂ α₃ α₄ β : Type} [HaxEnc α₁] [HaxEnc.Inj α₁] [HaxEnc α₂] [HaxEnc.Inj α₂]
  [HaxEnc α₃] [HaxEnc.Inj α₃] [HaxEnc α₄] [HaxEnc.Inj α₄] [HaxEnc β]

/-- The leaf of a constant. -/
noncomputable def leaf0 (c : β) : Leaf := liftFn (A := Unit) fun _ => c

/-- The leaf of a function of one argument. -/
noncomputable def leaf1 (g : α₁ → β) : Leaf := liftFn (A := α₁ × Unit) fun p => g p.1

/-- The leaf of a function of two arguments. -/
noncomputable def leaf2 (g : α₁ → α₂ → β) : Leaf :=
  liftFn (A := α₁ × α₂ × Unit) fun p => g p.1 p.2.1

/-- The leaf of a function of three arguments. -/
noncomputable def leaf3 (g : α₁ → α₂ → α₃ → β) : Leaf :=
  liftFn (A := α₁ × α₂ × α₃ × Unit) fun p => g p.1 p.2.1 p.2.2.1

/-- The leaf of a function of four arguments. -/
noncomputable def leaf4 (g : α₁ → α₂ → α₃ → α₄ → β) : Leaf :=
  liftFn (A := α₁ × α₂ × α₃ × α₄ × Unit) fun p => g p.1 p.2.1 p.2.2.1 p.2.2.2.1

theorem leaf0_apply (c : β) : leaf0 c [] = some (enc c) :=
  liftFn_encArgs (A := Unit) _ ()

theorem leaf1_apply (g : α₁ → β) (a₁ : α₁) : leaf1 g [enc a₁] = some (enc (g a₁)) :=
  liftFn_encArgs (A := α₁ × Unit) _ (a₁, ())

theorem leaf2_apply (g : α₁ → α₂ → β) (a₁ : α₁) (a₂ : α₂) :
    leaf2 g [enc a₁, enc a₂] = some (enc (g a₁ a₂)) :=
  liftFn_encArgs (A := α₁ × α₂ × Unit) _ (a₁, a₂, ())

theorem leaf3_apply (g : α₁ → α₂ → α₃ → β) (a₁ : α₁) (a₂ : α₂) (a₃ : α₃) :
    leaf3 g [enc a₁, enc a₂, enc a₃] = some (enc (g a₁ a₂ a₃)) :=
  liftFn_encArgs (A := α₁ × α₂ × α₃ × Unit) _ (a₁, a₂, a₃, ())

theorem leaf4_apply (g : α₁ → α₂ → α₃ → α₄ → β) (a₁ : α₁) (a₂ : α₂) (a₃ : α₃) (a₄ : α₄) :
    leaf4 g [enc a₁, enc a₂, enc a₃, enc a₄] = some (enc (g a₁ a₂ a₃ a₄)) :=
  liftFn_encArgs (A := α₁ × α₂ × α₃ × α₄ × Unit) _ (a₁, a₂, a₃, a₄, ())

variable {t : Table} {base : Builtins} {f : String}

theorem Table.over_leaf1 {g : α₁ → β} (h : List.lookup f t = some (leaf1 g)) (a₁ : α₁) :
    t.over base f [enc a₁] = some (enc (g a₁)) := by
  rw [Table.over_of_lookup h, leaf1_apply]

theorem Table.over_leaf2 {g : α₁ → α₂ → β} (h : List.lookup f t = some (leaf2 g))
    (a₁ : α₁) (a₂ : α₂) : t.over base f [enc a₁, enc a₂] = some (enc (g a₁ a₂)) := by
  rw [Table.over_of_lookup h, leaf2_apply]

theorem Table.over_leaf3 {g : α₁ → α₂ → α₃ → β} (h : List.lookup f t = some (leaf3 g))
    (a₁ : α₁) (a₂ : α₂) (a₃ : α₃) :
    t.over base f [enc a₁, enc a₂, enc a₃] = some (enc (g a₁ a₂ a₃)) := by
  rw [Table.over_of_lookup h, leaf3_apply]

end Curried

end Hax.Ascent
