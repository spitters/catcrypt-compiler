/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Builtins

/-!
# Leaves for the methods of a dependency class

The printer declares the primitives an extraction calls but does not define as a class
`<X>Deps` with one field per primitive, and the surface calls the field by its bare
name. A `DepMethod` is one such field, described independently of any particular
class: its name in the literal, its argument tuple type with a `HaxArgs` encoding, its
result type with a `HaxEnc` encoding, and the function an instance supplies. A list of
methods, built from a class instance, is the dependency class as a parameter;
`depsTable` is its table of leaves, each the `liftFn` leaf of its method.

The table is keyed by the literal's names. A class field whose name the surface resolves
to a runtime operation is not a method of this table.

## Main definitions

* `DepMethod`, `DepMethod.leaf`, `DepMethod.mk1`, `DepMethod.mk2`, `DepMethod.mk3`
* `depsTable`

## Main results

* `DepMethod.leaf_apply` — the leaf of a method maps the encoded arguments to the
  encoded result
* `DepMethod.mk1_leaf` … `DepMethod.mk3_leaf` — the leaf of a curried method is `leaf1` …
  `leaf3` of the function, whose `corres_app` equations are `leaf1_apply` … `leaf3_apply`
* `depsTable_lookup` — the leaf a table assigns to a method's name
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- A method of a dependency class: its name in the literal, its argument tuple type,
    its result type, and the function the class instance supplies. -/
structure DepMethod where
  /-- The name the literal calls. -/
  name : String
  /-- The argument tuple type. -/
  Args : Type
  /-- The result type. -/
  Ret : Type
  /-- The encoding of the arguments. -/
  [argsEnc : HaxArgs Args]
  /-- The encoding of the result. -/
  [retEnc : HaxEnc Ret]
  /-- The method. -/
  fn : Args → Ret

attribute [instance] DepMethod.argsEnc DepMethod.retEnc

namespace DepMethod

/-- The leaf of a method. -/
noncomputable def leaf (m : DepMethod) : Leaf := liftFn m.fn

/-- **Transport for a method.** -/
theorem leaf_apply (m : DepMethod) (a : m.Args) : m.leaf (encArgs a) = some (enc (m.fn a)) :=
  liftFn_encArgs _ _

variable {α₁ α₂ α₃ β : Type} [HaxEnc α₁] [HaxEnc.Inj α₁] [HaxEnc α₂] [HaxEnc.Inj α₂]
  [HaxEnc α₃] [HaxEnc.Inj α₃] [HaxEnc β]

/-- A method of one argument. -/
def mk1 (name : String) (g : α₁ → β) : DepMethod := ⟨name, α₁ × Unit, β, fun p => g p.1⟩

/-- A method of two arguments. -/
def mk2 (name : String) (g : α₁ → α₂ → β) : DepMethod :=
  ⟨name, α₁ × α₂ × Unit, β, fun p => g p.1 p.2.1⟩

/-- A method of three arguments. -/
def mk3 (name : String) (g : α₁ → α₂ → α₃ → β) : DepMethod :=
  ⟨name, α₁ × α₂ × α₃ × Unit, β, fun p => g p.1 p.2.1 p.2.2.1⟩

theorem mk1_leaf (name : String) (g : α₁ → β) : (mk1 name g).leaf = leaf1 g := rfl

theorem mk2_leaf (name : String) (g : α₁ → α₂ → β) : (mk2 name g).leaf = leaf2 g := rfl

theorem mk3_leaf (name : String) (g : α₁ → α₂ → α₃ → β) : (mk3 name g).leaf = leaf3 g := rfl

end DepMethod

/-- The leaves of the methods of a dependency class. -/
noncomputable def depsTable (ms : List DepMethod) : Table := ms.map fun m => (m.name, m.leaf)

/-- A method not preceded by a method of the same name is interpreted by its leaf. -/
theorem depsTable_lookup {pre post : List DepMethod} {m : DepMethod}
    (h : m.name ∉ pre.map DepMethod.name) :
    List.lookup m.name (depsTable (pre ++ m :: post)) = some m.leaf := by
  simp only [depsTable, List.map_append, List.map_cons]
  rw [Table.lookup_append_of_none (Table.lookup_eq_none_of_not_mem (by simpa using h)),
    Table.lookup_cons_self]

end Hax.Ascent
