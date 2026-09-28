/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresHoare
public import CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory

/-!
# The machine-side squares as a thin double category

This module places the machine-side correspondence squares of `Ascent/SquareStrict.lean`
in the thin double category `CategoryTheory.ThinDoubleCategory.ofRelSemantics` of lax
squares over a relational semantics.

## The double category

* Objects: `JLevel A` has two objects, the machine level `mach` with carrier `JState 64`
  and the abstract level `abs` with carrier `A`.
* Horizontal category: an arrow `mach ⟶ mach` is a block `List (JInstr 64)`, composed by
  `++` with the empty block as identity; an arrow `abs ⟶ abs` is an abstract step `A → A`,
  composed in diagram order (`u ≫ v = v ∘ u`); there are no horizontal arrows between the
  two levels. Both composites are strictly associative and unital, so no normal form is
  needed.
* Semantics: a block denotes the graph of `runBlock`, an abstract step its graph.
  `runBlock_append` is the functoriality of this semantics.
* Vertical category: relations between the carriers (`relCategory`). A vertical arrow
  `mach ⟶ abs` is a state relation `JState 64 → A → Prop`.
* Squares: with top a block `c`, bottom a step `fa`, left `R` and right `R'`, a square is
  `∀ st a, R st a → R' (runBlock st c) (fa a)` (`sq_mach_iff`).

`CorresJ SR P fa c` is the square with left side `SR` restricted to `P` and right side `SR`
(`corresJ_iff_sq`); `RunBlockTriple P c Q` is the square over `A = Unit` with bottom the
identity step (`runBlockTriple_iff_sq`). Horizontal pasting of these squares is
`RunBlockTriple.seq`/`corresJ_hcomp`; vertical pasting composes the state relations.

## Main definitions

* `JLevel`, `JLevel.carrier`, `JLevel.HHom` — objects, carriers and horizontal arrows
* `JLevel.relSemantics` — the semantics of blocks and steps as relations
* `JLevel.sq_mach_iff`, `JLevel.corresJ_iff_sq`, `JLevel.runBlockTriple_iff_sq` — the squares
  at the machine-over-abstract boundary are the workspace judgments
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CategoryTheory ThinDoubleCategory
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The two levels of the machine-side double category over the abstract state type `A`. -/
inductive JLevel (A : Type) where
  /-- The machine level, with carrier `JState 64`. -/
  | mach
  /-- The abstract level, with carrier `A`. -/
  | abs

namespace JLevel

variable {A : Type}

/-- The carrier of a level. -/
def carrier : JLevel A → Type
  | .mach => JState 64
  | .abs => A

/-- Horizontal arrows: blocks at the machine level, abstract steps at the abstract level,
none between the levels. -/
def HHom : JLevel A → JLevel A → Type
  | .mach, .mach => List (JInstr 64)
  | .abs, .abs => A → A
  | _, _ => PEmpty

/-- The horizontal identity: the empty block, the identity step. -/
def hid : (a : JLevel A) → HHom a a
  | .mach => ([] : List (JInstr 64))
  | .abs => (id : A → A)

/-- Horizontal composition: concatenation of blocks, diagrammatic composition of steps. -/
def hcomp : {a b c : JLevel A} → HHom a b → HHom b c → HHom a c
  | .mach, .mach, .mach, l₁, l₂ => List.append (α := JInstr 64) l₁ l₂
  | .abs, .abs, .abs, f, g => Function.comp (α := A) (β := A) (δ := A) g f
  | .mach, .abs, _, u, _ => PEmpty.elim u
  | .abs, .mach, _, u, _ => PEmpty.elim u
  | .mach, .mach, .abs, _, v => PEmpty.elim v
  | .abs, .abs, .mach, _, v => PEmpty.elim v

/-- The horizontal category of blocks and abstract steps. -/
instance : Category (Hor (JLevel A)) where
  Hom := HHom
  id := hid
  comp := hcomp
  id_comp := by
    intro a b f; cases a <;> cases b
    all_goals first | rfl | exact PEmpty.elim f
  comp_id := by
    intro a b f; cases a <;> cases b
    all_goals first | exact List.append_nil (α := JInstr 64) _ | rfl | exact PEmpty.elim f
  assoc := by
    intro a b c d f g h
    cases a <;> cases b <;> cases c <;> cases d
    all_goals first
      | exact List.append_assoc (α := JInstr 64) _ _ _ | rfl
      | exact PEmpty.elim f | exact PEmpty.elim g | exact PEmpty.elim h

/-- The relation a horizontal arrow denotes: the graph of `runBlock` for a block, the graph
of the step for an abstract step. -/
def sem : {a b : JLevel A} → HHom a b → carrier a → carrier b → Prop
  | .mach, .mach, l => fun st st' => runBlock (st : JState 64) l = st'
  | .abs, .abs, f => fun x y => (f : A → A) x = y
  | .mach, .abs, u => PEmpty.elim u
  | .abs, .mach, u => PEmpty.elim u

/-- The semantics of blocks and steps is functorial; for blocks this is
`runBlock_append`. -/
def relSemantics : RelSemantics (C := JLevel A) carrier where
  sem := sem
  sem_id a := by cases a <;> rfl
  sem_comp := by
    intro a b c u v
    cases a <;> cases b <;> cases c
    all_goals first | exact PEmpty.elim u | exact PEmpty.elim v | skip
    · funext x z; apply propext
      have happ : runBlock x (List.append (α := JInstr 64) u v) = runBlock (runBlock x u) v :=
        runBlock_append x u v
      show runBlock x (List.append (α := JInstr 64) u v) = z ↔
        ∃ y, runBlock x u = y ∧ runBlock y v = z
      rw [happ]
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
    · funext x z; apply propext
      show v (u x) = z ↔ ∃ y, u x = y ∧ v y = z
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩

/-- The vertical category: relations between the carriers of the two levels. -/
instance : Category (JLevel A) := relCategory carrier

/-- The machine-side thin double category: lax squares of relations over the `runBlock`
semantics of blocks. -/
instance : ThinDoubleCategory (JLevel A) := ofRelSemantics relSemantics

/-- A square with a block `c` on top, an abstract step `fa` at the bottom and state
relations `R`, `R'` on the sides is the forward simulation of `fa` by `c`. -/
theorem sq_mach_iff (c : List (JInstr 64)) (R R' : JState 64 → A → Prop) (fa : A → A) :
    Sq (C := JLevel A) (a := .mach) (b := .mach) (c := .abs) (d := .abs) c R R' fa ↔
      ∀ st a, R st a → R' (runBlock st c) (fa a) := by
  constructor
  · intro h st a hR
    obtain ⟨st', hst, hR'⟩ := h st a (fa a) hR rfl
    exact (show runBlock st c = st' from hst) ▸ hR'
  · intro h st a a' hR ha
    exact ⟨runBlock st c, rfl, (show fa a = a' from ha) ▸ h st a hR⟩

/-- `CorresJ SR P fa c` is the square with left side `SR` restricted to `P`, right side
`SR`, top `c` and bottom `fa`. -/
theorem corresJ_iff_sq (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔
      Sq (C := JLevel A) (a := .mach) (b := .mach) (c := .abs) (d := .abs) c
        (fun st a => SR st a ∧ P a) SR fa := by
  rw [sq_mach_iff]
  exact ⟨fun h st a hR => h st a hR.1 hR.2, fun h st a hSR hP => h st a ⟨hSR, hP⟩⟩

/-- `RunBlockTriple P c Q` is the square over the one-point abstract state with the
identity step at the bottom and the predicates `P`, `Q` as the sides. -/
theorem runBlockTriple_iff_sq (P Q : JState 64 → Prop) (c : List (JInstr 64)) :
    RunBlockTriple P c Q ↔
      Sq (C := JLevel Unit) (a := .mach) (b := .mach) (c := .abs) (d := .abs) c
        (fun st _ => P st) (fun st _ => Q st) id := by
  refine Iff.trans ?_ (sq_mach_iff (A := Unit) c _ _ id).symm
  exact ⟨fun h st _ hP => h st hP, fun h st hP => h st () hP⟩

end JLevel

end CatCrypt.Crypto.SecureCompilation.Ascent
