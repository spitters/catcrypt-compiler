/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.RustMSquare
public import CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory

/-!
# The `RustM` correspondence squares as a thin double category

This module places the squares `CorresM P G p V Q` of `Ascent/RustMSquare.lean` in the
thin double category `CategoryTheory.ThinDoubleCategory.ofRelSemantics` of lax squares
over a relational semantics.

## The double category

* Objects: `MLevel C S` has a concrete object `conc A` and an abstract object `abs A` for
  every value type `A`. The carrier of `conc A` is `A × C` (a value and a concrete state),
  that of `abs A` is `A × S` (a value and an abstract state).
* Horizontal category at the concrete level: the Kleisli category of the state-passing
  `RustM` programs. An arrow `conc A ⟶ conc B` is a continuation
  `A → C → RustM (B × C)`, composed by `kseq` with `pureK` as identity. `kseq_pure_left`,
  `kseq_pure_right` and `kseq_assoc` are the category laws, strictly, so no normal form is
  needed.
* Horizontal category at the abstract level: state-indexed value maps `S → A → B`,
  composed pointwise in diagram order. A `CorresM` value side `V : S → A` is the map
  `fun σ _ => V σ` out of `abs Unit`.
* Semantics: a continuation `f` relates `(a, c)` to `(b, c')` when `f a c = .ok (b, c')`,
  so `.fail` and `.div` relate to nothing; a value map `W` relates `(a, σ)` to
  `(W σ a, σ)`, leaving the abstract state unchanged as `CorresM` does.
* Vertical category: relations between the carriers (`relCategory`).

`corresM_iff_sq` identifies `CorresM P G p V Q` with the square from `conc Unit` to
`conc A` over `abs Unit` to `abs A` whose left side is `P` under the guard `G` and whose
right side is `Q` together with the equality of the concrete and abstract values.
Horizontal pasting of squares whose left side pins the value is `corresM_bind`.

## Main definitions

* `MLevel`, `MLevel.carrier`, `MLevel.HHom` — objects, carriers, horizontal arrows
* `MLevel.relSemantics` — the relational semantics of both levels
* `MLevel.sq_conc_iff`, `MLevel.corresM_iff_sq` — the squares at the concrete-over-abstract
  boundary
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.RustM

open CategoryTheory ThinDoubleCategory

/-- The objects of the `RustM` double category over the concrete state `C` and the abstract
state `S`: a concrete and an abstract object for every value type. -/
inductive MLevel (C S : Type) : Type 1 where
  /-- The concrete object at value type `A`, with carrier `A × C`. -/
  | conc (A : Type)
  /-- The abstract object at value type `A`, with carrier `A × S`. -/
  | abs (A : Type)

namespace MLevel

variable {C S : Type}

/-- The carrier of an object. -/
def carrier : MLevel C S → Type
  | .conc A => A × C
  | .abs A => A × S

/-- Horizontal arrows: state-passing `RustM` continuations at the concrete level,
state-indexed value maps at the abstract level, none between the levels. -/
def HHom : MLevel C S → MLevel C S → Type
  | .conc A, .conc B => A → C → Aeneas.Std.RustM (B × C)
  | .abs A, .abs B => S → A → B
  | _, _ => PEmpty

/-- The horizontal identity: `pureK`, the identity value map. -/
def hid : (a : MLevel C S) → HHom a a
  | .conc A => (fun a c => pureK a c : A → C → Aeneas.Std.RustM (A × C))
  | .abs A => (fun _ a => a : S → A → A)

/-- Horizontal composition: Kleisli composition by `kseq`, pointwise diagrammatic
composition of value maps. -/
def hcomp : {a b c : MLevel C S} → HHom a b → HHom b c → HHom a c
  | .conc A, .conc B, .conc D, f, g =>
      (fun a c => kseq ((f : A → C → Aeneas.Std.RustM (B × C)) a)
        (g : B → C → Aeneas.Std.RustM (D × C)) c : A → C → Aeneas.Std.RustM (D × C))
  | .abs A, .abs B, .abs D, f, g =>
      (fun σ a => (g : S → B → D) σ ((f : S → A → B) σ a) : S → A → D)
  | .conc _, .abs _, _, u, _ => PEmpty.elim u
  | .abs _, .conc _, _, u, _ => PEmpty.elim u
  | .conc _, .conc _, .abs _, _, v => PEmpty.elim v
  | .abs _, .abs _, .conc _, _, v => PEmpty.elim v

/-- The horizontal category: the Kleisli category of state-passing `RustM` programs at the
concrete level, state-indexed value maps at the abstract level. -/
instance : Category (Hor (MLevel C S)) where
  Hom := HHom
  id := hid
  comp := hcomp
  id_comp := by
    intro a b f; cases a <;> cases b
    all_goals first | rfl | exact PEmpty.elim f
  comp_id := by
    intro a b f; cases a <;> cases b
    all_goals first | exact PEmpty.elim f | rfl | skip
    funext x c
    exact congrFun (kseq_pure_right _) c
  assoc := by
    intro a b c d f g h
    cases a <;> cases b <;> cases c <;> cases d
    all_goals first
      | exact PEmpty.elim f | exact PEmpty.elim g | exact PEmpty.elim h | rfl | skip
    funext x c
    exact congrFun (kseq_assoc _ _ _) c

/-- The relation a horizontal arrow denotes: the `.ok` graph of a continuation, the graph
of a value map at a fixed abstract state. -/
def sem : {a b : MLevel C S} → HHom a b → carrier a → carrier b → Prop
  | .conc A, .conc B, f => fun x y =>
      (f : A → C → Aeneas.Std.RustM (B × C)) (x : A × C).1 x.2 = .ok (y : B × C)
  | .abs A, .abs B, W => fun x y =>
      (y : B × S) = ((W : S → A → B) (x : A × S).2 x.1, x.2)
  | .conc _, .abs _, u => PEmpty.elim u
  | .abs _, .conc _, u => PEmpty.elim u

/-- The relational semantics of both levels; at the concrete level, functoriality is the
behaviour of `RustM`'s bind on `.ok`, `.fail` and `.div`. -/
def relSemantics : RelSemantics (C := MLevel C S) carrier where
  sem := sem
  sem_id a := by
    cases a
    · funext x y; apply propext
      show Aeneas.Std.RustM.ok (x.1, x.2) = .ok y ↔ x = y
      exact ⟨fun h => by cases h; rfl, fun h => by subst h; rfl⟩
    · funext x y; apply propext
      show y = (x.1, x.2) ↔ x = y
      exact ⟨fun h => h ▸ rfl, fun h => h ▸ rfl⟩
  sem_comp := by
    intro a b c u v
    cases a <;> cases b <;> cases c
    all_goals first | exact PEmpty.elim u | exact PEmpty.elim v | skip
    · funext x z; apply propext
      show kseq (u x.1) v x.2 = .ok z ↔ ∃ y, u x.1 x.2 = .ok y ∧ v y.1 y.2 = .ok z
      simp only [kseq]
      cases hu : u x.1 x.2 with
      | ok r =>
        simp only [Aeneas.Std.bind_tc_ok]
        exact ⟨fun h => ⟨r, rfl, h⟩, fun ⟨_, h1, h2⟩ => by cases h1; exact h2⟩
      | fail e =>
        exact ⟨fun h => (by cases h), fun ⟨_, h1, _⟩ => (by cases h1)⟩
      | div =>
        exact ⟨fun h => (by cases h), fun ⟨_, h1, _⟩ => (by cases h1)⟩
    · funext x z; apply propext
      show z = (v x.2 (u x.2 x.1), x.2) ↔
        ∃ y, y = (u x.2 x.1, x.2) ∧ z = (v y.2 y.1, y.2)
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, h1, h2⟩ => by subst h1; exact h2⟩

/-- The vertical category: relations between the carriers. -/
instance : Category (MLevel C S) := relCategory carrier

/-- The `RustM` thin double category: lax squares of relations over the `.ok` semantics of
state-passing continuations. -/
instance : ThinDoubleCategory (MLevel C S) := ofRelSemantics relSemantics

/-- The square at the concrete-over-abstract boundary: from a concrete point related to
`(a, σ)` by the left side, the continuation returns `.ok` at a point related to
`(W σ a, σ)` by the right side. -/
theorem sq_conc_iff {A B : Type} (f : A → C → Aeneas.Std.RustM (B × C))
    (R : A × C → A × S → Prop) (R' : B × C → B × S → Prop) (W : S → A → B) :
    Sq (C := MLevel C S) (a := .conc A) (b := .conc B) (c := .abs A) (d := .abs B)
        f R R' W ↔
      ∀ x a σ, R x (a, σ) → ∃ y, f x.1 x.2 = .ok y ∧ R' y (W σ a, σ) := by
  constructor
  · intro h x a σ hR
    exact h x (a, σ) (W σ a, σ) hR rfl
  · intro h x y y' hR hy
    obtain ⟨z, hz, hR'⟩ := h x y.1 y.2 hR
    exact ⟨z, hz, (show y' = (W y.2 y.1, y.2) from hy) ▸ hR'⟩

/-- `CorresM P G p V Q` is the square from `conc Unit` to `conc A` over `abs Unit` to
`abs A` with left side `P` under the guard `G`, right side `Q` with equal values, top the
program `p` and bottom the value map `V`. -/
theorem corresM_iff_sq {A : Type} (P Q : C → S → Prop) (G : S → Prop)
    (p : C → Aeneas.Std.RustM (A × C)) (V : S → A) :
    CorresM P G p V Q ↔
      Sq (C := MLevel C S) (a := .conc Unit) (b := .conc A) (c := .abs Unit) (d := .abs A)
        (fun (_ : Unit) c => p c) (fun x y => P x.2 y.2 ∧ G y.2)
        (fun x y => Q x.2 y.2 ∧ x.1 = y.1) (fun σ _ => V σ) := by
  refine Iff.trans ?_ (sq_conc_iff (C := C) (S := S) (A := Unit) (B := A)
    (fun (_ : Unit) c => p c) _ _ (fun σ _ => V σ)).symm
  constructor
  · intro h x _ σ ⟨hP, hG⟩
    obtain ⟨c', hc, hQ⟩ := h x.2 σ hP hG
    exact ⟨(V σ, c'), hc, hQ, rfl⟩
  · intro h c σ hP hG
    obtain ⟨⟨v, c'⟩, hc, hQ, hv⟩ := h ((), c) () σ ⟨hP, hG⟩
    exact ⟨c', (show v = V σ from hv) ▸ hc, hQ⟩

end MLevel

end Hax.Ascent.RustM
