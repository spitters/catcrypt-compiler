/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Do
public import Batteries.Data.List.Basic

/-!
# The success-restricted Kleisli relation and the pointwise array relation

`RCompOk Rα c c'` relates a computation `c : M α` in a monad whose `Std.Do`
postcondition shape may carry exception components to a computation `c' : N α'` in a
monad of shape `.pure`: every postcondition that `c'` establishes is established, up to
`Rα`, by every successful execution of `c`. At `N = Id` it states that every successful
result of `c` is `Rα`-related to `c'.run` (`RCompOk.id_iff`).

`ArrayRel R a b` is the pointwise relation on arrays, `List.Forall₂ R` on the underlying
lists; `ArrayRel.iff_getElem` states it by size and index.

The definitions of `RCompOk` and `ArrayRel` and the statements of `RCompOk.id_iff` and
`ArrayRel.iff_getElem` are those of ParamTransfer
(`Transfer.Integrations.ParamRCompOk`). This module states them over Lean core, `Std`
and the `List.Forall₂` of Batteries, so that the encoding squares of
`CatCrypt.Hax.RustSemantics` import no Mathlib module.

## Main results

* `RCompOk`, `RCompOk.id_iff` — the relation and its form against an `Id` computation
* `ArrayRel`, `ArrayRel.iff_getElem` — the pointwise array relation by size and index
* `forall₂_iff_getElem`, `forall₂_length_eq`, `forall₂_append`, `forall₂_take` —
  `List.Forall₂` by length and index, its lengths, under append and under `take`
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

namespace CatCrypt.Hax.RustSemantics

open Std.Do

/-- The success-restricted Kleisli lift of a value relation. `RCompOk Rα c c'`
    holds when every postcondition `Q'` that the total computation `c'`
    establishes is established, up to `Rα`, by every successful execution of
    `c`: each value `a` that `c` returns without an exception has a partner
    `a'` with `Rα a a'` and `Q' a'`. The monad `N` has postcondition shape
    `.pure`, so `wp⟦c'⟧ (⇓ a' => ⌜Q' a'⌝)` states that every result of `c'`
    satisfies `Q'`. -/
def RCompOk {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {N : Type u → Type w} [WP N .pure]
    {α α' : Type u} (Rα : α → α' → Prop) (c : M α) (c' : N α') : Prop :=
  ∀ Q' : α' → Prop, (⊢ₛ wp⟦c'⟧ (⇓ a' => ⌜Q' a'⌝)) →
    ⊢ₛ wp⟦c⟧ (⇓? a => ⌜∃ a', Rα a a' ∧ Q' a'⌝)

/-- At `N = Id`, `RCompOk R c c'` states that every successful result of `c` is
    `R`-related to `c'.run`. -/
theorem RCompOk.id_iff {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {α α' : Type u} {R : α → α' → Prop} {c : M α} {c' : Id α'} :
    RCompOk R c c' ↔ ⊢ₛ wp⟦c⟧ (⇓? a => ⌜R a c'.run⌝) := by
  constructor
  · intro h
    refine (h (· = c'.run) ?_).trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
    · exact SPred.pure_intro rfl
    · exact SPred.pure_elim' fun ⟨a', hr, hq⟩ => SPred.pure_intro (hq ▸ hr)
  · intro h Q' hQ
    have hq : Q' c'.run := hQ True.intro
    refine h.trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
    exact SPred.pure_elim' fun hr => SPred.pure_intro ⟨_, hr, hq⟩

section Forall₂

variable {α : Type x} {β : Type y} {R : α → β → Prop}

/-- The empty list is not `Forall₂`-related to a nonempty list. -/
theorem forall₂_nil_cons_iff {b : β} {l : List β} :
    List.Forall₂ R [] (b :: l) ↔ False :=
  ⟨fun h => (nomatch h), False.elim⟩

/-- A nonempty list is not `Forall₂`-related to the empty list. -/
theorem forall₂_cons_nil_iff {a : α} {l : List α} :
    List.Forall₂ R (a :: l) [] ↔ False :=
  ⟨fun h => (nomatch h), False.elim⟩

/-- `List.Forall₂` by length and index. -/
theorem forall₂_iff_getElem {l₁ : List α} {l₂ : List β} :
    List.Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧
      ∀ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i] := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact ⟨fun _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ => .nil⟩
    | cons b l₂ => simp [forall₂_nil_cons_iff]
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp [forall₂_cons_nil_iff]
    | cons b l₂ =>
      rw [List.forall₂_cons, ih]
      constructor
      · rintro ⟨hab, hlen, h⟩
        refine ⟨by simp [hlen], fun i h₁ h₂ => ?_⟩
        cases i with
        | zero => exact hab
        | succ i => exact h i (by simpa using h₁) (by simpa using h₂)
      · rintro ⟨hlen, h⟩
        refine ⟨h 0 (by simp) (by simp), by simpa using hlen, fun i h₁ h₂ => ?_⟩
        exact h (i + 1) (by simpa using h₁) (by simpa using h₂)

/-- `List.Forall₂`-related lists have equal length. -/
theorem forall₂_length_eq {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length :=
  (forall₂_iff_getElem.mp h).1

/-- `List.Forall₂` is preserved by appending related lists. -/
theorem forall₂_append {l₁ m₁ : List α} {l₂ m₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (h' : List.Forall₂ R m₁ m₂) :
    List.Forall₂ R (l₁ ++ m₁) (l₂ ++ m₂) := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

/-- `List.Forall₂` is preserved by taking the same number of entries. -/
theorem forall₂_take (n : Nat) {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    List.Forall₂ R (l₁.take n) (l₂.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons hab _ ih =>
    cases n with
    | zero => simp
    | succ n => exact .cons hab (ih n)

end Forall₂

section ArrayRel

variable {α : Type x} {β : Type y}

/-- The pointwise relation on arrays: `a` and `b` have the same size and
    corresponding entries are `R`-related, stated as `List.Forall₂ R` on the
    underlying lists. -/
def ArrayRel (R : α → β → Prop) (a : Array α) (b : Array β) : Prop :=
  List.Forall₂ R a.toList b.toList

/-- `ArrayRel` by size and index. -/
theorem ArrayRel.iff_getElem {R : α → β → Prop} {a : Array α} {b : Array β} :
    ArrayRel R a b ↔
      a.size = b.size ∧ ∀ (i : Nat) (h : i < a.size) (h' : i < b.size), R a[i] b[i] := by
  simp [ArrayRel, forall₂_iff_getElem]

end ArrayRel

end CatCrypt.Hax.RustSemantics
