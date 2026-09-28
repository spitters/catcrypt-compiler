/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.SquareKleisli
public import CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory

/-!
# The correspondence squares as a thin double category

This module places the source-level correspondence squares `Corres bi P G e V Q` of
`Ascent/Square.lean` in the thin double category
`CategoryTheory.ThinDoubleCategory.ofRelSemantics` of lax squares over a relational
semantics.

## The double category

* Objects: `CLevel bi S` has two objects, the concrete level `conc` with carrier
  `Env × Value` (an environment and the last value produced) and the abstract level `abs`
  with carrier `S × Value`.
* Horizontal category at the concrete level: the free-monoid presentation of `.seq`. An
  arrow is a list of legs `List ImpExpr`, composed by `++` with `[]` as identity. `.seq` on
  `ImpExpr` is associative and unital only up to the equality of runs
  (`SquareKleisli.lean`: `denote'_seq_assoc`, no right unit under `corres_seq`), so the
  expressions themselves do not form a category; their normal forms `seqFlatten e` do, and
  `seqOfList` reads a normal form back as a right-nested program.
* Horizontal category at the abstract level: value transformers `S → Value → Value`
  indexed by the abstract state, composed pointwise in diagram order. A `Corres` bottom side
  `V : S → Value` is the transformer `fun σ _ => V σ`.
* Semantics: a leg `e` denotes the relation `leafSem bi e` — from `(env, _)` the run of `e`
  eventually (for all large fuel) returns a plain value `v` in environment `env'`, relating
  it to `(env', v)`. A list of legs denotes the relational composite of its legs
  (`blockSem`), so functoriality holds by construction (`blockSem_append`). An abstract
  transformer `W` relates `(σ, v)` to `(σ, W σ v)`: the abstract state is unchanged, as in
  `Corres`.
* Vertical category: relations between the carriers (`relCategory`).
* Squares: lax squares; `sq_conc_iff` unfolds the square at the concrete-over-abstract
  boundary.

## Relation to `Corres`

`Corres` admits control-flow values (early exit); the leg semantics admits only plain
values, since `.seq` propagates a control-flow value without running its second leg and
so is not the relational composite there. The squares of this double category are
therefore the plain-valued correspondences: `sq_single_of_corres` builds the square of a
one-leg list from a `Corres` square whose value is plain under the guard, and
`corres_of_sq_single` reads a `Corres` square back. For a list of legs,
`corres_seqOfList_of_sq` gives the `Corres` square of its right-nested program, which
by `corres_of_seqFlatten_eq` is the square of every expression with that normal form.
The guard `G` of a `Corres` square is carried by the left vertical side.

## Main definitions

* `CLevel`, `CLevel.carrier`, `CLevel.HHom` — objects, carriers, horizontal arrows
* `CLevel.leafSem`, `CLevel.blockSem`, `CLevel.blockSem_append` — the leg semantics
* `CLevel.relSemantics` — the relational semantics of both levels
* `CLevel.sq_conc_iff` — the square at the concrete-over-abstract boundary
* `CLevel.sq_single_of_corres`, `CLevel.corres_of_sq_single`,
  `CLevel.corres_seqOfList_of_sq` — the link to `Corres`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open CategoryTheory ThinDoubleCategory

/-- The two levels of the source-level double category for builtins `bi` over the abstract
state type `S`. -/
inductive CLevel (bi : Builtins) (S : Type) where
  /-- The concrete level, with carrier `Env × Value`. -/
  | conc
  /-- The abstract level, with carrier `S × Value`. -/
  | abs

namespace CLevel

variable {bi : Builtins} {S : Type}

/-- The carrier of a level. -/
def carrier : CLevel bi S → Type
  | .conc => Env × Value
  | .abs => S × Value

/-- Horizontal arrows: lists of legs at the concrete level, state-indexed value
transformers at the abstract level, none between the levels. -/
def HHom : CLevel bi S → CLevel bi S → Type
  | .conc, .conc => List ImpExpr
  | .abs, .abs => S → Value → Value
  | _, _ => PEmpty

/-- The horizontal identity: the empty list of legs, the identity transformer. -/
def hid : (a : CLevel bi S) → HHom a a
  | .conc => ([] : List ImpExpr)
  | .abs => (fun _ v => v : S → Value → Value)

/-- Horizontal composition: concatenation of legs, pointwise diagrammatic composition of
transformers. -/
def hcomp : {a b c : CLevel bi S} → HHom a b → HHom b c → HHom a c
  | .conc, .conc, .conc, l₁, l₂ => List.append (α := ImpExpr) l₁ l₂
  | .abs, .abs, .abs, f, g =>
      (fun σ v => (g : S → Value → Value) σ ((f : S → Value → Value) σ v) :
        S → Value → Value)
  | .conc, .abs, _, u, _ => PEmpty.elim u
  | .abs, .conc, _, u, _ => PEmpty.elim u
  | .conc, .conc, .abs, _, v => PEmpty.elim v
  | .abs, .abs, .conc, _, v => PEmpty.elim v

/-- The horizontal category: the free monoid on legs at the concrete level, value
transformers at the abstract level. -/
instance : Category (Hor (CLevel bi S)) where
  Hom := HHom
  id := hid
  comp := hcomp
  id_comp := by
    intro a b f; cases a <;> cases b
    all_goals first | rfl | exact PEmpty.elim f
  comp_id := by
    intro a b f; cases a <;> cases b
    all_goals first | exact List.append_nil (α := ImpExpr) _ | rfl | exact PEmpty.elim f
  assoc := by
    intro a b c d f g h
    cases a <;> cases b <;> cases c <;> cases d
    all_goals first
      | exact List.append_assoc (α := ImpExpr) _ _ _ | rfl
      | exact PEmpty.elim f | exact PEmpty.elim g | exact PEmpty.elim h

variable (bi) in
/-- The relation a single leg denotes: from `(env, _)`, for all large fuel the run of `e`
returns the plain value `v` in the environment `env'`. -/
def leafSem (e : ImpExpr) (x y : Env × Value) : Prop :=
  y.2.isControlFlow = false ∧
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → denote' bi fuel e x.1 = (.val y.2, y.1)

variable (bi) in
/-- The relation a list of legs denotes: the relational composite of its legs. -/
def blockSem : List ImpExpr → Env × Value → Env × Value → Prop
  | [] => (· = ·)
  | e :: es => Relation.Comp (leafSem bi e) (blockSem es)

/-- The leg semantics takes concatenation to relational composition. -/
theorem blockSem_append (l₁ l₂ : List ImpExpr) :
    blockSem bi (l₁ ++ l₂) = Relation.Comp (blockSem bi l₁) (blockSem bi l₂) := by
  induction l₁ with
  | nil =>
    funext x z; apply propext
    exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
  | cons e es ih =>
    funext x z; apply propext
    simp only [List.cons_append, blockSem, ih]
    exact ⟨fun ⟨m, h1, n, h2, h3⟩ => ⟨n, ⟨m, h1, h2⟩, h3⟩,
      fun ⟨n, ⟨m, h1, h2⟩, h3⟩ => ⟨m, h1, n, h2, h3⟩⟩

/-- The relation a horizontal arrow denotes. -/
def sem : {a b : CLevel bi S} → HHom a b → carrier a → carrier b → Prop
  | .conc, .conc, l => blockSem bi l
  | .abs, .abs, W => fun x y => y = (x.1, (W : S → Value → Value) x.1 x.2)
  | .conc, .abs, u => PEmpty.elim u
  | .abs, .conc, u => PEmpty.elim u

/-- The relational semantics of both levels; functoriality at the concrete level is
`blockSem_append`. -/
def relSemantics : RelSemantics (C := CLevel bi S) carrier where
  sem := sem
  sem_id a := by
    cases a
    · rfl
    · funext x y; apply propext
      exact ⟨fun h => h.symm, fun h => h.symm⟩
  sem_comp := by
    intro a b c u v
    cases a <;> cases b <;> cases c
    all_goals first | exact PEmpty.elim u | exact PEmpty.elim v | skip
    · exact blockSem_append (bi := bi) u v
    · funext x z; apply propext
      show z = (x.1, v x.1 (u x.1 x.2)) ↔
        ∃ y, y = (x.1, u x.1 x.2) ∧ z = (y.1, v y.1 y.2)
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, h1, h2⟩ => by subst h1; exact h2⟩

/-- The vertical category: relations between the carriers of the two levels. -/
instance : Category (CLevel bi S) := relCategory carrier

/-- The source-level thin double category: lax squares of relations over the leg
semantics. -/
instance : ThinDoubleCategory (CLevel bi S) := ofRelSemantics relSemantics

/-- The square at the concrete-over-abstract boundary: from a concrete point related to
`(σ, v)` by the left side, the legs run to a concrete point related to `(σ, W σ v)` by the
right side. -/
theorem sq_conc_iff (l : List ImpExpr) (R R' : Env × Value → S × Value → Prop)
    (W : S → Value → Value) :
    Sq (C := CLevel bi S) (a := .conc) (b := .conc) (c := .abs) (d := .abs) l R R' W ↔
      ∀ x σ v, R x (σ, v) → ∃ x', blockSem bi l x x' ∧ R' x' (σ, W σ v) := by
  constructor
  · intro h x σ v hR
    exact h x (σ, v) (σ, W σ v) hR rfl
  · intro h x y y' hR hy
    obtain ⟨x', hl, hR'⟩ := h x y.1 y.2 hR
    exact ⟨x', hl, (show y' = (y.1, W y.1 y.2) from hy) ▸ hR'⟩

/-- The left side induced by an entry relation `P` and a guard `G`. -/
def entryRel (P : Env → S → Prop) (G : S → Prop) (x : Env × Value) (y : S × Value) : Prop :=
  P x.1 y.1 ∧ G y.1

/-- The right side induced by an exit relation `Q`: the concrete and abstract values
agree. -/
def exitRel (Q : Env → S → Prop) (x : Env × Value) (y : S × Value) : Prop :=
  Q x.1 y.1 ∧ x.2 = y.2

/-- A `Corres` square whose value is plain under the guard is a square of the double
category over the one-leg list `[e]`. -/
theorem sq_single_of_corres {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Sq (C := CLevel bi S) (a := .conc) (b := .conc) (c := .abs) (d := .abs) [e]
      (entryRel P G) (exitRel Q) (fun σ _ => V σ) := by
  rw [sq_conc_iff]
  intro x σ _ ⟨hP, hG⟩
  obtain ⟨f₀, env', hQ, hrun⟩ := h x.1 σ hP hG
  exact ⟨(env', V σ), ⟨(env', V σ), ⟨hplain σ hG, f₀, hrun⟩, rfl⟩, hQ, rfl⟩

/-- The run of a nonempty list of legs is the eventual run of its right-nested program. -/
theorem denote'_seqOfList_of_blockSem :
    ∀ (l : List ImpExpr), l ≠ [] → ∀ {x y : Env × Value}, blockSem bi l x y →
      ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → denote' bi fuel (seqOfList l) x.1 = (.val y.2, y.1)
  | [], hne, _, _, _ => absurd rfl hne
  | [e], _, x, y, h => by
    obtain ⟨m, ⟨_, f₀, hrun⟩, hm⟩ := h
    subst hm
    exact ⟨f₀, hrun⟩
  | e :: e' :: es, _, x, y, h => by
    obtain ⟨m, ⟨hplain, f₁, hrun₁⟩, hrest⟩ := h
    obtain ⟨f₂, hrun₂⟩ := denote'_seqOfList_of_blockSem (e' :: es) (List.cons_ne_nil _ _) hrest
    refine ⟨max f₁ f₂, fun fuel hf => ?_⟩
    rw [seqOfList_cons e (List.cons_ne_nil e' es),
      denote'_seq bi fuel (hrun₁ fuel (by omega)) hplain]
    exact hrun₂ fuel (by omega)

/-- A square over a nonempty list of legs gives the `Corres` square of its right-nested
program. -/
theorem corres_seqOfList_of_sq {P Q : Env → S → Prop} {G : S → Prop} {l : List ImpExpr}
    {V : S → Value} (hne : l ≠ [])
    (h : Sq (C := CLevel bi S) (a := .conc) (b := .conc) (c := .abs) (d := .abs) l
      (entryRel P G) (exitRel Q) (fun σ _ => V σ)) :
    Corres bi P G (seqOfList l) V Q := by
  rw [sq_conc_iff] at h
  intro env σ hP hG
  obtain ⟨x', hl, hQ, hv⟩ := h (env, .unit) σ .unit ⟨hP, hG⟩
  obtain ⟨f₀, hrun⟩ := denote'_seqOfList_of_blockSem l hne hl
  refine ⟨f₀, x'.1, hQ, fun fuel hf => ?_⟩
  rw [hrun fuel hf, show x'.2 = V σ from hv]

/-- A square over the one-leg list `[e]` gives the `Corres` square of `e`. -/
theorem corres_of_sq_single {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value}
    (h : Sq (C := CLevel bi S) (a := .conc) (b := .conc) (c := .abs) (d := .abs) [e]
      (entryRel P G) (exitRel Q) (fun σ _ => V σ)) :
    Corres bi P G e V Q :=
  corres_seqOfList_of_sq (List.cons_ne_nil e []) h

end CLevel

end Hax.Ascent
