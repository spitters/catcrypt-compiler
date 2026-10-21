/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.StructTuple
public import HaxAscent.Ascent.Structs
public import HaxAscent.Ascent.TableCongr

/-!
# Function correspondences across the struct-to-tuple rewrite

`tStructToTuple sf t` replaces struct constructions, field reads and field updates by tuple
syntax. `StructTuple.denote'_tStructToTuple_of_structTab` states that the rewrite refines
`denote'` from a table `S` to a table `T` with `StructTuple.StructTab sf S T`. A function
correspondence is a statement about non-error outcomes of `denote'`, so it is carried across
the rewrite.

## Main definitions

* `StructsAgree` — struct specifications whose names have, under a field layout, the struct
  roles of their leaves, and a table that covers every name with a struct role

## Main results

* `structTab_structsTable` — the struct leaves over `base`, at arity at least `2`, answer every
  call on arguments without a control-flow value as `structBi sf base` does
* `fnCorres_tStructToTuple` — a function correspondence of a struct term under `S` is one of
  its rewrite under `T`, when `StructTab sf S T` and the term never reads the reserved name.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open StructTuple

/-! ### The struct leaves as struct heads -/

/-- The struct specifications `structs` agree with the field layout `sf`: each
    constructor, projection and update name of a specification has, under `sf`, the
    struct role of its leaf, and every name without an entry in `structsTable structs` has
    no struct role. -/
def StructsAgree (sf : StructFieldTys) (structs : List StructSpec) : Prop :=
  (∀ s ∈ structs, structHead? sf s.name = some (.ctor s.arity) ∧
    (∀ p ∈ s.projs, structHead? sf p.1 = some (.field p.2 s.arity)) ∧
    ∀ i < s.arity,
      structHead? sf (structUpdateHead s.name i s.arity) = some (.update i s.arity)) ∧
  ∀ f, (structsTable structs).lookup f = none → structHead? sf f = none

/-- An entry found by `List.lookup` is a member of the table. -/
theorem mem_of_lookup_eq_some {t : Table} {f : String} {g : Leaf}
    (h : t.lookup f = some g) : (f, g) ∈ t := by
  induction t with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨f', g'⟩ := p
    by_cases hf : f = f'
    · subst hf
      rw [Table.lookup_cons_self] at h
      cases h
      exact List.mem_cons_self
    · rw [Table.lookup_cons_of_ne _ _ hf] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- The leaves of struct specifications of arity at least `2` that agree with the field
    layout `sf` answer every call on arguments without a control-flow value as the struct
    heads of `sf` over `base` do. -/
theorem structTab_structsTable (sf : StructFieldTys) (structs : List StructSpec)
    (base : Builtins) (hagree : StructsAgree sf structs)
    (h2 : ∀ s ∈ structs, 2 ≤ s.arity) :
    StructTab sf ((structsTable structs).over base) base := by
  intro f vals v hc h
  cases hl : (structsTable structs).lookup f with
  | none =>
    rw [Table.over_of_lookup_none hl] at h
    simp [structBi, hagree.2 f hl, h]
  | some g =>
    rw [Table.over_of_lookup hl] at h
    obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp (mem_of_lookup_eq_some hl)
    obtain ⟨hctor, hproj, hupd⟩ := hagree.1 s hs
    have h2s := h2 s hs
    simp only [StructSpec.table, List.cons_append, List.mem_cons, List.mem_append,
      List.mem_map, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨p, hp, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩
    · simp only [structBi, hctor]
      simp only [ctorLeaf, if_neg (show s.arity ≠ 1 by omega)] at h
      exact h
    · simp only [structBi, hproj p hp]
      rcases vals with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · simp [projLeaf] at h
      · simp only [projLeaf, if_neg (show ¬ s.arity ≤ 1 by omega)] at h
        cases x <;> simp_all
      · simp [projLeaf] at h
    · simp only [structBi, hupd i (List.mem_range.mp hi)]
      rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
      · simp [updateLeaf] at h
      · simp [updateLeaf] at h
      · simp only [updateLeaf, if_neg (show ¬ s.arity ≤ 1 by omega)] at h
        cases x <;> simp_all
      · simp [updateLeaf] at h

/-- A function correspondence of the struct term `e` under the table `S` is a function
    correspondence of its rewrite `tStructToTuple sf t e` under `T`, when `S` answers every
    call as the struct heads over `T` do and the erasure of `e` never reads the reserved
    name `t`. -/
theorem fnCorres_tStructToTuple {sf : StructFieldTys} {t : String} {e : TExpr}
    {S T : Builtins} {A β : Type} [HaxEnc β] {entry : A → Env} {G : A → Prop} {f : A → β}
    (hS : StructTab sf S T) (hv : noVarRef t e.erase = true)
    (hf : FnCorres S e.erase entry G f) :
    FnCorres T (tStructToTuple sf t e).erase entry G f := by
  intro a hG
  obtain ⟨fuel₀, hrun⟩ := hf a hG
  refine ⟨fuel₀, fun fuel hle => ?_⟩
  have href := denote'_tStructToTuple_of_structTab sf S T hS t e hv fuel (entry a) (entry a)
    (Env.AgreeExcept.rfl' t (entry a))
  exact (href (by rw [hrun fuel hle]; rfl)).1.trans (hrun fuel hle)

/-- The layout of the two-field struct `P { a : int, b : int }`. -/
def pairLayout : StructFieldTys := [("P", [("a", .int), ("b", .int)])]

/-- The struct construction `P x y`. -/
def pairCtorTerm : TExpr :=
  .mk (.app "P" [.mk (.var "x") .int, .mk (.var "y") .int]) (.adt "P" [])

example (base : Builtins) :
    FnCorres base (tStructToTuple pairLayout "struct#t" pairCtorTerm).erase
      (fun a : Int × Int => bindParams [("x", .int a.1), ("y", .int a.2)]) (fun _ => True)
      id := by
  refine fnCorres_tStructToTuple (StructTab.of_structBi pairLayout base) (by decide) ?_
  intro a _
  refine ⟨0, fun fuel _ => ?_⟩
  have hc : structHead? pairLayout "P" = some (.ctor 2) := by decide
  simp [pairCtorTerm, TExpr.erase, denote', denoteApp', denoteArgs', structBi, hc,
    bindParams, enc]
  rfl

end Hax.Ascent
