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
  roles of their leaves, and a table that covers every name with a struct role. `structHead?`
  classifies a head by equality with the names the layout generates, so a non-canonical
  spelling of a struct name has no struct role and needs no entry in the table.
* `pairSpec` — the specification of the two-field struct of `pairLayout`

## Main results

* `structTab_structsTable` — the struct leaves over `base`, at arity at least `2`, answer every
  call on arguments without a control-flow value as `structBi sf base` does
* `fnCorres_tStructToTuple` — a function correspondence of a struct term under `S` is one of
  its rewrite under `T`, when `StructTab sf S T` and the term never reads the reserved name.
* `structsAgree_pairLayout` — `pairSpec` agrees with `pairLayout`, so `structTab_structsTable`
  applies at the two-field struct `P`.
-/

@[expose] public section

set_option autoImplicit false

namespace HaxAscent.Ascent

open Hax Hax.Ascent StructTuple

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
    have hmem : (f, g) ∈ structsTable structs := by
      obtain ⟨_, _, he, -⟩ := List.lookup_eq_some_iff.mp hl
      rw [he]
      simp
    obtain ⟨s, hs, hm⟩ := List.mem_flatMap.mp hmem
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

/-- The specification of the struct `P` of `pairLayout`: its constructor, the projections
    `P.a`, `.a`, `P.b` and `.b`, and two fields. -/
def pairSpec : StructSpec :=
  { name := "P", arity := 2, projs := [("P.a", 0), (".a", 0), ("P.b", 1), (".b", 1)] }

/-- The specification `pairSpec` agrees with the layout `pairLayout`. -/
theorem structsAgree_pairLayout : StructsAgree pairLayout [pairSpec] := by
  have hu : ∀ i, structUpdateHead "P" i 2 =
      "struct_update#" ++ ("P" ++ ("#" ++ (Nat.repr i ++ ("#" ++ Nat.repr 2)))) := by
    intro i
    unfold structUpdateHead
    simp only [toString, String.append_assoc]
  have r0 : Nat.repr 0 = "0" := by
    rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_zero.2 rfl]
    decide
  have r1 : Nat.repr 1 = "1" := by
    rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.2 rfl]
    decide
  have r2 : Nat.repr 2 = "2" := by
    rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_two.2 rfl]
    decide
  have u0 : structUpdateHead "P" 0 2 = "struct_update#P#0#2" := by
    rw [hu, r0, r2]
    decide
  have u1 : structUpdateHead "P" 1 2 = "struct_update#P#1#2" := by
    rw [hu, r1, r2]
    decide
  refine ⟨?_, fun f hf => ?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    refine ⟨by decide, by decide, fun i hi => ?_⟩
    match i, hi with
    | 0, _ =>
      show structHead? pairLayout (structUpdateHead "P" 0 2) = some (.update 0 2)
      simp [structHead?, structUpdateRole?, pairLayout, List.lookup, List.range,
        List.range.loop, u0]
    | 1, _ =>
      show structHead? pairLayout (structUpdateHead "P" 1 2) = some (.update 1 2)
      simp [structHead?, structUpdateRole?, pairLayout, List.lookup, List.find?, List.range,
        List.range.loop, u0, u1]
  · have hne : ∀ x, ((structsTable [pairSpec]).lookup x).isSome = true →
        (f == x) = false ∧ (x == f) = false := fun x hx => by
      have hfx : f ≠ x := by
        rintro rfl
        simp [hf] at hx
      exact ⟨by simpa using hfx, by simpa using Ne.symm hfx⟩
    have hT : ∀ x, ((structsTable [pairSpec]).lookup x).isSome =
        ((structsTable [pairSpec]).map Prod.fst).contains x := by
      intro x
      simp only [structsTable, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      induction (pairSpec.table) with
      | nil => rfl
      | cons p t ih =>
        simp only [List.lookup, List.map_cons, List.contains_cons]
        cases h : x == p.1 <;> simp_all
    simp [structHead?, structUpdateRole?, structFieldRole?, pairLayout, List.lookup, List.find?,
      List.range, List.range.loop, List.findIdx?, List.findIdx?.go, List.filter, List.any, u0, u1,
      (hne "P" (by decide)).1, (hne "P.a" (by decide)).2, (hne "P.b" (by decide)).2,
      (hne ".a" (by decide)).2, (hne ".b" (by decide)).2,
      (hne "struct_update#P#0#2" (by rw [hT]; simp [structsTable, StructSpec.table, pairSpec,
        List.range, List.range.loop, u0, u1])).2,
      (hne "struct_update#P#1#2" (by rw [hT]; simp [structsTable, StructSpec.table, pairSpec,
        List.range, List.range.loop, u0, u1])).2]

/-- The struct leaves of `pairSpec` over `base` answer every call on arguments without a
    control-flow value as the struct heads of `pairLayout` over `base` do. -/
example (base : Builtins) :
    StructTab pairLayout ((structsTable [pairSpec]).over base) base :=
  structTab_structsTable pairLayout [pairSpec] base structsAgree_pairLayout (by decide)

end HaxAscent.Ascent
