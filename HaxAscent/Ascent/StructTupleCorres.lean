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

## Main results

* `fnCorres_tStructToTuple` — a function correspondence of a struct term under `S` is one of
  its rewrite under `T`, when `StructTab sf S T` and the term never reads the reserved name.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open StructTuple

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
