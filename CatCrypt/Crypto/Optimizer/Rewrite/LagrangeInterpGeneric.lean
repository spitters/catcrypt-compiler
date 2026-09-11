/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange interpolation over a generic field

Toom-style multiplication and the NTT both reconstruct a polynomial of degree
`< n` from its values at `n` distinct evaluation points.  This file packages
Mathlib's `Lagrange` interpolation API into the exact "interpolation
correctness" statements those rewrite passes depend on, over a generic
`[Field F]`:

* `interpolate_eval_at_node` — the round-trip: interpolating a value table
  `r` through nodes `v` and then evaluating at a node `v i` returns `r i`.
* `interpolate_recovers` — a polynomial of `degree < n` is recovered exactly
  by interpolating its own values at `n` distinct points (the foundation of
  evaluation/interpolation algorithms).
* `interpolate_unique` — uniqueness: any polynomial of `degree < n` matching
  the value table on all nodes *is* the interpolant.
* `eq_of_eval_eq_on_nodes` — the consequence used to justify Toom/NTT splits:
  two polynomials of `degree < n` that agree at `n` distinct points are equal.

These are thin re-statements of `Lagrange.eval_interpolate_at_node`,
`Lagrange.interpolate_poly_eq_self`, `Lagrange.eq_interpolate_of_eval_eq`, and
`Polynomial.eq_of_degrees_lt_of_eval_finset_eq`.

A worked `Fin 3` example (interpolation through three points is a polynomial of
degree `< 3`, i.e. at most a quadratic) closes the file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Optimizer.Rewrite.LagrangeInterpGeneric

open Polynomial

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F}

/-- **Round-trip at a node.**  Build the interpolating polynomial through the
nodes `v` carrying the value table `r`, evaluate it at a node `v i` with
`i ∈ s`, and recover `r i`.  Requires the nodes to be distinct (`Set.InjOn`).
This is the per-point correctness Toom/NTT interpolation relies on. -/
theorem interpolate_eval_at_node (r : ι → F) (hvs : Set.InjOn v s)
    {i : ι} (hi : i ∈ s) :
    eval (v i) ((Lagrange.interpolate s v) r) = r i :=
  Lagrange.eval_interpolate_at_node r hvs hi

/-- **Reconstruction.**  A polynomial `P` of `degree < s.card` is recovered
exactly by interpolating its own values `eval (v i) P` through the distinct
nodes `v`.  This is the evaluate-then-interpolate identity at the heart of
Toom-3 and the NTT. -/
theorem interpolate_recovers (hvs : Set.InjOn v s) {P : F[X]}
    (hP : P.degree < s.card) :
    ((Lagrange.interpolate s v) fun i => eval (v i) P) = P :=
  (Lagrange.eq_interpolate hvs hP).symm

/-- **Uniqueness (interpolant form).**  Any polynomial `f` of
`degree < s.card` whose values on the distinct nodes match the table `r` is the
Lagrange interpolant of `r`. -/
theorem interpolate_unique (r : ι → F) (hvs : Set.InjOn v s)
    {f : F[X]} (degree_f_lt : f.degree < s.card)
    (eval_f : ∀ i ∈ s, eval (v i) f = r i) :
    f = (Lagrange.interpolate s v) r :=
  Lagrange.eq_interpolate_of_eval_eq r hvs degree_f_lt eval_f

/-- **Characteristic property.**  `f` of `degree < s.card` agreeing with the
table `r` on every node iff `f` is the interpolant — Mathlib's
`Lagrange.eq_interpolate_iff` re-exported. -/
theorem interpolate_iff (r : ι → F) (hvs : Set.InjOn v s) {f : F[X]} :
    (f.degree < s.card ∧ ∀ i ∈ s, eval (v i) f = r i) ↔
      f = (Lagrange.interpolate s v) r :=
  Lagrange.eq_interpolate_iff r hvs

/-- **Uniqueness (consequence used by the passes).**  Two polynomials of
`degree < t.card` that agree at the `t.card` distinct evaluation points
`t : Finset F` are equal.  This justifies recombining Toom/NTT sub-products:
matching the product at enough points pins it down.  The points are field
elements (the elements of `t` themselves), so no injectivity hypothesis is
needed. -/
theorem eq_of_eval_eq_on_nodes (t : Finset F) {f g : F[X]}
    (degree_f_lt : f.degree < t.card) (degree_g_lt : g.degree < t.card)
    (eval_fg : ∀ x ∈ t, eval x f = eval x g) :
    f = g :=
  Polynomial.eq_of_degrees_lt_of_eval_finset_eq t degree_f_lt degree_g_lt eval_fg

/-! ### Worked example: interpolation through three points is a quadratic

Over any field, three distinct nodes give a value table whose interpolant has
degree `< 3` — i.e. at most a quadratic.  This is exactly the Toom-3 shape
(five points for a degree-`< 5` product; here we use the smaller three-point
case to keep the example self-contained). -/

section Quadratic

variable [DecidableEq F] {a b c : F}

/-- The three-node finset `{a, b, c}` used by the example. -/
def threeNodes (a b c : F) : Finset F := {a, b, c}

/-- A polynomial interpolated through three distinct points has `degree < 3`:
it is recovered by, and agrees with, any quadratic-or-lower polynomial taking
those values.  Concretely, the interpolant of a value table on three distinct
nodes is at most a quadratic. -/
theorem interpolate_three_degree_lt
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (r : F → F) :
    ((Lagrange.interpolate (threeNodes a b c) id) r).degree < 3 := by
  have hcard : (threeNodes a b c).card = 3 := by
    rw [threeNodes, Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hvs : Set.InjOn id (threeNodes a b c : Set F) := Function.injective_id.injOn
  have h := Lagrange.degree_interpolate_lt r hvs
  rwa [hcard] at h

/-- A polynomial `P` of `degree < 3` (at most a quadratic) is recovered exactly
from its values at three distinct points — the Toom/NTT reconstruction
specialised to the three-point case. -/
theorem quadratic_recovered_from_three_points
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {P : F[X]} (hP : P.degree < 3) :
    ((Lagrange.interpolate (threeNodes a b c) id) fun x => eval x P) = P := by
  have hcard : (threeNodes a b c).card = 3 := by
    rw [threeNodes, Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hvs : Set.InjOn id (threeNodes a b c : Set F) := Function.injective_id.injOn
  refine interpolate_recovers hvs ?_
  rw [hcard]; exact hP

end Quadratic

end CatCrypt.Optimizer.Rewrite.LagrangeInterpGeneric
