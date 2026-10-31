/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Hax.FoldRange

/-!
# Counting loops and mapped folds of hax extractions

Facts about the loop forms of haxpipe extractions, over the reasoning interface of
`CatCryptCore.Hax.FoldRange`.

## Main results

* `whileFold_count`: a `Hax.whileFold` with constant-true guard whose state carries a
  counter tested against a bound is the `Hax.foldRange` of its step;
  `whileFold_count_merge` states the step as the projection of the body's result.
* `foldRange_map_bounded`: a fold from `φ b` whose step commutes with `φ` on the range
  is `φ` of the fold on the other side.
* `index_map`: indexing a mapped array.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-- A `Hax.whileFold` whose state `mk s j` carries a counter `j` tested against `n`, steps
    `s` with `g` and increments the counter, is the `Hax.foldRange` of `g`. -/
theorem whileFold_count {T σ : Type} (mk : σ → Int → T) (n : Int)
    (g : Int → σ → σ) (f : T → ControlFlow T T)
    (hf : ∀ s j, f (mk s j) =
      if Hax.lt j n then Hax.cfContinue (mk (g j s) (Hax.add j (1 : Int)))
      else Hax.cfBreak (mk s j)) :
    ∀ (m : Nat) (i : Int) (s : σ), i + m = n →
      Hax.whileFold (mk s i) (fun _ => true) f
        = ControlFlow.Break (mk (Hax.foldRange i n s g) n) := by
  intro m i s hm
  refine Hax.whileFold_eq_of_fuel (n := m + 1) ?_
  induction m generalizing i s with
  | zero =>
    have hin : i = n := by simpa using hm
    subst hin
    simp [Hax.whileFoldFuel, hf, Hax.lt, Hax.cfBreak, Hax.foldRange_stop]
  | succ m ih =>
    have hlt : i < n := by push_cast at hm; omega
    have hstep := ih (i + 1) (g i s) (by push_cast at hm ⊢; omega)
    rw [Hax.whileFoldFuel]
    simp only [hf, Hax.lt, hlt, decide_true, ite_true, Hax.cfContinue, Hax.add]
    rw [hstep, Hax.foldRange_step _ _ _ _ hlt]

/-- `whileFold_count` with the step read off the body: when the body continues from
    `mk s' (j + 1)` while `j < n` and breaks otherwise, the loop is the `Hax.foldRange` of
    the step `s ↦ proj` of the body's result. -/
theorem whileFold_count_merge {T σ : Type} (mk : σ → Int → T) (proj : T → σ) (n : Int)
    (f : T → ControlFlow T T)
    (hf : ∀ s j, f (mk s j) =
      if j < n then .Continue (mk (proj (f (mk s j)).merge) (j + 1)) else .Break (mk s j)) :
    ∀ (m : Nat) (i : Int) (s : σ), i + m = n →
      Hax.whileFold (mk s i) (fun _ => true) f =
        .Break (mk (Hax.foldRange i n s fun j s => proj (f (mk s j)).merge) n) := by
  refine whileFold_count mk n _ f fun s j => ?_
  by_cases h : j < n
  · conv_lhs => rw [hf s j]
    simp [h, Hax.lt, Hax.cfContinue, Hax.add]
  · conv_lhs => rw [hf s j]
    simp [h, Hax.lt, Hax.cfBreak]

/-- A `Hax.foldRange` over `[lo, hi)` from `φ b` whose step commutes with `φ` on the range is
    `φ` of the fold of the step on the other side. -/
theorem foldRange_map_bounded {α β : Type} (φ : β → α) {lo hi : Int} {fa : Int → α → α}
    (fb : Int → β → β) (hstep : ∀ j b, lo ≤ j → j < hi → fa j (φ b) = φ (fb j b)) (b : β) :
    Hax.foldRange lo hi (φ b) fa = φ (Hax.foldRange lo hi b fb) :=
  foldRange_rel_bounded (R := fun a b => a = φ b) rfl
    fun j hj hj' a b' hab => by subst hab; exact hstep j b' hj hj'

/-- Indexing an array mapped by `f` is `f` of the indexed entry, for a nonempty array. -/
theorem index_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    (ha : 0 < a.size) (i : Int) : Hax.index (a.map f) i = f (Hax.index a i) := by
  grind [Hax.index]

end Hax
