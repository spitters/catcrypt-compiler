/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Runtime
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Reasoning API for `Hax.foldRange`

`Hax.foldRange` is the loop form every haxpipe extraction emits, and it is sealed
`@[irreducible]` (unfolding it inside the large `mutual` blocks haxpipeT produces
is what blows past the heartbeat limit). This module is the reasoning interface:
each lemma `unseal`s locally, so downstream proofs never have to.

Four ways to reason about such a loop, in increasing order of what they need:

* `foldRange_step` / `foldRange_stop`, stated in `Runtime` — peel one iteration,
  or finish. Unrolls a concrete-bound loop.
* `foldRange_rel_bounded` — relational congruence, with the step relation
  required only for indices *inside* the range (`Hax.foldRange_rel` in `Runtime`
  demands it everywhere, which is often false at out-of-range indices).
* `foldRange_induct` — a running-index invariant `P i acc`, for when the
  post-condition mentions how far the loop has got.
* `foldRange_finFoldl_rel` — bridges an extraction loop to a reference stated
  with `Fin.foldl`, which is how the clean specs are written.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

variable {α β : Type}

/-! ## Unrolling

`Hax.foldRange_step` and `Hax.foldRange_stop` (peel one iteration, or finish) are
stated in `HaxLean.Runtime`. -/

/-- Reindex the step function by shifting both endpoints. -/
theorem go_shift (fa : Int → α → α) :
    ∀ (m : Nat) (s : Int) (b : α),
      Hax.foldRange.go fa m (s + 1) b = Hax.foldRange.go (fun i => fa (i + 1)) m s b := by
  intro m
  induction m with
  | zero => intro s b; rfl
  | succ m ih =>
    intro s b
    show Hax.foldRange.go fa m (s + 1 + 1) (fa (s + 1) b)
        = Hax.foldRange.go (fun i => fa (i + 1)) m (s + 1) (fa (s + 1) b)
    exact ih (s + 1) (fa (s + 1) b)

unseal Hax.foldRange in
/-- Shift both endpoints by one, reindexing the step. -/
theorem foldRange_shift (lo hi : Int) (b : α) (fa : Int → α → α) :
    Hax.foldRange (lo + 1) (hi + 1) b fa
      = Hax.foldRange lo hi b (fun i => fa (i + 1)) := by
  show Hax.foldRange.go fa ((hi + 1) - (lo + 1)).toNat (lo + 1) b
      = Hax.foldRange.go (fun i => fa (i + 1)) (hi - lo).toNat lo b
  have he : ((hi + 1) - (lo + 1)).toNat = (hi - lo).toNat := by omega
  rw [he]; exact go_shift fa (hi - lo).toNat lo b

/-! ## Relational congruence and invariants -/

unseal Hax.foldRange in
/-- Relational congruence needing the step relation only on `[lo, hi)`. -/
theorem foldRange_rel_bounded {R : α → β → Prop} {lo hi : Int}
    {fa : Int → α → α} {fb : Int → β → β} {ia : α} {ib : β}
    (h0 : R ia ib)
    (hstep : ∀ i, lo ≤ i → i < hi → ∀ a b, R a b → R (fa i a) (fb i b)) :
    R (Hax.foldRange lo hi ia fa) (Hax.foldRange lo hi ib fb) := by
  show R (Hax.foldRange.go fa (hi - lo).toNat lo ia) (Hax.foldRange.go fb (hi - lo).toNat lo ib)
  suffices H : ∀ (n : Nat) (s : Int) a b, lo ≤ s → s + n ≤ hi → R a b →
      R (Hax.foldRange.go fa n s a) (Hax.foldRange.go fb n s b) by
    by_cases hle : lo ≤ hi
    · exact H _ lo ia ib (le_refl _) (by omega) h0
    · rw [show (hi - lo).toNat = 0 from by omega]; exact h0
  intro n
  induction n with
  | zero => intro s a b _ _ hab; exact hab
  | succ n ih =>
    intro s a b hs hsn hab
    show R (Hax.foldRange.go fa n (s + 1) (fa s a)) (Hax.foldRange.go fb n (s + 1) (fb s b))
    exact ih (s + 1) (fa s a) (fb s b) (by omega) (by omega) (hstep s hs (by omega) a b hab)

unseal Hax.foldRange in
/-- A running-index invariant: `P lo` of the initial value, advanced by each
    in-range step, yields `P hi` of the fold. -/
theorem foldRange_induct {P : Int → α → Prop} {lo hi : Int}
    {f : Int → α → α} {init : α} (hle : lo ≤ hi) (h0 : P lo init)
    (hstep : ∀ i a, lo ≤ i → i < hi → P i a → P (i + 1) (f i a)) :
    P hi (Hax.foldRange lo hi init f) := by
  show P hi (Hax.foldRange.go f (hi - lo).toNat lo init)
  suffices H : ∀ (n : Nat) (s : Int) a, lo ≤ s → s + n = hi → P s a →
      P hi (Hax.foldRange.go f n s a) by
    exact H _ lo init (le_refl _) (by omega) h0
  intro n
  induction n with
  | zero => intro s a _ hsn ha; rw [show hi = s by omega]; exact ha
  | succ n ih =>
    intro s a hs hsn ha
    show P hi (Hax.foldRange.go f n (s + 1) (f s a))
    exact ih (s + 1) (f s a) (by omega) (by omega) (hstep s a hs (by omega) ha)

/-! ## Bridging to a `Fin.foldl` reference -/

/-- `foldRange 0 0` with a `Nat`-cast bound. -/
theorem foldRange_zero_cast (ia : α) (fa : Int → α → α) :
    Hax.foldRange 0 ((0 : Nat) : Int) ia fa = ia := by
  rw [Nat.cast_zero]; exact foldRange_stop 0 0 ia fa (by norm_num)

/-- Peel the first index off `foldRange 0 (n+1)` with a `Nat`-cast bound. -/
theorem foldRange_succ_cast (n : Nat) (ia : α) (fa : Int → α → α) :
    Hax.foldRange 0 ((n + 1 : Nat) : Int) ia fa
      = Hax.foldRange 0 ((n : Nat) : Int) (fa 0 ia) (fun i => fa (i + 1)) := by
  rw [show ((n + 1 : Nat) : Int) = ((n : Nat) : Int) + 1 by push_cast; ring,
      foldRange_step 0 (((n : Nat) : Int) + 1) ia fa (by push_cast; omega)]
  exact foldRange_shift 0 ((n : Nat) : Int) (fa 0 ia) fa

/-- Relate an extraction's `foldRange 0 n` to a reference's `Fin.foldl n`: both
    visit `0, 1, …, n-1` in order, so per-index step compatibility suffices. -/
theorem foldRange_finFoldl_rel {R : α → β → Prop} :
    ∀ (n : Nat) {fa : Int → α → α} {gb : β → Fin n → β} {ia : α} {ib : β},
      R ia ib →
      (∀ (i : Nat) (hi : i < n) a b, R a b → R (fa (i : Int) a) (gb b ⟨i, hi⟩)) →
      R (Hax.foldRange 0 (n : Int) ia fa) (Fin.foldl n gb ib) := by
  intro n
  induction n with
  | zero =>
    intro fa gb ia ib h0 _
    rw [foldRange_zero_cast, Fin.foldl_zero]; exact h0
  | succ n ih =>
    intro fa gb ia ib h0 hstep
    rw [foldRange_succ_cast, Fin.foldl_succ]
    refine ih (fa := fun i => fa (i + 1)) (gb := fun x i => gb x i.succ)
      (ia := fa 0 ia) (ib := gb ib 0) ?_ ?_
    · have := hstep 0 (Nat.zero_lt_succ n) ia ib h0
      simpa using this
    · intro i hi a b hab
      have := hstep (i + 1) (Nat.succ_lt_succ hi) a b hab
      simpa [Fin.succ, Nat.add_comm] using this

end Hax
