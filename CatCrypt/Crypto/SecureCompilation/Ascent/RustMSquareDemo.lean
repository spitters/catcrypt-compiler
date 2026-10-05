/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.RustMSquare

/-!
# Demo: the correspondence square over a `RustM` program

A checked decrement run twice, carried through the square algebra of
`RustMSquare.lean`. The five steps are those of `AsmSquareDemo.lean` over an x86
block, in the same order, so the two sides can be read side by side.

1. A leg: `dec_square` is the square of one checked decrement.
2. Horizontal composition: `corresM_bind` composes the two legs over `kseq`.
3. The horizontal unit: `pureK` absorbs on the left and on the right, as an
   equality of programs.
4. The vertical direction: a `VMapM` raises the guard and weakens the exit
   relation to a bound, and `vsquareM_act` applies it.
5. A point inside the guard, and two boundaries at which the square is false.

## Main results

* `decSquare` — the two-step program refines `decTwiceSpec` under the guard
  `2 ≤ σ`.
* `dec_pureK_left`, `dec_pureK_right` — `pureK` on either side of `dec` gives
  back `dec`.
* `decSquare_bounded` — the composite read at the weakened boundary.
* `decSquare_witness` — a point inside the guard at which the program succeeds.
* `decSquare_not_unguarded`, `decSquare_not_shifted` — the square is false
  without the guard, and false with the value function shifted by one.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.RustM.Demos

open Aeneas.Std

/-- A checked decrement: a panic at zero. -/
def dec (n : Nat) : Aeneas.Std.RustM (Nat × Nat) :=
  if n = 0 then .fail .panic else .ok (n - 1, n - 1)

/-- The two-step program: decrement twice, carrying the counter as both value and
    state. -/
def decTwice : Nat → Aeneas.Std.RustM (Nat × Nat) := kseq dec (fun _ c => dec c)

/-- The abstract counterpart of `decTwice`. -/
def decTwiceSpec (σ : Nat) : Nat := σ - 2

/-! ## 1. The leg -/

/-- One decrement, as a square: the entry relation identifies the concrete counter with
    the abstract one, the guard is that the abstract counter is positive, and the exit
    relation identifies the decremented counters. -/
theorem dec_square :
    CorresM (fun c σ => c = σ) (fun σ => 1 ≤ σ) dec (fun σ => σ - 1)
      (fun c σ => c = σ - 1) := by
  intro c σ hc hG
  subst hc
  refine ⟨c - 1, ?_, rfl⟩
  simp only [dec, if_neg (by omega : ¬ c = 0)]

/-! ## 2. Horizontal composition -/

/-- **The composite.** Under the guard `2 ≤ σ`, `decTwice` succeeds with value
    `decTwiceSpec σ`, and its exit counter is that value. The continuation's square is
    the leg reindexed along `σ ↦ σ - 1`, since the second decrement runs one counter
    below the first. -/
theorem decSquare :
    CorresM (fun c σ => c = σ) (fun σ => 2 ≤ σ) decTwice decTwiceSpec
      (fun c σ => c = σ - 2) := by
  refine corresM_bind (Q := fun c σ => c = σ - 1) (V := fun σ => σ - 1) ?_ ?_
  · exact corresM_conseq dec_square (fun _ _ h _ => h) (fun _ h => by omega)
      (fun _ _ => rfl) (fun _ _ _ h => h)
  · intro a
    refine corresM_conseq (corresM_reindex (fun σ => σ - 1) dec_square) ?_ ?_ ?_ ?_
    · rintro c σ ⟨hc, -⟩ -; exact hc
    · intro σ hG; omega
    · intro σ hG; simp only [decTwiceSpec]; omega
    · intro c σ _ h; omega

/-! ## 3. The horizontal unit -/

/-- `pureK` on the left of `dec` gives back `dec`. -/
theorem dec_pureK_left (v : Nat) : kseq (pureK v) (fun _ c => dec c) = dec :=
  kseq_pure_left v (fun _ c => dec c)

/-- `pureK` on the right of `dec` gives back `dec`. -/
theorem dec_pureK_right : kseq dec (fun a c => pureK a c) = dec :=
  kseq_pure_right dec

/-! ## 4. The vertical direction -/

/-- A vertical arrow: raise the guard to `3 ≤ σ`, and read the exit relation as the
    bound `c ≤ σ` rather than the exact counter. -/
theorem boundExit :
    VMapM (fun c σ => c = σ) (fun c σ => c = σ) (fun σ => 2 ≤ σ) (fun σ => 3 ≤ σ)
      decTwiceSpec decTwiceSpec (fun c σ => c = σ - 2) (fun c σ => c ≤ σ) where
  hP := fun _ _ h _ => h
  hG := fun _ h => by omega
  hV := fun _ _ => rfl
  hQ := fun _ _ _ h => by omega

/-- **The composite at the weakened boundary**, by the action of `boundExit`. -/
theorem decSquare_bounded :
    CorresM (fun c σ => c = σ) (fun σ => 3 ≤ σ) decTwice decTwiceSpec
      (fun c σ => c ≤ σ) :=
  vsquareM_act decSquare boundExit

/-! ## 5. Two boundaries at which the square is false -/

/-- A point inside the guard at which both relations of `decSquare` hold and the program
    succeeds. -/
theorem decSquare_witness : decTwice 5 = .ok (decTwiceSpec 5, 3) := rfl

/-- Dropping the guard makes the square false: at `σ = 1` the second decrement
    panics. -/
theorem decSquare_not_unguarded :
    ¬ CorresM (fun c σ => c = σ) (fun _ => True) decTwice decTwiceSpec
        (fun c σ => c = σ - 2) := by
  intro h
  obtain ⟨c', hc, -⟩ := h 1 1 rfl trivial
  simp only [decTwice, kseq, dec] at hc
  cases hc

/-- Shifting the value function by one makes the square false. -/
theorem decSquare_not_shifted :
    ¬ CorresM (fun c σ => c = σ) (fun σ => 2 ≤ σ) decTwice (fun σ => σ - 1)
        (fun c σ => c = σ - 2) := by
  intro h
  obtain ⟨c', hc, -⟩ := h 2 2 rfl (by omega)
  simp only [decTwice, kseq, dec] at hc
  cases hc

end Hax.Ascent.RustM.Demos
