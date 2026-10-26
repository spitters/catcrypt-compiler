/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.WP

@[expose] public section

set_option autoImplicit false

/-!
# `Std.WP` triples over `StateT σ Option`

A program of `StateT σ Option` runs from a state to a value and a final state, or fails. Its
`Std.WP` assertions are predicates on `σ`, and its failure postcondition is a predicate on
`Unit`. The weakest precondition at a state is the postcondition at the result of the run
(`wp_apply_run`), and a triple with the failure postcondition `⊥` is the total-correctness
statement on `run` (`triple_iff_run`). The machine runs of `SepLogic/VC` (state `σ × T`) and
the bignum runs of `Jasmin/BignumExec` are instances.

## Main results

* `wp_apply_run`: the weakest precondition of a `StateT σ Option` program at a state.
* `triple_iff_run`: a triple over `StateT σ Option` is a statement on `run`.
-/

namespace CatCrypt.Crypto.Util

open Std.WP

variable {σ α : Type _}

/-- The weakest precondition of a `StateT σ Option` program at a state is its postcondition at
    the result of the run, and the failure postcondition when the run fails. -/
theorem wp_apply_run (x : StateT σ Option α) (Q : α → σ → Prop) (E : Unit → Prop) (s : σ) :
    wp x Q E s = (match x.run s with | some (a, s') => Q a s' | none => E ()) := by
  rw [StateT.wp_apply_eq]
  rcases x.run s with _ | ⟨a, s'⟩ <;> rfl

/-- **Triples over `StateT σ Option` are statements on `run`.** The triple with the failure
    postcondition `⊥` says that from every state satisfying `P` the run returns a value and a
    state satisfying `Q`. -/
theorem triple_iff_run (x : StateT σ Option α) (P : σ → Prop) (Q : α → σ → Prop) :
    ⦃fun s => P s⦄ x ⦃fun a s => Q a s⦄ ↔
      ∀ s, P s → ∃ a s', x.run s = some (a, s') ∧ Q a s' := by
  rw [Triple.iff]
  refine forall_congr' fun s => imp_congr Iff.rfl ?_
  rw [wp_apply_run]
  rcases x.run s with _ | ⟨a, s'⟩
  · simp [Lean.Order.bot_apply]
  · exact ⟨fun h => ⟨a, s', rfl, h⟩, fun ⟨_, _, h, hq⟩ => by cases h; exact hq⟩

end CatCrypt.Crypto.Util
