/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCrypt.Relational.Rules

/-!
# Basic pRHL Tactics

This file provides basic tactic automation for pRHL proofs.
-/

@[expose] public section

namespace CatCrypt.Tactic

open Lean Elab Tactic
open CatCrypt.Relational

/-- Apply reflexivity rule -/
elab "rsame" : tactic => do
  evalTactic (← `(tactic| apply rHoare_refl))

/-- Apply bind rule -/
elab "rbind" : tactic => do
  evalTactic (← `(tactic| apply rHoare_bind))

/-- Apply return rule -/
elab "rret" : tactic => do
  evalTactic (← `(tactic| apply rHoare_ret))

/-- Apply sample_same rule (diagonal coupling) -/
elab "rsample_same" : tactic => do
  evalTactic (← `(tactic| apply rHoare_sample_same))

/-- Apply sample_bij rule with given bijection -/
elab "rsample_bij" f:term : tactic => do
  evalTactic (← `(tactic| apply rHoare_sample_bij $f))

/-- Apply consequence rule -/
elab "rconseq" : tactic => do
  evalTactic (← `(tactic| apply rHoare_conseq))

/-- Simplify relational assertions -/
elab "rsimp" : tactic => do
  evalTactic (← `(tactic| simp only [eqPre, eqPost, andPre, truePre, truePost]))

/-- Apply get_sync rule -/
elab "rget_sync" : tactic => do
  evalTactic (← `(tactic| apply rHoare_get_sync))

/-- Apply set_sync rule -/
elab "rset_sync" : tactic => do
  evalTactic (← `(tactic| apply rHoare_set_sync))

end CatCrypt.Tactic
