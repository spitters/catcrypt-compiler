/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresAttr
import Lean

/-!
# `corres_solve`: composing `CorresJ` leaves over a straight-line `JInstr` block

The ascent supplies per-instruction `CorresJ` leaves — `corresJ_sbb`, `corresJ_adc`,
`corresJ_mulx`, `corresJ_adcx`, `corresJ_adox` (and their `SRcarry2` dual-flag
variants) — each refining one machine instruction against a clean abstract step
through a carry-tracking state relation. A multi-instruction block is refined by
folding these leaves through `corresJ_append`, threading the carry/limb state from
one instruction to the next. Every chain in the ascent (`corresJ_sbbChain`,
`corresJ_mulxChain`, `corresJ_adcxChain`, `corresJ_adxBlock`) is that fold written
out by hand for one instruction family.

This module makes the fold a tactic.

* `@[corres]` is a label attribute collecting the per-instruction leaves. A leaf is
  a lemma whose conclusion is `CorresJ SR (fun _ => True) step [i]` for a single
  instruction `i`.
* `corresJ_cons` is the cons form of `corresJ_append`: a single-instruction leaf on
  the head, a `CorresJ` on the tail, composed to a `CorresJ` on `i :: c` with the
  abstract steps composed as `fun a => ga (fa a)`.
* `corres_leaf` applies the first `@[corres]` leaf that unifies with the goal.
* `corres_solve` walks the block: a single-instruction block is closed by
  `corres_leaf`; a `i :: c` block is split by `corresJ_cons` — `corres_leaf` on the
  head, `corres_solve` on the tail, the `corresJ_append` precondition discharged by
  `fun _ => trivial` (every leaf has precondition `fun _ => True`). It composes the
  small per-instruction leaves by application, synthesizing the abstract fold, rather
  than elaborating a whole-block symbolic execution.

Extending the solver to a new instruction is one `@[corres]` lemma; the tactic is
unchanged.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The cons composition lemma -/

/-- The cons form of `corresJ_append`: a single-instruction leaf `[i]` composed with
    the `CorresJ` on the remaining block `c`. The abstract steps compose as
    `fun a => ga (fa a)`, and the head leaf's postcondition feeds the tail's
    precondition (`hpre`). The lemma `corres_solve` recurses through. -/
theorem corresJ_cons {AState : Type} (SR : JState 64 → AState → Prop)
    {P Q : AState → Prop} {fa ga : AState → AState} {i : JInstr 64} {c : List (JInstr 64)}
    (h₁ : CorresJ SR P fa [i]) (h₂ : CorresJ SR Q ga c) (hpre : ∀ a, P a → Q (fa a)) :
    CorresJ SR P (fun a => ga (fa a)) (i :: c) := by
  have h := corresJ_append SR h₁ h₂ hpre
  simpa using h

/-! ## The `@[corres]` leaf registry -/

attribute [corres] corresJ_sbb corresJ_adc corresJ_mulx corresJ_adcx
  corresJ_adcx2 corresJ_adox2 corresJ_mulx2

/-! ## The tactics -/

open Lean Elab Tactic Meta in
/-- Apply the first `@[corres]` leaf lemma that unifies with the goal. Each candidate
    is applied with fresh universe metavariables at **reducible** transparency, so the
    unification matches the goal's single-instruction block structurally (by
    instruction and register constructors) and the state relation by head constant,
    without unfolding the machine semantics (`evalInstr`) or the relation bodies
    (`SRcarry`, `SRcarry2`). Fails if no leaf applies. -/
elab "corres_leaf" : tactic => do
  let names ← Lean.labelled `corres
  let goal ← getMainGoal
  for name in names do
    let s ← saveState
    try
      let newGoals ← withReducible (goal.apply (← mkConstWithFreshMVarLevels name))
      replaceMainGoal newGoals
      return
    catch _ =>
      restoreState s
  throwError "corres_leaf: no @[corres] leaf lemma applies to the goal"

/-- Rewrite the abstract transition of a `CorresJ` along an equality. Lets
    `corres_solve` synthesize the fold against a fresh metavariable and reconcile it
    with a goal's pinned transition afterwards. -/
theorem corresJ_castFa {AState : Type} (SR : JState 64 → AState → Prop)
    {P : AState → Prop} {fa fa' : AState → AState} {block : List (JInstr 64)}
    (h : CorresJ SR P fa block) (he : fa = fa') : CorresJ SR P fa' block :=
  he ▸ h

/-- Compose the registered `@[corres]` leaves over a straight-line block against a
    metavariable abstract transition. A single-instruction block is closed by
    `corres_leaf`; a `i :: c` block is split by `corresJ_cons` — the head matched by a
    leaf, the tail solved recursively, the `corresJ_append` precondition (all leaves
    have precondition `fun _ => True`) discharged by `fun _ => trivial`. The transition
    is a metavariable throughout, so `corresJ_cons` assigns it the composed fold
    `fun a => ga (fa a)` with no higher-order guessing. -/
syntax "corres_chain" : tactic
macro_rules
  | `(tactic| corres_chain) =>
    `(tactic|
      first
      | corres_leaf
      | (apply corresJ_cons
         · corres_leaf
         · corres_chain
         · exact fun _ _ => trivial))

/-- Refine a `CorresJ` over a straight-line `JInstr` block by composing the registered
    `@[corres]` leaves, threading the carry/limb state. The abstract transition is
    synthesized bottom-up as the composed fold of the per-instruction abstract steps:
    `corresJ_castFa` frees the goal's transition to a fresh metavariable, `corres_chain`
    builds the fold against it, and the residual `synthesized-fold = goal-transition`
    equality closes by `rfl` (they are beta-equal) — so a goal that pins a concrete
    fold leaves no residual, and one that leaves it open synthesizes it. Each leaf
    discharges its per-instruction obligation, so the carry-out predicates are carried
    inside the abstract steps (`sbbStep`/`adcStep`), not left as separate goals; a
    residual arises only when the caller states the transition in a form not definitionally
    equal to the fold. Composes small per-instruction leaf lemmas by application rather
    than elaborating a whole-block symbolic execution. -/
syntax "corres_solve" : tactic
macro_rules
  | `(tactic| corres_solve) =>
    `(tactic|
      (apply corresJ_castFa
       · corres_chain
       · rfl))

/-! ## Tests -/

/-- A two-limb subtract-with-borrow chain, solved by `corres_solve` (the ascent's
    hand-proved `corresJ_sbb_chain`). -/
theorem corres_solve_sbb2 (d0 s0 d1 s1 : String) :
    CorresJ SRcarry (fun _ => True) (fun a => sbbStep d1 s1 (sbbStep d0 s0 a))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1)] := by
  corres_solve

/-- A three-instruction subtract-with-borrow chain. -/
theorem corres_solve_sbb3 (d0 s0 d1 s1 d2 s2 : String) :
    CorresJ SRcarry (fun _ => True)
      (fun a => sbbStep d2 s2 (sbbStep d1 s1 (sbbStep d0 s0 a)))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1), .sbb d2 (.reg s2)] := by
  corres_solve

/-- A mixed widening-multiply + add-with-carry block over the single-carry relation
    `SRcarry`. -/
theorem corres_solve_mulx_adcx (dh dl ra rb d s : String) :
    CorresJ SRcarry (fun _ => True)
      (fun a => adcStep d s (mulxStep dh dl ra rb a))
      [.mulx dh dl (.reg ra) (.reg rb), .adcx d (.reg s)] := by
  corres_solve

/-- A dual-carry (`CF`+`OF`) block over `SRcarry2`: a widening multiply, an `adcx`
    (`CF` chain), and an `adox` (`OF` chain). -/
theorem corres_solve_adx (dh dl ra rb d1 s1 d2 s2 : String) :
    CorresJ SRcarry2 (fun _ => True)
      (fun a => adoxStep2 d2 s2 (adcxStep2 d1 s1 (mulxStep2 dh dl ra rb a)))
      [.mulx dh dl (.reg ra) (.reg rb), .adcx d1 (.reg s1), .adox d2 (.reg s2)] := by
  corres_solve

end CatCrypt.Crypto.SecureCompilation.Ascent
