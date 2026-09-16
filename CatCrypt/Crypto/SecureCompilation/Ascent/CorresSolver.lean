/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresAttr
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresAttr
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine
public import Lean

/-!
# Composing `CorresJ` leaves over a straight-line `JInstr` block

The ascent supplies per-instruction `CorresJ` leaves — `corresJ_sbb`, `corresJ_adc`,
`corresJ_mulx`, `corresJ_adcx`, `corresJ_adox` (and their `SRcarry2` dual-flag
variants) — each refining one machine instruction against a clean abstract step
through a carry-tracking state relation. A multi-instruction block is refined by
folding these leaves through `corresJ_append`, threading the carry/limb state from
one instruction to the next. Every chain in the ascent (`corresJ_sbbChain`,
`corresJ_mulxChain`, `corresJ_adcxChain`, `corresJ_adxBlock`) is that fold written
out by hand for one instruction family.

This module makes the fold a tactic, in two forms.

* `@[corres]` is a label attribute collecting the per-instruction leaves. A leaf is
  a lemma whose conclusion is `CorresJ SR (fun _ => True) step [i]` for a single
  instruction `i`.
* `corresJ_cons` is the cons form of `corresJ_append`: a single-instruction leaf on
  the head, a `CorresJ` on the tail, composed to a `CorresJ` on `i :: c` with the
  abstract steps composed as `fun a => ga (fa a)`; `corresJ_cons_true` is its
  instance at precondition `fun _ => True`.
* `corres_sym` runs the `SymM` engine of `CorresSymEngine` at the machine
  `corresJMachine`: the `@[corres]` leaves indexed by relation and instruction,
  `corresJ_cons_true` on a composite block, `corresJ_nil` on the empty block,
  side conditions by `decide`. It is the solver the x86 ascent uses.
* `corres_leaf` applies the first `@[corres]` leaf that unifies with the goal, and
  `corres_solve` walks the block with it through `corresJ_cons`, as a macro
  recursion.

Extending the solvers to a new instruction is one `@[corres]` lemma; the tactics are
unchanged.

## Main results

* `corresJ_cons`, `corresJ_cons_true`, `corresJ_castFa`: the composition and
  transition-rewrite lemmas.
* `corresJMachine`, `corres_sym`: the engine instance and its tactic.
* `corres_leaf`, `corres_chain`, `corres_solve`: the macro solver.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The cons composition lemma -/

/-- The cons form of `corresJ_append`: a single-instruction leaf `[i]` composed with
    the `CorresJ` on the remaining block `c`. The abstract steps compose as
    `fun a => ga (fa a)`, and the head leaf's postcondition feeds the tail's
    precondition (`hpre`). -/
theorem corresJ_cons {AState : Type} (SR : JState 64 → AState → Prop)
    {P Q : AState → Prop} {fa ga : AState → AState} {i : JInstr 64} {c : List (JInstr 64)}
    (h₁ : CorresJ SR P fa [i]) (h₂ : CorresJ SR Q ga c) (hpre : ∀ a, P a → Q (fa a)) :
    CorresJ SR P (fun a => ga (fa a)) (i :: c) := by
  have h := corresJ_append SR h₁ h₂ hpre
  simpa using h

/-- `corresJ_cons` at precondition `fun _ => True`: a leaf on the head instruction and a
    `CorresJ` on the tail compose to the block `i :: c` with the transitions composed as
    `fun a => ga (fa a)`. -/
theorem corresJ_cons_true {AState : Type} (SR : JState 64 → AState → Prop)
    {fa ga : AState → AState} {i : JInstr 64} {c : List (JInstr 64)}
    (h₁ : CorresJ SR (fun _ => True) fa [i]) (h₂ : CorresJ SR (fun _ => True) ga c) :
    CorresJ SR (fun _ => True) (fun a => ga (fa a)) (i :: c) :=
  corresJ_cons SR h₁ h₂ (fun _ _ => trivial)

/-- Rewrite the abstract transition of a `CorresJ` along an equality. Lets a solver
    synthesize the fold against a fresh metavariable and reconcile it with a goal's
    pinned transition afterwards. -/
theorem corresJ_castFa {AState : Type} (SR : JState 64 → AState → Prop)
    {P : AState → Prop} {fa fa' : AState → AState} {block : List (JInstr 64)}
    (h : CorresJ SR P fa block) (he : fa = fa') : CorresJ SR P fa' block :=
  he ▸ h

/-! ## The `@[corres]` leaf registry -/

attribute [corres] corresJ_sbb corresJ_adc corresJ_mulx corresJ_adcx
  corresJ_adcx2 corresJ_adox2 corresJ_mulx2

/-! ## The `SymM` solver -/

/-- The x86 machine of the `SymM` engine: `CorresJ` over a `List (JInstr 64)` block, the
    `@[corres]` leaves, `corresJ_cons_true`, `corresJ_nil`, `corresJ_weaken` and
    `corresJ_castFa`, side conditions tried by `decide`. -/
meta def corresJMachine : CorresSymEngine.Machine where
  name := "corres_sym"
  judgment := ``CorresJ
  leaves := Lean.labelled `corres
  split := ``corresJ_cons_true
  empty := ``corresJ_nil
  weaken := ``corresJ_weaken
  castFa := ``corresJ_castFa
  classify := CorresSymEngine.listShape

/-- Close `CorresJ SR P fa block` over a straight-line block by composing the `@[corres]`
    leaves with the `SymM` engine of `CorresSymEngine` at `corresJMachine`. The block may
    be a list literal, a definition, a concatenation, or a translation `xs.map f` whose
    instructions reduce to `JInstr` constructors. The synthesized transition is matched
    against the goal's transition by definitional equality. Side conditions that
    `decide` does not close are left as goals. -/
elab "corres_sym" : tactic => CorresSymEngine.solve corresJMachine

/-! ## The macro solver -/

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
    equal to the fold. The recursion is a macro recursion, so its depth grows with the
    block length. -/
syntax "corres_solve" : tactic
macro_rules
  | `(tactic| corres_solve) =>
    `(tactic|
      (apply corresJ_castFa
       · corres_chain
       · rfl))

/-! ## Tests -/

/-- A two-limb subtract-with-borrow chain, solved by `corres_sym` (the ascent's
    hand-proved `corresJ_sbb_chain`). -/
theorem corres_solve_sbb2 (d0 s0 d1 s1 : String) :
    CorresJ SRcarry (fun _ => True) (fun a => sbbStep d1 s1 (sbbStep d0 s0 a))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1)] := by
  corres_sym

/-- A three-instruction subtract-with-borrow chain. -/
theorem corres_solve_sbb3 (d0 s0 d1 s1 d2 s2 : String) :
    CorresJ SRcarry (fun _ => True)
      (fun a => sbbStep d2 s2 (sbbStep d1 s1 (sbbStep d0 s0 a)))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1), .sbb d2 (.reg s2)] := by
  corres_sym

/-- A mixed widening-multiply + add-with-carry block over the single-carry relation
    `SRcarry`. -/
theorem corres_solve_mulx_adcx (dh dl ra rb d s : String) :
    CorresJ SRcarry (fun _ => True)
      (fun a => adcStep d s (mulxStep dh dl ra rb a))
      [.mulx dh dl (.reg ra) (.reg rb), .adcx d (.reg s)] := by
  corres_sym

/-- A dual-carry (`CF`+`OF`) block over `SRcarry2`: a widening multiply, an `adcx`
    (`CF` chain), and an `adox` (`OF` chain). -/
theorem corres_solve_adx (dh dl ra rb d1 s1 d2 s2 : String) :
    CorresJ SRcarry2 (fun _ => True)
      (fun a => adoxStep2 d2 s2 (adcxStep2 d1 s1 (mulxStep2 dh dl ra rb a)))
      [.mulx dh dl (.reg ra) (.reg rb), .adcx d1 (.reg s1), .adox d2 (.reg s2)] := by
  corres_sym

/-- The macro solver `corres_solve` on the three-instruction subtract-with-borrow
    chain. -/
example (d0 s0 d1 s1 d2 s2 : String) :
    CorresJ SRcarry (fun _ => True)
      (fun a => sbbStep d2 s2 (sbbStep d1 s1 (sbbStep d0 s0 a)))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1), .sbb d2 (.reg s2)] := by
  corres_solve

end CatCrypt.Crypto.SecureCompilation.Ascent
