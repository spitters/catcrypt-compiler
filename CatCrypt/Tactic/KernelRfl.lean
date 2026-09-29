/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# `kernel_rfl` — definitional equality checked by the kernel only

`kernel_rfl` closes a goal `a = b` with `Eq.refl a` without running the
elaborator's definitional-equality check. The kernel checks `a ≡ b` when the
enclosing declaration is added, and rejects the declaration when the two sides are
not definitionally equal.

The kernel reduces closed computations and keeps shared subterms shared, while the
elaborator's `isDefEq` unfolds through the transparency machinery. On the
evaluation of a reified straight-line program against its specification
(`ScalarStraightRun.runProg`), the elaborator's `rfl` exceeds its heartbeat budget
where the kernel finishes in about a second.

Scope: the goal must be an `Eq` without metavariables. Free variables are allowed;
the kernel treats them as opaque. A failure is reported at the declaration, not at
the tactic. In a `module` file the kernel unfolds only exposed definitions, so the
definitions the evaluation passes through must be exposed, and names built with
`toString` need `import all Init.Data.Repr` in the consuming module.
-/

@[expose] public section

namespace CatCrypt.Tactic

open Lean Elab Tactic Meta

/-- Close an `Eq` goal without metavariables by `Eq.refl` of its left-hand side,
    leaving the definitional-equality check to the kernel. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if tgt.hasMVar then
    throwError "kernel_rfl: the goal contains metavariables{indentExpr tgt}"
  let some (_, lhs, _) := tgt.eq? | throwError "kernel_rfl: the goal is not an equality{indentExpr tgt}"
  g.assign (← mkEqRefl lhs)
  replaceMainGoal []

end CatCrypt.Tactic
