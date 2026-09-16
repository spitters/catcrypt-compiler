/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvLeaves
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvLeaves
public import Lean
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine

/-!
# Composing `CorresR` leaves over a straight-line `RInst64` block

The RV64 twin of `corres_sym` and `corres_solve` (`CorresSolver`). The
per-instruction leaves of `CorresRiscvLeaves` are folded through `corresR_cons`, the
cons form of `corresR_append`, and the abstract transition is synthesized as the
composed fold of the per-instruction steps.

* `@[corresR]` is the leaf registry, populated here with the twelve leaves.
* `corresR_cons` composes a single-instruction leaf on the head with a `CorresR`
  on the tail; `corresR_cons_true` is its instance at precondition `fun _ => True`.
* `corres_sym_rv` runs the `SymM` engine of `CorresSymEngine` at the machine
  `corresRMachine`: the `@[corresR]` leaves, `corresR_cons_true` on a composite
  block, `corresR_nil` on the empty block.
* `corresR_leaf` applies the first `@[corresR]` leaf that unifies with the goal.
* `corresR_chain` walks the block, `corresR_leaf` on each head.
* `corres_solve_rv` frees the goal's transition to a metavariable through
  `corresR_castFa`, runs `corresR_chain`, and closes the residual equality by
  `rfl`.

`corresR_subBorrow3` is the three-limb subtract with materialised borrows, the
RV64 counterpart of the `sbb` chain: each limb's borrow-out is an `sltu` word,
and the next limb subtracts it and folds its own `sltu` into the running borrow
by `or`.

## Main results

* `corresRMachine`, `corres_sym_rv`: the engine instance and its tactic.
* `corres_solve_rv`: the macro tactic composing the `@[corresR]` leaves over a
  straight-line `RInst64` block against a synthesized transition.
* `corresR_cons`, `corresR_cons_true`, `corresR_castFa`: the composition and
  transition-rewrite lemmas the tactics use.
* `corresR_subBorrow3`: the twelve-instruction three-limb subtract with borrows
  materialised by `sltu`, closed by `corres_sym_rv`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## The cons composition lemma -/

/-- The cons form of `corresR_append`: a single-instruction leaf `[i]` composed with
    the `CorresR` on the remaining block `c`, the abstract steps composed as
    `fun a => ga (fa a)`. -/
theorem corresR_cons {AState : Type} (SR : RState64 → AState → Prop)
    {P Q : AState → Prop} {fa ga : AState → AState} {i : RInst64} {c : List RInst64}
    (h₁ : CorresR SR P fa [i]) (h₂ : CorresR SR Q ga c) (hpre : ∀ a, P a → Q (fa a)) :
    CorresR SR P (fun a => ga (fa a)) (i :: c) := by
  exact corresR_append SR h₁ h₂ hpre

/-- `corresR_cons` at precondition `fun _ => True`. -/
theorem corresR_cons_true {AState : Type} (SR : RState64 → AState → Prop)
    {fa ga : AState → AState} {i : RInst64} {c : List RInst64}
    (h₁ : CorresR SR (fun _ => True) fa [i]) (h₂ : CorresR SR (fun _ => True) ga c) :
    CorresR SR (fun _ => True) (fun a => ga (fa a)) (i :: c) :=
  corresR_cons SR h₁ h₂ (fun _ _ => trivial)

/-- Rewrite the abstract transition of a `CorresR` along an equality. -/
theorem corresR_castFa {AState : Type} (SR : RState64 → AState → Prop)
    {P : AState → Prop} {fa fa' : AState → AState} {block : List RInst64}
    (h : CorresR SR P fa block) (he : fa = fa') : CorresR SR P fa' block :=
  he ▸ h

/-! ## The `@[corresR]` leaf registry -/

attribute [corresR] corresR_add corresR_sub corresR_sltu corresR_and corresR_or
  corresR_xor corresR_mul corresR_mulhu corresR_li corresR_mv corresR_srli corresR_slli

/-! ## The tactics -/

open Lean Elab Tactic Meta in
/-- Apply the first `@[corresR]` leaf lemma that unifies with the goal. Each
    candidate is applied at reducible transparency, so the match is structural on
    the instruction constructor and the relation's head constant, without unfolding
    `evalRInst64` or `SRr`. Fails if no leaf applies. -/
elab "corresR_leaf" : tactic => do
  let names ← Lean.labelled `corresR
  let goal ← getMainGoal
  for name in names do
    let s ← saveState
    try
      let newGoals ← withReducible (goal.apply (← mkConstWithFreshMVarLevels name))
      replaceMainGoal newGoals
      return
    catch _ =>
      restoreState s
  throwError "corresR_leaf: no @[corresR] leaf lemma applies to the goal"

/-- Compose the registered `@[corresR]` leaves over a straight-line block against a
    metavariable abstract transition: a single instruction is closed by
    `corresR_leaf`; `i :: c` is split by `corresR_cons`, the head matched by a leaf,
    the tail solved recursively, the precondition discharged by `fun _ _ => trivial`
    (every leaf has precondition `fun _ => True`). -/
syntax "corresR_chain" : tactic
macro_rules
  | `(tactic| corresR_chain) =>
    `(tactic|
      first
      | corresR_leaf
      | (apply corresR_cons
         · corresR_leaf
         · corresR_chain
         · exact fun _ _ => trivial))

/-- Refine a `CorresR` over a straight-line `RInst64` block by composing the
    registered `@[corresR]` leaves. `corresR_castFa` frees the goal's transition to
    a fresh metavariable, `corresR_chain` builds the composed fold against it, and
    the residual `fold = transition` equality closes by `rfl`; a goal that states its
    transition in a form not definitionally equal to the fold leaves that residual. -/
syntax "corres_solve_rv" : tactic
macro_rules
  | `(tactic| corres_solve_rv) =>
    `(tactic|
      (apply corresR_castFa
       · corresR_chain
       · rfl))

/-! ## The `SymM` solver -/

/-- The RV64 machine of the `SymM` engine: `CorresR` over a `List RInst64` block, the
    `@[corresR]` leaves, `corresR_cons_true`, `corresR_nil`, `corresR_weaken` and
    `corresR_castFa`, side conditions tried by `decide`. -/
meta def corresRMachine : CorresSymEngine.Machine where
  name := "corres_sym_rv"
  judgment := ``CorresR
  leaves := Lean.labelled `corresR
  split := ``corresR_cons_true
  empty := ``corresR_nil
  weaken := ``corresR_weaken
  castFa := ``corresR_castFa
  classify := CorresSymEngine.listShape

/-- Close `CorresR SR P fa block` over a straight-line `RInst64` block by composing the
    `@[corresR]` leaves with the `SymM` engine of `CorresSymEngine` at `corresRMachine`.
    A block given as a definition is put in weak head normal form by the engine; the
    synthesized transition is matched against the goal's transition by definitional
    equality. -/
elab "corres_sym_rv" : tactic => CorresSymEngine.solve corresRMachine

/-! ## The three-limb borrow chain

`subBorrow3Block` subtracts the three-limb value in `b0 b1 b2` from the one in
`a0 a1 a2`, little-endian, writing the difference limbs to `d0 d1 d2` and the
final borrow word to `bout`. Limb 0 is `sub`/`sltu`; each later limb `i` computes
`t := aᵢ - bᵢ`, its borrow `cᵢ := aᵢ <ᵘ bᵢ`, then `dᵢ := t - c_{i-1}` with the
second borrow `t <ᵘ c_{i-1}`, and the limb's borrow-out is the `or` of the two
(at most one of them is `1`). `subBorrow3Step` is the same computation on the
abstract state, as the fold of the per-instruction steps. -/

/-- The three-limb subtract with `sltu`-materialised borrows. -/
def subBorrow3Block (a0 a1 a2 b0 b1 b2 d0 d1 d2 c0 t1 c1 e1 t2 c2 e2 bout : String) :
    List RInst64 :=
  [ .sub d0 a0 b0, .sltu c0 a0 b0,
    .sub t1 a1 b1, .sltu c1 a1 b1, .sub d1 t1 c0, .sltu e1 t1 c0, .or c1 c1 e1,
    .sub t2 a2 b2, .sltu c2 a2 b2, .sub d2 t2 c1, .sltu e2 t2 c1, .or bout c2 e2 ]

/-- The abstract transition of `subBorrow3Block`: the fold of its twelve
    single-instruction steps, in program order. -/
def subBorrow3Step (a0 a1 a2 b0 b1 b2 d0 d1 d2 c0 t1 c1 e1 t2 c2 e2 bout : String)
    (st : AStateR) : AStateR :=
  orStepR bout c2 e2 (sltuStepR e2 t2 c1 (subStepR d2 t2 c1 (sltuStepR c2 a2 b2
    (subStepR t2 a2 b2 (orStepR c1 c1 e1 (sltuStepR e1 t1 c0 (subStepR d1 t1 c0
      (sltuStepR c1 a1 b1 (subStepR t1 a1 b1 (sltuStepR c0 a0 b0
        (subStepR d0 a0 b0 st)))))))))))

/-- The three-limb borrow chain refines its abstract fold. -/
theorem corresR_subBorrow3 (a0 a1 a2 b0 b1 b2 d0 d1 d2 c0 t1 c1 e1 t2 c2 e2 bout : String) :
    CorresR SRr (fun _ => True)
      (subBorrow3Step a0 a1 a2 b0 b1 b2 d0 d1 d2 c0 t1 c1 e1 t2 c2 e2 bout)
      (subBorrow3Block a0 a1 a2 b0 b1 b2 d0 d1 d2 c0 t1 c1 e1 t2 c2 e2 bout) := by
  corres_sym_rv

/-! ## Tests -/

/-- A single instruction. -/
theorem corres_solve_rv_add (d a b : String) :
    CorresR SRr (fun _ => True) (addStepR d a b) [.add d a b] := by
  corres_sym_rv

/-- A three-instruction mixed block: an add, its carry-out by `sltu`, a shift. -/
theorem corres_solve_rv_mixed (d a b c e : String) (sh : Nat) :
    CorresR SRr (fun _ => True)
      (fun st => srliStepR e d sh (sltuStepR c d a (addStepR d a b st)))
      [.add d a b, .sltu c d a, .srli e d sh] := by
  corres_sym_rv

end CatCrypt.Crypto.SecureCompilation.Ascent
