/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF

/-!
# Fuel monotonicity of `denote'`

`denote'` consumes fuel only in its loop helpers, which return `.err "out of fuel"` at
fuel `0`. A run that does not end in an error is the run at every larger fuel. The
argument follows the evaluation order: a construct evaluates a subexpression only when
the outcomes before it are normal, so a non-error run evaluates each subexpression to a
non-error outcome, and by induction each of those runs is stable under more fuel. A
counted loop evaluates its upper bound only when its lower bound is a value that is not
a control-flow value.

## Main results

* `fuelFree` — the expression contains no loop, so its run does not use fuel
* `denote'_fuel_mono` — a non-error run is the run at every larger fuel
* `denote'_fuel_mono_of_fuelFree` — the run of a `fuelFree` program does not depend on
  the fuel
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- The outcome is an error. -/
def isErr : Outcome → Bool
  | .err _ => true
  | _ => false

@[simp] theorem isErr_val (v : Value) : isErr (.val v) = false := rfl
@[simp] theorem isErr_err (m : String) : isErr (.err m) = true := rfl
@[simp] theorem isErr_earlyRet (v : Value) : isErr (.earlyRet v) = false := rfl
@[simp] theorem isErr_broke (v : Value) : isErr (.broke v) = false := rfl
@[simp] theorem isErr_continued : isErr .continued = false := rfl

/-- The expression contains no loop construct, so its run consumes no fuel. -/
def fuelFree : ImpExpr → Bool
  | .forLoop _ _ _ _ | .forLoopRev _ _ _ _ | .whileLoop _ _ | .forFold _ _ _ _
  | .forFoldRev _ _ _ _ | .whileFold _ _ | .forFoldReturn _ _ _ _
  | .forFoldRevReturn _ _ _ _ | .whileFoldReturn _ _ => false
  | .lit _ | .var _ | .unitVal | .continue_ | .lam _ _ | .break_ none => true
  | .letBind _ v b => fuelFree v && fuelFree b
  | .app _ args => fuelFreeList args
  | .tuple elems => fuelFreeList elems
  | .proj e _ => fuelFree e
  | .ifThenElse c t e => fuelFree c && fuelFree t && fuelFree e
  | .match_ s arms => fuelFree s && fuelFreeArms arms
  | .seq e1 e2 => fuelFree e1 && fuelFree e2
  | .borrow e => fuelFree e
  | .deref e => fuelFree e
  | .assign _ rhs => fuelFree rhs
  | .break_ (some e) => fuelFree e
  | .earlyReturn e => fuelFree e
  | .questionMark e => fuelFree e
  | .cfBreak e => fuelFree e
  | .cfContinue e => fuelFree e
  | .cfBreakContinue e => fuelFree e
  | .typeAscription e _ => fuelFree e
where
  /-- Every expression of the list is `fuelFree`. -/
  fuelFreeList : List ImpExpr → Bool
    | [] => true
    | e :: es => fuelFree e && fuelFreeList es
  /-- Every arm body is `fuelFree`. -/
  fuelFreeArms : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => fuelFree e && fuelFreeArms rest

theorem stateM_bind_apply {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

theorem stateM_get_apply {σ : Type} (s : σ) : (get : StateM σ σ) s = (s, s) := rfl

theorem stateM_set_apply {σ : Type} (s t : σ) : (set t : StateM σ PUnit) s = (⟨⟩, t) := rfl

theorem stateM_modify_apply {σ : Type} (g : σ → σ) (s : σ) :
    (modify g : StateM σ PUnit) s = (⟨⟩, g s) := rfl

set_option hygiene false in
/-- The case of a counted loop in `denote'_fuel_mono_aux`: the lower bound; when it is
    a value that is not a control-flow value, the upper bound; then the loop helper. -/
local macro "bounded_loop_case" : tactic => `(tactic| (
  intro fuel var lo hi body ihlo ihhi ihl env hd fuel' hle
  simp only [fuelFree, Bool.false_eq_true, false_or] at hd
  rcases hr1 : denote' bi fuel lo env with ⟨o1, s1⟩
  have hlo : isErr o1 = false := by
    rcases o1 with (v1|v1|v1|_|m1)
    all_goals try rfl
    exfalso
    revert hd
    simp [denote', stateM_bind_apply, hr1, pure, StateT.pure]
  have h1 : denote' bi fuel' lo env = denote' bi fuel lo env :=
    ihlo env (Or.inr (by rw [hr1]; exact hlo)) fuel' hle
  simp only [denote', stateM_bind_apply, h1, hr1] at hd ⊢
  rcases o1 with (v1|v1|v1|_|m1)
  all_goals try rfl
  cases v1
  all_goals try rfl
  all_goals
    simp only [stateM_bind_apply] at hd ⊢
    rcases hr2 : denote' bi fuel hi s1 with ⟨o2, s2⟩
    have hhi : isErr o2 = false := by
      rcases o2 with (v2|v2|v2|_|m2)
      all_goals try rfl
      exfalso
      revert hd
      simp [hr2, pure, StateT.pure]
    have h2 : denote' bi fuel' hi s1 = denote' bi fuel hi s1 :=
      ihhi s1 (Or.inr (by rw [hr2]; exact hhi)) fuel' hle
    simp only [h2, hr2] at hd ⊢
    rcases o2 with (v2|v2|v2|_|m2)
    all_goals try rfl
    all_goals try cases v2
    all_goals try rfl
    all_goals exact ihl _ _ s2 hd fuel' hle))

set_option hygiene false in
/-- The case of a construct with one child whose non-value outcomes pass through, in
    `denote'_fuel_mono_aux`. -/
local macro "strict_child_case" : tactic => `(tactic| (
  intro fuel e ih env hd fuel' hle
  simp only [fuelFree] at hd
  rcases hr : denote' bi fuel e env with ⟨o, s⟩
  have h1 : denote' bi fuel' e env = denote' bi fuel e env := by
    refine ih env (hd.imp id (fun hd => ?_)) fuel' hle
    cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
  simp only [denote', stateM_bind_apply, h1]))

set_option hygiene false in
/-- The case of a `while` construct in `denote'_fuel_mono_aux`. -/
local macro "while_case" : tactic => `(tactic| (
  intro fuel c b ih env hd fuel' hle
  simp only [fuelFree, Bool.false_eq_true, false_or] at hd
  simp only [denote'] at hd ⊢
  exact ih env hd fuel' hle))

set_option hygiene false in
/-- The fuel-`0` case of a loop helper in `denote'_fuel_mono_aux`: the run is an
    error. -/
local macro "loop_zero_case" f:ident : tactic => `(tactic| (
  intro var lo hi body hlt env hd fuel' _
  exfalso
  unfold $f at hd
  simp [if_neg hlt, pure, StateT.pure] at hd))

set_option hygiene false in
/-- The fuel-`0` case of a `while` helper in `denote'_fuel_mono_aux`: the run is an
    error. -/
local macro "while_zero_case" f:ident : tactic => `(tactic| (
  intro c b env hd fuel' _
  exfalso
  unfold $f at hd
  simp [pure, StateT.pure] at hd))

set_option hygiene false in
/-- The empty-range case of a counted-loop helper in `denote'_fuel_mono_aux`. -/
local macro "loop_empty_case" f:ident : tactic => `(tactic| (
  intro fuel var lo hi body hge env _ fuel' _
  unfold $f
  simp only [if_pos hge]))

set_option hygiene false in
/-- The recursive call of a loop helper in `denote'_fuel_mono_aux`, through `ihr`. -/
local macro "loop_rec" : tactic => `(tactic| (
  exact ihr _ hd (fuel' - 1) (by omega)))

set_option hygiene false in
/-- Closes the goals left after the first step of a loop helper: equal outcomes, or
    the recursive call through `ihr`. -/
local macro "loop_close" : tactic => `(tactic| (
  all_goals try rfl
  all_goals try loop_rec
  all_goals cases v
  all_goals try rfl
  all_goals try loop_rec
  all_goals rename_i b w
  all_goals cases b
  all_goals try rfl
  all_goals try loop_rec
  all_goals cases w
  all_goals try rfl
  all_goals try loop_rec
  all_goals rename_i b' w'
  all_goals cases b'
  all_goals first | rfl | loop_rec))

set_option hygiene false in
/-- The step case of a counted-loop helper in `denote'_fuel_mono_aux`, with the
    loop variable bound to `idx`. -/
local macro "loop_step_case" f:ident idx:term : tactic => `(tactic| (
  intro fuel var lo hi body hlt hf ihb ihr env hd fuel' hle
  have hf' : ¬ fuel' = 0 := by omega
  unfold $f at hd ⊢
  simp only [if_neg hlt, if_neg hf, if_neg hf', stateM_bind_apply, stateM_modify_apply] at hd ⊢
  rcases hr : denote' bi fuel body (Env.extend env var (.int $idx)) with ⟨o, s⟩
  have h1 : denote' bi fuel' body (Env.extend env var (.int $idx)) =
      denote' bi fuel body (Env.extend env var (.int $idx)) := by
    refine ihb _ (Or.inr ?_) fuel' hle
    rw [hr]
    rcases o with (v|v|v|_|m) <;> simp_all [pure, StateT.pure]
  simp only [h1, hr] at hd ⊢
  rcases o with (v|v|v|_|m)
  loop_close))

set_option hygiene false in
/-- The step case of a `while` helper in `denote'_fuel_mono_aux`. -/
local macro "while_step_case" f:ident : tactic => `(tactic| (
  intro fuel c b hf ihc ihb ihr env hd fuel' hle
  have hf' : ¬ fuel' = 0 := by omega
  unfold $f at hd ⊢
  simp only [if_neg hf, if_neg hf', stateM_bind_apply] at hd ⊢
  rcases hr1 : denote' bi fuel c env with ⟨o1, s1⟩
  have h1 : denote' bi fuel' c env = denote' bi fuel c env := by
    refine ihc env (Or.inr ?_) fuel' hle
    rw [hr1]
    rcases o1 with (v|v|v|_|m) <;> simp_all [pure, StateT.pure]
  simp only [h1, hr1] at hd ⊢
  rcases o1 with (v1|v1|v1|_|m1)
  all_goals try rfl
  cases v1
  all_goals try rfl
  rename_i bc
  cases bc
  · rfl
  simp only [stateM_bind_apply] at hd ⊢
  rcases hr2 : denote' bi fuel b s1 with ⟨o2, s2⟩
  have h2 : denote' bi fuel' b s1 = denote' bi fuel b s1 := by
    refine ihb s1 (Or.inr ?_) fuel' hle
    rw [hr2]
    rcases o2 with (v|v|v|_|m) <;> simp_all [pure, StateT.pure]
  simp only [h2, hr2] at hd ⊢
  rcases o2 with (v|v|v|_|m)
  loop_close))

/-- Fuel stability of `denote'` on a run that is `fuelFree` or not an error, proved with
    the thirteen helpers of the mutual block. -/
theorem denote'_fuel_mono_aux (bi : Builtins) :
    (∀ fuel e env, (fuelFree e = true ∨ isErr (denote' bi fuel e env).1 = false) →
      ∀ fuel', fuel ≤ fuel' → denote' bi fuel' e env = denote' bi fuel e env) := by
  intro fuel e
  refine (denote'.mutual_induct
    (motive1 := fun fuel e => ∀ env,
      (fuelFree e = true ∨ isErr (denote' bi fuel e env).1 = false) →
      ∀ fuel', fuel ≤ fuel' → denote' bi fuel' e env = denote' bi fuel e env)
    (motive2 := fun fuel c b => ∀ env,
      isErr (denoteWhile'Return bi fuel c b env).1 = false →
      ∀ fuel', fuel ≤ fuel' → denoteWhile'Return bi fuel' c b env = denoteWhile'Return bi fuel c b env)
    (motive3 := fun fuel var lo hi body => ∀ env,
      isErr (denoteForLoopRev'Return bi fuel var lo hi body env).1 = false →
      ∀ fuel', fuel ≤ fuel' →
        denoteForLoopRev'Return bi fuel' var lo hi body env =
          denoteForLoopRev'Return bi fuel var lo hi body env)
    (motive4 := fun fuel var lo hi body => ∀ env,
      isErr (denoteForLoop'Return bi fuel var lo hi body env).1 = false →
      ∀ fuel', fuel ≤ fuel' →
        denoteForLoop'Return bi fuel' var lo hi body env =
          denoteForLoop'Return bi fuel var lo hi body env)
    (motive5 := fun fuel c b => ∀ env,
      isErr (denoteWhile' bi fuel c b env).1 = false →
      ∀ fuel', fuel ≤ fuel' → denoteWhile' bi fuel' c b env = denoteWhile' bi fuel c b env)
    (motive6 := fun fuel var lo hi body => ∀ env,
      isErr (denoteForLoopRev' bi fuel var lo hi body env).1 = false →
      ∀ fuel', fuel ≤ fuel' →
        denoteForLoopRev' bi fuel' var lo hi body env = denoteForLoopRev' bi fuel var lo hi body env)
    (motive7 := fun fuel var lo hi body => ∀ env,
      isErr (denoteForLoop' bi fuel var lo hi body env).1 = false →
      ∀ fuel', fuel ≤ fuel' →
        denoteForLoop' bi fuel' var lo hi body env = denoteForLoop' bi fuel var lo hi body env)
    (motive8 := fun fuel c b => ∀ env,
      isErr (denoteWhileOrig' bi fuel c b env).1 = false →
      ∀ fuel', fuel ≤ fuel' → denoteWhileOrig' bi fuel' c b env = denoteWhileOrig' bi fuel c b env)
    (motive9 := fun fuel var lo hi body => ∀ env,
      isErr (denoteForLoopRevOrig' bi fuel var lo hi body env).1 = false →
      ∀ fuel', fuel ≤ fuel' →
        denoteForLoopRevOrig' bi fuel' var lo hi body env =
          denoteForLoopRevOrig' bi fuel var lo hi body env)
    (motive10 := fun fuel var lo hi body => ∀ env,
      isErr (denoteForLoopOrig' bi fuel var lo hi body env).1 = false →
      ∀ fuel', fuel ≤ fuel' →
        denoteForLoopOrig' bi fuel' var lo hi body env =
          denoteForLoopOrig' bi fuel var lo hi body env)
    (motive11 := fun fuel v arms => ∀ env,
      (fuelFree.fuelFreeArms arms = true ∨ isErr (denoteMatchArms' bi fuel v arms env).1 = false) →
      ∀ fuel', fuel ≤ fuel' →
        denoteMatchArms' bi fuel' v arms env = denoteMatchArms' bi fuel v arms env)
    (motive12 := fun fuel args => ∀ env,
      (fuelFree.fuelFreeList args = true ∨ (denoteArgs' bi fuel args env).1.isSome = true) →
      ∀ fuel', fuel ≤ fuel' → denoteArgs' bi fuel' args env = denoteArgs' bi fuel args env)
    (motive13 := fun fuel f args => ∀ env,
      (fuelFree.fuelFreeList args = true ∨ isErr (denoteApp' bi fuel f args env).1 = false) →
      ∀ fuel', fuel ≤ fuel' → denoteApp' bi fuel' f args env = denoteApp' bi fuel f args env)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_).1 fuel e
  -- lit
  · intros; simp only [denote']
  -- var
  · intros; simp only [denote']
  -- letBind
  · intro fuel n val body ih1 ih2 env hd fuel' hle
    simp only [fuelFree, Bool.and_eq_true] at hd
    rcases hr : denote' bi fuel val env with ⟨o, s⟩
    have h1 : denote' bi fuel' val env = denote' bi fuel val env := by
      refine ih1 env ?_ fuel' hle
      rcases hd with hd | hd
      · exact Or.inl hd.1
      · right; cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case controlFlow => rfl
      all_goals
        simp only [stateM_bind_apply, stateM_modify_apply]
        refine ih2 _ (hd.imp (·.2) (fun h => ?_)) fuel' hle
        simpa [denote', stateM_bind_apply, hr, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure] using h
    | _ => rfl
  -- lam
  · intros; simp only [denote']
  -- app
  · intro fuel f args ih env hd fuel' hle
    simp only [fuelFree] at hd
    simp only [denote'] at hd ⊢
    exact ih env hd fuel' hle
  -- tuple
  · intro fuel elems ih env hd fuel' hle
    simp only [fuelFree] at hd
    rcases hr : denoteArgs' bi fuel elems env with ⟨o, s⟩
    have h1 : denoteArgs' bi fuel' elems env = denoteArgs' bi fuel elems env := by
      refine ih env (hd.imp id (fun hd => ?_)) fuel' hle
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1]
  -- proj
  · intro fuel e i ih env hd fuel' hle
    simp only [fuelFree] at hd
    rcases hr : denote' bi fuel e env with ⟨o, s⟩
    have h1 : denote' bi fuel' e env = denote' bi fuel e env := by
      refine ih env (hd.imp id (fun hd => ?_)) fuel' hle
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1]
  -- ifThenElse
  · intro fuel c t e ihc iht ihe env hd fuel' hle
    simp only [fuelFree, Bool.and_eq_true] at hd
    rcases hr : denote' bi fuel c env with ⟨o, s⟩
    have h1 : denote' bi fuel' c env = denote' bi fuel c env := by
      refine ihc env ?_ fuel' hle
      rcases hd with hd | hd
      · exact Or.inl hd.1.1
      · right; cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case bool b =>
        cases b
        · refine ihe s (hd.imp (·.2) (fun h => ?_)) fuel' hle
          simpa [denote', stateM_bind_apply, hr] using h
        · refine iht s (hd.imp (·.1.2) (fun h => ?_)) fuel' hle
          simpa [denote', stateM_bind_apply, hr] using h
      all_goals rfl
    | _ => rfl
  -- match_
  · intro fuel scrut arms ihs iha env hd fuel' hle
    simp only [fuelFree, Bool.and_eq_true] at hd
    rcases hr : denote' bi fuel scrut env with ⟨o, s⟩
    have h1 : denote' bi fuel' scrut env = denote' bi fuel scrut env := by
      refine ihs env ?_ fuel' hle
      rcases hd with hd | hd
      · exact Or.inl hd.1
      · right; cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case controlFlow => rfl
      all_goals
        refine iha _ s (hd.imp (·.2) (fun h => ?_)) fuel' hle
        simpa [denote', stateM_bind_apply, hr] using h
    | _ => rfl
  -- unitVal
  · intros; simp only [denote']
  -- seq
  · intro fuel e1 e2 ih1 ih2 env hd fuel' hle
    simp only [fuelFree, Bool.and_eq_true] at hd
    rcases hr : denote' bi fuel e1 env with ⟨o, s⟩
    have h1 : denote' bi fuel' e1 env = denote' bi fuel e1 env := by
      refine ih1 env ?_ fuel' hle
      rcases hd with hd | hd
      · exact Or.inl hd.1
      · right; cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case controlFlow => rfl
      all_goals
        refine ih2 s (hd.imp (·.2) (fun h => ?_)) fuel' hle
        simpa [denote', stateM_bind_apply, hr] using h
    | _ => rfl
  -- borrow
  · intro fuel e ih env hd fuel' hle
    simp only [fuelFree] at hd
    simp only [denote'] at hd ⊢
    exact ih env hd fuel' hle
  -- deref
  · intro fuel e ih env hd fuel' hle
    simp only [fuelFree] at hd
    simp only [denote'] at hd ⊢
    exact ih env hd fuel' hle
  -- assign
  · intro fuel n e ih env hd fuel' hle
    simp only [fuelFree] at hd
    rcases hr : denote' bi fuel e env with ⟨o, s⟩
    have h1 : denote' bi fuel' e env = denote' bi fuel e env := by
      refine ih env (hd.imp id (fun hd => ?_)) fuel' hle
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1]
  -- forLoop
  · bounded_loop_case
  -- forLoopRev
  · bounded_loop_case
  -- whileLoop
  · while_case
  -- break_ (some e)
  · strict_child_case
  -- break_ none
  · intros; simp only [denote']
  -- continue_
  · intros; simp only [denote']
  -- earlyReturn
  · strict_child_case
  -- questionMark
  · strict_child_case
  -- forFold
  · bounded_loop_case
  -- forFoldRev
  · bounded_loop_case
  -- whileFold
  · while_case
  -- forFoldReturn
  · bounded_loop_case
  -- forFoldRevReturn
  · bounded_loop_case
  -- whileFoldReturn
  · while_case
  -- cfBreak
  · strict_child_case
  -- cfContinue
  · strict_child_case
  -- cfBreakContinue
  · strict_child_case
  -- typeAscription
  · intro fuel e tyStr ih env hd fuel' hle
    simp only [fuelFree] at hd
    simp only [denote'] at hd ⊢
    exact ih env hd fuel' hle
  -- denoteWhile'Return
  · while_zero_case denoteWhile'Return
  · while_step_case denoteWhile'Return
  -- denoteForLoopRev'Return
  · loop_empty_case denoteForLoopRev'Return
  · loop_zero_case denoteForLoopRev'Return
  · loop_step_case denoteForLoopRev'Return (hi - 1)
  -- denoteForLoop'Return
  · loop_empty_case denoteForLoop'Return
  · loop_zero_case denoteForLoop'Return
  · loop_step_case denoteForLoop'Return lo
  -- denoteWhile'
  · while_zero_case denoteWhile'
  · while_step_case denoteWhile'
  -- denoteForLoopRev'
  · loop_empty_case denoteForLoopRev'
  · loop_zero_case denoteForLoopRev'
  · loop_step_case denoteForLoopRev' (hi - 1)
  -- denoteForLoop'
  · loop_empty_case denoteForLoop'
  · loop_zero_case denoteForLoop'
  · loop_step_case denoteForLoop' lo
  -- denoteWhileOrig'
  · while_zero_case denoteWhileOrig'
  · while_step_case denoteWhileOrig'
  -- denoteForLoopRevOrig'
  · loop_empty_case denoteForLoopRevOrig'
  · loop_zero_case denoteForLoopRevOrig'
  · loop_step_case denoteForLoopRevOrig' (hi - 1)
  -- denoteForLoopOrig'
  · loop_empty_case denoteForLoopOrig'
  · loop_zero_case denoteForLoopOrig'
  · loop_step_case denoteForLoopOrig' lo
  -- denoteMatchArms' []
  · intros; simp only [denoteMatchArms']
  -- denoteMatchArms' (arm :: rest)
  · intro fuel v pat body rest ihb ihr env hd fuel' hle
    simp only [fuelFree.fuelFreeArms, Bool.and_eq_true] at hd
    simp only [denoteMatchArms', stateM_bind_apply, stateM_get_apply] at hd ⊢
    cases hm : matchPat pat v env with
    | none =>
      simp only [hm] at hd ⊢
      exact ihr env (hd.imp (·.2) id) fuel' hle
    | some env' =>
      simp only [hm, stateM_bind_apply, stateM_set_apply] at hd ⊢
      exact ihb env' (hd.imp (·.1) id) fuel' hle
  -- denoteArgs' []
  · intros; simp only [denoteArgs']
  -- denoteArgs' (e :: es)
  · intro fuel e es ihe ihr env hd fuel' hle
    simp only [fuelFree.fuelFreeList, Bool.and_eq_true] at hd
    rcases hr : denote' bi fuel e env with ⟨o, s⟩
    have h1 : denote' bi fuel' e env = denote' bi fuel e env := by
      refine ihe env ?_ fuel' hle
      rcases hd with hd | hd
      · exact Or.inl hd.1
      · right; rcases o with (v|v|v|_|m) <;> simp_all [denoteArgs', stateM_bind_apply, pure, StateT.pure]
    simp only [denoteArgs', stateM_bind_apply, h1, hr] at hd ⊢
    rcases o with (v|v|v|_|m)
    all_goals try rfl
    cases v
    case controlFlow => rfl
    all_goals
      simp only [stateM_bind_apply] at hd ⊢
      rw [ihr s (hd.imp (·.2) (fun h => by simpa [pure, StateT.pure] using h)) fuel' hle]
  -- denoteApp'
  · intro fuel f args ih env hd fuel' hle
    simp only [denoteApp', stateM_bind_apply] at hd ⊢
    rcases hr : denoteArgs' bi fuel args env with ⟨o, s⟩
    have h1 : denoteArgs' bi fuel' args env = denoteArgs' bi fuel args env := by
      refine ih env (hd.imp id (fun hd => ?_)) fuel' hle
      rw [hr]
      cases o <;> simp_all [pure, StateT.pure]
    rw [h1, hr]

/-- **Fuel monotonicity.** A run at `fuel` that does not end in an error is the run,
    outcome and environment, at every `fuel' ≥ fuel`. -/
theorem denote'_fuel_mono (bi : Builtins) {fuel fuel' : Nat} {e : ImpExpr} {env : Env}
    (hne : isErr (denote' bi fuel e env).1 = false)
    (hle : fuel ≤ fuel') : denote' bi fuel' e env = denote' bi fuel e env :=
  denote'_fuel_mono_aux bi fuel e env (Or.inr hne) fuel' hle

/-- The run of a `fuelFree` program does not depend on the fuel. -/
theorem denote'_fuel_mono_of_fuelFree (bi : Builtins) {fuel fuel' : Nat} {e : ImpExpr}
    {env : Env} (hf : fuelFree e = true) :
    denote' bi fuel' e env = denote' bi fuel e env := by
  rcases Nat.le_total fuel fuel' with h | h
  · exact denote'_fuel_mono_aux bi fuel e env (Or.inl hf) fuel' h
  · exact (denote'_fuel_mono_aux bi fuel' e env (Or.inl hf) fuel h).symm

/-- A value outcome at `fuel` is the outcome at every larger fuel. -/
theorem denote'_val_mono (bi : Builtins) {fuel fuel' : Nat} {e : ImpExpr} {env : Env}
    {v : Value} (hv : (denote' bi fuel e env).1 = .val v)
    (hle : fuel ≤ fuel') : denote' bi fuel' e env = denote' bi fuel e env :=
  denote'_fuel_mono bi (by rw [hv]; rfl) hle

end Hax.Ascent
