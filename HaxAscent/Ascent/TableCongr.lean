/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.EarlyExit

/-!
# Runs under builtin tables that agree on the called names

`denote'` consults its builtin table only at `.app f args`. `callsOK ok e` states that
every call of `e`, closures included, is to a name accepted by `ok`. Two tables that agree
on every accepted name give the same run of such an expression, at every fuel and from
every environment. A table extended by entries for names the program does not call
therefore leaves every run of the program unchanged, successful or not, and every
correspondence proved under the smaller table holds under the larger one.

## Main definitions

* `callsOK`

## Main results

* `denote'_congr` — the run is the same under two tables that agree on the called names
* `haxEval_congr`, `fnCorres_congr`, `fnCorresX_congr` — the same for the eventual value
  and for the function correspondences
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- Every call of the expression is to a name accepted by `ok`; closures included. -/
def callsOK (ok : String → Bool) : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal | .continue_ | .break_ none => true
  | .lam _ b => callsOK ok b
  | .letBind _ v b => callsOK ok v && callsOK ok b
  | .app f args => ok f && callsOKList ok args
  | .tuple elems => callsOKList ok elems
  | .proj e _ => callsOK ok e
  | .ifThenElse c t e => callsOK ok c && callsOK ok t && callsOK ok e
  | .match_ s arms => callsOK ok s && callsOKArms ok arms
  | .seq e1 e2 => callsOK ok e1 && callsOK ok e2
  | .borrow e => callsOK ok e
  | .deref e => callsOK ok e
  | .assign _ rhs => callsOK ok rhs
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b =>
    callsOK ok lo && callsOK ok hi && callsOK ok b
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b => callsOK ok c && callsOK ok b
  | .break_ (some e) => callsOK ok e
  | .earlyReturn e => callsOK ok e
  | .questionMark e => callsOK ok e
  | .cfBreak e => callsOK ok e
  | .cfContinue e => callsOK ok e
  | .cfBreakContinue e => callsOK ok e
  | .typeAscription e _ => callsOK ok e
where
  /-- Every expression of the list passes `callsOK`. -/
  callsOKList (ok : String → Bool) : List ImpExpr → Bool
    | [] => true
    | e :: es => callsOK ok e && callsOKList ok es
  /-- Every arm body passes `callsOK`. -/
  callsOKArms (ok : String → Bool) : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => callsOK ok e && callsOKArms ok rest

section Congr

/-- Unfold the loop helper at the head of the goal once. -/
local macro "unfold_loop_helper" : tactic => `(tactic| first
  | unfold denoteWhile'Return | unfold denoteWhile' | unfold denoteWhileOrig'
  | unfold denoteForLoopRev'Return | unfold denoteForLoop'Return | unfold denoteForLoopRev'
  | unfold denoteForLoop' | unfold denoteForLoopRevOrig' | unfold denoteForLoopOrig')

variable (bi bi' : Builtins) (ok : String → Bool)

/-- The run of `denote'` and of its thirteen helpers is the same under two tables that
    agree on the accepted names, by the mutual induction of `denote'`. -/
theorem denote'_congr_aux (hag : ∀ f, ok f = true → bi f = bi' f) :
    ∀ fuel e, callsOK ok e = true → denote' bi fuel e = denote' bi' fuel e := by
  intro fuel e
  refine (denote'.mutual_induct
    (motive1 := fun fuel e => callsOK ok e = true → denote' bi fuel e = denote' bi' fuel e)
    (motive2 := fun fuel c b => callsOK ok c = true → callsOK ok b = true →
      denoteWhile'Return bi fuel c b = denoteWhile'Return bi' fuel c b)
    (motive3 := fun fuel var lo hi body => callsOK ok body = true →
      denoteForLoopRev'Return bi fuel var lo hi body = denoteForLoopRev'Return bi' fuel var lo hi body)
    (motive4 := fun fuel var lo hi body => callsOK ok body = true →
      denoteForLoop'Return bi fuel var lo hi body = denoteForLoop'Return bi' fuel var lo hi body)
    (motive5 := fun fuel c b => callsOK ok c = true → callsOK ok b = true →
      denoteWhile' bi fuel c b = denoteWhile' bi' fuel c b)
    (motive6 := fun fuel var lo hi body => callsOK ok body = true →
      denoteForLoopRev' bi fuel var lo hi body = denoteForLoopRev' bi' fuel var lo hi body)
    (motive7 := fun fuel var lo hi body => callsOK ok body = true →
      denoteForLoop' bi fuel var lo hi body = denoteForLoop' bi' fuel var lo hi body)
    (motive8 := fun fuel c b => callsOK ok c = true → callsOK ok b = true →
      denoteWhileOrig' bi fuel c b = denoteWhileOrig' bi' fuel c b)
    (motive9 := fun fuel var lo hi body => callsOK ok body = true →
      denoteForLoopRevOrig' bi fuel var lo hi body = denoteForLoopRevOrig' bi' fuel var lo hi body)
    (motive10 := fun fuel var lo hi body => callsOK ok body = true →
      denoteForLoopOrig' bi fuel var lo hi body = denoteForLoopOrig' bi' fuel var lo hi body)
    (motive11 := fun fuel v arms => callsOK.callsOKArms ok arms = true →
      denoteMatchArms' bi fuel v arms = denoteMatchArms' bi' fuel v arms)
    (motive12 := fun fuel args => callsOK.callsOKList ok args = true →
      denoteArgs' bi fuel args = denoteArgs' bi' fuel args)
    (motive13 := fun fuel f args => ok f = true → callsOK.callsOKList ok args = true →
      denoteApp' bi fuel f args = denoteApp' bi' fuel f args)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_).1 fuel e
  all_goals
    intros
    try simp only [callsOK, callsOK.callsOKList, callsOK.callsOKArms, Bool.and_eq_true] at *
  all_goals first
    | (simp only [denote', *]; done)
    | (simp only [denoteApp', denoteArgs', denoteMatchArms', *]; done)
    | (unfold_loop_helper; simp only [*, ↓reduceIte]; done)

variable {bi bi' ok}

/-- **Table extension.** Two builtin tables that agree on every name accepted by `ok`
    give the same run of an expression whose calls are all accepted by `ok`. -/
theorem denote'_congr (hag : ∀ f, ok f = true → bi f = bi' f) {e : ImpExpr}
    (he : callsOK ok e = true) (fuel : Nat) : denote' bi fuel e = denote' bi' fuel e :=
  denote'_congr_aux bi bi' ok hag fuel e he

theorem haxEval_congr (hag : ∀ f, ok f = true → bi f = bi' f) {e : ImpExpr}
    (he : callsOK ok e = true) (env : Env) : haxEval bi e env = haxEval bi' e env := by
  by_cases hex : ∃ v fuel₀, ∀ fuel, fuel₀ ≤ fuel → (denote' bi fuel e env).1 = .val v
  · obtain ⟨v, f₀, hv⟩ := hex
    rw [haxEval_eq hv, haxEval_eq (fuel₀ := f₀) fun fuel hf => by
      rw [← denote'_congr hag he]; exact hv fuel hf]
  · have hex' : ¬ ∃ v fuel₀, ∀ fuel, fuel₀ ≤ fuel → (denote' bi' fuel e env).1 = .val v :=
      fun ⟨v, f₀, hv⟩ => hex ⟨v, f₀, fun fuel hf => by rw [denote'_congr hag he]; exact hv fuel hf⟩
    unfold haxEval
    rw [dif_neg hex, dif_neg hex']

theorem fnCorres_congr (hag : ∀ f, ok f = true → bi f = bi' f) {e : ImpExpr}
    (he : callsOK ok e = true) {A β : Type} [HaxEnc β] {entry : A → Env} {G : A → Prop}
    {g : A → β} (h : FnCorres bi e entry G g) : FnCorres bi' e entry G g := by
  intro a hG
  obtain ⟨f₀, hr⟩ := h a hG
  exact ⟨f₀, fun fuel hf => by rw [← denote'_congr hag he]; exact hr fuel hf⟩

theorem fnCorresX_congr (hag : ∀ f, ok f = true → bi f = bi' f) {e : ImpExpr}
    (he : callsOK ok e = true) {A R β : Type} [HaxEnc R] [HaxEnc β] {entry : A → Env}
    {G : A → Prop} {g : A → Except R β} (h : FnCorresX bi e entry G g) :
    FnCorresX bi' e entry G g := by
  intro a hG
  obtain ⟨f₀, hr⟩ := h a hG
  exact ⟨f₀, fun fuel hf => by rw [← denote'_congr hag he]; exact hr fuel hf⟩

end Congr

section TableLE

variable {bi bi' : Builtins} {ok : String → Bool}

set_option hygiene false in
/-- The case of a construct with one child whose non-value outcomes pass through, in
    `denote'_tableLE_aux`. -/
local macro "strict_child_case" : tactic => `(tactic| (
  intro ih hc env hd
  simp only [callsOK] at hc
  rcases hr : denote' bi fuel e env with ⟨o, s⟩
  have h1 : denote' bi' fuel e env = denote' bi fuel e env := by
    refine ih hc env ?_
    cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
  simp only [denote', stateM_bind_apply, h1]))

set_option hygiene false in
/-- The case of a construct that is the run of its child or of a loop helper, in
    `denote'_tableLE_aux`. -/
local macro "transparent_case" : tactic => `(tactic| (
  intro ih hc env hd
  simp only [callsOK, Bool.and_eq_true] at hc
  simp only [denote'] at hd ⊢
  first | exact ih hc env hd | exact ih hc.1 hc.2 env hd))

set_option hygiene false in
/-- The case of a counted loop in `denote'_tableLE_aux`: the lower bound; when it is a
    value that is not a control-flow value, the upper bound; then the loop helper, through
    `ihl` at the integers the two bounds denote. -/
local macro "bounded_loop_case" : tactic => `(tactic| (
  intro fuel var lo hi body ihlo ihhi ihl _ _ _ hc env hd
  simp only [callsOK, Bool.and_eq_true] at hc
  rcases hr1 : denote' bi fuel lo env with ⟨o1, s1⟩
  have hlo : isErr o1 = false := by
    rcases o1 with (v1|v1|v1|_|m1)
    all_goals try rfl
    exfalso
    revert hd
    simp [denote', stateM_bind_apply, hr1, pure, StateT.pure]
  have h1 : denote' bi' fuel lo env = denote' bi fuel lo env :=
    ihlo hc.1.1 env (by rw [hr1]; exact hlo)
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
    have h2 : denote' bi' fuel hi s1 = denote' bi fuel hi s1 :=
      ihhi hc.1.2 s1 (by rw [hr2]; exact hhi)
    simp only [h2, hr2] at hd ⊢
    rcases o2 with (v2|v2|v2|_|m2)
    all_goals try rfl
    all_goals try cases v2
    all_goals try rfl
    all_goals exact ihl _ _ hc.2 s2 hd))

set_option hygiene false in
/-- The fuel-`0` case of a counted-loop helper in `denote'_tableLE_aux`: the run is an
    error. -/
local macro "loop_zero_case" f:ident : tactic => `(tactic| (
  intro var lo hi body hlt hc env hd
  exfalso
  unfold $f at hd
  simp [if_neg hlt, pure, StateT.pure] at hd))

set_option hygiene false in
/-- The fuel-`0` case of a `while` helper in `denote'_tableLE_aux`: the run is an
    error. -/
local macro "while_zero_case" f:ident : tactic => `(tactic| (
  intro c b hcc hcb env hd
  exfalso
  unfold $f at hd
  simp [pure, StateT.pure] at hd))

set_option hygiene false in
/-- The empty-range case of a counted-loop helper in `denote'_tableLE_aux`. -/
local macro "loop_empty_case" f:ident : tactic => `(tactic| (
  intro fuel var lo hi body hge hc env _
  unfold $f
  simp only [if_pos hge]))

set_option hygiene false in
/-- The recursive call of a loop helper in `denote'_tableLE_aux`, through `ihr`. -/
local macro "loop_rec" : tactic => `(tactic| (
  first | exact ihr hc _ hd | exact ihr hcc hcb _ hd))

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
/-- The step case of a counted-loop helper in `denote'_tableLE_aux`, with the loop
    variable bound to `idx`. -/
local macro "loop_step_case" f:ident idx:term : tactic => `(tactic| (
  intro fuel var lo hi body hlt hf ihb ihr hc env hd
  unfold $f at hd ⊢
  simp only [if_neg hlt, if_neg hf, stateM_bind_apply, stateM_modify_apply] at hd ⊢
  rcases hr : denote' bi fuel body (Env.extend env var (.int $idx)) with ⟨o, s⟩
  have h1 : denote' bi' fuel body (Env.extend env var (.int $idx)) =
      denote' bi fuel body (Env.extend env var (.int $idx)) := by
    refine ihb hc _ ?_
    rw [hr]
    rcases o with (v|v|v|_|m) <;> simp_all [pure, StateT.pure]
  simp only [h1, hr] at hd ⊢
  rcases o with (v|v|v|_|m)
  loop_close))

set_option hygiene false in
/-- The step case of a `while` helper in `denote'_tableLE_aux`. -/
local macro "while_step_case" f:ident : tactic => `(tactic| (
  intro fuel c b hf ihc ihb ihr hcc hcb env hd
  unfold $f at hd ⊢
  simp only [if_neg hf, stateM_bind_apply] at hd ⊢
  rcases hr1 : denote' bi fuel c env with ⟨o1, s1⟩
  have h1 : denote' bi' fuel c env = denote' bi fuel c env := by
    refine ihc hcc env ?_
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
  have h2 : denote' bi' fuel b s1 = denote' bi fuel b s1 := by
    refine ihb hcb s1 ?_
    rw [hr2]
    rcases o2 with (v|v|v|_|m) <;> simp_all [pure, StateT.pure]
  simp only [h2, hr2] at hd ⊢
  rcases o2 with (v|v|v|_|m)
  loop_close))

/-- A run of `denote'` or of one of its thirteen helpers that does not end in an error
    is the run under every table that returns the same value wherever the first table
    returns one on an accepted name, by the mutual induction of `denote'`. -/
theorem denote'_tableLE_aux
    (hsub : ∀ f, ok f = true → ∀ args r, bi f args = some r → bi' f args = some r) :
    ∀ fuel e, callsOK ok e = true → ∀ env, isErr (denote' bi fuel e env).1 = false →
      denote' bi' fuel e env = denote' bi fuel e env := by
  intro fuel e
  refine (denote'.mutual_induct
    (motive1 := fun fuel e => callsOK ok e = true → ∀ env,
      isErr (denote' bi fuel e env).1 = false → denote' bi' fuel e env = denote' bi fuel e env)
    (motive2 := fun fuel c b => callsOK ok c = true → callsOK ok b = true → ∀ env,
      isErr (denoteWhile'Return bi fuel c b env).1 = false →
      denoteWhile'Return bi' fuel c b env = denoteWhile'Return bi fuel c b env)
    (motive3 := fun fuel var lo hi body => callsOK ok body = true → ∀ env,
      isErr (denoteForLoopRev'Return bi fuel var lo hi body env).1 = false →
      denoteForLoopRev'Return bi' fuel var lo hi body env =
        denoteForLoopRev'Return bi fuel var lo hi body env)
    (motive4 := fun fuel var lo hi body => callsOK ok body = true → ∀ env,
      isErr (denoteForLoop'Return bi fuel var lo hi body env).1 = false →
      denoteForLoop'Return bi' fuel var lo hi body env =
        denoteForLoop'Return bi fuel var lo hi body env)
    (motive5 := fun fuel c b => callsOK ok c = true → callsOK ok b = true → ∀ env,
      isErr (denoteWhile' bi fuel c b env).1 = false →
      denoteWhile' bi' fuel c b env = denoteWhile' bi fuel c b env)
    (motive6 := fun fuel var lo hi body => callsOK ok body = true → ∀ env,
      isErr (denoteForLoopRev' bi fuel var lo hi body env).1 = false →
      denoteForLoopRev' bi' fuel var lo hi body env = denoteForLoopRev' bi fuel var lo hi body env)
    (motive7 := fun fuel var lo hi body => callsOK ok body = true → ∀ env,
      isErr (denoteForLoop' bi fuel var lo hi body env).1 = false →
      denoteForLoop' bi' fuel var lo hi body env = denoteForLoop' bi fuel var lo hi body env)
    (motive8 := fun fuel c b => callsOK ok c = true → callsOK ok b = true → ∀ env,
      isErr (denoteWhileOrig' bi fuel c b env).1 = false →
      denoteWhileOrig' bi' fuel c b env = denoteWhileOrig' bi fuel c b env)
    (motive9 := fun fuel var lo hi body => callsOK ok body = true → ∀ env,
      isErr (denoteForLoopRevOrig' bi fuel var lo hi body env).1 = false →
      denoteForLoopRevOrig' bi' fuel var lo hi body env =
        denoteForLoopRevOrig' bi fuel var lo hi body env)
    (motive10 := fun fuel var lo hi body => callsOK ok body = true → ∀ env,
      isErr (denoteForLoopOrig' bi fuel var lo hi body env).1 = false →
      denoteForLoopOrig' bi' fuel var lo hi body env =
        denoteForLoopOrig' bi fuel var lo hi body env)
    (motive11 := fun fuel v arms => callsOK.callsOKArms ok arms = true → ∀ env,
      isErr (denoteMatchArms' bi fuel v arms env).1 = false →
      denoteMatchArms' bi' fuel v arms env = denoteMatchArms' bi fuel v arms env)
    (motive12 := fun fuel args => callsOK.callsOKList ok args = true → ∀ env,
      (denoteArgs' bi fuel args env).1.isSome = true →
      denoteArgs' bi' fuel args env = denoteArgs' bi fuel args env)
    (motive13 := fun fuel f args => ok f = true → callsOK.callsOKList ok args = true → ∀ env,
      isErr (denoteApp' bi fuel f args env).1 = false →
      denoteApp' bi' fuel f args env = denoteApp' bi fuel f args env)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_).1 fuel e
  -- lit
  · intros; simp only [denote']
  -- var
  · intros; simp only [denote']
  -- letBind
  · intro fuel n val body ih1 ih2 hc env hd
    simp only [callsOK, Bool.and_eq_true] at hc
    rcases hr : denote' bi fuel val env with ⟨o, s⟩
    have h1 : denote' bi' fuel val env = denote' bi fuel val env := by
      refine ih1 hc.1 env ?_
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case controlFlow => rfl
      all_goals
        simp only [stateM_bind_apply, stateM_modify_apply]
        refine ih2 hc.2 _ ?_
        simpa [denote', stateM_bind_apply, hr, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure] using hd
    | _ => rfl
  -- lam
  · intros; simp only [denote']
  -- app
  · intro fuel f args
    transparent_case
  -- tuple
  · intro fuel elems ih hc env hd
    simp only [callsOK] at hc
    rcases hr : denoteArgs' bi fuel elems env with ⟨o, s⟩
    have h1 : denoteArgs' bi' fuel elems env = denoteArgs' bi fuel elems env := by
      refine ih hc env ?_
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1]
  -- proj
  · intro fuel e i
    strict_child_case
  -- ifThenElse
  · intro fuel c t e ihc iht ihe hc env hd
    simp only [callsOK, Bool.and_eq_true] at hc
    rcases hr : denote' bi fuel c env with ⟨o, s⟩
    have h1 : denote' bi' fuel c env = denote' bi fuel c env := by
      refine ihc hc.1.1 env ?_
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case bool b =>
        cases b
        · refine ihe hc.2 s ?_
          simpa [denote', stateM_bind_apply, hr] using hd
        · refine iht hc.1.2 s ?_
          simpa [denote', stateM_bind_apply, hr] using hd
      all_goals rfl
    | _ => rfl
  -- match_
  · intro fuel scrut arms ihs iha hc env hd
    simp only [callsOK, Bool.and_eq_true] at hc
    rcases hr : denote' bi fuel scrut env with ⟨o, s⟩
    have h1 : denote' bi' fuel scrut env = denote' bi fuel scrut env := by
      refine ihs hc.1 env ?_
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case controlFlow => rfl
      all_goals
        refine iha _ hc.2 s ?_
        simpa [denote', stateM_bind_apply, hr] using hd
    | _ => rfl
  -- unitVal
  · intros; simp only [denote']
  -- seq
  · intro fuel e1 e2 ih1 ih2 hc env hd
    simp only [callsOK, Bool.and_eq_true] at hc
    rcases hr : denote' bi fuel e1 env with ⟨o, s⟩
    have h1 : denote' bi' fuel e1 env = denote' bi fuel e1 env := by
      refine ih1 hc.1 env ?_
      cases o <;> simp_all [denote', stateM_bind_apply, pure, StateT.pure]
    simp only [denote', stateM_bind_apply, h1, hr]
    cases o with
    | val v =>
      cases v
      case controlFlow => rfl
      all_goals
        refine ih2 hc.2 s ?_
        simpa [denote', stateM_bind_apply, hr] using hd
    | _ => rfl
  -- borrow
  · intro fuel e
    transparent_case
  -- deref
  · intro fuel e
    transparent_case
  -- assign
  · intro fuel n e
    strict_child_case
  -- forLoop
  · bounded_loop_case
  -- forLoopRev
  · bounded_loop_case
  -- whileLoop
  · intro fuel c b
    transparent_case
  -- break_ (some e)
  · intro fuel e
    strict_child_case
  -- break_ none
  · intros; simp only [denote']
  -- continue_
  · intros; simp only [denote']
  -- earlyReturn
  · intro fuel e
    strict_child_case
  -- questionMark
  · intro fuel e
    strict_child_case
  -- forFold
  · bounded_loop_case
  -- forFoldRev
  · bounded_loop_case
  -- whileFold
  · intro fuel c b
    transparent_case
  -- forFoldReturn
  · bounded_loop_case
  -- forFoldRevReturn
  · bounded_loop_case
  -- whileFoldReturn
  · intro fuel c b
    transparent_case
  -- cfBreak
  · intro fuel e
    strict_child_case
  -- cfContinue
  · intro fuel e
    strict_child_case
  -- cfBreakContinue
  · intro fuel e
    strict_child_case
  -- typeAscription
  · intro fuel e tyStr
    transparent_case
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
  · intro fuel v pat body rest ihb ihr hc env hd
    simp only [callsOK.callsOKArms, Bool.and_eq_true] at hc
    simp only [denoteMatchArms', stateM_bind_apply, stateM_get_apply] at hd ⊢
    cases hm : matchPat pat v env with
    | none =>
      simp only [hm] at hd ⊢
      exact ihr hc.2 env hd
    | some env' =>
      simp only [hm, stateM_bind_apply, stateM_set_apply] at hd ⊢
      exact ihb hc.1 env' hd
  -- denoteArgs' []
  · intros; simp only [denoteArgs']
  -- denoteArgs' (e :: es)
  · intro fuel e es ihe ihr hc env hd
    simp only [callsOK.callsOKList, Bool.and_eq_true] at hc
    rcases hr : denote' bi fuel e env with ⟨o, s⟩
    have h1 : denote' bi' fuel e env = denote' bi fuel e env := by
      refine ihe hc.1 env ?_
      rcases o with (v|v|v|_|m) <;> simp_all [denoteArgs', stateM_bind_apply, pure, StateT.pure]
    simp only [denoteArgs', stateM_bind_apply, h1, hr] at hd ⊢
    rcases o with (v|v|v|_|m)
    all_goals try rfl
    cases v
    case controlFlow => rfl
    all_goals
      simp only [stateM_bind_apply] at hd ⊢
      rw [ihr hc.2 s (by simpa [pure, StateT.pure] using hd)]
  -- denoteApp'
  · intro fuel f args ih hf hc env hd
    simp only [denoteApp', stateM_bind_apply] at hd ⊢
    rcases hr : denoteArgs' bi fuel args env with ⟨o, s⟩
    have h1 : denoteArgs' bi' fuel args env = denoteArgs' bi fuel args env := by
      refine ih hc env ?_
      rw [hr]
      cases o <;> simp_all [pure, StateT.pure]
    rw [h1, hr]
    rw [hr] at hd
    cases o with
    | none => rfl
    | some vals =>
      cases hb : bi f vals with
      | none => simp [hb, pure, StateT.pure] at hd
      | some r => simp only [hb, hsub f hf vals r hb]

/-- **Table inclusion.** Let `bi'` return the value `bi` returns wherever `bi` returns one
    on a name accepted by `ok`, and let every call of `e` be to such a name. A run of `e`
    under `bi` that does not end in an error is the run under `bi'`, outcome and
    environment, at the same fuel. -/
theorem denote'_eq_of_tableLE
    (hsub : ∀ f, ok f = true → ∀ args r, bi f args = some r → bi' f args = some r)
    {e : ImpExpr} (he : callsOK ok e = true) (fuel : Nat) (env : Env)
    (hne : isErr (denote' bi fuel e env).1 = false) :
    denote' bi' fuel e env = denote' bi fuel e env :=
  denote'_tableLE_aux hsub fuel e he env hne

/-- A run under `bi` that returns a value returns the same value and environment under
    every table `bi'` that includes `bi` on the accepted names. -/
theorem denote'_mono
    (hsub : ∀ f, ok f = true → ∀ args r, bi f args = some r → bi' f args = some r)
    {e : ImpExpr} (he : callsOK ok e = true) (fuel : Nat) (env : Env) (v : Value) (env' : Env)
    (h : denote' bi fuel e env = (.val v, env')) : denote' bi' fuel e env = (.val v, env') := by
  rw [denote'_eq_of_tableLE hsub he fuel env (by rw [h]; rfl), h]

/-- A function correspondence under the larger table `bi'` fixes every value a run under
    the smaller table `bi` returns, at any fuel: the run is the run under `bi'`, which is
    stable under more fuel. -/
theorem fnCorres_val_of_sub
    (hsub : ∀ f, ok f = true → ∀ args r, bi f args = some r → bi' f args = some r)
    {e : ImpExpr} (he : callsOK ok e = true) {A β : Type} [HaxEnc β] {entry : A → Env}
    {G : A → Prop} {g : A → β} (h : FnCorres bi' e entry G g) (a : A) (hG : G a)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : denote' bi fuel e (entry a) = (.val v, env')) : v = HaxEnc.enc (g a) := by
  obtain ⟨f₀, hr⟩ := h a hG
  have h' := denote'_mono hsub he fuel (entry a) v env' hrun
  have hm := denote'_val_mono bi' (fuel' := max fuel f₀) (by rw [h']) (Nat.le_max_left fuel f₀)
  have := hr (max fuel f₀) (Nat.le_max_right fuel f₀)
  rw [hm, h'] at this
  exact Outcome.val.inj this

end TableLE

end Hax.Ascent
