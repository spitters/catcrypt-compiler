/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.CorresCore

/-!
# The eventual semantics of `denote'`

`Eval bi e env v env'` holds when, from some fuel on, the run of `e` from `env` is
`(.val v, env')`. It is deterministic (`Eval_det`) and its value is `haxEval`
(`Eval.haxEval_eq`). Fuel occurs only in the definition and in the equations below; a
statement over `Eval` carries no fuel bound.

## Main results

* `EvRun`, `bindCF`, `evRun_bindCF_iff` — the eventual run of a construct that runs one
  subexpression and passes a plain value to a continuation; every such constructor of
  `denote'` is a `bindCF` (`denote'_seq_bindCF`, ...)
* `Eval_lit_iff`, `Eval_unitVal_iff`, `Eval_var_iff`, `Eval_seq_iff`, `Eval_letBind_iff`,
  `Eval_assign_iff`, `Eval_ifThenElse_iff`, `Eval_proj_iff`, `Eval_cfBreak_iff`,
  `Eval_cfContinue_iff`, `Eval_app_iff`, `Eval_tuple_iff`, `Eval_borrow_iff`,
  `Eval_deref_iff`, `Eval_typeAscription_iff`, `EvalArgs_nil_iff`, `EvalArgs_cons_iff` —
  fuel-free equations of the eventual semantics
* `Eval_forFold_intro`, `Eval_forFold_lo_cf`, `Eval_forFold_hi_cf`, `EvalLoop_done`,
  `EvalLoop_break`, `EvalLoop_next` — introduction rules for the counted loop
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## Eventual runs -/

/-- The fuel-indexed computation `r` eventually returns the value `v` in the environment
    `env'`: from some fuel on, every run is `(.val v, env')`. -/
def EvRun (r : Nat → Outcome × Env) (v : Value) (env' : Env) : Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → r fuel = (.val v, env')

/-- An eventual run of a computation that does not depend on the fuel is its run. -/
theorem evRun_const {p : Outcome × Env} {v : Value} {env' : Env} :
    EvRun (fun _ => p) v env' ↔ p = (.val v, env') :=
  ⟨fun ⟨_, h⟩ => h _ (Nat.le_refl _), fun h => ⟨0, fun _ _ => h⟩⟩

/-- The sequencing of `denote'`: a control-flow value of the first run is the outcome, a
    plain value is passed to the continuation `k`, and any other outcome is the
    outcome. -/
def bindCF (r : Outcome × Env) (k : Value → Env → Outcome × Env) : Outcome × Env :=
  match r with
  | (.val (.controlFlow b u), s) => (.val (.controlFlow b u), s)
  | (.val w, s) => k w s
  | (o, s) => (o, s)

/-- A value outcome of `bindCF p k` is a control-flow value of `p`, or the value outcome
    of the continuation at a plain value of `p`. -/
theorem bindCF_eq_val {p : Outcome × Env} {k : Value → Env → Outcome × Env} {v : Value}
    {env' : Env} :
    bindCF p k = (.val v, env') ↔ ∃ w s, p = (.val w, s) ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ k w s = (.val v, env'))) := by
  constructor
  · intro h
    rcases p with ⟨o, s⟩
    rcases o with (w|w|w|_|m)
    · refine ⟨w, s, rfl, ?_⟩
      cases w
      case controlFlow c u =>
        cases h
        exact Or.inl ⟨rfl, rfl, rfl⟩
      all_goals exact Or.inr ⟨rfl, h⟩
    all_goals cases h
  · rintro ⟨w, s, rfl, ⟨hc, hv, hs⟩ | ⟨hc, h⟩⟩
    · rw [hv, hs]; cases w <;> first | rfl | simp at hc
    · cases w <;> first | exact h | simp at hc

/-- **Eventual runs of a `bindCF`.** When the first run is stable under more fuel once
    it is a value, the eventual run of `bindCF (r₁ fuel) (k fuel)` is a control-flow
    value of the eventual run of `r₁`, or the eventual run of the continuation at a plain
    value of `r₁`. -/
theorem evRun_bindCF_iff {r₁ r : Nat → Outcome × Env} {k : Nat → Value → Env → Outcome × Env}
    (hr : ∀ f, r f = bindCF (r₁ f) (k f))
    (hmono : ∀ f f' w s, f ≤ f' → r₁ f = (.val w, s) → r₁ f' = (.val w, s))
    {v : Value} {env' : Env} :
    EvRun r v env' ↔ ∃ w s, EvRun r₁ w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ EvRun (fun f => k f w s) v env')) := by
  constructor
  · rintro ⟨f₀, h⟩
    obtain ⟨w, s, h₀, hc⟩ := bindCF_eq_val.mp ((hr f₀).symm.trans (h f₀ (Nat.le_refl _)))
    refine ⟨w, s, ⟨f₀, fun f hf => hmono f₀ f w s hf h₀⟩, ?_⟩
    rcases hc with hc | ⟨hc, -⟩
    · exact Or.inl hc
    · refine Or.inr ⟨hc, f₀, fun f hf => ?_⟩
      obtain ⟨w', s', h₁, hc'⟩ := bindCF_eq_val.mp ((hr f).symm.trans (h f hf))
      obtain ⟨hw, hs⟩ := Prod.mk.inj ((hmono f₀ f w s hf h₀).symm.trans h₁)
      cases Outcome.val.inj hw
      cases hs
      rcases hc' with ⟨hc', -⟩ | ⟨-, hk⟩
      · rw [hc] at hc'; cases hc'
      · exact hk
  · rintro ⟨w, s, ⟨f₁, h₁⟩, hc⟩
    rcases hc with hc | ⟨hc, f₂, h₂⟩
    · exact ⟨f₁, fun f hf => by rw [hr f]; exact bindCF_eq_val.mpr ⟨w, s, h₁ f hf, Or.inl hc⟩⟩
    · exact ⟨max f₁ f₂, fun f hf => by
        rw [hr f]
        exact bindCF_eq_val.mpr ⟨w, s, h₁ f (by omega), Or.inr ⟨hc, h₂ f (by omega)⟩⟩⟩

/-! ## The constructors of `denote'` as `bindCF` -/

section Steps

variable (bi : Builtins) (fuel : Nat)

theorem denote'_seq_bindCF (e1 e2 : ImpExpr) (env : Env) :
    denote' bi fuel (.seq e1 e2) env =
      bindCF (denote' bi fuel e1 env) (fun _ s => denote' bi fuel e2 s) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel e1 env with ⟨o, s⟩
  rcases o with (w|w|w|_|m) <;> try (cases w <;> rfl)
  all_goals rfl

theorem denote'_letBind_bindCF (x : String) (val body : ImpExpr) (env : Env) :
    denote' bi fuel (.letBind x val body) env =
      bindCF (denote' bi fuel val env) (fun w s => denote' bi fuel body (s.extend x w)) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel val env with ⟨o, s⟩
  rcases o with (w|w|w|_|m) <;> try (cases w <;> rfl)
  all_goals rfl

theorem denote'_assign_bindCF (x : String) (rhs : ImpExpr) (env : Env) :
    denote' bi fuel (.assign x rhs) env =
      bindCF (denote' bi fuel rhs env) (fun w s => (.val .unit, s.extend x w)) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel rhs env with ⟨o, s⟩
  rcases o with (w|w|w|_|m) <;> try (cases w <;> rfl)
  all_goals rfl

theorem denote'_ifThenElse_bindCF (c t e : ImpExpr) (env : Env) :
    denote' bi fuel (.ifThenElse c t e) env =
      bindCF (denote' bi fuel c env) (fun w s => match w with
        | .bool true => denote' bi fuel t s
        | .bool false => denote' bi fuel e s
        | _ => (.err "if condition not a bool", s)) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel c env with ⟨o, s⟩
  rcases o with (w|w|w|_|m) <;> try (cases w <;> try rfl)
  all_goals first | rfl | (rename_i b; cases b <;> rfl)

theorem denote'_proj_bindCF (e : ImpExpr) (i : Nat) (env : Env) :
    denote' bi fuel (.proj e i) env =
      bindCF (denote' bi fuel e env) (fun w s => match w.projIdx i with
        | some vi => (.val vi, s)
        | none => (.err s!"projection index {i} out of range", s)) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel e env with ⟨o, s⟩
  rcases o with (w|w|w|_|m)
  · rcases hp : w.projIdx i with _ | vi <;> cases w <;>
      first | rfl | (simp only [bindCF, hp]; rfl) | (simp only [bindCF, hp])
  all_goals rfl

theorem denote'_cfBreak_bindCF (e : ImpExpr) (env : Env) :
    denote' bi fuel (.cfBreak e) env =
      bindCF (denote' bi fuel e env) (fun w s => (.val (.controlFlow true w), s)) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel e env with ⟨o, s⟩
  rcases o with (w|w|w|_|m) <;> try (cases w <;> rfl)
  all_goals rfl

theorem denote'_cfContinue_bindCF (e : ImpExpr) (env : Env) :
    denote' bi fuel (.cfContinue e) env =
      bindCF (denote' bi fuel e env) (fun w s => (.val (.controlFlow false w), s)) := by
  simp only [denote', stateM_bind_apply]
  rcases denote' bi fuel e env with ⟨o, s⟩
  rcases o with (w|w|w|_|m) <;> try (cases w <;> rfl)
  all_goals rfl

/-- A value run of an argument list is the run at every larger fuel. -/
theorem denoteArgs'_val_mono {fuel' : Nat} {es : List ImpExpr} {env s : Env}
    {vs : List Value} (h : denoteArgs' bi fuel es env = (some vs, s)) (hle : fuel ≤ fuel') :
    denoteArgs' bi fuel' es env = (some vs, s) := by
  have ht := denote'_tuple bi fuel h
  have hm := denote'_val_mono bi (by rw [ht]) hle
  rw [ht] at hm
  simp only [denote', stateM_bind_apply] at hm
  rcases hr : denoteArgs' bi fuel' es env with ⟨o, s'⟩
  rw [hr] at hm
  rcases o with _ | vs'
  · cases hm
  · cases hm; rfl

theorem denoteArgs'_cons_eq {e : ImpExpr} {es : List ImpExpr} {env env' : Env}
    {vs : List Value} :
    denoteArgs' bi fuel (e :: es) env = (some vs, env') ↔
      ∃ w s ws, denote' bi fuel e env = (.val w, s) ∧ w.isControlFlow = false ∧
        denoteArgs' bi fuel es s = (some ws, env') ∧ vs = w :: ws := by
  constructor
  · intro h
    simp only [denoteArgs', stateM_bind_apply] at h
    rcases hr : denote' bi fuel e env with ⟨o, s⟩
    rw [hr] at h
    rcases o with (w|w|w|_|m)
    · cases w
      case controlFlow c u => cases h
      all_goals
        simp only [stateM_bind_apply] at h
        rcases hr2 : denoteArgs' bi fuel es s with ⟨o2, s2⟩
        rw [hr2] at h
        rcases o2 with _ | ws
        · cases h
        · cases h; exact ⟨_, s, ws, rfl, rfl, hr2, rfl⟩
    all_goals cases h
  · rintro ⟨w, s, ws, h, hc, hs, rfl⟩
    exact denoteArgs'_cons bi fuel h hc hs

theorem denote'_app_eq {g : String} {args : List ImpExpr} {env env' : Env} {v : Value} :
    denote' bi fuel (.app g args) env = (.val v, env') ↔
      ∃ vs, denoteArgs' bi fuel args env = (some vs, env') ∧ bi g vs = some v := by
  constructor
  · intro h
    simp only [denote', denoteApp', stateM_bind_apply] at h
    rcases hr : denoteArgs' bi fuel args env with ⟨o, s⟩
    rw [hr] at h
    rcases o with _ | vs
    · cases h
    · dsimp only at h
      rcases hb : bi g vs with _ | w
      · rw [hb] at h; cases h
      · rw [hb] at h; cases h; exact ⟨vs, rfl, hb⟩
  · rintro ⟨vs, h, hb⟩
    exact denote'_app bi fuel h hb

theorem denote'_tuple_eq {es : List ImpExpr} {env env' : Env} {v : Value} :
    denote' bi fuel (.tuple es) env = (.val v, env') ↔
      ∃ vs, denoteArgs' bi fuel es env = (some vs, env') ∧ v = .tuple vs := by
  constructor
  · intro h
    simp only [denote', stateM_bind_apply] at h
    rcases hr : denoteArgs' bi fuel es env with ⟨o, s⟩
    rw [hr] at h
    rcases o with _ | vs
    · cases h
    · cases h; exact ⟨vs, rfl, rfl⟩
  · rintro ⟨vs, h, rfl⟩
    exact denote'_tuple bi fuel h

theorem denote'_var_eq {x : String} {env env' : Env} {v : Value} :
    denote' bi fuel (.var x) env = (.val v, env') ↔ env x = some v ∧ env' = env := by
  simp only [denote', stateM_bind_apply, stateM_get_apply]
  rcases h : env x with _ | w
  · simp only [reduceCtorEq, false_and, iff_false]; exact fun h' => nomatch h'
  · constructor
    · intro h'; cases h'; exact ⟨rfl, rfl⟩
    · rintro ⟨hw, rfl⟩; cases hw; rfl

/-- A counted loop whose lower bound returns a control-flow value returns it. -/
theorem denote'_forFold_lo_cf {var : String} {lo hi body : ImpExpr} {env s : Env} {w : Value}
    (h : denote' bi fuel lo env = (.val w, s)) (hc : w.isControlFlow = true) :
    denote' bi fuel (.forFold var lo hi body) env = (.val w, s) := by
  simp only [denote', stateM_bind_apply, h]
  cases w <;> first | rfl | simp at hc

/-- A counted loop whose upper bound returns a control-flow value returns it. -/
theorem denote'_forFold_hi_cf {var : String} {lo hi body : ImpExpr} {env s1 s2 : Env} {a : Int}
    {w : Value} (hlo : denote' bi fuel lo env = (.val (.int a), s1))
    (hhi : denote' bi fuel hi s1 = (.val w, s2)) (hc : w.isControlFlow = true) :
    denote' bi fuel (.forFold var lo hi body) env = (.val w, s2) := by
  simp only [denote', stateM_bind_apply, hlo, hhi]
  cases w <;> first | rfl | simp at hc

end Steps

/-! ## The eventual semantics -/

section Eval

variable (bi : Builtins)

/-- **The eventual semantics of `denote'`.** From some fuel on, the run of `e` from `env`
    is `(.val v, env')`. -/
def Eval (e : ImpExpr) (env : Env) (v : Value) (env' : Env) : Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → denote' bi fuel e env = (.val v, env')

/-- The eventual semantics of an argument list: from some fuel on, `denoteArgs'` returns
    the values `vs` in the environment `env'`. -/
def EvalArgs (es : List ImpExpr) (env : Env) (vs : List Value) (env' : Env) : Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → denoteArgs' bi fuel es env = (some vs, env')

/-- The eventual semantics of the counted-loop helper `denoteForLoop'`. -/
def EvalLoop (var : String) (a b : Int) (body : ImpExpr) (env : Env) (v : Value)
    (env' : Env) : Prop :=
  ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → denoteForLoop' bi fuel var a b body env = (.val v, env')

variable {bi}

theorem eval_iff_evRun {e : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi e env v env' ↔ EvRun (fun fuel => denote' bi fuel e env) v env' := Iff.rfl

/-- A value run of `denote'` at one fuel is the run at every larger fuel. -/
theorem denote'_run_mono {e : ImpExpr} {env : Env} :
    ∀ f f' w s, f ≤ f' → denote' bi f e env = (.val w, s) →
      denote' bi f' e env = (.val w, s) :=
  fun _ _ _ _ hle h => (denote'_val_mono bi (by rw [h]) hle).trans h

/-- A value run at one fuel is the eventual run. -/
theorem Eval.of_run {e : ImpExpr} {env env' : Env} {v : Value} {fuel : Nat}
    (h : denote' bi fuel e env = (.val v, env')) : Eval bi e env v env' :=
  ⟨fuel, fun f hf => denote'_run_mono fuel f v env' hf h⟩

/-- The eventual semantics is deterministic. -/
theorem Eval_det {e : ImpExpr} {env env₁ env₂ : Env} {v₁ v₂ : Value}
    (h₁ : Eval bi e env v₁ env₁) (h₂ : Eval bi e env v₂ env₂) : v₁ = v₂ ∧ env₁ = env₂ := by
  obtain ⟨f₁, r₁⟩ := h₁
  obtain ⟨f₂, r₂⟩ := h₂
  obtain ⟨h, h'⟩ :=
    Prod.mk.inj ((r₁ (max f₁ f₂) (by omega)).symm.trans (r₂ (max f₁ f₂) (by omega)))
  exact ⟨Outcome.val.inj h, h'⟩

/-- The eventual value `haxEval` is the value of the eventual semantics. -/
theorem Eval.haxEval_eq {e : ImpExpr} {env env' : Env} {v : Value}
    (h : Eval bi e env v env') : haxEval bi e env = some v := by
  obtain ⟨f₀, r⟩ := h
  exact Hax.Ascent.haxEval_eq (fuel₀ := f₀) fun f hf => by rw [r f hf]

/-- A value run of an argument list at one fuel is the eventual run. -/
theorem EvalArgs.of_run {es : List ImpExpr} {env env' : Env} {vs : List Value} {fuel : Nat}
    (h : denoteArgs' bi fuel es env = (some vs, env')) : EvalArgs bi es env vs env' :=
  ⟨fuel, fun _ hf => denoteArgs'_val_mono bi fuel h hf⟩

theorem EvalArgs_det {es : List ImpExpr} {env env₁ env₂ : Env} {vs₁ vs₂ : List Value}
    (h₁ : EvalArgs bi es env vs₁ env₁) (h₂ : EvalArgs bi es env vs₂ env₂) :
    vs₁ = vs₂ ∧ env₁ = env₂ := by
  obtain ⟨f₁, r₁⟩ := h₁
  obtain ⟨f₂, r₂⟩ := h₂
  obtain ⟨h, h'⟩ :=
    Prod.mk.inj ((r₁ (max f₁ f₂) (by omega)).symm.trans (r₂ (max f₁ f₂) (by omega)))
  exact ⟨Option.some.inj h, h'⟩

/-! ### Equations of the eventual semantics -/

theorem Eval_lit_iff {l : ImpLit} {env env' : Env} {v : Value} :
    Eval bi (.lit l) env v env' ↔ v = Value.ofLit l ∧ env' = env := by
  rw [eval_iff_evRun]
  simp only [denote'_lit, evRun_const, Prod.mk.injEq, Outcome.val.injEq]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩

theorem Eval_unitVal_iff {env env' : Env} {v : Value} :
    Eval bi .unitVal env v env' ↔ v = .unit ∧ env' = env := by
  rw [eval_iff_evRun]
  simp only [denote'_unitVal, evRun_const, Prod.mk.injEq, Outcome.val.injEq]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩

theorem Eval_var_iff {x : String} {env env' : Env} {v : Value} :
    Eval bi (.var x) env v env' ↔ env x = some v ∧ env' = env :=
  ⟨fun ⟨_, h⟩ => (denote'_var_eq bi _).mp (h _ (Nat.le_refl _)),
   fun h => ⟨0, fun _ _ => (denote'_var_eq bi _).mpr h⟩⟩

theorem Eval_borrow_iff {e : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.borrow e) env v env' ↔ Eval bi e env v env' := by
  simp only [Eval, denote'_borrow]

theorem Eval_deref_iff {e : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.deref e) env v env' ↔ Eval bi e env v env' := by
  simp only [Eval, denote'_deref]

theorem Eval_typeAscription_iff {e : ImpExpr} {ty : String} {env env' : Env} {v : Value} :
    Eval bi (.typeAscription e ty) env v env' ↔ Eval bi e env v env' := by
  simp only [Eval, denote'_typeAscription]

/-- **Sequence.** A control-flow value of the first expression is the outcome; a plain
    value continues with the second expression from its exit environment. -/
theorem Eval_seq_iff {e1 e2 : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.seq e1 e2) env v env' ↔ ∃ w s, Eval bi e1 env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ Eval bi e2 s v env')) :=
  evRun_bindCF_iff (fun f => denote'_seq_bindCF bi f e1 e2 env) denote'_run_mono

/-- **`let`.** A control-flow value of the bound expression is the outcome; a plain value
    is bound at the name and the body runs. -/
theorem Eval_letBind_iff {x : String} {val body : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.letBind x val body) env v env' ↔ ∃ w s, Eval bi val env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ Eval bi body (s.extend x w) v env')) :=
  evRun_bindCF_iff (fun f => denote'_letBind_bindCF bi f x val body env) denote'_run_mono

theorem Eval_assign_iff {x : String} {rhs : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.assign x rhs) env v env' ↔ ∃ w s, Eval bi rhs env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ v = .unit ∧ env' = s.extend x w)) := by
  rw [eval_iff_evRun, evRun_bindCF_iff (fun f => denote'_assign_bindCF bi f x rhs env)
    denote'_run_mono]
  simp only [evRun_const, Prod.mk.injEq, Outcome.val.injEq]
  constructor
  · rintro ⟨w, s, h, hc | ⟨hc, h₁, h₂⟩⟩
    · exact ⟨w, s, h, Or.inl hc⟩
    · exact ⟨w, s, h, Or.inr ⟨hc, h₁.symm, h₂.symm⟩⟩
  · rintro ⟨w, s, h, hc | ⟨hc, h₁, h₂⟩⟩
    · exact ⟨w, s, h, Or.inl hc⟩
    · exact ⟨w, s, h, Or.inr ⟨hc, h₁.symm, h₂.symm⟩⟩

/-- **Conditional.** A control-flow value of the condition is the outcome; `.bool true`
    and `.bool false` select the branch. -/
theorem Eval_ifThenElse_iff {c t e : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.ifThenElse c t e) env v env' ↔ ∃ w s, Eval bi c env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w = .bool true ∧ Eval bi t s v env') ∨ (w = .bool false ∧ Eval bi e s v env')) := by
  rw [eval_iff_evRun, evRun_bindCF_iff (fun f => denote'_ifThenElse_bindCF bi f c t e env)
    denote'_run_mono]
  refine exists_congr fun w => exists_congr fun s => and_congr_right fun _h => ?_
  cases w
  case bool b =>
    cases b
    · simp only [Value.isControlFlow_bool, Bool.false_eq_true, false_and, true_and, false_or,
        Value.bool.injEq]
      exact Iff.rfl
    · simp only [Value.isControlFlow_bool, Bool.false_eq_true, false_and, true_and, false_or,
        reduceCtorEq, Value.bool.injEq, or_false]
      exact Iff.rfl
  case controlFlow b u =>
    simp only [Value.isControlFlow_controlFlow, true_and, Bool.true_eq_false, false_and,
      reduceCtorEq, or_false]
  all_goals
    simp only [reduceCtorEq, false_and, or_false, evRun_const]
    constructor
    · rintro (⟨hc, -⟩ | ⟨-, h⟩)
      · simp at hc
      · cases h
    · rintro ⟨hc, -⟩; simp at hc

theorem Eval_proj_iff {e : ImpExpr} {i : Nat} {env env' : Env} {v : Value} :
    Eval bi (.proj e i) env v env' ↔ ∃ w s, Eval bi e env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ w.projIdx i = some v ∧ env' = s)) := by
  rw [eval_iff_evRun, evRun_bindCF_iff (fun f => denote'_proj_bindCF bi f e i env)
    denote'_run_mono]
  refine exists_congr fun w => exists_congr fun s => and_congr_right fun _ =>
    or_congr Iff.rfl (and_congr_right fun _ => ?_)
  rw [evRun_const]
  rcases w.projIdx i with _ | u
  · exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
  · constructor
    · intro h; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨h, rfl⟩; cases h; rfl

theorem Eval_cfBreak_iff {e : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.cfBreak e) env v env' ↔ ∃ w s, Eval bi e env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ v = .controlFlow true w ∧ env' = s)) := by
  rw [eval_iff_evRun, evRun_bindCF_iff (fun f => denote'_cfBreak_bindCF bi f e env)
    denote'_run_mono]
  simp only [evRun_const, Prod.mk.injEq, Outcome.val.injEq]
  constructor
  · rintro ⟨w, s, h, hc | ⟨hc, h₁, h₂⟩⟩
    · exact ⟨w, s, h, Or.inl hc⟩
    · exact ⟨w, s, h, Or.inr ⟨hc, h₁.symm, h₂.symm⟩⟩
  · rintro ⟨w, s, h, hc | ⟨hc, h₁, h₂⟩⟩
    · exact ⟨w, s, h, Or.inl hc⟩
    · exact ⟨w, s, h, Or.inr ⟨hc, h₁.symm, h₂.symm⟩⟩

theorem Eval_cfContinue_iff {e : ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.cfContinue e) env v env' ↔ ∃ w s, Eval bi e env w s ∧
      ((w.isControlFlow = true ∧ v = w ∧ env' = s) ∨
       (w.isControlFlow = false ∧ v = .controlFlow false w ∧ env' = s)) := by
  rw [eval_iff_evRun, evRun_bindCF_iff (fun f => denote'_cfContinue_bindCF bi f e env)
    denote'_run_mono]
  simp only [evRun_const, Prod.mk.injEq, Outcome.val.injEq]
  constructor
  · rintro ⟨w, s, h, hc | ⟨hc, h₁, h₂⟩⟩
    · exact ⟨w, s, h, Or.inl hc⟩
    · exact ⟨w, s, h, Or.inr ⟨hc, h₁.symm, h₂.symm⟩⟩
  · rintro ⟨w, s, h, hc | ⟨hc, h₁, h₂⟩⟩
    · exact ⟨w, s, h, Or.inl hc⟩
    · exact ⟨w, s, h, Or.inr ⟨hc, h₁.symm, h₂.symm⟩⟩

theorem EvalArgs_nil_iff {env env' : Env} {vs : List Value} :
    EvalArgs bi [] env vs env' ↔ vs = [] ∧ env' = env := by
  constructor
  · rintro ⟨f, h⟩
    have h' := (denoteArgs'_nil bi f env).symm.trans (h f (Nat.le_refl _))
    cases h'; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, h⟩
    exact ⟨0, fun f _ => by rw [h]; exact denoteArgs'_nil bi f env⟩

/-- **Argument list.** The head returns a plain value, the tail runs from its exit
    environment. -/
theorem EvalArgs_cons_iff {e : ImpExpr} {es : List ImpExpr} {env env' : Env}
    {vs : List Value} :
    EvalArgs bi (e :: es) env vs env' ↔ ∃ w s ws, Eval bi e env w s ∧
      w.isControlFlow = false ∧ EvalArgs bi es s ws env' ∧ vs = w :: ws := by
  constructor
  · rintro ⟨f₀, h⟩
    obtain ⟨w, s, ws, h₀, hc, ht, rfl⟩ := (denoteArgs'_cons_eq bi f₀).mp (h f₀ (Nat.le_refl _))
    refine ⟨w, s, ws, Eval.of_run h₀, hc, ⟨f₀, fun f hf => ?_⟩, rfl⟩
    obtain ⟨w', s', ws', h₁, -, ht', hvs⟩ := (denoteArgs'_cons_eq bi f).mp (h f hf)
    obtain ⟨hw, hs⟩ := Prod.mk.inj ((denote'_run_mono f₀ f w s hf h₀).symm.trans h₁)
    cases Outcome.val.inj hw
    cases hs
    cases (List.cons.inj hvs).2
    exact ht'
  · rintro ⟨w, s, ws, ⟨f₁, h₁⟩, hc, ⟨f₂, h₂⟩, rfl⟩
    exact ⟨max f₁ f₂, fun f hf => (denoteArgs'_cons_eq bi f).mpr
      ⟨w, s, ws, h₁ f (by omega), hc, h₂ f (by omega), rfl⟩⟩

/-- **Call.** The arguments return `vs` and the builtin table maps them to the value. -/
theorem Eval_app_iff {g : String} {args : List ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.app g args) env v env' ↔ ∃ vs, EvalArgs bi args env vs env' ∧ bi g vs = some v := by
  constructor
  · rintro ⟨f₀, h⟩
    obtain ⟨vs, h₀, hb⟩ := (denote'_app_eq bi f₀).mp (h f₀ (Nat.le_refl _))
    exact ⟨vs, EvalArgs.of_run h₀, hb⟩
  · rintro ⟨vs, ⟨f₀, h⟩, hb⟩
    exact ⟨f₀, fun f hf => (denote'_app_eq bi f).mpr ⟨vs, h f hf, hb⟩⟩

theorem Eval_tuple_iff {es : List ImpExpr} {env env' : Env} {v : Value} :
    Eval bi (.tuple es) env v env' ↔ ∃ vs, EvalArgs bi es env vs env' ∧ v = .tuple vs := by
  constructor
  · rintro ⟨f₀, h⟩
    obtain ⟨vs, h₀, hv⟩ := (denote'_tuple_eq bi f₀).mp (h f₀ (Nat.le_refl _))
    exact ⟨vs, EvalArgs.of_run h₀, hv⟩
  · rintro ⟨vs, ⟨f₀, h⟩, hv⟩
    exact ⟨f₀, fun f hf => (denote'_tuple_eq bi f).mpr ⟨vs, h f hf, hv⟩⟩

/-! ### Counted loops (introduction rules) -/

/-- A counted loop whose lower bound returns a control-flow value returns it. -/
theorem Eval_forFold_lo_cf {var : String} {lo hi body : ImpExpr} {env s : Env} {w : Value}
    (h : Eval bi lo env w s) (hc : w.isControlFlow = true) :
    Eval bi (.forFold var lo hi body) env w s :=
  let ⟨f₀, r⟩ := h
  ⟨f₀, fun f hf => denote'_forFold_lo_cf bi f (r f hf) hc⟩

/-- A counted loop whose upper bound returns a control-flow value returns it. -/
theorem Eval_forFold_hi_cf {var : String} {lo hi body : ImpExpr} {env s1 s2 : Env} {a : Int}
    {w : Value} (hlo : Eval bi lo env (.int a) s1) (hhi : Eval bi hi s1 w s2)
    (hc : w.isControlFlow = true) : Eval bi (.forFold var lo hi body) env w s2 :=
  let ⟨f₁, r₁⟩ := hlo
  let ⟨f₂, r₂⟩ := hhi
  ⟨max f₁ f₂, fun f hf => denote'_forFold_hi_cf bi f (r₁ f (by omega)) (r₂ f (by omega)) hc⟩

/-- A counted loop with integer bounds runs the loop helper. -/
theorem Eval_forFold_intro {var : String} {lo hi body : ImpExpr} {env s1 s2 env' : Env}
    {a b : Int} {v : Value} (hlo : Eval bi lo env (.int a) s1) (hhi : Eval bi hi s1 (.int b) s2)
    (hl : EvalLoop bi var a b body s2 v env') : Eval bi (.forFold var lo hi body) env v env' :=
  let ⟨f₁, r₁⟩ := hlo
  let ⟨f₂, r₂⟩ := hhi
  let ⟨f₃, r₃⟩ := hl
  ⟨max f₁ (max f₂ f₃), fun f hf => by
    rw [denote'_forFold bi f (r₁ f (by omega)) (r₂ f (by omega))]
    exact r₃ f (by omega)⟩

theorem EvalLoop_done (var : String) {a b : Int} (body : ImpExpr) (env : Env) (h : a ≥ b) :
    EvalLoop bi var a b body env .unit env :=
  ⟨0, fun f _ => denoteForLoop'_done bi f var body env h⟩

/-- A body that returns `controlFlow true w` ends the loop with `w`. -/
theorem EvalLoop_break (var : String) {a b : Int} {body : ImpExpr} {env s : Env} {w : Value}
    (hab : a < b) (h : Eval bi body (env.extend var (.int a)) (.controlFlow true w) s) :
    EvalLoop bi var a b body env w s :=
  let ⟨f₀, r⟩ := h
  ⟨f₀ + 1, fun f hf => denoteForLoop'_break bi f var hab (by omega) (r f (by omega))⟩

/-- A body that returns any other value continues at the next index. -/
theorem EvalLoop_next (var : String) {a b : Int} {body : ImpExpr} {env s env' : Env}
    {v v' : Value} (hab : a < b) (h : Eval bi body (env.extend var (.int a)) v s)
    (hv : ∀ w, v ≠ .controlFlow true w) (hl : EvalLoop bi var (a + 1) b body s v' env') :
    EvalLoop bi var a b body env v' env' :=
  let ⟨f₁, r₁⟩ := h
  let ⟨f₂, r₂⟩ := hl
  ⟨max f₁ f₂ + 1, fun f hf => by
    rw [denoteForLoop'_next bi f var hab (by omega) (r₁ f (by omega)) hv]
    exact r₂ (f - 1) (by omega)⟩

end Eval

end Hax.Ascent
