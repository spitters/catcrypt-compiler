/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Fuel

/-!
# The correspondence judgment and the one-step equations of `denote'`

The one-step equations of `denote'` at a fixed fuel (`denote'_lit`, `denote'_seq`,
`denoteForLoop'_next`, ...), the correspondence judgment `Corres` and its argument-list
form `CorresArgs`, and the eventual value `haxEval` of a run. The eventual semantics
(`HaxAscent/Ascent/Eval.lean`) and the weakest precondition
(`HaxAscent/Ascent/Wp.lean`) are stated over these; the rules of `Corres` are in
`HaxAscent/Ascent/Corres.lean`.

`Corres bi P G e V Q` relates the post-pipeline program `e`, run by `denote' bi`, to a
shallow description over an abstract state `σ : S`: from `P env σ` and `G σ` there are
a fuel `fuel₀` and an environment `env'` with `Q env' σ` such that at every
`fuel ≥ fuel₀` the run is `(.val (V σ), env')`.

## Main definitions

* `Corres`, `CorresArgs`: the correspondence of an expression, and of an argument list,
  with a shallow description over an abstract state.
* `haxEval`: the eventual value of a run.

## Main results

* `denote'_lit`, `denote'_seq`, `denote'_letBind`, `denote'_ifThenElse`, `denote'_app`,
  `denote'_forFold`, `denoteForLoop'_done`, `denoteForLoop'_break`,
  `denoteForLoop'_next`: the one-step equations of `denote'` at a fixed fuel.
* `haxEval_eq`: a value returned from some fuel on is the eventual value.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## One-step equations of `denote'` -/

section Steps

variable (bi : Builtins) (fuel : Nat)

theorem denote'_lit (l : ImpLit) (env : Env) :
    denote' bi fuel (.lit l) env = (.val (Value.ofLit l), env) := by
  simp only [denote']; rfl

theorem denote'_unitVal (env : Env) : denote' bi fuel .unitVal env = (.val .unit, env) := by
  simp only [denote']; rfl

theorem denote'_var {x : String} {env : Env} {v : Value} (h : env x = some v) :
    denote' bi fuel (.var x) env = (.val v, env) := by
  simp only [denote', stateM_bind_apply, stateM_get_apply, h]; rfl

theorem denote'_letBind {x : String} {val body : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel val env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.letBind x val body) env = denote' bi fuel body (s.extend x v) := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | rfl | simp at hv

/-- The right-hand side's value is bound at the name, and the assignment itself
    returns `.unit`. -/
theorem denote'_assign {x : String} {rhs : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel rhs env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.assign x rhs) env = (.val .unit, s.extend x v) := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | rfl | simp at hv

theorem denote'_seq {e1 e2 : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel e1 env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.seq e1 e2) env = denote' bi fuel e2 s := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | rfl | simp at hv

theorem denote'_ifThenElse {c t e : ImpExpr} {env s : Env} {b : Bool}
    (h : denote' bi fuel c env = (.val (.bool b), s)) :
    denote' bi fuel (.ifThenElse c t e) env = denote' bi fuel (if b then t else e) s := by
  simp only [denote', stateM_bind_apply, h]
  cases b <;> rfl

theorem denote'_proj {e : ImpExpr} {i : Nat} {env s : Env} {v w : Value}
    (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false)
    (hp : v.projIdx i = some w) :
    denote' bi fuel (.proj e i) env = (.val w, s) := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | (simp only at hp ⊢; simp [hp]; rfl) | simp at hv

theorem denote'_borrow (e : ImpExpr) (env : Env) :
    denote' bi fuel (.borrow e) env = denote' bi fuel e env := by
  simp only [denote']

theorem denote'_deref (e : ImpExpr) (env : Env) :
    denote' bi fuel (.deref e) env = denote' bi fuel e env := by
  simp only [denote']

theorem denote'_typeAscription (e : ImpExpr) (ty : String) (env : Env) :
    denote' bi fuel (.typeAscription e ty) env = denote' bi fuel e env := by
  simp only [denote']

theorem denoteArgs'_nil (env : Env) : denoteArgs' bi fuel [] env = (some [], env) := by
  simp only [denoteArgs']; rfl

theorem denoteArgs'_cons {e : ImpExpr} {es : List ImpExpr} {env s s' : Env} {v : Value}
    {vs : List Value} (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false)
    (hs : denoteArgs' bi fuel es s = (some vs, s')) :
    denoteArgs' bi fuel (e :: es) env = (some (v :: vs), s') := by
  simp only [denoteArgs', stateM_bind_apply, h]
  cases v <;> first | (simp only [stateM_bind_apply, hs]; rfl) | simp at hv

theorem denote'_app {f : String} {args : List ImpExpr} {env s : Env} {vs : List Value}
    {w : Value} (h : denoteArgs' bi fuel args env = (some vs, s)) (hb : bi f vs = some w) :
    denote' bi fuel (.app f args) env = (.val w, s) := by
  simp only [denote', denoteApp', stateM_bind_apply, h, hb]; rfl

theorem denote'_tuple {es : List ImpExpr} {env s : Env} {vs : List Value}
    (h : denoteArgs' bi fuel es env = (some vs, s)) :
    denote' bi fuel (.tuple es) env = (.val (.tuple vs), s) := by
  simp only [denote', stateM_bind_apply, h]; rfl

theorem denote'_cfBreak {e : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.cfBreak e) env = (.val (.controlFlow true v), s) := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | rfl | simp at hv

theorem denote'_cfContinue {e : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.cfContinue e) env = (.val (.controlFlow false v), s) := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | rfl | simp at hv

theorem denote'_forFold {var : String} {lo hi body : ImpExpr} {env s1 s2 : Env} {a b : Int}
    (hlo : denote' bi fuel lo env = (.val (.int a), s1))
    (hhi : denote' bi fuel hi s1 = (.val (.int b), s2)) :
    denote' bi fuel (.forFold var lo hi body) env = denoteForLoop' bi fuel var a b body s2 := by
  simp only [denote', stateM_bind_apply, hlo, hhi]

theorem denoteForLoop'_done (var : String) {a b : Int} (body : ImpExpr) (env : Env)
    (h : a ≥ b) : denoteForLoop' bi fuel var a b body env = (.val .unit, env) := by
  rw [denoteForLoop']
  simp only [if_pos h]; rfl

theorem denoteForLoop'_break (var : String) {a b : Int} {body : ImpExpr} {env s : Env}
    {w : Value} (hab : a < b) (hf : fuel ≠ 0)
    (h : denote' bi fuel body (env.extend var (.int a)) = (.val (.controlFlow true w), s)) :
    denoteForLoop' bi fuel var a b body env = (.val w, s) := by
  rw [denoteForLoop']
  simp only [if_neg (Int.not_le.mpr hab), if_neg hf, stateM_bind_apply, stateM_modify_apply, h]
  rfl

theorem denoteForLoop'_next (var : String) {a b : Int} {body : ImpExpr} {env s : Env}
    {v : Value} (hab : a < b) (hf : fuel ≠ 0)
    (h : denote' bi fuel body (env.extend var (.int a)) = (.val v, s))
    (hv : ∀ w, v ≠ .controlFlow true w) :
    denoteForLoop' bi fuel var a b body env = denoteForLoop' bi (fuel - 1) var (a + 1) b body s := by
  rw [denoteForLoop']
  simp only [if_neg (Int.not_le.mpr hab), if_neg hf, stateM_bind_apply, stateM_modify_apply, h]
  cases v
  case controlFlow c w =>
    cases c
    · rfl
    · exact absurd rfl (hv w)
  all_goals rfl

end Steps

/-! ## The judgment -/

section Judgment

variable {S : Type} (bi : Builtins)

/-- **The correspondence judgment.** From an environment related to `σ` by `P` with the
    guard `G σ`, there are a fuel `fuel₀` and an exit environment `env'` related to `σ`
    by `Q` such that at every `fuel ≥ fuel₀` the run of `e` is `(.val (V σ), env')`. -/
def Corres (P : Env → S → Prop) (G : S → Prop) (e : ImpExpr) (V : S → Value)
    (Q : Env → S → Prop) : Prop :=
  ∀ env σ, P env σ → G σ →
    ∃ fuel₀ env', Q env' σ ∧ ∀ fuel, fuel₀ ≤ fuel → denote' bi fuel e env = (.val (V σ), env')

/-- The correspondence of an argument list: the run of `denoteArgs'` returns the values
    `Vs σ`. -/
def CorresArgs (P : Env → S → Prop) (G : S → Prop) (es : List ImpExpr) (Vs : S → List Value)
    (Q : Env → S → Prop) : Prop :=
  ∀ env σ, P env σ → G σ →
    ∃ fuel₀ env', Q env' σ ∧ ∀ fuel, fuel₀ ≤ fuel → denoteArgs' bi fuel es env = (some (Vs σ), env')

end Judgment

/-! ## The eventual value of a run -/

section EventualValue

variable {bi : Builtins}

/-- The eventual value of the run of `e` from `env`: the value the run returns at every
    fuel from some fuel on, when there is one. -/
noncomputable def haxEval (bi : Builtins) (e : ImpExpr) (env : Env) : Option Value :=
  open Classical in
  if h : ∃ v fuel₀, ∀ fuel, fuel₀ ≤ fuel → (denote' bi fuel e env).1 = .val v then
    some h.choose
  else none

theorem haxEval_eq {e : ImpExpr} {env : Env} {v : Value} {fuel₀ : Nat}
    (h : ∀ fuel, fuel₀ ≤ fuel → (denote' bi fuel e env).1 = .val v) :
    haxEval bi e env = some v := by
  have hex : ∃ v fuel₀, ∀ fuel, fuel₀ ≤ fuel → (denote' bi fuel e env).1 = .val v :=
    ⟨v, fuel₀, h⟩
  unfold haxEval
  rw [dif_pos hex]
  obtain ⟨fuel₁, h₁⟩ := hex.choose_spec
  have e₁ := h₁ (max fuel₀ fuel₁) (by omega)
  rw [h (max fuel₀ fuel₁) (by omega)] at e₁
  exact congrArg some (Outcome.val.inj e₁).symm

end EventualValue

end Hax.Ascent
