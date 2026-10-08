/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Eval

/-!
# Weakest preconditions over the eventual semantics of `denote'`

`wp bi e Φ Ψ env` holds when the eventual run of `e` from `env` (`Eval`) returns a value
`v` in an environment `env'` with `Φ v env'` if `v` is plain and `Ψ v env'` if `v` is a
control-flow value. Every construct of `denote'` passes a control-flow value of a
subexpression through unchanged, whatever its tag, so one second postcondition `Ψ`
serves `break`, `continue` and early exit.

## Main results

* `wp_seq`, `wp_letBind`, `wp_assign`, `wp_ifThenElse`, `wp_proj`, `wp_cfBreak`,
  `wp_cfContinue`, `wp_app`, `wp_tuple`, `wpArgs_cons`, ... — the rules in continuation
  form, each an equivalence and free of fuel
* `wp_forFold` — the counted loop under an invariant indexed by the counter
* `corres_iff_wp`, `corresArgs_iff_wpArgs` — the correspondence judgment is the triple
  whose postcondition is `v = V σ ∧ Q env' σ`; the rules of `Corres`
  (`HaxAscent/Ascent/Corres.lean`) are proved from the rules here through them
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {bi : Builtins}

/-! ## The weakest precondition -/

/-- The postcondition of an outcome value: `Φ` at a plain value, `Ψ` at a control-flow
    value. -/
def wpPost (Φ Ψ : Value → Env → Prop) (v : Value) (env : Env) : Prop :=
  (v.isControlFlow = false ∧ Φ v env) ∨ (v.isControlFlow = true ∧ Ψ v env)

theorem wpPost_of_plain {Φ Ψ : Value → Env → Prop} {v : Value} {env : Env}
    (h : v.isControlFlow = false) : wpPost Φ Ψ v env ↔ Φ v env := by
  simp only [wpPost, h, true_and, Bool.false_eq_true, false_and, or_false]

theorem wpPost_of_cf {Φ Ψ : Value → Env → Prop} {v : Value} {env : Env}
    (h : v.isControlFlow = true) : wpPost Φ Ψ v env ↔ Ψ v env := by
  simp only [wpPost, h, Bool.true_eq_false, false_and, true_and, false_or]

theorem wpPost_self {Φ : Value → Env → Prop} {v : Value} {env : Env} :
    wpPost Φ Φ v env ↔ Φ v env := by
  cases h : v.isControlFlow
  · exact wpPost_of_plain h
  · exact wpPost_of_cf h

variable (bi) in
/-- **Weakest precondition over the eventual semantics.** The run of `e` from `env`
    eventually returns a value `v` in an environment `env'` with `Φ v env'` when `v` is
    plain and `Ψ v env'` when `v` is a control-flow value. -/
def wp (e : ImpExpr) (Φ Ψ : Value → Env → Prop) (env : Env) : Prop :=
  ∃ v env', Eval bi e env v env' ∧ wpPost Φ Ψ v env'

variable (bi) in
/-- The weakest precondition of an argument list: its eventual run returns the values
    `vs` in an environment `env'` with `Φ vs env'`. -/
def wpArgs (es : List ImpExpr) (Φ : List Value → Env → Prop) (env : Env) : Prop :=
  ∃ vs env', EvalArgs bi es env vs env' ∧ Φ vs env'

/-- **Monotonicity**, with each postcondition weakened only at the values it reads. -/
theorem wp_mono {e : ImpExpr} {Φ Ψ Φ' Ψ' : Value → Env → Prop} {env : Env}
    (h : wp bi e Φ Ψ env) (hΦ : ∀ v s, v.isControlFlow = false → Φ v s → Φ' v s)
    (hΨ : ∀ v s, v.isControlFlow = true → Ψ v s → Ψ' v s) : wp bi e Φ' Ψ' env := by
  obtain ⟨v, s, hE, ⟨hc, hp⟩ | ⟨hc, hp⟩⟩ := h
  · exact ⟨v, s, hE, Or.inl ⟨hc, hΦ v s hc hp⟩⟩
  · exact ⟨v, s, hE, Or.inr ⟨hc, hΨ v s hc hp⟩⟩

/-- Postconditions that agree on every outcome have the same weakest precondition. -/
theorem wp_congr {e : ImpExpr} {Φ Ψ Φ' Ψ' : Value → Env → Prop} {env : Env}
    (h : ∀ v s, wpPost Φ Ψ v s ↔ wpPost Φ' Ψ' v s) : wp bi e Φ Ψ env ↔ wp bi e Φ' Ψ' env :=
  exists_congr fun v => exists_congr fun s => and_congr_right fun _ => h v s

/-- The weakest precondition is the postcondition at the outcome, which is unique. -/
theorem wp_iff_forall {e : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi e Φ Ψ env ↔ (∃ v s, Eval bi e env v s) ∧ ∀ v s, Eval bi e env v s → wpPost Φ Ψ v s := by
  constructor
  · rintro ⟨v, s, hE, hp⟩
    refine ⟨⟨v, s, hE⟩, fun v' s' hE' => ?_⟩
    obtain ⟨rfl, rfl⟩ := Eval_det hE hE'
    exact hp
  · rintro ⟨⟨v, s, hE⟩, h⟩
    exact ⟨v, s, hE, h v s hE⟩

/-! ## Rules in continuation form -/

theorem wp_lit {l : ImpLit} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.lit l) Φ Ψ env ↔ wpPost Φ Ψ (Value.ofLit l) env := by
  constructor
  · rintro ⟨v, s, hE, hp⟩
    obtain ⟨rfl, rfl⟩ := Eval_lit_iff.mp hE
    exact hp
  · intro hp
    exact ⟨_, env, Eval_lit_iff.mpr ⟨rfl, rfl⟩, hp⟩

theorem wp_unitVal {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi .unitVal Φ Ψ env ↔ Φ .unit env := by
  rw [← wpPost_of_plain (Φ := Φ) (Ψ := Ψ) (env := env) Value.isControlFlow_unit]
  constructor
  · rintro ⟨v, s, hE, hp⟩
    obtain ⟨rfl, rfl⟩ := Eval_unitVal_iff.mp hE
    exact hp
  · intro hp
    exact ⟨_, env, Eval_unitVal_iff.mpr ⟨rfl, rfl⟩, hp⟩

theorem wp_var {x : String} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.var x) Φ Ψ env ↔ ∃ v, env x = some v ∧ wpPost Φ Ψ v env := by
  constructor
  · rintro ⟨v, s, hE, hp⟩
    obtain ⟨hx, rfl⟩ := Eval_var_iff.mp hE
    exact ⟨v, hx, hp⟩
  · rintro ⟨v, hx, hp⟩
    exact ⟨v, env, Eval_var_iff.mpr ⟨hx, rfl⟩, hp⟩

theorem wp_borrow {e : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.borrow e) Φ Ψ env ↔ wp bi e Φ Ψ env := by
  simp only [wp, Eval_borrow_iff]

theorem wp_deref {e : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.deref e) Φ Ψ env ↔ wp bi e Φ Ψ env := by
  simp only [wp, Eval_deref_iff]

theorem wp_typeAscription {e : ImpExpr} {ty : String} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.typeAscription e ty) Φ Ψ env ↔ wp bi e Φ Ψ env := by
  simp only [wp, Eval_typeAscription_iff]

/-- **Sequence.** The second expression runs after a plain value of the first; a
    control-flow value of the first meets `Ψ`. -/
theorem wp_seq {e1 e2 : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.seq e1 e2) Φ Ψ env ↔ wp bi e1 (fun _ s => wp bi e2 Φ Ψ s) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨hc, h2⟩⟩ := Eval_seq_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨w, s, h1, Or.inl ⟨hc, v, env', h2, hp⟩⟩
  · rintro ⟨w, s, h1, ⟨hc, v, env', h2, hp⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨v, env', Eval_seq_iff.mpr ⟨w, s, h1, Or.inr ⟨hc, h2⟩⟩, hp⟩
    · exact ⟨w, s, Eval_seq_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

/-- **`let`.** The body runs from the exit environment extended at the name by a plain
    value of the bound expression; a control-flow value of the bound expression meets
    `Ψ`. -/
theorem wp_letBind {x : String} {val body : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.letBind x val body) Φ Ψ env ↔
      wp bi val (fun w s => wp bi body Φ Ψ (s.extend x w)) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨hc, h2⟩⟩ := Eval_letBind_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨w, s, h1, Or.inl ⟨hc, v, env', h2, hp⟩⟩
  · rintro ⟨w, s, h1, ⟨hc, v, env', h2, hp⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨v, env', Eval_letBind_iff.mpr ⟨w, s, h1, Or.inr ⟨hc, h2⟩⟩, hp⟩
    · exact ⟨w, s, Eval_letBind_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

/-- **Assignment.** A plain value of the right-hand side is bound at the name and the
    assignment returns `.unit`. -/
theorem wp_assign {x : String} {rhs : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.assign x rhs) Φ Ψ env ↔ wp bi rhs (fun w s => Φ .unit (s.extend x w)) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨hc, rfl, rfl⟩⟩ := Eval_assign_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨w, s, h1, Or.inl ⟨hc, (wpPost_of_plain Value.isControlFlow_unit).mp hp⟩⟩
  · rintro ⟨w, s, h1, ⟨hc, hΦ⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨.unit, s.extend x w, Eval_assign_iff.mpr ⟨w, s, h1, Or.inr ⟨hc, rfl, rfl⟩⟩,
        Or.inl ⟨Value.isControlFlow_unit, hΦ⟩⟩
    · exact ⟨w, s, Eval_assign_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

/-- **Conditional.** The condition returns `.bool true` or `.bool false` and the selected
    branch runs; a control-flow value of the condition meets `Ψ`. -/
theorem wp_ifThenElse {c t e : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.ifThenElse c t e) Φ Ψ env ↔
      wp bi c (fun w s => (w = .bool true ∧ wp bi t Φ Ψ s) ∨
        (w = .bool false ∧ wp bi e Φ Ψ s)) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := Eval_ifThenElse_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨_, s, h1, Or.inl ⟨Value.isControlFlow_bool _, Or.inl ⟨rfl, v, env', h2, hp⟩⟩⟩
    · exact ⟨_, s, h1, Or.inl ⟨Value.isControlFlow_bool _, Or.inr ⟨rfl, v, env', h2, hp⟩⟩⟩
  · rintro ⟨w, s, h1, ⟨-, ⟨rfl, v, env', h2, hp⟩ | ⟨rfl, v, env', h2, hp⟩⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨v, env', Eval_ifThenElse_iff.mpr ⟨_, s, h1, Or.inr (Or.inl ⟨rfl, h2⟩)⟩, hp⟩
    · exact ⟨v, env', Eval_ifThenElse_iff.mpr ⟨_, s, h1, Or.inr (Or.inr ⟨rfl, h2⟩)⟩, hp⟩
    · exact ⟨w, s, Eval_ifThenElse_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

/-- **Projection.** Index `i` of a plain value, read by `Value.projIdx`. -/
theorem wp_proj {e : ImpExpr} {i : Nat} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.proj e i) Φ Ψ env ↔
      wp bi e (fun w s => ∃ u, w.projIdx i = some u ∧ wpPost Φ Ψ u s) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨hc, hi, rfl⟩⟩ := Eval_proj_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨w, env', h1, Or.inl ⟨hc, v, hi, hp⟩⟩
  · rintro ⟨w, s, h1, ⟨hc, u, hi, hp⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨u, s, Eval_proj_iff.mpr ⟨w, s, h1, Or.inr ⟨hc, hi, rfl⟩⟩, hp⟩
    · exact ⟨w, s, Eval_proj_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

/-- **`break`.** A plain value `w` leaves as `controlFlow true w` through `Ψ`. -/
theorem wp_cfBreak {e : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.cfBreak e) Φ Ψ env ↔ wp bi e (fun w s => Ψ (.controlFlow true w) s) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨hc, rfl, rfl⟩⟩ := Eval_cfBreak_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨w, _, h1, Or.inl ⟨hc, (wpPost_of_cf (Value.isControlFlow_controlFlow _ _)).mp hp⟩⟩
  · rintro ⟨w, s, h1, ⟨hc, hΨ⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨_, s, Eval_cfBreak_iff.mpr ⟨w, s, h1, Or.inr ⟨hc, rfl, rfl⟩⟩,
        Or.inr ⟨Value.isControlFlow_controlFlow _ _, hΨ⟩⟩
    · exact ⟨w, s, Eval_cfBreak_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

/-- **`continue`.** A plain value `w` leaves as `controlFlow false w` through `Ψ`. -/
theorem wp_cfContinue {e : ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.cfContinue e) Φ Ψ env ↔ wp bi e (fun w s => Ψ (.controlFlow false w) s) Ψ env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨w, s, h1, ⟨hc, rfl, rfl⟩ | ⟨hc, rfl, rfl⟩⟩ := Eval_cfContinue_iff.mp hE
    · exact ⟨v, env', h1, Or.inr ⟨hc, (wpPost_of_cf hc).mp hp⟩⟩
    · exact ⟨w, _, h1, Or.inl ⟨hc, (wpPost_of_cf (Value.isControlFlow_controlFlow _ _)).mp hp⟩⟩
  · rintro ⟨w, s, h1, ⟨hc, hΨ⟩ | ⟨hc, hΨ⟩⟩
    · exact ⟨_, s, Eval_cfContinue_iff.mpr ⟨w, s, h1, Or.inr ⟨hc, rfl, rfl⟩⟩,
        Or.inr ⟨Value.isControlFlow_controlFlow _ _, hΨ⟩⟩
    · exact ⟨w, s, Eval_cfContinue_iff.mpr ⟨w, s, h1, Or.inl ⟨hc, rfl, rfl⟩⟩, Or.inr ⟨hc, hΨ⟩⟩

theorem wpArgs_nil {Φ : List Value → Env → Prop} {env : Env} :
    wpArgs bi [] Φ env ↔ Φ [] env := by
  constructor
  · rintro ⟨vs, s, hE, hp⟩
    obtain ⟨rfl, rfl⟩ := EvalArgs_nil_iff.mp hE
    exact hp
  · intro hp
    exact ⟨[], env, EvalArgs_nil_iff.mpr ⟨rfl, rfl⟩, hp⟩

/-- **Argument list.** The head returns a plain value and the tail runs after it; a
    control-flow value of the head is not an outcome of the list. -/
theorem wpArgs_cons {e : ImpExpr} {es : List ImpExpr} {Φ : List Value → Env → Prop}
    {env : Env} :
    wpArgs bi (e :: es) Φ env ↔
      wp bi e (fun w s => wpArgs bi es (fun ws => Φ (w :: ws)) s) (fun _ _ => False) env := by
  constructor
  · rintro ⟨vs, env', hE, hp⟩
    obtain ⟨w, s, ws, he, hc, hes, rfl⟩ := EvalArgs_cons_iff.mp hE
    exact ⟨w, s, he, Or.inl ⟨hc, ws, env', hes, hp⟩⟩
  · rintro ⟨w, s, he, ⟨hc, ws, env', hes, hp⟩ | ⟨-, hf⟩⟩
    · exact ⟨w :: ws, env', EvalArgs_cons_iff.mpr ⟨w, s, ws, he, hc, hes, rfl⟩, hp⟩
    · exact hf.elim

/-- **Call.** The arguments return `vs` and the builtin table maps them to the value. -/
theorem wp_app {g : String} {args : List ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.app g args) Φ Ψ env ↔
      wpArgs bi args (fun vs s => ∃ v, bi g vs = some v ∧ wpPost Φ Ψ v s) env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨vs, hargs, hb⟩ := Eval_app_iff.mp hE
    exact ⟨vs, env', hargs, v, hb, hp⟩
  · rintro ⟨vs, env', hargs, v, hb, hp⟩
    exact ⟨v, env', Eval_app_iff.mpr ⟨vs, hargs, hb⟩, hp⟩

theorem wp_tuple {es : List ImpExpr} {Φ Ψ : Value → Env → Prop} {env : Env} :
    wp bi (.tuple es) Φ Ψ env ↔ wpArgs bi es (fun vs s => Φ (.tuple vs) s) env := by
  constructor
  · rintro ⟨v, env', hE, hp⟩
    obtain ⟨vs, hargs, rfl⟩ := Eval_tuple_iff.mp hE
    exact ⟨vs, env', hargs, (wpPost_of_plain (Value.isControlFlow_tuple vs)).mp hp⟩
  · rintro ⟨vs, env', hargs, hp⟩
    exact ⟨_, env', Eval_tuple_iff.mpr ⟨vs, hargs, rfl⟩,
      Or.inl ⟨Value.isControlFlow_tuple vs, hp⟩⟩

/-! ## Counted loops -/

/-- The loop helper from index `i`, under an invariant `Inv` indexed by the counter, by
    induction on the number `n` of remaining iterations. -/
theorem evalLoop_of_inv {var : String} {body : ImpExpr} {a b : Int}
    {Φ Ψ : Value → Env → Prop} (Inv : Int → Env → Prop)
    (hstep : ∀ i s, a ≤ i → i < b → Inv i s →
      wp bi body (fun _ s' => Inv (i + 1) s')
        (fun v s' => (∃ w, v = .controlFlow true w ∧ wpPost Φ Ψ w s') ∨
          (∃ w, v = .controlFlow false w ∧ Inv (i + 1) s')) (s.extend var (.int i)))
    (hend : ∀ s, Inv (max a b) s → Φ .unit s) :
    ∀ n : Nat, ∀ i s, (b - i).toNat = n → a ≤ i → i ≤ max a b → Inv i s →
      ∃ v s', EvalLoop bi var i b body s v s' ∧ wpPost Φ Ψ v s' := by
  intro n
  induction n with
  | zero =>
    intro i s hn hai him hI
    have hbi : b ≤ i := by omega
    have hi : i = max a b := by omega
    subst hi
    exact ⟨.unit, s, EvalLoop_done var body s (by omega),
      Or.inl ⟨Value.isControlFlow_unit, hend s hI⟩⟩
  | succ n ih =>
    intro i s hn hai him hI
    have hib : i < b := by omega
    obtain ⟨v, s', hE, ⟨hc, hI'⟩ | ⟨hc, ⟨w, rfl, hp⟩ | ⟨w, rfl, hI'⟩⟩⟩ :=
      hstep i s hai hib hI
    · obtain ⟨v', s'', hl, hp⟩ := ih (i + 1) s' (by omega) (by omega) (by omega) hI'
      refine ⟨v', s'', EvalLoop_next var hib hE (fun w hw => ?_) hl, hp⟩
      rw [hw] at hc
      cases hc
    · exact ⟨w, s', EvalLoop_break var hib hE, hp⟩
    · obtain ⟨v', s'', hl, hp⟩ := ih (i + 1) s' (by omega) (by omega) (by omega) hI'
      exact ⟨v', s'', EvalLoop_next var hib hE (fun w' hw => by cases hw) hl, hp⟩

/-- **Counted loop.** The bounds return `.int a` and `.int b` (a control-flow value of a
    bound meets `Ψ`), and an invariant `Inv` indexed by the counter holds at `a`. Each
    iteration from `Inv i` re-establishes `Inv (i + 1)` by a plain value or a
    `controlFlow false` value of the body, or leaves the loop by `controlFlow true w`
    with `w` meeting the postcondition; at `max a b` the invariant gives `Φ .unit`. -/
theorem wp_forFold {var : String} {lo hi body : ImpExpr} {a b : Int}
    {Φ Ψ : Value → Env → Prop} {env : Env} (Inv : Int → Env → Prop)
    (hbounds : wp bi lo (fun vl s₁ => vl = .int a ∧
      wp bi hi (fun vh s₂ => vh = .int b ∧ Inv a s₂) Ψ s₁) Ψ env)
    (hstep : ∀ i s, a ≤ i → i < b → Inv i s →
      wp bi body (fun _ s' => Inv (i + 1) s')
        (fun v s' => (∃ w, v = .controlFlow true w ∧ wpPost Φ Ψ w s') ∨
          (∃ w, v = .controlFlow false w ∧ Inv (i + 1) s')) (s.extend var (.int i)))
    (hend : ∀ s, Inv (max a b) s → Φ .unit s) :
    wp bi (.forFold var lo hi body) Φ Ψ env := by
  obtain ⟨vl, s₁, hlo, ⟨-, rfl, vh, s₂, hhi, ⟨-, rfl, hI⟩ | ⟨hc, hΨ⟩⟩ | ⟨hc, hΨ⟩⟩ := hbounds
  · obtain ⟨v, s', hl, hp⟩ := evalLoop_of_inv Inv hstep hend _ a s₂ rfl (Int.le_refl a)
      (Int.le_max_left a b) hI
    exact ⟨v, s', Eval_forFold_intro hlo hhi hl, hp⟩
  · exact ⟨vh, s₂, Eval_forFold_hi_cf hlo hhi hc, Or.inr ⟨hc, hΨ⟩⟩
  · exact ⟨vl, s₁, Eval_forFold_lo_cf hlo hc, Or.inr ⟨hc, hΨ⟩⟩

/-! ## The correspondence judgment as a weakest precondition -/

/-- **`Corres` is a triple.** The correspondence holds when, for every abstract state
    under the guard and every related environment, the run eventually returns `V σ` and
    ends in an environment related by `Q`; the same postcondition serves plain and
    control-flow values. -/
theorem corres_iff_wp {S : Type} {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    Corres bi P G e V Q ↔ ∀ σ, G σ → ∀ env, P env σ →
      wp bi e (fun v env' => v = V σ ∧ Q env' σ) (fun v env' => v = V σ ∧ Q env' σ) env := by
  constructor
  · intro h σ hG env hP
    obtain ⟨f₀, env', hQ, hrun⟩ := h env σ hP hG
    exact ⟨V σ, env', ⟨f₀, hrun⟩, wpPost_self.mpr ⟨rfl, hQ⟩⟩
  · intro h env σ hP hG
    obtain ⟨v, env', ⟨f₀, hrun⟩, hp⟩ := h σ hG env hP
    obtain ⟨rfl, hQ⟩ := wpPost_self.mp hp
    exact ⟨f₀, env', hQ, hrun⟩

/-- `CorresArgs` is the weakest precondition of the argument list. -/
theorem corresArgs_iff_wpArgs {S : Type} {P Q : Env → S → Prop} {G : S → Prop}
    {es : List ImpExpr} {Vs : S → List Value} :
    CorresArgs bi P G es Vs Q ↔ ∀ σ, G σ → ∀ env, P env σ →
      wpArgs bi es (fun vs env' => vs = Vs σ ∧ Q env' σ) env := by
  constructor
  · intro h σ hG env hP
    obtain ⟨f₀, env', hQ, hrun⟩ := h env σ hP hG
    exact ⟨Vs σ, env', ⟨f₀, hrun⟩, rfl, hQ⟩
  · intro h env σ hP hG
    obtain ⟨vs, env', ⟨f₀, hrun⟩, rfl, hQ⟩ := h σ hG env hP
    exact ⟨f₀, env', hQ, hrun⟩

end Hax.Ascent
