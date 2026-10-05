/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AnfLowCT

/-!
# Conditionals with assignment-free branches as selects

`desugarIte ρ e` replaces a conditional `ifThenElse c a b` of `e` by the call
`select(c', a', b')` when `c`, `a` and `b` are speculatable expressions: a literal, a
variable, a call of a name `ρ` admits on speculatable arguments, or a conditional of
speculatable expressions. A call of `f` becomes the call of `g` when `ρ f = some g`;
a name with `ρ f = none` is refused. The renaming replaces a checked operation by a total
one that agrees with it wherever the checked one is defined (`Refines`), so that the arm
the source does not run still evaluates. `hax64Spec` renames the checked `Sub` and `Add`
to the wrapping operations at `64` bits and keeps the wrapping, bitwise, cast and
comparison calls.

The pass descends through `letBind` and `seq`; every other expression, and a conditional
with an arm outside the speculatable class, is unchanged.

A select evaluates both arms. The denotation lemmas therefore relate two successful runs:
when the source runs to a value that is not a control-flow value and the result of the
pass runs to a value, the two values and the two environments are equal. The run of the
result is a hypothesis; it holds when every renamed operation is defined on the values of
the environment.

## Main definitions

* `selectName` — the name of the select call.
* `specExpr`, `specArgs` — the speculatable form of an expression and of a list of
  arguments, along a renaming of the call names.
* `pureForm`, `pureForms` — the expressions built of literals, variables, calls and
  conditionals.
* `iteFree`, `iteFreeL` — the expressions built of the constructors `lit`, `var`,
  `unitVal`, `app`, `tuple`, `letBind`, `seq`, `assign`, `typeAscription` and `forFold`;
  none is a conditional.
* `desugarIte` — the pass.
* `Plain` — the values that are not control-flow values.
* `SelectSpec`, `Refines` — the hypotheses on the builtins: `select` reads its second
  operand at `true` and its third at `false`; a renamed call agrees with the source call
  where both are defined.
* `hax64Spec` — the renaming for `u64` code.

## Main results

* `denote'_pureForm_env` — a `pureForm` expression leaves the environment unchanged.
* `specExpr_denote` — a speculatable expression and its select form run to the same
  value.
* `desugarIte_denote` — the pass preserves the value and the final environment.
* `specExpr_iteFree`, `desugarIte_iteFree_of_spec`, `desugarIte_iteFree_letBind`,
  `desugarIte_iteFree_seq` — the select form has no conditional.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpDesugarIte

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote' denoteApp' denoteArgs')

/-! ## 1. The pass -/

/-- The name of the select call: `select(c, a, b)` is `a` at `c = true` and `b` at
    `c = false`. -/
def selectName : String := "select"

mutual
/-- The select form of a speculatable expression along the renaming `ρ` of call names:
    a literal and a variable are unchanged, a call of `f` with `ρ f = some g` is the call
    of `g` on the select forms of its arguments, and a conditional is the call of
    `selectName` on the select forms of its condition and its two arms. Every other
    expression is `none`. -/
def specExpr (ρ : String → Option String) : ImpExpr → Option ImpExpr
  | .lit l => some (.lit l)
  | .var x => some (.var x)
  | .app f args =>
      match ρ f, specArgs ρ args with
      | some g, some as => some (.app g as)
      | _, _ => none
  | .ifThenElse c a b =>
      match specExpr ρ c, specExpr ρ a, specExpr ρ b with
      | some c', some a', some b' => some (.app selectName [c', a', b'])
      | _, _, _ => none
  | _ => none
/-- The select forms of a list of arguments. -/
def specArgs (ρ : String → Option String) : List ImpExpr → Option (List ImpExpr)
  | [] => some []
  | e :: es =>
      match specExpr ρ e, specArgs ρ es with
      | some e', some es' => some (e' :: es')
      | _, _ => none
end

mutual
/-- An expression built of literals, variables, calls and conditionals. -/
def pureForm : ImpExpr → Bool
  | .lit _ | .var _ => true
  | .app _ args => pureForms args
  | .ifThenElse c a b => pureForm c && pureForm a && pureForm b
  | _ => false
/-- A list of `pureForm` expressions. -/
def pureForms : List ImpExpr → Bool
  | [] => true
  | e :: es => pureForm e && pureForms es
end

mutual
/-- An expression built of the constructors `lit`, `var`, `unitVal`, `app`, `tuple`,
    `letBind`, `seq`, `assign`, `typeAscription` and `forFold`. No such expression has a
    conditional. -/
def iteFree : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | .app _ args => iteFreeL args
  | .tuple es => iteFreeL es
  | .letBind _ v b => iteFree v && iteFree b
  | .seq a b => iteFree a && iteFree b
  | .assign _ r => iteFree r
  | .typeAscription e _ => iteFree e
  | .forFold _ lo hi body => iteFree lo && iteFree hi && iteFree body
  | _ => false
/-- A list of `iteFree` expressions. -/
def iteFreeL : List ImpExpr → Bool
  | [] => true
  | e :: es => iteFree e && iteFreeL es
end

/-- The pass: a conditional with a select form is replaced by it, through `letBind` and
    `seq`. Every other expression is unchanged. -/
def desugarIte (ρ : String → Option String) : ImpExpr → ImpExpr
  | .letBind x v b => .letBind x (desugarIte ρ v) (desugarIte ρ b)
  | .seq a b => .seq (desugarIte ρ a) (desugarIte ρ b)
  | .ifThenElse c a b => (specExpr ρ (.ifThenElse c a b)).getD (.ifThenElse c a b)
  | e => e

/-- The renaming for `u64` code: the checked `Sub` and `Add` are the wrapping operations
    at `64` bits; the wrapping, bitwise, cast and comparison calls are kept; every other
    name is refused. -/
def hax64Spec (f : String) : Option String :=
  if f = "Sub" then some "wrapping_sub#64"
  else if f = "Add" then some "wrapping_add#64"
  else if f ∈ ["wrapping_add#8", "wrapping_sub#8", "wrapping_mul#8", "BitAnd#8", "BitOr#8",
      "BitXor#8", "Not#8", "cast#8",
      "wrapping_add#16", "wrapping_sub#16", "wrapping_mul#16", "BitAnd#16", "BitOr#16",
      "BitXor#16", "Not#16", "cast#16",
      "wrapping_add#32", "wrapping_sub#32", "wrapping_mul#32", "BitAnd#32", "BitOr#32",
      "BitXor#32", "Not#32", "cast#32",
      "wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "BitAnd#64", "BitOr#64",
      "BitXor#64", "Not#64", "cast#64",
      "wrapping_add#size", "wrapping_sub#size", "wrapping_mul#size", "BitAnd#size",
      "BitOr#size", "BitXor#size", "Not#size", "cast#size",
      "Eq", "eq", "Ne", "ne", "Lt", "lt", "Le", "le", "Gt", "gt", "Ge", "ge"] then some f
  else none

/-! ## 2. The hypotheses on the builtins -/

/-- A value that is not a control-flow value. -/
def Plain (v : Value) : Prop := ∀ k p, v ≠ .controlFlow k p

/-- The builtin `selectName` reads its second operand at `true` and its third at
    `false`. -/
def SelectSpec (bi : Builtins) : Prop :=
  ∀ (k : Bool) (x y : Value), bi selectName [.bool k, x, y] = some (if k then x else y)

/-- A call renamed by `ρ` agrees with the source call on the arguments where both are
    defined. -/
def Refines (bi : Builtins) (ρ : String → Option String) : Prop :=
  ∀ f g, ρ f = some g → ∀ vals v w, bi f vals = some v → bi g vals = some w → v = w

/-! ## 3. Inversion of successful runs -/

/-- One-step unfolding of `denote'` at a call. -/
theorem denote'_app_run (bi : Builtins) (fuel : Nat) (f : String) (args : List ImpExpr)
    (env : Env) :
    denote' bi fuel (.app f args) env =
      match denoteArgs' bi fuel args env with
      | (some vals, e1) =>
          match bi f vals with
          | some v => (.val v, e1)
          | none => (.err s!"unknown function or bad args: {f}", e1)
      | (none, e1) => (.err "non-value in function arguments", e1) := by
  simp only [denote', denoteApp', bind, StateT.bind, pure]
  rcases denoteArgs' bi fuel args env with ⟨o, e1⟩
  rcases o with _ | vals
  · rfl
  · cases h : bi f vals <;> simp only [h] <;> rfl

/-- One-step unfolding of `denoteArgs'` at a nonempty list. -/
theorem denoteArgs'_cons_run (bi : Builtins) (fuel : Nat) (e : ImpExpr) (es : List ImpExpr)
    (env : Env) :
    denoteArgs' bi fuel (e :: es) env =
      match denote' bi fuel e env with
      | (.val (.controlFlow _ _), e1) => (none, e1)
      | (.val v, e1) =>
          ((denoteArgs' bi fuel es e1).1.map (v :: ·), (denoteArgs' bi fuel es e1).2)
      | (_, e1) => (none, e1) := by
  simp only [denoteArgs', bind, StateT.bind, pure]
  rcases denote' bi fuel e env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

/-- `denoteArgs'` at the empty list. -/
theorem denoteArgs'_nil_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denoteArgs' bi fuel [] env = (some [], env) := by
  simp only [denoteArgs']; rfl

/-- A call that runs to a value: its arguments run to values and the builtin is defined
    on them. -/
theorem denote'_app_val {bi : Builtins} {fuel : Nat} {f : String} {args : List ImpExpr}
    {env e₁ : Env} {v : Value} (h : denote' bi fuel (.app f args) env = (.val v, e₁)) :
    ∃ vals, denoteArgs' bi fuel args env = (some vals, e₁) ∧ bi f vals = some v := by
  rw [denote'_app_run] at h
  rcases hd : denoteArgs' bi fuel args env with ⟨o, e1⟩
  rw [hd] at h
  rcases o with _ | vals
  · cases h
  · dsimp only at h
    rcases hb : bi f vals with _ | u
    · rw [hb] at h; cases h
    · rw [hb] at h; cases h; exact ⟨vals, rfl, hb⟩

/-- A nonempty list of arguments that runs to values: the head runs to a value that is
    not a control-flow value, and the tail runs to values from the environment the head
    leaves. -/
theorem denoteArgs'_cons_some {bi : Builtins} {fuel : Nat} {e : ImpExpr}
    {es : List ImpExpr} {env e₁ : Env} {vs : List Value}
    (h : denoteArgs' bi fuel (e :: es) env = (some vs, e₁)) :
    ∃ u x vs0, denote' bi fuel e env = (.val u, x) ∧ Plain u ∧
      denoteArgs' bi fuel es x = (some vs0, e₁) ∧ vs = u :: vs0 := by
  rw [denoteArgs'_cons_run] at h
  rcases hd : denote' bi fuel e env with ⟨o, x⟩
  rw [hd] at h
  have key : ∀ u : Value, Plain u →
      ((denoteArgs' bi fuel es x).1.map (u :: ·), (denoteArgs' bi fuel es x).2) =
        (some vs, e₁) →
      ∃ u' x' vs0, (Outcome.val u, x) = (Outcome.val u', x') ∧ Plain u' ∧
        denoteArgs' bi fuel es x' = (some vs0, e₁) ∧ vs = u' :: vs0 := by
    intro u hu h'
    have h1 := congrArg Prod.fst h'
    have h2 := congrArg Prod.snd h'
    rcases hr : denoteArgs' bi fuel es x with ⟨o', x'⟩
    rw [hr] at h1 h2
    dsimp only at h1 h2
    rcases o' with _ | vs0
    · cases h1
    · cases h1; cases h2; exact ⟨u, x, vs0, rfl, hu, hr, rfl⟩
  rcases o with u | _ | _ | _ | _
  · cases u
    case controlFlow k p => dsimp only at h; cases h
    all_goals exact key _ (by intro k p hh; cases hh) h
  all_goals (dsimp only at h; cases h)

/-- A conditional that runs to a value that is not a control-flow value: its condition
    runs to a bit and the arm of that bit runs to the value. -/
theorem denote'_ite_val {bi : Builtins} {fuel : Nat} {c a b : ImpExpr} {env e₁ : Env}
    {v : Value} (h : denote' bi fuel (.ifThenElse c a b) env = (.val v, e₁))
    (hv : Plain v) :
    ∃ k x, denote' bi fuel c env = (.val (.bool k), x) ∧
      denote' bi fuel (if k then a else b) x = (.val v, e₁) := by
  rw [Hax.denote'_ifThenElse_run] at h
  rcases hd : denote' bi fuel c env with ⟨o, x⟩
  rw [hd] at h
  rcases o with u | _ | _ | _ | _
  · cases u
    case bool k => cases k <;> exact ⟨_, x, rfl, h⟩
    case controlFlow k p => dsimp only at h; cases h; exact absurd rfl (hv _ _)
    all_goals (dsimp only at h; cases h)
  all_goals (dsimp only at h; cases h)

/-- A `letBind` that runs to a value that is not a control-flow value: its bound
    expression runs to such a value and its body runs to the value from the extended
    environment. -/
theorem denote'_letBind_val {bi : Builtins} {fuel : Nat} {n : String} {a b : ImpExpr}
    {env e₁ : Env} {v : Value} (h : denote' bi fuel (.letBind n a b) env = (.val v, e₁))
    (hv : Plain v) :
    ∃ u x, denote' bi fuel a env = (.val u, x) ∧ Plain u ∧
      denote' bi fuel b (Hax.Env.extend x n u) = (.val v, e₁) := by
  rw [Hax.denote'_letBind_run] at h
  rcases hd : denote' bi fuel a env with ⟨o, x⟩
  rw [hd] at h
  rcases o with u | _ | _ | _ | _
  · cases u
    case controlFlow k p => dsimp only at h; cases h; exact absurd rfl (hv _ _)
    all_goals exact ⟨_, x, rfl, (by intro k p hh; cases hh), h⟩
  all_goals (dsimp only at h; cases h)

/-- A `seq` that runs to a value that is not a control-flow value: its first expression
    runs to such a value and its second runs to the value from the environment the first
    leaves. -/
theorem denote'_seq_val {bi : Builtins} {fuel : Nat} {a b : ImpExpr}
    {env e₁ : Env} {v : Value} (h : denote' bi fuel (.seq a b) env = (.val v, e₁))
    (hv : Plain v) :
    ∃ u x, denote' bi fuel a env = (.val u, x) ∧ Plain u ∧
      denote' bi fuel b x = (.val v, e₁) := by
  rw [Hax.denote'_seq_run] at h
  rcases hd : denote' bi fuel a env with ⟨o, x⟩
  rw [hd] at h
  rcases o with u | _ | _ | _ | _
  · cases u
    case controlFlow k p => dsimp only at h; cases h; exact absurd rfl (hv _ _)
    all_goals exact ⟨_, x, rfl, (by intro k p hh; cases hh), h⟩
  all_goals (dsimp only at h; cases h)

/-! ## 4. Purity -/

mutual
/-- A `pureForm` expression leaves the environment unchanged. -/
theorem denote'_pureForm_env (bi : Builtins) (fuel : Nat) :
    ∀ (e : ImpExpr) (env : Env), pureForm e = true → (denote' bi fuel e env).2 = env
  | .lit l, env, _ => by rw [Hax.denote'_lit_run]
  | .var x, env, _ => by rw [Hax.denote'_var_run]; cases env x <;> rfl
  | .app f args, env, h => by
      have ih := denoteArgs'_pureForms_env bi fuel args env (by simpa [pureForm] using h)
      rw [denote'_app_run]
      rcases hd : denoteArgs' bi fuel args env with ⟨o, e1⟩
      rw [hd] at ih
      rcases o with _ | vals
      · exact ih
      · dsimp only; split <;> exact ih
  | .ifThenElse c a b, env, h => by
      simp only [pureForm, Bool.and_eq_true] at h
      have ihc := denote'_pureForm_env bi fuel c env h.1.1
      rw [Hax.denote'_ifThenElse_run]
      rcases hd : denote' bi fuel c env with ⟨o, x⟩
      rw [hd] at ihc
      simp only at ihc
      subst ihc
      rcases o with u | _ | _ | _ | _ <;> try rfl
      cases u <;> try rfl
      rename_i k
      cases k
      · exact denote'_pureForm_env bi fuel b x h.2
      · exact denote'_pureForm_env bi fuel a x h.1.2
  | .letBind .., _, h | .lam .., _, h | .tuple .., _, h | .proj .., _, h
  | .match_ .., _, h | .unitVal, _, h | .seq .., _, h | .borrow .., _, h | .deref .., _, h
  | .assign .., _, h | .forLoop .., _, h | .forLoopRev .., _, h | .whileLoop .., _, h
  | .break_ .., _, h | .continue_, _, h | .earlyReturn .., _, h | .questionMark .., _, h
  | .forFold .., _, h | .forFoldRev .., _, h | .whileFold .., _, h
  | .forFoldReturn .., _, h | .forFoldRevReturn .., _, h | .whileFoldReturn .., _, h
  | .cfBreak .., _, h | .cfContinue .., _, h | .cfBreakContinue .., _, h
  | .typeAscription .., _, h => by simp [pureForm] at h
/-- A list of `pureForm` arguments leaves the environment unchanged. -/
theorem denoteArgs'_pureForms_env (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (env : Env), pureForms es = true →
      (denoteArgs' bi fuel es env).2 = env
  | [], env, _ => by rw [denoteArgs'_nil_run]
  | e :: es, env, h => by
      simp only [pureForms, Bool.and_eq_true] at h
      have ihe := denote'_pureForm_env bi fuel e env h.1
      rw [denoteArgs'_cons_run]
      rcases hd : denote' bi fuel e env with ⟨o, x⟩
      rw [hd] at ihe
      simp only at ihe
      subst ihe
      rcases o with u | _ | _ | _ | _ <;> try rfl
      cases u <;> first | rfl | exact denoteArgs'_pureForms_env bi fuel es x h.2
end

/-- The environment a `pureForm` expression leaves is the one it starts from. -/
theorem env_of_pureForm {bi : Builtins} {fuel : Nat} {e : ImpExpr} {env x : Env}
    {o : Outcome} (hp : pureForm e = true) (h : denote' bi fuel e env = (o, x)) :
    x = env := by
  have := denote'_pureForm_env bi fuel e env hp
  rw [h] at this
  exact this

/-! ## 5. The select form -/

mutual
/-- A speculatable expression and its select form are `pureForm`, and the select form is
    `iteFree`. -/
theorem specExpr_forms (ρ : String → Option String) :
    ∀ (e e' : ImpExpr), specExpr ρ e = some e' →
      pureForm e = true ∧ pureForm e' = true ∧ iteFree e' = true
  | .lit l, e', h => by
      unfold specExpr at h; cases h; simp [pureForm, iteFree]
  | .var x, e', h => by
      unfold specExpr at h; cases h; simp [pureForm, iteFree]
  | .app f args, e', h => by
      unfold specExpr at h
      rcases hg : ρ f with _ | g <;> rcases ha : specArgs ρ args with _ | as <;>
        rw [hg, ha] at h <;> try (cases h; done)
      cases h
      have ih := specArgs_forms ρ args as ha
      simp [pureForm, iteFree, ih]
  | .ifThenElse c a b, e', h => by
      unfold specExpr at h
      rcases hc : specExpr ρ c with _ | c' <;> rcases ha : specExpr ρ a with _ | a' <;>
        rcases hb : specExpr ρ b with _ | b' <;> rw [hc, ha, hb] at h <;>
        try (cases h; done)
      cases h
      have ihc := specExpr_forms ρ c c' hc
      have iha := specExpr_forms ρ a a' ha
      have ihb := specExpr_forms ρ b b' hb
      simp [pureForm, pureForms, iteFree, iteFreeL, ihc, iha, ihb]
  | .letBind .., _, h | .lam .., _, h | .tuple .., _, h | .proj .., _, h
  | .match_ .., _, h | .unitVal, _, h | .seq .., _, h | .borrow .., _, h | .deref .., _, h
  | .assign .., _, h | .forLoop .., _, h | .forLoopRev .., _, h | .whileLoop .., _, h
  | .break_ .., _, h | .continue_, _, h | .earlyReturn .., _, h | .questionMark .., _, h
  | .forFold .., _, h | .forFoldRev .., _, h | .whileFold .., _, h
  | .forFoldReturn .., _, h | .forFoldRevReturn .., _, h | .whileFoldReturn .., _, h
  | .cfBreak .., _, h | .cfContinue .., _, h | .cfBreakContinue .., _, h
  | .typeAscription .., _, h => by simp [specExpr] at h
/-- The list counterpart of `specExpr_forms`. -/
theorem specArgs_forms (ρ : String → Option String) :
    ∀ (es es' : List ImpExpr), specArgs ρ es = some es' →
      pureForms es = true ∧ pureForms es' = true ∧ iteFreeL es' = true
  | [], es', h => by
      unfold specArgs at h; cases h; simp [pureForms, iteFreeL]
  | e :: es, es', h => by
      unfold specArgs at h
      rcases he : specExpr ρ e with _ | e' <;> rcases hes : specArgs ρ es with _ | es0 <;>
        rw [he, hes] at h <;> try (cases h; done)
      cases h
      have ihe := specExpr_forms ρ e e' he
      have ihes := specArgs_forms ρ es es0 hes
      simp [pureForms, iteFreeL, ihe, ihes]
end

/-- The select form of a speculatable expression has no conditional. -/
theorem specExpr_iteFree {ρ : String → Option String} {e e' : ImpExpr}
    (h : specExpr ρ e = some e') : iteFree e' = true :=
  (specExpr_forms ρ e e' h).2.2

mutual
/-- **A speculatable expression and its select form run to the same value.** When the
    expression runs to a value that is not a control-flow value and its select form runs
    to a value, the two values are equal. The run of the select form is a hypothesis: a
    select evaluates both arms, so the arm the source does not run has to be defined. -/
theorem specExpr_denote {bi : Builtins} {fuel : Nat} {ρ : String → Option String}
    (hsel : SelectSpec bi) (href : Refines bi ρ) :
    ∀ (e e' : ImpExpr) (env e₁ e₂ : Env) (v w : Value), specExpr ρ e = some e' →
      denote' bi fuel e env = (.val v, e₁) → Plain v →
      denote' bi fuel e' env = (.val w, e₂) → v = w
  | .lit l, e', env, e₁, e₂, v, w, h, hs, _, ht => by
      unfold specExpr at h; cases h; rw [hs] at ht; cases ht; rfl
  | .var x, e', env, e₁, e₂, v, w, h, hs, _, ht => by
      unfold specExpr at h; cases h; rw [hs] at ht; cases ht; rfl
  | .app f args, e', env, e₁, e₂, v, w, h, hs, _, ht => by
      unfold specExpr at h
      rcases hg : ρ f with _ | g <;> rcases ha : specArgs ρ args with _ | as <;>
        rw [hg, ha] at h <;> try (cases h; done)
      cases h
      obtain ⟨vals, hd, hb⟩ := denote'_app_val hs
      obtain ⟨vals', hd', hb'⟩ := denote'_app_val ht
      have hvals := specArgs_denote hsel href args as env e₁ e₂ vals vals' ha hd hd'
      subst hvals
      exact href f g hg vals v w hb hb'
  | .ifThenElse c a b, e', env, e₁, e₂, v, w, h, hs, hv, ht => by
      unfold specExpr at h
      rcases hc : specExpr ρ c with _ | c' <;> rcases ha : specExpr ρ a with _ | a' <;>
        rcases hb : specExpr ρ b with _ | b' <;> rw [hc, ha, hb] at h <;>
        try (cases h; done)
      cases h
      obtain ⟨k, x, hck, hrun⟩ := denote'_ite_val hs hv
      obtain ⟨ws, hd, hsw⟩ := denote'_app_val ht
      obtain ⟨wc, x1, r1, hc1, _, hr1, rfl⟩ := denoteArgs'_cons_some hd
      obtain ⟨wa, x2, r2, ha1, _, hr2, rfl⟩ := denoteArgs'_cons_some hr1
      obtain ⟨wb, x3, r3, hb1, _, hr3, rfl⟩ := denoteArgs'_cons_some hr2
      rw [denoteArgs'_nil_run] at hr3
      cases hr3
      have ex : x = env := env_of_pureForm (specExpr_forms ρ c c' hc).1 hck
      have ex1 : x1 = env := env_of_pureForm (specExpr_forms ρ c c' hc).2.1 hc1
      have ex2 : x2 = x1 := env_of_pureForm (specExpr_forms ρ a a' ha).2.1 ha1
      subst ex
      subst ex1
      subst ex2
      have hkc : Value.bool k = wc :=
        specExpr_denote hsel href c c' _ _ _ _ _ hc hck (by intro k p hh; cases hh) hc1
      subst hkc
      rw [hsel] at hsw
      cases hsw
      cases k
      · exact specExpr_denote hsel href b b' _ _ _ _ _ hb hrun hv hb1
      · exact specExpr_denote hsel href a a' _ _ _ _ _ ha hrun hv ha1
  | .letBind .., _, _, _, _, _, _, h, _, _, _ | .lam .., _, _, _, _, _, _, h, _, _, _
  | .tuple .., _, _, _, _, _, _, h, _, _, _ | .proj .., _, _, _, _, _, _, h, _, _, _
  | .match_ .., _, _, _, _, _, _, h, _, _, _ | .unitVal, _, _, _, _, _, _, h, _, _, _
  | .seq .., _, _, _, _, _, _, h, _, _, _ | .borrow .., _, _, _, _, _, _, h, _, _, _
  | .deref .., _, _, _, _, _, _, h, _, _, _ | .assign .., _, _, _, _, _, _, h, _, _, _
  | .forLoop .., _, _, _, _, _, _, h, _, _, _ | .forLoopRev .., _, _, _, _, _, _, h, _, _, _
  | .whileLoop .., _, _, _, _, _, _, h, _, _, _ | .break_ .., _, _, _, _, _, _, h, _, _, _
  | .continue_, _, _, _, _, _, _, h, _, _, _ | .earlyReturn .., _, _, _, _, _, _, h, _, _, _
  | .questionMark .., _, _, _, _, _, _, h, _, _, _ | .forFold .., _, _, _, _, _, _, h, _, _, _
  | .forFoldRev .., _, _, _, _, _, _, h, _, _, _ | .whileFold .., _, _, _, _, _, _, h, _, _, _
  | .forFoldReturn .., _, _, _, _, _, _, h, _, _, _
  | .forFoldRevReturn .., _, _, _, _, _, _, h, _, _, _
  | .whileFoldReturn .., _, _, _, _, _, _, h, _, _, _
  | .cfBreak .., _, _, _, _, _, _, h, _, _, _ | .cfContinue .., _, _, _, _, _, _, h, _, _, _
  | .cfBreakContinue .., _, _, _, _, _, _, h, _, _, _
  | .typeAscription .., _, _, _, _, _, _, h, _, _, _ => by simp [specExpr] at h
/-- The list counterpart of `specExpr_denote`. -/
theorem specArgs_denote {bi : Builtins} {fuel : Nat} {ρ : String → Option String}
    (hsel : SelectSpec bi) (href : Refines bi ρ) :
    ∀ (es es' : List ImpExpr) (env e₁ e₂ : Env) (vs ws : List Value),
      specArgs ρ es = some es' → denoteArgs' bi fuel es env = (some vs, e₁) →
      denoteArgs' bi fuel es' env = (some ws, e₂) → vs = ws
  | [], es', env, e₁, e₂, vs, ws, h, hs, ht => by
      unfold specArgs at h
      cases h
      rw [denoteArgs'_nil_run] at hs ht
      cases hs
      cases ht
      rfl
  | e :: es, es', env, e₁, e₂, vs, ws, h, hs, ht => by
      unfold specArgs at h
      rcases he : specExpr ρ e with _ | e' <;> rcases hes : specArgs ρ es with _ | es0 <;>
        rw [he, hes] at h <;> try (cases h; done)
      cases h
      obtain ⟨u, x, vs0, hu1, hpu, hr, rfl⟩ := denoteArgs'_cons_some hs
      obtain ⟨u', x', ws0, hu1', _, hr', rfl⟩ := denoteArgs'_cons_some ht
      have ex : x = env := env_of_pureForm (specExpr_forms ρ e e' he).1 hu1
      have ex' : x' = env := env_of_pureForm (specExpr_forms ρ e e' he).2.1 hu1'
      subst ex
      subst ex'
      have h1 : u = u' := specExpr_denote hsel href e e' _ _ _ _ _ he hu1 hpu hu1'
      have h2 : vs0 = ws0 := specArgs_denote hsel href es es0 _ _ _ _ _ hes hr hr'
      rw [h1, h2]
end

/-! ## 6. The pass -/

/-- **The pass preserves the value and the final environment.** When the source runs to
    a value that is not a control-flow value and the result of the pass runs to such a
    value, the two values and the two final environments are equal. -/
theorem desugarIte_denote {bi : Builtins} {fuel : Nat} {ρ : String → Option String}
    (hsel : SelectSpec bi) (href : Refines bi ρ) :
    ∀ (e : ImpExpr) (env e₁ e₂ : Env) (v w : Value),
      denote' bi fuel e env = (.val v, e₁) → Plain v →
      denote' bi fuel (desugarIte ρ e) env = (.val w, e₂) → Plain w → v = w ∧ e₁ = e₂
  | .letBind n a b, env, e₁, e₂, v, w, hs, hv, ht, hw => by
      simp only [desugarIte] at ht
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_letBind_val hs hv
      obtain ⟨u', x', h1', hu', h2'⟩ := denote'_letBind_val ht hw
      obtain ⟨rfl, rfl⟩ := desugarIte_denote hsel href a _ _ _ _ _ h1 hu h1' hu'
      exact desugarIte_denote hsel href b _ _ _ _ _ h2 hv h2' hw
  | .seq a b, env, e₁, e₂, v, w, hs, hv, ht, hw => by
      simp only [desugarIte] at ht
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_seq_val hs hv
      obtain ⟨u', x', h1', hu', h2'⟩ := denote'_seq_val ht hw
      obtain ⟨_, rfl⟩ := desugarIte_denote hsel href a _ _ _ _ _ h1 hu h1' hu'
      exact desugarIte_denote hsel href b _ _ _ _ _ h2 hv h2' hw
  | .ifThenElse c a b, env, e₁, e₂, v, w, hs, hv, ht, _ => by
      simp only [desugarIte] at ht
      rcases hsp : specExpr ρ (.ifThenElse c a b) with _ | e'
      · rw [hsp] at ht
        dsimp only [Option.getD] at ht
        rw [hs] at ht
        cases ht
        exact ⟨rfl, rfl⟩
      · rw [hsp] at ht
        dsimp only [Option.getD] at ht
        have pf := specExpr_forms ρ _ _ hsp
        exact ⟨specExpr_denote hsel href _ _ _ _ _ _ _ hsp hs hv ht,
          (env_of_pureForm pf.1 hs).trans (env_of_pureForm pf.2.1 ht).symm⟩
  | .lit .., _, _, _, _, _, hs, _, ht, _ | .var .., _, _, _, _, _, hs, _, ht, _
  | .app .., _, _, _, _, _, hs, _, ht, _
  | .lam .., _, _, _, _, _, hs, _, ht, _
  | .tuple .., _, _, _, _, _, hs, _, ht, _ | .proj .., _, _, _, _, _, hs, _, ht, _
  | .match_ .., _, _, _, _, _, hs, _, ht, _ | .unitVal, _, _, _, _, _, hs, _, ht, _
  | .borrow .., _, _, _, _, _, hs, _, ht, _
  | .deref .., _, _, _, _, _, hs, _, ht, _ | .assign .., _, _, _, _, _, hs, _, ht, _
  | .forLoop .., _, _, _, _, _, hs, _, ht, _ | .forLoopRev .., _, _, _, _, _, hs, _, ht, _
  | .whileLoop .., _, _, _, _, _, hs, _, ht, _ | .break_ .., _, _, _, _, _, hs, _, ht, _
  | .continue_, _, _, _, _, _, hs, _, ht, _ | .earlyReturn .., _, _, _, _, _, hs, _, ht, _
  | .questionMark .., _, _, _, _, _, hs, _, ht, _ | .forFold .., _, _, _, _, _, hs, _, ht, _
  | .forFoldRev .., _, _, _, _, _, hs, _, ht, _ | .whileFold .., _, _, _, _, _, hs, _, ht, _
  | .forFoldReturn .., _, _, _, _, _, hs, _, ht, _
  | .forFoldRevReturn .., _, _, _, _, _, hs, _, ht, _
  | .whileFoldReturn .., _, _, _, _, _, hs, _, ht, _
  | .cfBreak .., _, _, _, _, _, hs, _, ht, _ | .cfContinue .., _, _, _, _, _, hs, _, ht, _
  | .cfBreakContinue .., _, _, _, _, _, hs, _, ht, _
  | .typeAscription .., _, _, _, _, _, hs, _, ht, _ => by
      simp only [desugarIte] at ht
      rw [hs] at ht
      cases ht
      exact ⟨rfl, rfl⟩

/-- A conditional with a select form: the pass returns an expression without a
    conditional. -/
theorem desugarIte_iteFree_of_spec {ρ : String → Option String} {c a b e' : ImpExpr}
    (h : specExpr ρ (.ifThenElse c a b) = some e') :
    iteFree (desugarIte ρ (.ifThenElse c a b)) = true := by
  simp only [desugarIte, h, Option.getD]
  exact specExpr_iteFree h

/-- The pass on a `letBind` is `iteFree` when it is on the bound expression and on the
    body. -/
theorem desugarIte_iteFree_letBind {ρ : String → Option String} {n : String}
    {v b : ImpExpr} (hv : iteFree (desugarIte ρ v) = true)
    (hb : iteFree (desugarIte ρ b) = true) :
    iteFree (desugarIte ρ (.letBind n v b)) = true := by
  simp [desugarIte, iteFree, hv, hb]

/-- The pass on a `seq` is `iteFree` when it is on both expressions. -/
theorem desugarIte_iteFree_seq {ρ : String → Option String} {a b : ImpExpr}
    (ha : iteFree (desugarIte ρ a) = true) (hb : iteFree (desugarIte ρ b) = true) :
    iteFree (desugarIte ρ (.seq a b)) = true := by
  simp [desugarIte, iteFree, ha, hb]

end CatCrypt.Crypto.Hax.ImpDesugarIte
