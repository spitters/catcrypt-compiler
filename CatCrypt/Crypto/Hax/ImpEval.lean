/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Semantics
public import HaxLean.Value

/-!
# The value projection of hax-lean's reference semantics

`evalImp` projects the fuel-parametric big-step semantics `denote` of hax-lean to the runs
that end in a value. `forToLoop` reads the loop-functionalised forms `forFold`,
`forFoldRev` and `whileFold`, to which `denote` gives no meaning, as the loops `forLoop`,
`forLoopRev` and `whileLoop` with the same range and body; the source semantics of a
program with such loops is `denote` of `forToLoop e`.

## Main definitions

* `evalImp bi fuel e env` — the value and exit environment of a run of `denote` that ends
  in a value, `none` otherwise
* `forToLoop`, `forToLoopArgs`, `forToLoopArms` — every `forFold`, `forFoldRev` and
  `whileFold` of a program, of a list of programs and of a list of match arms replaced by
  `forLoop`, `forLoopRev` and `whileLoop`

## Main results

* `evalImp_unitVal`, `evalImp_var_some`, `evalImp_typeAscription` — `evalImp` on a unit
  value, a bound variable and a type ascription
* `evalImp_var_inv`, `evalImp_unitVal_inv`, `evalImp_letBind_lit_inv` — a successful
  `evalImp` on a variable, a unit value and a `let` of a literal, inverted
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env Outcome Builtins denote)

/-! ## `evalImp` -/

/-- `evalImp bi fuel e env` returns `some (v, env')` when `denote`
    produces `Outcome.val v` with final env `env'`; `none` otherwise. -/
def evalImp (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) :
    Option (Value × Env) :=
  match (denote bi fuel e).run env with
  | (.val v, env') => some (v, env')
  | _ => none

/-- `unitVal` evaluates to `.unit` with env unchanged. -/
theorem evalImp_unitVal (bi : Builtins) (fuel : Nat) (env : Env) :
    evalImp bi fuel .unitVal env = some (.unit, env) := by
  unfold evalImp denote
  simp only [pure, Pure.pure, StateT.pure, StateT.run]

/-- `var name` evaluates to the env lookup when defined; env unchanged. -/
theorem evalImp_var_some (bi : Builtins) (fuel : Nat) (name : String)
    (env : Env) (v : Value) (h : env name = some v) :
    evalImp bi fuel (.var name) env = some (v, env) := by
  unfold evalImp denote
  simp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
             StateT.get, pure, Pure.pure, StateT.pure, StateT.run, h]

/-- Inverse: extract `env name = some v` and `env' = env` from a
    successful `evalImp` on `.var name`. -/
theorem evalImp_var_inv (bi : Builtins) (fuel : Nat) (name : String)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.var name) env = some (v, env')) :
    env name = some v ∧ env' = env := by
  cases hen : env name with
  | none =>
    exfalso
    unfold evalImp denote at h
    simp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
               StateT.get, pure, Pure.pure, StateT.pure, StateT.run, hen] at h
    cases h
  | some w =>
    have key := evalImp_var_some bi fuel name env w hen
    rw [key] at h
    rw [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨congrArg some h.1, h.2.symm⟩

/-- Inverse: extract `v = .unit` and `env' = env` from a successful
    `evalImp` on `.unitVal`. -/
theorem evalImp_unitVal_inv (bi : Builtins) (fuel : Nat)
    (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel .unitVal env = some (v, env')) :
    v = .unit ∧ env' = env := by
  have key := evalImp_unitVal bi fuel env
  rw [key] at h
  rw [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- `denote` erases a type ascription. -/
theorem denote_typeAscription (bi : Builtins) (fuel : Nat) (e : ImpExpr) (ty : String) :
    denote bi fuel (.typeAscription e ty) = denote bi fuel e := by
  rw [denote]

/-- `evalImp` erases a type ascription. -/
theorem evalImp_typeAscription (bi : Builtins) (fuel : Nat) (e : ImpExpr) (ty : String)
    (env : Env) :
    evalImp bi fuel (.typeAscription e ty) env = evalImp bi fuel e env := by
  unfold evalImp
  rw [denote_typeAscription]

/-- A successful `evalImp` of `letBind name (.lit l) body` is the run of `body` in the
    environment extended at `name` with `Value.ofLit l`. -/
theorem evalImp_letBind_lit_inv (bi : Builtins) (fuel : Nat) (name : String)
    (l : ImpLit) (body : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (h : evalImp bi fuel (.letBind name (.lit l) body) env = some (v, env')) :
    evalImp bi fuel body (env.extend name (Value.ofLit l)) = some (v, env') := by
  unfold evalImp at h ⊢
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure, StateT.pure, modify, modifyGet,
             MonadStateOf.modifyGet, StateT.modifyGet] at h
  exact h

/-! ## `forToLoop` -/

mutual

/-- Every `forFold v lo hi body`, `forFoldRev v lo hi body` and `whileFold c body`
    of a program replaced by `forLoop v lo hi body`, `forLoopRev v lo hi body`
    and `whileLoop c body`, recursively. -/
def forToLoop : ImpExpr → ImpExpr
  | .lit l => .lit l
  | .var n => .var n
  | .letBind n v b => .letBind n (forToLoop v) (forToLoop b)
  | .lam ps b => .lam ps (forToLoop b)
  | .app f args => .app f (forToLoopArgs args)
  | .tuple es => .tuple (forToLoopArgs es)
  | .proj e i => .proj (forToLoop e) i
  | .ifThenElse c t e => .ifThenElse (forToLoop c) (forToLoop t) (forToLoop e)
  | .match_ s arms => .match_ (forToLoop s) (forToLoopArms arms)
  | .unitVal => .unitVal
  | .seq a b => .seq (forToLoop a) (forToLoop b)
  | .borrow e => .borrow (forToLoop e)
  | .deref e => .deref (forToLoop e)
  | .assign n r => .assign n (forToLoop r)
  | .forLoop v lo hi b => .forLoop v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .forLoopRev v lo hi b => .forLoopRev v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .whileLoop c b => .whileLoop (forToLoop c) (forToLoop b)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (forToLoop e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (forToLoop e)
  | .questionMark e => .questionMark (forToLoop e)
  | .forFold v lo hi b => .forLoop v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .forFoldRev v lo hi b => .forLoopRev v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .whileFold c b => .whileLoop (forToLoop c) (forToLoop b)
  | .forFoldReturn v lo hi b => .forFoldReturn v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .whileFoldReturn c b => .whileFoldReturn (forToLoop c) (forToLoop b)
  | .cfBreak e => .cfBreak (forToLoop e)
  | .cfContinue e => .cfContinue (forToLoop e)
  | .cfBreakContinue e => .cfBreakContinue (forToLoop e)
  | .typeAscription e ty => .typeAscription (forToLoop e) ty

/-- `forToLoop` on every element of a list. -/
def forToLoopArgs : List ImpExpr → List ImpExpr
  | [] => []
  | a :: as => forToLoop a :: forToLoopArgs as

/-- `forToLoop` on every arm body. -/
def forToLoopArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
  | [] => []
  | (p, e) :: rest => (p, forToLoop e) :: forToLoopArms rest

end

/-! ## Unfold equations for `denote`

Each lemma states `(denote bi fuel e).run env` for one constructor `e` as a match on the
runs of its sub-expressions, without the `StateT` plumbing. -/

section Unfold

open _root_.Hax (denoteArgs denoteForLoop)

/-- A `.lit` evaluates to `.val (Value.ofLit l)` with the environment unchanged. -/
theorem denote_lit_eq (bi : Builtins) (fuel : Nat) (l : ImpLit) (env : Env) :
    (denote bi fuel (.lit l)).run env = (.val (Value.ofLit l), env) := by
  simp [denote, StateT.run, pure, Pure.pure, StateT.pure]

/-- `.unitVal` evaluates to `.val .unit` with the environment unchanged. -/
theorem denote_unitVal_eq (bi : Builtins) (fuel : Nat) (env : Env) :
    (denote bi fuel .unitVal).run env = (.val .unit, env) := by
  simp [denote, StateT.run, pure, Pure.pure, StateT.pure]

/-- `.var n` runs to the environment lookup (value or undefined-variable error)
    with the environment unchanged. -/
theorem denote_var_run_eq (bi : Builtins) (fuel : Nat) (n : String)
    (env : Env) :
    (denote bi fuel (.var n)).run env =
      ((match env n with
        | some v => Outcome.val v
        | none => Outcome.err s!"undefined variable: {n}"), env) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
             MonadStateOf.get, StateT.get, pure, Pure.pure]
  cases env n <;> rfl

/-- Unfold equation for `.letBind`. -/
theorem denote_letBind_run_eq (bi : Builtins) (fuel : Nat) (n : String)
    (val body : ImpExpr) (env : Env) :
    (denote bi fuel (.letBind n val body)).run env =
      (match (denote bi fuel val).run env with
       | (.val v, env_a) => (denote bi fuel body).run (env_a.extend n v)
       | (other, env_a) => (other, env_a)) := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure,
        modify, modifyGet, MonadStateOf.modifyGet]
  cases denote bi fuel val env with
  | mk a s => cases a <;> rfl

/-- Unfold equation for `.seq`. -/
theorem denote_seq_run_eq (bi : Builtins) (fuel : Nat)
    (e1 e2 : ImpExpr) (env : Env) :
    (denote bi fuel (.seq e1 e2)).run env =
      (match (denote bi fuel e1).run env with
       | (.val _, env_a) => (denote bi fuel e2).run env_a
       | (other, env_a) => (other, env_a)) := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denote bi fuel e1 env with
  | mk a s => cases a <;> rfl

/-- Unfold equation for `.ifThenElse`. -/
theorem denote_ifThenElse_run_eq (bi : Builtins) (fuel : Nat)
    (c t e : ImpExpr) (env : Env) :
    (denote bi fuel (.ifThenElse c t e)).run env =
      (match (denote bi fuel c).run env with
       | (.val (.bool true), env_a) => (denote bi fuel t).run env_a
       | (.val (.bool false), env_a) => (denote bi fuel e).run env_a
       | (.val _, env_a) => (.err "if condition not a bool", env_a)
       | (other, env_a) => (other, env_a)) := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denote bi fuel c env with
  | mk a s =>
    cases a with
    | val v => cases v <;> first | rfl | (rename_i b; cases b <;> rfl)
    | _ => rfl

/-- Unfold equation for `.assign`. -/
theorem denote_assign_run_eq (bi : Builtins) (fuel : Nat) (n : String)
    (rhs : ImpExpr) (env : Env) :
    (denote bi fuel (.assign n rhs)).run env =
      (match (denote bi fuel rhs).run env with
       | (.val v, env_a) => (.val .unit, env_a.extend n v)
       | (other, env_a) => (other, env_a)) := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure,
        modify, modifyGet, MonadStateOf.modifyGet]
  cases denote bi fuel rhs env with
  | mk a s => cases a <;> rfl

/-- Unfold equation for `denoteArgs` on a cons cell.  The recursive
    `denoteArgs bi fuel es` call is kept opaque so it can be rewritten
    by an induction hypothesis. -/
theorem denoteArgs_cons_run_eq (bi : Builtins) (fuel : Nat)
    (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    (denoteArgs bi fuel (e :: es)).run env =
      (match (denote bi fuel e).run env with
       | (.val v, env_a) =>
           (match (denoteArgs bi fuel es).run env_a with
            | (rest, env_b) => (rest.map (v :: ·), env_b))
       | (_, env_a) => (none, env_a)) := by
  have hEq : denoteArgs bi fuel (e :: es) = (do
      let r ← denote bi fuel e
      match r with
      | .val v => do
          let rest ← denoteArgs bi fuel es
          pure (rest.map (v :: ·))
      | _ => pure none) := by
    conv => lhs; unfold denoteArgs
    rfl
  show (denoteArgs bi fuel (e :: es)).run env = _
  rw [hEq]
  simp only [StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  cases denote bi fuel e env with
  | mk a s =>
    rcases a with v | v | v | _ | msg
    · show StateT.bind (denoteArgs bi fuel es) _ s = _
      simp only [StateT.bind]
      cases denoteArgs bi fuel es s with
      | mk rest s2 => rfl
    all_goals rfl

/-- Unfold equation for `.app`. -/
theorem denote_app_run_eq (bi : Builtins) (fuel : Nat) (f : String)
    (args : List ImpExpr) (env : Env) :
    (denote bi fuel (.app f args)).run env =
      (match (denoteArgs bi fuel args).run env with
       | (some vals, env_a) =>
           (match bi f vals with
            | some v => (Outcome.val v, env_a)
            | none => (Outcome.err s!"unknown function or bad args: {f}", env_a))
       | (none, env_a) => (Outcome.err "non-value in function arguments", env_a)) := by
  simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
  rw [show (denoteArgs bi fuel args) env = (denoteArgs bi fuel args).run env from rfl]
  rcases (denoteArgs bi fuel args).run env with ⟨mvals, env_a⟩
  cases mvals with
  | none => rfl
  | some vs =>
    dsimp only
    cases bi f vs <;> rfl

/-- A counted loop whose start is not below its bound runs no trip. -/
theorem denoteForLoop_ge_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : hi ≤ lo) :
    (denoteForLoop bi fuel v lo hi body).run env = (.val .unit, env) := by
  show (denoteForLoop bi fuel v lo hi body).run env = _
  unfold denoteForLoop
  simp [h, StateT.run, pure, Pure.pure, StateT.pure]

/-- A counted loop with a trip left fails at zero fuel. -/
theorem denoteForLoop_zero_run (bi : Builtins) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoop bi 0 v lo hi body).run env = (.err "out of fuel", env) := by
  show (denoteForLoop bi 0 v lo hi body).run env = _
  unfold denoteForLoop
  simp [show ¬ hi ≤ lo by omega, StateT.run, pure, Pure.pure, StateT.pure]

/-- One trip of a counted loop at successor fuel: the body runs at the same fuel
    with the counter bound to the start, and the loop continues from the next
    start at the predecessor fuel. -/
theorem denoteForLoop_succ_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoop bi (fuel + 1) v lo hi body).run env =
      (match (denote bi (fuel + 1) body).run (env.extend v (.int lo)) with
       | (.val _, env_b) => (denoteForLoop bi fuel v (lo + 1) hi body).run env_b
       | (.continued, env_b) => (denoteForLoop bi fuel v (lo + 1) hi body).run env_b
       | (.broke w, env_b) => (.val w, env_b)
       | (other, env_b) => (other, env_b)) := by
  have hFor : denoteForLoop bi (fuel + 1) v lo hi body = (do
      modify (Env.extend · v (.int lo))
      let rb ← denote bi (fuel + 1) body
      match rb with
      | .val _ | .continued => denoteForLoop bi fuel v (lo + 1) hi body
      | .broke w => pure (.val w)
      | other => pure other) := by
    conv => lhs; unfold denoteForLoop
    simp only [show ¬ lo ≥ hi by omega, ite_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
    rfl
  show (denoteForLoop bi (fuel + 1) v lo hi body).run env = _
  rw [hFor]
  simp only [StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  cases denote bi (fuel + 1) body (env.extend v (.int lo)) with
  | mk a s => cases a <;> rfl

/-- Unfold equation for `.forLoop` with integer literal bounds. -/
theorem denote_forLoop_lit_run (bi : Builtins) (fuel : Nat) (v : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) :
    (denote bi fuel (.forLoop v (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (denoteForLoop bi fuel v lo hi body).run env := by
  simp [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure,
    Value.ofLit]

end Unfold

end CatCrypt.Crypto.Hax
