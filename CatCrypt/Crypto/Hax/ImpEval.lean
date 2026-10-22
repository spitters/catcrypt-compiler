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

end CatCrypt.Crypto.Hax
