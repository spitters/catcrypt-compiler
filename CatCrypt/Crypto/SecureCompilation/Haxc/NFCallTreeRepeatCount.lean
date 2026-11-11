/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
public import CatCrypt.Crypto.Hax.HaxRepeatCount

/-!
# The literal counts of `repeat` at the level of call trees

The front reads the literal count of a `repeat` into the call (`repeatCountInline`): in
`let c = N; let m = repeat(x, c); b` with a literal `N` the count `c` of the call becomes `N`.
The binding of `c` stays, so the call reads the same arguments, and the reading `denoteT` of the
rewritten expression at every tree table is the reading of the expression: the two call trees are
equal, events and leaves alike.

## Main results

* `denoteT_repeatCountBind`: the reading of `repeatCountBind c v b` is that of `let c = v; b`.
* `denoteT_repeatCountInline`: the reading of `repeatCountInline e` is that of `e`, at every
  tree table and fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount

open _root_.Hax
open CatCrypt.Crypto.Hax (repeatCountBind repeatCountInline)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree

variable {E : EventSig}

/-- A sequence of stateful tree computations runs the first from the state and continues at its
    result and state. -/
theorem tm_bind_run {α β : Type} (x : TM E α) (f : α → TM E β) (s : Env) :
    (x >>= f) s = (x s).bind (fun p => f p.1 p.2) := rfl

/-- A pure stateful tree computation is a leaf at the state. -/
theorem tm_pure_run {α : Type} (a : α) (s : Env) : (pure a : TM E α) s = .ret (a, s) := rfl

/-- The reading of a literal is a leaf with its value. -/
theorem denoteT_lit_run (bt : TreeTable E) (fuel : Nat) (l : ImpLit) (s : Env) :
    denoteT bt fuel (.lit l) s = .ret (.val (Value.ofLit l), s) := by
  rw [denoteT]; rfl

/-- The reading of a variable bound in the state is a leaf with its value. -/
theorem denoteT_var_run (bt : TreeTable E) (fuel : Nat) (x : String) (s : Env) (v : Value)
    (h : s x = some v) : denoteT bt fuel (.var x) s = .ret (.val v, s) := by
  rw [denoteT, tm_bind_run]
  change (match s x with
    | some v => (pure (Outcome.val v) : TM E Outcome)
    | none => pure (.err s!"undefined variable: {x}")) s = _
  rw [h]; rfl

/-- The reading of a variable not bound in the state is a leaf with an error. -/
theorem denoteT_var_run_none (bt : TreeTable E) (fuel : Nat) (x : String) (s : Env)
    (h : s x = none) :
    denoteT bt fuel (.var x) s = .ret (.err s!"undefined variable: {x}", s) := by
  rw [denoteT, tm_bind_run]
  change (match s x with
    | some v => (pure (Outcome.val v) : TM E Outcome)
    | none => pure (.err s!"undefined variable: {x}")) s = _
  rw [h]; rfl

/-- The reading of a binding reads the bound expression, and then the body from the state
    extended by its value. -/
theorem denoteT_letBind_run (bt : TreeTable E) (fuel : Nat) (n : String) (v b : ImpExpr)
    (s : Env) :
    denoteT bt fuel (.letBind n v b) s = (denoteT bt fuel v s).bind (fun p =>
      (match p.1 with
        | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
        | .val w => do modify (Env.extend · n w); denoteT bt fuel b
        | other => pure other : TM E Outcome) p.2) := by
  rw [denoteT]; rfl

/-- The arguments `[x, c]` and `[x, N]` are read alike from an environment where `c` holds the
    value of the literal `N`. -/
theorem denoteArgsT_repeatCount (bt : TreeTable E) (fuel : Nat) (x c : String) (l : ImpLit)
    (env : Env) (hc : env c = some (Value.ofLit l)) :
    denoteArgsT bt fuel [.var x, .lit l] env = denoteArgsT bt fuel [.var x, .var c] env := by
  simp only [denoteArgsT, tm_bind_run]
  rcases hx : env x with _ | vx
  · rw [denoteT_var_run_none bt fuel x env hx]; rfl
  · rw [denoteT_var_run bt fuel x env vx hx]
    simp only [CallTree.bind]
    cases vx <;> simp only [tm_bind_run, denoteT_lit_run, denoteT_var_run bt fuel c env _ hc]

/-- **`repeatCountBind` keeps the call tree**: the reading of `repeatCountBind c v b` at the
    tree table `bt` is the reading of `let c = v; b`, at every fuel. -/
theorem denoteT_repeatCountBind (bt : TreeTable E) (fuel : Nat) (c : String) (v b : ImpExpr) :
    denoteT bt fuel (repeatCountBind c v b) = denoteT bt fuel (.letBind c v b) := by
  unfold repeatCountBind
  split
  · rename_i l m x c' b'
    by_cases h : c' = c
    · rw [ite_eq_left h]
      subst h
      have ha : ∀ env1 : Env, env1 c' = some (Value.ofLit l) →
          denoteT bt fuel (.app "repeat" [.var x, .lit l]) env1 =
            denoteT bt fuel (.app "repeat" [.var x, .var c']) env1 := by
        intro env1 h1
        rw [denoteT, denoteT, denoteAppT, denoteAppT, tm_bind_run, tm_bind_run,
          denoteArgsT_repeatCount bt fuel x c' l env1 h1]
      have hk : ∀ env1 : Env, env1 c' = some (Value.ofLit l) →
          denoteT bt fuel (.letBind m (.app "repeat" [.var x, .lit l]) b') env1 =
            denoteT bt fuel (.letBind m (.app "repeat" [.var x, .var c']) b') env1 := by
        intro env1 h1
        rw [denoteT_letBind_run, denoteT_letBind_run, ha env1 h1]
      funext env
      rw [denoteT_letBind_run, denoteT_letBind_run, denoteT_lit_run]
      cases l <;> exact hk _ (by simp [Value.ofLit, Env.extend])
    · rw [ite_eq_right h]
  · rfl

/-- Unfold the loop reading at the head of the goal once. -/
local macro "unfold_loopT" : tactic => `(tactic| first
  | unfold denoteWhileReturnT | unfold denoteWhileT
  | unfold denoteForLoopRevReturnT | unfold denoteForLoopReturnT
  | unfold denoteForLoopRevT | unfold denoteForLoopT)

/-- **`repeatCountInline` keeps the call tree**: the reading of `repeatCountInline e` at the
    tree table `bt` is the reading of `e`, at every fuel, by the mutual induction of `denote'`. -/
theorem denoteT_repeatCountInline (bt : TreeTable E) :
    ∀ fuel e, denoteT bt fuel (repeatCountInline e) = denoteT bt fuel e := by
  intro fuel e
  refine (_root_.Hax.denote'.mutual_induct
    (motive1 := fun fuel e => denoteT bt fuel (repeatCountInline e) = denoteT bt fuel e)
    (motive2 := fun fuel c b => denoteWhileReturnT bt fuel c (repeatCountInline b) =
      denoteWhileReturnT bt fuel c b)
    (motive3 := fun fuel var lo hi body =>
      denoteForLoopRevReturnT bt fuel var lo hi (repeatCountInline body) =
        denoteForLoopRevReturnT bt fuel var lo hi body)
    (motive4 := fun fuel var lo hi body =>
      denoteForLoopReturnT bt fuel var lo hi (repeatCountInline body) =
        denoteForLoopReturnT bt fuel var lo hi body)
    (motive5 := fun fuel c b => denoteWhileT bt fuel c (repeatCountInline b) =
      denoteWhileT bt fuel c b)
    (motive6 := fun fuel var lo hi body =>
      denoteForLoopRevT bt fuel var lo hi (repeatCountInline body) =
        denoteForLoopRevT bt fuel var lo hi body)
    (motive7 := fun fuel var lo hi body =>
      denoteForLoopT bt fuel var lo hi (repeatCountInline body) =
        denoteForLoopT bt fuel var lo hi body)
    (motive8 := fun _ _ _ => True) (motive9 := fun _ _ _ _ _ => True)
    (motive10 := fun _ _ _ _ _ => True) (motive11 := fun _ _ _ => True)
    (motive12 := fun _ _ => True) (motive13 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_).1 fuel e
  all_goals intros
  all_goals first
    | trivial
    | (simp only [repeatCountInline, denoteT_repeatCountBind]; simp only [denoteT, *])
    | (unfold_loopT; simp only [*, ↓reduceIte])

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount
