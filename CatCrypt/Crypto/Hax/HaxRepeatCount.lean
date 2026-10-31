/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AnfDenote

/-!
# The count of `repeat` read from its literal binding

A-normalisation binds the literal count of `repeat(x, N)` to a fresh name:
`let c = N; let m = repeat(x, c); b`. `repeatCountInline` rewrites every such pair at a
statement position into `let c = N; let m = repeat(x, N); b`, so that the count of the
call is a literal of the call itself. The rewrite leaves every run unchanged
(`repeatCountInline_denote`): after `let c = N` the name `c` holds the value of `N`, and
reading the variable `x` leaves the environment unchanged.

## Main definitions

* `repeatCountBind` — `let c = v; b` with the count of a `repeat` bound first in `b` read
  from `v`, when `v` is a literal and the count is the variable `c`
* `repeatCountInline` — `repeatCountBind` at every `letBind` of a statement position

## Main results

* `repeatCountBind_denote` — `denote'` of `repeatCountBind c v b` is `denote'` of
  `let c = v; b`, at every fuel
* `repeatCountInline_denote` — `denote'` of `repeatCountInline e` is `denote'` of `e`, at
  every fuel
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Builtins denote' denoteArgs' denoteApp'
  denote'_letBind_run denote'_lit_run denote'_var_run)

/-- `let c = v; b` with the count of a `repeat` bound first in `b` read from `v` when `v`
    is a literal and the count is the variable `c`. -/
def repeatCountBind (c : String) (v b : ImpExpr) : ImpExpr :=
  match v, b with
  | .lit l, .letBind m (.app "repeat" [.var x, .var c']) b' =>
      if c' = c then .letBind c (.lit l) (.letBind m (.app "repeat" [.var x, .lit l]) b')
      else .letBind c v b
  | _, _ => .letBind c v b

/-- `repeatCountBind` at every `letBind` of a statement position: the bodies of `letBind`,
    `seq`, the branches of `ifThenElse`, `typeAscription` and the bodies of the folded
    loops. -/
def repeatCountInline : ImpExpr → ImpExpr
  | .letBind c v b => repeatCountBind c v (repeatCountInline b)
  | .seq a b => .seq (repeatCountInline a) (repeatCountInline b)
  | .ifThenElse cnd t e => .ifThenElse cnd (repeatCountInline t) (repeatCountInline e)
  | .typeAscription e ty => .typeAscription (repeatCountInline e) ty
  | .forFold i lo hi b => .forFold i lo hi (repeatCountInline b)
  | .forFoldRev i lo hi b => .forFoldRev i lo hi (repeatCountInline b)
  | .whileFold c b => .whileFold c (repeatCountInline b)
  | .forFoldReturn i lo hi b => .forFoldReturn i lo hi (repeatCountInline b)
  | .forFoldRevReturn i lo hi b => .forFoldRevReturn i lo hi (repeatCountInline b)
  | .whileFoldReturn c b => .whileFoldReturn c (repeatCountInline b)
  | .lit l => .lit l
  | .var x => .var x
  | .lam ps b => .lam ps b
  | .app f args => .app f args
  | .tuple es => .tuple es
  | .proj e i => .proj e i
  | .match_ s arms => .match_ s arms
  | .unitVal => .unitVal
  | .borrow e => .borrow e
  | .deref e => .deref e
  | .assign n r => .assign n r
  | .forLoop v lo hi b => .forLoop v lo hi b
  | .forLoopRev v lo hi b => .forLoopRev v lo hi b
  | .whileLoop c b => .whileLoop c b
  | .break_ e => .break_ e
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn e
  | .questionMark e => .questionMark e
  | .cfBreak e => .cfBreak e
  | .cfContinue e => .cfContinue e
  | .cfBreakContinue e => .cfBreakContinue e

private theorem stateM_bind_run {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (m >>= f) s = (f (m s).1) (m s).2 := rfl

/-- The arguments `[x, c]` and `[x, N]` evaluate alike where `c` holds the value of `N`. -/
theorem denoteArgs'_repeatCount (bi : Builtins) (fuel : Nat) (x c : String) (l : ImpLit)
    (env : Env) (hc : env c = some (Value.ofLit l)) :
    denoteArgs' bi fuel [.var x, .lit l] env = denoteArgs' bi fuel [.var x, .var c] env := by
  simp only [denoteArgs', stateM_bind_run, denote'_var_run]
  rcases env x with _ | vx
  · rfl
  · cases vx <;> simp only [stateM_bind_run, denote'_lit_run, denote'_var_run, hc] <;> rfl

/-- **`repeatCountBind` leaves every run unchanged**: `denote'` of `repeatCountBind c v b`
    is `denote'` of `let c = v; b`, at every fuel. -/
theorem repeatCountBind_denote (bi : Builtins) (fuel : Nat) (c : String) (v b : ImpExpr) :
    denote' bi fuel (repeatCountBind c v b) = denote' bi fuel (.letBind c v b) := by
  funext env
  unfold repeatCountBind
  split
  · rename_i l m x c' b'
    by_cases h : c' = c
    · rw [ite_eq_left h]
      subst h
      rw [denote'_letBind_run, denote'_letBind_run, denote'_lit_run]
      have key : ∀ env1 : Env, env1 c' = some (Value.ofLit l) →
          denote' bi fuel (.letBind m (.app "repeat" [.var x, .lit l]) b') env1 =
          denote' bi fuel (.letBind m (.app "repeat" [.var x, .var c']) b') env1 := by
        intro env1 h1
        rw [denote'_letBind_run, denote'_letBind_run]
        have ha : denote' bi fuel (.app "repeat" [.var x, .lit l]) env1 =
            denote' bi fuel (.app "repeat" [.var x, .var c']) env1 := by
          simp only [denote', denoteApp', stateM_bind_run,
            denoteArgs'_repeatCount bi fuel x c' l env1 h1]
        rw [ha]
      cases l <;> exact key _ (by simp [Env.extend])
    · rw [ite_eq_right h]
  · rfl

/-- Unfold the loop helper at the head of the goal once. -/
local macro "unfold_loop_helper" : tactic => `(tactic| first
  | unfold _root_.Hax.denoteWhile'Return | unfold _root_.Hax.denoteWhile'
  | unfold _root_.Hax.denoteForLoopRev'Return | unfold _root_.Hax.denoteForLoop'Return
  | unfold _root_.Hax.denoteForLoopRev' | unfold _root_.Hax.denoteForLoop')

/-- **`repeatCountInline` leaves every run unchanged**, at every fuel, by the mutual
    induction of `denote'`. -/
theorem repeatCountInline_denote (bi : Builtins) :
    ∀ fuel e, denote' bi fuel (repeatCountInline e) = denote' bi fuel e := by
  intro fuel e
  refine (_root_.Hax.denote'.mutual_induct
    (motive1 := fun fuel e => denote' bi fuel (repeatCountInline e) = denote' bi fuel e)
    (motive2 := fun fuel c b => _root_.Hax.denoteWhile'Return bi fuel c (repeatCountInline b) =
      _root_.Hax.denoteWhile'Return bi fuel c b)
    (motive3 := fun fuel var lo hi body =>
      _root_.Hax.denoteForLoopRev'Return bi fuel var lo hi (repeatCountInline body) =
        _root_.Hax.denoteForLoopRev'Return bi fuel var lo hi body)
    (motive4 := fun fuel var lo hi body =>
      _root_.Hax.denoteForLoop'Return bi fuel var lo hi (repeatCountInline body) =
        _root_.Hax.denoteForLoop'Return bi fuel var lo hi body)
    (motive5 := fun fuel c b => _root_.Hax.denoteWhile' bi fuel c (repeatCountInline b) =
      _root_.Hax.denoteWhile' bi fuel c b)
    (motive6 := fun fuel var lo hi body =>
      _root_.Hax.denoteForLoopRev' bi fuel var lo hi (repeatCountInline body) =
        _root_.Hax.denoteForLoopRev' bi fuel var lo hi body)
    (motive7 := fun fuel var lo hi body =>
      _root_.Hax.denoteForLoop' bi fuel var lo hi (repeatCountInline body) =
        _root_.Hax.denoteForLoop' bi fuel var lo hi body)
    (motive8 := fun _ _ _ => True) (motive9 := fun _ _ _ _ _ => True)
    (motive10 := fun _ _ _ _ _ => True) (motive11 := fun _ _ _ => True)
    (motive12 := fun _ _ => True) (motive13 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_).1 fuel e
  all_goals intros
  all_goals first
    | trivial
    | (simp only [repeatCountInline, repeatCountBind_denote]; simp only [denote', *]; done)
    | (simp only [repeatCountInline]; done)
    | (simp only [repeatCountInline, denote', *]; done)
    | (unfold_loop_helper; simp only [*, ↓reduceIte]; done)

end CatCrypt.Crypto.Hax
