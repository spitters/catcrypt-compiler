/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.EarlyExit

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

end Hax.Ascent
