/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.InlineMapClosure
public import HaxLean.Phase.LetIntoBranches
public import HaxLean.Phase.EarlyReturnElim
public import CatCrypt.Crypto.Hax.HaxRepeatCount

/-!
# The preparation steps of the front on `ImpExpr`

The steps of the front that rewrite an extracted function body within `ImpExpr` before
A-normalisation (`haxFrontAnf`, whose body `nfBody` of compileA's front selects), with
their refinements of the source reading. No declaration of this module refers to `LowCT`
or to the translation to it.

1. `inlineSpine` — let-bound local closures inlined.
2. `letsInto` — a binding of an `if`-expression or a block moved into its statements.
3. `inlineMapClosures` — `collect (map (iter s) (lam [p] body))` bound on the spine
   rewritten to a counted loop.

`haxFrontPrep` composes the three. `anfEPick ok a` chooses, by a Boolean test `ok`, among a
body `a`, its rewriting with function-level early returns moved into branches (`ere`) and
the latter with each returned binding `let r = Some(x); r` in tail position replaced by
`Some(x)` (`tailSome`). `repeatCountInline` (`HaxRepeatCount`) reads the literal counts of
`repeat` into the calls.

The source reading of a body is `denoteSpine`: `denote'` with each let-bound closure that
`inlineSpine` inlines read through its closure table. `denote'` errs on a closure, and on a
`map` over a closure literal (`denote'_mapSite_err`); a run of the source that reaches a
`map` binding errs, so the `map` pass is justified on every run of the source that does not
err (`denoteMapSpine_nameMapSources`).

## Main definitions

* `haxFrontFlag` — the flag onto which the front rewrites `while true` loops
* `haxFrontPrep` — steps 1–3
* `isSomeRet`, `tailSome`, `anfEPick` — the returned `Some` bindings and the choice of the
  body by a Boolean test

## Main results

* `tailSome_run`, `anfEPick_run` — the choice keeps the outcome up to `RetRel`
* `denote'_mapSite_err`, `denoteMapSpine_nameMapSources`
* `haxFrontPrep_refines` — steps 1–3 refine the source reading
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Env Outcome Builtins denote' denoteArgs')
open _root_.Hax.InlineLocalClosures (inlineSpine denoteSpine denote'_inlineSpine RefR IsErr)
open _root_.Hax.InlineMap (inlineMapClosures nameMapSources denoteMapSpine
  denote'_inlineMapClosures ArrayOps mapSrc? mapSite?)
open _root_.Hax.LetIntoBranches (letsInto denote'_letsInto)
open _root_.Hax.EarlyReturnElim (ere ere_run RetRel)

/-! ## The steps -/

/-- The flag onto which the front rewrites `while true` loops (`wtFn haxFrontFlag`, in
    `haxFrontBodyP`). -/
def haxFrontFlag : String := "_wt_flag"

/-- Steps 1–3 of the front: let-bound closures inlined, bindings moved into statements,
    `map` over closure literals rewritten to loops. -/
def haxFrontPrep (e : ImpExpr) : ImpExpr := inlineMapClosures (letsInto (inlineSpine e))

/-- `let n = v; b` returns the `Some` value it binds: `v` is `Some(x)` and `b` is `n`. -/
def isSomeRet (n : String) : ImpExpr → ImpExpr → Bool
  | .app "Some" [_], .var r => r == n
  | _, _ => false

/-- The body with each tail `let r = Some(x); r` replaced by `Some(x)`, at the tail of a
    `letBind`, of a `seq`, of both branches of a conditional and of a type ascription. -/
def tailSome : ImpExpr → ImpExpr
  | .letBind n v b => if isSomeRet n v b then v else .letBind n v (tailSome b)
  | .seq a b => .seq a (tailSome b)
  | .ifThenElse c t e => .ifThenElse c (tailSome t) (tailSome e)
  | .typeAscription e t => .typeAscription (tailSome e) t
  | e => e

theorem isSomeRet_eq {n : String} {v b : ImpExpr} (h : isSomeRet n v b = true) :
    b = .var n := by
  unfold isSomeRet at h
  split at h
  · simp only [beq_iff_eq] at h; subst h; rfl
  · cases h

/-- `tailSome` keeps the outcome of every run; the final environment lacks the bindings of
    the returned names. -/
theorem tailSome_run (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) :
    ((denote' bi fuel (tailSome e)).run env).1 = ((denote' bi fuel e).run env).1 := by
  fun_induction tailSome e generalizing env with
  | case1 n v b h =>
    rw [isSomeRet_eq h, _root_.Hax.ContinueFlag.letBind_run]
    rcases (denote' bi fuel v).run env with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w <;> simp [_root_.Hax.ContinueFlag.var_run]
    all_goals rfl
  | case2 n v b h ih =>
    rw [_root_.Hax.ContinueFlag.letBind_run, _root_.Hax.ContinueFlag.letBind_run]
    rcases (denote' bi fuel v).run env with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w <;> first | rfl | exact ih _
    all_goals rfl
  | case3 a b ih =>
    rw [_root_.Hax.ContinueFlag.seq_run, _root_.Hax.ContinueFlag.seq_run]
    rcases (denote' bi fuel a).run env with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w <;> first | rfl | exact ih _
    all_goals rfl
  | case4 c t e iht ihe =>
    rw [_root_.Hax.ContinueFlag.ifThenElse_run, _root_.Hax.ContinueFlag.ifThenElse_run]
    rcases (denote' bi fuel c).run env with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | bool bb =>
        cases bb
        · exact ihe _
        · exact iht _
      | _ => rfl
    all_goals rfl
  | case5 e t ih =>
    simp only [denote']
    exact ih env
  | case6 => rfl

/-- The body chosen by the Boolean test `ok`: `a` when it meets the test, otherwise `ere a`
    (function-level early returns moved into branches) when it meets the test, and otherwise
    `tailSome (ere a)`. -/
def anfEPick (ok : ImpExpr → Bool) (a : ImpExpr) : ImpExpr :=
  if ok a then a else if ok (ere a) then ere a else tailSome (ere a)

/-- Every run of `a` to a value is matched by a run of `anfEPick ok a` from the same
    environment to an outcome related by `RetRel`. -/
theorem anfEPick_run (bi : Builtins) (fuel : Nat) (ok : ImpExpr → Bool) (a : ImpExpr)
    (env env' : Env) (o : Outcome) (ha : (denote' bi fuel a).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    ∃ o' s, (denote' bi fuel (anfEPick ok a)).run env = (o', s) ∧ RetRel o o' := by
  unfold anfEPick
  split
  · exact ⟨o, env', ha, Or.inl rfl⟩
  · obtain ⟨o', he, hrel⟩ := ere_run (bi := bi) (fuel := fuel) a env env' o ha hval
    split
    · exact ⟨o', env', he, hrel⟩
    · refine ⟨o', ((denote' bi fuel (tailSome (ere a))).run env).2, Prod.ext ?_ rfl, hrel⟩
      rw [tailSome_run, he]

/-! ## `map` over a closure literal errs in `denote'` -/

section MapErr

variable (bi : Builtins) (fuel : Nat)

theorem mapSrc?_eq_some {v src : ImpExpr} {p : String} {body : ImpExpr}
    (h : mapSrc? v = some (src, p, body)) :
    v = .app "collect" [.app "map" [.app "iter" [src], .lam [p] body]] := by
  unfold mapSrc? at h
  split at h
  · cases h; rfl
  · cases h

theorem mapSite?_eq_none {v : ImpExpr} (h : mapSrc? v = none) : mapSite? v = none := by
  unfold mapSite?
  split
  · simp [mapSrc?] at h
  · rfl

/-- An argument list ending in a closure literal has no values. -/
theorem denoteArgs'_lam_none (a : ImpExpr) (ps : List String) (b : ImpExpr) (env : Env) :
    ((denoteArgs' bi fuel [a, .lam ps b]).run env).1 = none := by
  have hl : ∀ e1 : Env, ((denoteArgs' bi fuel [.lam ps b]).run e1).1 = none := by
    intro e1
    rw [_root_.Hax.ContinueFlag.args_cons_run]
    simp only [denote']
    rfl
  rw [_root_.Hax.ContinueFlag.args_cons_run]
  rcases (denote' bi fuel a).run env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> simp only [hl, Option.map_none]
  all_goals rfl

/-- `denote'` errs on `collect (map (iter src) (lam [p] body))`. -/
theorem denote'_mapSite_err (src : ImpExpr) (p : String) (body : ImpExpr) (env : Env) :
    IsErr ((denote' bi fuel
      (.app "collect" [.app "map" [.app "iter" [src], .lam [p] body]])).run env).1 := by
  have hn := denoteArgs'_lam_none bi fuel (.app "iter" [src]) [p] body env
  have hin : ∃ m e1, (denote' bi fuel
      (.app "map" [.app "iter" [src], .lam [p] body])).run env = (.err m, e1) := by
    rw [_root_.Hax.ContinueFlag.app_run]
    rcases hr : (denoteArgs' bi fuel [.app "iter" [src], .lam [p] body]).run env with ⟨r, e1⟩
    rw [hr] at hn
    cases hn
    exact ⟨_, e1, rfl⟩
  obtain ⟨m, e1, hm⟩ := hin
  rw [_root_.Hax.ContinueFlag.app_run, _root_.Hax.ContinueFlag.args_cons_run, hm]
  exact ⟨_, rfl⟩

/-- `denote'` errs on a binding of `collect (map (iter src) (lam [p] body))`. -/
theorem denote'_letBind_mapSite_err (z : String) (v k : ImpExpr) {t : ImpExpr × String × ImpExpr}
    (hv : mapSrc? v = some t) (env : Env) :
    IsErr ((denote' bi fuel (.letBind z v k)).run env).1 := by
  obtain ⟨src, p, body⟩ := t
  rw [mapSrc?_eq_some hv, _root_.Hax.ContinueFlag.letBind_run]
  obtain ⟨m, hm⟩ := denote'_mapSite_err bi fuel src p body env
  rcases hr : (denote' bi fuel
      (.app "collect" [.app "map" [.app "iter" [src], .lam [p] body]])).run env with ⟨o, e1⟩
  rw [hr] at hm
  cases hm
  exact ⟨m, rfl⟩

end MapErr

/-- **The `map` pass on the runs of `denote'`.** From one environment, every run of
    `denote'` that does not err is a run of the `map` reading of the program with its
    sources named, to the same outcome and environment. -/
theorem denoteMapSpine_nameMapSources (bi : Builtins) (fuel : Nat) (y : ImpExpr) :
    RefR (fun e₁ e₂ => e₁ = e₂) (fun e₁ e₂ => e₁ = e₂) IsErr
      (denoteMapSpine bi fuel (nameMapSources y)) (denote' bi fuel y) := by
  open _root_.Hax.InlineLocalClosures in
  induction y using ImpExpr.ind with
  | letBind z v k _ ihk =>
    cases hv : mapSrc? v with
    | some t => exact RefR.of_bad (denote'_letBind_mapSite_err bi fuel z v k hv)
    | none =>
      simp only [nameMapSources, hv, denoteMapSpine, mapSite?_eq_none hv, denote']
      refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
        (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
      rcases o with w | _ | _ | _ | _
      · cases w <;> dsimp only <;>
          first
            | exact RefR.pure_mono _ (fun _ _ h => h)
            | exact RefR.modify_mono (fun _ _ h => h ▸ rfl) (fun _ => ihk)
      all_goals (dsimp only; exact RefR.pure_mono _ (fun _ _ h => h))
  | seq a b _ ihb =>
    simp only [nameMapSources, denoteMapSpine, denote']
    refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    rcases o with w | _ | _ | _ | _
    · cases w <;> dsimp only <;>
        first | exact RefR.pure_mono _ (fun _ _ h => h) | exact ihb
    all_goals (dsimp only; exact RefR.pure_mono _ (fun _ _ h => h))
  | _ =>
    simp only [nameMapSources, denoteMapSpine]
    exact RefR.refl _

/-! ## Steps 1–3 refine the source reading -/

/-- **Steps 1–3 refine the source reading.** From one environment, every run of
    `denoteSpine bi fuel e` that does not err is matched by a run of `haxFrontPrep e` to
    the same outcome. -/
theorem haxFrontPrep_refines (bi : Builtins) (fuel : Nat) (hbi : ArrayOps bi) (e : ImpExpr)
    (env env' : Env) (o : Outcome) (hrun : (denoteSpine bi fuel e).run env = (o, env'))
    (ho : ¬ IsErr o) :
    ∃ s, (denote' bi fuel (haxFrontPrep e)).run env = (o, s) := by
  obtain ⟨s₁, h₁, _⟩ := denote'_inlineSpine e bi fuel env env rfl o env' hrun ho
  have h₂ : (denote' bi fuel (letsInto (inlineSpine e))).run env = (o, s₁) := by
    rw [denote'_letsInto]; exact h₁
  obtain ⟨s₃, h₃, _⟩ := denoteMapSpine_nameMapSources bi fuel _ env env rfl o s₁ h₂ ho
  obtain ⟨s₄, h₄, _⟩ := denote'_inlineMapClosures bi fuel hbi _ env env rfl o s₃ h₃ ho
  exact ⟨s₄, h₄⟩

end CatCrypt.Crypto.Hax
