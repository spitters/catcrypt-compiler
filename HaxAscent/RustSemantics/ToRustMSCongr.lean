/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMS
public import HaxAscent.Ascent.TableCongr

/-!
# The state-passing reading under two readings of the calls that agree on the called names

`toRustMS app e ρ` consults the reading `app` of the calls only at `.app f args`, with the
name `f` of the call. `Hax.Ascent.callsOK ok e` states that every call of `e` is to a name
accepted by `ok`. Two readings of the calls that are the same function at every accepted
name give the same reading of such an expression from every environment: the same value,
the same failure or the same divergence.

The agreement hypothesis is an equation of functions `app f = app' f`, on every argument
list, so it does not mention the values of the arguments. It holds between a reading and
its restriction to a set of names.

## Main results

* `toRustMS_congr` — the reading is the same under two readings of the calls that agree on
  the called names
* `toRustMS_ok_of_congr` — the same for a value of the reading
* `toRustMS_triple_congr` — the same for a total triple of the reading
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do Hax.Ascent

/-- The conclusion of `toRustMS_congr` for a computation `r` that reads `e` from `ρ`. -/
private def CongrOk (ok : String → Bool) (app' : String → List AVal → RustM AVal)
    (e : Hax.ImpExpr) (ρ : AEnv) (r : RustM (AVal × AEnv)) : Prop :=
  callsOK ok e = true → r = toRustMS app' e ρ

/-- The conclusion of `toRustMS_congr` for a computation `r` that reads the arguments `args`
    from `ρ`. -/
private def CongrArgsOk (ok : String → Bool) (app' : String → List AVal → RustM AVal)
    (args : List Hax.ImpExpr) (ρ : AEnv) (r : RustM (List AVal × AEnv)) : Prop :=
  callsOK.callsOKList ok args = true → r = toRustMS.argsS app' args ρ

/-- **Congruence of the reading in the reading of the calls.** If `app` and `app'` are the
    same function at every name accepted by `ok` and every call of `e` is to such a name,
    the readings of `e` under `app` and under `app'` are equal from every environment. -/
theorem toRustMS_congr {app app' : String → List AVal → RustM AVal} {ok : String → Bool}
    (hag : ∀ f, ok f = true → app f = app' f) (e : Hax.ImpExpr) (ρ : AEnv)
    (hc : callsOK ok e = true) : toRustMS app e ρ = toRustMS app' e ρ := by
  suffices H : ∀ e ρ, CongrOk ok app' e ρ (toRustMS app e ρ) from H e ρ hc
  apply toRustMS.induct_unfolding app (CongrArgsOk ok app') (CongrOk ok app')
  all_goals intros
  case case12 es ρ ih =>
    intro hc
    simp only [callsOK] at hc
    rw [toRustMS_tuple_eq, ← ih hc]
  case case17 f args ρ _ _ _ ih =>
    intro hc
    simp only [callsOK, Bool.and_eq_true] at hc
    rw [toRustMS_app_eq, ← ih hc.2, hag f hc.1]
  case case19 ρ =>
    intro _
    simp only [toRustMS.argsS]
  case case20 a as ρ ih2 ih1 =>
    intro hc
    simp only [callsOK.callsOKList, Bool.and_eq_true] at hc
    simp only [toRustMS.argsS, ← ih2 hc.1, fun p => (ih1 p hc.2).symm]
  all_goals intro hc
  all_goals try simp only [CongrOk] at *
  all_goals try simp only [callsOK, callsOK.callsOKList, Bool.and_eq_true, Bool.and_true] at hc
  all_goals try simp only [toRustMS]
  all_goals try simp_all
  all_goals
    intro p q hpq
    rename_i ihA ihB
    first
      | simp only [fun b => ihA p b, fun b => ihB p b]
      | simp only [fun b => ihB p b]
      | simp only [fun b => ihA p b]

/-- A value of the reading under `app` is the value of the reading under a reading `app'`
    of the calls that agrees with `app` on the called names. -/
theorem toRustMS_ok_of_congr {app app' : String → List AVal → RustM AVal} {ok : String → Bool}
    (hag : ∀ f, ok f = true → app f = app' f) {e : Hax.ImpExpr} (hc : callsOK ok e = true)
    {ρ : AEnv} {r : AVal × AEnv} (h : toRustMS app e ρ = .ok r) :
    toRustMS app' e ρ = .ok r :=
  toRustMS_congr hag e ρ hc ▸ h

/-- A total triple of the reading under `app` is the triple of the reading under a reading
    `app'` of the calls that agrees with `app` on the called names. -/
theorem toRustMS_triple_congr {app app' : String → List AVal → RustM AVal}
    {ok : String → Bool} (hag : ∀ f, ok f = true → app f = app' f) {e : Hax.ImpExpr}
    (hc : callsOK ok e = true) {ρ : AEnv} {Q : AVal × AEnv → Prop}
    (h : ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃⌜True⌝⦄ toRustMS app' e ρ ⦃⇓ r => ⌜Q r⌝⦄ :=
  toRustMS_congr hag e ρ hc ▸ h

end CatCrypt.Hax.RustSemantics
