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

/-- **Congruence of the reading in the reading of the calls.** If `app` and `app'` are the
    same function at every name accepted by `ok` and every call of `e` is to such a name,
    the readings of `e` under `app` and under `app'` are equal from every environment. -/
theorem toRustMS_congr {app app' : String → List AVal → RustM AVal} {ok : String → Bool}
    (hag : ∀ f, ok f = true → app f = app' f) (e : Hax.ImpExpr) (ρ : AEnv)
    (hc : callsOK ok e = true) : toRustMS app e ρ = toRustMS app' e ρ := by
  fun_induction toRustMS app e ρ
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
