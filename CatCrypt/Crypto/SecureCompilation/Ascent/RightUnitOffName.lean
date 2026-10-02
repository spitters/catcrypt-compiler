/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.KleisliQuotient

/-!
# The Kleisli right unit up to the bound name

`Hax/Ascent/SquareKleisli.lean` composes horizontal arrows with `hcompK` at a name `x`
and has `hidK x` as its identity, so the right unit of that composition is the run of
`.letBind x e (.var x)` against the run of `e`. As an equivalence of squares it is
refuted (`corres_letBind_var_right_not_iff`), and `letBind_var_run_ne_of_unbound`
exhibits an environment at which the two runs differ.

This module bounds that difference to the name `x`. At every fuel and every
environment, the two runs return the same outcome (`letBind_var_outcome_eq`) and their
exit environments agree off `x` (`letBind_var_exit_agreeOff`, over the `EnvAgreeOff` of
`KleisliQuotient.lean`); `letBind_var_right_unit_offName` is the pair of the two.
Neither statement carries a side condition: the `letBind` arm of `denote'` propagates a
control-flow value and an error without running the body, so in those two cases the runs
are equal on the nose (`letBind_var_run_of_cf`, `letBind_var_run_of_not_val`), and in the
plain-value case the exit environment is the leg's extended at `x`
(`letBind_var_exit_extends`). The difference is realised:
`letBind_var_exit_ne_of_unbound` gives an environment at which the two exit environments
are distinct.

`.seq` is a different case. Its exit environment is already the leg's on the nose when
the leg returns a plain value (`seq_var_run`), and what the trailing read changes is the
outcome: `.seq` discards the first leg's value, so the value function of
`.seq e (.var x)` is the value held at `x` rather than the value of `e`. There is no
environment discrepancy to bound.

`Ascent/RustMSquare.lean` proves the corresponding law on the nose for the `RustM`
Kleisli composition (`kseq_pure_right`). No interpretation between the two compositions
is stated here.

## Main results

* `letBind_var_outcome_eq` — the two runs return the same outcome, at every fuel and
  environment and with no side condition.
* `letBind_var_exit_agreeOff` — their exit environments agree at every name other
  than `x`.
* `letBind_var_right_unit_offName` — the conjunction of the two.
* `letBind_var_exit_eq_extend` — in the plain-value case, the composite's exit
  environment is the leg's extended at `x` with the leg's value.
* `letBind_var_run_of_cf`, `letBind_var_run_of_not_val` — the control-flow and
  non-value cases, where the two runs agree outright.
* `letBind_var_exit_ne_of_unbound` — an environment at which the two exit
  environments differ.
* `seq_var_run` — the run of `.seq e (.var x)` on a plain value, where the exit
  environment is the leg's and the outcome is the value held at `x`.

## Main statements

* `letBind_var_run_of_cf`, `letBind_var_run_of_not_val` — the runs are equal when the leg
  returns a control-flow value or does not return a value
* `letBind_var_outcome_eq` — the two runs return the same outcome
* `letBind_var_exit_agreeOff` — the two exit environments agree off `x`
* `letBind_var_right_unit_offName` — the two together
* `letBind_var_exit_eq_extend` — the exit environment in the plain-value case
* `letBind_var_exit_ne_of_unbound` — an environment at which the exit environments differ
* `seq_var_run` — the run of `.seq e (.var x)`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {bi : Builtins}

/-! ## The cases of the composite's run -/

/-- A leg returning a control-flow value: the composite does not run the trailing read,
    so the two runs agree. -/
theorem letBind_var_run_of_cf (fuel : Nat) (x : String) {e : ImpExpr} {env s : Env}
    {b : Bool} {w : Value} (h : denote' bi fuel e env = (.val (.controlFlow b w), s)) :
    denote' bi fuel (.letBind x e (.var x)) env = (.val (.controlFlow b w), s) := by
  simp only [denote', stateM_bind_apply, h]
  rfl

/-- A leg whose outcome is not a value: the composite does not run the trailing read, so
    the two runs agree. -/
theorem letBind_var_run_of_not_val (fuel : Nat) (x : String) {e : ImpExpr} {env s : Env}
    {o : Outcome} (ho : o.isVal = false) (h : denote' bi fuel e env = (o, s)) :
    denote' bi fuel (.letBind x e (.var x)) env = (o, s) := by
  cases o with
  | val v => simp [Outcome.isVal] at ho
  | _ => simp only [denote', stateM_bind_apply, h]; rfl

/-- The exit environment of the composite in the plain-value case: the leg's, extended at
    `x` with the returned value. -/
theorem letBind_var_exit_eq_extend (fuel : Nat) (x : String) {e : ImpExpr} {env s : Env}
    {v : Value} (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false) :
    (denote' bi fuel (.letBind x e (.var x)) env).2 = s.extend x v := by
  rw [letBind_var_exit_extends fuel h hv]

/-! ## The right unit up to the bound name -/

/-- **The two runs return the same outcome**, at every fuel and every environment, with
    no side condition. -/
theorem letBind_var_outcome_eq (fuel : Nat) (x : String) (e : ImpExpr) (env : Env) :
    (denote' bi fuel (.letBind x e (.var x)) env).1 = (denote' bi fuel e env).1 := by
  rcases hr : denote' bi fuel e env with ⟨o, s⟩
  cases o with
  | val v =>
    cases v with
    | controlFlow b w => rw [letBind_var_run_of_cf fuel x hr]
    | _ => rw [letBind_var_exit_extends fuel hr rfl]
  | _ => rw [letBind_var_run_of_not_val fuel x rfl hr]

/-- **The two exit environments agree off `x`**, at every fuel and every environment,
    with no side condition: the composite's binding at `x` is the whole of the
    difference. -/
theorem letBind_var_exit_agreeOff (fuel : Nat) (x : String) (e : ImpExpr) (env : Env) :
    EnvAgreeOff x (denote' bi fuel (.letBind x e (.var x)) env).2
      (denote' bi fuel e env).2 := by
  rcases hr : denote' bi fuel e env with ⟨o, s⟩
  cases o with
  | val v =>
    cases v with
    | controlFlow b w =>
      rw [letBind_var_run_of_cf fuel x hr]
      exact EnvAgreeOff.rfl' x s
    | _ =>
      rw [letBind_var_exit_extends fuel hr rfl]
      exact envAgreeOff_extend x s _
  | _ =>
    rw [letBind_var_run_of_not_val fuel x rfl hr]
    exact EnvAgreeOff.rfl' x s

/-- **The right unit of `hcompK` holds up to the bound name.** The run of
    `.letBind x e (.var x)` and the run of `e` return the same outcome and their exit
    environments agree at every name other than `x`. -/
theorem letBind_var_right_unit_offName (fuel : Nat) (x : String) (e : ImpExpr)
    (env : Env) :
    (denote' bi fuel (.letBind x e (.var x)) env).1 = (denote' bi fuel e env).1 ∧
      EnvAgreeOff x (denote' bi fuel (.letBind x e (.var x)) env).2
        (denote' bi fuel e env).2 :=
  ⟨letBind_var_outcome_eq fuel x e env, letBind_var_exit_agreeOff fuel x e env⟩

/-- The exit environments do differ: at an environment where `x` is unbound, the run of
    `.letBind x .unitVal (.var x)` leaves an exit environment other than the run of
    `.unitVal`. -/
theorem letBind_var_exit_ne_of_unbound (fuel : Nat) (x : String) :
    (denote' bi fuel (.letBind x .unitVal (.var x)) Env.empty).2
      ≠ (denote' bi fuel .unitVal Env.empty).2 := by
  intro h
  exact letBind_var_run_ne_of_unbound fuel x
    (Prod.ext (letBind_var_outcome_eq fuel x .unitVal Env.empty) h)

/-! ## `.seq` against the same law -/

/-- The run of `.seq e (.var x)` after a leg returning a plain value: the exit
    environment is the leg's, and the outcome is the value held at `x`. -/
theorem seq_var_run (fuel : Nat) (x : String) {e : ImpExpr} {env s : Env} {v w : Value}
    (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false)
    (hx : s x = some w) :
    denote' bi fuel (.seq e (.var x)) env = (.val w, s) := by
  rw [denote'_seq bi fuel h hv]
  exact denote'_var bi fuel hx

end Hax.Ascent
