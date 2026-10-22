/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Corres
public import HaxLean.Runtime

/-!
# Data-dependent and reverse loops in the `denote'` correspondence

## The abstract while loop

A while loop over an accumulator `A` is described by a guard `c : A → Bool` and a step
`f : A → Except B A` (`.error b` stops the loop with `b`, the reading of
`ControlFlow.Break b`). `WhileRecIn c f n a r` is the inductive predicate "the top-tested
loop from `a` stops with `r` after `n` continuing trips"; its derivations are the
terminating runs, and the trip count is an index read off the derivation. `whileLoopE c f a`
is the result of a terminating loop and `.ok a` when the loop does not terminate, the
same totalisation as the runtime's `Hax.whileFold`. `cfToExcept_whileFold` states that
`Hax.whileFold` is `whileLoopE` read through `cfToExcept`.

## The rules

`denote'` runs `.whileFold cond body` through `denoteWhile'`: the condition is evaluated,
on `true` the body runs, a body value `controlFlow true w` stops the loop with `w`, any
other value repeats the loop from the body's exit environment, and on `false` the loop
returns `.unit`. The accumulator is carried by the environment through an invariant
`Inv env σ a`; the condition leads from `Inv` to `InvC`, the body from `InvC` back to `Inv`
at the stepped accumulator (`WhileBody`).

`whileLoop_total` and `whileLoop_sim` are stated for any loop helper satisfying the
one-trip equations of `denoteWhile'` with a classifier `stop` of the body's value, so they
serve `whileFold` (`stopPlain`) and `whileFoldReturn` (`stopReturn`,
`HaxAscent/Ascent/EarlyExit.lean`). `revLoop_corres` is the same for the reverse counted
loop helpers.

## Main results

* `WhileRecIn`, `WhileTerminates`, `whileLoopE`, `whileLoopE_eq_of_rec`,
  `whileTerminates_of_measure`, `cfToExcept_whileFold`
* `whileLoop_total`, `whileLoop_sim` — a derivation gives a run, a value run gives a
  derivation with fewer trips than the fuel
* `corres_whileFold` — the correspondence of `.whileFold cond body` with `whileLoopE`, for
  abstract states from which the loop terminates
* `corres_whileFold_terminates`, `corres_whileFold_run` — a value run of the loop proves
  that the abstract loop terminates and returns `loopVal W σ (whileLoopE …)`
* `corres_whileFold_runtime` — the rule stated with `Hax.whileFold`
* `foldFromRevE`, `foldRangeRevE`, `cfToExcept_forFoldRev`, `revLoop_corres`,
  `corres_forFoldRevE`, `corres_forFoldRev` — the reverse counted loop against
  `Hax.forFoldRev`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## `ControlFlow` as `Except` -/

section CF

variable {A B : Type}

/-- The `Except` reading of a runtime `ControlFlow`: `Break b` is `.error b`,
    `Continue a` is `.ok a`. -/
def cfToExcept : ControlFlow B A → Except B A
  | .Break b => .error b
  | .Continue a => .ok a

/-- The runtime `ControlFlow` of an `Except`. -/
def exceptToCF : Except B A → ControlFlow B A
  | .error b => .Break b
  | .ok a => .Continue a

@[simp] theorem cfToExcept_exceptToCF (r : Except B A) : cfToExcept (exceptToCF r) = r := by
  cases r <;> rfl

@[simp] theorem exceptToCF_cfToExcept (r : ControlFlow B A) : exceptToCF (cfToExcept r) = r := by
  cases r <;> rfl

end CF

/-! ## The abstract while loop -/

section AbstractWhile

variable {A B : Type}

/-- `WhileRecIn c f n a r`: the top-tested loop with guard `c` and step `f`, started in
    `a`, stops with `r` after `n` continuing trips. `r` is `.ok a'` when the guard is
    false in `a'` and `.error b` when a step stops with `b`. -/
inductive WhileRecIn (c : A → Bool) (f : A → Except B A) : Nat → A → Except B A → Prop
  | done {a : A} : c a = false → WhileRecIn c f 0 a (.ok a)
  | brk {a : A} {b : B} : c a = true → f a = .error b → WhileRecIn c f 0 a (.error b)
  | step {n : Nat} {a a' : A} {r : Except B A} :
      c a = true → f a = .ok a' → WhileRecIn c f n a' r → WhileRecIn c f (n + 1) a r

/-- The loop started in `a` terminates. -/
def WhileTerminates (c : A → Bool) (f : A → Except B A) (a : A) : Prop :=
  ∃ n r, WhileRecIn c f n a r

variable {c : A → Bool} {f : A → Except B A}

/-- Determinism: the trip count and the result are unique. -/
theorem WhileRecIn.det {n m : Nat} {a : A} {r s : Except B A} (h₁ : WhileRecIn c f n a r)
    (h₂ : WhileRecIn c f m a s) : n = m ∧ r = s := by
  induction h₁ generalizing m s with
  | done hc =>
    cases h₂ with
    | done _ => exact ⟨rfl, rfl⟩
    | brk hc' _ => simp [hc] at hc'
    | step hc' _ _ => simp [hc] at hc'
  | brk hc hf =>
    cases h₂ with
    | done hc' => simp [hc] at hc'
    | brk _ hf' => rw [hf] at hf'; cases hf'; exact ⟨rfl, rfl⟩
    | step _ hf' _ => rw [hf] at hf'; cases hf'
  | step hc hf _ ih =>
    cases h₂ with
    | done hc' => simp [hc] at hc'
    | brk _ hf' => rw [hf] at hf'; cases hf'
    | step _ hf' h' =>
      rw [hf] at hf'; cases hf'
      obtain ⟨rfl, rfl⟩ := ih h'
      exact ⟨rfl, rfl⟩

variable (c f) in
/-- The result of the loop from `a`: the result of its terminating run, `.ok a` when it
    does not terminate. -/
noncomputable def whileLoopE (a : A) : Except B A :=
  open Classical in
  if h : WhileTerminates c f a then h.choose_spec.choose else .ok a

theorem whileLoopE_eq_of_rec {n : Nat} {a : A} {r : Except B A} (h : WhileRecIn c f n a r) :
    whileLoopE c f a = r := by
  have ht : WhileTerminates c f a := ⟨n, r, h⟩
  unfold whileLoopE
  rw [dif_pos ht]
  exact (ht.choose_spec.choose_spec.det h).2

theorem whileLoopE_of_not_terminates {a : A} (h : ¬ WhileTerminates c f a) :
    whileLoopE c f a = .ok a := by
  unfold whileLoopE
  rw [dif_neg h]

theorem WhileTerminates.of_false {a : A} (hc : c a = false) : WhileTerminates c f a :=
  ⟨0, _, .done hc⟩

theorem WhileTerminates.of_step {a a' : A} (hc : c a = true) (hf : f a = .ok a')
    (h : WhileTerminates c f a') : WhileTerminates c f a := by
  obtain ⟨n, r, hr⟩ := h
  exact ⟨n + 1, r, .step hc hf hr⟩

/-- Termination from a measure that decreases on every continuing trip. -/
theorem whileTerminates_of_measure (μ : A → Nat)
    (hdec : ∀ a a', c a = true → f a = .ok a' → μ a' < μ a) (a : A) :
    WhileTerminates c f a := by
  suffices H : ∀ m a, μ a < m → WhileTerminates c f a from H _ a (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro a hm
    cases hc : c a with
    | false => exact .of_false hc
    | true =>
      cases hf : f a with
      | error b => exact ⟨0, _, .brk hc hf⟩
      | ok a' => exact .of_step hc hf (ih a' (by have := hdec a a' hc hf; omega))

/-- Unfolding at a false guard. -/
theorem whileLoopE_of_false {a : A} (hc : c a = false) : whileLoopE c f a = .ok a :=
  whileLoopE_eq_of_rec (.done hc)

/-- Unfolding at a stopping step. -/
theorem whileLoopE_of_break {a : A} {b : B} (hc : c a = true) (hf : f a = .error b) :
    whileLoopE c f a = .error b :=
  whileLoopE_eq_of_rec (.brk hc hf)

/-- A loop that terminates from `a` with a continuing step terminates from the stepped
    accumulator. -/
theorem WhileTerminates.next {a a' : A} (hc : c a = true) (hf : f a = .ok a')
    (h : WhileTerminates c f a) : WhileTerminates c f a' := by
  obtain ⟨n, r, hr⟩ := h
  cases hr with
  | done hc' => simp [hc] at hc'
  | brk _ hf' => rw [hf] at hf'; cases hf'
  | step _ hf' h' => rw [hf] at hf'; cases hf'; exact ⟨_, _, h'⟩

/-- Unfolding at a continuing step of a terminating loop. -/
theorem whileLoopE_of_step {a a' : A} (hc : c a = true) (hf : f a = .ok a')
    (h : WhileTerminates c f a) : whileLoopE c f a = whileLoopE c f a' := by
  obtain ⟨n, r, hr⟩ := h
  cases hr with
  | done hc' => simp [hc] at hc'
  | brk _ hf' => rw [hf] at hf'; cases hf'
  | step _ hf' h' =>
    rw [hf] at hf'; cases hf'
    rw [whileLoopE_eq_of_rec h', whileLoopE_eq_of_rec (.step hc hf h')]

end AbstractWhile

/-! ## The runtime `whileFold` -/

section RuntimeWhile

variable {A B : Type} {cond : A → Bool} {g : A → ControlFlow B A}

/-- A derivation of the loop is a stopping bounded run of the runtime's while-fold. -/
theorem whileFoldFuel_of_rec {n : Nat} {a : A} {r : Except B A}
    (h : WhileRecIn cond (fun a => cfToExcept (g a)) n a r) :
    ∀ m, n < m → Hax.whileFoldFuel cond g m a = some (exceptToCF r) := by
  induction h with
  | done hc =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [Hax.whileFoldFuel, hc, exceptToCF]
  | @brk a b hc hf =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Hax.whileFoldFuel, hc, if_true]
    cases hg : g a with
    | Break b' => rw [hg] at hf; cases hf; rfl
    | Continue a' => rw [hg] at hf; cases hf
  | @step n a a' r hc hf _ ih =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Hax.whileFoldFuel, hc, if_true]
    cases hg : g a with
    | Break b' => rw [hg] at hf; cases hf
    | Continue a'' => rw [hg] at hf; cases hf; exact ih m (by omega)

/-- A stopping bounded run of the runtime's while-fold is a derivation of the loop. -/
theorem rec_of_whileFoldFuel :
    ∀ (m : Nat) (a : A) (r : ControlFlow B A), Hax.whileFoldFuel cond g m a = some r →
      ∃ n, WhileRecIn cond (fun a => cfToExcept (g a)) n a (cfToExcept r) := by
  intro m
  induction m with
  | zero => intro a r h; simp [Hax.whileFoldFuel] at h
  | succ m ih =>
    intro a r h
    simp only [Hax.whileFoldFuel] at h
    cases hc : cond a with
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      exact ⟨0, .done hc⟩
    | true =>
      rw [hc, if_pos rfl] at h
      cases hg : g a with
      | Break b =>
        rw [hg] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨0, .brk hc (by rw [hg]; rfl)⟩
      | Continue a' =>
        rw [hg] at h
        obtain ⟨n, hn⟩ := ih a' r h
        exact ⟨n + 1, .step hc (by rw [hg]; rfl) hn⟩

/-- **The runtime's while-fold is `whileLoopE`.** -/
theorem cfToExcept_whileFold (a : A) :
    cfToExcept (Hax.whileFold a cond g) = whileLoopE cond (fun a => cfToExcept (g a)) a := by
  by_cases ht : WhileTerminates cond (fun a => cfToExcept (g a)) a
  · obtain ⟨n, r, hr⟩ := ht
    rw [Hax.whileFold_eq_of_fuel (whileFoldFuel_of_rec hr (n + 1) (by omega)),
      whileLoopE_eq_of_rec hr, cfToExcept_exceptToCF]
  · have hs : ¬ Hax.WhileFoldStops a cond g := by
      rintro ⟨m, hm⟩
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hm
      obtain ⟨n, hn⟩ := rec_of_whileFoldFuel m a r hr
      exact ht ⟨n, _, hn⟩
    rw [Hax.whileFold_of_not_stops hs, whileLoopE_of_not_terminates ht]
    rfl

end RuntimeWhile

/-! ## One-trip equations of the while helpers -/

section WhileSteps

variable (bi : Builtins)

/-- The classifier of a `whileFold`/`forFold` body value: `controlFlow true w` stops the
    loop with `w`, any other value continues it. -/
def stopPlain : Value → Option Value
  | .controlFlow true w => some w
  | _ => none

/-- The classifier of a `whileFoldReturn`/`forFoldReturn` body value:
    `controlFlow true (controlFlow false w)` is a loop break with `w`, any other
    `controlFlow true w` an early return propagated as `controlFlow true w`, any other
    value continues the loop. -/
def stopReturn : Value → Option Value
  | .controlFlow true (.controlFlow false w) => some w
  | .controlFlow true w => some (.controlFlow true w)
  | _ => none

theorem denote'_whileFold (fuel : Nat) (cond body : ImpExpr) (env : Env) :
    denote' bi fuel (.whileFold cond body) env = denoteWhile' bi fuel cond body env := by
  simp only [denote']

theorem denote'_whileFoldReturn (fuel : Nat) (cond body : ImpExpr) (env : Env) :
    denote' bi fuel (.whileFoldReturn cond body) env = denoteWhile'Return bi fuel cond body env := by
  simp only [denote']

theorem denoteWhile'_false {fuel : Nat} {cond body : ImpExpr} {env s : Env} (hf : fuel ≠ 0)
    (hc : denote' bi fuel cond env = (.val (.bool false), s)) :
    denoteWhile' bi fuel cond body env = (.val .unit, s) := by
  rw [denoteWhile']
  simp only [if_neg hf, stateM_bind_apply, hc]
  rfl

theorem denoteWhile'_true {fuel : Nat} {cond body : ImpExpr} {env s s' : Env} {v : Value}
    (hf : fuel ≠ 0) (hc : denote' bi fuel cond env = (.val (.bool true), s))
    (hb : denote' bi fuel body s = (.val v, s')) :
    denoteWhile' bi fuel cond body env = match stopPlain v with
      | some w => (.val w, s')
      | none => denoteWhile' bi (fuel - 1) cond body s' := by
  rw [denoteWhile']
  simp only [if_neg hf, stateM_bind_apply, hc]
  simp only [hb]
  cases v with
  | controlFlow b w => cases b <;> rfl
  | _ => rfl

theorem denoteWhile'Return_false {fuel : Nat} {cond body : ImpExpr} {env s : Env}
    (hf : fuel ≠ 0) (hc : denote' bi fuel cond env = (.val (.bool false), s)) :
    denoteWhile'Return bi fuel cond body env = (.val .unit, s) := by
  rw [denoteWhile'Return]
  simp only [if_neg hf, stateM_bind_apply, hc]
  rfl

theorem denoteWhile'Return_true {fuel : Nat} {cond body : ImpExpr} {env s s' : Env}
    {v : Value} (hf : fuel ≠ 0) (hc : denote' bi fuel cond env = (.val (.bool true), s))
    (hb : denote' bi fuel body s = (.val v, s')) :
    denoteWhile'Return bi fuel cond body env = match stopReturn v with
      | some w => (.val w, s')
      | none => denoteWhile'Return bi (fuel - 1) cond body s' := by
  rw [denoteWhile'Return]
  simp only [if_neg hf, stateM_bind_apply, hc]
  simp only [hb]
  cases v with
  | controlFlow b w =>
    cases b
    · rfl
    · cases w with
      | controlFlow b' w' => cases b' <;> rfl
      | _ => rfl
  | _ => rfl

/-- A value run of `denoteWhile'` has positive fuel, a condition run that is not an
    error, and, when the condition is `true`, a body run that is not an error. -/
theorem denoteWhile'_inv {fuel : Nat} {cond body : ImpExpr} {env e' : Env} {w : Value}
    (h : denoteWhile' bi fuel cond body env = (.val w, e')) :
    fuel ≠ 0 ∧ isErr (denote' bi fuel cond env).1 = false ∧
      ∀ s, denote' bi fuel cond env = (.val (.bool true), s) →
        isErr (denote' bi fuel body s).1 = false := by
  rw [denoteWhile'] at h
  by_cases hf : fuel = 0
  · simp only [hf, if_true] at h
    cases h
  refine ⟨hf, ?_, ?_⟩
  · rcases hc : denote' bi fuel cond env with ⟨o, s⟩
    simp only [if_neg hf, stateM_bind_apply, hc] at h
    cases o with
    | err m => cases h
    | _ => rfl
  · intro s hc
    simp only [if_neg hf, stateM_bind_apply, hc] at h
    rcases hb : denote' bi fuel body s with ⟨o, s'⟩
    rw [hb] at h
    cases o with
    | err m => cases h
    | _ => rfl

/-- A value run of `denoteWhile'Return` has positive fuel, a condition run that is not an
    error, and, when the condition is `true`, a body run that is not an error. -/
theorem denoteWhile'Return_inv {fuel : Nat} {cond body : ImpExpr} {env e' : Env}
    {w : Value} (h : denoteWhile'Return bi fuel cond body env = (.val w, e')) :
    fuel ≠ 0 ∧ isErr (denote' bi fuel cond env).1 = false ∧
      ∀ s, denote' bi fuel cond env = (.val (.bool true), s) →
        isErr (denote' bi fuel body s).1 = false := by
  rw [denoteWhile'Return] at h
  by_cases hf : fuel = 0
  · simp only [hf, if_true] at h
    cases h
  refine ⟨hf, ?_, ?_⟩
  · rcases hc : denote' bi fuel cond env with ⟨o, s⟩
    simp only [if_neg hf, stateM_bind_apply, hc] at h
    cases o with
    | err m => cases h
    | _ => rfl
  · intro s hc
    simp only [if_neg hf, stateM_bind_apply, hc] at h
    rcases hb : denote' bi fuel body s with ⟨o, s'⟩
    rw [hb] at h
    cases o with
    | err m => cases h
    | _ => rfl

end WhileSteps

/-! ## The while rule -/

section WhileRule

variable {S A B : Type} {bi : Builtins}

/-- The result of a step as a stop of the loop: `none` for a continuing step, `W σ b`
    for a step stopping with `b`. -/
def stepStop (W : S → B → Value) (σ : S) : Except B A → Option Value
  | .ok _ => none
  | .error b => some (W σ b)

/-- The exit relation of a while loop: `InvC` at the final accumulator when the guard is
    false, the break relation `Brk` when a step stops. -/
def whileExit (InvC : Env → S → A → Prop) (Brk : Env → S → B → Prop) (σ : S) :
    Except B A → Env → Prop
  | .ok a => fun env => InvC env σ a
  | .error b => fun env => Brk env σ b

/-- The condition correspondence of a while loop: from `Inv` at accumulator `a`, the
    condition returns `.bool (c σ a)` and ends in `InvC`. -/
def WhileCond (bi : Builtins) (cond : ImpExpr) (G : S → Prop) (c : S → A → Bool)
    (Inv InvC : Env → S → A → Prop) : Prop :=
  Corres bi (fun env (t : S × A) => Inv env t.1 t.2) (fun t => G t.1) cond
    (fun t => .bool (c t.1 t.2)) (fun env t => InvC env t.1 t.2)

/-- The body correspondence of a while loop: from `InvC` at accumulator `a` with the
    guard true, the body ends in `Inv` at the stepped accumulator when the step continues
    and in `Brk` when it stops. -/
def WhileBody (bi : Builtins) (body : ImpExpr) (G : S → Prop) (c : S → A → Bool)
    (f : S → A → Except B A) (InvC Inv : Env → S → A → Prop) (Brk : Env → S → B → Prop)
    (Vb : S × A → Value) : Prop :=
  Corres bi (fun env (t : S × A) => InvC env t.1 t.2) (fun t => G t.1 ∧ c t.1 t.2 = true) body Vb
    (fun env t => match f t.1 t.2 with
      | .ok a' => Inv env t.1 a'
      | .error b => Brk env t.1 b)

/-- A run of `cond` that is not an error is its eventual run. -/
theorem run_eq_of_corres {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr} {V : S → Value}
    (h : Corres bi P G e V Q) {env : Env} {σ : S} (hP : P env σ) (hG : G σ) (fuel : Nat)
    (hne : isErr (denote' bi fuel e env).1 = false) :
    ∃ env', Q env' σ ∧ denote' bi fuel e env = (.val (V σ), env') := by
  obtain ⟨f₀, e₀, hQ, hrun⟩ := h env σ hP hG
  refine ⟨e₀, hQ, ?_⟩
  rw [← denote'_fuel_mono bi hne (Nat.le_max_left fuel f₀)]
  exact hrun _ (Nat.le_max_right _ _)

variable {cond body : ImpExpr} {L : Nat → Env → Outcome × Env} {stop : Value → Option Value}
  {G : S → Prop} {c : S → A → Bool} {f : S → A → Except B A}
  {Inv InvC : Env → S → A → Prop} {Brk : Env → S → B → Prop} {Vb : S × A → Value}
  {W : S → B → Value}

/-- **A terminating abstract run gives a concrete run.** For a loop helper `L` with the
    one-trip equations of a while loop under the classifier `stop`, a derivation of the
    abstract loop from `a` gives, from any environment satisfying `Inv` at `a`, the run
    returning `loopVal W σ r` at every sufficient fuel. -/
theorem whileLoop_total
    (hLf : ∀ fuel env s, fuel ≠ 0 → denote' bi fuel cond env = (.val (.bool false), s) →
      L fuel env = (.val .unit, s))
    (hLt : ∀ fuel env s s' v, fuel ≠ 0 → denote' bi fuel cond env = (.val (.bool true), s) →
      denote' bi fuel body s = (.val v, s') →
      L fuel env = match stop v with
        | some w => (.val w, s')
        | none => L (fuel - 1) s')
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true → stop (Vb t) = stepStop W t.1 (f t.1 t.2))
    {σ : S} (hG : G σ) {n : Nat} {a : A} {r : Except B A} (hr : WhileRecIn (c σ) (f σ) n a r) :
    ∀ env, Inv env σ a → ∃ fuel₀ env', whileExit InvC Brk σ r env' ∧
      ∀ fuel, fuel₀ ≤ fuel → L fuel env = (.val (loopVal W σ r), env') := by
  induction hr with
  | @done a hc =>
    intro env hInv
    obtain ⟨fc, ec, hQc, rc⟩ := hcond env (σ, a) hInv hG
    refine ⟨max fc 1, ec, hQc, fun fuel hfu => ?_⟩
    have r := rc fuel (by omega)
    simp only [hc] at r
    exact hLf fuel env ec (by omega) r
  | @brk a b hc hf =>
    intro env hInv
    obtain ⟨fc, ec, hQc, rc⟩ := hcond env (σ, a) hInv hG
    obtain ⟨fb, eb, hQb, rb⟩ := hbody ec (σ, a) hQc ⟨hG, hc⟩
    have hVt := hV (σ, a) hG hc
    simp only [hf, stepStop] at hQb hVt
    refine ⟨max (max fc fb) 1, eb, hQb, fun fuel hfu => ?_⟩
    have r := rc fuel (by omega)
    simp only [hc] at r
    rw [hLt fuel env ec eb _ (by omega) r (rb fuel (by omega)), hVt]
    rfl
  | @step n a a' r hc hf _ ih =>
    intro env hInv
    obtain ⟨fc, ec, hQc, rc⟩ := hcond env (σ, a) hInv hG
    obtain ⟨fb, eb, hQb, rb⟩ := hbody ec (σ, a) hQc ⟨hG, hc⟩
    have hVt := hV (σ, a) hG hc
    simp only [hf, stepStop] at hQb hVt
    obtain ⟨fr, er, hQr, rr⟩ := ih eb hQb
    refine ⟨max (max fc fb) (fr + 1), er, hQr, fun fuel hfu => ?_⟩
    have r := rc fuel (by omega)
    simp only [hc] at r
    rw [hLt fuel env ec eb _ (by omega) r (rb fuel (by omega)), hVt]
    exact rr (fuel - 1) (by omega)

/-- **A value run gives a terminating abstract run.** For a loop helper `L` with the
    one-trip equations of a while loop, whose value runs have positive fuel and
    non-error condition and body runs, a value run from an environment satisfying `Inv`
    at `a` is the run of a derivation of the abstract loop with fewer trips than the
    fuel, and ends in the loop's exit relation. -/
theorem whileLoop_sim
    (hLf : ∀ fuel env s, fuel ≠ 0 → denote' bi fuel cond env = (.val (.bool false), s) →
      L fuel env = (.val .unit, s))
    (hLt : ∀ fuel env s s' v, fuel ≠ 0 → denote' bi fuel cond env = (.val (.bool true), s) →
      denote' bi fuel body s = (.val v, s') →
      L fuel env = match stop v with
        | some w => (.val w, s')
        | none => L (fuel - 1) s')
    (hLinv : ∀ fuel env w e', L fuel env = (.val w, e') →
      fuel ≠ 0 ∧ isErr (denote' bi fuel cond env).1 = false ∧
        ∀ s, denote' bi fuel cond env = (.val (.bool true), s) →
          isErr (denote' bi fuel body s).1 = false)
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true → stop (Vb t) = stepStop W t.1 (f t.1 t.2))
    {σ : S} (hG : G σ) :
    ∀ (fuel : Nat) (a : A) (env e' : Env) (w : Value), Inv env σ a →
      L fuel env = (.val w, e') →
      ∃ n r, n < fuel ∧ WhileRecIn (c σ) (f σ) n a r ∧ w = loopVal W σ r ∧
        whileExit InvC Brk σ r e' := by
  intro fuel
  induction fuel with
  | zero =>
    intro a env e' w _ h
    exact absurd rfl (hLinv 0 env w e' h).1
  | succ k ih =>
    intro a env e' w hInv h
    obtain ⟨-, hcne, hbne⟩ := hLinv (k + 1) env w e' h
    obtain ⟨ec, hQc, rc⟩ := run_eq_of_corres hcond (σ := (σ, a)) hInv hG (k + 1) hcne
    cases hc : c σ a with
    | false =>
      simp only [hc] at rc
      rw [hLf (k + 1) env ec (by omega) rc] at h
      simp only [Prod.mk.injEq, Outcome.val.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, .ok a, by omega, .done hc, rfl, hQc⟩
    | true =>
      simp only [hc] at rc
      obtain ⟨eb, hQb, rb⟩ := run_eq_of_corres hbody (σ := (σ, a)) hQc ⟨hG, hc⟩ (k + 1)
        (hbne ec rc)
      have hVt := hV (σ, a) hG hc
      rw [hLt (k + 1) env ec eb _ (by omega) rc rb] at h
      simp only at hQb hVt
      cases hf : f σ a with
      | error b =>
        simp only [hf, stepStop] at hQb hVt
        rw [hVt] at h
        simp only [Prod.mk.injEq, Outcome.val.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨0, .error b, by omega, .brk hc hf, rfl, hQb⟩
      | ok a' =>
        simp only [hf, stepStop] at hQb hVt
        rw [hVt] at h
        simp only [Nat.add_sub_cancel] at h
        obtain ⟨n, r, hn, hr, hw, hx⟩ := ih a' eb e' w hQb h
        exact ⟨n + 1, r, by omega, .step hc hf hr, hw, hx⟩

/-- **The `whileFold` rule.** `.whileFold cond body` corresponds to the abstract loop
    `whileLoopE (c σ) (f σ) (a₀ σ)` on every abstract state satisfying the guard from
    which the loop terminates: it returns `loopVal W σ (whileLoopE …)` (`.unit` on a
    false guard, `W σ b` when a step stops with `b`) and ends in `whileExit`. The
    accumulator is carried by the environment through `Inv`; the condition runs from
    `Inv` to `InvC` and returns `.bool (c σ a)`; a body value classified by `stopPlain`
    agrees with the step. -/
theorem corres_whileFold {P : Env → S → Prop} {a₀ : S → A}
    (hinit : ∀ env σ, P env σ → G σ → Inv env σ (a₀ σ))
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true →
      stopPlain (Vb t) = stepStop W t.1 (f t.1 t.2))
    (hterm : ∀ σ, G σ → WhileTerminates (c σ) (f σ) (a₀ σ)) :
    Corres bi P G (.whileFold cond body)
      (fun σ => loopVal W σ (whileLoopE (c σ) (f σ) (a₀ σ)))
      (fun env σ => whileExit InvC Brk σ (whileLoopE (c σ) (f σ) (a₀ σ)) env) := by
  intro env σ hP hG
  obtain ⟨n, r, hr⟩ := hterm σ hG
  dsimp only
  rw [whileLoopE_eq_of_rec hr]
  obtain ⟨f₀, e₀, hQ, hrun⟩ := whileLoop_total (L := fun fuel env => denoteWhile' bi fuel cond body env)
    (fun fuel env s hf hc => denoteWhile'_false bi hf hc)
    (fun fuel env s s' v hf hc hb => denoteWhile'_true bi hf hc hb)
    hcond hbody hV hG hr env (hinit env σ hP hG)
  exact ⟨f₀, e₀, hQ, fun fuel hf => by rw [denote'_whileFold]; exact hrun fuel hf⟩

/-- **A value run of `whileFold` proves termination.** From an environment related to `σ`
    with the guard, a value run of `.whileFold cond body` at any fuel shows that the
    abstract loop terminates from `a₀ σ`. -/
theorem corres_whileFold_terminates {P : Env → S → Prop} {a₀ : S → A}
    (hinit : ∀ env σ, P env σ → G σ → Inv env σ (a₀ σ))
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true →
      stopPlain (Vb t) = stepStop W t.1 (f t.1 t.2))
    {env e' : Env} {σ : S} {fuel : Nat} {w : Value} (hP : P env σ) (hG : G σ)
    (hrun : denote' bi fuel (.whileFold cond body) env = (.val w, e')) :
    WhileTerminates (c σ) (f σ) (a₀ σ) := by
  rw [denote'_whileFold] at hrun
  obtain ⟨n, r, -, hr, -⟩ := whileLoop_sim (L := fun fuel env => denoteWhile' bi fuel cond body env)
    (fun fuel env s hf hc => denoteWhile'_false bi hf hc)
    (fun fuel env s s' v hf hc hb => denoteWhile'_true bi hf hc hb)
    (fun fuel env w e' h => denoteWhile'_inv bi h)
    hcond hbody hV hG fuel (a₀ σ) env e' w (hinit env σ hP hG) hrun
  exact ⟨n, r, hr⟩

/-- **The partial `whileFold` rule.** A value run of `.whileFold cond body` from an
    environment related to `σ` returns `loopVal W σ (whileLoopE (c σ) (f σ) (a₀ σ))` and
    ends in `whileExit`. -/
theorem corres_whileFold_run {P : Env → S → Prop} {a₀ : S → A}
    (hinit : ∀ env σ, P env σ → G σ → Inv env σ (a₀ σ))
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true →
      stopPlain (Vb t) = stepStop W t.1 (f t.1 t.2))
    {env e' : Env} {σ : S} {fuel : Nat} {w : Value} (hP : P env σ) (hG : G σ)
    (hrun : denote' bi fuel (.whileFold cond body) env = (.val w, e')) :
    w = loopVal W σ (whileLoopE (c σ) (f σ) (a₀ σ)) ∧
      whileExit InvC Brk σ (whileLoopE (c σ) (f σ) (a₀ σ)) e' := by
  rw [denote'_whileFold] at hrun
  obtain ⟨n, r, -, hr, hw, hx⟩ := whileLoop_sim (L := fun fuel env => denoteWhile' bi fuel cond body env)
    (fun fuel env s hf hc => denoteWhile'_false bi hf hc)
    (fun fuel env s s' v hf hc hb => denoteWhile'_true bi hf hc hb)
    (fun fuel env w e' h => denoteWhile'_inv bi h)
    hcond hbody hV hG fuel (a₀ σ) env e' w (hinit env σ hP hG) hrun
  rw [whileLoopE_eq_of_rec hr]
  exact ⟨hw, hx⟩

/-- **The `whileFold` rule against the runtime.** For a step `g σ` in the runtime's
    `ControlFlow`, `.whileFold cond body` returns
    `loopVal W σ (cfToExcept (Hax.whileFold (a₀ σ) (c σ) (g σ)))`. -/
theorem corres_whileFold_runtime {P : Env → S → Prop} {a₀ : S → A}
    {g : S → A → ControlFlow B A}
    (hinit : ∀ env σ, P env σ → G σ → Inv env σ (a₀ σ))
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c (fun σ a => cfToExcept (g σ a)) InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true →
      stopPlain (Vb t) = stepStop W t.1 (cfToExcept (g t.1 t.2)))
    (hterm : ∀ σ, G σ → Hax.WhileFoldStops (a₀ σ) (c σ) (g σ)) :
    Corres bi P G (.whileFold cond body)
      (fun σ => loopVal W σ (cfToExcept (Hax.whileFold (a₀ σ) (c σ) (g σ))))
      (fun env σ => whileExit InvC Brk σ (cfToExcept (Hax.whileFold (a₀ σ) (c σ) (g σ))) env) := by
  simp only [cfToExcept_whileFold]
  refine corres_whileFold hinit hcond hbody hV (fun σ hG => ?_)
  obtain ⟨m, hm⟩ := hterm σ hG
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨n, hn⟩ := rec_of_whileFoldFuel m (a₀ σ) r hr
  exact ⟨n, _, hn⟩

end WhileRule

/-! ## Reverse counted loops -/

section RevLoops

variable {A B : Type}

/-- The reverse fold over `n` indices down from `i` whose step may stop with `.error b`:
    the recursion equation of the runtime's `Hax.forFoldRev.go`. -/
def foldFromRevE (f : Int → A → Except B A) : Nat → Int → A → Except B A
  | 0, _, a => .ok a
  | n + 1, i, a =>
    match f i a with
    | .error b => .error b
    | .ok a' => foldFromRevE f n (i - 1) a'

/-- The reverse fold over `n` indices down from `i`: the recursion equation of the
    runtime's `Hax.foldRangeRev.go`. -/
def foldFromRev (f : Int → A → A) : Nat → Int → A → A
  | 0, _, a => a
  | n + 1, i, a => foldFromRev f n (i - 1) (f i a)

/-- The stopping reverse fold over `[lo, hi)`, from `hi - 1` down to `lo`. -/
def foldRangeRevE (lo hi : Int) (a : A) (f : Int → A → Except B A) : Except B A :=
  foldFromRevE f (hi - lo).toNat (hi - 1) a

/-- The reverse fold over `[lo, hi)`, from `hi - 1` down to `lo`. -/
def foldRangeRevSpec (lo hi : Int) (a : A) (f : Int → A → A) : A :=
  foldFromRev f (hi - lo).toNat (hi - 1) a

theorem foldFromRevE_ok (f : Int → A → A) :
    ∀ (n : Nat) (i : Int) (a : A),
      foldFromRevE (B := B) (fun i a => .ok (f i a)) n i a = .ok (foldFromRev f n i a)
  | 0, _, _ => rfl
  | n + 1, i, a => foldFromRevE_ok f n (i - 1) (f i a)

/-- **The runtime's reverse fold is `foldRangeRevE`.** -/
theorem cfToExcept_forFoldRev (lo hi : Int) (a : A) (g : Int → A → ControlFlow B A) :
    cfToExcept (Hax.forFoldRev lo hi a g) =
      foldRangeRevE lo hi a (fun i a => cfToExcept (g i a)) := by
  unfold Hax.forFoldRev foldRangeRevE
  suffices H : ∀ n i a, cfToExcept (Hax.forFoldRev.go g n i a) =
      foldFromRevE (fun i a => cfToExcept (g i a)) n i a from H _ _ _
  intro n
  induction n with
  | zero => intro i a; rfl
  | succ n ih =>
    intro i a
    simp only [Hax.forFoldRev.go, foldFromRevE]
    cases g i a with
    | Break b => rfl
    | Continue a' => exact ih (i - 1) a'

theorem denote'_forFoldRev (bi : Builtins) (fuel : Nat) {var : String} {lo hi body : ImpExpr}
    {env s1 s2 : Env} {a b : Int}
    (hlo : denote' bi fuel lo env = (.val (.int a), s1))
    (hhi : denote' bi fuel hi s1 = (.val (.int b), s2)) :
    denote' bi fuel (.forFoldRev var lo hi body) env = denoteForLoopRev' bi fuel var a b body s2 := by
  simp only [denote', stateM_bind_apply, hlo, hhi]

theorem denoteForLoopRev'_step (bi : Builtins) {fuel : Nat} (var : String) {a b : Int}
    {body : ImpExpr} {env s : Env} {v : Value} (hab : a < b) (hf : fuel ≠ 0)
    (h : denote' bi fuel body (env.extend var (.int (b - 1))) = (.val v, s)) :
    denoteForLoopRev' bi fuel var a b body env = match stopPlain v with
      | some w => (.val w, s)
      | none => denoteForLoopRev' bi (fuel - 1) var a (b - 1) body s := by
  rw [denoteForLoopRev']
  simp only [if_neg (Int.not_le.mpr hab), if_neg hf, stateM_bind_apply, stateM_modify_apply, h]
  cases v with
  | controlFlow c w => cases c <;> rfl
  | _ => rfl

variable {S : Type} {bi : Builtins}

/-- The body correspondence of a reverse counted loop with loop variable `var`: from an
    environment satisfying the invariant at `i + 1` with `var` bound to `i`, under `G σ`
    and `loF σ ≤ i < hiF σ`, the body ends in the invariant at `i` when the step
    continues and in `Brk` when it stops. -/
def LoopBodyRev (bi : Builtins) (var : String) (body : ImpExpr) (G : S → Prop)
    (loF hiF : S → Int) (f : S → Int → A → Except B A) (Inv : Env → S → Int → A → Prop)
    (Brk : Env → S → B → Prop) (Vb : S × Int × A → Value) : Prop :=
  Corres bi (fun env t => Inv env t.1 (t.2.1 + 1) t.2.2 ∧ env var = some (.int t.2.1))
    (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb
    (fun env t => match f t.1 t.2.1 t.2.2 with
      | .ok a' => Inv env t.1 t.2.1 a'
      | .error b => Brk env t.1 b)

/-- **The run of a reverse loop helper.** For a helper `L fuel lo hi env` with the
    one-trip equations of a reverse counted loop under the classifier `stop`, the run
    over the `n` indices from `j - 1` down to `loF σ` returns
    `loopVal W σ (foldFromRevE (f σ) n (j - 1) a)`. -/
theorem revLoop_corres {var : String} {body : ImpExpr}
    {L : Nat → Int → Int → Env → Outcome × Env} {stop : Value → Option Value}
    (hLd : ∀ fuel lo hi env, hi ≤ lo → L fuel lo hi env = (.val .unit, env))
    (hLs : ∀ fuel lo hi env s v, lo < hi → fuel ≠ 0 →
      denote' bi fuel body (env.extend var (.int (hi - 1))) = (.val v, s) →
      L fuel lo hi env = match stop v with
        | some w => (.val w, s)
        | none => L (fuel - 1) lo (hi - 1) s)
    {G : S → Prop} {loF hiF : S → Int} {f : S → Int → A → Except B A}
    {Inv : Env → S → Int → A → Prop} {Brk : Env → S → B → Prop} {Vb : S × Int × A → Value}
    {W : S → B → Value}
    (hbody : LoopBodyRev bi var body G loF hiF f Inv Brk Vb)
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      stop (Vb t) = stepStop W t.1 (f t.1 t.2.1 t.2.2))
    (hext : ∀ env σ j a, Inv env σ j a → Inv (env.extend var (.int (j - 1))) σ j a) :
    ∀ (n : Nat) (σ : S) (j : Int) (a : A) (env : Env), G σ → loF σ + n = j → j ≤ hiF σ →
      Inv env σ j a →
      ∃ fuel₀ env', loopExit Inv Brk σ (loF σ) (foldFromRevE (f σ) n (j - 1) a) env' ∧
        ∀ fuel, fuel₀ ≤ fuel → L fuel (loF σ) j env =
          (.val (loopVal W σ (foldFromRevE (f σ) n (j - 1) a)), env') := by
  intro n
  induction n with
  | zero =>
    intro σ j a env _ hj _ hInv
    refine ⟨0, env, ?_, fun fuel _ => ?_⟩
    · simp only [foldFromRevE, loopExit]
      rw [show loF σ = j by omega]; exact hInv
    · exact hLd fuel _ _ env (by omega)
  | succ n ih =>
    intro σ j a env hG hj hjh hInv
    have hP : Inv (env.extend var (.int (j - 1))) σ (j - 1 + 1) a ∧
        (env.extend var (.int (j - 1))) var = some (.int (j - 1)) := by
      rw [Int.sub_add_cancel]
      exact ⟨hext env σ j a hInv, Env.extend_same _ _ _⟩
    have h₁ : loF σ ≤ j - 1 := by omega
    have h₂ : j - 1 < hiF σ := by omega
    obtain ⟨fb, e₁, hQ, rb⟩ := hbody (env.extend var (.int (j - 1))) (σ, j - 1, a) hP
      ⟨hG, h₁, h₂⟩
    have hVt := hV (σ, j - 1, a) hG h₁ h₂
    simp only at hQ hVt rb
    cases hf : f σ (j - 1) a with
    | error b =>
      simp only [hf, stepStop] at hQ hVt
      refine ⟨max fb 1, e₁, ?_, fun fuel hfu => ?_⟩
      · simp only [foldFromRevE, hf, loopExit]; exact hQ
      · simp only [foldFromRevE, hf, loopVal]
        rw [hLs fuel _ _ env e₁ _ (by omega) (by omega) (rb fuel (by omega)), hVt]
    | ok a' =>
      simp only [hf, stepStop] at hQ hVt
      obtain ⟨fr, e₂, hQ₂, rr⟩ := ih σ (j - 1) a' e₁ hG (by omega) (by omega) hQ
      refine ⟨max fb (fr + 1), e₂, ?_, fun fuel hfu => ?_⟩
      · simp only [foldFromRevE, hf]; exact hQ₂
      · simp only [foldFromRevE, hf]
        rw [hLs fuel _ _ env e₁ _ (by omega) (by omega) (rb fuel (by omega)), hVt]
        exact rr (fuel - 1) (by omega)

/-- **Reverse counted loop with an exit.** `forFoldRev var lo hi body` over the bounds
    `loF σ ≤ hiF σ` corresponds to the stopping reverse fold
    `foldRangeRevE (loF σ) (hiF σ) (a₀ σ) (f σ)`: it returns `.unit` and ends in the
    invariant at `loF σ` when every step continues, and returns `W σ b` and ends in `Brk`
    when a step stops with `b`. -/
theorem corres_forFoldRevE {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {f : S → Int → A → Except B A} {Inv : Env → S → Int → A → Prop}
    {Brk : Env → S → B → Prop} {Vb : S × Int × A → Value} {W : S → B → Value}
    (hlo : Corres bi P G lo (fun σ => .int (loF σ)) Q₁)
    (hhi : Corres bi Q₁ G hi (fun σ => .int (hiF σ)) Q₂)
    (hinit : ∀ env σ, Q₂ env σ → G σ → Inv env σ (hiF σ) (a₀ σ))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hbody : LoopBodyRev bi var body G loF hiF f Inv Brk Vb)
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      stopPlain (Vb t) = stepStop W t.1 (f t.1 t.2.1 t.2.2))
    (hext : ∀ env σ j a, Inv env σ j a → Inv (env.extend var (.int (j - 1))) σ j a) :
    Corres bi P G (.forFoldRev var lo hi body)
      (fun σ => loopVal W σ (foldRangeRevE (loF σ) (hiF σ) (a₀ σ) (f σ)))
      (fun env σ => loopExit Inv Brk σ (loF σ)
        (foldRangeRevE (loF σ) (hiF σ) (a₀ σ) (f σ)) env) := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG
  obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG
  have hl := hle σ hG
  obtain ⟨f₃, e₃, hQ₃, r₃⟩ := revLoop_corres
    (L := fun fuel lo hi env => denoteForLoopRev' bi fuel var lo hi body env)
    (fun fuel lo hi env h => denoteForLoopRev'_done bi fuel var body env h)
    (fun fuel lo hi env s v hab hf h => denoteForLoopRev'_step bi var hab hf h)
    hbody hV hext ((hiF σ - loF σ).toNat) σ (hiF σ) (a₀ σ) e₂ hG (by omega) (Int.le_refl _)
    (hinit e₂ σ hQ₂ hG)
  refine ⟨max f₁ (max f₂ f₃), e₃, hQ₃, fun fuel hf => ?_⟩
  rw [denote'_forFoldRev bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega))]
  exact r₃ fuel (by omega)

/-- **Reverse counted loop.** `forFoldRev var lo hi body` whose body never breaks
    corresponds to the reverse fold `foldRangeRevSpec (loF σ) (hiF σ) (a₀ σ) (g σ)`: it
    returns `.unit` and ends in the invariant at `loF σ`. -/
theorem corres_forFoldRev {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {g : S → Int → A → A} {Inv : Env → S → Int → A → Prop} {Vb : S × Int × A → Value}
    (hlo : Corres bi P G lo (fun σ => .int (loF σ)) Q₁)
    (hhi : Corres bi Q₁ G hi (fun σ => .int (hiF σ)) Q₂)
    (hinit : ∀ env σ, Q₂ env σ → G σ → Inv env σ (hiF σ) (a₀ σ))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hbody : Corres bi (fun env t => Inv env t.1 (t.2.1 + 1) t.2.2 ∧ env var = some (.int t.2.1))
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb
      (fun env t => Inv env t.1 t.2.1 (g t.1 t.2.1 t.2.2)))
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      stopPlain (Vb t) = none)
    (hext : ∀ env σ j a, Inv env σ j a → Inv (env.extend var (.int (j - 1))) σ j a) :
    Corres bi P G (.forFoldRev var lo hi body) (fun _ => .unit)
      (fun env σ => Inv env σ (loF σ) (foldRangeRevSpec (loF σ) (hiF σ) (a₀ σ) (g σ))) := by
  have h := corres_forFoldRevE (B := Empty) (f := fun σ i a => .ok (g σ i a))
    (Brk := fun _ _ _ => False) (W := fun _ b => nomatch b) hlo hhi hinit hle hbody
    (fun t hG hlo hlt => hV t hG hlo hlt) hext
  refine corres_conseq h (fun _ _ hP _ => hP) (fun _ hG => hG) (fun σ _ => ?_)
    (fun env σ _ hQ => ?_)
  · simp only [foldRangeRevE, foldFromRevE_ok, loopVal]
  · simpa only [foldRangeRevE, foldFromRevE_ok, loopExit, foldRangeRevSpec] using hQ

end RevLoops

end Hax.Ascent
