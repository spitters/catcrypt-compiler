/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileTop
public import Mathlib.Data.Nat.Find

/-!
# The functional ascent rule for `RWhileNz`

`corresU_while` (`Ascent/WhileTop.lean`) relates a terminating run of the loop node
`.RWhileNz name body` to some abstract state satisfying the invariant. This module
relates it to the value of one abstract function, `loopFun guardA fb`, following
the decompilation of loops into tail-recursive functions of Myreen (TR-765 §2.7), as
adapted to Lean 4 by dhsorens/riscv-decomp (`Tailrec.TerminatesIn`).

A loop is described by an abstract guard `guard : A → Bool` and step
`body : A → A`. `LoopRecIn guard body n a b` is the inductive predicate "the
top-tested loop from `a` exits in `b` after `n` trips"; its least fixpoint is
termination, and the trip count `n` is an index read off the derivation, so no
fuel enters the abstract side. `loopFun guard body a h` is the exit state of a loop
that terminates from `a` (`h : LoopTerminates guard body a`), defined through the
least trip count at which the guard is false.

The node `.RWhileNz` is a do-while: the body runs before the guard is read. Its
abstract function at entry `a` is therefore `loopFun guardA fb (fb a)`.

## Main definitions

* `LoopRecIn`, `LoopRec`, `LoopTerminates` — the trip-indexed loop relation, its
  projection, and termination
* `loopTrips`, `loopFun` — the trip count and the exit state of a terminating loop
* `LoopTerminates.induction`, `loopTerminates_of_measure` — the induction principle
  on terminating states, and termination from a decreasing measure

## Main results

* `LoopRecIn.det`, `loopFun_eq_of_loopRec` — determinism
* `loopFun_of_guard_false`, `loopFun_of_guard_true` — the unfolding equations
* `whileFun_sim` — a terminating do-while run over any body semantics is related to
  the exit state of a `LoopRecIn` derivation, with fewer trips than the fuel
* `whileFun_total` — conversely, a `LoopRecIn` derivation with fewer trips than the
  fuel yields a terminating concrete run related to its exit state
* `corresU_whileFun_terminates`, `corresU_whileFun`, `corresU_whileFun_total` — the
  node rules at `semU`: a terminating run proves termination of the abstract loop
  and is related to `loopFun`; enough fuel makes the run terminate
* `corresU_while_of_loopRec` — the conclusion of `corresU_while`, derived from
  `whileFun_sim` at the abstract state pairing the concrete environment with the
  abstract one
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## A. The abstract loop -/

section AbstractLoop

variable {A : Type} (guard : A → Bool) (body : A → A)

/-- `LoopRecIn guard body n a b`: the top-tested loop with guard `guard` and step
    `body`, started in `a`, exits in `b` after exactly `n` trips. -/
inductive LoopRecIn : Nat → A → A → Prop
  | exit {a : A} : guard a = false → LoopRecIn 0 a a
  | iter {n : Nat} {a b : A} : guard a = true → LoopRecIn n (body a) b → LoopRecIn (n + 1) a b

/-- The loop started in `a` exits in `b` after some number of trips. -/
def LoopRec (a b : A) : Prop := ∃ n, LoopRecIn guard body n a b

/-- The loop started in `a` terminates. -/
def LoopTerminates (a : A) : Prop := ∃ b, LoopRec guard body a b

variable {guard body}

/-- A `LoopRecIn` derivation is the `n`-fold iterate of the step, with the guard
    true before each trip and false at the exit. -/
theorem loopRecIn_iff {n : Nat} {a b : A} :
    LoopRecIn guard body n a b ↔
      (∀ i < n, guard (body^[i] a) = true) ∧ guard (body^[n] a) = false ∧ b = body^[n] a := by
  induction n generalizing a with
  | zero =>
      constructor
      · rintro ⟨hg⟩; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), hg, rfl⟩
      · rintro ⟨-, hg, rfl⟩; exact .exit hg
  | succ n ih =>
      constructor
      · rintro (_ | ⟨hg, h⟩)
        obtain ⟨hlt, hex, rfl⟩ := ih.mp h
        refine ⟨fun i hi => ?_, hex, rfl⟩
        cases i with
        | zero => exact hg
        | succ i => exact hlt i (by omega)
      · rintro ⟨hlt, hex, rfl⟩
        exact .iter (hlt 0 (by omega)) (ih.mpr ⟨fun i hi => hlt (i + 1) (by omega), hex, rfl⟩)

/-- Determinism: the trip count and the exit state are unique. -/
theorem LoopRecIn.det {n m : Nat} {a b c : A} (h₁ : LoopRecIn guard body n a b)
    (h₂ : LoopRecIn guard body m a c) : n = m ∧ b = c := by
  induction h₁ generalizing m c with
  | exit hg =>
      cases h₂ with
      | exit _ => exact ⟨rfl, rfl⟩
      | iter hg' _ => simp [hg] at hg'
  | iter hg _ ih =>
      cases h₂ with
      | exit hg' => simp [hg] at hg'
      | iter _ h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩

/-- The exit state of a loop has the guard false. -/
theorem LoopRecIn.guard_false {n : Nat} {a b : A} (h : LoopRecIn guard body n a b) :
    guard b = false := by
  induction h with
  | exit hg => exact hg
  | iter _ _ ih => exact ih

/-- A step invariant holds at the exit state. -/
theorem LoopRecIn.pres {P : A → Prop} (hinv : ∀ a, P a → P (body a)) {n : Nat} {a b : A}
    (h : LoopRecIn guard body n a b) (ha : P a) : P b := by
  induction h with
  | exit _ => exact ha
  | iter _ _ ih => exact ih (hinv _ ha)

theorem LoopTerminates.exists_exit {a : A} (h : LoopTerminates guard body a) :
    ∃ n, guard (body^[n] a) = false := by
  obtain ⟨_, n, hn⟩ := h
  exact ⟨n, (loopRecIn_iff.mp hn).2.1⟩

variable (guard body)

/-- The number of trips of a terminating loop: the least `n` at which the guard is
    false on the `n`-fold iterate. -/
def loopTrips (a : A) (h : LoopTerminates guard body a) : Nat :=
  Nat.find h.exists_exit

/-- The exit state of a terminating loop. -/
def loopFun (a : A) (h : LoopTerminates guard body a) : A :=
  body^[loopTrips guard body a h] a

variable {guard body}

/-- `loopFun` is the exit state of a `LoopRecIn` derivation with `loopTrips` trips. -/
theorem loopRecIn_loopFun (a : A) (h : LoopTerminates guard body a) :
    LoopRecIn guard body (loopTrips guard body a h) a (loopFun guard body a h) := by
  refine loopRecIn_iff.mpr ⟨fun i hi => ?_, Nat.find_spec h.exists_exit, rfl⟩
  have := Nat.find_min h.exists_exit hi
  simpa using this

theorem loopFun_eq_of_loopRecIn {n : Nat} {a b : A} (hr : LoopRecIn guard body n a b)
    (h : LoopTerminates guard body a) : loopFun guard body a h = b :=
  ((loopRecIn_loopFun a h).det hr).2

theorem loopTrips_eq_of_loopRecIn {n : Nat} {a b : A} (hr : LoopRecIn guard body n a b)
    (h : LoopTerminates guard body a) : loopTrips guard body a h = n :=
  ((loopRecIn_loopFun a h).det hr).1

theorem loopFun_eq_of_loopRec {a b : A} (hr : LoopRec guard body a b)
    (h : LoopTerminates guard body a) : loopFun guard body a h = b :=
  loopFun_eq_of_loopRecIn hr.choose_spec h

theorem LoopTerminates.of_guard_false {a : A} (hg : guard a = false) :
    LoopTerminates guard body a :=
  ⟨a, 0, .exit hg⟩

theorem LoopTerminates.of_body {a : A} (hg : guard a = true)
    (h : LoopTerminates guard body (body a)) : LoopTerminates guard body a := by
  obtain ⟨b, n, hn⟩ := h
  exact ⟨b, n + 1, .iter hg hn⟩

theorem LoopTerminates.step {a : A} (hg : guard a = true) (h : LoopTerminates guard body a) :
    LoopTerminates guard body (body a) := by
  obtain ⟨b, n, hn⟩ := h
  cases hn with
  | exit hg' => simp [hg] at hg'
  | iter _ h' => exact ⟨b, _, h'⟩

/-- Unfolding at a false guard: the loop exits in its entry state. -/
theorem loopFun_of_guard_false {a : A} (hg : guard a = false) (h : LoopTerminates guard body a) :
    loopFun guard body a h = a :=
  loopFun_eq_of_loopRecIn (.exit hg) h

/-- Unfolding at a true guard: the loop is the loop from the stepped state. -/
theorem loopFun_of_guard_true {a : A} (hg : guard a = true) (h : LoopTerminates guard body a) :
    loopFun guard body a h = loopFun guard body (body a) (h.step hg) :=
  loopFun_eq_of_loopRecIn (.iter hg (loopRecIn_loopFun _ _)) h

theorem loopFun_guard_false (a : A) (h : LoopTerminates guard body a) :
    guard (loopFun guard body a h) = false :=
  (loopRecIn_loopFun a h).guard_false

theorem loopFun_pres {P : A → Prop} (hinv : ∀ a, P a → P (body a)) (a : A)
    (h : LoopTerminates guard body a) (ha : P a) : P (loopFun guard body a h) :=
  (loopRecIn_loopFun a h).pres hinv ha

/-- The induction principle on terminating states: a property closed under the exit
    case and under the step case holds on every state from which the loop
    terminates. -/
theorem LoopTerminates.induction {motive : A → Prop}
    (exit : ∀ a, guard a = false → motive a)
    (iter : ∀ a, guard a = true → LoopTerminates guard body (body a) → motive (body a) →
      motive a)
    {a : A} (h : LoopTerminates guard body a) : motive a := by
  obtain ⟨_, _, hn⟩ := h
  induction hn with
  | exit hg => exact exit _ hg
  | iter hg hn ih => exact iter _ hg ⟨_, _, hn⟩ ih

/-- Termination from a measure that decreases on every trip. -/
theorem loopTerminates_of_measure (μ : A → Nat)
    (hdec : ∀ a, guard a = true → μ (body a) < μ a) (a : A) : LoopTerminates guard body a := by
  induction hm : μ a using Nat.strong_induction_on generalizing a with
  | _ m ih =>
      cases hg : guard a with
      | false => exact .of_guard_false hg
      | true => exact .of_body hg (ih _ (hm ▸ hdec a hg) _ rfl)

end AbstractLoop

/-! ## B. Simulation of the do-while by the abstract loop -/

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-- A do-while run that terminates within `fuel` is related to the exit state of the
    abstract loop started after one abstract step, with fewer trips than `fuel`.
    The hypotheses are a body correspondence, a step invariant, and the agreement of
    the concrete guard with the abstract guard on related states. -/
theorem whileFun_sim (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool)
    {P : AState → Prop} {guardA : AState → Bool} {fb : AState → AState}
    (hbody : ∀ env a, SR env a → P a → ∃ env', semBody env = some env' ∧ SR env' (fb a))
    (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guard env = guardA a) :
    ∀ (fuel : Nat) (env : SEnvScalar) (a : AState) (env' : SEnvScalar), SR env a → P a →
      semScalarWhile semBody guard fuel env = some env' →
      ∃ n a', n < fuel ∧ LoopRecIn guardA fb n (fb a) a' ∧ SR env' a' := by
  intro fuel
  induction fuel with
  | zero => intro env a env' _ _ h; simp [semScalarWhile] at h
  | succ k ih =>
      intro env a env' hSR hP h
      obtain ⟨env₁, hstep, hSR₁⟩ := hbody env a hSR hP
      have hg := hguard env₁ (fb a) hSR₁ (hinv a hP)
      simp only [semScalarWhile, hstep] at h
      cases hga : guardA (fb a) with
      | false =>
          rw [hga] at hg
          simp only [hg, Bool.false_eq_true, ite_false, Option.some.injEq] at h
          subst h
          exact ⟨0, fb a, by omega, .exit hga, hSR₁⟩
      | true =>
          rw [hga] at hg
          simp only [hg, ite_true] at h
          obtain ⟨n, a', hn, hrec, hSR'⟩ := ih env₁ (fb a) env' hSR₁ (hinv a hP) h
          exact ⟨n + 1, a', by omega, .iter hga hrec, hSR'⟩

/-- An abstract loop derivation from `fb a` with at most `k` trips yields a
    terminating do-while run within fuel `k + 1`, related to the exit state. -/
theorem whileFun_total (semBody : SEnvScalar → Option SEnvScalar) (guard : SEnvScalar → Bool)
    {P : AState → Prop} {guardA : AState → Bool} {fb : AState → AState}
    (hbody : ∀ env a, SR env a → P a → ∃ env', semBody env = some env' ∧ SR env' (fb a))
    (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guard env = guardA a)
    {n : Nat} {a₀ b : AState} (hrec : LoopRecIn guardA fb n a₀ b) :
    ∀ (k : Nat) (env : SEnvScalar) (a : AState), fb a = a₀ → SR env a → P a → n ≤ k →
      ∃ env', semScalarWhile semBody guard (k + 1) env = some env' ∧ SR env' b := by
  induction hrec with
  | exit hga =>
      intro k env a hfa hSR hP _
      subst hfa
      obtain ⟨env₁, hstep, hSR₁⟩ := hbody env a hSR hP
      have hg := hguard env₁ (fb a) hSR₁ (hinv a hP)
      rw [hga] at hg
      exact ⟨env₁, by simp [semScalarWhile, hstep, hg], hSR₁⟩
  | @iter m a₁ b hga _ ih =>
      intro k env a hfa hSR hP hk
      subst hfa
      obtain ⟨env₁, hstep, hSR₁⟩ := hbody env a hSR hP
      have hg := hguard env₁ (fb a) hSR₁ (hinv a hP)
      rw [hga] at hg
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨env', hrun, hSR'⟩ := ih k' env₁ (fb a) rfl hSR₁ (hinv a hP) (by omega)
      exact ⟨env', by simp only [semScalarWhile, hstep, hg, ite_true]; exact hrun, hSR'⟩

/-! ## C. The node rules at `semU` -/

/-- A terminating run of `.RWhileNz name body` proves that the abstract loop
    terminates from the state after one abstract step. -/
theorem corresU_whileFun_terminates {fuel : Nat} {P : AState → Prop}
    {guardA : AState → Bool} {fb : AState → AState} {name : String} {body : LowCT}
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guardNz name env = guardA a)
    (env : SEnvScalar) (a : AState) (env' : SEnvScalar) (hSR : SR env a) (hP : P a)
    (hrun : semU fuel (.RWhileNz name body) env = some env') :
    LoopTerminates guardA fb (fb a) := by
  rw [semU_rWhileNz] at hrun
  obtain ⟨n, a', -, hrec, -⟩ :=
    whileFun_sim SR (fun e => semU fuel body e) (guardNz name) hbody hinv hguard fuel env a env'
      hSR hP hrun
  exact ⟨a', n, hrec⟩

/-- **The functional ascent `while` rule.** For the loop node `.RWhileNz name body`
    at the unified waist `semU`, from a body correspondence whose abstract step `fb`
    preserves the invariant `P`, and an abstract guard `guardA` agreeing with
    `guardNz name` on related states, a terminating run lands in a state related to
    `loopFun guardA fb (fb a)`, for every proof that the abstract loop terminates
    (`corresU_whileFun_terminates` supplies one from the run). -/
theorem corresU_whileFun {fuel : Nat} {P : AState → Prop}
    {guardA : AState → Bool} {fb : AState → AState} {name : String} {body : LowCT}
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guardNz name env = guardA a)
    (env : SEnvScalar) (a : AState) (env' : SEnvScalar) (hSR : SR env a) (hP : P a)
    (hrun : semU fuel (.RWhileNz name body) env = some env')
    (hterm : LoopTerminates guardA fb (fb a)) :
    SR env' (loopFun guardA fb (fb a) hterm) := by
  rw [semU_rWhileNz] at hrun
  obtain ⟨n, a', -, hrec, hSR'⟩ :=
    whileFun_sim SR (fun e => semU fuel body e) (guardNz name) hbody hinv hguard fuel env a env'
      hSR hP hrun
  rwa [loopFun_eq_of_loopRecIn hrec hterm]

/-- The total form of the functional rule: when the abstract loop terminates from
    `fb a` in fewer trips than `fuel`, the run of `.RWhileNz name body` terminates
    and lands in a state related to `loopFun guardA fb (fb a)`. -/
theorem corresU_whileFun_total {fuel : Nat} {P : AState → Prop}
    {guardA : AState → Bool} {fb : AState → AState} {name : String} {body : LowCT}
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guardNz name env = guardA a)
    (env : SEnvScalar) (a : AState) (hSR : SR env a) (hP : P a)
    (hterm : LoopTerminates guardA fb (fb a)) (hfuel : loopTrips guardA fb (fb a) hterm < fuel) :
    ∃ env', semU fuel (.RWhileNz name body) env = some env' ∧
      SR env' (loopFun guardA fb (fb a) hterm) := by
  rw [semU_rWhileNz]
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hrec := loopRecIn_loopFun (guard := guardA) (body := fb) (fb a) hterm
  have := whileFun_total SR (fun e => semU fuel body e) (guardNz name) hbody hinv hguard hrec
    k env a rfl hSR hP (by omega)
  rwa [← hk] at this

/-- The conclusion of `corresU_while`, derived from `whileFun_sim`. The abstract
    state pairs the concrete environment with the abstract state, so the abstract
    guard is `guardNz name` on the first component and agrees with the concrete
    guard by construction. -/
theorem corresU_while_of_loopRec {fuel : Nat} {P : AState → Prop} {fb : AState → AState}
    {name : String} {body : LowCT}
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (env : SEnvScalar) (a : AState) (env' : SEnvScalar)
    (hSR : SR env a) (hP : P a)
    (hrun : semU fuel (.RWhileNz name body) env = some env') :
    ∃ a', SR env' a' ∧ P a' ∧ guardNz name env' = false := by
  rw [semU_rWhileNz] at hrun
  let SR' : SEnvScalar → SEnvScalar × AState → Prop := fun e p => e = p.1 ∧ SR e p.2
  let fb' : SEnvScalar × AState → SEnvScalar × AState :=
    fun p => ((semU fuel body p.1).getD p.1, fb p.2)
  have hbody' : ∀ e p, SR' e p → P p.2 → ∃ e', semU fuel body e = some e' ∧ SR' e' (fb' p) := by
    rintro e ⟨e₀, a₀⟩ ⟨rfl, hSR₀⟩ hP₀
    obtain ⟨e₁, hstep, hSR₁⟩ := hbody e a₀ hSR₀ hP₀
    exact ⟨e₁, hstep, by simp [fb', hstep], hSR₁⟩
  obtain ⟨n, ⟨e'', a'⟩, -, hrec, rfl, hSR'⟩ :=
    whileFun_sim SR' (fun e => semU fuel body e) (guardNz name) (P := fun p => P p.2)
      (guardA := fun p => guardNz name p.1) hbody' (fun p hp => hinv p.2 hp)
      (by rintro e p ⟨rfl, -⟩ -; rfl) fuel env (env, a) env' ⟨rfl, hSR⟩ hP hrun
  exact ⟨a', hSR', hrec.pres (P := fun p => P p.2) (fun p hp => hinv p.2 hp) (hinv a hP),
    hrec.guard_false⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
