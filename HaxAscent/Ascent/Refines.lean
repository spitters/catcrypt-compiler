/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Refinement at three result monads

A concrete semantics `sem : C → Option D` runs from an input state to an output state;
an abstract program runs from `A` to `B` in one of three monads. An abstract program is
`AbsProg ε A B`: a pure function `A → B`, an `Option`-valued one (`none` is guard
failure), or an exception program `A → Option (Except ε B)` (a thrown value is an early
exit). `MonadLevel` orders the three as `pure ≤ option ≤ except`.

`RefinesP` is the forward simulation of a pure function under a precondition and
`RefinesO` that of an `Option`-valued one; the exception level is `RefinesO` at
`Except ε B`. The input relation `SRin` and the output relation `SRout` are separate, so
the same definitions serve a command over one state space (`C = D`, `A = B`) and a
whole-program reading from an entry environment to a result. `AbsProg.Refines` reads
each level over one output relation on `Except ε B`, and the lifting lemmas
`refinesP_iff_refinesO_guard`, `refinesO_iff_refinesO_mapOk` and
`AbsProg.refines_iff_toExcept` state that a program strengthened to a lower level has
the same correspondence as its image one level up.

The vocabulary follows AutoCorres's type strengthening and Sebastian Graf's
AutoCorres-in-Lean port (sgraf812/ascent).

## Main definitions

* `MonadLevel`, `AbsProg`, `AbsProg.level`, `AbsProg.toExcept`, `AbsProg.lift`
* `RefinesP`, `RefinesO`, `AbsProg.Refines`
* `optGuard`, `exceptOk`, `liftOk`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

section Strengthen

variable {C D A B ε : Type}

/-- The result monads of type strengthening: a pure function, an `Option`-valued
    function (`none` is guard failure), an exception program over `Option` (a thrown
    value is an early exit). -/
inductive MonadLevel where
  | pure
  | option
  | except
  deriving DecidableEq, Repr

/-- The position of a level in the order `pure ≤ option ≤ except`. -/
def MonadLevel.rank : MonadLevel → Nat
  | .pure => 0
  | .option => 1
  | .except => 2

instance : LE MonadLevel := ⟨fun l m => l.rank ≤ m.rank⟩

instance (l m : MonadLevel) : Decidable (l ≤ m) :=
  inferInstanceAs (Decidable (l.rank ≤ m.rank))

/-- Forward simulation of a pure abstract function under a precondition: from related
    states with `P a`, the concrete run makes progress to a state related to `f a`. -/
def RefinesP (sem : C → Option D) (SRin : C → A → Prop) (SRout : D → B → Prop)
    (P : A → Prop) (f : A → B) : Prop :=
  ∀ c a, SRin c a → P a → ∃ d, sem c = some d ∧ SRout d (f a)

/-- Forward simulation of an `Option`-valued abstract function: whenever the abstract
    program returns `some b`, the concrete run makes progress to a state related to
    `b`. Abstract failure `none` constrains nothing. -/
def RefinesO (sem : C → Option D) (SRin : C → A → Prop) (SRout : D → B → Prop)
    (f : A → Option B) : Prop :=
  ∀ c a b, SRin c a → f a = some b → ∃ d, sem c = some d ∧ SRout d b

/-- The `Option` program of a pure function under a decidable guard: `f a` when the
    guard holds, failure otherwise. -/
def optGuard (P : A → Prop) [DecidablePred P] (f : A → B) (a : A) : Option B :=
  if P a then some (f a) else none

/-- **Pure to option, under a guard.** A pure refinement under the precondition `P`
    is the `Option` refinement of `optGuard P f`. -/
theorem refinesP_iff_refinesO_guard (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → B → Prop) (P : A → Prop) [DecidablePred P] (f : A → B) :
    RefinesP sem SRin SRout P f ↔ RefinesO sem SRin SRout (optGuard P f) := by
  constructor
  · intro h c a b hSR hf
    unfold optGuard at hf
    by_cases hP : P a
    · rw [ite_eq_left hP, Option.some.injEq] at hf
      subst hf
      exact h c a hSR hP
    · rw [ite_eq_right hP] at hf
      exact absurd hf (by simp)
  · intro h c a hSR hP
    exact h c a (f a) hSR (by simp [optGuard, hP])

/-- **Pure to option.** A pure refinement with no precondition is the `Option`
    refinement of `some ∘ f`. -/
theorem refinesP_true_iff_refinesO_some (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → B → Prop) (f : A → B) :
    RefinesP sem SRin SRout (fun _ => True) f ↔ RefinesO sem SRin SRout (fun a => some (f a)) := by
  constructor
  · intro h c a b hSR hf
    obtain rfl := Option.some.inj hf
    exact h c a hSR trivial
  · intro h c a hSR _
    exact h c a (f a) hSR rfl

/-- **Option to exception.** An `Option` refinement over the normal-result reading
    `SRout d (.ok b)` is the exception refinement of the same program with every
    result tagged `.ok`. -/
theorem refinesO_iff_refinesO_mapOk (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) (f : A → Option B) :
    RefinesO sem SRin (fun d b => SRout d (.ok b)) f ↔
      RefinesO sem SRin SRout (fun a => (f a).map Except.ok) := by
  constructor
  · intro h c a r hSR hf
    dsimp only at hf
    cases hfa : f a with
    | none => rw [hfa] at hf; exact absurd hf (by simp)
    | some b =>
        rw [hfa, Option.map_some, Option.some.injEq] at hf
        subst hf
        exact h c a b hSR hfa
  · intro h c a b hSR hf
    exact h c a (.ok b) hSR (by dsimp only; rw [hf, Option.map_some])

/-- The normal results of an exception program, as an `Option` program: a thrown
    value and a failure both read as `none`. -/
def exceptOk (f : A → Option (Except ε B)) (a : A) : Option B :=
  match f a with
  | some (.ok b) => some b
  | _ => none

/-- An exception program that never throws is the `.ok`-image of its normal
    results. -/
theorem exceptOk_mapOk_of_noThrow (f : A → Option (Except ε B))
    (h : ∀ a e, f a ≠ some (.error e)) (a : A) :
    (exceptOk f a).map Except.ok = f a := by
  unfold exceptOk
  rcases hfa : f a with _ | (e | b)
  · rfl
  · exact absurd hfa (h a e)
  · rfl

/-- **Exception to option.** An exception program that never throws refines exactly
    when its normal results refine at the `Option` level. -/
theorem refinesO_except_iff_exceptOk (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) (f : A → Option (Except ε B))
    (h : ∀ a e, f a ≠ some (.error e)) :
    RefinesO sem SRin SRout f ↔ RefinesO sem SRin (fun d b => SRout d (.ok b)) (exceptOk f) := by
  rw [refinesO_iff_refinesO_mapOk]
  have hf : (fun a => (exceptOk f a).map Except.ok) = f := funext (exceptOk_mapOk_of_noThrow f h)
  rw [hf]

/-- **Option to pure.** An `Option` program that never fails refines exactly when the
    pure function of its results refines with no precondition. -/
theorem refinesO_iff_refinesP_of_total (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → B → Prop) (fo : A → Option B) (f : A → B) (h : ∀ a, fo a = some (f a)) :
    RefinesO sem SRin SRout fo ↔ RefinesP sem SRin SRout (fun _ => True) f := by
  have hf : fo = fun a => some (f a) := funext h
  rw [hf, refinesP_true_iff_refinesO_some]

/-- An abstract program at one of the three levels. -/
inductive AbsProg (ε A B : Type) where
  | pure (f : A → B)
  | option (f : A → Option B)
  | except (f : A → Option (Except ε B))

/-- The level of an abstract program. -/
def AbsProg.level : AbsProg ε A B → MonadLevel
  | .pure _ => .pure
  | .option _ => .option
  | .except _ => .except

/-- The image of an abstract program in the exception monad. -/
def AbsProg.toExcept : AbsProg ε A B → A → Option (Except ε B)
  | .pure f => fun a => some (.ok (f a))
  | .option f => fun a => (f a).map Except.ok
  | .except f => f

/-- The image of an abstract program one level up: `pure f` as the `Option` program
    `some ∘ f`, `option f` as the exception program `.ok`-tagging its results, an
    exception program unchanged. -/
def AbsProg.lift : AbsProg ε A B → AbsProg ε A B
  | .pure f => .option (fun a => some (f a))
  | .option f => .except (fun a => (f a).map Except.ok)
  | .except f => .except f

/-- The correspondence of an abstract program at its own level, over one output
    relation on `Except ε B`: the pure and `Option` levels read it at `.ok`. -/
def AbsProg.Refines (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) : AbsProg ε A B → Prop
  | .pure f => RefinesP sem SRin (fun d b => SRout d (.ok b)) (fun _ => True) f
  | .option f => RefinesO sem SRin (fun d b => SRout d (.ok b)) f
  | .except f => RefinesO sem SRin SRout f

/-- **The lifting lemma.** A program's correspondence at its level is the
    correspondence of its image one level up. -/
theorem AbsProg.refines_lift_iff (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) (p : AbsProg ε A B) :
    p.lift.Refines sem SRin SRout ↔ p.Refines sem SRin SRout := by
  cases p with
  | pure f => exact (refinesP_true_iff_refinesO_some sem SRin _ f).symm
  | option f => exact (refinesO_iff_refinesO_mapOk sem SRin SRout f).symm
  | except f => exact Iff.rfl

/-- A program's correspondence at its level is the exception-level correspondence
    of its image `toExcept`. -/
theorem AbsProg.refines_iff_toExcept (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) (p : AbsProg ε A B) :
    p.Refines sem SRin SRout ↔ RefinesO sem SRin SRout p.toExcept := by
  cases p with
  | pure f =>
      exact (refinesP_true_iff_refinesO_some sem SRin _ f).trans
        (refinesO_iff_refinesO_mapOk sem SRin SRout (fun a => some (f a)))
  | option f => exact refinesO_iff_refinesO_mapOk sem SRin SRout f
  | except f => exact Iff.rfl

/-- The output relation of the exception level induced by a relation on normal
    results: `.ok b` is related as `b`, a thrown value is related to nothing. -/
def liftOk (SR : D → B → Prop) : D → Except ε B → Prop
  | d, .ok b => SR d b
  | _, .error _ => False

/-- The normal results of a refining exception program refine at the `Option`
    level. -/
theorem refinesO_exceptOk (sem : C → Option D) (SRin : C → A → Prop)
    (SRout : D → Except ε B → Prop) (f : A → Option (Except ε B))
    (h : RefinesO sem SRin SRout f) :
    RefinesO sem SRin (fun d b => SRout d (.ok b)) (exceptOk f) := by
  intro c a b hSR hf
  unfold exceptOk at hf
  rcases hfa : f a with _ | (e | b')
  · rw [hfa] at hf; exact absurd hf (by simp)
  · rw [hfa] at hf; exact absurd hf (by simp)
  · rw [hfa, Option.some.injEq] at hf
    subst hf
    exact h c a (.ok b') hSR hfa

end Strengthen

end Hax.Ascent
