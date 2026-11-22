/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaWP
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfg
public import Std.WP

/-!
# Texts with exits of an instruction set over `Std.WP`

A text is a program of an instruction set together with a set of program counters and the
counter of its normal exit. Its weakest precondition holds at a state when finitely many steps
at counters of the text reach a counter outside it in a state that satisfies the postcondition
of that exit: the normal postcondition at the counter of the normal exit, the exception
postcondition, indexed by the counter, at every other exit. There is no fuel, and a state
inside the text at which no instruction is fetched or the step fails satisfies no weakest
precondition, so the logic is one of total correctness.

## Main definitions

* `Isa.Text`, `Isa.Text.Runs`: texts and their terminating runs to an exit.
* The `Std.WP` instance of `Isa.Text`, with the exception postcondition `Nat → LstateMF → Prop`,
  and its `WPConjunctive` instance.
* `Isa.Text.whole`: the text of all counters of a body.

## Main results

* `wp_leave`, `wp_step`: the weakest precondition outside and inside a text.
* `wp_sub`: the weakest precondition of a text through a smaller text.
* `Runs.steps_iff`: a segment `IsaCfg.Steps` preserves the runs of a text that contains every
  counter of the body.
* `runs_whole_iff`, `wp_whole_bot_iff`: adequacy for the fuel interpreter.
* `corresIsaRun_of_triple`, `corresIsaRun_iff_triple`: `CorresIsaRun` as a family of triples.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

open Std.WP Lean.Order
open JasminLprogExport (LLabel LabelKind)
open JasminLsemMem (LinstrRM MemTag)
open JasminLsemMemLoop (LprogM findInstrMem)
open JasminLsemMemFlagGuard (LstateMF)
open Ascent (CorresIsaRun)

/-- A text of an instruction set: a program, the counters inside the text, and the counter of
    the normal exit. -/
structure Text where
  /-- The instruction set. -/
  isa : Isa
  /-- The program from which the instructions are fetched. -/
  prog : LprogM
  /-- The counters of the text. -/
  inside : Nat → Prop
  /-- The counter of the normal exit. -/
  fall : Nat

namespace Text

/-- The text of all counters of the body of `P`, whose normal exit is the counter after the
    body. -/
def whole (I : Isa) (P : LprogM) : Text :=
  ⟨I, P, (· < P.body.length), P.body.length⟩

/-- `t.Runs post s`: finitely many steps from `s` at counters of `t` reach a counter outside
    `t` in a state satisfying `post`. -/
inductive Runs (t : Text) (post : LstateMF → Prop) : LstateMF → Prop
  /-- A state outside the text has left it. -/
  | leave (s : LstateMF) : ¬ t.inside s.prog.base.lpc → post s → t.Runs post s
  /-- A fetched step inside the text, followed by a run. -/
  | step (s : LstateMF) (i : LinstrRM) (s' : LstateMF) : t.inside s.prog.base.lpc →
      findInstrMem t.prog s.prog = some i → t.isa.step t.prog i s = some s' →
      t.Runs post s' → t.Runs post s

/-- The postcondition of an exit: `Q` at the normal exit, `E` at the counter of any other. -/
def exitPost (t : Text) (Q : Unit → LstateMF → Prop) (E : Nat → LstateMF → Prop)
    (s : LstateMF) : Prop :=
  if s.prog.base.lpc = t.fall then Q () s else E s.prog.base.lpc s

variable {t : Text} {post post' : LstateMF → Prop} {Q : Unit → LstateMF → Prop}
  {E : Nat → LstateMF → Prop} {s : LstateMF}

/-- Runs are monotone in the postcondition. -/
theorem Runs.mono (h : t.Runs post s) (hp : ∀ u, post u → post' u) : t.Runs post' s := by
  induction h with
  | leave u hu hq => exact .leave u hu (hp u hq)
  | step u i u' hu hf hs _ ih => exact .step u i u' hu hf hs ih

/-- The weakest precondition of a text: a run to an exit satisfying its postcondition. -/
instance instWP : WP Text Unit (LstateMF → Prop) (Nat → LstateMF → Prop) where
  trans t := ⟨fun Q E => t.Runs (t.exitPost Q E)⟩
  trans_monotone t := fun Q Q' E E' hE hQ s h => h.mono fun u => by
    unfold exitPost
    split
    · exact hQ () u
    · exact hE _ u

/-- The unfolding lemma of the weakest precondition of a text. -/
theorem wp_apply : wp t Q E s = t.Runs (t.exitPost Q E) s := rfl

/-- The steps are deterministic, so the runs are closed under conjunction. -/
theorem Runs.and (h : t.Runs post s) (h' : t.Runs post' s) :
    t.Runs (fun u => post u ∧ post' u) s := by
  induction h with
  | leave u hu hq =>
    cases h' with
    | leave _ _ hq' => exact .leave u hu ⟨hq, hq'⟩
    | step _ _ _ hu' => exact absurd hu' hu
  | step u i u' hu hf hs _ ih =>
    cases h' with
    | leave _ hu' => exact absurd hu hu'
    | step _ _ _ _ hf' hs' hr => grind [Runs.step]

/-- The weakest precondition of a text is conjunctive. -/
instance instWPConjunctive (t : Text) : WPConjunctive t where
  wp_meet_wp_le := by
    intro Q₁ Q₂ E₁ E₂ s h
    simp only [WP.trans_apply_eq, meet_apply, meet_prop_eq_and, wp_apply] at h ⊢
    refine (h.1.and h.2).mono fun u => ?_
    simp only [exitPost, meet_apply, meet_prop_eq_and]
    split <;> exact id

/-- Outside the text the weakest precondition is the postcondition of the exit. -/
theorem wp_leave (hs : ¬ t.inside s.prog.base.lpc) :
    wp t Q E s ↔ if s.prog.base.lpc = t.fall then Q () s else E s.prog.base.lpc s := by
  rw [wp_apply]
  constructor
  · intro h
    cases h with
    | leave _ _ hq => exact hq
    | step _ _ _ hu => exact absurd hu hs
  · exact fun h => .leave s hs h

/-- Inside the text the weakest precondition is that of the successor of the fetched step. -/
theorem wp_step {i : LinstrRM} (hs : t.inside s.prog.base.lpc)
    (hi : findInstrMem t.prog s.prog = some i) :
    wp t Q E s ↔ ∃ s', t.isa.step t.prog i s = some s' ∧ wp t Q E s' := by
  simp only [wp_apply]
  constructor
  · intro h
    cases h with
    | leave _ hu => exact absurd hs hu
    | step _ _ s' _ hf hst hr => grind
  · exact fun ⟨s', hst, hr⟩ => .step s i s' hs hi hst hr

/-- The weakest precondition of a text is that of a smaller text of the same program whose
    exits continue in the larger text. -/
theorem wp_sub {inner outer : Text} (hisa : inner.isa = outer.isa)
    (hprog : inner.prog = outer.prog) (hsub : ∀ k, inner.inside k → outer.inside k) :
    wp outer Q E s ↔ wp inner (fun _ => wp outer Q E) (fun _ => wp outer Q E) s := by
  have hpost : inner.exitPost (fun _ => wp outer Q E) (fun _ => wp outer Q E) =
      outer.Runs (outer.exitPost Q E) := by
    funext u
    exact ite_self _
  simp only [wp_apply, hpost]
  constructor
  · intro h
    induction h with
    | leave u hu hq => exact .leave u (fun h => hu (hsub _ h)) (.leave u hu hq)
    | step u i u' hu hf hst hr ih =>
      by_cases hin : inner.inside u.prog.base.lpc
      · exact .step u i u' hin (hprog ▸ hf) (by rw [hisa, hprog, hst]) ih
      · exact .leave u hin (.step u i u' hu hf hst hr)
  · intro h
    induction h with
    | leave u _ hq => exact hq
    | step u i u' hu hf hst _ ih =>
      exact .step u i u' (hsub _ hu) (hprog ▸ hf) (by rw [← hisa, ← hprog, hst]) ih

/-- A fetched counter is a counter of the body. -/
theorem lpc_lt_of_findInstrMem {P : LprogM} {i : LinstrRM}
    (h : findInstrMem P s.prog = some i) : s.prog.base.lpc < P.body.length := by
  grind [findInstrMem]

/-- No instruction is fetched past the body. -/
theorem halted_of_length_le {P : LprogM} (h : P.body.length ≤ s.prog.base.lpc) :
    Ascent.IsaCfg.Halted P s := by
  grind [Ascent.IsaCfg.Halted, findInstrMem]

/-- A segment of steps preserves and reflects the runs of a text that contains every counter
    of the body. -/
theorem Runs.steps_iff (hcov : ∀ k, k < t.prog.body.length → t.inside k) :
    ∀ {n : Nat} {s u : LstateMF}, Ascent.IsaCfg.Steps t.isa t.prog n s u →
      (t.Runs post s ↔ t.Runs post u) := by
  intro n
  induction n with
  | zero =>
    intro s u h
    cases h
    rfl
  | succ n ih =>
    intro s u h
    simp only [Ascent.IsaCfg.Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, h⟩ := h
    rw [← ih h]
    unfold Isa.lsemStepPMemF at hw
    cases hf : findInstrMem t.prog s.prog with
    | none => grind
    | some i =>
      have hin := hcov _ (lpc_lt_of_findInstrMem hf)
      constructor
      · intro hr
        cases hr with
        | leave _ hu => exact absurd hin hu
        | step _ _ _ _ hf' hst' hr => grind
      · exact fun hr => .step s i w hin hf (by grind) hr

section Adequacy

variable {I : Isa} {P : LprogM}

/-- A run of the text of a whole body is a halting run of the fuel interpreter that ends at or
    past the end of the body. -/
theorem runs_whole_iff :
    (whole I P).Runs post s ↔ ∃ fuel s', I.lsemFuelMemF P fuel s = some s' ∧
      P.body.length ≤ s'.prog.base.lpc ∧ post s' := by
  constructor
  · intro h
    induction h with
    | leave u hu hq =>
      have hle : P.body.length ≤ u.prog.base.lpc := Nat.le_of_not_lt hu
      exact ⟨0, u, I.lsemFuelMemF_halt P 0 u (halted_of_length_le hle), hle, hq⟩
    | step u i u' _ hf hst _ ih =>
      obtain ⟨fuel, v, hrun, hv⟩ := ih
      exact ⟨fuel + 1, v, (I.lsemFuelMemF_step P fuel i u u' hf hst).trans hrun, hv⟩
  · rintro ⟨fuel, v, hrun, hle, hq⟩
    obtain ⟨n, hsteps⟩ : ∃ n, Ascent.IsaCfg.Steps I P n s v := by
      induction fuel generalizing s with
      | zero => exact ⟨0, by grind [lsemFuelMemF, Ascent.IsaCfg.Steps, Ascent.CutPoint.iter]⟩
      | succ fuel ih =>
        cases hf : findInstrMem P s.prog with
        | none => exact ⟨0, by grind [lsemFuelMemF, Ascent.IsaCfg.Steps, Ascent.CutPoint.iter]⟩
        | some i =>
          cases hst : I.step P i s with
          | none => grind [lsemFuelMemF]
          | some w =>
            obtain ⟨n, hn⟩ := ih ((I.lsemFuelMemF_step P fuel i s w hf hst).symm.trans hrun)
            exact ⟨1 + n, (Ascent.IsaCfg.Steps.one (by grind [lsemStepPMemF])).trans hn⟩
    exact (Runs.steps_iff (t := whole I P) (fun _ h => h) hsteps).2
      (.leave v (Nat.not_lt.2 hle) hq)

/-- Adequacy: the weakest precondition of the text of a whole body without other exits holds
    exactly when the fuel interpreter halts at the counter after the body in a state
    satisfying the postcondition. -/
theorem wp_whole_bot_iff :
    wp (whole I P) Q bot s ↔ ∃ fuel s', I.lsemFuelMemF P fuel s = some s' ∧
      s'.prog.base.lpc = P.body.length ∧ Q () s' := by
  rw [wp_apply, runs_whole_iff]
  simp only [exitPost, whole, bot_apply, bot_prop_eq]
  grind

variable {A : Type} {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}

/-- The triples of the text of a whole body give the correspondence with the fuel chosen per
    initial state. -/
theorem corresIsaRun_of_triple
    (h : ∀ a, Pre a → Triple (whole I P) (SR · a) (fun _ m => SR m (fa a)) bot) :
    CorresIsaRun I P SR Pre fa := by
  intro m a hSR hPre
  obtain ⟨fuel, m', hrun, _, hSR'⟩ := wp_whole_bot_iff.1 ((h a hPre).le_wp m hSR)
  exact ⟨fuel, m', hrun, hSR'⟩

/-- When the related final states are at the counter after the body, the correspondence with
    the fuel chosen per initial state is the family of triples of the text of the body. -/
theorem corresIsaRun_iff_triple
    (hend : ∀ m a, Pre a → SR m (fa a) → m.prog.base.lpc = P.body.length) :
    CorresIsaRun I P SR Pre fa ↔
      ∀ a, Pre a → Triple (whole I P) (SR · a) (fun _ m => SR m (fa a)) bot := by
  refine ⟨fun h a hPre => Triple.intro fun m hSR => ?_, corresIsaRun_of_triple⟩
  obtain ⟨fuel, m', hrun, hSR'⟩ := h m a hSR hPre
  exact wp_whole_bot_iff.2 ⟨fuel, m', hrun, hend m' a hPre hSR', hSR'⟩

/-- A body of one label satisfies the hypothesis of `corresIsaRun_iff_triple` at the relation
    that fixes the counter, and corresponds to the update of the counter from zero to one. -/
example (fn : String) (k : LabelKind) (l : LLabel) (tag : MemTag) :
    CorresIsaRun I (JasminLsemMemLoop.singletonProgM fn [(.Llabel k l, tag)])
      (fun m pc => m.prog.lfn = fn ∧ m.prog.base.lpc = pc) (· = 0) (fun _ => 1) := by
  refine (corresIsaRun_iff_triple fun m a _ h => h.2).2 fun a ha => Triple.intro fun m hm => ?_
  obtain ⟨hs, hat⟩ := Ascent.IsaCfg.steps_label I
    (P := JasminLsemMemLoop.singletonProgM fn [(.Llabel k l, tag)])
    (k := 0) ⟨hm.1, hm.2.trans ha⟩ rfl
  refine wp_whole_bot_iff.2 ⟨1, _, Ascent.IsaCfg.lsemFuelMemF_of_steps I _ hs ?_ 0, hat.2, hat⟩
  exact halted_of_length_le hat.2.ge

end Adequacy

end Text

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

end
