/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.CorresMCore

/-!
# A cut-point rule for the correspondence `CorresM`

This module proves a total-correctness cut-point rule for machines whose runs are built
from segments, and derives from it the generic correspondence `CorresM` of
`Calculus/CorresMCore.lean` for a program that runs from an entry point to an exit.

## The rule

The data are a type `L` of cut-point labels, a type `E` of exit labels, a family of
invariants `Inv : L → M → A → Prop` relating the machine state to the abstract state at
each cut point, a family of exit relations `Post : E → M → A → Prop`, and a measure
`μ : L → M → A → Nat`. The obligation, one per cut point, is that from a state
satisfying `Inv l` the machine reaches a state `m'` and the abstract side moves to a
state `a'` such that either some exit relation `Post e m' a'` holds, or some invariant
`Inv l' m' a'` holds at a smaller measure. The conclusion is that from every state
satisfying an invariant the machine reaches a state satisfying an exit relation.

The machine enters through a reachability relation. In the fuel-indexed form it is a
family `R : Nat → M → M → Prop` that composes additively, each segment takes at most `B`
steps, and the run takes at most `B * (μ l m a + 1)` steps (`sim_fuel_le`). In the
fuel-free form it is a transitive relation `Reach` (`sim`). The abstract side enters
through a transitive relation `T`: each segment gives `T a a'`, and the conclusion
relates the entry abstract state to the exit one by `T`. Three choices of `T` occur:

* `T a a' := a' = a`, where the abstract state is the entry state throughout and the
  invariants describe the progress made (Floyd's assertions over the input values);
* a segment obligation with `a' := fa l a` for an abstract transition `fa : L → A → A`
  per label, where `T` is any transitive relation containing every transition;
* `T a a' := F a' = F a` for a function `F` constant along the transitions and the
  identity on exit states, where the exit abstract state is `F a` (`corresM_of_blocks`).

A partial labelling `cut : M → Option L` of the machine states, such as the label of a
program counter, enters through the invariant `atCut cut Inv`.

## Machines

* `iter step n` is the `n`-fold iterate of a one-step function `step : M → Option M`;
  `iter_add` is its additive composition, so `fun n m m' => iter step n m = some m'`
  is a fuel-indexed reachability relation.
* An interpreter with fuel `run : Nat → M → Option M` over a one-step function `stepI`
  and a halting predicate `halted` enters through its two run equations: a halted state
  is returned at every fuel, and a step consumes one unit of fuel. `run_of_iter` states
  that `n` steps to a halted state give that state at every fuel `n + k`. `sim_run_le`
  and `sim_run` are the rule for such an interpreter, with exit relations that imply
  `halted`; the first returns the exit state at every fuel from `B * (μ l m a + 1)`, the
  second at some fuel.
* An interpreter that is not presented by a one-step function, such as a structured
  interpreter that unrolls a `while` loop into its continuation, instantiates `sim`
  or `sim_fuel_le` at a reachability relation on its configurations.

## The correspondence

* `corresM_of_cutPoint` derives `CorresM step SR P fa c` from the rule over a transitive
  `Reach`, given that `SR` under `P` implies an invariant and that an exit state reached
  from an entry state is the result of `step c` and is related to `fa a`.
* `corresM_run` is the instance for an interpreter with fuel at a fixed fuel that bounds
  `B * (μ l m a + 1)` at every entry state.
* `sim_blocks` and `corresM_of_blocks` take the obligation between cut points as a
  `CorresM` of a segment: block `l` has code `code l` and the abstract transition
  `fb l`, and is in `CorresM sstep SR (at_ l) (fb l) (code l)`, where `at_ l a` states
  that the abstract state is at label `l`. Since `CorresM` has one state relation,
  the label of a state is read from the abstract state.

## The literature

The rule is Floyd's method of inductive assertions (R. W. Floyd, *Assigning meanings to
programs*, 1967): assertions at a set of cut points that every cycle of the program
crosses, a verification condition per path between cut points, and termination by a
measure that decreases along each path. The obligations are stated over the step
function of the machine, without a verification-condition generator, as in Matthews,
Moore, Ray and Vroon, *Verification condition generation via theorem proving* (LPAR
2006). The labelled exits, each with its own relation, are the postconditions of a
machine-code triple with several exit points, as in Myreen and Gordon, *Hoare logic for
realistically modelled machine code* (TACAS 2007); a fall-through exit and a jump exit
are two exit labels.

## The `RustM` loop

The invariant rule `corresM_loop` of `Calculus/RustMSquareLoop.lean` for hax-lean's
`loop` is an instance of `sim`, at the reachability relation
`fun x x' => loop body x = loop body x'`; the instance
`Hax.Ascent.RustM.corresM_loop_of_cutPoint` is in `Calculus/CorresMCutPointRustM.lean`,
so that this module imports the calculus core only.

## Main results

* `CutPoint.sim_fuel_le` — the cut-point rule, fuel-indexed, with a bound on the fuel
* `CutPoint.sim` — the cut-point rule over a transitive reachability relation
* `CutPoint.atCut` — an invariant family restricted to a labelling of machine states
* `CutPoint.iter`, `CutPoint.iter_add` — the iterate of a one-step function
* `CutPoint.run_of_iter` — steps to a halted state as a run of an interpreter with fuel
* `CutPoint.sim_run_le`, `CutPoint.sim_run` — the rule for an interpreter with fuel
* `CutPoint.corresM_of_cutPoint`, `CutPoint.corresM_run` — the `CorresM` forms
* `CutPoint.sim_blocks`, `CutPoint.corresM_of_blocks` — the rule from `CorresM` blocks
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace CutPoint

variable {M A L E C : Type}

/-! ## The rule -/

/-- **The cut-point rule, fuel-indexed.** `R n m m'` states that the machine reaches `m'`
    from `m` in `n` steps and composes additively; `T` is a transitive relation on
    abstract states. If from every cut point `l` with invariant `Inv l m a` the machine
    reaches in at most `B` steps a state `m'`, with an abstract state `a'` such that
    `T a a'`, where either an exit relation `Post e m' a'` holds or an invariant
    `Inv l' m' a'` holds at a smaller measure, then from every cut point the machine
    reaches a state satisfying an exit relation in at most `B * (μ l m a + 1)` steps. -/
theorem sim_fuel_le (R : Nat → M → M → Prop)
    (hadd : ∀ n k m m' m'', R n m m' → R k m' m'' → R (n + k) m m'')
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → M → A → Prop) (Post : E → M → A → Prop) (μ : L → M → A → Nat) (B : Nat)
    (hseg : ∀ l m a, Inv l m a → ∃ n m' a', n ≤ B ∧ R n m m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a)) :
    ∀ l m a, Inv l m a →
      ∃ n m' a' e, n ≤ B * (μ l m a + 1) ∧ R n m m' ∧ T a a' ∧ Post e m' a' := by
  intro l m a
  generalize hk : μ l m a = k
  induction k using Nat.strongRecOn generalizing l m a with
  | _ k ih =>
    intro hI
    obtain ⟨n, m', a', hn, hR, hT, hd⟩ := hseg l m a hI
    have hB : B * (k + 1) = B * k + B := by rw [Nat.mul_add, Nat.mul_one]
    cases hd with
    | inl he =>
      obtain ⟨e, he⟩ := he
      exact ⟨n, m', a', e, by omega, hR, hT, he⟩
    | inr hc =>
      obtain ⟨l', hI', hlt⟩ := hc
      obtain ⟨n₂, m'', a'', e, hn₂, hR₂, hT₂, he⟩ := ih _ (hk ▸ hlt) l' m' a' rfl hI'
      have hmono : B * (μ l' m' a' + 1) ≤ B * k := Nat.mul_le_mul_left B (by omega)
      exact ⟨n + n₂, m'', a'', e, by omega, hadd _ _ _ _ _ hR hR₂, htrans _ _ _ hT hT₂, he⟩

/-- **The cut-point rule.** `Reach` is a transitive reachability relation on machine
    states and `T` a transitive relation on abstract states. If from every cut point `l`
    with invariant `Inv l m a` the machine reaches a state `m'`, with an abstract state
    `a'` such that `T a a'`, where either an exit relation `Post e m' a'` holds or an
    invariant `Inv l' m' a'` holds at a smaller measure, then from every cut point the
    machine reaches a state satisfying an exit relation. -/
theorem sim (Reach : M → M → Prop)
    (hreach : ∀ m m' m'', Reach m m' → Reach m' m'' → Reach m m'')
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → M → A → Prop) (Post : E → M → A → Prop) (μ : L → M → A → Nat)
    (hseg : ∀ l m a, Inv l m a → ∃ m' a', Reach m m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a)) :
    ∀ l m a, Inv l m a → ∃ m' a' e, Reach m m' ∧ T a a' ∧ Post e m' a' := by
  intro l m a hI
  obtain ⟨_, m', a', e, _, hR, hT, he⟩ :=
    sim_fuel_le (fun _ => Reach) (fun _ _ => hreach) T htrans Inv Post μ 0
      (fun l m a hI => by
        obtain ⟨m', a', hR, hT, hd⟩ := hseg l m a hI
        exact ⟨0, m', a', Nat.le_refl 0, hR, hT, hd⟩) l m a hI
  exact ⟨m', a', e, hR, hT, he⟩

/-- The invariant family `Inv` restricted to the machine states that the partial
    labelling `cut` places at the label. -/
def atCut (cut : M → Option L) (Inv : L → M → A → Prop) (l : L) (m : M) (a : A) : Prop :=
  cut m = some l ∧ Inv l m a

/-- A machine state satisfies the restricted invariant at one label at most. -/
theorem atCut_label_unique {cut : M → Option L} {Inv : L → M → A → Prop} {l l' : L} {m : M}
    {a a' : A} (h : atCut cut Inv l m a) (h' : atCut cut Inv l' m a') : l = l' :=
  Option.some.inj (h.1.symm.trans h'.1)

/-! ## Machines given by a one-step function -/

/-- The `n`-fold iterate of the one-step function `step`: `none` when a step fails. -/
def iter (step : M → Option M) : Nat → M → Option M
  | 0, m => some m
  | n + 1, m => (step m).bind (iter step n)

/-- `n` steps followed by `k` steps are `n + k` steps. -/
theorem iter_add (step : M → Option M) :
    ∀ (n k : Nat) (m m' m'' : M), iter step n m = some m' → iter step k m' = some m'' →
      iter step (n + k) m = some m'' := by
  intro n
  induction n with
  | zero =>
    intro k m m' m'' h h'
    simp only [iter, Option.some.injEq] at h
    subst h
    rw [Nat.zero_add]; exact h'
  | succ n ih =>
    intro k m m' m'' h h'
    rw [Nat.add_right_comm]
    cases hs : step m with
    | none => simp [iter, hs] at h
    | some m₁ =>
      simp only [iter, hs, Option.bind_some] at h ⊢
      exact ih k m₁ m' m'' h h'

/-- **Steps to a halted state as a run with fuel.** For an interpreter `run` that returns
    a halted state at every fuel (`hhalt`) and consumes one unit of fuel per step of
    `stepI` (`hstep`), `n` steps from `m` to a halted state `m'` give `m'` at every
    fuel `n + k`. -/
theorem run_of_iter (run : Nat → M → Option M) (stepI : M → Option M) (halted : M → Prop)
    (hhalt : ∀ fuel m, halted m → run fuel m = some m)
    (hstep : ∀ fuel m m', stepI m = some m' → run (fuel + 1) m = run fuel m') :
    ∀ (n k : Nat) (m m' : M), iter stepI n m = some m' → halted m' →
      run (n + k) m = some m' := by
  intro n
  induction n with
  | zero =>
    intro k m m' h hm
    simp only [iter, Option.some.injEq] at h
    subst h
    exact hhalt _ _ hm
  | succ n ih =>
    intro k m m' h hm
    rw [Nat.add_right_comm]
    cases hs : stepI m with
    | none => simp [iter, hs] at h
    | some m₁ =>
      simp only [iter, hs, Option.bind_some] at h
      rw [hstep _ _ _ hs]
      exact ih k m₁ m' h hm

/-- **The cut-point rule for an interpreter with fuel, with a bound.** For an interpreter
    `run` with the run equations `hhalt` and `hstep`, segments of at most `B` steps of
    `stepI` between cut points, and exit relations that imply `halted`, the run from a
    cut point returns a state satisfying an exit relation at every fuel from
    `B * (μ l m a + 1)`. -/
theorem sim_run_le (run : Nat → M → Option M) (stepI : M → Option M) (halted : M → Prop)
    (hhalt : ∀ fuel m, halted m → run fuel m = some m)
    (hstep : ∀ fuel m m', stepI m = some m' → run (fuel + 1) m = run fuel m')
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → M → A → Prop) (Post : E → M → A → Prop) (μ : L → M → A → Nat) (B : Nat)
    (hseg : ∀ l m a, Inv l m a → ∃ n m' a', n ≤ B ∧ iter stepI n m = some m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a))
    (hfinal : ∀ e m a, Post e m a → halted m) :
    ∀ l m a, Inv l m a → ∀ fuel, B * (μ l m a + 1) ≤ fuel →
      ∃ m' a' e, run fuel m = some m' ∧ T a a' ∧ Post e m' a' := by
  intro l m a hI fuel hfuel
  obtain ⟨n, m', a', e, hn, hR, hT, he⟩ :=
    sim_fuel_le (fun n m m' => iter stepI n m = some m') (iter_add stepI) T htrans Inv Post μ B
      hseg l m a hI
  refine ⟨m', a', e, ?_, hT, he⟩
  have h := run_of_iter run stepI halted hhalt hstep n (fuel - n) m m' hR (hfinal e m' a' he)
  rwa [show n + (fuel - n) = fuel by omega] at h

/-- **The cut-point rule for an interpreter with fuel.** For an interpreter `run` with
    the run equations `hhalt` and `hstep`, segments of steps of `stepI` between cut
    points, and exit relations that imply `halted`, the run from a cut point returns a
    state satisfying an exit relation at some fuel. -/
theorem sim_run (run : Nat → M → Option M) (stepI : M → Option M) (halted : M → Prop)
    (hhalt : ∀ fuel m, halted m → run fuel m = some m)
    (hstep : ∀ fuel m m', stepI m = some m' → run (fuel + 1) m = run fuel m')
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → M → A → Prop) (Post : E → M → A → Prop) (μ : L → M → A → Nat)
    (hseg : ∀ l m a, Inv l m a → ∃ n m' a', iter stepI n m = some m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a))
    (hfinal : ∀ e m a, Post e m a → halted m) :
    ∀ l m a, Inv l m a → ∃ fuel m' a' e, run fuel m = some m' ∧ T a a' ∧ Post e m' a' := by
  intro l m a hI
  obtain ⟨m', a', e, ⟨n, hR⟩, hT, he⟩ :=
    sim (fun m m' => ∃ n, iter stepI n m = some m')
      (fun m m' m'' h h' => by
        obtain ⟨n, h⟩ := h
        obtain ⟨k, h'⟩ := h'
        exact ⟨n + k, iter_add stepI n k m m' m'' h h'⟩) T htrans Inv Post μ
      (fun l m a hI => by
        obtain ⟨n, m', a', hR, hT, hd⟩ := hseg l m a hI
        exact ⟨m', a', ⟨n, hR⟩, hT, hd⟩) l m a hI
  exact ⟨n, m', a', e,
    by simpa using run_of_iter run stepI halted hhalt hstep n 0 m m' hR (hfinal e m' a' he),
    hT, he⟩

/-! ## The correspondence from the rule -/

/-- **`CorresM` from cut points.** If `SR` under `P` implies an invariant at some cut
    point (`hentry`), the segments between cut points satisfy the obligation of `sim`
    (`hseg`), and a state satisfying an exit relation that is reached from an entry state
    is the result of `step c` and is related by `SR` to `fa a` (`hexit`), then `c` is in
    the correspondence with `fa`. -/
theorem corresM_of_cutPoint (step : C → M → Option M) (c : C) (Reach : M → M → Prop)
    (hreach : ∀ m m' m'', Reach m m' → Reach m' m'' → Reach m m'')
    (SR : M → A → Prop) (P : A → Prop) (fa : A → A)
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → M → A → Prop) (Post : E → M → A → Prop) (μ : L → M → A → Nat)
    (hentry : ∀ m a, SR m a → P a → ∃ l, Inv l m a)
    (hseg : ∀ l m a, Inv l m a → ∃ m' a', Reach m m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a))
    (hexit : ∀ m a m' a' e, SR m a → P a → Reach m m' → T a a' → Post e m' a' →
      step c m = some m' ∧ SR m' (fa a)) :
    CorresM step SR P fa c := by
  intro m a hSR hP
  obtain ⟨l, hI⟩ := hentry m a hSR hP
  obtain ⟨m', a', e, hR, hT, he⟩ := sim Reach hreach T htrans Inv Post μ hseg l m a hI
  exact ⟨m', hexit m a m' a' e hSR hP hR hT he⟩

/-- **`CorresM` of an interpreter with fuel from cut points.** For an interpreter
    `run c` with the run equations `hhalt` and `hstep` over `stepI c`, if `SR` under `P`
    implies an invariant at a cut point whose bound `B * (μ l m a + 1)` is at most `fuel`
    (`hentry`), the segments take at most `B` steps (`hseg`), and the exit relations
    imply `halted` (`hfinal`) and `SR` at `fa a` (`hexit`), then `c` is in the
    correspondence with `fa` for the step `fun c => run c fuel`. -/
theorem corresM_run (run : C → Nat → M → Option M) (stepI : C → M → Option M) (c : C)
    (halted : M → Prop)
    (hhalt : ∀ fuel m, halted m → run c fuel m = some m)
    (hstep : ∀ fuel m m', stepI c m = some m' → run c (fuel + 1) m = run c fuel m')
    (SR : M → A → Prop) (P : A → Prop) (fa : A → A)
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → M → A → Prop) (Post : E → M → A → Prop) (μ : L → M → A → Nat) (B fuel : Nat)
    (hentry : ∀ m a, SR m a → P a → ∃ l, Inv l m a ∧ B * (μ l m a + 1) ≤ fuel)
    (hseg : ∀ l m a, Inv l m a → ∃ n m' a', n ≤ B ∧ iter (stepI c) n m = some m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a))
    (hfinal : ∀ e m a, Post e m a → halted m)
    (hexit : ∀ a m' a' e, P a → T a a' → Post e m' a' → SR m' (fa a)) :
    CorresM (fun c => run c fuel) SR P fa c := by
  intro m a hSR hP
  obtain ⟨l, hI, hfuel⟩ := hentry m a hSR hP
  obtain ⟨m', a', e, hrun, hT, he⟩ :=
    sim_run_le (run c) (stepI c) halted hhalt hstep T htrans Inv Post μ B hseg hfinal
      l m a hI fuel hfuel
  exact ⟨m', hrun, hexit a m' a' e hP hT he⟩

/-! ## Segments given as correspondences -/

/-- **The cut-point rule from `CorresM` blocks.** Block `l` has code `code l` and the
    abstract transition `fb l`; `at_ l a` states that the abstract state `a` is at label
    `l`, and `done a` that it is at an exit. If every block is in the correspondence from
    `at_ l` (`hblock`), a successful block step is a reachability step (`hsem`), every
    transition is in the transitive relation `T` (`hT`), and after a transition the
    abstract state is at an exit or at a label with a smaller measure (`hnext`), then
    from a related pair at a label the machine reaches a state related to an abstract
    exit state. -/
theorem sim_blocks (sstep : C → M → Option M) (code : L → C) (Reach : M → M → Prop)
    (hreach : ∀ m m' m'', Reach m m' → Reach m' m'' → Reach m m'')
    (hsem : ∀ l m m', sstep (code l) m = some m' → Reach m m')
    (SR : M → A → Prop) (at_ : L → A → Prop) (done : A → Prop) (fb : L → A → A)
    (T : A → A → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'') (μ : A → Nat)
    (hblock : ∀ l, CorresM sstep SR (at_ l) (fb l) (code l))
    (hT : ∀ l a, at_ l a → T a (fb l a))
    (hnext : ∀ l a, at_ l a → done (fb l a) ∨ ∃ l', at_ l' (fb l a) ∧ μ (fb l a) < μ a) :
    ∀ l m a, SR m a → at_ l a → ∃ m' a', Reach m m' ∧ T a a' ∧ SR m' a' ∧ done a' := by
  intro l m a hSR hat
  obtain ⟨m', a', _, hR, hT', hpost⟩ :=
    sim (E := Unit) Reach hreach T htrans (fun l m a => SR m a ∧ at_ l a)
      (fun _ m a => SR m a ∧ done a) (fun _ _ a => μ a)
      (fun l m a hI => by
        obtain ⟨m', hs, hSR'⟩ := hblock l m a hI.1 hI.2
        refine ⟨m', fb l a, hsem l m m' hs, hT l a hI.2, ?_⟩
        cases hnext l a hI.2 with
        | inl hd => exact Or.inl ⟨(), hSR', hd⟩
        | inr hc =>
          obtain ⟨l', hat', hlt⟩ := hc
          exact Or.inr ⟨l', ⟨hSR', hat'⟩, hlt⟩) l m a ⟨hSR, hat⟩
  exact ⟨m', a', hR, hT', hpost⟩

/-- **`CorresM` from `CorresM` blocks.** Under the block hypotheses of `sim_blocks`, if
    `P` places the abstract state at a label (`hentry`), the function `F` is constant
    along the block transitions (`hF`) and the identity on exit states (`hdone`), and a
    state reached from an entry state and related to `F a` is the result of `step c`
    (`hrun`), then `c` is in the correspondence with `F`. -/
theorem corresM_of_blocks (step : C → M → Option M) (c : C)
    (sstep : C → M → Option M) (code : L → C) (Reach : M → M → Prop)
    (hreach : ∀ m m' m'', Reach m m' → Reach m' m'' → Reach m m'')
    (hsem : ∀ l m m', sstep (code l) m = some m' → Reach m m')
    (SR : M → A → Prop) (P : A → Prop) (F : A → A)
    (at_ : L → A → Prop) (done : A → Prop) (fb : L → A → A) (μ : A → Nat)
    (hblock : ∀ l, CorresM sstep SR (at_ l) (fb l) (code l))
    (hnext : ∀ l a, at_ l a → done (fb l a) ∨ ∃ l', at_ l' (fb l a) ∧ μ (fb l a) < μ a)
    (hentry : ∀ a, P a → ∃ l, at_ l a)
    (hF : ∀ l a, at_ l a → F (fb l a) = F a)
    (hdone : ∀ a, done a → F a = a)
    (hrun : ∀ m a m', SR m a → P a → Reach m m' → SR m' (F a) → step c m = some m') :
    CorresM step SR P F c := by
  intro m a hSR hP
  obtain ⟨l, hat⟩ := hentry a hP
  obtain ⟨m', a', hR, hT, hSR', hd⟩ :=
    sim_blocks sstep code Reach hreach hsem SR at_ done fb (fun a a' => F a' = F a)
      (fun _ _ _ h h' => h'.trans h) μ hblock hF hnext l m a hSR hat
  have ha' : a' = F a := by rw [← hT, hdone a' hd]
  subst ha'
  exact ⟨m', hrun m a m' hSR hP hR hSR', hSR'⟩

end CutPoint

end CatCrypt.Crypto.SecureCompilation.Ascent
