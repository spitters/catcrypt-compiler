/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.WriterTMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# Can we add a *grade* to `mvcgen`? — an empirical probe

A **grade** is a monoid quantity — a cost (`ℕ`), an error/ε budget (`ℝ≥0∞`), an
interface-resource multiset — that **accumulates to `g₁ + g₂` under sequencing**
and yields a `total ≤ budget` obligation. `GradedWP.lean` builds the standalone
graded Dijkstra monad (`gbind` grades add) *outside* `Std.Do`; `WriterTMvcgen.lean`
shows the writer-as-state route lands inside `mvcgen`. This module settles the
concrete question — *can stock `mvcgen` carry a grade?* — by testing **both** the
pragmatic route and the faithful boundary, and reports the exact finding.

## Part 1 — the pragmatic route: grade as operational state (WORKS today)

`CostM := StateM ℕ` with `tick n = modify (· + n)` makes the grade a **write-only
state cell**. A `GradedTriple budget P prog Q` is then the native `Std.Do` triple
whose postcondition mentions the **final accumulated cost** and additionally
demands `final_cost ≤ budget`. Because the cost lives in the `StateM ℕ` state, its
`PostShape` is `.arg ℕ .pure` — exactly the shape `mvcgen`'s `modify`/`bind`
`@[spec]` lemmas fire on. `mvcgen [tick_spec]` **threads the cost** through a
`tick 1; tick 1; tick 1` program, accumulating `0 + 1 + 1 + 1 = 3`, and the
residual verification condition is precisely `3 ≤ budget`. Graded-mvcgen-via-state
works out of the box (`demo_cost`, `demo_cost_accumulates`).

The catch — and the whole reason Part 2 exists — is that this route makes the grade
**operational**: the program must literally read/write a `ℕ` cell (`modify (· + n)`).
That is fine for a real cost counter, but it *mis-models* a grade that is a
**proof-level** index — an ε-budget bound on a reduction's advantage is not a value
the extracted code carries at runtime. For that we need a grade the program does
**not** compute.

## Part 2 — the faithful boundary: a spec-only grade (needs a `PostShape` change)

The real test: thread a grade contributed by `@[spec]` lemmas / a wrapper — a grade
the *program does not compute* — and see whether stock `mvcgen` accumulates it
out-of-band. It **cannot**, and here is the exact wall, with a compiling witness.

* **The `WP` codomain is grade-free and fixed.** `WP m ps` interprets `m α` as
  `PredTrans ps α`, and `ps : PostShape` is the *fixed* inductive
  `pure | arg σ | except ε` — it has **no** monoid-grade constructor. The exhaustive
  `cases` in `postShape_exhaustive` is the compiling witness that these three are
  *all* the constructors: there is no `.graded G` barrel. So there is no `ps` whose
  `PredTrans ps α` carries a grade beside its state/exception barrels.

* **A `@[spec]` lemma cannot introduce the grade either.** `Triple` is
  `Triple [WP m ps] (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop`
  (`Std.Do.Triple.Basic`). Its type quantifies over `ps`, `P`, `Q` — and **no
  grade** `G`/`g` appears. A `@[spec]` lemma *is* a `Triple`, so it has nowhere to
  put a grade; `mvcgen` composes specs via `PredTrans.bind`, which sees only the
  grade-free carrier.

* **The provable witness (`forget_gradedBind`).** We *can* type-tag a grade on top
  of the real `PredTrans`: `GradedPT g ps α` wraps `PredTrans ps α` with a grade
  index `g`, and `gradedBind` produces grade `g₁ + g₂`. But `forget_gradedBind`
  proves — by `rfl` — that the **underlying transformer of a graded bind is the
  ordinary, grade-free `PredTrans.bind`**. The sum `g₁ + g₂` lives *only in the type
  tag*; the object `mvcgen` actually manipulates (obtained through `WP.wp`, of type
  `PredTrans ps α`) has the grade **erased**. So no spec lemma — which speaks about
  that object — can force the grade to accumulate.

* **The only monoid-accumulating barrel `PostShape` offers is `.arg`, i.e. state.**
  `Assertion (.arg G ps) = SPred (G :: PostShape.args ps)` is a `G`-cell: threading a
  monoid through `.arg G` *is* Part 1's operational state encoding. There is no
  fourth, non-operational slot.

## The definitive answer

* **What stock `mvcgen` supports today:** a grade encoded as **operational state**
  (`StateM G`, `.arg G .pure`). `mvcgen` threads it and leaves `total ≤ budget` as
  the residual VC — genuinely proved in Part 1. Adequate for a runtime cost counter;
  it changes the operational semantics (the program computes the grade).

* **What a *faithful* spec-only grade requires:** a **`.graded G` `PostShape`
  constructor** (an upstream `Std.Do` change) carrying a monoid index, plus a
  grade-**additive** `bind` `@[spec]` lemma teaching `mvcgen`'s spec engine to
  accumulate `g₁ + g₂` while it walks the VC — exactly `GradedWP.gbind`/`seq`, lifted
  into the metatheory. **A spec lemma alone cannot do it**, because the fixed
  `PredTrans ps` / `Assertion ps` codomain has no place to hold the grade. This is a
  framework extension, not a library lemma. (We do **not** fork the toolchain here;
  the point is to locate the wall precisely.)

This is the empirical answer to "could we add a grade to `mvcgen`": *as state, yes,
today; as a faithful proof-level index, only via a `PostShape` extension.*
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent.GradedMvcgenProbe

open Std.Do

/-! ## Part 1 — the pragmatic route: the grade as an operational cost state

`CostM = StateM ℕ` is a write-only cost cell; `tick n` adds `n`. Its `PostShape` is
`.arg ℕ .pure`, the native `StateT` shape `mvcgen` walks. -/

/-- **The cost monad**: a `ℕ`-valued cost counter, encoded as `StateM ℕ`. The grade
    (accumulated cost) is carried as operational state. -/
abbrev CostM (α : Type) : Type := StateM Nat α

/-- **`tick n`** charges `n` units of cost, adding to the running counter. This is the
    state encoding of the cost grade: `modify (· + n)`. -/
def tick (n : Nat) : CostM Unit :=
  modify (fun c => c + n)

/-- The `PostShape` of `CostM = StateT ℕ Id`: a single cost argument over the pure
    base — the native `StateT` shape, `.arg ℕ .pure`. -/
abbrev psC : PostShape := .arg Nat .pure

/-- **The `tick` `@[spec]` triple.** The Hoare triple for one `tick n`: its
    precondition is the native `modify` weakest precondition (the post evaluated at
    the `+ n`-updated cost). `mvcgen`'s built-in `modify` handling discharges it; no
    custom `wp` lemma. This is what makes `tick` — and hence the accumulating grade —
    `mvcgen`-walkable. -/
@[spec]
theorem tick_spec (n : Nat) (Q : PostCond Unit psC) :
    Triple (tick n) (fun c => Q.1 () (c + n)) Q := by
  unfold tick Triple
  mvcgen

/-- **The graded triple.** A `Std.Do` triple over a `CostM` program whose
    postcondition mentions the **final accumulated cost** `c`, *and* additionally
    demands `c ≤ budget`. `mvcgen` threads the cost; the `≤ budget` conjunct is the
    residual verification condition. This is the graded-triple-via-state. -/
def GradedTriple {α : Type} (budget : Nat) (P : Nat → Prop) (prog : CostM α)
    (Q : α → Nat → Prop) : Prop :=
  ⦃fun c => ⌜P c⌝⦄ prog ⦃⇓ a c => ⌜Q a c ∧ c ≤ budget⌝⦄

/-- **The write-only-cost bridge.** The graded triple is equivalent to the run-level
    statement `∀ c, P c → Q (final) (final_cost) ∧ final_cost ≤ budget`, where
    `final`/`final_cost = prog.run c`. Forward evaluates the WP at a concrete initial
    cost via the `StateM` adequacy lemma `StateM.of_wp_run_eq`; reverse is
    reflexivity of the `StateM` WP. Makes precise that the grade *is* a write-only
    state and the `≤ budget` obligation is a fact about the accumulated total. -/
theorem gradedTriple_iff {α : Type} (budget : Nat) (P : Nat → Prop)
    (Q : α → Nat → Prop) (prog : CostM α) :
    GradedTriple budget P prog Q ↔
      (∀ c, P c → Q (prog.run c).1 (prog.run c).2 ∧ (prog.run c).2 ≤ budget) := by
  unfold GradedTriple
  constructor
  · intro h c hP
    exact StateM.of_wp_run_eq (x := prog.run c) rfl
      (fun p => Q p.1 p.2 ∧ p.2 ≤ budget) (fun _ => h c hP)
  · intro h
    refine Triple.iff.mpr ?_
    simp only [SPred.entails_1]
    intro c hP
    exact h c hP

/-! ### Demonstration: `mvcgen` accumulates the grade -/

/-- A three-`tick` program, each charging one unit. -/
def demoTicks : CostM Unit := do
  tick 1
  tick 1
  tick 1

/-- **`mvcgen` threads the cost and leaves `3 ≤ budget`.** Starting from cost `0`,
    `mvcgen [tick_spec]` fires the cost step spec three times, accumulating
    `0 + 1 + 1 + 1 = 3`; the postcondition pins the final cost to `3` and the
    residual verification condition is exactly `3 ≤ budget`, discharged from the
    hypothesis. This is the positive result: a **graded triple whose grade `mvcgen`
    genuinely accumulates**, with `total ≤ budget` as the residual VC. -/
theorem demo_cost (budget : Nat) (h : 3 ≤ budget) :
    GradedTriple budget (fun c => c = 0) demoTicks (fun _ c => c = 3) := by
  unfold GradedTriple demoTicks
  mvcgen [tick_spec]
  simp_all

/-- **The grade genuinely accumulates onto the incoming cost.** From any starting
    cost `w`, the three ticks bring the total to `w + 3` — `mvcgen` *adds* onto
    whatever the incoming counter was, and the residual bound `w + 3 ≤ w + 3` holds.
    Witnesses that the cost is a real accumulation, not overwritten. -/
theorem demo_cost_accumulates (w : Nat) :
    GradedTriple (w + 3) (fun c => c = w) demoTicks (fun _ c => c = w + 3) := by
  unfold GradedTriple demoTicks
  mvcgen [tick_spec]
  simp_all

/-! ## Part 2 — the faithful boundary: a spec-only grade

We now attempt a grade the program does *not* compute — a grade contributed by a
wrapper / spec — and pin down exactly why stock `mvcgen` cannot accumulate it. -/

/-- **`PostShape` is exhaustively `pure | arg σ | except ε`.** This compiling
    `cases` is the witness that the effect stack `mvcgen` runs on has **no** monoid-
    grade constructor: there is no `.graded G` barrel in which a grade could
    accumulate beside state/exceptions. Any faithful spec-only grade must *add* such
    a constructor — an upstream `Std.Do` change. -/
theorem postShape_exhaustive (ps : PostShape) : True := by
  cases ps with
  | pure => trivial
  | arg σ ps => trivial
  | except ε ps => trivial

section GradeTag

variable {G : Type} [Zero G] [Add G]

/-- **A grade-tagged predicate transformer.** We *can* index the real `Std.Do`
    `PredTrans ps α` by a grade `g : G` — but only as an outer **type tag**: the
    underlying transformer is grade-oblivious. This is the most one can bolt onto the
    fixed carrier without changing `PostShape`. -/
structure GradedPT (g : G) (ps : PostShape) (α : Type) where
  /-- The underlying, grade-free `Std.Do` predicate transformer. -/
  pt : PredTrans ps α

/-- **Grade erasure — the `mvcgen` boundary.** `WP.wp` produces exactly a
    `PredTrans ps α`; this `forget` is the map through which `mvcgen`/`@[spec]` see a
    graded transformer, and it **drops the grade `g`** (its type does not depend on
    `g`). Everything `mvcgen` manipulates is downstream of this erasure. -/
def GradedPT.forget {g : G} {ps : PostShape} {α : Type}
    (t : GradedPT g ps α) : PredTrans ps α := t.pt

/-- **Graded return** at grade `0`, over the real `PredTrans.pure`. -/
def gradedPure {ps : PostShape} {α : Type} (a : α) : GradedPT (0 : G) ps α :=
  ⟨PredTrans.pure a⟩

/-- **Graded bind — grades add.** Sequencing a `g₁`-transformer with a
    `g₂`-continuation yields grade `g₁ + g₂`, over the real `PredTrans.bind`. The
    grade addition is exactly `GradedWP.gbind`'s — but here on top of the *actual*
    `Std.Do` carrier. -/
def gradedBind {ps : PostShape} {α β : Type} {g₁ g₂ : G}
    (t : GradedPT g₁ ps α) (f : α → GradedPT g₂ ps β) : GradedPT (g₁ + g₂) ps β :=
  ⟨PredTrans.bind t.pt (fun a => (f a).pt)⟩

omit [Zero G] in
/-- **THE WALL, made provable.** The underlying transformer of a *graded* bind is the
    **ordinary, grade-free** `PredTrans.bind` — the sum `g₁ + g₂` lives only in the
    type tag, never in the object. Since `mvcgen` and every `@[spec]` `Triple` speak
    only about this grade-erased object (via `WP.wp`/`GradedPT.forget`), **no spec
    lemma can make the grade accumulate out-of-band.** A faithful spec-only grade
    therefore *requires* a `.graded G` `PostShape` constructor plus a grade-additive
    `bind` spec — it is not expressible by a library lemma over the fixed carrier. -/
theorem forget_gradedBind {ps : PostShape} {α β : Type} {g₁ g₂ : G}
    (t : GradedPT g₁ ps α) (f : α → GradedPT g₂ ps β) :
    (gradedBind t f).forget = PredTrans.bind t.forget (fun a => (f a).forget) := rfl

omit [Zero G] [Add G] in
/-- Corollary: the grade tag is invisible below `forget`. Two differently-graded
    wrappers of the *same* transformer forget to the *same* object — the object
    `mvcgen` sees cannot distinguish grades, so it cannot track them. -/
theorem forget_grade_irrelevant {ps : PostShape} {α : Type} {g g' : G}
    (x : PredTrans ps α) :
    (GradedPT.forget (g := g) ⟨x⟩) = (GradedPT.forget (g := g') ⟨x⟩) := rfl

end GradeTag

end CatCrypt.Crypto.SecureCompilation.Ascent.GradedMvcgenProbe
