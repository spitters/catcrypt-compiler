/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Relational.Approx

/-!
# Identical-Until-Bad as a Graded Exception Structure

This file gives the precise algebraic statement of the up-to-bad technique:
**identical-until-bad is exact equality after bad-truncation, and the grade of
the up-to-bad rule is exactly the truncated (= "thrown") mass.**

## The truncation

For a bad event `bad : α → Prop` on outcomes, `truncBad bad d` is the
bad-stopping transformation of a sub-distribution `d : SDistr α`: the mass on
bad outcomes is redirected to the failure point. In the sub-probability
setting (`SDistr α = PMF (Option α)`) the exception monad's `throw` is
literally available as `none`, so the truncation is the Kleisli extension of
the "throw on bad" arrow:

    truncBad bad d = d.bind fun a => if bad a then fail else pure a

**Design note (`none` vs `Except`)**: redirecting bad mass into `none` merges
it with pre-existing failure (non-termination) mass. This collision is
*harmless* for the factorization theorem (a `PMF` is determined by its `some`
entries, `SDistr.eq_of_some_eq`) and for the TV-transport (`tvMargin` ignores
the `none` mass). It *does* matter for grade recovery: equal truncations pin
down only the **sum** `d none + badMass bad d` (`truncBad_apply_none`,
`badMass_balance`), so recovering `Pr[bad]` from the truncated program needs
`NoFail` — exactly the side condition already carried by
`rHoareApprox_upto_bad` and `BadEvent.advantage_upto_bad`. The tagged variant
`truncBadE : SDistr α → SDistr (Except Unit α)` keeps the two failure modes
apart (`throw = some (.error ())`, non-termination = `none`) and yields the
side-condition-free characterization `truncBadE_eq_iff`; it erases onto the
untagged form (`truncBadE_erase`).

## The factorization theorem

`eqUntilBad_iff_truncBad_eq`: two sub-distributions agree off the bad event
**iff** their bad-truncations are *equal on the nose*. This is an unconditional
iff — no `NoFail`, no mass side conditions — because the truncations' `some`
entries are `0` on bad outcomes and the original masses elsewhere. The grade is
recoverable: the mass truncated on each side is the bad probability,
`tvMargin d (truncBad bad d) = badMass bad d` (`tvMargin_truncBad`), and for
`NoFail` games equal truncations force *equal* bad probabilities on the two
sides (`badMass_eq_of_none_eq_zero` — the disjoint-support mass balance that
`rHoareApprox_upto_bad` obtains analytically from `tv_both_le_of_pointwise`).

## The graded reading

`liftRApprox_eq_of_truncBad_eq` re-derives the content of the up-to-bad rule
from the factorization: exact equality of the truncations plus a bound on the
truncated mass yields the grade-`ε` lifting, by pure transport — each game is
within `tvMargin ≤ badMass ≤ ε` of the *common* truncation, and the
truncation embeds exactly (its one-sided distance to the original is `0`,
`tvMargin_truncBad_le_zero`). The relational rule
`rHoareApprox_upto_bad_trunc` and the advantage bound
`advantageA_upto_bad_trunc` (Shoup's fundamental lemma, for the
exact-agreement form of identical-until-bad) follow. The bridge lemmas
`identicalUntilBad_badProg` / `prTrue_badProg` connect to the inequality-form
vocabulary of `CatCrypt.Crypto.BadEvent`: the predicate form provides, for
each direction, a bad *program* witnessing `IdenticalUntilBad` whose `prTrue`
is exactly the bad mass. (The two directions need the two different witnesses
`badProg bad G₀` / `badProg bad G₁`; a single shared bad program would have to
dominate both games' bad-conditioned mass pointwise, which equal truncations
do not provide. The direct derivation bypasses this.)

## The algebraic packaging

Bad events grade the exception structure of `SDistr`, with grades in the
additive monoid `(ℝ≥0∞, +, 0)` — the graded-monad tradition of Katsumata's
parametric effect monads (POPL 2014), here in sub-probability form:

* **unit**: `truncBad bad (pure a) = pure a` off bad, and
  `badMass bad (pure a) = if bad a then 1 else 0` (`truncBad_pure_of_not_bad`,
  `badMass_pure`);
* **bind, grades add**: exception mass composes additively,
  `(d.bind k) none ≤ ε₁ + ε₂` from `d none ≤ ε₁` and pointwise
  `(k a) none ≤ ε₂` (`bind_none_le`), and bad mass is non-expansive under
  bind, `badMass bb (d.bind k) ≤ ε` from pointwise bounds (`badMass_bind_le`);
* **union bound**: `badMass_or_le`, mirroring
  `BadEvent.prTrue_union_bound`;
* **truncations compose**: bad-stopping composites of equal truncations are
  equal (`truncBad_bind_congr`) — note the composite stops at the *first* bad
  event along the run, which is a trace event, not in general the truncation
  of the composite by any single event on the output type — and the composite
  graded statement `GradedUntilBad.bind`: graded-until-bad data for the
  prefixes at `ε₁` and for the continuations at `ε₂` yields the
  grade-`(ε₁ + ε₂)` lifting of the binds, via the common stopped composite
  (`tvMargin_bind_trunc_le` controls the stopped mass by
  `badMass + ε₂`, the graded bind law).

`GradedUntilBad bad d₀ d₁ ε` bundles the factorized form (truncation equality
+ both bad masses ≤ ε); it is the algebraic normal form of the up-to-bad
hypothesis pair consumed by `rHoareApprox_upto_bad`.

## Main definitions

* `badMass bad d` — probability mass of `d` on the bad event
* `truncBad bad d` — bad-stopping truncation (throw to `none`)
* `truncBadE bad d` — tagged truncation into `SDistr (Except Unit α)`
* `EqUntilBad bad d₀ d₁` — distribution-level identical-until-bad
  (exact agreement off bad)
* `GradedUntilBad bad d₀ d₁ ε` — bundled graded form

## Main results

* `eqUntilBad_iff_truncBad_eq` — **the factorization**: identical-until-bad
  ↔ equality of the truncations (unconditional iff)
* `truncBadE_eq_iff` — tagged factorization: equality of tagged truncations
  ↔ agreement off bad **and** equal bad masses (no `NoFail` needed)
* `tvMargin_truncBad` — the truncated mass *is* the bad probability
* `badMass_balance` / `badMass_eq_of_none_eq_zero` — mass balance: equal
  truncations balance failure + bad mass; under `NoFail` the bad
  probabilities agree
* `liftRApprox_eq_of_truncBad_eq` — the graded reading: truncation equality
  + truncated-mass bound ⟹ grade-`ε` lifting (transport along the exact
  embedding of the truncation)
* `rHoareApprox_upto_bad_trunc` / `advantageA_upto_bad_trunc` — the
  up-to-bad rule and Shoup's advantage bound re-derived through the
  factorization
* `identicalUntilBad_badProg`, `prTrue_badProg` — bridge to the
  inequality-form `BadEvent.IdenticalUntilBad` vocabulary
* `bind_none_le`, `badMass_bind_le`, `truncBad_bind_congr`,
  `GradedUntilBad.bind` — the graded bind laws

## References

* V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security
  Proofs*, ePrint 2004/332, Lemma 1 — the up-to-bad technique.
* M. Bellare, P. Rogaway, *The Security of Triple Encryption and a Framework
  for Code-Based Game-Playing Proofs*, EUROCRYPT 2006 — identical-until-bad
  for code-based games (the exact-agreement form factorized here).
* S. Katsumata, *Parametric Effect Monads and Semantics of Effect Systems*,
  POPL 2014 — monads graded by an ordered monoid; the classical source for
  the graded-monad framing (the precise instance here — `ℝ≥0∞`-weighted
  exception mass on the sub-Giry monad — is folklore as far as we know).
* T. Sato, *Approximate Span Liftings*, LICS 2019 — the graded relational
  layer (`liftRApprox`) this file transports into.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Prob

open scoped ENNReal

variable {α β : Type*}

/-! ## tsub helpers -/

private theorem tsum_tsub_tsum_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' i, f i) - (∑' i, g i) ≤ ∑' i, (f i - g i) := by
  rw [tsub_le_iff_right]
  calc ∑' i, f i
      ≤ ∑' i, ((f i - g i) + g i) := ENNReal.tsum_le_tsum fun i => le_tsub_add
    _ = (∑' i, (f i - g i)) + ∑' i, g i := ENNReal.tsum_add

private theorem mul_tsub_le' (a x y : ℝ≥0∞) : a * x - a * y ≤ a * (x - y) := by
  rw [tsub_le_iff_right, ← mul_add]
  exact mul_le_mul_right le_tsub_add a

/-! ## Bad mass and the bad-stopping truncation -/

/-- The probability mass of a sub-distribution on a bad event. This is the
    grade of the up-to-bad rule: `Pr[bad]` for the distribution `d`. -/
noncomputable def badMass (bad : α → Prop) [DecidablePred bad] (d : SDistr α) : ℝ≥0∞ :=
  ∑' a, if bad a then d (some a) else 0

/-- **The bad-stopping truncation**: redirect the mass on bad outcomes to the
    failure point `none`. In the sub-probability setting the exception monad's
    `throw` is literally `SDistr.fail`, so this is the Kleisli extension of
    the "throw on bad" arrow. -/
noncomputable def truncBad (bad : α → Prop) [DecidablePred bad] (d : SDistr α) : SDistr α :=
  d.bind fun a => if bad a then SDistr.fail else SDistr.pure a

/-- Tagged bad-stopping truncation into the exception monad: bad outcomes are
    sent to the *tagged* exception `Except.error ()`, kept apart from the
    untagged failure mass at `none` (non-termination). Use this form when the
    two failure modes must be distinguished (grade recovery without a
    `NoFail` hypothesis, `truncBadE_eq_iff`). -/
noncomputable def truncBadE (bad : α → Prop) [DecidablePred bad] (d : SDistr α) :
    SDistr (Except Unit α) :=
  d.bind fun a =>
    if bad a then SDistr.pure (Except.error ()) else SDistr.pure (Except.ok a)

section BadMass

variable (bad : α → Prop) [DecidablePred bad]

theorem badMass_le_one (d : SDistr α) : badMass bad d ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum fun a => ?_) (SDistr.tsum_some_le_one d)
  by_cases h : bad a <;> simp [h]

theorem badMass_ne_top (d : SDistr α) : badMass bad d ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (badMass_le_one bad d)

/-- Bad mass is monotone in the bad event. -/
theorem badMass_mono {bad' : α → Prop} [DecidablePred bad']
    (hb : ∀ a, bad a → bad' a) (d : SDistr α) :
    badMass bad d ≤ badMass bad' d := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases h : bad a
  · simp [h, hb a h]
  · simp [h]

/-- **Union bound** for bad masses (Boole's inequality), the distribution-level
    analogue of `BadEvent.prTrue_union_bound`. -/
theorem badMass_or_le (bad' : α → Prop) [DecidablePred bad'] (d : SDistr α) :
    badMass (fun a => bad a ∨ bad' a) d ≤ badMass bad d + badMass bad' d := by
  rw [badMass, badMass, badMass, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases h : bad a <;> by_cases h' : bad' a <;> simp [h, h']

/-- Bad mass of a point mass: the indicator of the bad event (unit law of the
    graded structure). -/
theorem badMass_pure (a : α) :
    badMass bad (SDistr.pure a) = if bad a then 1 else 0 := by
  classical
  rw [badMass]
  rw [tsum_eq_single a]
  · by_cases h : bad a <;> simp [h]
  · intro a' hne
    by_cases h : bad a' <;> simp [h, Ne.symm hne]

end BadMass

/-! ## A `bind` application formula at `none`

The `some` analogue is `SDistr.bind_apply_some` (SpanLifting). At `none`, the
failure mass of the prefix passes through (`fail` has mass `1` on `none`) and
each successful prefix outcome contributes its continuation's failure mass. -/

theorem SDistr.bind_apply_none (d : SDistr α) (f : α → SDistr β) :
    (d.bind f) none = d none + ∑' a, d (some a) * (f a) none := by
  show (PMF.bind d _) none = _
  rw [PMF.bind_apply, SDistr.tsum_option_eq_add]
  congr 1
  simp

/-- **Graded exception bind law, grades add**: if the prefix throws with mass
    at most `ε₁` and each continuation (on the support) throws with mass at
    most `ε₂`, the composite throws with mass at most `ε₁ + ε₂`. This is the
    `(ℝ≥0∞, +, 0)`-graded bind of the exception structure. -/
theorem bind_none_le {d : SDistr α} {k : α → SDistr β} {ε₁ ε₂ : ℝ≥0∞}
    (hd : d none ≤ ε₁) (hk : ∀ a, d (some a) ≠ 0 → (k a) none ≤ ε₂) :
    (d.bind k) none ≤ ε₁ + ε₂ := by
  rw [SDistr.bind_apply_none]
  refine add_le_add hd ?_
  calc ∑' a, d (some a) * (k a) none
      ≤ ∑' a, d (some a) * ε₂ := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases h0 : d (some a) = 0
        · simp [h0]
        · exact mul_le_mul_right (hk a h0) _
    _ = (∑' a, d (some a)) * ε₂ := ENNReal.tsum_mul_right
    _ ≤ 1 * ε₂ := mul_le_mul_left (SDistr.tsum_some_le_one d) _
    _ = ε₂ := one_mul _

/-- Bad mass is non-expansive under bind: a pointwise bad-mass bound on the
    continuations (on the support) bounds the bad mass of the composite.
    (The prefix's own bad event is accounted separately — see
    `tvMargin_bind_trunc_le`.) -/
theorem badMass_bind_le {bb : β → Prop} [DecidablePred bb]
    {d : SDistr α} {k : α → SDistr β} {ε : ℝ≥0∞}
    (hk : ∀ a, d (some a) ≠ 0 → badMass bb (k a) ≤ ε) :
    badMass bb (d.bind k) ≤ ε := by
  have hsum : badMass bb (d.bind k) = ∑' a, d (some a) * badMass bb (k a) := by
    rw [badMass]
    calc ∑' b, (if bb b then (d.bind k) (some b) else 0)
        = ∑' b, ∑' a, d (some a) * (if bb b then (k a) (some b) else 0) := by
          refine tsum_congr fun b => ?_
          by_cases h : bb b
          · simp only [h, if_true]
            exact SDistr.bind_apply_some d k b
          · simp [h]
      _ = ∑' a, ∑' b, d (some a) * (if bb b then (k a) (some b) else 0) :=
          ENNReal.tsum_comm
      _ = ∑' a, d (some a) * badMass bb (k a) := by
          refine tsum_congr fun a => ?_
          rw [badMass, ENNReal.tsum_mul_left]
  rw [hsum]
  calc ∑' a, d (some a) * badMass bb (k a)
      ≤ ∑' a, d (some a) * ε := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases h0 : d (some a) = 0
        · simp [h0]
        · exact mul_le_mul_right (hk a h0) _
    _ = (∑' a, d (some a)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul_left (SDistr.tsum_some_le_one d) _
    _ = ε := one_mul _

/-! ## Application formulas for the truncation -/

section TruncApply

variable (bad : α → Prop) [DecidablePred bad]

/-- The truncation kills bad outcomes and keeps the rest. -/
theorem truncBad_apply_some (d : SDistr α) (a : α) :
    truncBad bad d (some a) = if bad a then 0 else d (some a) := by
  classical
  rw [truncBad, SDistr.bind_apply_some]
  rw [tsum_eq_single a]
  · by_cases h : bad a <;> simp [h]
  · intro a' hne
    by_cases h : bad a' <;> simp [h, hne]

/-- The truncation's failure mass is the original failure mass **plus** the
    truncated bad mass — the collision point of `none`-as-bad with
    `none`-as-failure (see the module docstring; `truncBadE` disambiguates). -/
theorem truncBad_apply_none (d : SDistr α) :
    truncBad bad d none = d none + badMass bad d := by
  rw [truncBad, SDistr.bind_apply_none, badMass]
  congr 1
  refine tsum_congr fun a => ?_
  by_cases h : bad a <;> simp [h]

/-- The truncation is dominated by the original on successful outcomes. -/
theorem truncBad_le_some (d : SDistr α) (a : α) :
    truncBad bad d (some a) ≤ d (some a) := by
  rw [truncBad_apply_some]
  by_cases h : bad a <;> simp [h]

/-- Truncating a point mass at a non-bad value is the identity (unit law of
    the graded structure; on a bad value it is `fail` by `pure_bind`). -/
theorem truncBad_pure_of_not_bad {a : α} (h : ¬ bad a) :
    truncBad bad (SDistr.pure a) = SDistr.pure a := by
  rw [truncBad, SDistr.pure_bind, if_neg h]

end TruncApply

/-! ## The factorization theorem -/

/-- Distribution-level **identical-until-bad**: exact agreement of the output
    masses off the bad event. This is the semantic content of
    Bellare–Rogaway's syntactic "identical-until-bad" for code-based games
    (the two programs share all code outside the `bad`-flagged branch). -/
def EqUntilBad (bad : α → Prop) (d₀ d₁ : SDistr α) : Prop :=
  ∀ a, ¬ bad a → d₀ (some a) = d₁ (some a)

theorem EqUntilBad.symm {bad : α → Prop} {d₀ d₁ : SDistr α}
    (h : EqUntilBad bad d₀ d₁) : EqUntilBad bad d₁ d₀ :=
  fun a ha => (h a ha).symm

/-- **The factorization theorem** (the heart of the file): two
    sub-distributions are identical until bad **iff** their bad-truncations
    are equal on the nose. Unconditional — no `NoFail`, no mass side
    conditions: the truncations agree at `none` automatically because a `PMF`
    is determined by its `some` entries. Up-to-bad is exact equality in the
    image of the bad-stopping transformation. -/
theorem eqUntilBad_iff_truncBad_eq (bad : α → Prop) [DecidablePred bad]
    (d₀ d₁ : SDistr α) :
    EqUntilBad bad d₀ d₁ ↔ truncBad bad d₀ = truncBad bad d₁ := by
  constructor
  · intro h
    apply SDistr.eq_of_some_eq
    intro a
    rw [truncBad_apply_some, truncBad_apply_some]
    by_cases hb : bad a
    · simp [hb]
    · simp [hb, h a hb]
  · intro h a ha
    have := congrArg (fun d : SDistr α => d (some a)) h
    simpa [truncBad_apply_some, ha] using this

/-- **Mass balance**: equal truncations balance failure mass against bad mass
    — the truncated `none` entries agree, so `d₀ none + Pr₀[bad] = d₁ none +
    Pr₁[bad]`. Bad mass alone is *not* determined (the `none`-collision). -/
theorem badMass_balance {bad : α → Prop} [DecidablePred bad] {d₀ d₁ : SDistr α}
    (h : truncBad bad d₀ = truncBad bad d₁) :
    d₀ none + badMass bad d₀ = d₁ none + badMass bad d₁ := by
  have := congrArg (fun d : SDistr α => d none) h
  simpa [truncBad_apply_none] using this

/-- For failure-free distributions, equal truncations force **equal** bad
    probabilities — the disjoint-support mass balance behind the symmetric
    grade of `rHoareApprox_upto_bad` (there obtained analytically inside
    `tv_both_le_of_pointwise`). -/
theorem badMass_eq_of_none_eq_zero {bad : α → Prop} [DecidablePred bad]
    {d₀ d₁ : SDistr α} (h : truncBad bad d₀ = truncBad bad d₁)
    (h₀ : d₀ none = 0) (h₁ : d₁ none = 0) :
    badMass bad d₀ = badMass bad d₁ := by
  have hb := badMass_balance h
  rwa [h₀, h₁, zero_add, zero_add] at hb

/-! ## Grade recovery: the truncated mass is the bad probability -/

/-- The one-sided statistical distance from a distribution to its truncation
    is **exactly** the bad mass: the grade of the up-to-bad rule is the
    thrown exception mass, on the nose. -/
theorem tvMargin_truncBad (bad : α → Prop) [DecidablePred bad] (d : SDistr α) :
    tvMargin d (truncBad bad d) = badMass bad d := by
  rw [tvMargin, badMass]
  refine tsum_congr fun a => ?_
  rw [truncBad_apply_some]
  by_cases h : bad a <;> simp [h]

/-- The truncation embeds exactly: its one-sided distance back to the
    original is `0` (it is pointwise dominated on successful outcomes). -/
theorem tvMargin_truncBad_le_zero (bad : α → Prop) [DecidablePred bad] (d : SDistr α) :
    tvMargin (truncBad bad d) d = 0 := by
  rw [tvMargin]
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  exact tsub_eq_zero_of_le (truncBad_le_some bad d a)

/-- One-sided distance vanishes under pointwise domination (helper). -/
theorem tvMargin_eq_zero_of_le {d₀ d₁ : SDistr α}
    (h : ∀ a, d₀ (some a) ≤ d₁ (some a)) : tvMargin d₀ d₁ = 0 := by
  rw [tvMargin]
  exact ENNReal.tsum_eq_zero.mpr fun a => tsub_eq_zero_of_le (h a)

/-! ## The graded reading: transport along the truncation

The up-to-bad rule factors: exact equality of the truncations + a bound on
the truncated mass gives the grade-`ε` lifting, by the triangle inequality
through the *common* truncation. This is the exact-embedding + TV-transport
decomposition of `rHoareApprox_upto_bad`. -/

/-- **Up-to-bad from the factorization**: equal truncations within truncated
    mass `ε` on each side relate at grade `ε` with equality. No `NoFail`
    hypothesis (compare `rHoareApprox_upto_bad`): the two bad-mass bounds are
    taken separately; under `NoFail` they coincide
    (`badMass_eq_of_none_eq_zero`). -/
theorem liftRApprox_eq_of_truncBad_eq {bad : α → Prop} [DecidablePred bad]
    {d₀ d₁ : SDistr α} {ε : ℝ≥0∞}
    (h : truncBad bad d₀ = truncBad bad d₁)
    (h₀ : badMass bad d₀ ≤ ε) (h₁ : badMass bad d₁ ≤ ε) :
    liftRApprox ε Eq d₀ d₁ := by
  refine liftRApprox_eq_of_tv ?_ ?_
  · calc tvMargin d₀ d₁
        ≤ tvMargin d₀ (truncBad bad d₀) + tvMargin (truncBad bad d₀) d₁ :=
          tvMargin_triangle _ _ _
      _ = badMass bad d₀ + 0 := by
          rw [tvMargin_truncBad, h, tvMargin_truncBad_le_zero]
      _ ≤ ε := by simpa using h₀
  · calc tvMargin d₁ d₀
        ≤ tvMargin d₁ (truncBad bad d₁) + tvMargin (truncBad bad d₁) d₀ :=
          tvMargin_triangle _ _ _
      _ = badMass bad d₁ + 0 := by
          rw [tvMargin_truncBad, ← h, tvMargin_truncBad_le_zero]
      _ ≤ ε := by simpa using h₁

/-- The same-grade statement directly from the identical-until-bad predicate
    (factorization applied left-to-right). -/
theorem liftRApprox_eq_of_eqUntilBad {bad : α → Prop} [DecidablePred bad]
    {d₀ d₁ : SDistr α} {ε : ℝ≥0∞}
    (h : EqUntilBad bad d₀ d₁)
    (h₀ : badMass bad d₀ ≤ ε) (h₁ : badMass bad d₁ ≤ ε) :
    liftRApprox ε Eq d₀ d₁ :=
  liftRApprox_eq_of_truncBad_eq ((eqUntilBad_iff_truncBad_eq bad d₀ d₁).mp h) h₀ h₁

/-! ## The tagged truncation: separating `throw` from non-termination -/

section TruncE

variable (bad : α → Prop) [DecidablePred bad]

theorem truncBadE_apply_ok (d : SDistr α) (a : α) :
    truncBadE bad d (some (Except.ok a)) = if bad a then 0 else d (some a) := by
  classical
  rw [truncBadE, SDistr.bind_apply_some]
  rw [tsum_eq_single a]
  · by_cases h : bad a <;> simp [h]
  · intro a' hne
    by_cases h : bad a' <;> simp [h, hne]

/-- The tagged exception carries exactly the bad mass — grade recovery with
    no `NoFail` side condition. -/
theorem truncBadE_apply_error (d : SDistr α) :
    truncBadE bad d (some (Except.error ())) = badMass bad d := by
  classical
  rw [truncBadE, SDistr.bind_apply_some, badMass]
  refine tsum_congr fun a => ?_
  by_cases h : bad a <;> simp [h]

/-- The tagged truncation leaves the genuine failure mass untouched. -/
theorem truncBadE_apply_none (d : SDistr α) :
    truncBadE bad d none = d none := by
  rw [truncBadE, SDistr.bind_apply_none]
  have hz : ∀ a : α, d (some a) *
      ((if bad a then SDistr.pure (Except.error ()) else SDistr.pure (Except.ok a)) :
        SDistr (Except Unit α)) none = 0 := by
    intro a
    by_cases h : bad a <;> simp [h]
  rw [ENNReal.tsum_eq_zero.mpr hz, add_zero]

/-- **Tagged factorization**: equality of the tagged truncations is exactly
    identical-until-bad **plus** equality of the bad masses — the
    side-condition-free sharpening of `eqUntilBad_iff_truncBad_eq` +
    `badMass_eq_of_none_eq_zero`, available because the tag keeps thrown mass
    apart from non-termination mass. -/
theorem truncBadE_eq_iff (d₀ d₁ : SDistr α) :
    truncBadE bad d₀ = truncBadE bad d₁ ↔
      EqUntilBad bad d₀ d₁ ∧ badMass bad d₀ = badMass bad d₁ := by
  constructor
  · intro h
    constructor
    · intro a ha
      have := congrArg (fun d : SDistr (Except Unit α) => d (some (Except.ok a))) h
      simpa [truncBadE_apply_ok, ha] using this
    · have := congrArg
        (fun d : SDistr (Except Unit α) => d (some (Except.error ()))) h
      simpa [truncBadE_apply_error] using this
  · rintro ⟨hagree, hmass⟩
    apply SDistr.eq_of_some_eq
    intro e
    match e with
    | Except.error () =>
      rw [truncBadE_apply_error, truncBadE_apply_error, hmass]
    | Except.ok a =>
      rw [truncBadE_apply_ok, truncBadE_apply_ok]
      by_cases hb : bad a
      · simp [hb]
      · simp [hb, hagree a hb]

/-- Erasing the tag recovers the untagged truncation: the tagged exception is
    folded back into the failure point. -/
theorem truncBadE_erase (d : SDistr α) :
    ((truncBadE bad d).bind fun e =>
      match e with
      | Except.ok a => SDistr.pure a
      | Except.error _ => SDistr.fail) = truncBad bad d := by
  rw [truncBadE, truncBad, SDistr.bind_assoc]
  congr 1
  funext a
  by_cases h : bad a <;> simp [h, SDistr.pure_bind]

end TruncE

/-! ## The bundled graded form and its bind law -/

/-- **Graded-until-bad**: the algebraic normal form of an up-to-bad hop.
    `GradedUntilBad bad d₀ d₁ ε` packages the factorized statement — exact
    equality of the bad-truncations, with the truncated mass (= the grade)
    bounded by `ε` on each side. By `eqUntilBad_iff_truncBad_eq` the first
    field is equivalent to identical-until-bad; by
    `liftRApprox_eq_of_truncBad_eq` the bundle yields the grade-`ε`
    lifting. -/
structure GradedUntilBad (bad : α → Prop) [DecidablePred bad]
    (d₀ d₁ : SDistr α) (ε : ℝ≥0∞) : Prop where
  /-- The bad-truncations are equal on the nose (identical-until-bad). -/
  trunc_eq : truncBad bad d₀ = truncBad bad d₁
  /-- The left truncated mass (= `Pr₀[bad]`) is within the grade. -/
  badMass_left : badMass bad d₀ ≤ ε
  /-- The right truncated mass (= `Pr₁[bad]`) is within the grade. -/
  badMass_right : badMass bad d₁ ≤ ε

namespace GradedUntilBad

variable {bad : α → Prop} [DecidablePred bad] {d₀ d₁ : SDistr α} {ε : ℝ≥0∞}

theorem symm (h : GradedUntilBad bad d₀ d₁ ε) : GradedUntilBad bad d₁ d₀ ε :=
  ⟨h.trunc_eq.symm, h.badMass_right, h.badMass_left⟩

theorem eqUntilBad (h : GradedUntilBad bad d₀ d₁ ε) : EqUntilBad bad d₀ d₁ :=
  (eqUntilBad_iff_truncBad_eq bad d₀ d₁).mpr h.trunc_eq

theorem mono_eps {ε' : ℝ≥0∞} (hε : ε ≤ ε') (h : GradedUntilBad bad d₀ d₁ ε) :
    GradedUntilBad bad d₀ d₁ ε' :=
  ⟨h.trunc_eq, h.badMass_left.trans hε, h.badMass_right.trans hε⟩

/-- The graded reading of a bundle: grade-`ε` lifting at equality. -/
theorem liftRApprox (h : GradedUntilBad bad d₀ d₁ ε) :
    liftRApprox ε Eq d₀ d₁ :=
  liftRApprox_eq_of_truncBad_eq h.trunc_eq h.badMass_left h.badMass_right

end GradedUntilBad

/-! ## Composition: truncations of binds

The bad-stopping composite `(truncBad b₁ d).bind (truncBad b₂ ∘ k)` stops a
sequential program at the *first* bad event along the run. Equal truncations
compose to equal composites (`truncBad_bind_congr`), and the composite's
distance to the original bind is controlled by the summed grades
(`tvMargin_bind_trunc_le`) — together these give the graded bind
`GradedUntilBad.bind`. Note the run-level stopping event is a *trace* event:
the composite is in general not `truncBad` of `d.bind k` by any single event
on the output type, which is why the graded structure lives on Kleisli
arrows with bad-stopping composition. -/

/-- Bad-stopping composites of equal truncations are equal: the prefix
    truncations agree, and on the (necessarily non-bad) support the
    continuation truncations agree. -/
theorem truncBad_bind_congr {b₁ : α → Prop} [DecidablePred b₁]
    {b₂ : β → Prop} [DecidablePred b₂]
    {d₀ d₁ : SDistr α} {k₀ k₁ : α → SDistr β}
    (hd : truncBad b₁ d₀ = truncBad b₁ d₁)
    (hk : ∀ a, ¬ b₁ a → truncBad b₂ (k₀ a) = truncBad b₂ (k₁ a)) :
    (truncBad b₁ d₀).bind (fun a => truncBad b₂ (k₀ a)) =
      (truncBad b₁ d₁).bind (fun a => truncBad b₂ (k₁ a)) := by
  rw [hd]
  refine SDistr.bind_congr_support fun a ha => ?_
  refine hk a fun hb => ha ?_
  rw [truncBad_apply_some, if_pos hb]

/-- The bad-stopping composite is dominated by the original bind on
    successful outcomes. -/
theorem bind_trunc_le_some {b₁ : α → Prop} [DecidablePred b₁]
    {b₂ : β → Prop} [DecidablePred b₂]
    (d : SDistr α) (k : α → SDistr β) (b : β) :
    ((truncBad b₁ d).bind fun a => truncBad b₂ (k a)) (some b)
      ≤ (d.bind k) (some b) := by
  rw [SDistr.bind_apply_some, SDistr.bind_apply_some]
  exact ENNReal.tsum_le_tsum fun a =>
    mul_le_mul' (truncBad_le_some b₁ d a) (truncBad_le_some b₂ (k a) b)

/-- **Graded bind law for the truncated mass**: the one-sided distance from a
    bind to its bad-stopping composite is at most the prefix's bad mass plus
    the (uniform) continuation grade — grades add along Kleisli
    composition. -/
theorem tvMargin_bind_trunc_le {b₁ : α → Prop} [DecidablePred b₁]
    {b₂ : β → Prop} [DecidablePred b₂]
    (d : SDistr α) (k : α → SDistr β) {ε₂ : ℝ≥0∞}
    (hk : ∀ a, d (some a) ≠ 0 → ¬ b₁ a → badMass b₂ (k a) ≤ ε₂) :
    tvMargin (d.bind k) ((truncBad b₁ d).bind fun a => truncBad b₂ (k a))
      ≤ badMass b₁ d + ε₂ := by
  have hper : ∀ a, (∑' b, (d (some a) * (k a) (some b)
        - truncBad b₁ d (some a) * truncBad b₂ (k a) (some b)))
      ≤ (if b₁ a then d (some a) else 0) + d (some a) * ε₂ := by
    intro a
    by_cases h0 : d (some a) = 0
    · have ht : truncBad b₁ d (some a) = 0 := by
        rw [truncBad_apply_some]
        simp [h0]
      simp [h0, ht]
    by_cases hb : b₁ a
    · have ht : truncBad b₁ d (some a) = 0 := by
        rw [truncBad_apply_some, if_pos hb]
      calc ∑' b, (d (some a) * (k a) (some b)
              - truncBad b₁ d (some a) * truncBad b₂ (k a) (some b))
          = ∑' b, d (some a) * (k a) (some b) := by
            refine tsum_congr fun b => ?_
            rw [ht, zero_mul, tsub_zero]
        _ = d (some a) * ∑' b, (k a) (some b) := ENNReal.tsum_mul_left
        _ ≤ d (some a) * 1 := mul_le_mul_right (SDistr.tsum_some_le_one (k a)) _
        _ = d (some a) := mul_one _
        _ ≤ _ := by rw [if_pos hb]; exact le_self_add
    · have ht : truncBad b₁ d (some a) = d (some a) := by
        rw [truncBad_apply_some, if_neg hb]
      calc ∑' b, (d (some a) * (k a) (some b)
              - truncBad b₁ d (some a) * truncBad b₂ (k a) (some b))
          = ∑' b, (d (some a) * (k a) (some b)
              - d (some a) * truncBad b₂ (k a) (some b)) := by rw [ht]
        _ ≤ ∑' b, d (some a) * ((k a) (some b) - truncBad b₂ (k a) (some b)) :=
            ENNReal.tsum_le_tsum fun b => mul_tsub_le' _ _ _
        _ = d (some a) * badMass b₂ (k a) := by
            rw [ENNReal.tsum_mul_left]
            exact congrArg (d (some a) * ·) (tvMargin_truncBad b₂ (k a))
        _ ≤ d (some a) * ε₂ := mul_le_mul_right (hk a h0 hb) _
        _ ≤ _ := by rw [if_neg hb, zero_add]
  calc tvMargin (d.bind k) ((truncBad b₁ d).bind fun a => truncBad b₂ (k a))
      ≤ ∑' b, ∑' a, (d (some a) * (k a) (some b)
          - truncBad b₁ d (some a) * truncBad b₂ (k a) (some b)) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [SDistr.bind_apply_some, SDistr.bind_apply_some]
        exact tsum_tsub_tsum_le _ _
    _ = ∑' a, ∑' b, (d (some a) * (k a) (some b)
          - truncBad b₁ d (some a) * truncBad b₂ (k a) (some b)) :=
        ENNReal.tsum_comm
    _ ≤ ∑' a, ((if b₁ a then d (some a) else 0) + d (some a) * ε₂) :=
        ENNReal.tsum_le_tsum hper
    _ = badMass b₁ d + ∑' a, d (some a) * ε₂ := by
        rw [ENNReal.tsum_add, badMass]
    _ ≤ badMass b₁ d + ε₂ := by
        refine add_le_add le_rfl ?_
        calc ∑' a, d (some a) * ε₂
            = (∑' a, d (some a)) * ε₂ := ENNReal.tsum_mul_right
          _ ≤ 1 * ε₂ := mul_le_mul_left (SDistr.tsum_some_le_one d) _
          _ = ε₂ := one_mul _

/-- **Graded composition**: graded-until-bad prefixes at `ε₁` and pointwise
    graded-until-bad continuations at `ε₂` (off the prefix bad event) give the
    grade-`(ε₁ + ε₂)` lifting of the binds — transport through the *common*
    bad-stopping composite (`truncBad_bind_congr`), whose distance to each
    bind is at most `badMass + ε₂ ≤ ε₁ + ε₂` (`tvMargin_bind_trunc_le`). This
    is the up-to-bad analogue of `liftRApprox_bind`. -/
theorem GradedUntilBad.bind {b₁ : α → Prop} [DecidablePred b₁]
    {b₂ : β → Prop} [DecidablePred b₂]
    {d₀ d₁ : SDistr α} {k₀ k₁ : α → SDistr β} {ε₁ ε₂ : ℝ≥0∞}
    (hd : GradedUntilBad b₁ d₀ d₁ ε₁)
    (hk : ∀ a, ¬ b₁ a → GradedUntilBad b₂ (k₀ a) (k₁ a) ε₂) :
    _root_.CatCrypt.Prob.liftRApprox (ε₁ + ε₂) Eq (d₀.bind k₀) (d₁.bind k₁) := by
  have hcomp : (truncBad b₁ d₀).bind (fun a => truncBad b₂ (k₀ a))
      = (truncBad b₁ d₁).bind (fun a => truncBad b₂ (k₁ a)) :=
    truncBad_bind_congr hd.trunc_eq fun a ha => (hk a ha).trunc_eq
  refine liftRApprox_eq_of_tv ?_ ?_
  · calc tvMargin (d₀.bind k₀) (d₁.bind k₁)
        ≤ tvMargin (d₀.bind k₀) ((truncBad b₁ d₀).bind fun a => truncBad b₂ (k₀ a))
            + tvMargin ((truncBad b₁ d₀).bind fun a => truncBad b₂ (k₀ a))
                (d₁.bind k₁) := tvMargin_triangle _ _ _
      _ ≤ (badMass b₁ d₀ + ε₂) + 0 := by
          refine add_le_add
            (tvMargin_bind_trunc_le d₀ k₀ fun a _ ha => (hk a ha).badMass_left) ?_
          rw [hcomp]
          exact le_of_eq (tvMargin_eq_zero_of_le fun b => bind_trunc_le_some d₁ k₁ b)
      _ ≤ ε₁ + ε₂ := by
          rw [add_zero]
          exact add_le_add hd.badMass_left le_rfl
  · calc tvMargin (d₁.bind k₁) (d₀.bind k₀)
        ≤ tvMargin (d₁.bind k₁) ((truncBad b₁ d₁).bind fun a => truncBad b₂ (k₁ a))
            + tvMargin ((truncBad b₁ d₁).bind fun a => truncBad b₂ (k₁ a))
                (d₀.bind k₀) := tvMargin_triangle _ _ _
      _ ≤ (badMass b₁ d₁ + ε₂) + 0 := by
          refine add_le_add
            (tvMargin_bind_trunc_le d₁ k₁ fun a _ ha => (hk a ha).badMass_right) ?_
          rw [← hcomp]
          exact le_of_eq (tvMargin_eq_zero_of_le fun b => bind_trunc_le_some d₀ k₀ b)
      _ ≤ ε₁ + ε₂ := by
          rw [add_zero]
          exact add_le_add hd.badMass_right le_rfl

end CatCrypt.Prob

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

open scoped ENNReal

variable {α : Type*}

/-! ## The relational up-to-bad rule, re-derived through the factorization

`rHoareApprox_upto_bad` consumes the symmetrized inequality-form
`BadEvent.IdenticalUntilBad` pair and works analytically
(`tv_both_le_of_pointwise`). Here the rule is re-derived for the
exact-agreement (predicate) form of identical-until-bad, factoring through
`truncBad`-equality: the judgment is transport along the exact embedding of
the common truncation. The conclusion shape is identical, and the rule is
available at *any* result type, not just `Bool`. -/

/-- **Up-to-bad rule via truncation**: per-heap equality of bad-truncations,
    with the truncated mass bounded by `ε` on both sides, gives the grade-`ε`
    judgment with equality post. No `NoFail` hypothesis. -/
theorem rHoareApprox_upto_bad_trunc {G₀ G₁ : SPComp α}
    (bad : α × Heap → Prop) [DecidablePred bad] {ε : ℝ≥0∞}
    (htrunc : ∀ h, truncBad bad (G₀ h) = truncBad bad (G₁ h))
    (hbad₀ : ∀ h, badMass bad (G₀ h) ≤ ε)
    (hbad₁ : ∀ h, badMass bad (G₁ h) ≤ ε) :
    rHoareApprox ε eqPre G₀ G₁ eqPost := by
  intro h₁ h₂ heq
  have heq' : h₁ = h₂ := heq
  subst heq'
  refine liftRApprox_mono_rel (fun p₁ p₂ hp => ?_)
    (liftRApprox_eq_of_truncBad_eq (htrunc h₁) (hbad₀ h₁) (hbad₁ h₁))
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Up-to-bad rule via truncation, `NoFail` form: matching the hypothesis
    shape of `rHoareApprox_upto_bad`, the bad-mass bound is needed on one
    side only — mass balance (`badMass_eq_of_none_eq_zero`) transfers it. -/
theorem rHoareApprox_upto_bad_trunc_noFail {G₀ G₁ : SPComp α}
    (bad : α × Heap → Prop) [DecidablePred bad] {ε : ℝ≥0∞}
    (htrunc : ∀ h, truncBad bad (G₀ h) = truncBad bad (G₁ h))
    (hnf₀ : SPComp.NoFail G₀) (hnf₁ : SPComp.NoFail G₁)
    (hbad : ∀ h, badMass bad (G₀ h) ≤ ε) :
    rHoareApprox ε eqPre G₀ G₁ eqPost :=
  rHoareApprox_upto_bad_trunc bad htrunc hbad fun h =>
    badMass_eq_of_none_eq_zero (htrunc h) (hnf₀ h) (hnf₁ h) ▸ hbad h

/-- **Shoup's fundamental lemma through the factorization**: for games that
    agree exactly off the bad event, every adversary's advantage is bounded
    by the bad probability — `advantage_upto_bad`'s content, re-derived as
    factorization + transport + adequacy. -/
theorem advantageA_upto_bad_trunc {G₀ G₁ : SPComp α}
    (bad : α × Heap → Prop) [DecidablePred bad] {ε : ℝ≥0∞}
    (htrunc : ∀ h, truncBad bad (G₀ h) = truncBad bad (G₁ h))
    (hbad₀ : ∀ h, badMass bad (G₀ h) ≤ ε)
    (hbad₁ : ∀ h, badMass bad (G₁ h) ≤ ε)
    (A : α → SPComp Bool) :
    AdvantageA G₀ G₁ A ≤ ε :=
  rHoareApprox_advantageA (rHoareApprox_upto_bad_trunc bad htrunc hbad₀ hbad₁) A

/-! ## Bridge to the inequality-form `BadEvent.IdenticalUntilBad`

The Crypto-layer vocabulary states identical-until-bad as a pointwise
inequality against a bad *program* (`BadEvent.IdenticalUntilBad`). From the
predicate form, each direction is witnessed by the bad-flagging
instrumentation of the corresponding left game: `badProg bad G` runs `G` and
outputs whether its outcome was bad. Its acceptance probability is exactly
the bad mass (`prTrue_badProg`), so the grade vocabularies agree. -/

/-- The bad-flagging instrumentation of a game: run `G`, output whether the
    outcome (value and final heap) lies in the bad event. -/
noncomputable def badProg (bad : Bool × Heap → Prop) [DecidablePred bad]
    (G : SPComp Bool) : SPComp Bool :=
  fun h => (G h).bind fun p => SDistr.pure (if bad p then true else false, p.2)

theorem badProg_apply_true (bad : Bool × Heap → Prop) [DecidablePred bad]
    (G : SPComp Bool) (h h' : Heap) :
    badProg bad G h (some (true, h')) =
      ∑' p : Bool × Heap, if bad p ∧ p.2 = h' then G h (some p) else 0 := by
  classical
  rw [badProg, SDistr.bind_apply_some]
  refine tsum_congr fun p => ?_
  by_cases hb : bad p
  · by_cases hh : p.2 = h'
    · simp [hb, hh]
    · simp [hb, hh]
  · simp [hb]

/-- The instrumentation accepts with probability exactly the bad mass: the
    grade of the program-form vocabulary (`prTrue bad`) coincides with the
    grade of the truncation (`badMass`). -/
theorem prTrue_badProg (bad : Bool × Heap → Prop) [DecidablePred bad]
    (G : SPComp Bool) (h : Heap) :
    prTrue (badProg bad G) h = badMass bad (G h) := by
  classical
  calc prTrue (badProg bad G) h
      = ∑' h', ∑' p : Bool × Heap, if bad p ∧ p.2 = h' then G h (some p) else 0 :=
        tsum_congr fun h' => badProg_apply_true bad G h h'
    _ = ∑' p : Bool × Heap, ∑' h', if bad p ∧ p.2 = h' then G h (some p) else 0 :=
        ENNReal.tsum_comm
    _ = ∑' p : Bool × Heap, if bad p then G h (some p) else 0 := by
        refine tsum_congr fun p => ?_
        by_cases hb : bad p
        · rw [if_pos hb, tsum_eq_single p.2]
          · simp [hb]
          · intro h'' hne
            simp [hb, Ne.symm hne]
        · simp [hb]
    _ = badMass bad (G h) := rfl

/-- Identical-until-bad games (exact-agreement form) satisfy the
    inequality-form `BadEvent.IdenticalUntilBad`, witnessed by the
    bad-flagging instrumentation of the **left** game. The symmetric
    direction holds with `badProg bad G₁` (apply to `htrunc.symm`); a single
    shared witness for both directions would need to dominate both games'
    bad-conditioned mass pointwise per heap, which equal truncations do not
    provide — the direct rule `rHoareApprox_upto_bad_trunc` does not need
    one. -/
theorem identicalUntilBad_badProg {G₀ G₁ : SPComp Bool}
    (bad : Bool × Heap → Prop) [DecidablePred bad]
    (htrunc : ∀ h, truncBad bad (G₀ h) = truncBad bad (G₁ h)) :
    BadEvent.IdenticalUntilBad G₀ G₁ (badProg bad G₀) := by
  refine ⟨fun h b h' => ?_⟩
  by_cases hb : bad (b, h')
  · have hle : G₀ h (some (b, h')) ≤ badProg bad G₀ h (some (true, h')) := by
      rw [badProg_apply_true]
      refine le_trans ?_ (ENNReal.le_tsum (b, h'))
      simp [hb]
    exact le_add_left hle
  · have heq := ((eqUntilBad_iff_truncBad_eq bad (G₀ h) (G₁ h)).mpr (htrunc h))
      (b, h') hb
    rw [heq]
    exact le_self_add

end CatCrypt.Relational
