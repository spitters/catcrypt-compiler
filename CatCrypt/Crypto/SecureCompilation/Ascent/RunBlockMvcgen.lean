/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresHoare
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
import Std.Do.Triple
import Std.Tactic.Do

set_option autoImplicit false

/-!
# The ascent (`CorresJ` / `runBlock`) on the `Std.Do` WP metatheory

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

`Ascent/CorresHoare.lean` recast the ascent's forward simulation `CorresJ` as the
bespoke total Hoare triple

    RunBlockTriple P body Q := ∀ st, P st → Q (runBlock st body)

and proved `corresJ_iff_triple` — `CorresJ` **is** an `fa`-indexed family of these
triples. This module closes the remaining hop: it collapses that bespoke triple
into the standard **`Std.Do` weakest-precondition** triple `⦃P⦄ · ⦃Q⦄` that
`mvcgen` discharges — the very metatheory the upstream ascend runs on. Once an
ascent leaf is a `Std.Do` triple, `mvcgen` walks it natively.

## The construction

`runBlock` is modeled as the pure state monad `StateM (JState 64)`: each
instruction is `modify (evalInstr · i)`, the block is their `forM`
(`runBlockM`). `runBlockM_run` proves the monadic run returns exactly the
`runBlock` fold, so a `Std.Do` triple over `runBlockM` is a statement about the
real machine execution. The `PostShape` is `.arg (JState 64) .pure` — the pure
(no-throw) single-state shape `mvcgen`'s `modify`/`forM` `@[spec]` lemmas fire on
out of the box.

`runBlockM_triple_iff` is the bridge: the `Std.Do` triple over `runBlockM` is
*equivalent* to `RunBlockTriple`. Forward uses the `StateM` adequacy lemma
`StateM.of_wp_run_eq`; reverse composes the per-instruction `stepM_spec` over the
block (`runBlockM_spec`) and strengthens the precondition. Chaining
`corresJ_iff_triple → RunBlockTriple → runBlockM_triple_iff` sends any `CorresJ`
leaf to a `Std.Do` triple, and `mvcgen [stepM_spec]` discharges it — witnessed on
the subtract-with-borrow leaf `corresJ_sbb`.

## Relationship to the bignum interpreter (`Jasmin/BignumHoare.lean`)

`BignumHoare.BignumTriple` is the same *shape* of statement over a different
machine: `bignumExec : List InstrR → BignumState → Option BignumState` is
**partial** (it runs in `StateT BignumState Option`, not the total `StateM`), so
its `Std.Do` incarnation has the richer `PostShape` `.arg BignumState (.except
Unit .pure)` and needs a custom per-instruction `wp` lemma (the `StateT _ Option`
monad `mvcgen` does not auto-drive). The pure-`StateM` bridge here therefore does
not *literally* subsume `BignumTriple`; it is the total-machine instance of the
same recipe, and the bignum interpreter would become a second `Std.Do` mvcgen
instance built the same way over its Option monad rather than folded into this one.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. `runBlock` as a `Std.Do` state monad

Mirrors `X86Backend/LowCTMvcgen.lean`'s pure-`StateM` model, restated in the
ascent's namespace over its own dependency footprint (`JasminModel` + the ascent
`CorresHoare`). -/

/-- The per-instruction monadic step: update the machine state by `evalInstr · i`.
    The `do`-shaped atom `mvcgen` walks. -/
def stepM (i : JInstr 64) : StateM (JState 64) Unit :=
  modify (fun s => evalInstr s i)

/-- **The monadic block run.** `forM` of the per-instruction step over the block —
    the `do`-shaped form of `runBlock`. -/
def runBlockM (block : List (JInstr 64)) : StateM (JState 64) Unit :=
  block.forM stepM

@[simp] theorem runBlockM_nil : runBlockM [] = pure () := rfl

@[simp] theorem runBlockM_cons (i : JInstr 64) (is : List (JInstr 64)) :
    runBlockM (i :: is) = stepM i >>= fun _ => runBlockM is := by
  unfold runBlockM; simp

/-- **Faithfulness.** The monadic block run from `s` returns the same final state
    as the `runBlock` fold, so a triple about `runBlockM` is a statement about the
    real machine execution `runBlock`. -/
theorem runBlockM_run (block : List (JInstr 64)) (s : JState 64) :
    (runBlockM block).run s = ((), runBlock s block) := by
  induction block generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (stepM i >>= fun _ => runBlockM is).run s = _
    simp only [stepM, StateT.run_bind, StateT.run_modify, runBlock_cons, ih]
    rfl

/-! ## 2. The per-instruction `@[spec]` triple and the composed block spec -/

/-- The `PostShape` of `StateM (JState 64) = StateT (JState 64) Id`: a single state
    argument over the pure (no-throw) base. -/
abbrev psJM : PostShape := .arg (JState 64) .pure

/-- **The per-instruction step spec.** The Hoare triple for one step
    `modify (evalInstr · i)`: the precondition is the weakest precondition (the
    post evaluated at the `evalInstr`-updated state). `mvcgen`'s built-in `modify`
    spec discharges it directly (the `StateM` monad needs no custom `wp` lemma). -/
@[spec]
theorem stepM_spec (i : JInstr 64) (Q : PostCond Unit psJM) :
    Triple (stepM i) (fun s => Q.1 () (evalInstr s i)) Q := by
  unfold stepM Triple
  mvcgen

/-- **The composed block-run triple.** For any block and any state predicate `R`,
    running the block from a state where `R` holds at `runBlock s block` leaves a
    state where `R` holds. Proven by induction over the block, composing
    `stepM_spec` through `Triple.bind`. -/
theorem runBlockM_spec (block : List (JInstr 64)) (R : JState 64 → Prop) :
    Triple (runBlockM block)
      (fun s => ⌜R (runBlock s block)⌝)
      (⇓ _ => fun s => ⌜R s⌝) := by
  induction block with
  | nil =>
    simp only [runBlockM_nil, runBlock_nil]
    mvcgen
  | cons i is ih =>
    rw [runBlockM_cons]
    refine Triple.bind (stepM i) _
      (Q := fun _ => (fun s => ⌜R (runBlock s is)⌝ : Assertion psJM)) ?_ ?_
    · have := stepM_spec i (PostCond.noThrow fun _ s => ⌜R (runBlock s is)⌝)
      simpa [runBlock_cons] using this
    · intro _; exact ih

/-! ## 3. The bridge: the `Std.Do` triple IS `RunBlockTriple`

For the pure `StateM`, the weakest precondition of `runBlockM body` at post
`⌜Q ·⌝` is exactly `⌜Q (runBlock · body)⌝`, so the `Std.Do` Hoare triple over
`runBlockM` and the ascent's bespoke `RunBlockTriple` are the same statement. -/

/-- **The bridge.** The `Std.Do` weakest-precondition Hoare triple over `runBlockM`
    equals the ascent's bespoke `RunBlockTriple`. Forward is the `StateM` adequacy
    lemma `StateM.of_wp_run_eq` (evaluate the WP at a concrete state via
    `runBlockM_run`); reverse composes `runBlockM_spec` and strengthens the
    precondition through `Triple.conseq` + `SPred.pure_mono`. -/
theorem runBlockM_triple_iff (P Q : JState 64 → Prop) (body : List (JInstr 64)) :
    (⦃fun s => ⌜P s⌝⦄ runBlockM body ⦃⇓ _ s => ⌜Q s⌝⦄) ↔ RunBlockTriple P body Q := by
  constructor
  · -- forward: apply the WP at a concrete state via the `StateM` adequacy lemma.
    intro h st hP
    refine StateM.of_wp_run_eq (runBlockM_run body st) (fun p => Q p.2) ?_
    exact fun _ => h st hP
  · -- reverse: compose the block spec, strengthen the precondition.
    intro h
    exact Triple.entails_wp_of_pre (runBlockM_spec body Q)
      (SPred.entails_cons_intro (fun s => SPred.pure_mono (h s)))

/-! ## 4. An ascend leaf is `mvcgen`-native once on the `Std.Do` WP

The subtract-with-borrow leaf `corresJ_sbb` (the flag-carrying content the scalar
`Corres` could not phrase), transported to a `Std.Do` triple two ways: through the
`corresJ_iff_triple → RunBlockTriple → runBlockM_triple_iff` chain, and — the point
— by plain `mvcgen`. -/

/-- **The `sbb` ascend leaf as a `Std.Do` triple**, via the equivalence. The chain
    `corresJ_sbb` → `RunBlockTriple` (`sbb_as_triple`) → `runBlockM_triple_iff`
    lands the flag leaf on the standard WP triple with no `mvcgen` — the connection
    the ascent needed. -/
theorem sbb_leaf_triple (dst src : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄ runBlockM [.sbb dst (.reg src)]
      ⦃⇓ _ st => ⌜SRcarry st (sbbStep dst src a)⌝⦄ :=
  (runBlockM_triple_iff _ _ _).mpr (sbb_as_triple dst src a)

/-- **`mvcgen` discharges the `sbb` ascend leaf.** Plain `mvcgen` walks the
    one-instruction block, composing the per-instruction `stepM_spec`; the residual
    per-instruction VC is exactly the ascend leaf `corresJ_sbb` (the borrow-out bit
    equals the true-signed-difference-underflowed predicate). This demonstrates
    ascent leaves are `mvcgen`-native once expressed on the `Std.Do` WP. -/
theorem sbb_leaf_triple_mvcgen (dst src : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄ runBlockM [.sbb dst (.reg src)]
      ⦃⇓ _ st => ⌜SRcarry st (sbbStep dst src a)⌝⦄ := by
  simp only [runBlockM_cons, runBlockM_nil]
  mvcgen [stepM_spec]
  rename_i st hSR
  exact corresJ_sbb dst src st a hSR trivial

end CatCrypt.Crypto.SecureCompilation.Ascent
