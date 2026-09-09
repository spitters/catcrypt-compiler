/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare
import CatCrypt.Crypto.Jasmin.BignumHoare.ModP25519Final

/-!
# `mvcgen'` smoke test — Phase 1 (notation port) ✅ + Phase 2-5 skeleton

Phase 1 of the
migration is implemented in this file (notation port from
`BignumTriple` to upstream `⦃P⦄ body ⦃Q⦄`); Phases 2-5 remain
documented as shape contracts pending upstream `mvcgen'`
promotion out of `tests/bench/`.

## Status

The upstream `mvcgen'` tactic lives at
`leanprover/lean4:tests/bench/mvcgen/sym/lib/VCGen.lean` and is
not yet importable from CatCrypt (it's in `tests/bench/`, not a
production module).

**Phase 1 deliverable (this file)**: definitionally bridge
`BignumTriple` (the partial-correctness state-relation form used
across the bignum tree) with the upstream `Triple` /
`⦃P⦄ body ⦃Q⦄` notation. The bridge uses the *partial-correctness*
form `⇓?` (`PostCond.mayThrow`) since `BignumTriple` does not
require successful termination.

**What's blocked on upstream**:

* `mvcgen'` tactic invocation.
* `WPMonad` instance dispatch via the upstream typeclass.
* `@[spec]` attribute registration for chain-step axioms.

## What this file ships

* `BignumTripleM P body Q` — Triple-form alias of `BignumTriple`,
  in upstream `⦃P⦄ body ⦃Q⦄` notation, partial-correctness form.
* `bignumTripleM_iff_bignumTriple` — both-directions bridge lemma
  derived from `bignumExecM_iff_bignumExec` (in `BignumExec.lean`).
* `bignum_mod_p25519_4_correct_triple` — Phase 1 smoke-test target:
  the existing `bignum_mod_p25519_4_correct_universal` re-stated in
  upstream Triple notation, proved by `iff.mpr` of the bridge.

These lemmas are the bridge infrastructure that lets
existing `BignumTriple`-shape proofs be re-used with upstream
mvcgen' once it lands.

## Migration timeline

When `mvcgen'` is promoted out of `tests/bench/`:

1. Add `import Lean.Meta.Sym` etc. to this file.
2. Replace the Phase 1 Triple lemmas with native `mvcgen'`
   invocations.
3. Annotate the chain-step contracts (`MontmulAxiom.lean`,
   `ChainStepAxioms.lean`) with `@[spec]`.
4. Re-prove `bignum_mod_p25519_4_correct` via single
   `mvcgen'` call.
5. Measure the LoC delta and decide on the broader migration.

Until then, this file ships the bridging lemmas as the
preparatory groundwork.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.MVCGenPrimeSmoke

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open Std.Do

/-! ## §1  Phase 1 — notation port (✅ landed)

Bridges `BignumTriple` (partial-correctness state-relation form
used across the bignum tree) with the upstream `Std.Do.Triple` /
`⦃P⦄ body ⦃Q⦄` notation. The bridge uses `⇓?` (`PostCond.mayThrow`)
because `BignumTriple` is partial-correctness — it does not
require successful termination.

```
BignumTriple P body Q  :=  ∀ s s', P s → bignumExec body s = some s' → Q s'

BignumTripleM P body Q :=  ⦃fun s => ⌜P s⌝⦄
                             bignumExecM emptyRegistry body
                           ⦃⇓? _ => fun s => ⌜Q s⌝⦄
```

The two are equivalent via the `bignumExecM_iff_bignumExec`
bridge in `BignumExec.lean`. -/

/-- Triple-form alias of `BignumTriple`, in upstream
    `⦃P⦄ body ⦃Q⦄` notation. Partial-correctness form via
    `⇓?` (`PostCond.mayThrow`). -/
def BignumTripleM (P : BignumState → Prop) (body : List InstrR)
    (Q : BignumState → Prop) : Prop :=
  Triple (bignumExecM emptyRegistry body)
         (fun s => ⌜P s⌝)
         (⇓? _ => fun s => ⌜Q s⌝)

/-- Forward bridge: a `BignumTripleM` lifts back to the
    state-relation form. Successful runs of `bignumExec` satisfy
    the postcondition. -/
theorem bignumTripleM_to_relation
    {P Q : BignumState → Prop} {body : List InstrR}
    (h : BignumTripleM P body Q) :
    ∀ s s', P s → bignumExec body s = some s' → Q s' := by
  intro s s' hP hExec
  simp only [BignumTripleM, Triple, Std.Do.WP.wp,
             Std.Do.PredTrans.apply_pushArg, Std.Do.PredTrans.apply_pushOption,
             Std.Do.PredTrans.apply_Pure_pure, PostCond.mayThrow,
             Id.run, OptionT.run, Option.instWP._aux_1, StateT.run] at h
  have hRun : bignumExecM emptyRegistry body s = some ((), s') :=
    (bignumExecM_iff_bignumExec body s s').mpr hExec
  have h' := h s hP
  dsimp only at h'
  rw [hRun] at h'
  exact h'

/-- Reverse bridge: a `BignumTriple` lifts to a `BignumTripleM`. -/
theorem bignumTripleM_of_relation
    {P Q : BignumState → Prop} {body : List InstrR}
    (h : ∀ s s', P s → bignumExec body s = some s' → Q s') :
    BignumTripleM P body Q := by
  simp only [BignumTripleM, Triple, Std.Do.WP.wp,
             Std.Do.PredTrans.apply_pushArg, Std.Do.PredTrans.apply_pushOption,
             Std.Do.PredTrans.apply_Pure_pure, PostCond.mayThrow,
             Id.run, OptionT.run, Option.instWP._aux_1, StateT.run]
  intro s hP
  dsimp only
  split
  · rename_i a hRun
    obtain ⟨_, s'⟩ := a
    have hExec := (bignumExecM_iff_bignumExec body s s').mp hRun
    exact h s s' hP hExec
  · simp [ExceptConds.true, ExceptConds.const]

/-- Phase 1 bridge: `BignumTriple` ↔ `BignumTripleM`. The two
    shapes are interconvertible. -/
theorem bignumTripleM_iff_bignumTriple
    (P : BignumState → Prop) (body : List InstrR) (Q : BignumState → Prop) :
    BignumTripleM P body Q ↔ BignumTriple P body Q := by
  constructor
  · intro h
    intro s s' hP hStep
    exact bignumTripleM_to_relation h s s' hP hStep
  · intro h
    exact bignumTripleM_of_relation h

/-! ## §2  WPMonad instance shape (Phase 2 target)

The upstream `mvcgen'` requires a `WPMonad` instance for the
target monad.  For `bignumExecM` (which is essentially
`StateT BignumState Option Unit`), the instance has the shape:

```
instance : WPMonad BignumM where
  wp prog post := fun s =>
    match prog s with
    | none => False  -- partial correctness: failure is fine
    | some (a, s') => post a s'
```

This is essentially what `BignumTriple` already encodes, just
rephrased from "∀ s s', P s → bignumStep body s s' → Q s'" to
"∀ s, P s → wp body Q s".

Building this instance is Phase 2 of the migration.  Once
landed, `mvcgen'` will work on `bignumExecM` bodies natively.

This file provides the **shape contract** for the WPMonad
instance.  The actual implementation lands when the migration
phase begins. -/

/-! ## §3  Phase 1 smoke test — `bignum_mod_p25519_4` (✅ landed)

Re-states the existing universal correctness theorem
`CatCrypt.Crypto.Jasmin.BignumHoare.bignum_mod_p25519_4_correct_universal`
(in `BignumHoare.lean`) using the upstream `⦃P⦄ body ⦃Q⦄`
notation, by transporting through `bignumTripleM_iff_bignumTriple`.

This validates that **the notation port is real**: the existing
proof's content is preserved, only the surface syntax changes.
When upstream `mvcgen'` lands, this is the same theorem statement
that a single `mvcgen' [...]` invocation should target (Phase 4
deliverable in the migration plan).

Phase 4/5 target (blocked on upstream):

```
theorem bignum_mod_p25519_4_correct' (base_a base_op : UInt64) (h_disj : ...) :
    ⦃bignumModPre base_a base_op⦄
      bignumExecM registry BignumModP25519.body
    ⦃⇓ _ => bignumModPost base_a base_op⦄ := by
  mvcgen' [BignumModP25519.body]  -- spec dispatch via @[spec]
```

If that lands at < 30 LoC (vs the current ~200 LoC chunked
recipe), the migration is validated. -/

/-- Phase 1 smoke test: `bignum_mod_p25519_4_correct_universal`
re-stated in upstream Triple notation via the partial-correctness
bridge.

Proved by `bignumTripleM_of_relation` applied to the existing
state-relation universal — no new proof content. The migration
to `mvcgen'` (Phase 4) would replace the body with a single
`mvcgen' [...]` call. -/
theorem bignum_mod_p25519_4_correct_triple
    (base_a base_op : UInt64)
    (h_disj : MemoryModel.Disjoint
                (MemoryModel.range base_a 32)
                (MemoryModel.range base_op 32)) :
    BignumTripleM
      (CatCrypt.Crypto.Jasmin.BignumHoare.bignumModPre base_a base_op)
      S2NBignumSSA.BignumModP25519_4.body
      (CatCrypt.Crypto.Jasmin.BignumHoare.bignumModPost base_a base_op) := by
  apply bignumTripleM_of_relation
  exact CatCrypt.Crypto.Jasmin.BignumHoare.bignum_mod_p25519_4_correct_universal
          base_a base_op h_disj

/-! ## §4  Spec annotations target

Once `mvcgen'` is in place, the chain-step contracts become spec-
annotated for automatic dispatch (`MontmulCallFacts.call_correct` is
the hypothesis-structure field the chain theorems consume):

```
@[spec]
theorem chain_sqr_step_correct ...

@[spec]
theorem chain_mul_step_correct ...

@[spec]
theorem chain_repeated_sqr_then_mul_correct_generic ...
```

The 13 per-block instances in `PerBlockInstances.lean` then
discharge automatically: `mvcgen'` walks the chain, encounters
each block's pattern, dispatches the appropriate `chain_*_correct`
theorem from the spec database, glues via the WPMonad bind law.

Result: 13 individual ~5-LoC theorems collapse to one
`mvcgen'` call covering the full chain.

Total LoC delta target: -300 LoC across `PerBlockInstances.lean`,
`PowP58LayerB.lean`, `BignumHoare.lean` chunked recipes. -/

/-! ## §5  Summary

Phase 1 of the `mvcgen → mvcgen'` migration is **complete in
this file**: `BignumTripleM` plus the `bignumTripleM_iff_bignumTriple`
bridge lemma plus the smoke-test theorem
`bignum_mod_p25519_4_correct_triple` validate that the upstream
`Std.Do.Triple` notation is a drop-in for the existing
`BignumTriple` formalism (modulo partial-correctness via `⇓?`).

Phases 2-5 remain documented as shape contracts pending
upstream `mvcgen'` promotion out of `tests/bench/`:

1. ✅ Phase 1 (this file): Triple-form alias + iff bridge.
2. Phase 2 (blocked): `instance : WPMonad BignumM`.
3. Phase 3 (blocked): `@[spec]` annotations on chain-step axioms.
4. Phase 4 (blocked): rewrite per-block instances via `mvcgen'`.
5. Phase 5 (blocked): discharge full chain via single `mvcgen'`.

Phases 2-5 require importing `mvcgen'` from
`tests/bench/mvcgen/sym/lib/VCGen.lean`, which is not stable
upstream API. Total remaining effort: ~4 sessions once upstream
promotes `mvcgen'`. -/

end CatCrypt.Crypto.Jasmin.BignumHoare.MVCGenPrimeSmoke
