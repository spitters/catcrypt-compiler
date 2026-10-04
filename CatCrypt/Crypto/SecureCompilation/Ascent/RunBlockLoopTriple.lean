/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen
public import CatCrypt.Crypto.SecureCompilation.Ascent.SquareStrict

@[expose] public section
set_option autoImplicit false

/-!
# The counted-loop rule of the ascent on `Std.Do` triples

`Ascent/RunBlockCorres.lean` proves the block-replication combinator `corresJ_loop`
by induction on the count through `corresJ_append`. This module states the same
rule as an invariant rule over the `Std.Do` triples on `runBlockM`
(`Ascent/RunBlockMvcgen.lean`) and recovers `corresJ_loop` from it.

`runBlockM_loop_triple` fixes an abstract start state `a`. If, for every index
`i < n`, the body `body i` maps `SR · (loopStep step i a)` to
`SR · (loopStep step (i + 1) a)` as a triple, then the replicated block
`loopBlock body n` maps `SR · a` to `SR · (loopStep step n a)`. The induction on
`n` composes the per-index triples with `runBlockM_triple_hcomp`
(`Ascent/SquareStrict.lean`); the base case is the empty block.

`corresJ_loop_of_triple` has the hypotheses and the conclusion of `corresJ_loop`.
Its proof sends each per-index `CorresJ` leaf to a triple at the iterate
`loopStep step i a` (the invariant `P` holds there by `loopStep_preserves`), applies
`runBlockM_loop_triple`, and returns to `CorresJ` through `runBlockM_triple_iff`
and `corresJ_iff_triple`.

## Main results

* `runBlockM_loop_triple`: the invariant rule for `loopBlock` over `runBlockM`.
* `corresJ_loop_of_triple`: `corresJ_loop`, proved through the triple rule.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- **The counted-loop invariant rule on `Std.Do` triples.** For a fixed abstract
    start state `a`, if each body `body i` (`i < n`) maps `SR · (loopStep step i a)`
    to `SR · (loopStep step (i + 1) a)`, then the replicated block
    `loopBlock body n` maps `SR · a` to `SR · (loopStep step n a)`. -/
theorem runBlockM_loop_triple {AState : Type} (SR : JState 64 → AState → Prop)
    {step : Nat → AState → AState} {body : Nat → List (JInstr 64)} (a : AState) :
    ∀ n, (∀ i < n, ⦃fun s => ⌜SR s (loopStep step i a)⌝⦄ runBlockM (body i)
        ⦃⇓ _ s => ⌜SR s (loopStep step (i + 1) a)⌝⦄) →
      ⦃fun s => ⌜SR s a⌝⦄ runBlockM (loopBlock body n)
        ⦃⇓ _ s => ⌜SR s (loopStep step n a)⌝⦄
  | 0, _ => (runBlockM_triple_iff _ _ _).mpr fun st h => by
      simpa only [loopBlock, runBlock_nil, loopStep, id_eq] using h
  | k + 1, h =>
      runBlockM_triple_hcomp
        (runBlockM_loop_triple SR a k fun i hi => h i (Nat.lt_succ_of_lt hi))
        (h k (Nat.lt_succ_self k))

/-- **`corresJ_loop` through triples.** The hypotheses and conclusion of
    `corresJ_loop`: per-index leaves `hstep` and a step-invariant precondition `P`
    give `CorresJ SR P (loopStep step n) (loopBlock body n)`. The proof applies
    `runBlockM_loop_triple` at each abstract start state satisfying `P`. -/
theorem corresJ_loop_of_triple {AState : Type} (SR : JState 64 → AState → Prop)
    {P : AState → Prop} {step : Nat → AState → AState}
    {body : Nat → List (JInstr 64)}
    (hstep : ∀ i, CorresJ SR P (step i) (body i))
    (hinv : ∀ i a, P a → P (step i a)) (n : Nat) :
    CorresJ SR P (loopStep step n) (loopBlock body n) :=
  (corresJ_iff_triple SR P _ _).mpr fun a ha =>
    (runBlockM_triple_iff _ _ _).mp
      (runBlockM_loop_triple SR a n fun i _ =>
        (runBlockM_triple_iff _ _ _).mpr
          (corresJ_toTriple SR P (step i) (body i) (hstep i) (loopStep step i a)
            (loopStep_preserves hinv i a ha)))

end CatCrypt.Crypto.SecureCompilation.Ascent
