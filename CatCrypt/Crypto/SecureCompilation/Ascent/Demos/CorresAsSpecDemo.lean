/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresHoareSpec
public import CatCrypt.Crypto.SecureCompilation.Ascent.SquareStrict

/-!
# Demo: an ascent result used as a callee specification under `mvcgen`

The callee is the subtract-with-borrow leaf `[.sbb dst (.reg src)]`, whose
correspondence `corresJ_sbb` is proved in `Ascent/RunBlockCorres.lean` from the
instruction semantics. `sbb_leaf_spec_at` and `sbb_leaf_spec` are the two `Std.Do`
specifications of that leaf obtained from `corresJ_sbb` through `corresJ_spec_at`
and `corresJ_spec`; neither proof evaluates the instruction.

The caller is the concatenation of two such blocks. `runBlockM_append` turns the
concatenation into a bind, and `mvcgen` applies a leaf specification at each block
it is given one for.

## Main results

* `sbb_then_sbb_triple` — both blocks are discharged by `sbb_leaf_spec_at`;
  `mvcgen` leaves no verification condition.
* `sbb_then_step_triple` — the first block is discharged by `sbb_leaf_spec_at` and
  the second is walked instruction by instruction with `stepM_spec`; the remaining
  verification condition is `corresJ_sbb d1 s1` at the intermediate state.
* `step_then_sbb_triple` — the first block is walked with `stepM_spec` and the
  second, in tail position, is discharged by the arbitrary-postcondition form
  `sbb_leaf_spec`.
-/

@[expose] public section

set_option autoImplicit false
set_option mvcgen.warning false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent

/-- The subtract-with-borrow leaf as a `Std.Do` triple at the abstract state `a`,
    derived from `corresJ_sbb` by `corresJ_spec_at`. -/
theorem sbb_leaf_spec_at (dst src : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄ runBlockM [.sbb dst (.reg src)]
      ⦃⇓ _ st => ⌜SRcarry st (sbbStep dst src a)⌝⦄ :=
  corresJ_spec_at (corresJ_sbb dst src) a trivial

/-- The subtract-with-borrow leaf as a `Std.Do` triple for an arbitrary
    postcondition, derived from `corresJ_sbb` by `corresJ_spec`. -/
theorem sbb_leaf_spec (dst src : String) (Q : PostCond Unit psJM) :
    ⦃fun st => ⌜∃ a, SRcarry st a ∧ True ∧
        ∀ st', SRcarry st' (sbbStep dst src a) → (Q.1 () st').down⌝⦄
      runBlockM [.sbb dst (.reg src)] ⦃Q⦄ :=
  corresJ_spec (corresJ_sbb dst src) Q

/-- Two subtract-with-borrow leaves in sequence, each used through
    `sbb_leaf_spec_at`. -/
theorem sbb_then_sbb_triple (d0 s0 d1 s1 : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄
      runBlockM ([.sbb d0 (.reg s0)] ++ [.sbb d1 (.reg s1)])
    ⦃⇓ _ st => ⌜SRcarry st (sbbStep d1 s1 (sbbStep d0 s0 a))⌝⦄ := by
  rw [runBlockM_append]
  mvcgen [sbb_leaf_spec_at]

/-- The first leaf used through `sbb_leaf_spec_at`, followed by one instruction
    walked by `stepM_spec`. -/
theorem sbb_then_step_triple (d0 s0 d1 s1 : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄
      runBlockM ([.sbb d0 (.reg s0)] ++ [.sbb d1 (.reg s1)])
    ⦃⇓ _ st => ⌜SRcarry st (sbbStep d1 s1 (sbbStep d0 s0 a))⌝⦄ := by
  rw [runBlockM_append, runBlockM_cons (.sbb d1 (.reg s1)) [], runBlockM_nil]
  mvcgen [sbb_leaf_spec_at, stepM_spec]
  rename_i st' hSR'
  exact corresJ_sbb d1 s1 st' _ hSR' trivial

/-- One instruction walked by `stepM_spec`, followed by the leaf in tail position
    used through the arbitrary-postcondition form `sbb_leaf_spec`. -/
theorem step_then_sbb_triple (d0 s0 d1 s1 : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄
      runBlockM ([.sbb d0 (.reg s0)] ++ [.sbb d1 (.reg s1)])
    ⦃⇓ _ st => ⌜SRcarry st (sbbStep d1 s1 (sbbStep d0 s0 a))⌝⦄ := by
  rw [runBlockM_append, runBlockM_cons (.sbb d0 (.reg s0)) [], runBlockM_nil]
  mvcgen [sbb_leaf_spec, stepM_spec]
  rename_i st hSR
  exact ⟨_, corresJ_sbb d0 s0 st a hSR trivial, trivial, fun _ h => h⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
