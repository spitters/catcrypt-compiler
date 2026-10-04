/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Solver

/-!
# Probe: `mvcgen` on a triple with a schematic abstract transition

The probe poses the goal `∃ f, ∀ a, ⦃⌜SRcarry · a⌝⦄ runBlockM c ⦃⇓ _ s => ⌜SRcarry s (f a)⌝⦄`
on the one-instruction block `[sbb dst src]` and on the two-instruction block
`[sbb d0 s0, sbb d1 s1]`, and records whether `mvcgen [stepM_spec]` determines `f`.

## Outcome

`mvcgen` does not synthesise `f`.

* Applied to the existential goal directly, `mvcgen` fails: the goal is not a triple,
  and the elaborator reports that `SPred.Tactic.PropAsSPredTautology` cannot be
  synthesised for it.
* After `refine ⟨?f, fun a => ?h⟩`, `mvcgen` walks the block and leaves one
  verification condition with `?f` unassigned:
  `SRcarry (evalInstr s (sbb dst src)) (?f a)` on one instruction and
  `SRcarry (evalInstr (evalInstr s (sbb d0 s0)) (sbb d1 s1)) (?f a)` on two.
* Closing that condition with the ascent leaf `corresJ_sbb` (once, or nested twice)
  assigns `?f` by higher-order pattern unification. The witnesses are
  `sbbStep dst src` and `fun a => sbbStep d1 s1 (sbbStep d0 s0 a)`
  (`sbb1Synth_val`, `sbb2Synth_val`), definitionally the transitions of
  `corresJ_sbb` and of the `corres_sym` proof `sbb2_refines` (`sbb2Synth_eq_sym`).
* `corres_sym` likewise does not accept an unassigned outer transition: on
  `CorresJ SRcarry (fun _ => True) ?f [sbb d0 s0, sbb d1 s1]` it reports that
  `corresJ_cons_true` does not apply. With the transition stated, it proves
  `sbb2_refines`.

The function is determined by the ascent leaves; `mvcgen` contributes the
decomposition of the block into the per-instruction condition.

## Main results

* `sbb1Synth`, `sbb1Synth_val`: the one-instruction witness and its value.
* `sbb2Synth`, `sbb2Synth_val`: the two-instruction witness and its value.
* `sbb2_refines`, `sbb2Synth_eq_sym`: the `corres_sym` proof on the same block and
  the definitional agreement of the two transitions.
-/

@[expose] public section

set_option autoImplicit false
set_option mvcgen.warning false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- `mvcgen` does not accept the existential goal itself. -/
example (dst src : String) : ∃ f : ACarry → ACarry, ∀ a,
    ⦃fun st => ⌜SRcarry st a⌝⦄ runBlockM [.sbb dst (.reg src)]
      ⦃⇓ _ st => ⌜SRcarry st (f a)⌝⦄ := by
  fail_if_success mvcgen [stepM_spec]
  exact ⟨sbbStep dst src, sbb_leaf_triple dst src⟩

/-- The one-instruction block with a schematic transition. `mvcgen` leaves the
    condition `SRcarry (evalInstr s (sbb dst src)) (?f a)` open; the leaf
    `corresJ_sbb` closes it and assigns `?f`. -/
def sbb1Synth (dst src : String) : { f : ACarry → ACarry // ∀ a,
    ⦃fun st => ⌜SRcarry st a⌝⦄ runBlockM [.sbb dst (.reg src)]
      ⦃⇓ _ st => ⌜SRcarry st (f a)⌝⦄ } := by
  refine ⟨?f, fun a => ?h⟩
  case h =>
    simp only [runBlockM_cons, runBlockM_nil]
    mvcgen [stepM_spec]
    fail_if_success done
    rename_i st hSR
    exact corresJ_sbb dst src st a hSR trivial

/-- The one-instruction witness is the `corresJ_sbb` transition. -/
theorem sbb1Synth_val (dst src : String) : (sbb1Synth dst src).val = sbbStep dst src :=
  rfl

/-- The two-instruction block with a schematic transition. `mvcgen` leaves the
    condition `SRcarry (evalInstr (evalInstr s (sbb d0 s0)) (sbb d1 s1)) (?f a)`
    open; two nested `corresJ_sbb` leaves close it and assign `?f`. -/
def sbb2Synth (d0 s0 d1 s1 : String) : { f : ACarry → ACarry // ∀ a,
    ⦃fun st => ⌜SRcarry st a⌝⦄ runBlockM [.sbb d0 (.reg s0), .sbb d1 (.reg s1)]
      ⦃⇓ _ st => ⌜SRcarry st (f a)⌝⦄ } := by
  refine ⟨?f, fun a => ?h⟩
  case h =>
    simp only [runBlockM_cons, runBlockM_nil]
    mvcgen [stepM_spec]
    fail_if_success done
    rename_i st hSR
    exact corresJ_sbb d1 s1 _ _ (corresJ_sbb d0 s0 st a hSR trivial) trivial

/-- The two-instruction witness is the composite of the two `sbbStep` transitions. -/
theorem sbb2Synth_val (d0 s0 d1 s1 : String) :
    (sbb2Synth d0 s0 d1 s1).val = fun a => sbbStep d1 s1 (sbbStep d0 s0 a) :=
  rfl

/-- The two-instruction subtract-with-borrow block refines the composite `sbbStep`
    transition, by `corres_sym`. -/
theorem sbb2_refines (d0 s0 d1 s1 : String) :
    CorresJ SRcarry (fun _ => True) (fun a => sbbStep d1 s1 (sbbStep d0 s0 a))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1)] := by
  corres_sym

/-- `corres_sym` does not accept an unassigned transition; `sbb2_refines`, with the
    transition stated, assigns it. -/
example (d0 s0 d1 s1 : String) : ∃ f : ACarry → ACarry,
    CorresJ SRcarry (fun _ => True) f [.sbb d0 (.reg s0), .sbb d1 (.reg s1)] := by
  refine ⟨?f, ?h⟩
  case h =>
    fail_if_success corres_sym
    exact sbb2_refines d0 s0 d1 s1

/-- The witness assigned in `sbb2Synth` is the transition `corres_sym` proves in
    `sbb2_refines`, and `sbb2_refines` holds at it. -/
theorem sbb2Synth_eq_sym (d0 s0 d1 s1 : String) :
    CorresJ SRcarry (fun _ => True) (sbb2Synth d0 s0 d1 s1).val
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1)] :=
  sbb2_refines d0 s0 d1 s1

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
