/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Cross-block residency: classification as a physical-level pass

This module contains no declarations. It records where the correctness of
cross-block residency (`CrossBlockResidencyUnroll`) is stated.

## Main results

None. The relevant theorems are in other modules:

* `X86Backend.ToLprogFaithfulNary.physBody_lsem_result_uniform` — after the
  body runs, the VM register holding the result holds the abstract-semantics
  value;
* `X86Backend.ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform` — the
  physical lowering `toLprogPhysAbi` is faithful to `Com.denote`.

## Why residency is not a `Com` rewrite

`Com d Γ t` (`VIR/Core.lean`) is intrinsically typed, register-free SSA:
variables are `Ctxt.Var Γ t` (de Bruijn indices), not physical registers or
stack slots. Cross-block residency decides which logical slots stay pinned to
a physical register across an iteration boundary instead of being spilled and
reloaded at each loop head and tail. Its decision record
(`CrossBlockResidencyDecisions`) is a register-residency labelling:

* `carriedSlots` — slots whose physical register is reused across the
  boundary (written in iteration `i`, read in iteration `i+1`);
* `prologuePins` — slots pinned to a physical register once before the loop;
* `epilogueUnpins` — slots unpinned once after the loop;
* `fullCarry` — whether the per-iteration pin/unpin sequence is hoistable in
  bulk.

Pins, spills, reloads and the register holding a slot across the boundary
exist only at the `Lprog`/`Lstate` level produced by `Com.toLprogPhysAbi`; the
loop body, its bindings and its trip count are unchanged. The correctness of
a lowering that uses the decision is therefore a physical-level statement of
the form

  `physExec (toLprogPhysAbi com (physAssign … with boundary-stable residency))
     = Com.denote com`,

the same obligation `RegisterAllocationReclassify.lean` identifies for
ordinary register allocation. Beyond plain register allocation it needs a
move-cancellation lemma at the `toLprogPhysAbi` layer: an epilogue unpin
immediately followed by a prologue re-pin at the iteration boundary is the
identity data move (`move reg → stack → reg`), so eliding the matched pair
preserves the computed values and, since the moves target constant
register and stack addresses, the constant-time profile.

## Classification of the optimizer passes

* `Com`-level transforms with a denotation theorem: DCE (`DeadCodeElimReal`),
  CSE (`CommonSubexprElimReal`), LICM (`LoopInvariantHoistReal`), strength
  reduction (`StrengthReduceReal`), scheduling (`InstructionScheduleReal`) and
  software pipelining (`SoftwarePipeliningReal`).
* Physical-level decisions, whose correctness is stated at the
  `toLprogPhysAbi` layer: `RegisterAllocation` (see
  `RegisterAllocationReclassify.lean`) and `CrossBlockResidencyUnroll`.
-/

@[expose] public section
