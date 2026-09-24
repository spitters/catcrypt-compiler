/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Cross-block residency unroll: reclassification (audit Class A)

`CrossBlockResidencyUnroll.applyCrossBlockResidency = fun p _ => p` is the
identity, with `rfl` preservation. **Cross-block residency is the same kind of
pass as `RegisterAllocation` — a PHYSICAL-level decision — and is the
`Com`-level identity.** It has no `*Real.lean` `Com → Com` transform sibling.

## Why cross-block residency is the `Com`-level identity

`Com d Γ t` (`VIR/Core.lean`) is intrinsically-typed, register-FREE SSA:
variables are `Ctxt.Var Γ t` (de Bruijn indices), not physical registers or
stack slots. Cross-block residency decides which *logical slots* should be
**pinned to a physical register across an iteration boundary** (rather than
spilled and reloaded at each loop-head / loop-tail). Its decision record
(`CrossBlockResidencyDecisions`) is precisely a register-residency labelling:

* `carriedSlots`  — slots whose physical register can be **reused** across the
  boundary (written in iter `i`, read in iter `i+1`);
* `prologuePins`  — slots to **pin to a physical register** ONCE before the
  loop, instead of at each iteration head;
* `epilogueUnpins`— slots to **unpin / commit** ONCE after the loop;
* `fullCarry`     — whether the per-iteration pin/unpin sequence is hoistable
  in bulk.

Pins, spills, reloads, and "which physical register holds slot `s` across the
boundary" exist only at the `Lprog`/`Lstate` level produced by
`Com.toLprogPhysAbi`. A residency decision therefore *cannot* rewrite the
`Com`; the only `Com → Com` action it determines is the identity. Contrast
`DeadCodeElimReal` / `CommonSubexprElimReal` / `ScheduleReal` /
`SoftwarePipeliningReal`, which change the binding / context / loop structure
(so their preservation theorems are non-`rfl`). Cross-block residency
has no such `Com`-level analogue: the loop body, its bindings, and its trip
count are all unchanged — only the storage-class of each value across the
boundary changes, and storage class is invisible to `Com`.

## The pass routes through the RA framework

`CrossBlockResidencyUnroll.lean` packages its decision as a
`RegisterAllocation` (`crossBlockResidencyRA`, with `slotOf := id`,
`seqOf := id`) and discharges its `Com`-level preservation through the RA
framework's `applyRA_denote_preserves` (`crossBlockResidency_via_RA`). So this
pass lives at the same layer as RA: its
real content is a physical-register-allocation refinement (boundary-stable
residency), consumed by the per-protocol `*RaEmit.lean` lowering, not a
`Com` rewrite.

## Where the real cross-block residency + its correctness live

The residency decision is realised by the **physical** emit pass: the
per-protocol `*RaEmit.lean` (e.g. `ChachaRaEmit`, `Poseidon2RaEmit`,
`Sha2Emit`) chooses physical names for the carried slots and emits the lifted
prologue-pin / steady-body / epilogue-unpin sequence. Its correctness is a
**physical-level** (`Lstate`) statement, NOT a `Com → Com` equation, of the
form

  `physExec (toLprogPhysAbi com (physAssign … with boundary-stable residency))
     = Com.denote com`

— the same `toLprogPhysAbi` physical-machine obligation that
`RegisterAllocationReclassify.lean` identifies for ordinary RA, whose
discharged structural core is
`X86Backend.ToLprogFaithfulNary.physBody_lsem_result_uniform` (after the body
runs, the VM register holding the result holds the abstract-semantics value).

The specific extra fact cross-block residency needs over plain RA is that an
**epilogue-unpin immediately followed by a prologue-re-pin at the iteration
boundary is the identity data-move** (`move reg → stack → reg`), so eliding the
matched pair preserves both the computed values and the constant-time profile
(the elided moves target constant register/stack addresses — e.g. ChaCha20's
`m14s`/`m15s` spill cells — so no secret-dependent path is added or removed).
That is a physical-machine (`Lstate`) move-cancellation lemma at the
`toLprogPhysAbi` layer, NOT a `Com` equation — which is exactly why
`applyCrossBlockResidency` is correctly the `Com`-identity.

## Classification of the optimizer passes

* **`Com`-level passes, each with a `*Real.lean` transform:** DCE (`DeadCodeElimReal`), CSE
  (`CommonSubexprElimReal`), LICM (`LoopInvariantHoistReal`), StrengthReduce,
  Schedule (`InstructionScheduleReal`), and SoftwarePipelining
  (`SoftwarePipeliningReal`, the prologue-peel loop transform).
* **Physical-level passes, the `Com`-identity, correctness at the
  `toLprogPhysAbi` layer:** `RegisterAllocation` (see
  `RegisterAllocationReclassify.lean`) and **`CrossBlockResidencyUnroll`**
  (this file) — both register-residency decisions.

(This module is documentation only — the machine-checked claims
`applyCrossBlockResidency = id` / `crossBlockResidencyRA.slotOf = id` are
trivial `rfl`s over `CrossBlockResidencyUnroll`'s own defs; the substantive
fact is the physical theorem `physBody_lsem_result_uniform` plus the
boundary move-cancellation lemma at the `toLprogPhysAbi` layer.)
-/

@[expose] public section
