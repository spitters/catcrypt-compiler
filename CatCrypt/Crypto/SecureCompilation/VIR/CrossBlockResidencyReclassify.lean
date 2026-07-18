/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Cross-block residency unroll: reclassification (audit Class A)

The compiler-proof-cheats audit flagged
`CrossBlockResidencyUnroll.applyCrossBlockResidency = fun p _ => p` (identity,
`rfl` preservation) alongside DCE/CSE/LICM/StrengthReduce/Schedule/SoftwarePipelining
as a "vacuous optimizer pass". On investigation, **cross-block residency is the
same kind of pass as `RegisterAllocation` — a PHYSICAL-level decision — and is
honestly the `Com`-level identity.** It should NOT get a `*Real.lean`
`Com → Com` real-transform sibling.

## Why cross-block residency is honestly the `Com`-level identity

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
`Com`; the only honest `Com → Com` action is the identity. Contrast
`DeadCodeElimReal` / `CommonSubexprElimReal` / `ScheduleReal` /
`SoftwarePipeliningReal`, which change the binding / context / loop structure
(so their preservation theorems are genuinely non-`rfl`). Cross-block residency
has no such `Com`-level analogue: the loop body, its bindings, and its trip
count are all unchanged — only the storage-class of each value across the
boundary changes, and storage class is invisible to `Com`.

## The file already witnesses this: it routes through the RA framework

`CrossBlockResidencyUnroll.lean` itself packages its decision as a
`RegisterAllocation` (`crossBlockResidencyRA`, with `slotOf := id`,
`seqOf := id`) and discharges its `Com`-level preservation through the RA
framework's `applyRA_denote_preserves` (`crossBlockResidency_via_RA`). That is
the structural admission that this pass lives at the same layer as RA: its
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

— the same `Phase 1` (`toLprogPhysAbi` physical-machine) obligation that
`RegisterAllocationReclassify.lean` identifies for ordinary RA, whose
discharged structural core already exists as
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

## Audit accounting

The audit's Class-A list therefore over-counts cross-block residency, the same
way it over-counted RA. The honest accounting:

* **Genuinely vacuous `Com`-level passes, now each fixed with a real
  `*Real.lean` transform:** DCE (`DeadCodeElimReal`), CSE
  (`CommonSubexprElimReal`), LICM (`LoopInvariantHoistReal`), StrengthReduce,
  Schedule (`InstructionScheduleReal`), and SoftwarePipelining
  (`SoftwarePipeliningReal`, the prologue-peel loop transform).
* **Physical-level passes, correctly the `Com`-identity, real correctness in
  Phase 1:** `RegisterAllocation` (see `RegisterAllocationReclassify.lean`) and
  **`CrossBlockResidencyUnroll`** (this file) — both register-residency
  decisions, both reclassified.

(This module is documentation only — the machine-checked claims
`applyCrossBlockResidency = id` / `crossBlockResidencyRA.slotOf = id` are
trivial `rfl`s over `CrossBlockResidencyUnroll`'s own defs; the load-bearing
fact is the Phase-1 physical theorem `physBody_lsem_result_uniform` plus the
boundary move-cancellation lemma at the `toLprogPhysAbi` layer.)
-/
