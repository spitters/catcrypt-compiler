/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Register allocation: reclassification (audit Class A)

The compiler-proof-cheats audit flagged `RegisterAllocation.applyRA = fun p _ => p`
(identity, `rfl` preservation) alongside DCE/CSE/LICM/StrengthReduce/Schedule as a
"vacuous optimizer pass". On investigation, **RA is different from those five and is
NOT a `Com → Com` cheat** — it should not get a `*Real.lean` real-transform sibling.

## Why RA is honestly the Com-level identity

`Com d Γ t` (`VIR/Core.lean`) is intrinsically-typed, register-FREE SSA: variables are
`Ctxt.Var Γ t` (de Bruijn indices), not physical registers. Register allocation assigns
SSA values to physical registers / stack slots, which exist only at the `Lprog`/`Lstate`
level produced by `Com.toLprogPhysAbi`. An RA decision therefore *cannot* rewrite the
`Com`; the only honest `Com → Com` action is the identity. Contrast `DeadCodeElimReal`,
`CommonSubexprElimReal`, etc., which change the binding/context structure (so their
preservation theorems are genuinely non-`rfl`). RA has no such Com-level analogue.

## Where the real RA + its correctness live

The real allocator is `JasminLprogExport.physAssign` (a Poletto–Sarkar linear scan over
PHYSICAL registers), used by `Com.toLprogPhysAbi`. Its correctness is a **physical-level**
(`Lstate`) statement, NOT a `Com → Com` equation, of the form

  `physExec (toLprogPhysAbi com (physAssign …)) = Com.denote com`

and the discharged structural core already exists as
`X86Backend.ToLprogFaithfulNary.physBody_lsem_result_uniform` (after the body runs, the
VM register holding the result holds the abstract-semantics value).

So RA's real correctness obligation is **Phase 1** (the `toLprogPhysAbi` physical-machine
proof), and the body-register-scan part of it is proved. `RegisterAllocation.linearScanRA`'s
own `slotOf := id` slot decision is orphan metadata at the `Com` level — no consumer reads
its `seqOf`; the live allocation is `physAssign`.

The audit's Class-A list therefore over-counts RA: the honest count is **5 vacuous
`Com`-level passes** (DCE/CSE/LICM/StrengthReduce/Schedule — all now fixed with real
`*Real.lean` transforms) plus RA, which is correctly the `Com`-identity with its real
correctness living in (and partly proved within) Phase 1.

(This module is documentation only — the machine-checked claims `applyRA = id` /
`linearScanRA.slotOf = id` are trivial `rfl`s over `RegisterAllocation`'s own defs; the
load-bearing fact is the Phase-1 physical theorem `physBody_lsem_result_uniform`.)
-/
