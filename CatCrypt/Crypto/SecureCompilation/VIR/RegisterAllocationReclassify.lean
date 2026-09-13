/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Register allocation at the `Com` level and at the physical level

`RegisterAllocation.applyRA` is the identity on `JForProg`
(`RegisterAllocation.applyRA_denote_preserves_of_any`), and the `slotOf` of
`RegisterAllocation.linearScanRA` is `id` (`linearScanRA_slotOf_eq_id`). Every
theorem stated over `applyRA` therefore holds for every allocation and states no
property of it.

## Why the `Com`-level pass is the identity

`Com d Γ t` (`VIR/Core.lean`) is intrinsically typed SSA without registers:
variables are `Ctxt.Var Γ t` (de Bruijn indices). Physical registers and stack
slots exist only at the `Lprog`/`Lstate` level produced by `Com.toLprogPhysAbi`, so
a register assignment has no `Com → Com` action other than the identity.
`DeadCodeElimReal`, `CommonSubexprElimReal` and the other `*Real.lean` passes change
the binding structure, and their preservation theorems are not `rfl`.

## The physical allocator

The allocator used by `Com.toLprogPhysAbi` is `JasminLprogExport.physAssign`, a
linear scan over physical registers built on `physScanSpill`. Its semantic theorem
is at the `Lstate` level: `X86Backend.ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform`,
with the body core `X86Backend.ToLprogFaithfulNary.physBody_lsem_result_uniform`
(after the body runs, the physical register holding the result holds the value of
the abstract semantics).

`linearScanRA` stores its slot map in `seqOf`. The emit modules `Sha2RaEmit`,
`KeccakRaEmit` and `ChachaRaEmit` read `seqOf` to name slots in rendered text; no
theorem relates that rendered text to the unrenamed emit.

This module contains no declarations.
-/

@[expose] public section
