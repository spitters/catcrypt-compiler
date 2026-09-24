/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.RegMachineToSim


@[expose] public section
set_option autoImplicit false

/-!
# The unified register allocator (`MachineTarget` capstone)

The generic register-allocation pass is proved ONCE and inherited by every ISA,
through two interfaces and one bridge:

* **resident path** — `RegMachineSim I S` (the simulation-relation machine). The
  theorem `renameBlock_runBlock_sim_reindexed` (`GenericRegAllocSim`) is the single
  resident-path soundness theorem. Via `regMachineToRegMachineSim` every register-only
  `RegMachine` — ARM `AInst`, RISC-V `RInst`, the vector backends — is a `RegMachineSim`
  with trivial `aux`; x86 supplies its flags+memory `aux` directly. So **all three ISAs
  sit under one resident-path theorem.**

* **spill path** — `MemMachine M` (the memory-extended machine). The lemmas
  `spillStore_establishes` / `evalReload_noop` / `reload_sandwich` (`GenericRegAlloc`)
  are the single spill-path soundness theorems. ARM (`instMemMachineAMemState`),
  RISC-V (`instMemMachineRMemState`), and x86 (`instMemMachineJState`) all instantiate
  it. So **all three ISAs sit under one spill-path theorem.**

This module re-exports the two generic soundness theorems under the unified
`MachineTarget` reading and records that they hold for any ISA providing the
interfaces — "prove once, inherit per backend", realized for register
allocation. Per-ISA instruction selection / lowering / encoding stay separate by
design (the upstream ISel boundary), not as a gap.
-/

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

variable {I S M : Type}

/-- **Unified spill-path soundness** (the spill-path theorem, ISA-agnostic). For ANY
    ISA's spill interface (`MemMachine`), a single spill+reload roundtrip is a no-op on
    the registers when the spill cell still holds the register (`SpillValid`). ARM
    (`instMemMachineAMemState`), RISC-V (`instMemMachineRMemState`), and x86
    (`instMemMachineJState`) all instantiate `MemMachine`, so all three inherit this
    with no per-ISA proof. -/
theorem unified_spill_sound [MemMachine M] (m : M) (off : Int) (r : String)
    (hv : SpillValid off r m) : evalReload m r off = m :=
  reload_sandwich m off r hv

/-- **The resident-path theorem is ISA-agnostic too.** Every register-only `RegMachine`
    resolves a `RegMachineSim` (via `regMachineToRegMachineSim`), so the resident-path
    soundness theorem `GenericRegAllocSim.renameBlock_runBlock_sim_reindexed` — the
    main theorem (renaming commutes with `runBlock` on the register file under an
    injective ρ that preserves register reads + the auxiliary relation) — applies to
    ARM `AInst`, RISC-V `RInst`, and the vector backends as well as x86. This `example`
    witnesses that the `RegMachineSim` interface is available for any `RegMachine`, so
    the resident-path theorem is in scope for all of them. -/
example [RegMachine I S] : RegMachineSim I S := inferInstance

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
