/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAllocSim


@[expose] public section
set_option autoImplicit false

/-!
# `RegMachineSim` is the one universal resident-path interface

The generic register allocator has a two-tier resident-path abstraction:
`RegMachine` (register-only `writes_rename`, instantiated by ARM `AInst` / RISC-V
`RInst` / the vector backends) and `RegMachineSim` (a ρ-aware auxiliary `aux` relation
for the flag- and memory-reading x86 scalar ops, whose register-only `writes_rename` is
*not* provable for `adc`/`loadMem`/…).

The **conservative-extension** instance the `RegMachineSim` docstring names unifies them:
every `RegMachine` is a `RegMachineSim` with the trivial auxiliary relation
`aux := fun _ _ _ => True`. The register-only `writes_rename` discharges the
`aux`-conditioned `writes_rename_sim` (the `aux` hypothesis is ignored), and `aux_step`
is `trivial`. So `RegMachineSim` is the single resident-path interface all three backends
instantiate: ARM/RISC-V (and the vector backends) inherit it here, x86 supplies its
flags+memory `aux` directly. The generic simulation theorem
`renameBlock_runBlock_sim_reindexed` is then the one resident-path soundness theorem for
every ISA — the "one `MachineTarget`" unification on the register-allocation pass.
-/

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

variable {I S : Type}

/-- **The universal bridge.** Every register-only `RegMachine` is a `RegMachineSim` with
    trivial `aux`. Low priority so a backend's bespoke `RegMachineSim` (x86's flags+memory
    `aux`) is preferred where it exists. With this, `RegMachineSim` — and its main theorem
    `renameBlock_runBlock_sim_reindexed` — is the single resident-path interface ARM,
    RISC-V, the vector backends, and x86 all sit under. -/
instance (priority := 50) regMachineToRegMachineSim [inst : RegMachine I S] :
    RegMachineSim I S where
  toMachineModel := inst.toMachineModel
  runBlock := RegMachine.runBlock
  Val := RegMachine.Val I S
  get := RegMachine.get
  set := RegMachine.set
  writes := RegMachine.writes
  renameInst := RegMachine.renameInst (S := S)
  isDiscard := RegMachine.isDiscard I S
  aux _ _ _ := True
  get_discard := RegMachine.get_discard
  get_set_same := RegMachine.get_set_same
  get_set_other := RegMachine.get_set_other
  evalInst_eq_set := RegMachine.evalInst_eq_set
  runBlock_nil := RegMachine.runBlock_nil
  runBlock_append := RegMachine.runBlock_append
  writes_names := RegMachine.writes_names
  writes_rename_sim ρ s t i hread _ := RegMachine.writes_rename ρ s t i hread
  aux_step _ _ _ _ _ _ _ := trivial

/-- **Smoke: the bridge fires.** Any register-only `RegMachine` (ARM `AInst`, RISC-V
    `RInst`, the vector backends) also resolves a `RegMachineSim` instance — so the
    single simulation theorem covers all three ISAs, x86 included. -/
example [RegMachine I S] : RegMachineSim I S := inferInstance

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
