/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmRegAlloc
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# The A64 `AInst`/`AState` allocator fits the generic `MachineModel` (validation)

`ArmRegAlloc` is the A64 spilling register allocator, monomorphized to
`AInst`/`AState`. `Optimizer.GenericRegAlloc` abstracts that allocator (and the
x86 one) into a `MachineModel`-parameterized validated pass with the soundness theorems
proved **once**. This module **validates the abstraction against the existing ARM
instance**: it exhibits `MachineModel AInst` / `RegMachine AInst AState` / `MemMachine
AMemState` instances built from the *already-proved* `ArmRegAlloc` facts
(`evalAInst_eq_set`, `writtenName_rename`, the `AState` register-file laws, the
`AMemState` cell laws), and shows the generic theorem `renameBlock_runBlock`, instantiated
at the ARM types, gives back exactly what `ArmRegAlloc.renameABlock_runABlock` proved.

This is the "do the generic lemmas, specialized, recover the hand-proved ones?" check:
the answer is yes, with no re-proof — the instance wiring is pure plumbing over the
existing ArmRegAlloc theorems (which are **not** edited). Together with the fresh RISC-V
instantiation (`RISCVBackend.RiscvRegAlloc`), this confirms the `MachineModel` abstraction
is faithful on these two backends. (x86 `SpillingRegAlloc` is not instantiated: its `JInstr`
two-destination `mulx` needs a multi-written-name generalization of the single-`writtenName`
shape; the monomorphic x86 soundness is proved in `SpillingRegAlloc`.)

No `sorry`; the per-read-name `instVal_rename` is by `cases` over `AInst`, the rest is the
existing ArmRegAlloc/ArmModel laws.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmRegAllocGeneric

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmRegAlloc
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. The per-read-name source-locality of `instVal` (the one fact not already
in the shape the generic class wants)

`ArmRegAlloc.instVal_rename` is stated with the full `Reindexed`/injectivity bundle; the
generic `RegMachine.instVal_rename` wants the weaker per-read-name hypothesis. We derive
it by `cases` over `AInst` (each op's `instVal` reads only its `readNames`). -/

/-- **The renamed op writes the same value**, given that every source read agrees via
    `ρ`. The A64 per-read-name source-locality the generic `RegMachine` class needs. -/
theorem instVal_rename_local (ρ : String → String) (s t : AState) (i : AInst)
    (h : ∀ a ∈ readNames i, t.get (ρ a) = s.get a) :
    instVal t (renameAInst ρ i) = instVal s i := by
  cases i <;>
    simp only [renameAInst, instVal, ArmRegAlloc.readNames, ainstDstSrcs, List.mem_cons,
      forall_eq_or_imp] at h ⊢ <;>
    (try obtain ⟨ha, hb⟩ := h) <;>
    simp_all [AState.get]

/-! ## 2. The `MachineModel` / `RegMachine` / `MemMachine` instances for A64 -/

/-- **`MachineModel AInst`**: the syntactic interface for the A64 backend — written/read
    names from `writtenName`/`readNames`, the A64 GP file `gpFile`, and `str`/`ldr`
    rendered (here as `mov` markers carrying the name, the printer attaching the offset,
    matching the `ArmRegAlloc.Item.spill` posture). -/
instance instMachineModelAInst : MachineModel AInst where
  writtenNames i := [ArmRegAlloc.writtenName i]
  readNames := ArmRegAlloc.readNames
  physRegs := gpFile
  mkSpill r _off := .mov r r
  mkReload r _off := .mov r r

/-- **`RegMachine AInst AState`**: the A64 semantic interface, wired from the existing
    `ArmRegAlloc`/`ArmModel` facts. The generic theorem `renameBlock_runBlock` specializes
    through this instance to the A64 register-resident path that `ArmRegAlloc.renameABlock_runABlock`
    proves by hand. -/
instance instRegMachineAInst : RegMachine AInst AState where
  toMachineModel := instMachineModelAInst
  runBlock := runABlock
  Val := W32
  get := AState.get
  set := AState.set
  isDiscard r := r == "wzr"
  writes s i := [(ArmRegAlloc.writtenName i, instVal s i)]
  renameInst := renameAInst
  get_discard s s' r r' hr hr' := by
    have h1 : r = "wzr" := by simpa using hr
    have h2 : r' = "wzr" := by simpa using hr'
    simp [AState.get, h1, h2]
  get_set_same s r v h := AState.get_set_same s r v (by simpa using h)
  get_set_other s r r' v h := AState.get_set_other s r' r v (Ne.symm h)
  evalInst_eq_set s i r :=
    congrArg (fun st => AState.get st r) (by
      have := evalAInst_eq_set s i
      simpa [runABlock] using this)
  runBlock_nil := runABlock_nil
  runBlock_append := runABlock_append
  writes_names s i := rfl
  writes_rename ρ s t i h := by
    show [(ArmRegAlloc.writtenName (renameAInst ρ i), instVal t (renameAInst ρ i))]
      = [(ρ (ArmRegAlloc.writtenName i), instVal s i)]
    rw [instVal_rename_local ρ s t i h, writtenName_rename ρ i]

/-- **`MemMachine AMemState`**: the A64 spill-path interface, from the existing
    `ArmRegAlloc.AMemState` cell/register laws, so the generic spill soundness applies. -/
instance instMemMachineAMemState : MemMachine AMemState where
  Val := W32
  get := AMemState.get
  load := AMemState.load
  setReg := AMemState.setReg
  store := AMemState.store
  load_store_same := AMemState.load_store_same
  load_store_other m off o v h := AMemState.load_store_other m off o v h
  get_store := AMemState.get_store
  setReg_get_self m r := by
    -- `setReg r (get r) = m`: writing a register a value it already holds is a no-op.
    unfold AMemState.setReg AMemState.get
    by_cases hz : r = "wzr"
    · cases m with | mk st mem => simp only [AState.set, hz, if_true]
    · cases m with
      | mk st mem =>
        simp only [AState.get, hz, if_false]
        congr 1
        cases st with
        | mk regs =>
          simp only [AState.set, hz, if_false]
          congr 1
          funext r'
          by_cases h : r' = r <;> simp [h]

/-! ## 3. The abstraction validated: the generic theorems recover the ARM ones

The generic `renameBlock_runBlock` / `spillStore_establishes` / `reload_sandwich`,
instantiated at the A64 types, give `ArmRegAlloc.renameABlock_runABlock`,
`ArmRegAlloc.spillStore_establishes` and `ArmRegAlloc.evalReload_noop` from the generic
pass with no re-proof. -/

/-- **A64 resident-path soundness via the generic pass.** `GenericRegAlloc.renameBlock_runBlock`
    at `AInst`/`AState`: an injective `wzr`-preserving renaming `ρ` commutes with `runABlock`.
    The same content as the hand-proved `ArmRegAlloc.renameABlock_runABlock`, recovered from
    the abstraction — the validation that the generic typeclass is faithful on the A64 instance. -/
theorem renameABlock_runABlock_generic (ρ : String → String) (hinj : Function.Injective ρ)
    (hρd : ∀ r, rmDisc AInst AState r = true → rmDisc AInst AState (ρ r) = true)
    (hρnd : ∀ r, rmDisc AInst AState r = false → rmDisc AInst AState (ρ r) = false)
    (block : List AInst)
    (hz : ∀ i ∈ block, rmDisc AInst AState (ArmRegAlloc.writtenName i) = false)
    (s t : AState) (h : Reindexed AInst ρ s t) :
    Reindexed AInst ρ (rmRun AInst s block) (rmRun AInst t (renameBlock (S := AState) ρ block)) :=
  renameBlock_runBlock AInst ρ hinj hρd hρnd block
    (fun i hi n hn => by
      have hn' : n = ArmRegAlloc.writtenName i := by
        simpa [MachineModel.writtenNames, instMachineModelAInst] using hn
      exact hn' ▸ hz i hi) s t h

/-- **A64 spill-store establishes the cell↦reg invariant via the generic pass** —
    `GenericRegAlloc.spillStore_establishes` at `AMemState` (the content of
    `ArmRegAlloc.spillStore_establishes`). -/
theorem spillStore_establishes_generic (m : AMemState) (off : Int) (r : String) :
    CatCrypt.Crypto.Optimizer.GenericRegAlloc.SpillValid off r
      (CatCrypt.Crypto.Optimizer.GenericRegAlloc.evalSpillStore m off r) :=
  CatCrypt.Crypto.Optimizer.GenericRegAlloc.spillStore_establishes m off r

/-- **A64 reload at an agreeing cell via the generic pass** — `GenericRegAlloc.reload_sandwich`
    at `AMemState`: when cell `off` holds `r`'s value, the reload is a no-op (the content of
    `ArmRegAlloc.evalReload_noop`). The composition with a spill store and an intervening
    block is `ArmRegAlloc.reload_sandwich`. -/
theorem reload_sandwich_generic (m : AMemState) (off : Int) (r : String)
    (hv : CatCrypt.Crypto.Optimizer.GenericRegAlloc.SpillValid off r m) :
    CatCrypt.Crypto.Optimizer.GenericRegAlloc.evalReload m r off = m :=
  CatCrypt.Crypto.Optimizer.GenericRegAlloc.reload_sandwich m off r hv

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmRegAllocGeneric
