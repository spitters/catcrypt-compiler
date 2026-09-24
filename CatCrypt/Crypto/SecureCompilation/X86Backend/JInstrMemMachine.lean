/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine


@[expose] public section
set_option autoImplicit false

/-!
# `MemMachine (JState 64)` — x86 inherits the generic spill soundness theorems

The generic register-allocation spill soundness (`GenericRegAlloc.spillStore_establishes`
/ `evalReload_noop` / `reload_sandwich`) is proved ONCE over
`[MemMachine M]`. ARM (`instMemMachineAMemState`) and RISC-V (`instMemMachineRMemState`)
instantiate it; this module instantiates it for **x86**.

x86's spill/reload write/read the `%rsp` frame (`mkSpill r off = storeMem "%rsp" off`,
`mkReload r off = loadMem r "%rsp" off` — see `instMachineModelJInstr`), so the
offset-indexed `MemMachine` frame is `JState`'s memory at the fixed base `"%rsp"`. The
four cell/register laws are immediate from `JState`'s reg/mem separation (`store` keeps
`regs`, `setReg` is a single-`regs` update). With this instance the generic spill
theorems apply at the x86 types — x86 inherits the generic spill soundness, as
ARM and RISC-V do, completing the resident-path (`RegMachineSim`) story on the spill side.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrMemMachine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-- **`MemMachine (JState 64)`**: the x86 spill-path interface over the `%rsp` frame,
    so the generic spill theorems apply at the x86 types (mirroring the A64
    `instMemMachineAMemState` / RV64 `instMemMachineRMemState`). -/
instance instMemMachineJState : MemMachine (JState 64) where
  Val := BitVec 64
  get s r := s.get r
  load s off := s.load "%rsp" off
  setReg := JState.setReg
  store s off v := s.store "%rsp" off v
  load_store_same s off v := JState.load_store_same s "%rsp" off v
  load_store_other s off o v h :=
    JState.load_store_other s "%rsp" off v "%rsp" o (by simp [h])
  get_store s off v r := by simp [JState.store, JState.get]
  setReg_get_self s r := by
    -- writing register `r` a value it already holds is a no-op
    cases s with
    | mk regs flags mem =>
      simp only [JState.setReg, JState.get, JState.mk.injEq, and_self, and_true]
      funext r'
      by_cases h : r' = r <;> simp [h]

/-! ## x86 inherits the generic spill theorems

The three generic spill-soundness theorems, specialized to the x86 `JState 64` — no
re-proof, they fall out of `instMemMachineJState`. These are the x86 analogues of the
A64 `reload_sandwich` the monomorphic `SpillingRegAlloc` proved by hand. -/

/-- **x86 spill establishes `SpillValid`** (generic `spillStore_establishes` at `JState`). -/
theorem jstate_spillStore_establishes (s : JState 64) (off : Int) (r : String) :
    SpillValid off r (evalSpillStore s off r) :=
  spillStore_establishes s off r

/-- **x86 reload is a no-op under `SpillValid`** (generic `evalReload_noop` at `JState`). -/
theorem jstate_evalReload_noop (s : JState 64) (off : Int) (r : String)
    (hv : SpillValid off r s) : evalReload s r off = s :=
  evalReload_noop s off r hv

/-- **x86 single-spill roundtrip soundness** — the generic `reload_sandwich` at the x86
    types: the reload before `r`'s use is a no-op when the `%rsp` spill cell still holds
    `r`. x86 inherits the spill soundness exactly as ARM/RISC-V do. -/
theorem jstate_reload_sandwich (s : JState 64) (off : Int) (r : String)
    (hv : SpillValid off r s) : evalReload s r off = s :=
  reload_sandwich s off r hv

end CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrMemMachine
