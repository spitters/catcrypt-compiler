/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFor
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr

/-!
# The mirror memory `emem` in the `Com ↔ Jasmin` state relation

The JasminPrint `Store` has no memory component, and `JasminPrint.lowerExpr`
emits no `Pload`/`Lmem`. The mirror state nevertheless carries a memory `emem`,
which a callee run may change. `StateCorrMem regNames arrNames P st s` extends
the register and array correspondences (`StateCorrReg`, `StateCorrArr`) by a
predicate `P` on the mirror memory: an invariant chosen by the caller, for
instance equality with a fixed memory, or a separation-style frame.

The register and array steps of the bridge change only the mirror `Vm`
(`Estate.withVm`), so they preserve `P`. A mixed `Cassgn`/rotate block and a
counted `Cfor` over such a body leave the memory unchanged
(`mixedBlockSim_emem`, `forBodySim_emem`). A leaf call replaces the memory by the
callee's; `P` holds afterwards when it holds of the callee's memory.

## Contents

* `StateCorrMem`, `stateCorrMem_withVm`.
* `mixedBlockSim_emem` / `mixedBlock_simulates_mem`.
* `forBodySim_emem` / `cfor_simulates_mem`.
* `ccall_leaf_simulates_mem`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeMem

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFor
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The relation -/

/-- `StateCorrMem regNames arrNames P st s`: the store `st` corresponds to the
    mirror `Vm` on the register frame `regNames` and the array frame `arrNames`,
    and the mirror memory satisfies `P`. -/
def StateCorrMem (regNames arrNames : List Var) (P : Mem → Prop) (st : Store)
    (s : Estate SyscallState Mem) : Prop :=
  StateCorrReg regNames st s.evm ∧ StateCorrArr arrNames st s.evm ∧ P s.emem

omit [MemModel Mem] in
/-- A step that replaces only the mirror `Vm` keeps the memory component: the
    register and array correspondences of the new `Vm`, together with `P` on the
    old memory, give `StateCorrMem` of the new state. -/
theorem stateCorrMem_withVm (regNames arrNames : List Var) (P : Mem → Prop)
    (st : Store) (s : Estate SyscallState Mem) (vm : Vm)
    (hreg : StateCorrReg regNames st vm) (harr : StateCorrArr arrNames st vm)
    (hP : P s.emem) :
    StateCorrMem regNames arrNames P st (s.withVm vm) :=
  ⟨hreg, harr, hP⟩

/-! ## §2. Blocks and loops leave the memory unchanged -/

/-- A mixed `Cassgn`/rotate chain ends with the memory and syscall state it
    started with. -/
theorem mixedBlockSim_emem (aS : AsmSem) (gd : GlobDecls) (opS : OpSem)
    {steps : List MixedStep} {st : Store} {s : Estate SyscallState Mem} {names : List Var}
    {st' : Store} {s' : Estate SyscallState Mem} {names' : List Var}
    (h : MixedBlockSim aS gd opS steps st s names st' s' names') :
    s'.emem = s.emem ∧ s'.escs = s.escs := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | assgn _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | ror _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- **Mixed block with memory.** Under the hypotheses of `mixedBlock_simulates`
    and `P s.emem`, the block run reaches `s'` with
    `StateCorrMem names' [] P st' s'`. -/
theorem mixedBlock_simulates_mem
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (steps : List MixedStep) (P : Mem → Prop)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hblock : MixedBlockSim aS gd opS steps st s names st' s' names')
    (hcorr : StateCorrMem names [] P st s) :
    execCmd (Mem := Mem) aS opS gd (fuel + 1) s (mixedBlockCmd steps) prog = .ok s'
    ∧ StateCorrMem names' [] P st' s' := by
  obtain ⟨hrun, hreg⟩ :=
    mixedBlock_simulates aS opS gd prog steps st s names st' s' names' fuel hblock hcorr.1
  refine ⟨hrun, hreg, fun _ h => absurd h List.not_mem_nil, ?_⟩
  rw [(mixedBlockSim_emem aS gd opS hblock).1]
  exact hcorr.2.2

/-- The states of a counted loop whose iterations are `ForBodySim` chains all
    carry the initial memory. -/
theorem forBodySim_emem (aS : AsmSem) (gd : GlobDecls) (opS : OpSem)
    (i : VarI) (n : Nat) (body : List MixedStep)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var)
    (hsim : ForBodySim aS gd opS i n body stores states frames) :
    ∀ k ≤ n, (states k).emem = (states 0).emem := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [(mixedBlockSim_emem aS gd opS (hsim.step k (by omega))).1]
    exact ih (by omega)

/-- **Counted loop with memory.** Under the hypotheses of `cfor_simulates` and
    `P (states 0).emem`, the `Cfor` run reaches `states n` with
    `StateCorrMem (frames n) [] P (stores n) (states n)`. -/
theorem cfor_simulates_mem
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (i : VarI) (n : Nat) (body : List MixedStep) (P : Mem → Prop)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var) (fuel : Nat)
    (hsim : ForBodySim aS gd opS i n body stores states frames)
    (hcorr : StateCorrMem (frames 0) [] P (stores 0) (states 0)) :
    execInstrR (Mem := Mem) aS opS gd (fuel + n + 2) (states 0) (forInstr i n body) prog
      = .ok (states n)
    ∧ StateCorrMem (frames n) [] P (stores n) (states n) := by
  obtain ⟨hrun, hreg⟩ :=
    cfor_simulates aS opS gd prog i n body stores states frames fuel hsim hcorr.1
  refine ⟨hrun, hreg, fun _ h => absurd h List.not_mem_nil, ?_⟩
  rw [forBodySim_emem aS gd opS i n body stores states frames hsim n le_rfl]
  exact hcorr.2.2

/-! ## §3. A leaf call replaces the memory -/

/-- **Leaf call with memory.** Under the hypotheses of `ccall_leaf_simulates`,
    when the callee's resulting memory `m'` satisfies `P`, the call run reaches
    the post-state with `StateCorrMem (dst :: names) [] P (Store.set st dst.vname r)`. -/
theorem ccall_leaf_simulates_mem
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (dst : VarI) (fn : FunName) (args : List CallArg) (sz : WSize) (r : BitVec sz.bits)
    (P : Mem → Prop)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (scs' : SyscallState) (m' : Mem)
    (hdst : dst.v_var.vtype = .aword sz)
    (hargs : CallArgsRead names s args)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm))
    (hcall : execCall (Mem := Mem) aS opS gd fuel s.escs s.emem fn
        (args.map CallArg.value) prog = .ok (scs', m', [.Vword sz r]))
    (hP : P m') :
    execInstrR (Mem := Mem) aS opS gd (fuel + 1) s (callInstr dst fn args) prog
      = .ok ({ s with escs := scs', emem := m', evm := (s.evm).set dst.v_var (.Vword sz r) })
    ∧ StateCorrMem (dst.v_var :: names) [] P
        (Store.set st dst.v_var.vname (t := .reg sz.bits) r)
        ({ s with escs := scs', emem := m', evm := (s.evm).set dst.v_var (.Vword sz r) }) := by
  obtain ⟨hrun, _, hreg⟩ :=
    ccall_leaf_simulates aS opS gd prog fuel dst fn args sz r s st names scs' m'
      hdst hargs hdistinct hcorr hcall
  exact ⟨hrun, hreg, fun _ h => absurd h List.not_mem_nil, hP⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeMem
