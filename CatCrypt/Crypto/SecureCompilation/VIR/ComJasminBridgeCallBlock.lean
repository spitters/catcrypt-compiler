/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall

/-!
# Whole commands mixing `Cassgn`, the rotate `Copn` and leaf calls

`ComJasminBridgeCopn.MixedBlockSim` threads blocks of register-word `Cassgn`s and
rotate `Copn`s. `CallBlockSim` adds the leaf `Ccall` of `ComJasminBridgeCall` as
a third kind of step. Since a call's callee run is stated at a specific fuel,
the chain is indexed by the fuel `fuel` at which the callee runs; the block is
run by `execCmd` at `fuel + 1`.

## Contents

* `BlockStep`, `BlockStep.toInstr`, `callBlockCmd` — the steps and their emitted
  command.
* `CallBlockSim` — the list-threading predicate.
* `callBlockSim_of_mixedBlockSim` — a mixed block is a call block.
* `callBlock_simulates` / `callBlock_endToEnd` — the whole command runs to
  `.ok s'`, witnesses `Sem`, and ends in `StateCorrReg` with the final store.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCallBlock

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd (RegStep)

variable {SyscallState Mem : Type} [MemModel Mem]

/-- One step of a block: a mixed `Cassgn`/rotate step, or a leaf call
    `dst := fn(args)` annotated `ii`. -/
inductive BlockStep where
  /-- A register-word `Cassgn` or rotate `Copn` step. -/
  | mixed (step : MixedStep)
  /-- A leaf call. -/
  | call (ii : InstrInfo) (dst : VarI) (fn : FunName) (args : List CallArg)

/-- The emitted `Instr` of a block step. -/
def BlockStep.toInstr : BlockStep → Instr
  | .mixed step => step.toInstr
  | .call ii dst fn args => .MkI ii (callInstr dst fn args)

/-- The emitted `Cmd` of a block. -/
def callBlockCmd (steps : List BlockStep) : Cmd :=
  steps.map BlockStep.toInstr

/-- `CallBlockSim aS gd opS prog fuel steps st s names st' s' names'`: the block
    `steps`, started at `(st, s, names)`, ends at `(st', s', names')`. The
    `Cassgn` and rotate cases carry the hypotheses of the corresponding
    `MixedBlockSim` constructors; the call case carries those of
    `ccall_leaf_simulates`, with the callee run at fuel `fuel`. -/
inductive CallBlockSim (aS : AsmSem) (gd : GlobDecls) (opS : OpSem) (prog : Prog)
    (fuel : Nat) :
    List BlockStep → Store → Estate SyscallState Mem → List Var →
    Store → Estate SyscallState Mem → List Var → Prop where
  /-- Empty block. -/
  | nil (st : Store) (s : Estate SyscallState Mem) (names : List Var) :
      CallBlockSim aS gd opS prog fuel [] st s names st s names
  /-- A register-word `Cassgn` head step. -/
  | assgn
      (step : RegStep) (rest : List BlockStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (w : BitVec step.sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : step.dst.v_var.vtype = .aword step.sz)
      (hrhs : semPexpr (Mem := Mem) true gd opS s step.e = .ok (.Vword step.sz w))
      (hdistinct : ∀ r' ∈ names,
          r' ≠ step.dst.v_var ∧ r'.vname ≠ step.dst.v_var.vname)
      (htail : CallBlockSim aS gd opS prog fuel rest
          (Store.set st step.dst.v_var.vname (t := .reg step.sz.bits) w)
          (s.withVm ((s.evm).set step.dst.v_var (.Vword step.sz w)))
          (step.dst.v_var :: names) st' s' names') :
      CallBlockSim aS gd opS prog fuel (.mixed (.assgn step) :: rest) st s names st' s' names'
  /-- A rotate `Copn` head step. -/
  | ror
      (ii : InstrInfo) (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat)
      (rest : List BlockStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (w : BitVec sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : dst.v_var.vtype = .aword sz)
      (hmem : src.v_var ∈ names)
      (hread : (s.evm).get src.v_var = .Vword sz w)
      (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hasm : RorAsmAgrees aS sz)
      (htail : CallBlockSim aS gd opS prog fuel rest
          (Store.set st dst.v_var.vname (t := .reg sz.bits) (w.rotateRight n))
          (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))))
          (dst.v_var :: names) st' s' names') :
      CallBlockSim aS gd opS prog fuel (.mixed (.ror ii tag dst src sz n) :: rest)
        st s names st' s' names'
  /-- A leaf-call head step. -/
  | call
      (ii : InstrInfo) (dst : VarI) (fn : FunName) (args : List CallArg)
      (sz : WSize) (r : BitVec sz.bits) (rest : List BlockStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (scs' : SyscallState) (m' : Mem)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : dst.v_var.vtype = .aword sz)
      (hargs : CallArgsRead names s args)
      (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hcall : execCall (Mem := Mem) aS opS gd fuel s.escs s.emem fn
          (args.map CallArg.value) prog = .ok (scs', m', [.Vword sz r]))
      (htail : CallBlockSim aS gd opS prog fuel rest
          (Store.set st dst.v_var.vname (t := .reg sz.bits) r)
          { s with escs := scs', emem := m', evm := (s.evm).set dst.v_var (.Vword sz r) }
          (dst.v_var :: names) st' s' names') :
      CallBlockSim aS gd opS prog fuel (.call ii dst fn args :: rest) st s names st' s' names'

/-- A mixed block is a call block along `BlockStep.mixed`, with the same emitted
    command, at every fuel. -/
theorem callBlockSim_of_mixedBlockSim
    (aS : AsmSem) (gd : GlobDecls) (opS : OpSem) (prog : Prog) (fuel : Nat)
    {steps : List MixedStep}
    {st : Store} {s : Estate SyscallState Mem} {names : List Var}
    {st' : Store} {s' : Estate SyscallState Mem} {names' : List Var}
    (h : MixedBlockSim aS gd opS steps st s names st' s' names') :
    CallBlockSim aS gd opS prog fuel (steps.map BlockStep.mixed) st s names st' s' names'
    ∧ callBlockCmd (steps.map BlockStep.mixed) = mixedBlockCmd steps := by
  refine ⟨?_, ?_⟩
  · induction h with
    | nil st s names => exact .nil st s names
    | assgn step rest st0 s0 names0 w st'0 s'0 names'0 hdst hrhs hdistinct _ ih =>
      exact .assgn step _ st0 s0 names0 w st'0 s'0 names'0 hdst hrhs hdistinct ih
    | ror ii tag dst src sz n rest st0 s0 names0 w st'0 s'0 names'0
          hdst hmem hread hdistinct hasm _ ih =>
      exact .ror ii tag dst src sz n _ st0 s0 names0 w st'0 s'0 names'0
        hdst hmem hread hdistinct hasm ih
  · simp only [callBlockCmd, mixedBlockCmd, List.map_map]
    rfl

/-- **Whole block simulation with calls.** A `CallBlockSim` chain at callee fuel
    `fuel`, started from a `StateCorrReg names`-corresponding `(st, s)`,
    witnesses that the `execCmd` run of the emitted block at fuel `fuel + 1`
    returns `.ok s'`, and that `s'` corresponds to `st'` on `names'`. -/
theorem callBlock_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (steps : List BlockStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (hblock : CallBlockSim aS gd opS prog fuel steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    execCmd (Mem := Mem) aS opS gd (fuel + 1) s (callBlockCmd steps) prog = .ok s'
    ∧ StateCorrReg names' st' s'.evm := by
  induction hblock with
  | nil st s names =>
    exact ⟨CmdRun.execCmd_nil aS opS gd (fuel + 1) s prog, hcorr⟩
  | assgn step rest st0 s0 names0 w st'0 s'0 names'0 hdst hrhs hdistinct _ ih =>
    obtain ⟨hrun, hcorr'⟩ :=
      ComJasminBridgeFull.cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
        gd opS step.dst step.sz step.tag step.e w s0 st0 names0 hdst hrhs hdistinct hcorr
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((BlockStep.mixed (.assgn step)).toInstr :: callBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (BlockStep.mixed (.assgn step)).toInstr prog
          = .ok (s0.withVm ((s0.evm).set step.dst.v_var (.Vword step.sz w))) := by
      rw [BlockStep.toInstr, MixedStep.toInstr, ComJasminBridgeCmd.RegStep.toInstr, execInstr,
        OpSemCoverage.execInstrR_Cassgn_eq]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih hcorr'
  | ror ii tag dst src sz n rest st0 s0 names0 w st'0 s'0 names'0
        hdst hmem hread hdistinct hasm _ ih =>
    obtain ⟨hrun, _, hcorr'⟩ :=
      copn_ror_simulates aS opS gd prog fuel tag dst src sz n w s0 st0 names0
        hdst hmem hread hdistinct hcorr hasm
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((BlockStep.mixed (.ror ii tag dst src sz n)).toInstr :: callBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (BlockStep.mixed (.ror ii tag dst src sz n)).toInstr prog
          = .ok (s0.withVm ((s0.evm).set dst.v_var (.Vword sz (w.rotateRight n)))) := by
      rw [BlockStep.toInstr, MixedStep.toInstr, execInstr]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih hcorr'
  | call ii dst fn args sz r rest st0 s0 names0 scs' m' st'0 s'0 names'0
        hdst hargs hdistinct hcall _ ih =>
    obtain ⟨hrun, _, hcorr'⟩ :=
      ccall_leaf_simulates aS opS gd prog fuel dst fn args sz r s0 st0 names0 scs' m'
        hdst hargs hdistinct hcorr hcall
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((BlockStep.call ii dst fn args).toInstr :: callBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0 (BlockStep.call ii dst fn args).toInstr prog
          = .ok { s0 with escs := scs', emem := m', evm := (s0.evm).set dst.v_var (.Vword sz r) } := by
      rw [BlockStep.toInstr, execInstr]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih hcorr'

/-- **End-to-end whole block bridge with calls.** Under the hypotheses of
    `callBlock_simulates`, the emitted block witnesses the relational
    whole-command step `Sem` to `s'`, and `s'` corresponds to `st'` on `names'`. -/
theorem callBlock_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (steps : List BlockStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (hblock : CallBlockSim aS gd opS prog fuel steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    Sem (Mem := Mem) aS opS gd prog s (callBlockCmd steps) s'
    ∧ StateCorrReg names' st' s'.evm := by
  obtain ⟨hrun, hcorr'⟩ :=
    callBlock_simulates aS opS gd prog fuel steps st s names st' s' names' hblock hcorr
  exact ⟨execCmd_sound (n := fuel + 1) aS opS gd prog hrun, hcorr'⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCallBlock
