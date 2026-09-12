/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCallBlock
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeMem

/-!
# Whole commands with array reads and writes

`ComJasminBridgeCallBlock.CallBlockSim` threads blocks of register-word
`Cassgn`s, rotate `Copn`s and leaf calls over `StateCorrReg`. `ArrBlockSim` adds
the register-index array read `dst := arr[idx]` and the array write
`arr[idx] := src` of `ComJasminBridgeArrIdx`, and threads the full relation
`StateCorrMem regNames arrNames P` of `ComJasminBridgeMem`: registers, a byte
array frame, and a memory invariant.

Every register write keeps the array frame corresponding when the written
register is distinct from the frame (`stateCorrArr_write_reg`). An array write
at `arr` requires the array frame to be `arr :: arrRest` with `arrRest` distinct
from `arr`, the shape `ComJasminBridgeArrIdx.cassgn_laset_simulates` preserves.
A leaf call requires the invariant `P` of the callee's memory.

## Contents

* `stateCorrArr_write_reg` — a register write outside the array frame.
* `ArrBlockStep`, `ArrBlockStep.toInstr`, `arrBlockCmd`.
* `ArrBlockSim` — the list-threading predicate.
* `arrBlock_simulates` / `arrBlock_endToEnd`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrBlock

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCallBlock
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeMem
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd (RegStep)

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. Register writes outside the array frame -/

/-- Writing a register `dst` (any value on the mirror, any register word in the
    store) keeps `StateCorrArr` on an array frame whose variables and names are
    distinct from `dst`. -/
theorem stateCorrArr_write_reg (dst : Var) (sz : WSize) (w : BitVec sz.bits) (v : Value)
    (st : Store) (vm : Vm) (arrNames : List Var)
    (hd : ∀ r ∈ arrNames, r ≠ dst ∧ r.vname ≠ dst.vname)
    (h : StateCorrArr arrNames st vm) :
    StateCorrArr arrNames (Store.set st dst.vname (t := .reg sz.bits) w) (vm.set dst v) := by
  intro r hr
  obtain ⟨hne, hname⟩ := hd r hr
  show Store.set st dst.vname (t := .reg sz.bits) w r.vname = encodeArrVal ((vm.set dst v).get r)
  have hm : (vm.set dst v).get r = vm.get r := by simp [Vm.get, Vm.set, hne]
  have hs : Store.set st dst.vname (t := .reg sz.bits) w r.vname = st r.vname := by
    simp [Store.set, hname]
  rw [hm, hs]
  exact h r hr

/-! ## §2. Steps and the predicate -/

/-- One step of a block with array accesses: a `BlockStep`, the byte read
    `dst := arr[idx]`, or the byte write `arr[idx] := src`. -/
inductive ArrBlockStep where
  /-- A register-word `Cassgn`, rotate `Copn` or leaf call. -/
  | base (step : BlockStep)
  /-- The register-index read `dst := arr[idx]`. -/
  | pget (ii : InstrInfo) (tag : AssgnTag) (dst arr idx : VarI)
      (al : Aligned) (aa : ArrAccess) (ws : WSize)
  /-- The register-index write `arr[idx] := src`. -/
  | laset (ii : InstrInfo) (tag : AssgnTag) (arr idx src : VarI)
      (al : Aligned) (aa : ArrAccess)

/-- The emitted `Instr` of a step. -/
def ArrBlockStep.toInstr : ArrBlockStep → Instr
  | .base step => step.toInstr
  | .pget ii tag dst arr idx al aa ws =>
      .MkI ii (.Cassgn (.Lvar dst) tag (.aword .U8) (.Pget al aa ws (mkLvar arr) (idxExpr idx)))
  | .laset ii tag arr idx src al aa =>
      .MkI ii (.Cassgn (.Laset al aa .U8 arr (idxExpr idx)) tag (.aword .U8) (.Pvar (mkLvar src)))

/-- The emitted `Cmd` of a block. -/
def arrBlockCmd (steps : List ArrBlockStep) : Cmd :=
  steps.map ArrBlockStep.toInstr

/-- `ArrBlockSim aS gd opS prog fuel P steps st s regs arrs st' s' regs' arrs'`:
    the block `steps`, started at store `st`, mirror state `s`, register frame
    `regs` and array frame `arrs`, ends at `(st', s', regs', arrs')`. Each step
    carries the hypotheses of its per-step bridge, stated at the running state,
    together with distinctness of every written register from the array frame;
    a call also carries `P` of the callee's memory, and an array write requires
    the array frame to start with the written array. -/
inductive ArrBlockSim (aS : AsmSem) (gd : GlobDecls) (opS : OpSem) (prog : Prog)
    (fuel : Nat) (P : Mem → Prop) :
    List ArrBlockStep → Store → Estate SyscallState Mem → List Var → List Var →
    Store → Estate SyscallState Mem → List Var → List Var → Prop where
  /-- Empty block. -/
  | nil (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var) :
      ArrBlockSim aS gd opS prog fuel P [] st s regs arrs st s regs arrs
  /-- A register-word `Cassgn` head step. -/
  | assgn
      (step : RegStep) (rest : List ArrBlockStep)
      (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var)
      (w : BitVec step.sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
      (hdst : step.dst.v_var.vtype = .aword step.sz)
      (hrhs : semPexpr (Mem := Mem) true gd opS s step.e = .ok (.Vword step.sz w))
      (hdistinct : ∀ r' ∈ regs, r' ≠ step.dst.v_var ∧ r'.vname ≠ step.dst.v_var.vname)
      (hdA : ∀ r' ∈ arrs, r' ≠ step.dst.v_var ∧ r'.vname ≠ step.dst.v_var.vname)
      (htail : ArrBlockSim aS gd opS prog fuel P rest
          (Store.set st step.dst.v_var.vname (t := .reg step.sz.bits) w)
          (s.withVm ((s.evm).set step.dst.v_var (.Vword step.sz w)))
          (step.dst.v_var :: regs) arrs st' s' regs' arrs') :
      ArrBlockSim aS gd opS prog fuel P (.base (.mixed (.assgn step)) :: rest)
        st s regs arrs st' s' regs' arrs'
  /-- A rotate `Copn` head step. -/
  | ror
      (ii : InstrInfo) (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat)
      (rest : List ArrBlockStep)
      (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var)
      (w : BitVec sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
      (hdst : dst.v_var.vtype = .aword sz)
      (hmem : src.v_var ∈ regs)
      (hread : (s.evm).get src.v_var = .Vword sz w)
      (hdistinct : ∀ r' ∈ regs, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hdA : ∀ r' ∈ arrs, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hasm : RorAsmAgrees aS sz)
      (htail : ArrBlockSim aS gd opS prog fuel P rest
          (Store.set st dst.v_var.vname (t := .reg sz.bits) (w.rotateRight n))
          (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))))
          (dst.v_var :: regs) arrs st' s' regs' arrs') :
      ArrBlockSim aS gd opS prog fuel P (.base (.mixed (.ror ii tag dst src sz n)) :: rest)
        st s regs arrs st' s' regs' arrs'
  /-- A leaf-call head step. -/
  | call
      (ii : InstrInfo) (dst : VarI) (fn : FunName) (args : List CallArg)
      (sz : WSize) (r : BitVec sz.bits) (rest : List ArrBlockStep)
      (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var)
      (scs' : SyscallState) (m' : Mem)
      (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
      (hdst : dst.v_var.vtype = .aword sz)
      (hargs : CallArgsRead regs s args)
      (hdistinct : ∀ r' ∈ regs, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hdA : ∀ r' ∈ arrs, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hcall : execCall (Mem := Mem) aS opS gd fuel s.escs s.emem fn
          (args.map CallArg.value) prog = .ok (scs', m', [.Vword sz r]))
      (hP : P m')
      (htail : ArrBlockSim aS gd opS prog fuel P rest
          (Store.set st dst.v_var.vname (t := .reg sz.bits) r)
          { s with escs := scs', emem := m', evm := (s.evm).set dst.v_var (.Vword sz r) }
          (dst.v_var :: regs) arrs st' s' regs' arrs') :
      ArrBlockSim aS gd opS prog fuel P (.base (.call ii dst fn args) :: rest)
        st s regs arrs st' s' regs' arrs'
  /-- A register-index array read head step. -/
  | pget
      (ii : InstrInfo) (tag : AssgnTag) (dst arr idx : VarI)
      (al : Aligned) (aa : ArrAccess) (ws : WSize)
      (n : Nat) (a : JArrayMirror n) (i : BitVec WSize.U64.bits)
      (rest : List ArrBlockStep)
      (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var)
      (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
      (hagree : IntOfWordAgrees opS)
      (hdst : dst.v_var.vtype = .aword .U8)
      (hread : (s.evm).get arr.v_var = .Varr n a)
      (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
      (hin : i.toNat < n)
      (hdistinct : ∀ r' ∈ regs, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hdA : ∀ r' ∈ arrs, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (htail : ArrBlockSim aS gd opS prog fuel P rest
          (Store.set st dst.v_var.vname (t := .reg 8) (a ⟨i.toNat, hin⟩))
          (s.withVm ((s.evm).set dst.v_var (.Vword .U8 (a ⟨i.toNat, hin⟩))))
          (dst.v_var :: regs) arrs st' s' regs' arrs') :
      ArrBlockSim aS gd opS prog fuel P (.pget ii tag dst arr idx al aa ws :: rest)
        st s regs arrs st' s' regs' arrs'
  /-- A register-index array write head step, on an array frame headed by the
      written array. -/
  | laset
      (ii : InstrInfo) (tag : AssgnTag) (arr idx src : VarI)
      (al : Aligned) (aa : ArrAccess) (ws : WSize)
      (n : Nat) (a : JArrayMirror n) (i : BitVec WSize.U64.bits) (v : BitVec WSize.U8.bits)
      (rest : List ArrBlockStep)
      (st : Store) (s : Estate SyscallState Mem) (regs arrRest : List Var)
      (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
      (hagree : IntOfWordAgrees opS)
      (harrTy : arr.v_var.vtype = .aarr ws n)
      (hread : (s.evm).get arr.v_var = .Varr n a)
      (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
      (hsrc : (s.evm).get src.v_var = .Vword .U8 v)
      (hin : i.toNat < n)
      (him : idx.v_var ∈ regs) (hsm : src.v_var ∈ regs)
      (hdA : ∀ r ∈ arrRest, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname)
      (hdR : ∀ r ∈ regs, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname)
      (htail : ArrBlockSim aS gd opS prog fuel P rest
          (Store.set st arr.v_var.vname (t := .stackArr 8 n)
            (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))
          (s.withVm ((s.evm).set arr.v_var (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))))
          regs (arr.v_var :: arrRest) st' s' regs' arrs') :
      ArrBlockSim aS gd opS prog fuel P (.laset ii tag arr idx src al aa :: rest)
        st s regs (arr.v_var :: arrRest) st' s' regs' arrs'

/-! ## §3. The whole-command bridge -/

/-- **Whole block simulation with array accesses.** An `ArrBlockSim` chain,
    started from `StateCorrMem regs arrs P st s`, witnesses that the `execCmd`
    run of the emitted block at fuel `fuel + 1` returns `.ok s'`, and that
    `StateCorrMem regs' arrs' P st' s'` holds. -/
theorem arrBlock_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (P : Mem → Prop) (steps : List ArrBlockStep)
    (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
    (hblock : ArrBlockSim aS gd opS prog fuel P steps st s regs arrs st' s' regs' arrs')
    (hcorr : StateCorrMem regs arrs P st s) :
    execCmd (Mem := Mem) aS opS gd (fuel + 1) s (arrBlockCmd steps) prog = .ok s'
    ∧ StateCorrMem regs' arrs' P st' s' := by
  induction hblock with
  | nil st s regs arrs =>
    exact ⟨CmdRun.execCmd_nil aS opS gd (fuel + 1) s prog, hcorr⟩
  | assgn step rest st0 s0 regs0 arrs0 w st'0 s'0 regs'0 arrs'0
        hdst hrhs hdistinct hdA _ ih =>
    obtain ⟨hrun, hreg'⟩ :=
      ComJasminBridgeFull.cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
        gd opS step.dst step.sz step.tag step.e w s0 st0 regs0 hdst hrhs hdistinct hcorr.1
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((ArrBlockStep.base (.mixed (.assgn step))).toInstr :: arrBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (ArrBlockStep.base (.mixed (.assgn step))).toInstr prog
          = .ok (s0.withVm ((s0.evm).set step.dst.v_var (.Vword step.sz w))) := by
      rw [ArrBlockStep.toInstr, BlockStep.toInstr, MixedStep.toInstr,
        ComJasminBridgeCmd.RegStep.toInstr, execInstr, OpSemCoverage.execInstrR_Cassgn_eq]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih ⟨hreg', stateCorrArr_write_reg _ _ _ _ _ _ _ hdA hcorr.2.1, hcorr.2.2⟩
  | ror ii tag dst src sz n rest st0 s0 regs0 arrs0 w st'0 s'0 regs'0 arrs'0
        hdst hmem hread hdistinct hdA hasm _ ih =>
    obtain ⟨hrun, _, hreg'⟩ :=
      copn_ror_simulates aS opS gd prog fuel tag dst src sz n w s0 st0 regs0
        hdst hmem hread hdistinct hcorr.1 hasm
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((ArrBlockStep.base (.mixed (.ror ii tag dst src sz n))).toInstr :: arrBlockCmd rest)
          prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (ArrBlockStep.base (.mixed (.ror ii tag dst src sz n))).toInstr prog
          = .ok (s0.withVm ((s0.evm).set dst.v_var (.Vword sz (w.rotateRight n)))) := by
      rw [ArrBlockStep.toInstr, BlockStep.toInstr, MixedStep.toInstr, execInstr]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih ⟨hreg', stateCorrArr_write_reg _ _ _ _ _ _ _ hdA hcorr.2.1, hcorr.2.2⟩
  | call ii dst fn args sz r rest st0 s0 regs0 arrs0 scs' m' st'0 s'0 regs'0 arrs'0
        hdst hargs hdistinct hdA hcall hP _ ih =>
    obtain ⟨hrun, _, hreg'⟩ :=
      ccall_leaf_simulates aS opS gd prog fuel dst fn args sz r s0 st0 regs0 scs' m'
        hdst hargs hdistinct hcorr.1 hcall
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((ArrBlockStep.base (.call ii dst fn args)).toInstr :: arrBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (ArrBlockStep.base (.call ii dst fn args)).toInstr prog
          = .ok { s0 with escs := scs', emem := m', evm := (s0.evm).set dst.v_var (.Vword sz r) } := by
      rw [ArrBlockStep.toInstr, BlockStep.toInstr, execInstr]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih ⟨hreg', stateCorrArr_write_reg _ _ _ _ _ _ _ hdA hcorr.2.1, hP⟩
  | pget ii tag dst arr idx al aa ws n a i rest st0 s0 regs0 arrs0 st'0 s'0 regs'0 arrs'0
        hagree hdst hread hidx hin hdistinct hdA _ ih =>
    obtain ⟨hrun, hreg'⟩ :=
      cassgn_pget_reg_selfContained gd opS tag dst arr idx n a al aa ws i s0 st0 regs0
        hagree hdst hread hidx hin hdistinct hcorr.1
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((ArrBlockStep.pget ii tag dst arr idx al aa ws).toInstr :: arrBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (ArrBlockStep.pget ii tag dst arr idx al aa ws).toInstr prog
          = .ok (s0.withVm ((s0.evm).set dst.v_var (.Vword .U8 (a ⟨i.toNat, hin⟩)))) := by
      rw [ArrBlockStep.toInstr, execInstr, OpSemCoverage.execInstrR_Cassgn_eq]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih ⟨hreg', stateCorrArr_write_reg dst.v_var .U8 (a ⟨i.toNat, hin⟩) _ _ _ _ hdA hcorr.2.1,
      hcorr.2.2⟩
  | laset ii tag arr idx src al aa ws n a i v rest st0 s0 regs0 arrRest0 st'0 s'0 regs'0 arrs'0
        hagree harrTy hread hidx hsrc hin him hsm hdA hdR _ ih =>
    obtain ⟨hrun, _, harr', hreg'⟩ :=
      cassgn_laset_simulates gd opS arr idx src ws n a al aa i v s0 st0 arrRest0 regs0
        hagree harrTy hread hidx hsrc hin hcorr.2.1 hcorr.1 him hsm hdA hdR
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((ArrBlockStep.laset ii tag arr idx src al aa).toInstr :: arrBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (ArrBlockStep.laset ii tag arr idx src al aa).toInstr prog
          = .ok (s0.withVm ((s0.evm).set arr.v_var
              (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v)))) := by
      rw [ArrBlockStep.toInstr, execInstr, OpSemCoverage.execInstrR_Cassgn_eq]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih ⟨hreg', harr', hcorr.2.2⟩

/-- **End-to-end whole block bridge with array accesses.** Under the hypotheses
    of `arrBlock_simulates`, the emitted block witnesses the relational
    whole-command step `Sem` to `s'`, and `StateCorrMem regs' arrs' P st' s'`
    holds. -/
theorem arrBlock_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (P : Mem → Prop) (steps : List ArrBlockStep)
    (st : Store) (s : Estate SyscallState Mem) (regs arrs : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (regs' arrs' : List Var)
    (hblock : ArrBlockSim aS gd opS prog fuel P steps st s regs arrs st' s' regs' arrs')
    (hcorr : StateCorrMem regs arrs P st s) :
    Sem (Mem := Mem) aS opS gd prog s (arrBlockCmd steps) s'
    ∧ StateCorrMem regs' arrs' P st' s' := by
  obtain ⟨hrun, hcorr'⟩ :=
    arrBlock_simulates aS opS gd prog fuel P steps st s regs arrs st' s' regs' arrs' hblock hcorr
  exact ⟨execCmd_sound (n := fuel + 1) aS opS gd prog hrun, hcorr'⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrBlock
