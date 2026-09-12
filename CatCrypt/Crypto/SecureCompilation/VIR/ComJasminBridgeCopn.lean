/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

/-!
# The `Com ↔ Jasmin` bridge for the register-word `Copn` arm (`rorImm`)

`JasminPrint.lowerExpr` lowers the dialect op `rorImm w n` to the one `Copn` it
emits over register words:

```
Copn [Lnone _ bool, Lnone _ bool, Lvar dst] AT_none (Oasm "ROR_w") [Pvar src, Pconst n]
```

The first two l-values discard the OF/CF flags, the third receives the rotated
word. The JasminPrint evaluator (`JasminPrintSemCorrect.execExpr`, `rorImm` arm)
reads `src` at `reg w` and stores `BitVec.rotateRight a n` at `dst`.

This file relates that instruction's run under the `psem.v` mirror
(`JasminCoqSemMirror.execInstrR`, `Copn` arm `semSopn`) to the JasminPrint store
update, in the shape of `ComJasminBridgeFull.cassgn_regArith_simulates` and
`OperandReadCorr.cassgn_regArith_selfContained`: the source operand is read
through `StateCorrReg` (`OperandReadCorr.semPexpr_pvar_vword` /
`pvar_read_corr`), and the post-states correspond after the paired write
(`StateBijection.stateCorrReg_write`).

## The asm-op semantics parameter

The mirror carries `Oasm` semantics as the parameter `AsmSem`. The bridge is
stated under `RorAsmAgrees aS sz`: on every register word `w` and immediate `n`,
`aS` returns two writable flag values followed by `Vword sz (w.rotateRight n)`.
`rorAsmSem` is a concrete `AsmSem` and `rorAsmSem_agrees` proves it satisfies
the predicate for every width.

## Contents

* `rorOpName`, `rorLvals`, `rorArgs` — the mirror image of the emitted `Copn`.
* `FlagWritable`, `writeNone_flag` — a flag value accepted by `Lnone`.
* `RorAsmAgrees`, `rorAsmSem`, `rorAsmSem_agrees` — the asm-op parameter.
* `semSopn_ror_post` — the mirror `Copn` run lands `vm.set dst (Vword (rotateRight w n))`.
* `copn_ror_simulates` — the run, the source read agreeing with the `Store`, and
  the post-state correspondence to `Store.set st dst.vname (rotateRight w n)`.
* `copn_ror_endToEnd` — the same run witnesses the relational `SemIr` step.
* `MixedStep`, `mixedBlockCmd`, `MixedBlockSim` — straight-line blocks mixing
  register-word `Cassgn`s and the rotate `Copn`; `mixedBlockSim_of_regBlockSim`
  embeds `ComJasminBridgeCmd.RegBlockSim`.
* `mixedBlock_simulates` / `mixedBlock_endToEnd` — the whole mixed command runs
  to `.ok s'`, witnesses `Sem`, and ends in `StateCorrReg` with the final `Store`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The mirror image of the emitted rotate -/

/-- The asm-op identifier `JasminPrint` emits for a width-`sz` right rotate. -/
def rorOpName (sz : WSize) : String := "ROR_" ++ toString sz.bits

/-- The three l-values of the emitted rotate: two discarded flags, then `dst`. -/
def rorLvals (dst : VarI) : Lvals := [.Lnone () .abool, .Lnone () .abool, .Lvar dst]

/-- The two arguments of the emitted rotate: the source register and the
    immediate amount. -/
def rorArgs (src : VarI) (n : Nat) : Pexprs := [.Pvar (mkLvar src), .Pconst (Int.ofNat n)]

/-! ## §2. Flag values and the asm-op parameter -/

/-- A value that `writeNone` accepts at type `bool`: truncatable to `cbool` and
    passing the `DB` definedness check. -/
def FlagWritable (f : Value) : Prop := truncatable .cbool f = true ∧ DB f = true

omit [MemModel Mem] in
/-- Writing a writable flag value into an `Lnone` l-value leaves the state unchanged. -/
theorem writeNone_flag (s : Estate SyscallState Mem) (f : Value) (hf : FlagWritable f) :
    writeNone (Mem := Mem) s .cbool f = .ok s := by
  unfold writeNone
  simp [hf.1, hf.2]

/-- `aS` implements the width-`sz` right rotate: on `[Vword sz w, Vint n]` it
    returns two writable flag values followed by `Vword sz (w.rotateRight n)`. -/
def RorAsmAgrees (aS : AsmSem) (sz : WSize) : Prop :=
  ∀ (w : BitVec sz.bits) (n : Nat), ∃ f1 f2 : Value, FlagWritable f1 ∧ FlagWritable f2 ∧
    aS.sopn_sem (.Oasm (rorOpName sz)) [.Vword sz w, .Vint (Int.ofNat n)]
      = .ok [f1, f2, .Vword sz (w.rotateRight n)]

/-- A concrete asm-op semantics for the right rotate: on `ROR_w` applied to a
    `Vword` and a non-negative `Vint`, both flags are `false` and the result is
    the rotated word; every other application is a type error. -/
def rorAsmSem : AsmSem where
  sopn_sem := fun
    | .Oasm op, [.Vword sz w, .Vint k] =>
        if op = rorOpName sz ∧ 0 ≤ k then
          .ok [.Vbool false, .Vbool false, .Vword sz (w.rotateRight k.toNat)]
        else .typeError
    | _, _ => .typeError

/-- `rorAsmSem` implements the right rotate at every width. -/
theorem rorAsmSem_agrees (sz : WSize) : RorAsmAgrees rorAsmSem sz := by
  intro w n
  refine ⟨.Vbool false, .Vbool false, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  show (if rorOpName sz = rorOpName sz ∧ (0 : Int) ≤ Int.ofNat n then
          (.ok [.Vbool false, .Vbool false, .Vword sz (w.rotateRight (Int.ofNat n).toNat)] :
            JResult Values)
        else .typeError) = _
  rw [if_pos ⟨rfl, Int.natCast_nonneg n⟩]
  rfl

/-! ## §3. The mirror `Copn` post-state -/

/-- **Mirror rotate post-state.** Under `RorAsmAgrees aS sz`, when `src` holds
    `Vword sz w` and `dst` is declared `aword sz`, the mirror `semSopn` of the
    emitted rotate lands the state whose `Vm` is
    `vm.set dst (Vword sz (w.rotateRight n))`; memory and syscall state are unchanged. -/
theorem semSopn_ror_post
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (dst src : VarI) (sz : WSize) (n : Nat) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem)
    (hdst : dst.v_var.vtype = .aword sz)
    (hread : (s.evm).get src.v_var = .Vword sz w)
    (hasm : RorAsmAgrees aS sz) :
    semSopn (Mem := Mem) aS opS gd (.Oasm (rorOpName sz)) s (rorLvals dst) (rorArgs src n)
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n)))) := by
  obtain ⟨f1, f2, hf1, hf2, hsem⟩ := hasm w n
  have hargs : semPexprs (Mem := Mem) true gd opS s (rorArgs src n)
      = .ok [.Vword sz w, .Vint (Int.ofNat n)] := by
    show (do
        let v ← semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar src))
        let vs ← semPexprList (Mem := Mem) true gd opS s [.Pconst (Int.ofNat n)]
        .ok (v :: vs)) = _
    rw [semPexpr_pvar_vword gd opS s src sz w hread]
    rfl
  unfold semSopn
  rw [hargs]
  show (do let rs ← aS.sopn_sem (.Oasm (rorOpName sz)) [.Vword sz w, .Vint (Int.ofNat n)]
           writeLvals (Mem := Mem) true gd opS s (rorLvals dst) rs) = _
  rw [hsem]
  show (do let s1 ← writeNone (Mem := Mem) s .cbool f1
           let s2 ← writeNone (Mem := Mem) s1 .cbool f2
           let s3 ← writeLval (Mem := Mem) true gd opS (.Lvar dst) (.Vword sz (w.rotateRight n)) s2
           JResult.fold2 (.otherErr "write_lvals length mismatch")
             (fun x v st => writeLval (Mem := Mem) true gd opS x v st) [] [] s3) = _
  rw [writeNone_flag s f1 hf1]
  show (do let s2 ← writeNone (Mem := Mem) s .cbool f2
           let s3 ← writeLval (Mem := Mem) true gd opS (.Lvar dst) (.Vword sz (w.rotateRight n)) s2
           JResult.fold2 (.otherErr "write_lvals length mismatch")
             (fun x v st => writeLval (Mem := Mem) true gd opS x v st) [] [] s3) = _
  rw [writeNone_flag s f2 hf2]
  show writeVar (Mem := Mem) true dst (.Vword sz (w.rotateRight n)) s >>= (fun s3 => .ok s3) = _
  unfold writeVar setVar
  rw [hdst]
  simp only [DB, Value.isDefined, truncatable, Value.typeOf,
    Bool.not_true, decide_true, Bool.true_and]
  rfl

/-! ## §4. The paired step and the end-to-end composition -/

/-- **Simulation (paired step) for the emitted rotate.** Let `dst` be a register
    of width `sz`, frame-distinct from `names`, and let the source register
    `src ∈ names` hold `Vword sz w`. If the JasminPrint `Store` `st` corresponds
    to the mirror `Vm` on `names` and `aS` implements the rotate, then:

    * the mirror `Copn` run (`execInstrR`, fuel `fuel+1`) lands
      `s.withVm (s.evm.set dst (Vword sz (w.rotateRight n)))`;
    * the JasminPrint read of `src` at `reg sz.bits` is the same `w`; and
    * the post-state corresponds (`StateCorrReg (dst :: names)`) to
      `Store.set st dst.vname (w.rotateRight n)`, the store update of the
      `rorImm` arm of `JasminPrintSemCorrect.execExpr`. -/
theorem copn_ror_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword sz)
    (hmem : src.v_var ∈ names)
    (hread : (s.evm).get src.v_var = .Vword sz w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm))
    (hasm : RorAsmAgrees aS sz) :
    execInstrR (Mem := Mem) aS opS gd (fuel + 1) s
        (.Copn (rorLvals dst) tag (.Oasm (rorOpName sz)) (rorArgs src n)) prog
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))))
    ∧ Store.get st src.v_var.vname (.reg sz.bits) = w
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) (w.rotateRight n))
        ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))) := by
  refine ⟨?_, (pvar_read_corr gd opS s st names src sz w hcorr hmem hread).2,
    stateCorrReg_write dst.v_var sz (w.rotateRight n) st s.evm names hdst hdistinct hcorr⟩
  rw [OpSemCoverage.execInstrR_Copn_eq]
  exact semSopn_ror_post aS opS gd dst src sz n w s hdst hread hasm

/-- **End-to-end bridge for the emitted rotate.** Under the hypotheses of
    `copn_ror_simulates`, the emitted `Copn` witnesses the relational Jasmin step
    `SemIr` (the port of `psem.v`'s `sem_i`) to the state
    `s.withVm (s.evm.set dst (Vword sz (w.rotateRight n)))`, and that state's `Vm`
    corresponds to `Store.set st dst.vname (w.rotateRight n)`. -/
theorem copn_ror_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword sz)
    (hmem : src.v_var ∈ names)
    (hread : (s.evm).get src.v_var = .Vword sz w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm))
    (hasm : RorAsmAgrees aS sz) :
    SemIr (Mem := Mem) aS opS gd prog s
        (.Copn (rorLvals dst) tag (.Oasm (rorOpName sz)) (rorArgs src n))
        (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) (w.rotateRight n))
        ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))) := by
  obtain ⟨hrun, _, hcorr'⟩ :=
    copn_ror_simulates aS opS gd prog 0 tag dst src sz n w s st names
      hdst hmem hread hdistinct hcorr hasm
  exact ⟨execInstrR_sound (n := 1) aS opS gd prog hrun, hcorr'⟩

/-- **The rotate bridge over the concrete asm semantics.** `copn_ror_endToEnd`
    instantiated at `rorAsmSem`, whose agreement is `rorAsmSem_agrees`: the
    remaining hypotheses concern only the states. -/
theorem copn_ror_endToEnd_rorAsmSem
    (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword sz)
    (hmem : src.v_var ∈ names)
    (hread : (s.evm).get src.v_var = .Vword sz w)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) rorAsmSem opS gd prog s
        (.Copn (rorLvals dst) tag (.Oasm (rorOpName sz)) (rorArgs src n))
        (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) (w.rotateRight n))
        ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))) :=
  copn_ror_endToEnd rorAsmSem opS gd prog tag dst src sz n w s st names
    hdst hmem hread hdistinct hcorr (rorAsmSem_agrees sz)

/-! ## §5. Whole commands mixing `Cassgn` and the rotate `Copn`

`ComJasminBridgeCmd.RegBlockSim` threads a block of register-word `Cassgn`s.
`MixedBlockSim` threads a block whose steps are either such a `Cassgn`
(`ComJasminBridgeCmd.RegStep`) or the emitted rotate `Copn`, each step's
hypotheses stated at the running state, and the tail at the post-write state. -/

open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd (RegStep RegBlockSim regBlockCmd)

/-- One step of a mixed straight-line block: a register-word `Cassgn` or the
    emitted rotate `Copn` of `src` by the immediate `n` into `dst`. -/
inductive MixedStep where
  /-- A register-word `Cassgn` step. -/
  | assgn (step : RegStep)
  /-- The rotate `Copn [_, _, dst] (Oasm ROR_sz) [src, n]`, annotated `ii`. -/
  | ror (ii : InstrInfo) (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat)

/-- The emitted `Instr` of a mixed step. -/
def MixedStep.toInstr : MixedStep → Instr
  | .assgn step => step.toInstr
  | .ror ii tag dst src sz n =>
      .MkI ii (.Copn (rorLvals dst) tag (.Oasm (rorOpName sz)) (rorArgs src n))

/-- The emitted `Cmd` of a mixed block. -/
def mixedBlockCmd (steps : List MixedStep) : Cmd :=
  steps.map MixedStep.toInstr

/-- `MixedBlockSim aS gd opS steps st s names st' s' names'`: the mixed block
    `steps`, started at JasminPrint `Store` `st`, mirror state `s` and register
    frame `names`, ends at `(st', s', names')`. A `Cassgn` step carries the
    hypotheses of `ComJasminBridgeCmd.RegBlockSim.cons`; a rotate step carries
    those of `copn_ror_simulates`, all at the running state. -/
inductive MixedBlockSim (aS : AsmSem) (gd : GlobDecls) (opS : OpSem) :
    List MixedStep → Store → Estate SyscallState Mem → List Var →
    Store → Estate SyscallState Mem → List Var → Prop where
  /-- Empty block: the state and frame are unchanged. -/
  | nil (st : Store) (s : Estate SyscallState Mem) (names : List Var) :
      MixedBlockSim aS gd opS [] st s names st s names
  /-- A register-word `Cassgn` head step followed by the tail run. -/
  | assgn
      (step : RegStep) (rest : List MixedStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (w : BitVec step.sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : step.dst.v_var.vtype = .aword step.sz)
      (hrhs : semPexpr (Mem := Mem) true gd opS s step.e = .ok (.Vword step.sz w))
      (hdistinct : ∀ r' ∈ names,
          r' ≠ step.dst.v_var ∧ r'.vname ≠ step.dst.v_var.vname)
      (htail : MixedBlockSim aS gd opS rest
          (Store.set st step.dst.v_var.vname (t := .reg step.sz.bits) w)
          (s.withVm ((s.evm).set step.dst.v_var (.Vword step.sz w)))
          (step.dst.v_var :: names)
          st' s' names') :
      MixedBlockSim aS gd opS (.assgn step :: rest) st s names st' s' names'
  /-- A rotate `Copn` head step followed by the tail run. -/
  | ror
      (ii : InstrInfo) (tag : AssgnTag) (dst src : VarI) (sz : WSize) (n : Nat)
      (rest : List MixedStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (w : BitVec sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : dst.v_var.vtype = .aword sz)
      (hmem : src.v_var ∈ names)
      (hread : (s.evm).get src.v_var = .Vword sz w)
      (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
      (hasm : RorAsmAgrees aS sz)
      (htail : MixedBlockSim aS gd opS rest
          (Store.set st dst.v_var.vname (t := .reg sz.bits) (w.rotateRight n))
          (s.withVm ((s.evm).set dst.v_var (.Vword sz (w.rotateRight n))))
          (dst.v_var :: names)
          st' s' names') :
      MixedBlockSim aS gd opS (.ror ii tag dst src sz n :: rest) st s names st' s' names'

/-- A `Cassgn`-only block is a mixed block: `RegBlockSim` embeds into
    `MixedBlockSim` along `MixedStep.assgn`, with the same emitted command. -/
theorem mixedBlockSim_of_regBlockSim
    (aS : AsmSem) (gd : GlobDecls) (opS : OpSem) (steps : List RegStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (h : RegBlockSim (SyscallState := SyscallState) (Mem := Mem)
        gd opS steps st s names st' s' names') :
    MixedBlockSim aS gd opS (steps.map MixedStep.assgn) st s names st' s' names'
    ∧ mixedBlockCmd (steps.map MixedStep.assgn) = regBlockCmd steps := by
  refine ⟨?_, ?_⟩
  · induction h with
    | nil st s names => exact .nil st s names
    | cons step rest st0 s0 names0 w st'0 s'0 names'0 hdst hrhs hdistinct _ ih =>
      exact .assgn step (rest.map MixedStep.assgn) st0 s0 names0 w st'0 s'0 names'0
        hdst hrhs hdistinct ih
  · simp only [mixedBlockCmd, regBlockCmd, List.map_map]
    rfl

/-- **Whole mixed-command simulation.** A `MixedBlockSim` chain started from a
    `StateCorrReg names`-corresponding `(st, s)` witnesses that the `execCmd` run
    of the emitted block at fuel `fuel+1` returns `.ok s'`, and that `s'`'s `Vm`
    corresponds (`StateCorrReg names'`) to the final JasminPrint `Store` `st'`.
    Each `Cassgn` step is `ComJasminBridgeFull.cassgn_regArith_simulates`, each
    rotate step is `copn_ror_simulates`. -/
theorem mixedBlock_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (steps : List MixedStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hblock : MixedBlockSim aS gd opS steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    execCmd (Mem := Mem) aS opS gd (fuel + 1) s (mixedBlockCmd steps) prog = .ok s'
    ∧ StateCorrReg names' st' s'.evm := by
  induction hblock with
  | nil st s names =>
    exact ⟨CmdRun.execCmd_nil aS opS gd (fuel + 1) s prog, hcorr⟩
  | assgn step rest st0 s0 names0 w st'0 s'0 names'0 hdst hrhs hdistinct _ ih =>
    obtain ⟨hrun, hcorr'⟩ :=
      ComJasminBridgeFull.cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
        gd opS step.dst step.sz step.tag step.e w s0 st0 names0 hdst hrhs hdistinct hcorr
    show execCmd (Mem := Mem) aS opS gd (fuel + 1) s0
        ((MixedStep.assgn step).toInstr :: mixedBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0 (MixedStep.assgn step).toInstr prog
          = .ok (s0.withVm ((s0.evm).set step.dst.v_var (.Vword step.sz w))) := by
      rw [MixedStep.toInstr, RegStep.toInstr, execInstr, OpSemCoverage.execInstrR_Cassgn_eq]
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
        ((MixedStep.ror ii tag dst src sz n).toInstr :: mixedBlockCmd rest) prog = _ ∧ _
    rw [CmdRun.execCmd_cons]
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0
            (MixedStep.ror ii tag dst src sz n).toInstr prog
          = .ok (s0.withVm ((s0.evm).set dst.v_var (.Vword sz (w.rotateRight n)))) := by
      rw [MixedStep.toInstr, execInstr]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    exact ih hcorr'

/-- **End-to-end whole mixed-command bridge.** Under the hypotheses of
    `mixedBlock_simulates`, the emitted mixed block witnesses the relational
    whole-command step `Sem` (the port of `psem.v`'s `sem`) to `s'`, and `s'`'s
    `Vm` corresponds to the final JasminPrint `Store` `st'`. -/
theorem mixedBlock_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (steps : List MixedStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hblock : MixedBlockSim aS gd opS steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    Sem (Mem := Mem) aS opS gd prog s (mixedBlockCmd steps) s'
    ∧ StateCorrReg names' st' s'.evm := by
  obtain ⟨hrun, hcorr'⟩ :=
    mixedBlock_simulates aS opS gd prog steps st s names st' s' names' fuel hblock hcorr
  exact ⟨execCmd_sound (n := fuel + 1) aS opS gd prog hrun, hcorr'⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
