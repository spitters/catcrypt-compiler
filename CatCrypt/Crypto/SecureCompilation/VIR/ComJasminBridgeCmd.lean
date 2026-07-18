/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull

/-!
# The whole straight-line command `Com ↔ Jasmin` semantic bridge

`ComJasminBridgeFull.lean` lands the **per-instruction** simulation for the
register-word `Cassgn`/`regArith` fragment (`cassgn_regArith_simulates`): one
`Cassgn (.Lvar dst) tag (.aword sz) e` step, run from a `StateCorrReg`-
corresponding Estate, lands a mirror state that *still corresponds* — to the
JasminPrint `Store.set st dst.vname w` — and additionally *witnesses* the
reference relational step `SemIr` (`cassgn_regArith_endToEnd`).

This file **lifts that per-step lemma to a whole straight-line command**: a
`Cmd` (`List Instr`) whose every instruction is a register-word `Cassgn`. It
threads the per-step `StateCorrReg`-preservation over the list via
`CmdRun.execCmd_cons` and the growing name frame, concluding that running the
*whole* command on the mirror side tracks the JasminPrint side
register-for-register, and (via `ExecAdequacy.execCmd_sound`) *witnesses* the
reference whole-command relation `Sem`.

## The list-threading shape (`RegBlockSim`)

The load-bearing design choice is *how* the per-step RHS-evaluation hypothesis
is stated. Each step's `semPexpr … = .ok (.Vword szᵢ wᵢ)` must hold **against
the running mirror state** — the state reached after the *previous* writes, not
the initial one. We capture this with an inductive predicate `RegBlockSim`
(§1) that threads the triple `(Store, Estate, frame : List Var)` step by step:
its `cons` constructor carries, for the head step, the declared-type, the
RHS-evaluates-to-`Vword`, and the frame-distinctness hypotheses *at the current
state*, and recurses on the tail at the **post-write** `(Store.set …,
s.withVm (s.evm.set …), dst :: frame)`. This is exactly the threading the
single-step `cassgn_regArith_simulates` performs, made into a list.

`RegBlockSim steps st₀ s₀ names₀ st_f s_f names_f` therefore says: "the
straight-line block `steps`, started at `(st₀, s₀)` with frame `names₀`,
denote-tracks on both sides and ends at `(st_f, s_f)` with frame `names_f`",
where each step is a register-word `Cassgn` whose RHS the mirror `OpSem`
evaluates to the matching `Vword`.

## The whole-command bridge (§2–§3)

`regBlock_simulates` (§2) is the whole-command analogue of
`cassgn_regArith_simulates`: from a `RegBlockSim` chain and an initial
`StateCorrReg names₀`, running `execCmd` of the *emitted* block (each step
`MkI ii (Cassgn (.Lvar dst) tag (.aword sz) e)`) at any fuel `fuel+1` returns
`.ok s_f`, **and** `s_f`'s `Vm` corresponds (`StateCorrReg names_f`) to the
final JasminPrint `Store` `st_f` — the composed `Store.set`s. The induction is
on the `RegBlockSim` derivation; each cons peels one `execCmd_cons`, rewrites
the head `execInstr`/`execInstrR` to `assignExec` via the per-instruction
keystone `execInstrR_Cassgn_eq`, fires `mirror_aword_assign_post` to pin the
head's `.ok` post-state, and threads the *grown* `StateCorrReg (dst :: names)`
(from `stateCorrReg_write`) into the tail IH.

`regBlock_endToEnd` (§3) chains adequacy on top: the same `.ok` whole-command
run *witnesses* the reference relational `Sem` step (via
`ExecAdequacy.execCmd_sound`), **and** the post-state corresponds — the whole
straight-line command tracks the `Com.denote`-side store sequence
register-for-register, as a `psem.v` `Sem` derivation.

## Worked example (§4)

`xyz_blockSim` / `block_endToEnd`: the 2-instruction block
`x := y + 1 ; z := x + 1` (register `u32`), started at `y = 5`, run end-to-end:
the `execCmd` run returns `.ok` of the state with `x = 6`, `z = 7`, *witnesses*
the reference `Sem` whole-command relation, and the post-state corresponds
(`StateCorrReg`) to the JasminPrint `Store.set`-sequence writing the same `6`,
`7`. The second step's RHS (`x + 1`) reads the `x` written by the *first* step
— the genuine threading the whole-command bridge captures (the second
`semPexpr` is evaluated at the post-first-write mirror state).

## What cleanly closed vs. deferred (honest)

**Closed (sorry-free):**
* `RegBlockSim` — the list-threading predicate, generic over the register-word
  `Cassgn` fragment (any per-step `sz`, `w`, `dst`, frame);
* `regBlock_simulates` — the whole straight-line command bridge: `execCmd`
  returns `.ok s_f` and `StateCorrReg names_f st_f s_f.evm`, by induction on
  the `RegBlockSim` chain (the per-step lemma threaded over the list);
* `regBlock_endToEnd` — adds adequacy: the run *witnesses* `Sem`;
* the 2-instruction worked example `block_endToEnd` (`x := y+1 ; z := x+1`),
  with the second step reading the first's write.

**Deferred (honest — the same residuals the per-step file documents):**
1. **Non-`Cassgn` instructions in the list.** `RegBlockSim` is a block of
   register-word `Cassgn`s only. A list containing `Copn`/`Cif`/`Cwhile`/
   `Cfor`/`Ccall` is out of this fragment — control-flow needs the per-step
   simulation for those constructors first (gap #1 covers only `Cassgn`).
2. **The operand-read correspondence.** Each step's RHS value is supplied as a
   hypothesis `semPexpr … = .ok (.Vword sz w)` rather than *derived* from a
   `Store`-side evaluation of the same `Papp2` operands. Threading
   `semPexpr`/`evalPExpr` value-correspondence through every expression shape
   (so the mirror `w` is forced equal to the JasminPrint binop result on
   corresponding operands) is the residual the per-step file already names.
3. **Arrays / memory / syscall state.** `RegBlockSim` tracks the register frame
   only; `Varr`/`emem`/`escs` (the genuinely byte-shaped layout) are out of the
   reg fragment, exactly as in `StateBijection`'s honest-scope note.

None of these is introduced as a `sorry` here.

0 sorries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §0. A straight-line register-word `Cassgn` step

One element of a straight-line block: the destination register `dst`, its width
`sz`, the assignment tag, and the RHS `Pexpr`. The emitted instruction is
`MkI ii (Cassgn (.Lvar dst) tag (.aword sz) e)`. -/

/-- One register-word `Cassgn` step: `dst := e` at width `sz`, tagged `tag`,
    annotated with instruction-info `ii`. -/
structure RegStep where
  /-- Instruction-info annotation (the mirror's `InstrInfo = Unit`). -/
  ii  : InstrInfo
  /-- Destination register variable. -/
  dst : VarI
  /-- Register width. -/
  sz  : WSize
  /-- Assignment tag (ignored by the run past the guard). -/
  tag : AssgnTag
  /-- RHS expression. -/
  e   : Pexpr

/-- The emitted `Instr` for one step: `MkI ii (Cassgn (.Lvar dst) tag (.aword sz) e)`. -/
def RegStep.toInstr (st : RegStep) : Instr :=
  .MkI st.ii (.Cassgn (.Lvar st.dst) st.tag (.aword st.sz) st.e)

/-- The emitted `Cmd` of a straight-line block: map each step to its `Instr`. -/
def regBlockCmd (steps : List RegStep) : Cmd :=
  steps.map RegStep.toInstr

@[simp] theorem regBlockCmd_nil : regBlockCmd [] = [] := rfl

@[simp] theorem regBlockCmd_cons (st : RegStep) (rest : List RegStep) :
    regBlockCmd (st :: rest) = st.toInstr :: regBlockCmd rest := rfl

/-! ## §1. The list-threading simulation predicate `RegBlockSim`

`RegBlockSim steps st s names st' s' names'`: the straight-line block `steps`,
started at JasminPrint `Store` `st`, mirror `Estate` `s`, register frame
`names`, denote-tracks on both sides — each step is a register-word `Cassgn`
whose mirror RHS the `OpSem` evaluates to the matching `Vword` **at the running
state**, and whose `dst` is frame-distinct — and ends at `(st', s', names')`,
the JasminPrint `Store.set` sequence / mirror `withVm`-`set` sequence / grown
frame.

The cons constructor carries the head step's hypotheses *at the current state*
(`hdst`/`hrhs`/`hdistinct`) and recurses on the tail at the **post-write**
state `(Store.set …, s.withVm (s.evm.set …), dst :: names)` — exactly the
threading the single-step `cassgn_regArith_simulates` performs. -/

inductive RegBlockSim (gd : GlobDecls) (opS : OpSem) :
    List RegStep → Store → Estate SyscallState Mem → List Var →
    Store → Estate SyscallState Mem → List Var → Prop where
  /-- Empty block: the state and frame are unchanged. -/
  | nil (st : Store) (s : Estate SyscallState Mem) (names : List Var) :
      RegBlockSim gd opS [] st s names st s names
  /-- Cons: the head register-word `Cassgn` step, with its RHS evaluating to
      `Vword sz w` *at the current state `s`* and `dst` frame-distinct, followed
      by the tail run at the post-write `(Store.set …, s.withVm (s.evm.set …),
      dst :: names)`. -/
  | cons
      (step : RegStep) (rest : List RegStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (w : BitVec step.sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : step.dst.v_var.vtype = .aword step.sz)
      (hrhs : semPexpr (Mem := Mem) true gd opS s step.e = .ok (.Vword step.sz w))
      (hdistinct : ∀ r' ∈ names,
          r' ≠ step.dst.v_var ∧ r'.vname ≠ step.dst.v_var.vname)
      (htail : RegBlockSim gd opS rest
          (Store.set st step.dst.v_var.vname (t := .reg step.sz.bits) w)
          (s.withVm ((s.evm).set step.dst.v_var (.Vword step.sz w)))
          (step.dst.v_var :: names)
          st' s' names') :
      RegBlockSim gd opS (step :: rest) st s names st' s' names'

/-! ## §2. The whole straight-line command bridge

From a `RegBlockSim` chain and an initial `StateCorrReg names`, running the
*emitted* block `regBlockCmd steps` via `execCmd` (at any fuel `fuel+1`) returns
`.ok s'`, **and** the final mirror `Vm` corresponds (`StateCorrReg names'`) to
the final JasminPrint `Store` `st'`. The whole-command lift of the per-step
`cassgn_regArith_simulates`. -/

/-- **Whole straight-line command simulation.** A `RegBlockSim` chain witnesses,
    for the emitted block `regBlockCmd steps` at fuel `fuel+1` started from a
    `StateCorrReg names`-corresponding `(st, s)`:

    * the `execCmd` run returns `.ok s'` (the whole-command mirror run succeeds
      and lands the threaded post-state `s'`); and
    * `s'`'s `Vm` corresponds (`StateCorrReg names'`) to the threaded final
      JasminPrint `Store` `st'` — the composed `Store.set`s.

    Proved by induction on the `RegBlockSim` derivation: each cons peels one
    `execCmd_cons`, rewrites the head `execInstr (MkI _ (Cassgn …))` to
    `assignExec` (via `execInstr` + `execInstrR_Cassgn_eq`), pins its `.ok`
    post-state via `mirror_aword_assign_post`, and threads the grown
    `StateCorrReg (dst :: names)` (from `stateCorrReg_write`) into the tail IH —
    register-for-register tracking of the whole command. -/
theorem regBlock_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (steps : List RegStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hblock : RegBlockSim (SyscallState := SyscallState) (Mem := Mem)
        gd opS steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    execCmd (Mem := Mem) aS opS gd (fuel + 1) s (regBlockCmd steps) prog = .ok s'
    ∧ StateCorrReg names' st' s'.evm := by
  induction hblock with
  | nil st s names =>
    -- empty block: `execCmd … [] = .ok s`, and the correspondence is unchanged.
    exact ⟨CmdRun.execCmd_nil aS opS gd (fuel + 1) s prog, hcorr⟩
  | cons step rest st0 s0 names0 w st'0 s'0 names'0
        hdst hrhs hdistinct _htail ih =>
    -- the per-step simulation: the head run lands the post-state, and the
    -- states correspond on the grown frame `dst :: names0`.
    obtain ⟨hrun, hcorr'⟩ :=
      cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
        gd opS step.dst step.sz step.tag step.e w s0 st0 names0
        hdst hrhs hdistinct hcorr
    -- peel the head of the emitted command via `execCmd_cons`.
    rw [regBlockCmd_cons, CmdRun.execCmd_cons]
    -- the head `execInstr (MkI ii (Cassgn …))` = `execInstrR (Cassgn …)`
    -- = `assignExec …` (per-instruction keystone), which `hrun` pins to `.ok`.
    have hhead :
        execInstr (Mem := Mem) aS opS gd (fuel + 1) s0 step.toInstr prog
          = .ok (s0.withVm ((s0.evm).set step.dst.v_var (.Vword step.sz w))) := by
      rw [RegStep.toInstr, execInstr, OpSemCoverage.execInstrR_Cassgn_eq]
      exact hrun
    rw [hhead]
    -- thread the grown correspondence into the tail IH; `hcorr'` is its
    -- `StateCorrReg (dst :: names0)` precondition (note `(withVm vm).evm = vm`).
    simp only [JResult.bind]
    exact ih hcorr'

/-! ## §3. The end-to-end whole-command bridge (adequacy)

Chaining `ExecAdequacy.execCmd_sound` on top of `regBlock_simulates`: the same
`.ok` whole-command run *witnesses* the reference relational whole-command step
`Sem` (the port of Coq `psem.v`'s `sem`), **and** the post-state corresponds. -/

/-- **End-to-end whole straight-line command bridge.** For a `RegBlockSim` chain
    started from a `StateCorrReg names`-corresponding `(st, s)`, at fuel
    `fuel+1`:

    * **(adequacy)** the mirror whole-command run *witnesses* the reference
      relational `Sem` step landing `s'`; and
    * **(state bijection)** `s'`'s `Vm` corresponds (`StateCorrReg names'`) to
      the final JasminPrint `Store` `st'` — the composed `Store.set`s the
      `Com.denote`/`runProg` side performs.

    Together: running the whole straight-line command on the reference Jasmin
    operational semantics reaches a state that matches, register-for-register,
    the `Com.denote`-side store sequence. The whole-command lift of
    `cassgn_regArith_endToEnd`. -/
theorem regBlock_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (steps : List RegStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hblock : RegBlockSim (SyscallState := SyscallState) (Mem := Mem)
        gd opS steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    Sem (Mem := Mem) aS opS gd prog s (regBlockCmd steps) s'
    ∧ StateCorrReg names' st' s'.evm := by
  obtain ⟨hrun, hcorr'⟩ :=
    regBlock_simulates aS opS gd prog steps st s names st' s' names' fuel hblock hcorr
  exact ⟨execCmd_sound (n := fuel + 1) aS opS gd prog hrun, hcorr'⟩

/-! ## §4. Worked multi-instruction example: `x := y + 1 ; z := x + 1`

A genuine 2-instruction straight-line block (register `u32`). The second step's
RHS `x + 1` reads the `x` *written by the first step* — the second `semPexpr` is
evaluated at the post-first-write mirror state, which is exactly the threading
`RegBlockSim` captures. Started at `y = 5`, the block produces `x = 6`, `z = 7`,
and runs end-to-end (`execCmd` `.ok` + `Sem` witnessed + state correspondence). -/

namespace BlockExample

/-- The mirror destination registers (reuse the `ComJasminBridgeFull` `x`, `y`),
    plus a fresh `z : reg u32`. -/
def zVarRM : VarI := { v_var := { vname := "z", vtype := .aword .U32 } }

/-- An `OpSem` whose `Oadd (Op_w U32)` adds `1` to the read register word — used
    for both `y + 1` and `x + 1` (constant-folding the `Pconst 1`). The register
    analogue of `OpSemCoverage.AssignExample.addOpSem`. -/
def addOpSemW : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Oadd (.Op_w .U32), .Vword .U32 a, _ => .ok (.Vword .U32 (a + 1))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- Start `Estate` holding `y = Vword U32 5`. -/
def startStateW : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set Vm.init ComJasminBridgeFull.yVarRM.v_var (.Vword .U32 (5 : BitVec 32)) }

/-- The first step `x := y + 1`. -/
def step1 : RegStep :=
  { ii := default, dst := ComJasminBridgeFull.xVarRM, sz := .U32, tag := .AT_none,
    e := .Papp2 (.Oadd (.Op_w .U32)) (.Pvar (mkLvar ComJasminBridgeFull.yVarRM)) (.Pconst 1) }

/-- The second step `z := x + 1` — reads the `x` written by `step1`. -/
def step2 : RegStep :=
  { ii := default, dst := zVarRM, sz := .U32, tag := .AT_none,
    e := .Papp2 (.Oadd (.Op_w .U32)) (.Pvar (mkLvar ComJasminBridgeFull.xVarRM)) (.Pconst 1) }

/-- The straight-line block `[x := y + 1 ; z := x + 1]`. -/
def block : List RegStep := [step1, step2]

/-- The mirror state after the first write (`x = 6`). -/
def afterStep1 : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  startStateW.withVm ((startStateW.evm).set ComJasminBridgeFull.xVarRM.v_var
    (.Vword .U32 (6 : BitVec 32)))

/-- The mirror state after both writes (`x = 6`, `z = 7`). -/
def afterStep2 : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  afterStep1.withVm ((afterStep1.evm).set zVarRM.v_var (.Vword .U32 (7 : BitVec 32)))

/-- The JasminPrint store after the first write (`x = 6`). -/
def storeAfter1 (st : Store) : Store :=
  Store.set st ComJasminBridgeFull.xVarRM.v_var.vname (t := .reg 32) (6 : BitVec 32)

/-- The JasminPrint store after both writes (`x = 6`, `z = 7`). -/
def storeAfter2 (st : Store) : Store :=
  Store.set (storeAfter1 st) zVarRM.v_var.vname (t := .reg 32) (7 : BitVec 32)

/-- `step1`'s RHS `y + 1` evaluates to `Vword U32 6` from `startStateW` (`y = 5`). -/
theorem step1_rhs_eval :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        addOpSemW startStateW step1.e = .ok (.Vword .U32 (6 : BitVec 32)) := by
  rfl

/-- `step2`'s RHS `x + 1` evaluates to `Vword U32 7` from `afterStep1` (`x = 6`)
    — the genuine threading: the second RHS reads the *first step's* write. -/
theorem step2_rhs_eval :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        addOpSemW afterStep1 step2.e = .ok (.Vword .U32 (7 : BitVec 32)) := by
  rfl

/-- **The `RegBlockSim` chain for `x := y + 1 ; z := x + 1`.** Started from any
    `Store` `st` and the initial frame `[y]`, the block threads: `step1` writes
    `x = 6` (RHS read at `startStateW`), then `step2` writes `z = 7` (RHS read at
    the post-`step1` state `afterStep1`), ending at frame `[z, x, y]`. -/
theorem xyz_blockSim (st : Store) :
    RegBlockSim (SyscallState := Unit)
        (Mem := OpSemCoverage.AssignExample.TrivialMem)
        [] addOpSemW block st startStateW [ComJasminBridgeFull.yVarRM.v_var]
        (storeAfter2 st) afterStep2
        [zVarRM.v_var, ComJasminBridgeFull.xVarRM.v_var, ComJasminBridgeFull.yVarRM.v_var] := by
  refine RegBlockSim.cons step1 [step2] st startStateW
      [ComJasminBridgeFull.yVarRM.v_var] (6 : BitVec 32) _ _ _
      (by rfl) step1_rhs_eval
      (by
        intro r' hr'
        rcases List.mem_singleton.mp hr' with h
        subst h
        exact ⟨by decide, by decide⟩)
      ?_
  -- second step, run at the post-`step1` state with frame `[x, y]`.
  refine RegBlockSim.cons step2 [] (storeAfter1 st) afterStep1
      [ComJasminBridgeFull.xVarRM.v_var, ComJasminBridgeFull.yVarRM.v_var]
      (7 : BitVec 32) _ _ _
      (by rfl) step2_rhs_eval
      (by
        intro r' hr'
        rcases List.mem_cons.mp hr' with h | h
        · subst h; exact ⟨by decide, by decide⟩
        · rcases List.mem_singleton.mp h with h; subst h
          exact ⟨by decide, by decide⟩)
      ?_
  exact RegBlockSim.nil _ _ _

/-- **Worked end-to-end whole-command bridge.** From `y = 5`, the straight-line
    block `x := y + 1 ; z := x + 1` (register `u32`), given an initial
    `StateCorrReg [y]`, runs end-to-end:

    * the mirror whole-command run *witnesses* the reference relational `Sem`
      step landing `afterStep2` (`x = 6`, `z = 7`); and
    * the post-state corresponds (`StateCorrReg [z, x, y]`) to the JasminPrint
      `Store.set`-sequence `storeAfter2 st` writing the same `6`, `7`.

    The second instruction's RHS reads the `x` the first wrote — the threading
    the whole-command bridge captures — tying the multi-instruction block
    through the full composed chain (Com → emit → translate → reference-`Sem`
    = `Com.denote`-write sequence) on the register fragment. -/
theorem block_endToEnd
    (st : Store)
    (hy : RegCorr (st ComJasminBridgeFull.yVarRM.v_var.vname)
            ((startStateW.evm).get ComJasminBridgeFull.yVarRM.v_var)) :
    Sem (Mem := OpSemCoverage.AssignExample.TrivialMem)
        OpSemCoverage.AssignExample.addAsmSem addOpSemW [] Prog.empty
        startStateW (regBlockCmd block) afterStep2
    ∧ StateCorrReg
        [zVarRM.v_var, ComJasminBridgeFull.xVarRM.v_var,
          ComJasminBridgeFull.yVarRM.v_var]
        (storeAfter2 st) afterStep2.evm := by
  have hcorr0 : StateCorrReg [ComJasminBridgeFull.yVarRM.v_var] st startStateW.evm := by
    intro r hr
    rcases List.mem_singleton.mp hr with h
    subst h; exact hy
  exact regBlock_endToEnd
    (SyscallState := Unit) (Mem := OpSemCoverage.AssignExample.TrivialMem)
    OpSemCoverage.AssignExample.addAsmSem addOpSemW [] Prog.empty
    block st startStateW [ComJasminBridgeFull.yVarRM.v_var]
    (storeAfter2 st) afterStep2
    [zVarRM.v_var, ComJasminBridgeFull.xVarRM.v_var, ComJasminBridgeFull.yVarRM.v_var]
    0 (xyz_blockSim st) hcorr0

end BlockExample

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd
