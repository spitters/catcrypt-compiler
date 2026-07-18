/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd
import CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

/-!
# The self-contained whole straight-line command `Com ↔ Jasmin` bridge

`ComJasminBridgeCmd.lean` lifts the per-step `Cassgn`/`regArith` simulation to a
*whole straight-line command* (`regBlock_simulates` / `regBlock_endToEnd`), but
its list-threading predicate `RegBlockSim` carries, for each step, the **RHS
value as a hypothesis**:

```
hrhs : semPexpr true gd opS s step.e = .ok (.Vword step.sz w)
```

i.e. the mirror RHS value `w` is *supplied*, not *computed from the corresponding
JasminPrint `Store`*. `OperandReadCorr.lean` closes that gap for *one* step
(`cassgn_regArith_selfContained`): for the genuine two-register `regArith .add`
shape `dst := a + b` (both operands read from registers), the RHS value `wa + wb`
is **derived** from `StateCorrReg` + the operand reads (`papp2_word_add_corr`),
not assumed.

This file threads that operand-read derivation through the **whole command**: a
self-contained block predicate `RegAddBlockSim` whose every step is
`dst := a + b` over two live registers — with **no** `hrhs` value hypothesis
anywhere; each step's RHS is whatever `papp2_word_add_corr` derives from the
running Store. The whole-command bridge `regAddBlock_selfContained` runs the
emitted block on the reference Jasmin operational semantics and lands a state
that still corresponds (`StateCorrReg`) to the JasminPrint `Store.set`-sequence,
**with every RHS fully derived** — a fully self-contained whole-command bridge.

## The self-contained list-threading shape (`RegAddBlockSim`)

The load-bearing change versus `RegBlockSim`: each `cons` replaces the supplied
RHS value hypothesis by the two **operand-in-register reads** at the *running*
mirror state:

```
hma  : a.v_var ∈ names                       -- the operand is a live register
hmb  : b.v_var ∈ names
hra  : (s.evm).get a.v_var = .Vword sz wa    -- read at the running state
hrb  : (s.evm).get b.v_var = .Vword sz wb
```

The RHS value `wa + wb` is then *derived* (via `papp2_word_add_corr`), not
carried. The cons recurses on the tail at the **post-write** triple `(Store.set
…, s.withVm (s.evm.set …), dst :: names)` with the grown name list — so the next
step's operand reads are stated against the state reached after this write, and a
later step may read `dst` (it is now in the frame `dst :: names`). The genuine
threading: a step's operand can be the register a *previous* step wrote.

## The self-contained whole-command bridge (§2–§3)

`regAddBlock_selfContained` (§2): from a `RegAddBlockSim` chain and an initial
`StateCorrReg names`, running `execCmd` of the emitted block (each step
`dst := Papp2 (Oadd (Op_w sz)) (Pvar a) (Pvar b)`, over `addOpSemReg sz`) at any
fuel `fuel+1` returns `.ok s'`, **and** `s'`'s `Vm` corresponds
(`StateCorrReg names'`) to the final JasminPrint `Store` — the composed
`Store.set`s. **No supplied RHS anywhere**: each per-step bridge is
`cassgn_regArith_selfContained`, which *derives* its RHS from the operand reads.
The induction is on the `RegAddBlockSim` derivation, peeling one `execCmd_cons`
per step.

`regAddBlock_endToEnd` (§3) chains adequacy: the same `.ok` whole-command run
*witnesses* the reference relational whole-command step `Sem` (via
`ExecAdequacy.execCmd_sound`).

## Worked all-derived example (§4)

`xy_addBlockSim` / `block_selfContained_endToEnd`: the 2-instruction block
`x := y + z ; w := x + y` (register `u32`), started at `y = 5`, `z = 2`. Step 1
writes `x = 7` (RHS `y + z = 5 + 2` derived from the Store); step 2 reads the
`x` *that step 1 wrote* and `y`, writing `w = x + y = 7 + 5 = 12` (RHS again
derived). Bridged end-to-end with **every RHS derived** — no value hypothesis.

## What cleanly closed vs. deferred (honest)

**Closed (sorry-free):**
* `RegAddBlockSim` — the self-contained list-threading predicate: each step is
  `dst := a + b` over two live registers, no RHS value hypothesis;
* `regAddBlock_selfContained` — the self-contained whole-command bridge:
  `execCmd` returns `.ok s'` and `StateCorrReg names' st' s'.evm`, by induction
  on the chain, reusing `cassgn_regArith_selfContained` (RHS derived) per step;
* `regAddBlock_endToEnd` — adds adequacy: the run *witnesses* `Sem`;
* the worked all-derived example `block_selfContained_endToEnd`
  (`x := y + z ; w := x + y`), where step 2 reads step 1's write `x`.

**Deferred (honest — the same residuals the per-step file documents):**
1. **Other operand shapes / ops.** This closes the two-register word-add shape
   `Papp2 (Oadd (Op_w sz)) (Pvar a) (Pvar b)` over `addOpSemReg`. Other emit
   shapes (`Papp1 (Ozeroext …)` for `castW`, `Pget` for `stackLoad`, mixed
   `Pconst`-folded immediates) need their own read-correspondences
   (`OperandReadCorr`'s honest-scope note). Other binops than `.add` need their
   `OpSem`'s analogue of `addOpSemReg_sem`.
2. **Non-`Cassgn` instructions.** A list containing `Copn`/`Cif`/`Cwhile`/
   `Cfor`/`Ccall` is out of this fragment — control-flow needs the per-step
   simulation for those constructors first.
3. **Arrays / memory / syscall state.** `RegAddBlockSim` tracks the register
   frame only; `Varr`/`emem`/`escs` are out of the reg fragment, exactly as in
   `StateBijection`'s honest-scope note.

None of these is introduced as a `sorry` here.

0 sorries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeSelfContained

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCmd
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §0. A self-contained two-register word-add step

One element of a self-contained straight-line block: a destination register
`dst`, two source registers `a`, `b`, the width `sz`, and the tag. The emitted
instruction is the genuine two-register `regArith .add`
`dst := Papp2 (Oadd (Op_w sz)) (Pvar a) (Pvar b)` — both operands read from
registers, no folded immediate. -/

/-- One self-contained register word-add step `dst := a + b` at width `sz`. -/
structure RegAddStep where
  /-- Instruction-info annotation (the mirror's `InstrInfo = Unit`). -/
  ii  : InstrInfo
  /-- Destination register variable. -/
  dst : VarI
  /-- First source register operand. -/
  a   : VarI
  /-- Second source register operand. -/
  b   : VarI
  /-- Register width. -/
  sz  : WSize
  /-- Assignment tag (ignored by the run past the guard). -/
  tag : AssgnTag

/-- The two-register word-add RHS `Papp2 (Oadd (Op_w sz)) (Pvar a) (Pvar b)`. -/
def RegAddStep.rhs (st : RegAddStep) : Pexpr :=
  .Papp2 (.Oadd (.Op_w st.sz)) (.Pvar (mkLvar st.a)) (.Pvar (mkLvar st.b))

/-- The emitted `Instr` for one step:
    `MkI ii (Cassgn (.Lvar dst) tag (.aword sz) (a + b))`. -/
def RegAddStep.toInstr (st : RegAddStep) : Instr :=
  .MkI st.ii (.Cassgn (.Lvar st.dst) st.tag (.aword st.sz) st.rhs)

/-- The emitted `Cmd` of a self-contained add-block: map each step to its `Instr`. -/
def regAddBlockCmd (steps : List RegAddStep) : Cmd :=
  steps.map RegAddStep.toInstr

@[simp] theorem regAddBlockCmd_nil : regAddBlockCmd [] = [] := rfl

@[simp] theorem regAddBlockCmd_cons (st : RegAddStep) (rest : List RegAddStep) :
    regAddBlockCmd (st :: rest) = st.toInstr :: regAddBlockCmd rest := rfl

/-! ## §1. The self-contained list-threading predicate `RegAddBlockSim`

`RegAddBlockSim steps st s names st' s' names'`: the self-contained add-block
`steps`, started at JasminPrint `Store` `st`, mirror `Estate` `s`, register
frame `names`, denote-tracks on both sides — each step is `dst := a + b` whose
operands `a, b` are **live registers** (`∈ names`) read at the *running* state,
**with no RHS value hypothesis** — and ends at `(st', s', names')`, the
JasminPrint `Store.set` sequence / mirror `withVm`-`set` sequence / grown frame.

The cons constructor carries the head step's *operand reads* `hra`/`hrb` at the
current state `s`, the membership `hma`/`hmb`, the declared-type `hdst`, and
frame-distinctness `hdistinct`, and recurses on the tail at the **post-write**
`(Store.set …, s.withVm (s.evm.set …), dst :: names)`. The RHS value `wa + wb`
is *derived* (via `papp2_word_add_corr`), never carried. -/

inductive RegAddBlockSim (gd : GlobDecls) :
    List RegAddStep → Store → Estate SyscallState Mem → List Var →
    Store → Estate SyscallState Mem → List Var → Prop where
  /-- Empty block: the state and frame are unchanged. -/
  | nil (st : Store) (s : Estate SyscallState Mem) (names : List Var) :
      RegAddBlockSim gd [] st s names st s names
  /-- Cons: the head word-add step `dst := a + b`, with both operands `a, b`
      **live registers** read at the current state `s` to `Vword sz wa`,
      `Vword sz wb` (no RHS value hypothesis — the RHS is derived), `dst`
      register-typed and frame-distinct, followed by the tail run at the
      post-write `(Store.set …, s.withVm (s.evm.set …), dst :: names)` — the
      grown frame so a later step may read `dst`. -/
  | cons
      (step : RegAddStep) (rest : List RegAddStep)
      (st : Store) (s : Estate SyscallState Mem) (names : List Var)
      (wa wb : BitVec step.sz.bits)
      (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
      (hdst : step.dst.v_var.vtype = .aword step.sz)
      (hma : step.a.v_var ∈ names)
      (hmb : step.b.v_var ∈ names)
      (hra : (s.evm).get step.a.v_var = .Vword step.sz wa)
      (hrb : (s.evm).get step.b.v_var = .Vword step.sz wb)
      (hdistinct : ∀ r' ∈ names,
          r' ≠ step.dst.v_var ∧ r'.vname ≠ step.dst.v_var.vname)
      (htail : RegAddBlockSim gd rest
          (Store.set st step.dst.v_var.vname (t := .reg step.sz.bits) (wa + wb))
          (s.withVm ((s.evm).set step.dst.v_var (.Vword step.sz (wa + wb))))
          (step.dst.v_var :: names)
          st' s' names') :
      RegAddBlockSim gd (step :: rest) st s names st' s' names'

/-! ## §2. The self-contained whole straight-line command bridge

From a `RegAddBlockSim` chain and an initial `StateCorrReg names`, running the
*emitted* block `regAddBlockCmd steps` via `execCmd` (at any fuel `fuel+1`)
returns `.ok s'`, **and** the final mirror `Vm` corresponds
(`StateCorrReg names'`) to the final JasminPrint `Store`. The whole-command lift
of the per-step `cassgn_regArith_selfContained` — every RHS *derived*. -/

/-- **Self-contained whole straight-line command simulation (every RHS derived).**
    A `RegAddBlockSim` chain witnesses, for the emitted block `regAddBlockCmd
    steps` over `addOpSemReg` at fuel `fuel+1` started from a `StateCorrReg
    names`-corresponding `(st, s)`:

    * the `execCmd` run returns `.ok s'`; and
    * `s'`'s `Vm` corresponds (`StateCorrReg names'`) to the final JasminPrint
      `Store` `st'` — the composed `Store.set`s.

    **No supplied RHS anywhere.** Each per-step bridge is
    `cassgn_regArith_selfContained`, which *derives* its RHS value `wa + wb` from
    the running operand reads (`papp2_word_add_corr`) rather than taking it as a
    hypothesis. Proved by induction on the `RegAddBlockSim` derivation: each cons
    peels one `execCmd_cons`, derives-and-runs the head step, and threads the
    grown `StateCorrReg (dst :: names)` into the tail IH. -/
theorem regAddBlock_selfContained
    (aS : AsmSem) (gd : GlobDecls) (prog : Prog)
    (sz : WSize)
    (steps : List RegAddStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hsz : ∀ step ∈ steps, step.sz = sz)
    (hblock : RegAddBlockSim (SyscallState := SyscallState) (Mem := Mem)
        gd steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    execCmd (Mem := Mem) aS (addOpSemReg sz) gd (fuel + 1) s
        (regAddBlockCmd steps) prog = .ok s'
    ∧ StateCorrReg names' st' s'.evm := by
  induction hblock with
  | nil st s names =>
    -- empty block: `execCmd … [] = .ok s`, the correspondence is unchanged.
    exact ⟨CmdRun.execCmd_nil aS (addOpSemReg sz) gd (fuel + 1) s prog, hcorr⟩
  | cons step rest st0 s0 names0 wa wb st'0 s'0 names'0
        hdst hma hmb hra hrb hdistinct htail ih =>
    -- this step's width is `sz` (every step in the block has width `sz`).
    have hstepsz : step.sz = sz := hsz step List.mem_cons_self
    -- the tail's steps also all have width `sz`.
    have hsz' : ∀ s ∈ rest, s.sz = sz := fun s hs =>
      hsz s (List.mem_cons_of_mem _ hs)
    -- transport the per-step data along `step.sz = sz` so it speaks `addOpSemReg sz`.
    subst hstepsz
    -- the self-contained per-step bridge: derive the RHS `wa + wb`, run the head,
    -- and obtain the grown correspondence on `dst :: names0`.
    obtain ⟨hrun, hcorr'⟩ :=
      cassgn_regArith_selfContained (SyscallState := SyscallState) (Mem := Mem)
        gd step.tag step.dst step.a step.b step.sz s0 st0 names0 wa wb
        hdst hma hmb hra hrb hdistinct hcorr
    -- peel the head of the emitted command via `execCmd_cons`.
    rw [regAddBlockCmd_cons, CmdRun.execCmd_cons]
    -- the head `execInstr (MkI ii (Cassgn …))` = `execInstrR (Cassgn …)`
    -- = `assignExec …` (per-instruction keystone), which `hrun` pins to `.ok`.
    have hhead :
        execInstr (Mem := Mem) aS (addOpSemReg step.sz) gd (fuel + 1) s0
            step.toInstr prog
          = .ok (s0.withVm ((s0.evm).set step.dst.v_var
              (.Vword step.sz (wa + wb)))) := by
      rw [RegAddStep.toInstr, RegAddStep.rhs, execInstr,
        OpSemCoverage.execInstrR_Cassgn_eq]
      exact hrun
    rw [hhead]
    simp only [JResult.bind]
    -- thread the grown correspondence into the tail IH.
    exact ih hsz' hcorr'

/-! ## §3. The self-contained end-to-end whole-command bridge (adequacy)

Chaining `ExecAdequacy.execCmd_sound` on top of `regAddBlock_selfContained`: the
same `.ok` whole-command run *witnesses* the reference relational whole-command
step `Sem`, **and** the post-state corresponds — every RHS still derived. -/

/-- **Self-contained end-to-end whole straight-line command bridge.** For a
    `RegAddBlockSim` chain started from a `StateCorrReg names`-corresponding
    `(st, s)`, at fuel `fuel+1`:

    * **(adequacy)** the mirror whole-command run *witnesses* the reference
      relational `Sem` step landing `s'`; and
    * **(state bijection)** `s'`'s `Vm` corresponds (`StateCorrReg names'`) to
      the final JasminPrint `Store` `st'`.

    Every per-step RHS is *derived* from the running operand reads — no RHS value
    hypothesis anywhere. The self-contained whole-command lift of
    `cassgn_regArith_selfContained`. -/
theorem regAddBlock_endToEnd
    (aS : AsmSem) (gd : GlobDecls) (prog : Prog)
    (sz : WSize)
    (steps : List RegAddStep)
    (st : Store) (s : Estate SyscallState Mem) (names : List Var)
    (st' : Store) (s' : Estate SyscallState Mem) (names' : List Var)
    (fuel : Nat)
    (hsz : ∀ step ∈ steps, step.sz = sz)
    (hblock : RegAddBlockSim (SyscallState := SyscallState) (Mem := Mem)
        gd steps st s names st' s' names')
    (hcorr : StateCorrReg names st s.evm) :
    Sem (Mem := Mem) aS (addOpSemReg sz) gd prog s (regAddBlockCmd steps) s'
    ∧ StateCorrReg names' st' s'.evm := by
  obtain ⟨hrun, hcorr'⟩ :=
    regAddBlock_selfContained aS gd prog sz steps st s names st' s' names' fuel
      hsz hblock hcorr
  exact ⟨execCmd_sound (n := fuel + 1) aS (addOpSemReg sz) gd prog hrun, hcorr'⟩

/-! ## §4. Worked all-derived example: `x := y + z ; w := x + y`

A genuine 2-instruction self-contained block (register `u32`). Step 1's RHS
`y + z` is derived from the Store (`y = 5`, `z = 2`, giving `x = 7`). Step 2
reads the `x` *written by step 1* and `y`, deriving `w = x + y = 7 + 5 = 12`.
Both operands of both steps are live registers, and **every RHS is derived** —
no value hypothesis. Started at `y = 5`, `z = 2`, the block runs end-to-end. -/

namespace AddBlockExample

/-- `x : reg u32` (the destination of step 1; the operand of step 2). -/
def xVar : VarI := { v_var := { vname := "x", vtype := .aword .U32 } }
/-- `y : reg u32`. -/
def yVar : VarI := { v_var := { vname := "y", vtype := .aword .U32 } }
/-- `z : reg u32`. -/
def zVar : VarI := { v_var := { vname := "z", vtype := .aword .U32 } }
/-- `w : reg u32` (the destination of step 2). -/
def wVar : VarI := { v_var := { vname := "w", vtype := .aword .U32 } }

/-- Start `Estate` holding `y = Vword U32 5`, `z = Vword U32 2`. -/
def startState : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)))
              zVar.v_var (.Vword .U32 (2 : BitVec 32)) }

/-- Step 1: `x := y + z`. -/
def step1 : RegAddStep :=
  { ii := default, dst := xVar, a := yVar, b := zVar, sz := .U32, tag := .AT_none }

/-- Step 2: `w := x + y` — reads the `x` written by `step1`. -/
def step2 : RegAddStep :=
  { ii := default, dst := wVar, a := xVar, b := yVar, sz := .U32, tag := .AT_none }

/-- The self-contained block `[x := y + z ; w := x + y]`. -/
def block : List RegAddStep := [step1, step2]

/-- Every step in the block is at width `U32`. -/
theorem block_sz : ∀ step ∈ block, step.sz = .U32 := by
  intro step hstep
  rcases List.mem_cons.mp hstep with h | h
  · subst h; rfl
  · rcases List.mem_singleton.mp h with h; subst h; rfl

/-- The mirror state after step 1 (`x = 7`). -/
def afterStep1 : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  startState.withVm ((startState.evm).set xVar.v_var (.Vword .U32 (7 : BitVec 32)))

/-- The mirror state after step 2 (`x = 7`, `w = 12`). -/
def afterStep2 : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  afterStep1.withVm ((afterStep1.evm).set wVar.v_var (.Vword .U32 (12 : BitVec 32)))

/-- The JasminPrint store after step 1 (`x = 7`). -/
def storeAfter1 (st : Store) : Store :=
  Store.set st xVar.v_var.vname (t := .reg 32) (7 : BitVec 32)

/-- The JasminPrint store after step 2 (`x = 7`, `w = 12`). -/
def storeAfter2 (st : Store) : Store :=
  Store.set (storeAfter1 st) wVar.v_var.vname (t := .reg 32) (12 : BitVec 32)

/-- `startState` holds `y = Vword U32 5`. -/
theorem startState_y :
    (startState.evm).get yVar.v_var = .Vword .U32 (5 : BitVec 32) := by
  show (Vm.set (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)))
          zVar.v_var (.Vword .U32 (2 : BitVec 32))).get yVar.v_var = _
  simp [Vm.get, Vm.set]; decide

/-- `startState` holds `z = Vword U32 2`. -/
theorem startState_z :
    (startState.evm).get zVar.v_var = .Vword .U32 (2 : BitVec 32) := by
  show (Vm.set (Vm.set Vm.init yVar.v_var (.Vword .U32 (5 : BitVec 32)))
          zVar.v_var (.Vword .U32 (2 : BitVec 32))).get zVar.v_var = _
  simp [Vm.get, Vm.set]

/-- After step 1 (`x = 7`), the operand `x` of step 2 is the live register `7`
    — the genuine threading: step 2 reads the *register step 1 wrote*. -/
theorem afterStep1_x :
    (afterStep1.evm).get xVar.v_var = .Vword .U32 (7 : BitVec 32) := by
  show ((startState.evm).set xVar.v_var (.Vword .U32 (7 : BitVec 32))).get
        xVar.v_var = _
  simp [Vm.get, Vm.set]

/-- After step 1, `y` is still the live register `5` (the write to `x` left `y`). -/
theorem afterStep1_y :
    (afterStep1.evm).get yVar.v_var = .Vword .U32 (5 : BitVec 32) := by
  show ((startState.evm).set xVar.v_var (.Vword .U32 (7 : BitVec 32))).get
        yVar.v_var = _
  rw [show ((startState.evm).set xVar.v_var (.Vword .U32 (7 : BitVec 32))).get
        yVar.v_var = (startState.evm).get yVar.v_var from by
        simp [Vm.get, Vm.set]; decide]
  exact startState_y

/-- **The `RegAddBlockSim` chain for `x := y + z ; w := x + y`, every RHS
    derived.** Started from any `Store` `st` and the initial frame `[y, z]`, the
    block threads: step 1 derives `x = y + z = 7` (operands `y`, `z` read at
    `startState`), then step 2 derives `w = x + y = 12` (operand `x` read at the
    post-step-1 state `afterStep1` — the register step 1 wrote — and `y`). Ends at
    frame `[w, x, y, z]`. No RHS value hypothesis anywhere. -/
theorem xy_addBlockSim (st : Store) :
    RegAddBlockSim (SyscallState := Unit)
        (Mem := OpSemCoverage.AssignExample.TrivialMem)
        [] block st startState [yVar.v_var, zVar.v_var]
        (storeAfter2 st) afterStep2
        [wVar.v_var, xVar.v_var, yVar.v_var, zVar.v_var] := by
  -- step 1: `x := y + z`, operands `y, z ∈ [y, z]`, read `5`, `2` at `startState`.
  refine RegAddBlockSim.cons step1 [step2] st startState
      [yVar.v_var, zVar.v_var] (5 : BitVec 32) (2 : BitVec 32) _ _ _
      (by rfl) (by decide) (by decide) startState_y startState_z
      (by
        intro r' hr'
        rcases List.mem_cons.mp hr' with h | h
        · subst h; exact ⟨by decide, by decide⟩
        · rcases List.mem_singleton.mp h with h; subst h
          exact ⟨by decide, by decide⟩)
      ?_
  -- step 2: `w := x + y`, run at the post-step-1 state, frame `[x, y, z]`.
  -- operand `x` is the register step 1 wrote (`7`); `y` is still `5`.
  refine RegAddBlockSim.cons step2 [] (storeAfter1 st) afterStep1
      [xVar.v_var, yVar.v_var, zVar.v_var] (7 : BitVec 32) (5 : BitVec 32) _ _ _
      (by rfl) (by decide) (by decide) afterStep1_x afterStep1_y
      (by
        intro r' hr'
        rcases List.mem_cons.mp hr' with h | h
        · subst h; exact ⟨by decide, by decide⟩
        · rcases List.mem_cons.mp h with h | h
          · subst h; exact ⟨by decide, by decide⟩
          · rcases List.mem_singleton.mp h with h; subst h
            exact ⟨by decide, by decide⟩)
      ?_
  exact RegAddBlockSim.nil _ _ _

/-- **Worked self-contained end-to-end whole-command bridge.** From `y = 5`,
    `z = 2`, the self-contained block `x := y + z ; w := x + y` (register `u32`),
    given an initial `StateCorrReg [y, z]`, runs end-to-end:

    * the mirror whole-command run *witnesses* the reference relational `Sem`
      step landing `afterStep2` (`x = 7`, `w = 12`); and
    * the post-state corresponds (`StateCorrReg [w, x, y, z]`) to the JasminPrint
      `Store.set`-sequence `storeAfter2 st` writing the same `7`, `12`.

    Every RHS is *derived* from the running Store: step 1's `y + z` and — the
    genuine threading — step 2's `x + y`, where `x` is the register step 1 wrote.
    There is **no supplied RHS value hypothesis** anywhere; the whole block
    bridges to the reference Jasmin semantics fully self-contained. -/
theorem block_selfContained_endToEnd
    (st : Store)
    (hcorr : StateCorrReg [yVar.v_var, zVar.v_var] st startState.evm) :
    Sem (Mem := OpSemCoverage.AssignExample.TrivialMem)
        OpSemCoverage.AssignExample.addAsmSem (addOpSemReg .U32) [] Prog.empty
        startState (regAddBlockCmd block) afterStep2
    ∧ StateCorrReg
        [wVar.v_var, xVar.v_var, yVar.v_var, zVar.v_var]
        (storeAfter2 st) afterStep2.evm := by
  exact regAddBlock_endToEnd
    (SyscallState := Unit) (Mem := OpSemCoverage.AssignExample.TrivialMem)
    OpSemCoverage.AssignExample.addAsmSem [] Prog.empty .U32
    block st startState [yVar.v_var, zVar.v_var]
    (storeAfter2 st) afterStep2
    [wVar.v_var, xVar.v_var, yVar.v_var, zVar.v_var]
    0 block_sz (xy_addBlockSim st) hcorr

end AddBlockExample

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeSelfContained
