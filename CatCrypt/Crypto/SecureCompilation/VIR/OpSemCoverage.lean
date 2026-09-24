/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.CifLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.CifLowering
public meta import CatCrypt.Crypto.SecureCompilation.VIR.WhileLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.WhileLowering
public meta import CatCrypt.Crypto.SecureCompilation.VIR.CallLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.CallLowering
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering

/-!
# Operational ASSIGN run-correctness + the `InstrR` coverage capstone

This module completes the operational-semantics layer for the Jasmin instruction
executor (`JasminCoqSemMirror`'s `execInstrR`, the mechanical Lean port of Coq
`psem.v`). It does two things:

1. **`execInstrR_Cassgn_eq`** — the run-correctness theorem for the assignment
   construct `Cassgn x tag ty e`, completing the per-constructor family of the
   three siblings (`Cif`/`Cwhile`/`Ccall`) and the counted
   `Cfor` theorem (`LoopLowering`). `Cassgn` is non-recursive, so — exactly as
   the `Ccall` theorem — one `conv_lhs => rw [execInstrR]` peeling closes it.

2. **`OpSemCoverage`** — a capstone *coverage* section that collects, by
   `example`, the run-correctness theorem for **every** `InstrR` constructor,
   making explicit that `execInstrR` has a verified run-characterisation on the
   whole instruction set. The collected theorems are not re-proved here; the
   section merely *references* the existing theorems so the coverage claim is
   machine-checked (each `example` fails to elaborate if its theorem's
   signature drifts).

## The assignment construct (what `Cassgn` denotes)

`InstrR.Cassgn (lv : Lval) (tag : AssgnTag) (ty : Atype) (e : Pexpr)` is the
single-assignment AST node (`expr.v` mirror). Its operational meaning is the
relational `SemIr.Eassgn` (`psem.v:61`) and, functionally, the `.Cassgn` branch
of `execInstrR`:

```
semPexpr … s e   -- evaluate the RHS expression
  ⤳ truncateVal (evalAtype ty)   -- truncate to the declared type `ty`
  ⤳ writeLval … lv … s            -- write the truncated value into the l-value `lv`
```

i.e. *evaluate `e`; truncate to `ty`; write into `lv`* — the executor's own
`.Cassgn` branch, with no recursion and no fuel-recursive sub-run. We factor
this as `assignExec` (matching `ifExec`/`whileExec`/`callComposition` in the
siblings) and prove the executor unfolds to it.

## `InstrR` constructor coverage

`InstrR` (`JasminCoqSemMirror.lean:436`) has **seven** constructors:

| Constructor | Run-correctness theorem | Location | Status |
|---|---|---|---|
| `Cassgn`   | `execInstrR_Cassgn_eq`            | **this file** | covered |
| `Cif`      | `CifLowering.execInstrR_Cif_eq_ite` | CifLowering | covered |
| `Cfor`     | `LoopLowering.loopN_lower_denote_iterate` | LoopLowering | covered (counted loop) |
| `Cwhile`   | `WhileLowering.execInstrR_Cwhile_eq_whileExec` | WhileLowering | covered |
| `Ccall`    | `CallLowering.execInstrR_Ccall_eq` | CallLowering | covered |
| `Copn`     | `execInstrR_Copn_eq`              | **this file** | covered (this file adds it) |
| `Csyscall` | —                                 | —          | **NOT covered** (see note) |

So **six of seven** `InstrR` constructors have a verified run-characterisation.
`Csyscall` is the lone gap, *by construction*: the executor's `.Csyscall` branch
is `.otherErr "execInstrR Csyscall: deferred to Phase C"` (the mirror's §6 note
deliberately omits syscall semantics — Coq requires a `syscall_sem` typeclass
that the port does not instantiate). The module proves the one exact statement
about it — `execInstrR_Csyscall_err`, that the emitted `Csyscall` run *is* that
deferral error.

`Cfor`'s entry is the **counted-loop** theorem (`loopN_lower_denote_iterate`:
emitted `Cfor` run = `step^[n]`), the static-count form of `LoopLowering`;
the lower-level `execInstrR`-direct `Cfor` arm runs through `execFor` (mirrored
by `JForProgSemCorrect`). We additionally give here an `execInstrR`-level
`Cfor` peel (`execInstrR_Cfor_eq`) so the coverage table has a uniform
`execInstrR`-against-its-own-branch entry for every covered constructor.

All goals are closed; no opaque-leaf hypothesis is needed for the `Cassgn`,
`Copn`, `Cfor`-peel and `Csyscall` results (the executor branches are concrete
functional definitions). The `Cfor` *counted-loop* theorem carries the same
`LeafAgrees` opaque-leaf edge as the rest of the emit-correctness theory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.OpSemCoverage

open CatCrypt.Crypto.Jasmin.CoqSemMirror

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## 1. The assignment construct's effect as an explicit composition

`assignExec` spells out *exactly* what running `Cassgn lv tag ty e` does, as a
bind chain over the mirror's own building blocks — evaluate the RHS, truncate to
the declared type, write into the l-value — factored exactly like the siblings'
`ifExec` / `whileExec` / `callComposition`. -/

/-- The explicit composition a `Cassgn lv tag ty e` run should equal: evaluate
    the RHS expression `e`, truncate the value to the declared type `ty`, and
    write it into the l-value `lv`. This is the accumulator-level "assign = eval;
    truncate; write" that the assignment construct denotes — exactly the data the
    executor's `.Cassgn` branch carries. -/
def assignExec (opS : OpSem) (gd : GlobDecls)
    (lv : Lval) (ty : Atype) (e : Pexpr) (s : Estate SyscallState Mem) :
    JResult (Estate SyscallState Mem) := do
  let v ← semPexpr (Mem := Mem) true gd opS s e
  let v' ← truncateVal (evalAtype ty) v
  writeLval (Mem := Mem) true gd opS lv v' s

/-! ## 2. Main theorem: the emitted `Cassgn` run equals the composition

`execInstrR`'s `.Cassgn` branch, at fuel `fuel'+1`, unfolds to exactly
`assignExec`. This is the run-correctness theorem for the real Jasmin `Cassgn`
construct: its functional fuel-bounded run = (eval `e`; truncate to `ty`; write
into `lv`). `Cassgn` is non-recursive, so — exactly as the `Ccall` theorem —
one `conv_lhs => rw [execInstrR]` peeling closes it. -/

/-- **Main theorem.** The emitted `Cassgn lv tag ty e` executor (at fuel `fuel'+1`,
    for *any* `tag` — assignment is fuel-insensitive past the guard and ignores
    the tag) equals the explicit composition (eval `e` → truncate to `ty` →
    write into `lv`). This is run-correctness for the real Jasmin `Cassgn`
    construct, against the executor's own `.Cassgn` branch. -/
theorem execInstrR_Cassgn_eq
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (lv : Lval) (tag : AssgnTag) (ty : Atype) (e : Pexpr) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cassgn lv tag ty e) prog
      = assignExec (Mem := Mem) opS gd lv ty e s := by
  conv_lhs => rw [execInstrR]
  rfl

/-! ## 3. The `Copn` and `Cfor` `execInstrR`-branch peels

For a uniform coverage table, we give the matching `execInstrR`-against-its-own-
branch peel for `Copn` (a primitive opcode application, run by `semSopn`) and a
`Cfor` peel (a counted iteration, run by `execFor`). Both are one-step `rw`
peels of the executor's own branch — the same non-recursive shape as `Cassgn`. -/

/-- **`Copn` run theorem.** The emitted `Copn xs tag o es` run equals the
    primitive-opcode application `semSopn … o s xs es` — the executor's own
    `.Copn` branch (`SemIr.Eopn`, `psem.v:67`). -/
theorem execInstrR_Copn_eq
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (xs : Lvals) (tag : AssgnTag) (o : Sopn) (es : Pexprs) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Copn xs tag o es) prog
      = semSopn (Mem := Mem) aS opS gd o s xs es := by
  conv_lhs => rw [execInstrR]

/-- **`Cfor` run theorem (`execInstrR`-direct).** The emitted `Cfor v r body` run
    (at fuel `fuel'+1`) equals: evaluate the range bounds (`r.lo`/`r.hi`), coerce
    to `Int`, and run `execFor` over the materialised range list — the executor's
    own `.Cfor` branch (`SemIr.Efor`, `psem.v:99`). The packaged *counted-loop*
    theorem is `LoopLowering.loopN_lower_denote_iterate` (emitted loop run =
    `step^[n]`); this is its `execInstrR`-level companion. -/
theorem execInstrR_Cfor_eq
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (v : VarI) (r : Range) (body : Cmd) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cfor v r body) prog
      = (do
          let vloV ← semPexpr (Mem := Mem) true gd opS s r.lo
          let vlo  ← vloV.toInt
          let vhiV ← semPexpr (Mem := Mem) true gd opS s r.hi
          let vhi  ← vhiV.toInt
          execFor (Mem := Mem) aS opS gd fuel' v (wrange r.dir vlo vhi) body s prog) := by
  conv_lhs => rw [execInstrR]

/-! ## 4. `Csyscall`: the deferral error

The mirror's §6 note deliberately omits syscall semantics (Coq requires a
`syscall_sem` typeclass the port does not instantiate). The executor's
`.Csyscall` branch is therefore a deferral error, and the theorem below states
exactly that. -/

/-- **`Csyscall` deferral.** The emitted `Csyscall xs o es` run (at fuel
    `fuel'+1`) is the deferral error `execInstrR Csyscall: deferred to Phase C`.
    This is the exact run-characterisation: `Csyscall` semantics are not
    modelled (the mirror omits `syscall_sem`), so the constructor's run is a
    deterministic error, not a real effect. -/
theorem execInstrR_Csyscall_err
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (xs : Lvals) (o : SyscallT) (es : Pexprs) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Csyscall xs o es) prog
      = (.otherErr "execInstrR Csyscall: deferred to Phase C" :
          JResult (Estate SyscallState Mem)) := by
  conv_lhs => rw [execInstrR]

/-! ## 5. Worked concrete `Cassgn` example: `x := y + 1`

We instantiate the executor on two integer variables `x`, `y`, with the
assignment `x := y + 1`. Started from `y = 5` (and `x` unset), the emitted
`Cassgn` writes `6` into `x`. -/

namespace AssignExample

/-- Trivial memory model (no read/write reached by this example). -/
def TrivialMem : Type := Unit

instance : MemModel TrivialMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- An `OpSem` covering the integer addition this assignment needs. -/
def addOpSem : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Oadd .Op_int, .Vint x, .Vint y => .ok (.Vint (x + y))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops needed. -/
def addAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-- The source variable `y : aint`. -/
def yVar : VarI := { v_var := { vtype := .aint, vname := "y" } }
/-- The target variable `x : aint`. -/
def xVar : VarI := { v_var := { vtype := .aint, vname := "x" } }

/-- The RHS expression `y + 1`. -/
def rhs : Pexpr :=
  .Papp2 (.Oadd .Op_int) (.Pvar (mkLvar yVar)) (.Pconst 1)

/-- The emitted assignment `x := y + 1`. -/
def assignXY : InstrR := .Cassgn (.Lvar xVar) .AT_none .aint rhs

/-- A start state with `y = n`. -/
def startState (n : Int) : Estate Unit TrivialMem :=
  { escs := (), emem := (), evm := Vm.set Vm.init yVar.v_var (.Vint n) }

/-- Read `x` out of a post-state, projected to `Option Int`. -/
def readX (s : Estate Unit TrivialMem) : Option Int :=
  match (Vm.get s.evm xVar.v_var) with
  | .Vint z => some z
  | _ => none

/-- **KAT.** Started at `y = 5`, the emitted `Cassgn` `x := y + 1` writes `6`
    into `x`. -/
theorem assignXY_kat :
    (match execInstrR (Mem := TrivialMem) addAsmSem addOpSem []
              4 (startState 5) assignXY with
     | .ok s => readX s
     | _ => none) = some 6 := by
  native_decide

/-- **Run-correctness instance.** The emitted assignment run equals the §2
    composition theorem (eval `y + 1` → truncate to `aint` → write into `x`) —
    a direct instance of `execInstrR_Cassgn_eq`. -/
theorem assignXY_emitted_eq_assignExec (n : Int) (fuel' : Nat) :
    execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] (fuel'+1)
        (startState n) assignXY
      = assignExec (Mem := TrivialMem) addOpSem []
          (.Lvar xVar) .aint rhs (startState n) :=
  execInstrR_Cassgn_eq addAsmSem addOpSem [] (.Lvar xVar) .AT_none .aint rhs
    Prog.empty fuel' (startState n)

end AssignExample

/-! ## 6. CAPSTONE: `execInstrR` run-correctness coverage over all of `InstrR`

This section *collects* the per-constructor run-correctness theorems into one
place, making the coverage claim machine-checked: each `example` below pins the
signature of an existing theorem, so the coverage table cannot silently drift.

Six of `InstrR`'s seven constructors carry a verified run-characterisation
against the real `execInstrR` executor; `Csyscall` is outside the coverage (its
run is the deferral error, captured above). -/

section Coverage

variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
  (fuel' : Nat) (s : Estate SyscallState Mem)

/-- **`Cassgn` covered** — `execInstrR_Cassgn_eq` (this file). The emitted
    assignment run = (eval; truncate; write). -/
example (lv : Lval) (tag : AssgnTag) (ty : Atype) (e : Pexpr) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cassgn lv tag ty e) prog
      = assignExec (Mem := Mem) opS gd lv ty e s :=
  execInstrR_Cassgn_eq aS opS gd lv tag ty e prog fuel' s

/-- **`Copn` covered** — `execInstrR_Copn_eq` (this file). The emitted
    primitive-op run = `semSopn`. -/
example (xs : Lvals) (tag : AssgnTag) (o : Sopn) (es : Pexprs) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Copn xs tag o es) prog
      = semSopn (Mem := Mem) aS opS gd o s xs es :=
  execInstrR_Copn_eq aS opS gd xs tag o es prog fuel' s

/-- **`Cif` covered** — `CifLowering.execInstrR_Cif_eq_ite`. The emitted branch
    run = `ite` of the two arms' runs, on a public condition. -/
example (cond : Pexpr) (cthen celse : Cmd) (b : Bool)
    (hcond : semPexpr (Mem := Mem) true gd opS s cond = .ok (.Vbool b)) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cif cond cthen celse) prog
      = (if b then execCmd (Mem := Mem) aS opS gd fuel' s cthen prog
         else execCmd (Mem := Mem) aS opS gd fuel' s celse prog) :=
  CifLowering.execInstrR_Cif_eq_ite aS opS gd cond cthen celse prog fuel' s b hcond

/-- **`Cfor` covered** — `execInstrR_Cfor_eq` (this file, `execInstrR`-direct
    peel) and `LoopLowering.loopN_lower_denote_iterate` (the packaged counted-loop
    theorem: emitted loop run = `step^[n]`). The `execInstrR`-level entry: -/
example (v : VarI) (r : Range) (body : Cmd) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cfor v r body) prog
      = (do
          let vloV ← semPexpr (Mem := Mem) true gd opS s r.lo
          let vlo  ← vloV.toInt
          let vhiV ← semPexpr (Mem := Mem) true gd opS s r.hi
          let vhi  ← vhiV.toInt
          execFor (Mem := Mem) aS opS gd fuel' v (wrange r.dir vlo vhi) body s prog) :=
  execInstrR_Cfor_eq aS opS gd v r body prog fuel' s

/-- **`Cwhile` covered** — `WhileLowering.execInstrR_Cwhile_eq_whileExec`. The
    emitted while-loop run = the condition-driven fuel-bounded iteration. -/
example (al : Align) (cond : Pexpr) (ii : InstrInfo) (body : Cmd) (fuel : Nat) :
    execInstrR (Mem := Mem) aS opS gd fuel s (.Cwhile al [] cond ii body) prog
      = WhileLowering.whileExec (Mem := Mem) aS opS gd cond body prog fuel s :=
  WhileLowering.execInstrR_Cwhile_eq_whileExec aS opS gd al cond ii body prog
    fuel s

/-- **`Ccall` covered** — `CallLowering.execInstrR_Ccall_eq`. The emitted call
    run = (eval args; run callee via `execCall`; write results). -/
example (xs : Lvals) (fn : FunName) (args : Pexprs) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Ccall xs fn args) prog
      = CallLowering.callComposition (Mem := Mem) aS opS gd xs fn args prog
          fuel' s :=
  CallLowering.execInstrR_Ccall_eq aS opS gd xs fn args prog fuel' s

/-- **`Csyscall` NOT covered** — the statement collected here is the
    deferral: the emitted `Csyscall` run is the deferral error (syscall semantics
    are not modelled — the mirror omits `syscall_sem`). This is *not* a run
    characterisation of a real effect, and is collected here to make the gap
    explicit. -/
example (xs : Lvals) (o : SyscallT) (es : Pexprs) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Csyscall xs o es) prog
      = (.otherErr "execInstrR Csyscall: deferred to Phase C" :
          JResult (Estate SyscallState Mem)) :=
  execInstrR_Csyscall_err aS opS gd xs o es prog fuel' s

end Coverage

end CatCrypt.Crypto.SecureCompilation.VIR.OpSemCoverage
