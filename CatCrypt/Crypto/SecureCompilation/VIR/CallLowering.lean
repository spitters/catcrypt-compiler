/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror

/-!
# Operational CALL run-correctness: emitted `Ccall` run = running the callee

The linker theorem (`X86Backend/LinkerReloc.lean`) proves the *byte-level*
half of "a call is correct": the relocated `call rel32` displacement lands
**exactly on the callee's `.text` address**. Its own scope note is explicit
that the **operational** half is missing:

> *No executed-call semantics. … Property #1 of the task (linked-run = callee
> composed) is NOT here … no operational step relation for `call`/`ret`.*

This file closes that operational half against the **real** Jasmin call
semantics — the mechanical Coq port in `JasminCoqSemMirror` — and so the two
files together say: the emitted call *targets* the right function (LinkerReloc)
AND *running* it equals running the callee (here).

## What substrate we reuse (a *real* `Ccall` run-semantics already exists)

We do **not** invent a call model. `JasminCoqSemMirror` is the line-by-line
Lean port of Jasmin's Coq `psem.v`, and it carries the Jasmin
call construct:

* `InstrR.Ccall (xs) (fn) (es)` — the AST node (`expr.v:412` mirror): the
  result l-values `xs`, the callee name `fn`, the argument expressions `es`.
* The **relational** operational semantics `SemIr.Ecall` (`psem.v:105`):
  evaluate args (`semPexprs`), run the callee via the `SemCall` judgement
  (`SemCall.EcallRun`, `psem.v:122`: look `fn` up in the program, truncate
  args against `tyin`, bind them into the callee's fresh `Vm.init`, run the
  body with `Sem`, read returns via `getVarIs`, truncate against `tyout`),
  then write the returns into the caller's `xs` (`writeLvals`).
* The **functional** fuel-bounded executor `execInstrR`'s `.Ccall` branch
  (`JasminCoqSemMirror.lean`), which drives the same judgement and delegates
  the callee run to `execCall` (which mirrors `SemCall.EcallRun`). This is the
  branch the demo `Examples/JasminCoqSemMirrorDemo.lean` Example 7 smoke-tests
  (a 2-function program `main () { y := add1(5) }` with `add1 (in) { ret := in+1 }`).

So this is the run-correctness theorem for the **existing** `Ccall` executor:
its functional fuel-bounded run = (evaluate args → run the callee `fn`'s body
→ write the results), where the callee run is `execCall` (= `SemCall`).

## What this module adds

1. **`execInstrR_Ccall_eq`** — the main theorem: for any fuel `fuel'+1`, the emitted
   `Ccall xs fn args` run **equals** the explicit composition
   `bind (semPexprs args) (fun vargs => bind (execCall … fn vargs prog) (fun r =>
   writeLvals … r.vres))` — i.e. the call's effect *is* (eval args; run callee;
   write results). Proved by unfolding `execInstrR`'s `.Ccall` arm (the
   `WhileLowering` peeling technique: `conv_lhs => rw [execInstrR]`).

2. **`execInstrR_Ccall_eq_run_callee`** — the *linked-composition* corollary,
   in the regime that LinkerReloc cares about (a program where `fn` is defined):
   the call run **substitutes in the callee's own body run**. When `getFunDef
   prog fn = some f`, the call reduces to: bind args, truncate them against
   `f.tyin`, bind them into `Vm.init`, **run `f.body` via `execCmd`** (the
   callee's own semantics), read `f.rets`, truncate, write into `xs`. The
   `execCmd f.body` occurrence is literally the callee being run — this is the
   semantic "linked-run = callee composed in".

3. A **worked example** mirroring the demo's 2-function construction
   (`add1`/`main`): the caller's `Ccall` run on `[Pconst 5]` equals running the
   callee body `ret := in + 1` on the bound argument, yielding `y = 6`
   (`callAdd1_emitted_kat`, by `native_decide`); and that emitted run equals the
   composition theorem (`callAdd1_emitted_eq_composition`). All goals closed.

## Scope (honest)

* **Abstract arg-binding, not ABI marshalling.** The callee receives its
  arguments via `writeVars` into a fresh `Vm.init` (the abstract Jasmin
  pre-allocation calling convention). The *concrete* ABI — registers/stack
  slots, `init_state`/`finalize` stack-frame hooks — is **not** modelled here;
  `JasminCoqSemMirror` deliberately omits `extra_*_t` (its §6 header note). So
  this is the *pre-allocation* call semantics, the layer above the byte ABI that
  LinkerReloc lives in. Tying the two requires the register-allocation/ABI
  bridge (Phase B/regalloc), which is a separate seam.
* **Single non-recursive call, fuel-bounded.** The functional executor is
  fuel-bounded; one `Ccall` consumes one fuel level for the callee. Recursive or
  mutually-recursive calls run under the same `execCall`/`execCmd` recursion and
  are covered *operationally* (they just need enough fuel), but we do not here
  prove a fuel-independent / relational (`SemCall`) statement, nor a termination
  measure discharging "the executor's fuel suffices". That is the same residual
  `WhileLowering` notes for `Cwhile`.

All goals are closed; no opaque-leaf hypothesis is needed (the executor and the
composition target are both concrete functional definitions).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CallLowering

open CatCrypt.Crypto.Jasmin.CoqSemMirror

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## 1. The call's effect as an explicit composition

`callComposition` spells out *exactly* what running a `Ccall xs fn args` should
do, as a bind chain over the mirror's own building blocks:

* `semPexprs … args` — evaluate the argument expressions;
* `execCall … fn vargs prog` — **run the callee** `fn` (this is the mirror's
  `SemCall.EcallRun` driver: lookup, arg-bind, run body, read returns);
* `writeLvals … r xs vres` — write the returns into the caller's result l-values.

This is the accumulator-level "the call = eval args; run callee; write results"
that the call construct denotes. -/

/-- The explicit composition a `Ccall xs fn args` run should equal: evaluate the
    arguments, run the callee via `execCall`, then write the returned values into
    the caller's result l-values `xs`. -/
def callComposition (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (xs : Lvals) (fn : FunName) (args : Pexprs) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    JResult (Estate SyscallState Mem) := do
  let vargs ← semPexprs (Mem := Mem) true gd opS s args
  let (escs2, emem2, vres) ← execCall (Mem := Mem) aS opS gd fuel' s.escs s.emem fn vargs prog
  writeLvals (Mem := Mem) true gd opS
    ({ s with escs := escs2, emem := emem2 }) xs vres

/-! ## 2. Main theorem: the emitted `Ccall` run equals the composition

`execInstrR`'s `.Ccall` branch, at fuel `fuel'+1`, unfolds to exactly
`callComposition` at fuel `fuel'`. This is the run-correctness theorem for the
real Jasmin `Ccall` construct: its functional fuel-bounded run = (eval args; run
callee; write results). -/

/-- **Call run-correctness.** The emitted `Ccall xs fn args` executor (at fuel `fuel'+1`)
    equals the explicit composition (eval args → run callee `fn` via `execCall` →
    write results). This is run-correctness for the real Jasmin `Ccall`
    construct: the call's effect equals running the callee. -/
theorem execInstrR_Ccall_eq
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (xs : Lvals) (fn : FunName) (args : Pexprs) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Ccall xs fn args) prog
      = callComposition (Mem := Mem) aS opS gd xs fn args prog fuel' s := by
  conv_lhs => rw [execInstrR]
  rfl

/-! ## 3. Linked-composition corollary: the callee's body run is substituted in

In the regime LinkerReloc cares about — a program where `fn` is *defined* (so the
linker has a real callee, not an external relocation) — the call run substitutes
in the callee's own body run. Unfolding `execCall` past the `getFunDef = some f`
lookup exposes the literal `execCmd … f.body …`: that occurrence is the callee
being run. -/

/-- `linkedCall` is the call run with the callee's body **explicitly inlined**:
    look `fn` up (assumed `some f`), bind the truncated args into a fresh
    `Vm.init`, **run `f.body` via `execCmd`** (the callee's own semantics), read
    the returns, truncate, write into the caller's `xs`. The `execCmd f.body`
    occurrence is the callee composed in. -/
def linkedCall (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (xs : Lvals) (args : Pexprs) (f : FunDef) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    JResult (Estate SyscallState Mem) := do
  let vargs ← semPexprs (Mem := Mem) true gd opS s args
  -- the callee's own run, exactly as `execCall` packages it (mirrors
  -- `SemCall.EcallRun`): truncate args → bind into fresh `Vm.init` →
  -- run `f.body` via `execCmd` (the callee composed in) → read+truncate returns.
  let triple ← (do
    let cargs ← JResult.mapM
      (fun p => truncateVal (evalAtype p.fst) p.snd) (f.tyin.zip vargs)
    let s1 ← writeVars (Mem := Mem) true f.params cargs
      ({ escs := s.escs, emem := s.emem, evm := Vm.init } : Estate SyscallState Mem)
    let s2 ← execCmd (Mem := Mem) aS opS gd fuel' s1 f.body prog
    let vres ← getVarIs true s2.evm f.rets
    let vres' ← JResult.mapM
      (fun p => truncateVal (evalAtype p.fst) p.snd) (f.tyout.zip vres)
    .ok (s2.escs, s2.emem, vres'))
  writeLvals (Mem := Mem) true gd opS
    ({ s with escs := triple.fst, emem := triple.2.fst }) xs triple.2.snd

/-- **Linked-composition corollary.** When `fn` is defined in `prog`
    (`getFunDef prog fn = some f` — the intra-object case LinkerReloc's
    displacement lands in), the emitted `Ccall` run equals `linkedCall`, in which
    the callee's body run (`execCmd … f.body …`) is literally substituted in.
    This is the *semantic* "linked-run = callee composed in" complementing
    LinkerReloc's *byte-level* "the call targets the callee".

    The fuel is `fuel'+2`: one level for the call instruction, one for the call
    frame (`execCall`); the callee body then runs with `fuel'`. -/
theorem execInstrR_Ccall_eq_run_callee
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (xs : Lvals) (fn : FunName) (args : Pexprs) (prog : Prog)
    (f : FunDef) (hf : getFunDef prog fn = some f)
    (fuel' : Nat) (s : Estate SyscallState Mem) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+2) s (.Ccall xs fn args) prog
      = linkedCall (Mem := Mem) aS opS gd xs args f prog fuel' s := by
  rw [execInstrR_Ccall_eq]
  unfold callComposition linkedCall
  -- Peel the shared `semPexprs args` bind; then unfold `execCall` past the
  -- `getFunDef = some f` lookup. `linkedCall` is shaped to match `execCall`'s
  -- own triple-producing block exactly, so the two sides coincide on the nose.
  cases hargs : semPexprs (Mem := Mem) true gd opS s args with
  | ok vargs => simp only [execCall, hf]
  | typeError => rfl
  | undefError => rfl
  | addrUndef => rfl
  | otherErr m => rfl

/-! ## 4. Worked concrete example: a 2-function program (caller `Ccall`s callee)

We mirror the demo's 2-function construction
(`Examples/JasminCoqSemMirrorDemo.lean` Example 7):

* callee `add1 (in : aint) -> aint { ret := in + 1; return ret }`,
* caller `main () { y := add1(5) }`.

The caller's `Ccall` run on `[Pconst 5]`:

* drives `y` to `6` (`callAdd1_emitted_kat`, by `native_decide`) — the call's
  effect *is* running the callee body `ret := in + 1` on the bound argument;
* equals the §2 composition (`callAdd1_emitted_eq_composition`);
* equals the §3 linked-callee form with `add1`'s body substituted in
  (`callAdd1_emitted_eq_linked`).

This exhibits the full chain "emitted call run = (eval args; run callee; write
results) = the callee's body run composed in". -/

namespace Add1Example

/-- Trivial memory model (no read/write reached by this example). -/
def TrivialMem : Type := Unit

instance : MemModel TrivialMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- An `OpSem` covering the integer addition this example needs. -/
def addOpSem : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Oadd .Op_int, .Vint x, .Vint y => .ok (.Vint (x + y))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops needed. -/
def addAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-- Callee parameter name `in : aint`. -/
def add1_in : VarI := { v_var := { vtype := .aint, vname := "in" } }
/-- Callee return name `ret : aint`. -/
def add1_ret : VarI := { v_var := { vtype := .aint, vname := "ret" } }
/-- Caller result variable `y : aint`. -/
def yVar : VarI := { v_var := { vtype := .aint, vname := "y" } }

/-- Callee body: `ret := in + 1`. -/
def add1_body : Cmd :=
  [ .MkI () (.Cassgn (.Lvar add1_ret) .AT_none .aint
      (.Papp2 (.Oadd .Op_int) (.Pvar (mkLvar add1_in)) (.Pconst 1))) ]

/-- `add1 (in : aint) -> aint`. -/
def add1_fundef : FunDef :=
  { tyin   := [.aint]
  , params := [add1_in]
  , body   := add1_body
  , tyout  := [.aint]
  , rets   := [add1_ret] }

/-- The callee's `FunName`. -/
def add1_fn : FunName := { name := "add1" }

/-- Full program containing just the callee. -/
def callProg : Prog := { pFuncs := [(add1_fn, add1_fundef)], pGlobs := [] }

/-- The emitted call site `y := add1(5)`. -/
def callAdd1 : InstrR := .Ccall [.Lvar yVar] add1_fn [.Pconst 5]

/-- A starting state with empty `Vm` and trivial memory. -/
def startState : Estate Unit TrivialMem :=
  { escs := (), emem := (), evm := Vm.init }

/-- Read the caller's result variable `y` out of a post-state. -/
def readY (s : Estate Unit TrivialMem) : Option Int :=
  match (Vm.get s.evm yVar.v_var) with
  | .Vint z => some z
  | _ => none

/-- **KAT.** The emitted `Ccall` run, with ample fuel, drives `y` to `6` — the
    call's effect is running the callee `add1`'s body `ret := in + 1` on the
    argument `5` and writing the return into `y`. -/
theorem callAdd1_emitted_kat :
    (match execInstrR (Mem := TrivialMem) addAsmSem addOpSem []
              8 startState callAdd1 callProg with
     | .ok s => readY s
     | _ => none) = some 6 := by
  native_decide

/-- **Run-correctness instance.** The emitted call run equals the §2 composition
    (eval args → run callee via `execCall` → write results) — a direct
    instance of `execInstrR_Ccall_eq`. -/
theorem callAdd1_emitted_eq_composition (fuel' : Nat) :
    execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] (fuel'+1) startState
        callAdd1 callProg
      = callComposition (Mem := TrivialMem) addAsmSem addOpSem []
          [.Lvar yVar] add1_fn [.Pconst 5] callProg fuel' startState :=
  execInstrR_Ccall_eq addAsmSem addOpSem [] [.Lvar yVar] add1_fn [.Pconst 5]
    callProg fuel' startState

/-- **Linked-composition instance.** Because `add1` is defined in `callProg`, the
    emitted call run equals the §3 linked-callee form with `add1`'s body
    (`execCmd … add1_body …`) substituted in — the semantic complement of
    LinkerReloc's "the call targets `add1`'s byte address". -/
theorem callAdd1_emitted_eq_linked (fuel' : Nat) :
    execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] (fuel'+2) startState
        callAdd1 callProg
      = linkedCall (Mem := TrivialMem) addAsmSem addOpSem []
          [.Lvar yVar] [.Pconst 5] add1_fundef callProg fuel' startState :=
  execInstrR_Ccall_eq_run_callee addAsmSem addOpSem [] [.Lvar yVar] add1_fn
    [.Pconst 5] callProg add1_fundef rfl fuel' startState

end Add1Example

end CatCrypt.Crypto.SecureCompilation.VIR.CallLowering
