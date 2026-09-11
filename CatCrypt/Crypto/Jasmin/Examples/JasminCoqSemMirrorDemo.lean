/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror


@[expose] public section
set_option autoImplicit false

/-!
# Smoke tests for `JasminCoqSemMirror`

This file exercises the mechanical Coq-port semantics on small examples to
verify that the port runs and produces the expected outputs.  All checks
are by `decide` / `rfl` / `#eval`; no formal preservation theorems live
here.

## Examples covered

1. `semPexpr` on a literal-and-arithmetic expression (`Pconst`, `Papp2`).
2. `writeVar` then `getVar` roundtrip.
3. `execCmd` on a one-`Cassgn` command.
4. `execCmd` on a two-instruction sequence (`Cassgn` + `Cassgn`).
5. `execCmd` on a `Cif` branch.
6. `execCmd` on a `Cfor` loop accumulating into a counter.

For these tests we instantiate the `MemModel` with a trivial "no memory"
model (any read/write fails `typeError`); no instruction here reaches a
`Pload` or `Lmem` lvalue.

`Value` carries `JArrayMirror n = Fin n -> BitVec 8` (function type), so
its `DecidableEq` is non-reducible.  To keep `decide` available we
*project* the value of interest to `Option Int` and compare the
projection.  This is sufficient for these straight-line demonstrators.
-/

/-- Project a `Value` to an `Int`, returning `none` for non-int values. -/
def CatCrypt.Crypto.Jasmin.CoqSemMirror.Value.asInt? :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.Value → Option Int
  | .Vint z => some z
  | _ => none

/-- Project a `Value` to a `Bool`, returning `none` for non-bool values. -/
def CatCrypt.Crypto.Jasmin.CoqSemMirror.Value.asBool? :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.Value → Option Bool
  | .Vbool b => some b
  | _ => none

namespace CatCrypt.Crypto.Jasmin.CoqSemMirrorDemo

open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ### Concrete instances we need to drive the executor -/

/-- Trivial memory model: an empty byte-store that fails every read/write.
    Smoke tests below never touch memory, so this is sound. -/
def TrivialMem : Type := Unit

instance : MemModel TrivialMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- Concrete `OpSem` covering just the arithmetic on `Vint` that the smoke
    tests use.  Word-side arithmetic is left at `.typeError` (the demos
    don't need it). -/
def demoOpSem : OpSem where
  sem_sop1 := fun
    | .Onot, .Vbool b => .ok (.Vbool (!b))
    | _, _ => .typeError
  sem_sop2 := fun
    | .Oadd .Op_int, .Vint x, .Vint y => .ok (.Vint (x + y))
    | .Osub .Op_int, .Vint x, .Vint y => .ok (.Vint (x - y))
    | .Omul .Op_int, .Vint x, .Vint y => .ok (.Vint (x * y))
    | .Oand,         .Vbool a, .Vbool b => .ok (.Vbool (a && b))
    | .Oor,          .Vbool a, .Vbool b => .ok (.Vbool (a || b))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- Concrete `AsmSem`: no asm-ops are needed by these tests. -/
def demoAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-- A starting state with empty `Vm` and trivial memory. -/
def initState : Estate Unit TrivialMem :=
  { escs := (), emem := (), evm := Vm.init }

/-! ### Example 1 -- `sem_pexpr` on a literal and an `add` -/

/-- The Pexpr `3 + 4` (over `int`, not over a word size). -/
def expr_three_plus_four : Pexpr :=
  .Papp2 (.Oadd .Op_int) (.Pconst 3) (.Pconst 4)

/-- Smoke-eval: project the result to `Option Int`. -/
def example1Result : Option Int :=
  match semPexpr (Mem := TrivialMem) true [] demoOpSem initState
                 expr_three_plus_four with
  | .ok v => v.asInt?
  | _ => none

#eval example1Result    -- expected: `some 7`

/-- The port produces `Vint 7`. -/
example : example1Result = some 7 := by native_decide

/-! ### Example 2 -- `writeVar` then read it back through `Pvar` -/

/-- A local integer variable `x`. -/
def x : VarI := { v_var := { vtype := .aint, vname := "x" } }

/-- The Pexpr referencing `x` as a local. -/
def expr_x : Pexpr := .Pvar (mkLvar x)

def example2Result : Option Int :=
  match (do
           let s ← writeVar (Mem := TrivialMem) true x (.Vint 42) initState
           semPexpr (Mem := TrivialMem) true [] demoOpSem s expr_x) with
  | .ok v => v.asInt?
  | _ => none

#eval example2Result    -- expected: `some 42`

example : example2Result = some 42 := by native_decide

/-! ### Example 3 -- single-Cassgn command via `execCmd` -/

/-- Assign `5` to `x`. -/
def cassgn_x_5 : InstrR :=
  .Cassgn (.Lvar x) .AT_none .aint (.Pconst 5)

/-- A one-instruction command `[x := 5]`. -/
def cmd_assign_x_5 : Cmd :=
  [ .MkI () cassgn_x_5 ]

def example3Result : Option Int :=
  match execCmd (Mem := TrivialMem) demoAsmSem demoOpSem []
                8 initState cmd_assign_x_5 with
  | .ok s => (s.evm.get x.v_var).asInt?
  | _ => none

#eval example3Result    -- expected: `some 5`

example : example3Result = some 5 := by native_decide

/-! ### Example 4 -- two-statement program: `x := 3; y := x + 4`

Exercises:
* `execCmd` cons step,
* `writeLval` on a `Lvar`,
* `semPexpr` reading a freshly written `Vm` entry,
* `Papp2 (Oadd Op_int)` arithmetic. -/

def y : VarI := { v_var := { vtype := .aint, vname := "y" } }

def cmd_x_then_y : Cmd :=
  [ .MkI () (.Cassgn (.Lvar x) .AT_none .aint (.Pconst 3))
  , .MkI () (.Cassgn (.Lvar y) .AT_none .aint
              (.Papp2 (.Oadd .Op_int) expr_x (.Pconst 4))) ]

def example4Result : Option Int × Option Int :=
  match execCmd (Mem := TrivialMem) demoAsmSem demoOpSem []
                16 initState cmd_x_then_y with
  | .ok s => ((s.evm.get x.v_var).asInt?, (s.evm.get y.v_var).asInt?)
  | _ => (none, none)

#eval example4Result    -- expected: `(some 3, some 7)`

example : example4Result = (some 3, some 7) := by native_decide

/-! ### Example 5 -- `Cif` branch on a true literal -/

def cmd_if_true_x_99 : Cmd :=
  [ .MkI () (.Cif (.Pbool true)
              [ .MkI () (.Cassgn (.Lvar x) .AT_none .aint (.Pconst 99)) ]
              [ .MkI () (.Cassgn (.Lvar x) .AT_none .aint (.Pconst 0)) ]) ]

def example5Result : Option Int :=
  match execCmd (Mem := TrivialMem) demoAsmSem demoOpSem []
                16 initState cmd_if_true_x_99 with
  | .ok s => (s.evm.get x.v_var).asInt?
  | _ => none

#eval example5Result    -- expected: `some 99`

example : example5Result = some 99 := by native_decide

/-! ### Example 6 -- `Cfor` accumulator loop

A bounded for-loop `for j = 0 to 4 { acc := acc + 1 }`.  Initial `acc = 0`;
after four iterations `acc = 4`.  This exercises:

* `wrange` producing `[0, 1, 2, 3]`,
* `execFor` writing successive `Vint` values into the loop variable `j`,
* `execCmd` on the body, and
* the `Papp2 (Oadd Op_int)` arithmetic over `Vint`.

Note: the body does not actually *read* `j`; the loop is purely used as a
counted-iteration construct.  That's enough to prove the `Cfor` rule wires
through. -/

def j : VarI := { v_var := { vtype := .aint, vname := "j" } }
def acc : VarI := { v_var := { vtype := .aint, vname := "acc" } }

/-- The body `acc := acc + 1`. -/
def cmd_inc_acc : Cmd :=
  [ .MkI () (.Cassgn (.Lvar acc) .AT_none .aint
              (.Papp2 (.Oadd .Op_int)
                      (.Pvar (mkLvar acc))
                      (.Pconst 1))) ]

/-- The full program: `acc := 0; for j = 0 to 4 { acc := acc + 1 }`. -/
def cmd_for_accumulate : Cmd :=
  [ .MkI () (.Cassgn (.Lvar acc) .AT_none .aint (.Pconst 0))
  , .MkI () (.Cfor j ⟨.UpTo, .Pconst 0, .Pconst 4⟩ cmd_inc_acc) ]

def example6Result : Option Int :=
  match execCmd (Mem := TrivialMem) demoAsmSem demoOpSem []
                32 initState cmd_for_accumulate with
  | .ok s => (s.evm.get acc.v_var).asInt?
  | _ => none

#eval example6Result    -- expected: `some 4`

example : example6Result = some 4 := by native_decide

/-! ### Example 7 -- `Ccall` to a separate function

A 2-function program:
* callee `add1 (in : aint) -> aint { ret := in + 1; return ret }`
* caller `main () { y := add1(5); return y }`

The caller writes the return value of `add1` into `y`; we expect `y = 6`.
This exercises:

* `Prog.pFuncs` lookup via `getFunDef`,
* `writeVars` binding actual arguments into the callee's fresh `Vm.init`,
* `execCmd` on the callee body (a one-line `Cassgn`),
* `getVarIs` reading the callee's return name out of the post-state,
* `writeLvals` writing the returned values into the caller's `Lvals`. -/

/-- Callee parameter name. -/
def add1_in : VarI := { v_var := { vtype := .aint, vname := "in" } }
/-- Callee return name. -/
def add1_ret : VarI := { v_var := { vtype := .aint, vname := "ret" } }

/-- Callee body: `ret := in + 1`. -/
def add1_body : Cmd :=
  [ .MkI () (.Cassgn (.Lvar add1_ret) .AT_none .aint
              (.Papp2 (.Oadd .Op_int)
                      (.Pvar (mkLvar add1_in))
                      (.Pconst 1))) ]

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
def callDemoProg : Prog := { pFuncs := [(add1_fn, add1_fundef)], pGlobs := [] }

/-- Caller body: `y := add1(5)`.  The `Ccall` lvals are `[Lvar y]`, the
    function is `add1_fn`, and the arguments are `[Pconst 5]`. -/
def cmd_call_add1 : Cmd :=
  [ .MkI () (.Ccall [.Lvar y] add1_fn [.Pconst 5]) ]

def example7Result : Option Int :=
  match execCmd (Mem := TrivialMem) demoAsmSem demoOpSem []
                32 initState cmd_call_add1 callDemoProg with
  | .ok s => (s.evm.get y.v_var).asInt?
  | _ => none

#eval example7Result    -- expected: `some 6`

example : example7Result = some 6 := by native_decide

end CatCrypt.Crypto.Jasmin.CoqSemMirrorDemo
