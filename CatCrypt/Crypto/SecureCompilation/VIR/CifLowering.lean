/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror

/-!
# A fused two-way branch lowering: emitted `Cif` run = `ite` of the two arms' runs

`VIR/BranchLowering.lean` builds a public-condition two-way branch at
the **meta / semantic (`Phase`) level**: its `run` is *literally*
`if cond then thenPhase.run else elsePhase.run`, a `Bool`-parameter `ite` of the
two arms' emit denotations. Its scope note states what that level does not give:

> It is **not** a single fused control-flow graph emitted as one Jasmin `Cif`
> instruction … with a real conditional-jump … the verified-emit *denotation*
> theory … has **no** `Cif` `denote = ite` theorem tied to the … evaluator.

This module proves that fused lowering, as `VIR/WhileLowering.lean` does for
`Cwhile`: it states and proves the run-correctness theorem for the **existing**
`Cif` instruction against the **real** Jasmin operational semantics — *not* a
re-modeled `Phase`-level `ite`.

## What substrate we reuse (the `Cif` run-semantics of the Jasmin mirror)

`JasminCoqSemMirror` is the mechanical Lean port of Jasmin's Coq `psem.v`, and
it carries the Jasmin branch construct:

* `InstrR.Cif (cond) (cthen) (celse)` — the AST node (`expr.v:440` mirror).
* The **relational** operational semantics `SemIr.Eif_true` / `SemIr.Eif_false`
  (`psem.v:77`/`82`): evaluate `cond`; if it is `Vbool true` run `cthen`, if
  `Vbool false` run `celse`.
* The **functional** fuel-bounded executor `execInstrR`'s `.Cif` branch
  (`JasminCoqSemMirror`), which drives the same judgement and is smoke-tested in
  `Examples/JasminCoqSemMirrorDemo.lean` (Example 5).

So the route here is the run-correctness theorem for the **existing** `Cif`
executor, stated against the executor's own arm runs (`execCmd`).

## What this module adds

1. **`ifExec`** — the condition-driven branch over the executor's own state
   (`Estate`): evaluate `cond`, project it to a `Bool` via `Value.toBool`, then
   run `cthen` or `celse` via the executor's own `execCmd`. This is exactly the
   data the `.Cif` branch denotes, factored so the condition-evaluation is
   visible. It is **not** a `Bool`-parameter stand-in: the selecting bit is
   computed from the state by the real `semPexpr`/`toBool`, identically to the
   executor.

2. **`execInstrR_Cif_eq_ifExec`** — the main theorem: the emitted `Cif` executor
   equals `ifExec`, for every (positive) fuel. Proved by the same
   `conv_lhs => rw [execInstrR]` peeling used for `Cwhile`.

3. **`execInstrR_Cif_eq_ite`** — the headline `Cif` `denote = ite` law: when the
   condition evaluates (`semPexpr … cond = .ok (.Vbool b)`, the public-condition
   hypothesis), the emitted `Cif` run is exactly
   `if b then execCmd … cthen else execCmd … celse` — the `if-then-else` of the
   two branches' runs on the **real** `execInstrR` executor. The two taken-branch
   corollaries `…_true` / `…_false` follow.

4. A **worked, concrete example**: the branch `if 0 < x then x := x + x else
   x := x - x`, started at `x = 5`, with the run equal to the taken arm for
   **both** condition truth values — `5 + 5 = 10` on the true side and
   `5 - 5 = 0` (the int analogue of the prompt's `x ^^^ x`) on the false side —
   on the executor (`native_decide` KAT), plus the symbolic `ite` instance via
   the main theorem.

5. **`branchPhase`-bridge** (optional, §5): `execInstrR_Cif_eq_ite` discharges
   exactly the semantic `ite` law each arm of `BranchLowering.branchPhase` must
   satisfy — the executor-level `Cif` matches the `Phase`-level `ite` model when
   the `Phase` arms are taken to be the two `execCmd` runs.

## Public condition ⇒ CT preserved (honest framing)

`execInstrR_Cif_eq_ite`'s hypothesis is `semPexpr … s cond = .ok (.Vbool b)`:
the condition evaluates to a definite **public** bit `b` — a loop bound, message
length, protocol version, or Fiat-Shamir-public flag — the case where divergent
control flow is fine because the branch *taken* is not secret. The leakage
(which arm runs) is `b`, a function of public data only, so the two-way
control-flow branch preserves constant-time. This is the same public-condition
discipline `BranchLowering` makes a typing rule, here tied to the real
executor's selector rather than a `Bool` parameter. (Contrast the branchless
secret-`select`, where a *secret*-dependent choice is compiled to a mask-blend
with no control divergence.)

## Scope (honest)

`execInstrR_Cif_eq_ite` is the run-correctness theorem for the executor's
**functional** `Cif` run against the structured `ite` of its two arm runs. The
remaining gap — shared with `WhileLowering` — is the **relational**
`SemIr.Eif_*` against a single merged control-flow graph: the executor and the
relational `Eif_true`/`Eif_false` agree by construction here (both select on the
same `semPexpr` value), but a *merged-CFG* `Cif` (one conditional jump + a merge
block, rather than the executor's structured `if`) is a lowering target this
file does not emit; it supplies the `denote = ite` law that such a lowering must
satisfy. This is noted in the deliverable, not papered over.

All goals are closed; no opaque-leaf hypothesis is needed (the executor, `ifExec`
and `execCmd` are concrete functional definitions).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CifLowering

open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## 1. The condition-driven branch over the executor state -/

variable {SyscallState Mem : Type} [MemModel Mem]

/-- `ifExec aS opS gd cond cthen celse prog fuel s` is the **condition-driven**
    two-way branch over the executor state `s`:

    * out of fuel → error (matches `execInstrR`'s fuel-0 case);
    * evaluate `cond` at `s` (`semPexpr`), project it to a `Bool` (`toBool`);
      if it is `true` run `cthen` via `execCmd`, else run `celse` via `execCmd`.

    This is the accumulator-level "run `cthen` if `cond` holds, else `celse`"
    semantics that a two-way branch denotes — factored so the condition is
    evaluated by the **same** `semPexpr`/`toBool` the executor uses. -/
def ifExec (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (cthen celse : Cmd) (prog : Prog) :
    Nat → Estate SyscallState Mem → JResult (Estate SyscallState Mem)
  | 0, _ => .otherErr "execInstrR: out of fuel"
  | fuel'+1, s => do
      let vc ← semPexpr (Mem := Mem) true gd opS s cond
      let b ← vc.toBool
      if b then execCmd (Mem := Mem) aS opS gd fuel' s cthen prog
      else execCmd (Mem := Mem) aS opS gd fuel' s celse prog

/-! ## 2. Main theorem: the emitted `Cif` run equals the condition-driven branch

`execInstrR`'s `.Cif` branch unfolds — at every positive fuel level — to exactly
`ifExec`. This is the run-correctness theorem for the real Jasmin `Cif`
construct: its functional fuel-bounded run = the condition-driven selection of
the two arm runs. -/

/-- The emitted `Cif cond cthen celse` executor equals `ifExec`, for every fuel.
    Proved by the same `conv_lhs => rw [execInstrR]` peeling `WhileLowering`
    uses for `Cwhile`: at fuel `0` both sides reduce to the out-of-fuel error;
    at `fuel'+1` both unfold to the same `semPexpr`/`toBool`/`if` shape. -/
theorem execInstrR_Cif_eq_ifExec
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (cthen celse : Cmd) (prog : Prog) :
    ∀ (fuel : Nat) (s : Estate SyscallState Mem),
      execInstrR (Mem := Mem) aS opS gd fuel s (.Cif cond cthen celse) prog
      = ifExec (Mem := Mem) aS opS gd cond cthen celse prog fuel s := by
  intro fuel
  cases fuel with
  | zero => intro s; rw [execInstrR, ifExec]
  | succ fuel' =>
      intro s
      conv_lhs => rw [execInstrR]
      conv_rhs => rw [ifExec]

/-! ## 3. The `Cif` `denote = ite` law: emitted branch run = `ite` of the arms

When the condition evaluates to a definite **public** boolean `b`
(`semPexpr … cond = .ok (.Vbool b)`), the emitted `Cif` run collapses to the
plain `if b then … else …` of the two branch runs. This is the structural
`denote = ite` theorem the `BranchLowering` scope note refers to, stated
against the **real** `execInstrR` executor. -/

/-- **`Cif` denote-correctness (the `ite` law).** If `cond` evaluates at `s` to
    the public boolean value `.Vbool b`, then the emitted `Cif cond cthen celse`
    run is exactly `if b then execCmd … cthen else execCmd … celse` — the
    `if-then-else` of the two arms' runs, selected by the public condition, on
    the real executor. -/
theorem execInstrR_Cif_eq_ite
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (cthen celse : Cmd) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) (b : Bool)
    (hcond : semPexpr (Mem := Mem) true gd opS s cond = .ok (.Vbool b)) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cif cond cthen celse) prog
      = (if b then execCmd (Mem := Mem) aS opS gd fuel' s cthen prog
         else execCmd (Mem := Mem) aS opS gd fuel' s celse prog) := by
  rw [execInstrR_Cif_eq_ifExec, ifExec, hcond]
  rfl

/-- **Taken-branch corollary (`true`).** When the public condition evaluates to
    `true`, the emitted `Cif` run is exactly the `then` arm's run. -/
theorem execInstrR_Cif_true
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (cthen celse : Cmd) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem)
    (hcond : semPexpr (Mem := Mem) true gd opS s cond = .ok (.Vbool true)) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cif cond cthen celse) prog
      = execCmd (Mem := Mem) aS opS gd fuel' s cthen prog := by
  rw [execInstrR_Cif_eq_ite aS opS gd cond cthen celse prog fuel' s true hcond]
  simp

/-- **Taken-branch corollary (`false`).** When the public condition evaluates to
    `false`, the emitted `Cif` run is exactly the `else` arm's run. -/
theorem execInstrR_Cif_false
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (cthen celse : Cmd) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem)
    (hcond : semPexpr (Mem := Mem) true gd opS s cond = .ok (.Vbool false)) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cif cond cthen celse) prog
      = execCmd (Mem := Mem) aS opS gd fuel' s celse prog := by
  rw [execInstrR_Cif_eq_ite aS opS gd cond cthen celse prog fuel' s false hcond]
  simp

/-! ## 4. Worked concrete example: `if 0 < x then x := x + x else x := x - x`

We instantiate the executor on a single integer variable `x`, with the branch
`if 0 < x { x := x + x } else { x := x - x }` (the `else` block zeroes `x`, the
int analogue of the prompt's `x ^^^ x`). Started from `x = 5`:

* the **emitted** `Cif` run (true side fires) drives `x` to `10`
  (`doubleOrZero_true_kat`, by `native_decide`);
* a **false-side** instance (with a `0 < x` guard that is false, started at
  `x = 0`) zeroes `x` (`doubleOrZero_false_kat`, by `native_decide`);
* and both are the structural `ite` of the two `execCmd` runs via the §3
  theorem — the run equals the taken branch's `execCmd`, for both `c` values. -/

namespace DoubleOrZeroExample

/-- Trivial memory model (no read/write reached by this example). -/
def TrivialMem : Type := Unit

instance : MemModel TrivialMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- An `OpSem` covering the integer addition, subtraction and `<` comparison
    this branch needs. Everything else is `.typeError` (unreached). -/
def ifOpSem : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Oadd .Op_int, .Vint x, .Vint y => .ok (.Vint (x + y))
    | .Osub .Op_int, .Vint x, .Vint y => .ok (.Vint (x - y))
    | .Olt .Cmp_int, .Vint x, .Vint y => .ok (.Vbool (decide (x < y)))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops needed. -/
def ifAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-- The variable `x : aint`. -/
def xVar : VarI := { v_var := { vtype := .aint, vname := "x" } }

/-- The branch guard `0 < x`. -/
def guard : Pexpr :=
  .Papp2 (.Olt .Cmp_int) (.Pconst 0) (.Pvar (mkLvar xVar))

/-- The `then` arm `x := x + x` (doubling). -/
def thenArm : Cmd :=
  [ .MkI () (.Cassgn (.Lvar xVar) .AT_none .aint
      (.Papp2 (.Oadd .Op_int) (.Pvar (mkLvar xVar)) (.Pvar (mkLvar xVar)))) ]

/-- The `else` arm `x := x - x` (zeroing — the int analogue of `x ^^^ x`). -/
def elseArm : Cmd :=
  [ .MkI () (.Cassgn (.Lvar xVar) .AT_none .aint
      (.Papp2 (.Osub .Op_int) (.Pvar (mkLvar xVar)) (.Pvar (mkLvar xVar)))) ]

/-- The emitted two-way branch `if 0 < x { x := x + x } else { x := x - x }`. -/
def doubleOrZero : InstrR := .Cif guard thenArm elseArm

/-- A start state with `x = n`. -/
def startState (n : Int) : Estate Unit TrivialMem :=
  { escs := (), emem := (), evm := Vm.set Vm.init xVar.v_var (.Vint n) }

/-- Read `x` out of a post-state, projected to `Option Int`. -/
def readX (s : Estate Unit TrivialMem) : Option Int :=
  match (Vm.get s.evm xVar.v_var) with
  | .Vint z => some z
  | _ => none

/-- **KAT (`true` side).** Started at `x = 5`, the guard `0 < 5` holds, so the
    emitted `Cif` runs the `then` arm `x := x + x`, giving `x = 10`. -/
theorem doubleOrZero_true_kat :
    (match execInstrR (Mem := TrivialMem) ifAsmSem ifOpSem []
              8 (startState 5) doubleOrZero with
     | .ok s => readX s
     | _ => none) = some 10 := by
  native_decide

/-- **KAT (`false` side).** Started at `x = 0`, the guard `0 < 0` is false, so the
    emitted `Cif` runs the `else` arm `x := x - x`, giving `x = 0`. -/
theorem doubleOrZero_false_kat :
    (match execInstrR (Mem := TrivialMem) ifAsmSem ifOpSem []
              8 (startState 0) doubleOrZero with
     | .ok s => readX s
     | _ => none) = some 0 := by
  native_decide

/-- The guard `0 < x` evaluates to `.Vbool (decide (0 < n))` at `startState n`. -/
theorem guard_eval (n : Int) :
    semPexpr (Mem := TrivialMem) true [] ifOpSem (startState n) guard
      = .ok (.Vbool (decide (0 < n))) := by
  rfl

/-- **Run-correctness instance (`ite` form, symbolic in the seed).** For any
    seed `n` and ample fuel, the emitted branch run is exactly the `ite` of the
    two arms' `execCmd` runs, selected by the public guard `0 < n` — a direct
    instance of the §3 theorem `execInstrR_Cif_eq_ite`. -/
theorem doubleOrZero_run_eq (n : Int) (fuel' : Nat) :
    execInstrR (Mem := TrivialMem) ifAsmSem ifOpSem [] (fuel'+1) (startState n)
        doubleOrZero
      = (if decide (0 < n) then
          execCmd (Mem := TrivialMem) ifAsmSem ifOpSem [] fuel' (startState n)
            thenArm Prog.empty
         else
          execCmd (Mem := TrivialMem) ifAsmSem ifOpSem [] fuel' (startState n)
            elseArm Prog.empty) :=
  execInstrR_Cif_eq_ite ifAsmSem ifOpSem [] guard thenArm elseArm Prog.empty
    fuel' (startState n) (decide (0 < n)) (guard_eval n)

end DoubleOrZeroExample

/-! ## 5. Bridge to `BranchLowering`'s `Phase`-level `ite` model (optional)

`BranchLowering.branchPhase` lowers a public two-way branch at the meta-`Phase`
level: its `run init = if cond then thenPhase.run init else elsePhase.run init`.
`execInstrR_Cif_eq_ite` discharges exactly that `ite` law on the **real**
executor — read with the two `Phase` arms taken to be the two `execCmd` runs of
`cthen`/`celse`, the executor-level `Cif` *is* the `branchPhase` model. We state
the alignment as a definitional equality on the `ifExec` form: the executor's
`Cif` selector is the same `if b then … else …` `branchPhase` uses, with `b` the
public condition value. -/

/-- **Executor `Cif` matches the `Phase`-level `ite` shape.** With the condition
    value `b` supplied as the public selecting bit, the emitted `Cif` run is the
    `if b then thenRun else elseRun` of the two arm runs — definitionally the
    same `ite` `BranchLowering.branchPhase.run` uses, realised on the real
    `execInstrR`. -/
theorem execInstrR_Cif_matches_branchPhase_ite
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (cthen celse : Cmd) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem) (b : Bool)
    (hcond : semPexpr (Mem := Mem) true gd opS s cond = .ok (.Vbool b))
    (thenRun elseRun : JResult (Estate SyscallState Mem))
    (hthen : execCmd (Mem := Mem) aS opS gd fuel' s cthen prog = thenRun)
    (helse : execCmd (Mem := Mem) aS opS gd fuel' s celse prog = elseRun) :
    execInstrR (Mem := Mem) aS opS gd (fuel'+1) s (.Cif cond cthen celse) prog
      = (if b then thenRun else elseRun) := by
  rw [execInstrR_Cif_eq_ite aS opS gd cond cthen celse prog fuel' s b hcond,
      hthen, helse]

end CatCrypt.Crypto.SecureCompilation.VIR.CifLowering
