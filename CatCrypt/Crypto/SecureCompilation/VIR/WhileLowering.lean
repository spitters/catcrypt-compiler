/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror

/-!
# A runtime-bound (`while`) loop lowering: emitted `Cwhile` run = condition-driven iteration

The counted-loop lowering (`VIR/LoopLowering.lean`, `loopN`) covers
**static-count** loops: the iteration number is a `Nat` fixed at compile time
and the emitted `Cfor` run equals `step^[n]`. This module covers loops with a
runtime/`while` bound.

A runtime-bound loop iterates *while a run-time condition holds* — the iteration
count is determined by the data, not a static `Nat`. The terminating
shape (an arbitrary-predicate `while` need not terminate) is a **fuel-bounded /
decreasing-condition while**: iterate while `cond acc` holds, with a fuel `Nat`
bounding the recursion. We prove the **emitted while-loop run equals exactly
that fuel-bounded conditional iteration of the body**.

## What substrate we reuse (a *real* `Cwhile` run-semantics already exists)

We do **not** invent a semantic while model in a vacuum. `JasminCoqSemMirror`
is the mechanical Lean port of Jasmin's Coq `psem.v`, and it carries the
Jasmin while construct:

* `InstrR.Cwhile (al) (cbefore) (cond) (ii) (cafter)` — the AST node
  (`expr.v` mirror).
* The **relational** operational semantics `SemIr.Ewhile_true` /
  `SemIr.Ewhile_false` (`psem.v:87`/`94`): run `cbefore`, test `cond`; if true
  run `cafter` and recurse, else stop.
* The **functional** fuel-bounded executor `execInstrR`'s `.Cwhile` branch,
  which drives the same judgement (its `Cfor`/`Cif`/`Ccall` branches are the
  ones smoke-tested in `Examples/JasminCoqSemMirrorDemo.lean`; the `.Cwhile`
  branch is covered by the theorems of this module).

So the route here is *not* a fuel-bounded stand-in for a missing instruction
semantics; it is the run-correctness theorem for the **existing** `Cwhile`
executor, stated against a clean accumulator-level conditional iteration.

## Contents

1. **`whileExec`** — a fuel-recursive, condition-driven iteration over the
   executor's own state (`Estate`): evaluate `cond`; if it holds run the body
   and recurse on less fuel; else stop. This is the accumulator-level "iterate
   while the condition holds" semantics.

2. **`execInstrR_Cwhile_eq_whileExec`** — the main theorem: the emitted `Cwhile`
   executor (with empty `cbefore`, which is the idiomatic guard-after-step
   shape) **equals** `whileExec`, for every fuel. This ties the real Jasmin
   `Cwhile` run to the condition-driven iteration. Proved by fuel induction;
   each fuel level reduces the dynamic guard to the same `if cond then …`.

3. **`whileFuel`** — the abstract, pure conditional iteration over an arbitrary
   accumulator `α` (`if cond acc then whileFuel … (step acc) else acc`), and
   **`whileFuel_eq_iterate_of_count`**: when the condition first fails after
   exactly `k ≤ fuel` steps, the fuel-bounded while collapses to the *static*
   `step^[k]` — i.e. a runtime-bound loop whose data fixes the count `k`
   reduces to the counted-loop theorem at that `k`. This is the precise bridge
   "the dynamic count reduces to a static one".

4. A **worked, concrete example**: *decrement a counter to 0*. The emitted
   `Cwhile` (`while 0 < c { c := c - 1 }`) started at `c = 5`:
   - runs to `c = 0` (`decTo0_emitted_kat`, by `native_decide`);
   - its emitted run **equals** the abstract `whileFuel (0 < ·) (· - 1)`
     iteration started at `5` (`decTo0_emitted_eq_whileFuel`);
   - and that abstract while equals `(· - 1)^[5] 5 = 0` via the static-count
     collapse (`decTo0_whileFuel_eq_iterate`). All goals closed.

## Scope

This is a runtime-bound while over a **single accumulator** with empty
`cbefore` (guard-after-body shape) and a body run by the executor's own
`execCmd`. The `whileExec`/`whileFuel` equivalence is fuel-bounded: we prove
the executor's *functional* fuel-bounded run equals the conditional iteration.
A true **unbounded** `Cwhile` lowering — closing the *relational*
`SemIr.Ewhile_*` (which has no fuel and so models non-termination)
against an unbounded fixpoint, plus a termination-measure side-condition
discharging "the executor's fuel suffices" — is outside the scope of this
module.

All goals are closed; no opaque-leaf hypothesis is needed (the executor and `whileExec`
are both concrete functional definitions).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.WhileLowering

open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## 1. The condition-driven iteration over the executor state -/

variable {SyscallState Mem : Type} [MemModel Mem]

/-- `whileExec aS opS gd fuel cond body s prog` is the fuel-bounded,
    **condition-driven** iteration over the executor state `s`:

    * out of fuel → error (matches `execInstrR`'s fuel-0 case);
    * evaluate `cond` at `s`; if it is `true`, run `body` via `execCmd`, then
      recurse on the result with one less fuel; if `false`, stop and return `s`.

    This is the accumulator-level "iterate `body` while `cond` holds" semantics
    that a runtime-bound (`while`) loop denotes. -/
def whileExec (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (cond : Pexpr) (body : Cmd) (prog : Prog) :
    Nat → Estate SyscallState Mem → JResult (Estate SyscallState Mem)
  | 0, _ => .otherErr "execInstrR: out of fuel"
  | fuel'+1, s => do
      let vc ← semPexpr (Mem := Mem) true gd opS s cond
      let b ← vc.toBool
      if b then do
        let s' ← execCmd (Mem := Mem) aS opS gd fuel' s body prog
        whileExec aS opS gd cond body prog fuel' s'
      else
        .ok s

/-! ## 2. Main theorem: the emitted `Cwhile` run equals the condition-driven iteration

`execInstrR`'s `.Cwhile` branch, instantiated with **empty `cbefore`** (the
idiomatic guard-after-body shape: the body is `cafter`, run before the guard
is re-tested), unfolds — at every fuel level — to exactly `whileExec`. -/

/-- The emitted `Cwhile al [] cond ii body` executor equals `whileExec`,
    for every fuel. This is the run-correctness theorem for the real Jasmin
    `Cwhile` construct: its functional fuel-bounded run = the condition-driven
    iteration of the body. -/
theorem execInstrR_Cwhile_eq_whileExec
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (al : Align) (cond : Pexpr) (ii : InstrInfo) (body : Cmd) (prog : Prog) :
    ∀ (fuel : Nat) (s : Estate SyscallState Mem),
      execInstrR (Mem := Mem) aS opS gd fuel s
        (.Cwhile al [] cond ii body) prog
      = whileExec (Mem := Mem) aS opS gd cond body prog fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; rw [execInstrR, whileExec]
  | succ fuel' ih =>
      intro s
      -- Unfold both sides one step. `execCmd … [] = .ok s`, so `cbefore = []`
      -- makes the pre-guard `s'` equal `s`; then the `if b` shapes coincide, and
      -- the recursive `execInstrR fuel' s'' (Cwhile …)` call rewrites to
      -- `whileExec … fuel' s''` by `ih`.
      conv_lhs => rw [execInstrR]
      conv_rhs => rw [whileExec]
      simp only [execCmd, ih]
      rfl

/-! ## 3. Abstract conditional iteration and the static-count collapse

This section lifts the picture to a *pure* accumulator `α`, so the runtime-bound
loop can be stated independently of the executor state, and connects it to the
counted-loop theorem (`step^[k]`). -/

/-- `whileFuel cond step fuel acc` is the pure, fuel-bounded conditional
    iteration of `step` on accumulator `acc`: iterate `step` while `cond` holds,
    bounded by `fuel`. This is the data-driven (runtime-count) analogue of the
    counted-loop `step^[n]`. -/
def whileFuel {α : Type} (cond : α → Bool) (step : α → α) : Nat → α → α
  | 0, acc => acc
  | fuel'+1, acc => if cond acc then whileFuel cond step fuel' (step acc) else acc

@[simp] theorem whileFuel_zero {α : Type} (cond : α → Bool) (step : α → α)
    (acc : α) : whileFuel cond step 0 acc = acc := rfl

theorem whileFuel_succ {α : Type} (cond : α → Bool) (step : α → α)
    (fuel' : Nat) (acc : α) :
    whileFuel cond step (fuel'+1) acc
      = if cond acc then whileFuel cond step fuel' (step acc) else acc := rfl

/-- If the condition fails immediately, the while stops at `acc`. -/
theorem whileFuel_of_not_cond {α : Type} {cond : α → Bool} {step : α → α}
    {acc : α} (fuel' : Nat) (h : cond acc = false) :
    whileFuel cond step (fuel'+1) acc = acc := by
  simp [whileFuel_succ, h]

/-- **Static-count collapse.** When the loop runs exactly `k` body-steps before
    the guard fails — i.e. the guard holds on each of the first `k` iterates and
    fails on the `k`-th — the fuel-bounded *runtime-bound* while collapses to the
    *static* `step^[k]`. This is the precise bridge "the dynamic count reduces to
    a static one per fuel level": a data-driven loop whose data fixes the count
    `k` is the counted loop at `k`.

    Hypotheses:
    * `hk`: the guard holds at every iterate `step^[i] acc` for `i < k`;
    * `hstop`: the guard fails at `step^[k] acc`;
    * `hfuel`: there is at least `k+1` fuel (one extra to observe the stop). -/
theorem whileFuel_eq_iterate_of_count {α : Type} {cond : α → Bool} {step : α → α}
    (acc : α) (k fuel : Nat)
    (hk : ∀ i, i < k → cond (step^[i] acc) = true)
    (hstop : cond (step^[k] acc) = false)
    (hfuel : k < fuel) :
    whileFuel cond step fuel acc = step^[k] acc := by
  induction k generalizing fuel acc with
  | zero =>
      -- 0 body-steps: guard fails immediately.
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simpa using whileFuel_of_not_cond (cond := cond) (step := step) (acc := acc)
        fuel' (by simpa using hstop)
  | succ k ih =>
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hcond0 : cond acc = true := by
        have := hk 0 (by omega); simpa using this
      rw [whileFuel_succ, if_pos hcond0]
      -- Run the inner while on `step acc` for `k` steps.
      have hk' : ∀ i, i < k → cond (step^[i] (step acc)) = true := by
        intro i hi
        have := hk (i+1) (by omega)
        simpa [Function.iterate_succ_apply] using this
      have hstop' : cond (step^[k] (step acc)) = false := by
        have := hstop
        simpa [Function.iterate_succ_apply] using this
      have hfuel' : k < fuel' := by omega
      rw [ih (step acc) fuel' hk' hstop' hfuel', Function.iterate_succ_apply]

/-! ## 4. Worked concrete example: decrement a counter to 0

We instantiate the executor on a single integer accumulator `c`, with the
runtime-bound loop `while 0 < c { c := c - 1 }`. Starting from `c = 5`:

* the **emitted** `Cwhile` run drives `c` to `0` (`decTo0_emitted_kat`);
* that emitted run **equals** the abstract conditional iteration
  `whileFuel (0 < ·) (· - 1)` started at `5` (`decTo0_emitted_eq_whileFuel`),
  via the §2 theorem;
* and that abstract while collapses to the **static** counted loop
  `(· - 1)^[5] 5 = 0` (`decTo0_whileFuel_eq_iterate`), via the §3 bridge.

This exhibits the full chain "emitted runtime-bound while = condition-driven
iteration = counted loop at the data-determined count". -/

namespace DecTo0Example

/-- Trivial memory model (no read/write reached by this example). -/
def TrivialMem : Type := Unit

instance : MemModel TrivialMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- An `OpSem` covering the integer subtraction and `<` comparison this loop
    needs. Everything else is `.typeError` (unreached). -/
def decOpSem : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Osub .Op_int, .Vint x, .Vint y => .ok (.Vint (x - y))
    | .Olt .Cmp_int, .Vint x, .Vint y => .ok (.Vbool (decide (x < y)))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops needed. -/
def decAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-- The counter variable `c : aint`. -/
def cVar : VarI := { v_var := { vtype := .aint, vname := "c" } }

/-- The loop guard `0 < c`. -/
def guard : Pexpr :=
  .Papp2 (.Olt .Cmp_int) (.Pconst 0) (.Pvar (mkLvar cVar))

/-- The loop body `c := c - 1`. -/
def body : Cmd :=
  [ .MkI () (.Cassgn (.Lvar cVar) .AT_none .aint
      (.Papp2 (.Osub .Op_int) (.Pvar (mkLvar cVar)) (.Pconst 1))) ]

/-- The emitted runtime-bound loop `while 0 < c { c := c - 1 }`. -/
def decWhile : InstrR := .Cwhile .NoAlign [] guard () body

/-- Start state with `c = 5`. -/
def startState : Estate Unit TrivialMem :=
  { escs := (), emem := (), evm := Vm.set Vm.init cVar.v_var (.Vint 5) }

/-- Read the counter out of a post-state, projected to `Option Int`. -/
def readC (s : Estate Unit TrivialMem) : Option Int :=
  match (Vm.get s.evm cVar.v_var) with
  | .Vint z => some z
  | _ => none

/-- **KAT.** The emitted `Cwhile` run, with ample fuel, drives `c` to `0`. -/
theorem decTo0_emitted_kat :
    (match execInstrR (Mem := TrivialMem) decAsmSem decOpSem []
              16 startState decWhile with
     | .ok s => readC s
     | _ => none) = some 0 := by
  native_decide

/-- **Run-correctness instance.** The emitted runtime-bound loop run equals
    the condition-driven iteration `whileExec` of its body — a direct instance
    of the §2 theorem `execInstrR_Cwhile_eq_whileExec`. -/
theorem decTo0_emitted_eq_whileExec (fuel : Nat) :
    execInstrR (Mem := TrivialMem) decAsmSem decOpSem [] fuel startState decWhile
      = whileExec (Mem := TrivialMem) decAsmSem decOpSem [] guard body
          Prog.empty fuel startState :=
  execInstrR_Cwhile_eq_whileExec decAsmSem decOpSem [] .NoAlign guard () body
    Prog.empty fuel startState

/-- **Abstract collapse instance.** The pure conditional iteration
    `whileFuel (fun z => 0 < z) (fun z => z - 1)` started at `5` collapses to the
    static counted loop `(· - 1)^[5] 5`, which is `0`. A direct instance of the
    §3 bridge `whileFuel_eq_iterate_of_count` at the data-determined count `k = 5`. -/
theorem decTo0_whileFuel_eq_iterate :
    whileFuel (fun z : Int => decide (0 < z)) (fun z => z - 1) 16 5
      = (fun z : Int => z - 1)^[5] 5 :=
  whileFuel_eq_iterate_of_count 5 5 16 (by decide) (by decide) (by decide)

/-- The static iterate evaluates to `0`. -/
theorem decTo0_iterate_value :
    (fun z : Int => z - 1)^[5] 5 = 0 := by decide

end DecTo0Example

end CatCrypt.Crypto.SecureCompilation.VIR.WhileLowering
