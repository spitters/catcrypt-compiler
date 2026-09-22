/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelRule110
public import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelRule110

/-!
# Counted loops for the kernel backend

A `FlatProg` is straight-line: emitting a computation that repeats a body `n`
times from it means unrolling the body `n` times. This module adds a counted
loop as a statement. A loop reads its trip count and its initial state from the
environment, runs a straight-line body once per iteration over a one-number
state, and binds the final state.

One number of state is general, not a restriction: aggregate state is carried
packed into a single `Nat`, the representation the kernel reduces fastest.

## The loop combinator

`natLoop f n s` is `Nat.rec s f n`: the state after `n` steps, step `k` mapping
the state to `f k state`. The recursive call sits inside the argument of `f`, so
the kernel reduces each state as it is produced rather than building a nest of
pending applications, which is what makes a tail-recursive accumulator
quadratic in the kernel at a few thousand steps.

Both sides of the validating equation use `natLoop`: the specification
`LProg.run` loops over `FlatProg.run` of the body, and the emitted term loops
over the body's let-chain. The per-program equation is therefore `rfl` for
symbolic arguments, by the same unfolding that makes it `rfl` for a straight
line, with no induction over the trip count.

`natLoop` is defined by the recursor, which the code generator does not
compile, so it and every function emitted with a loop are `noncomputable`.
They exist to be reduced by the kernel.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.NatKernel

/-! ## 1. The combinator -/

/-- `n` steps of `f` from `s`, step `k` taking the state to `f k state`. -/
noncomputable def natLoop (f : Nat → Nat → Nat) (n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s f n

theorem natLoop_zero (f : Nat → Nat → Nat) (s : Nat) : natLoop f 0 s = s := rfl

theorem natLoop_succ (f : Nat → Nat → Nat) (k s : Nat) :
    natLoop f (k + 1) s = f k (natLoop f k s) := rfl

/-- `n` iterations of a straight-line body over one number of state. The body's
    environment holds the state at index `0` and the iteration number at index
    `1`. -/
noncomputable def iterRun (body : FlatProg) (n s : Nat) : Nat :=
  natLoop (fun k acc => body.run [acc, k]) n s

/-! ## 2. Loop programs -/

/-- A statement: one straight-line operation, or a counted loop that reads its
    trip count from index `count` and its initial state from index `init`. -/
inductive LStmt where
  | op (i : FlatInstr)
  | loop (count init : Nat) (body : FlatProg)

/-- One step of the loop machine: an operation as in `stepFlat`, or a loop whose
    final state is consed onto the environment. -/
noncomputable def stepL (env : List Nat) : LStmt → List Nat
  | .op i => stepFlat env i
  | .loop c s b => iterRun b (env.getD c 0) (env.getD s 0) :: env

/-- A program of statements, then the index of the result. -/
structure LProg where
  stmts : List LStmt
  ret : Nat

/-- Run the statements in order, then read the result index. -/
noncomputable def LProg.run (p : LProg) (env : List Nat) : Nat :=
  (p.stmts.foldl stepL env).getD p.ret 0

/-- A straight-line program read as a loop program. -/
def FlatProg.toL (p : FlatProg) : LProg := ⟨p.instrs.map .op, p.ret⟩

/-- Loop programs extend straight-line ones: a program with no loop computes
    what `FlatProg.run` says. -/
theorem FlatProg.toL_run (p : FlatProg) (env : List Nat) : p.toL.run env = p.run env := by
  simp only [LProg.run, FlatProg.toL, FlatProg.run, List.foldl_map]
  rfl

/-! ## 3. The emitter -/

meta section

open Lean Elab Term Meta

/-- The statement chain: an operation binds its value as in `buildChain`; a
    loop binds `natLoop` applied to the body's let-chain, abstracted over the
    iteration number and the state. -/
partial def buildLChain (stmts : List LStmt) (ret : Nat)
    (env : Array Lean.Expr) : MetaM Lean.Expr := do
  let arg (k : Nat) : Lean.Expr := (env[k]?).getD (mkNatLit 0)
  match stmts with
  | [] => pure (arg ret)
  | .op i :: rest =>
      let v ← instrExpr i env
      withLetDecl (← mkFreshUserName `t) (mkConst ``Nat) v fun x => do
        mkLetFVars #[x] (← buildLChain rest ret (#[x] ++ env))
  | .loop c s b :: rest =>
      let f ← withLocalDeclD `k (mkConst ``Nat) fun k =>
        withLocalDeclD `acc (mkConst ``Nat) fun acc => do
          mkLambdaFVars #[k, acc] (← buildChain b.instrs b.ret #[acc, k])
      let v ← mkAppM ``natLoop #[f, arg c, arg s]
      withLetDecl (← mkFreshUserName `t) (mkConst ``Nat) v fun x => do
        mkLetFVars #[x] (← buildLChain rest ret (#[x] ++ env))

/-- `natKernelLoopFn% p n` is the function of `n` `Nat` arguments that the loop
    program `p` computes. Argument order is that of `natKernelFn%`. -/
elab "natKernelLoopFn% " pStx:term:max nStx:term:max : term => do
  let pExpr ← elabTerm pStx (some (mkConst ``LProg))
  let nExpr ← elabTerm nStx (some (mkConst ``Nat))
  synthesizeSyntheticMVars
  let p ← unsafe evalExpr LProg (mkConst ``LProg) (← instantiateMVars pExpr)
  let n ← unsafe evalExpr Nat (mkConst ``Nat) (← instantiateMVars nExpr)
  withNatArgs n fun xs => do
    let body ← buildLChain p.stmts p.ret xs.reverse
    mkLambdaFVars xs body

end

/-! ## 4. Rule 110 over many generations -/

set_option maxRecDepth 8000

/-- `n` generations of rule 110 from a packed row: one loop over `rule110Prog`.
    The emitted function takes the row and then the generation count, so the
    count sits at index `0` and the row at index `1`. -/
def rule110GensProg : LProg where
  stmts := [.loop 0 1 rule110Prog]
  ret := 0

/-- The function `rule110GensProg` emits. -/
noncomputable def rule110Gens : Nat → Nat → Nat := natKernelLoopFn% rule110GensProg 2

/-- The emitted function computes what the loop program specifies. -/
theorem rule110Gens_run (row n : Nat) :
    rule110Gens row n = rule110GensProg.run [n, row] := rfl

/-- The emitted loop is `n` applications of the emitted one-generation
    function. -/
theorem rule110Gens_succ (row n : Nat) :
    rule110Gens row (n + 1) = rule110Step (rule110Gens row n) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.NatKernel
