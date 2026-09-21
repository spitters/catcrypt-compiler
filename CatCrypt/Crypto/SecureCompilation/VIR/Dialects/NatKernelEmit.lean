/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelFlatten
public import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelFlatten
public import Lean

/-!
# Emitting a Lean term from a `natKernelDialect` program

`FlatProg.run` is the specification of what a flat program computes; it reads
its environment with `List.getD`, so running it costs an environment traversal
per argument. The emitter produces the artifact instead: a Lean function whose
body is a chain of `let` binders, one per instruction, with each argument a
bound variable. Reducing that term costs the arithmetic and nothing else.

## The term elaborator and what carries the proof

`natKernelFn% p n` elaborates to a function of `n` `Nat` arguments whose body is
the let-chain of `p`'s instructions. The elaborator is ordinary metaprogramming
and is not trusted: each use is accompanied by an equation against
`FlatProg.run`, proved by `rfl` and therefore checked by the kernel:

```
def myFn : Nat → Nat → Nat := natKernelFn% myProg 2
theorem myFn_run (a b : Nat) : myFn a b = myProg.run [b, a] := rfl
```

That equation is translation validation per program. Composed with
`flatten_run` it gives the emitted function's value in terms of the source
program's denotation, with no step taken on trust.

## Argument order

The environment is most-recent-first, matching `Ctxt.Var`: for a program of
arity `n`, argument `0` of the emitted function is the outermost binding, so it
sits at index `n - 1` of the environment, and the last argument sits at index
`0`. The `myFn_run` equation above states that order explicitly, which is what
makes a mistake in it a failed `rfl` rather than a silent disagreement.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.NatKernel

/-! ## 1. A two-argument program and its emitted function -/

/-- A two-argument program: bind the sum of the two arguments, then multiply it
    by the first argument. -/
def sumTimesFirstProg : FlatProg where
  instrs := [{ op := .add, a := 0, b := 1 }, { op := .mul, a := 0, b := 2 }]
  ret := 0

/-! ## 2. The emitter -/

meta section

open Lean Elab Term Meta

/-- The `Nat` function a binary operation emits. `const` has none: it emits its
    literal instead. -/
def opConst : NatKernelOp → Option Name
  | .const _ => none
  | .add => ``Nat.add
  | .sub => ``Nat.sub
  | .mul => ``Nat.mul
  | .pow => ``Nat.pow
  | .gcd => ``Nat.gcd
  | .mod => ``Nat.mod
  | .div => ``Nat.div
  | .beq => ``Nat.beq
  | .ble => ``Nat.ble
  | .land => ``Nat.land
  | .lor => ``Nat.lor
  | .xor => ``Nat.xor
  | .shiftLeft => ``Nat.shiftLeft
  | .shiftRight => ``Nat.shiftRight

/-- The body of one instruction, as a term over the current environment. The
    environment is most-recent-first, so index `i` is `env[i]`. `beq` and `ble`
    are emitted as the `0`/`1` encoding `evalFlatOp` gives them, so the emitted
    term is `Nat`-valued throughout. -/
def instrExpr (i : FlatInstr) (env : Array Lean.Expr) : MetaM Lean.Expr := do
  let arg (k : Nat) : MetaM Lean.Expr :=
    match env[k]? with
    | some e => pure e
    | none => pure (mkNatLit 0)
  let boolToNat (f : Name) : MetaM Lean.Expr := do
    let a ← arg i.a
    let b ← arg i.b
    let c ← mkEq (← mkAppM f #[a, b]) (mkConst ``Bool.true)
    mkAppM ``ite #[c, mkNatLit 1, mkNatLit 0]
  match i.op with
  | .const n => pure (mkNatLit n)
  | .beq => boolToNat ``Nat.beq
  | .ble => boolToNat ``Nat.ble
  | op =>
      match opConst op with
      | some f => do mkAppM f #[← arg i.a, ← arg i.b]
      | none => throwError "natKernelFn%: no binary function for {repr op}"

/-- The let-chain: each instruction binds a fresh variable that the
    instructions after it may read. -/
partial def buildChain (instrs : List FlatInstr) (ret : Nat)
    (env : Array Lean.Expr) : MetaM Lean.Expr := do
  match instrs with
  | [] =>
      match env[ret]? with
      | some e => pure e
      | none => pure (mkNatLit 0)
  | i :: rest =>
      let v ← instrExpr i env
      withLetDecl (← mkFreshUserName `t) (mkConst ``Nat) v fun x => do
        let body ← buildChain rest ret (#[x] ++ env)
        mkLetFVars #[x] body

/-- Introduce `n` local `Nat` declarations and run `k` on them. -/
partial def withNatArgs (n : Nat) (k : Array Lean.Expr → TermElabM Lean.Expr) :
    TermElabM Lean.Expr :=
  go 0 #[]
where
  go (i : Nat) (acc : Array Lean.Expr) : TermElabM Lean.Expr :=
    if i = n then k acc
    else
      withLocalDeclD (Name.mkSimple s!"a{i}") (mkConst ``Nat) fun x =>
        go (i + 1) (acc.push x)

/-- `natKernelFn% p n` is the function of `n` `Nat` arguments that `p`
    computes, as a let-chain. -/
elab "natKernelFn% " pStx:term:max nStx:term:max : term => do
  let pExpr ← elabTerm pStx (some (mkConst ``FlatProg))
  let nExpr ← elabTerm nStx (some (mkConst ``Nat))
  synthesizeSyntheticMVars
  let p ← unsafe evalExpr FlatProg (mkConst ``FlatProg) (← instantiateMVars pExpr)
  let n ← unsafe evalExpr Nat (mkConst ``Nat) (← instantiateMVars nExpr)
  withNatArgs n fun xs => do
    -- argument 0 is the outermost binding, so it is the last environment slot
    let body ← buildChain p.instrs p.ret xs.reverse
    mkLambdaFVars xs body

end

/-! ## 3. The emitted function and its validating equation -/

/-- The function `sumTimesFirstProg` emits. -/
def sumTimesFirst : Nat → Nat → Nat := natKernelFn% sumTimesFirstProg 2

/-- The emitted function agrees with the flat program's specification on the
    environment the argument order prescribes. -/
example (a b : Nat) : sumTimesFirst a b = sumTimesFirstProg.run [b, a] := rfl

/-- A two-argument program whose single instruction is a comparison, so its
    value is the `0`/`1` encoding `encVal` gives a `.bool`. -/
def eqTestProg : FlatProg where
  instrs := [{ op := .beq, a := 0, b := 1 }]
  ret := 0

/-- The function `eqTestProg` emits. -/
def eqTest : Nat → Nat → Nat := natKernelFn% eqTestProg 2

/-- The comparison arm of the emitter agrees with `evalFlatOp` at `beq`. -/
example (a b : Nat) : eqTest a b = eqTestProg.run [b, a] := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.NatKernel
