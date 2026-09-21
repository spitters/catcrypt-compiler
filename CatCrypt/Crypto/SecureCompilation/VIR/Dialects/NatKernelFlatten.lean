/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelDialect

/-!
# Flattening a `natKernelDialect` program to an instruction list

A `Com natKernelDialect` is intrinsically typed: its variables are de Bruijn
witnesses and its valuation is an `HVector`. Reducing such a program's
denotation in the kernel walks that `HVector` once per variable read, which is
the interpretive cost the dialect exists to avoid. The emitter's job is to turn
the program into a plain Lean term with one binder per operation, and the
statement that the emitted term is right needs a form of the program the
emitter can consume and the proof can reason about.

`FlatProg` is that form: a list of operations, each naming its two arguments by
de Bruijn index into a value list, plus the index of the result. `flatten`
produces it from a `Com`, and `flatten_run` proves the two agree:

```
(flatten c).run (encEnv V) = encVal _ (c.denote V)
```

Values are carried as `Nat`. The dialect's `.bool` type (the return type of
`beq` and `ble`) is encoded by `encVal` as `0` and `1`, which is what lets one
flat environment hold both of the dialect's types.

`FlatProg.run` is a specification, not an execution path: it reads its
environment with `List.getD`, so running it costs what an interpreter costs.
What executes is the term the emitter builds from the same `FlatProg`; `run` is
the thing that term is proved equal to.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.NatKernel

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Values as `Nat` -/

/-- Carry a dialect value as a `Nat`: a `.nat` unchanged, a `.bool` as `0` or
    `1`. -/
def encVal : (t : natKernelDialect.Ty) → ⟦t⟧ → Nat
  | .nat, n => n
  | .bool, b => if b then 1 else 0

/-! ## 2. Flat programs -/

/-- One operation, with its two arguments named by de Bruijn index into the
    value list. A nullary `const` ignores both. -/
structure FlatInstr where
  op : NatKernelOp
  a : Nat
  b : Nat
  deriving Repr

/-- A straight-line program: operations in binding order, then the index of the
    result. -/
structure FlatProg where
  instrs : List FlatInstr
  ret : Nat
  deriving Repr

/-- One operation on two `Nat`-carried values. The comparisons return `1` and
    `0`, matching `encVal` at `.bool`. -/
def evalFlatOp : NatKernelOp → Nat → Nat → Nat
  | .const n,    _, _ => n
  | .add,        x, y => Nat.add x y
  | .sub,        x, y => Nat.sub x y
  | .mul,        x, y => Nat.mul x y
  | .pow,        x, y => Nat.pow x y
  | .gcd,        x, y => Nat.gcd x y
  | .mod,        x, y => Nat.mod x y
  | .div,        x, y => Nat.div x y
  | .beq,        x, y => if Nat.beq x y then 1 else 0
  | .ble,        x, y => if Nat.ble x y then 1 else 0
  | .land,       x, y => Nat.land x y
  | .lor,        x, y => Nat.lor x y
  | .xor,        x, y => Nat.xor x y
  | .shiftLeft,  x, y => Nat.shiftLeft x y
  | .shiftRight, x, y => Nat.shiftRight x y

/-- One step of the flat machine: evaluate an instruction against the
    environment and cons its result on. -/
def stepFlat (env : List Nat) (i : FlatInstr) : List Nat :=
  evalFlatOp i.op (env.getD i.a 0) (env.getD i.b 0) :: env

/-- Run the instructions, each consing its result onto the front of the
    environment, then read the result index. Index `0` is the most recent
    value, matching the de Bruijn convention of `Ctxt.Var`. -/
def FlatProg.run (p : FlatProg) (env : List Nat) : Nat :=
  (p.instrs.foldl stepFlat env).getD p.ret 0

/-! ## 3. Flattening -/

/-- The de Bruijn index of a variable. -/
def varIdx {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty} :
    Ctxt.Var Γ t → Nat
  | .here => 0
  | .there v => varIdx v + 1

/-- The first two variable indices of an argument vector, whatever its length.
    A nullary vector reports `0` for both; `evalFlatOp` ignores them at
    `const`, the only nullary operation. -/
def idxsOf {Γ : Ctxt natKernelDialect} {tys : List natKernelDialect.Ty} :
    HVector (fun ty => Ctxt.Var Γ ty) tys → Nat × Nat
  | .nil => (0, 0)
  | .cons x .nil => (varIdx x, 0)
  | .cons x (.cons y _) => (varIdx x, varIdx y)

/-- The two argument indices of an expression. -/
def argIdxs {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty}
    (e : Expr natKernelDialect Γ t) : Nat × Nat := idxsOf e.args

/-- The binary arm of `idxsOf`, as an equation a rewrite can use. The matcher
    reduces definitionally but `dsimp` does not expose it, because the
    argument-type list is an index of `HVector`. -/
theorem idxsOf_cons_cons {Γ : Ctxt natKernelDialect}
    {t s : natKernelDialect.Ty} {ts : List natKernelDialect.Ty}
    (x : Ctxt.Var Γ t) (y : Ctxt.Var Γ s)
    (r : HVector (fun ty => Ctxt.Var Γ ty) ts) :
    idxsOf (.cons x (.cons y r)) = (varIdx x, varIdx y) := rfl

/-- The instructions of a program, in binding order. -/
def flattenInstrs {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty} :
    Com natKernelDialect Γ t → List FlatInstr
  | .ret _ => []
  | .var e body =>
      let (a, b) := argIdxs e
      { op := e.op, a := a, b := b } :: flattenInstrs body

/-- The result index of a program, counted in the environment the instructions
    leave behind. -/
def flattenRet {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty} :
    Com natKernelDialect Γ t → Nat
  | .ret v => varIdx v
  | .var _ body => flattenRet body

/-- The flat form of a program. -/
def flatten {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty}
    (c : Com natKernelDialect Γ t) : FlatProg :=
  { instrs := flattenInstrs c, ret := flattenRet c }

/-- The environment a valuation encodes: one `Nat` per binding, most recent
    first. -/
def encEnv : {Γ : Ctxt natKernelDialect} → Ctxt.Valuation Γ → List Nat
  | [], _ => []
  | t :: _, .cons v V => encVal t v :: encEnv V

/-! ## 4. The flat form denotes what the program denotes -/

/-- Reading a variable's index out of the encoded environment gives the encoded
    value the valuation assigns it. -/
theorem encEnv_getD_varIdx {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) :
    (encEnv V).getD (varIdx v) 0 = encVal t (v.lookup V) := by
  induction v with
  | here => cases V with | cons x W => rfl
  | there v ih => cases V with | cons x W => exact ih W

/-- An instruction evaluated against the encoded environment gives the encoded
    value of the expression it came from. -/
theorem evalFlatOp_argIdxs {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty}
    (e : Expr natKernelDialect Γ t) (V : Ctxt.Valuation Γ) :
    evalFlatOp e.op ((encEnv V).getD (argIdxs e).1 0) ((encEnv V).getD (argIdxs e).2 0)
      = encVal t (e.denote V) := by
  rcases e with ⟨op, hr, args⟩
  subst hr
  cases op
  case const n => rfl
  all_goals
    cases args with
    | cons x r =>
      cases r with
      | cons y r2 =>
        cases r2
        have h1 : (encEnv V).getD (varIdx x) 0 = x.lookup V :=
          encEnv_getD_varIdx x V
        have h2 : (encEnv V).getD (varIdx y) 0 = y.lookup V :=
          encEnv_getD_varIdx y V
        have key : ∀ f : Nat → Nat → Nat,
            f ((encEnv V).getD (varIdx x) 0) ((encEnv V).getD (varIdx y) 0)
              = f (x.lookup V) (y.lookup V) := by
          intro f; rw [h1, h2]
        first
          | exact key Nat.add
          | exact key Nat.sub
          | exact key Nat.mul
          | exact key Nat.pow
          | exact key Nat.gcd
          | exact key Nat.mod
          | exact key Nat.div
          | exact key (fun a b => if Nat.beq a b then 1 else 0)
          | exact key (fun a b => if Nat.ble a b then 1 else 0)
          | exact key Nat.land
          | exact key Nat.lor
          | exact key Nat.xor
          | exact key Nat.shiftLeft
          | exact key Nat.shiftRight

/-- The flat form of a program, run on the encoded valuation, gives the encoded
    value of the program's denotation. -/
theorem flatten_run {Γ : Ctxt natKernelDialect} {t : natKernelDialect.Ty}
    (c : Com natKernelDialect Γ t) :
    ∀ V : Ctxt.Valuation Γ, (flatten c).run (encEnv V) = encVal t (c.denote V) := by
  induction c with
  | ret v => intro V; exact encEnv_getD_varIdx v V
  | var e body ih =>
      intro V
      show ((flattenInstrs (.var e body)).foldl stepFlat (encEnv V)).getD
        (flattenRet (.var e body)) 0 = _
      simp only [flattenInstrs, flattenRet, List.foldl_cons, stepFlat]
      have hstep : evalFlatOp e.op ((encEnv V).getD (argIdxs e).1 0)
          ((encEnv V).getD (argIdxs e).2 0) :: encEnv V
          = encEnv (V.extend (e.denote V)) := by
        simp only [Ctxt.Valuation.extend, encEnv, evalFlatOp_argIdxs]
      rw [hstep]
      exact ih (V.extend (e.denote V))

end CatCrypt.Crypto.SecureCompilation.VIR.NatKernel
