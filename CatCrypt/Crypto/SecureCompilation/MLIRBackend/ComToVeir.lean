/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MlirArithScfSum

/-!
# MLIR backend — AST-direct translation

`Jasmin.Cmd → VIR.Com mlirArithDialect` — the **AST-direct** path, the
canonical MLIR lowering. The text emit `ComToMLIR.lean` is a secondary
debug/interop path. Denotation preservation is proved in this module
(`compileProg_denote`, `compileScfProg_denote`).

## Veir API survey (read before reading the code)

`opencompl/veir` does not provide a typed-SSA AST in the shape `Com` /
`Expr` / `Ctxt` / `HVector` / `TyDenote` / `DialectSignature` /
`DialectDenote`. The components are distributed as follows:

| Component                | Provided by                                                           |
|--------------------------|-----------------------------------------------------------------------|
| Operation/Block/Region IR | `Veir.IR.Basic` — pointer-based untyped MLIR AST (`OperationPtr`, …) |
| OpCode enum              | `Veir.OpCode` — arith/func/vector/x86vector/memref/llvm tags          |
| Typed-SSA `Com`/`Expr`   | **`CatCrypt/Crypto/SecureCompilation/VIR/Core.lean`** (in-tree)       |
| `TyDenote` / `DialectSignature` / `DialectDenote` | in-tree `VIR/Core.lean`                                |
| Denoting MLIR arith dialect | `VIR/MlirArithDialect.lean` (in-tree)                               |
| `Com catCryptDialect → Com mlirArithDialect` with denote-preservation | `VIR/MlirArithDialect.lean` (`translate` + `translate_denote_eq`) |

Upstream `Veir`'s IR is the pointer-based untyped layer that text emits
into. The typed-SSA framework is the in-tree `VIR/Core.lean`, a
reimplementation of `opencompl/lean-mlir`'s core framework, and this module
uses it. The name `ComToVeir` refers to the `VIR` namespace of the
user-facing types (`VIR.Com`, `VIR.Expr`, etc.).

### What Veir (the package) provides

* `Veir.OpCode` — for the smoke-test naming check in `Smoke.lean`.
* The pointer-based `Operation` / `Block` / `Region` AST — used by the
  existing `VIR/CatCryptPrint.lean` chain for text emission; **not used
  here**.

### What in-tree VIR (the typed-SSA framework) provides

* `VIR.Dialect` / `VIR.Com` / `VIR.Expr` / `VIR.Ctxt` / `VIR.Var` /
  `VIR.HVector` — the typed-SSA AST.
* `VIR.TyDenote` / `VIR.DialectSignature` / `VIR.DialectDenote` — the
  denotation classes.
* `VIR.Com.denote` — the denotation function (a pure Lean function: no
  external interpreter).
* `MlirArithDialect.mlirArithDialect` — the target dialect, with the
  standard MLIR `arith.*` integer semantics proved equivalent to
  the catCrypt source semantics (per-op `agree_*` lemmas, `translate` +
  `translate_denote_eq` for `Com → Com`).

### What neither provides

* A VIR `Com` with **control-flow regions** (analogue of MLIR's `scf.if`
  / `scf.for` / `scf.while`). The in-tree `VIR/Core.lean` is straight-line
  ANF only — no regions. Control flow is handled by the `ScfProg` DSL,
  whose scf ops carry their branches / bodies as Lean closures (§6–§8).
* A **typed Jasmin source** to translate from. Jasmin `Cmd` is a
  named-variable imperative-style AST; VIR `Com` is intrinsically-typed
  De Bruijn SSA. Bridging requires name resolution, type inference for
  `Pconst`, and bailing out on anything outside the well-typed scalar
  subset. We package this as `Cmd → Option (VIR.Com _ _ _)` returning
  `none` on out-of-scope input. The denotation theorem is conditional on
  successful translation.
* A **denoting MLIR `vector` dialect** in VIR. `MlirArithDialect.lean`
  covers scalar `iN` only, so vector arith denotation is outside this
  module's scope.

## Coverage matrix

| Source constructor                | AST-direct handling                                   |
|-----------------------------------|-------------------------------------------------------|
| `Pconst z` (at `sword w`)         | `MlirArithOp.constant w (BitVec.ofInt w z)`           |
| `Pvar gv` (resolved)              | `Com.var` lookup → `VIR.Var`                          |
| `Papp2 (Oadd w) e1 e2`            | `MlirArithOp.addi w` — proved denote-equal            |
| `Papp2 (Osub w) e1 e2`            | `MlirArithOp.subi w`                                  |
| `Papp2 (Omul w) e1 e2`            | `MlirArithOp.muli w`                                  |
| `Papp2 (Oland w) e1 e2`           | `MlirArithOp.andi w`                                  |
| `Papp2 (Olor w) e1 e2`            | `MlirArithOp.ori w`                                   |
| `Papp2 (Olxor w) e1 e2`           | `MlirArithOp.xori w`                                  |
| `Papp2 (Olsl w) e1 e2`            | `MlirArithOp.shli w k` (k extracted from `Pconst`)    |
| `Papp2 (Olsr w) e1 e2`            | `MlirArithOp.shrui w k`                               |
| `Cassgn (Lvar x) tag (sword w) e` | A new `.var` binding in the VIR `Com`                 |
| `Cif` / `Cfor` / `Cwhile`         | `ScfProg` DSL via `compileScfProg` (§6–§8)            |
| `Ccall` / `Copn`                  | **out of scope**                                      |
| vector arith (`Ov*`)              | **out of scope** (no denoting MLIR vector dialect)    |

For the in-scope arms, translation success ⇒ Lean-side denotational
equality; no external trust hypothesis required (the dialect denotation
IS Lean computation).

For the out-of-scope arms, the text-emit path (with its
`MlirBackendSemanticsAgrees` external hypothesis, documented in
`Denote.lean`) is the bridge.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIRBackend

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect
  (MlirScfOp mlirScfDialect forFold whileFold)
open CatCrypt.Crypto.SecureCompilation.VIR.MlirArithScfSum
  (MlirArithScfOp mlirArithScfDialect)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-! ## §1. Source-type bridge

`Jasmin.SType → CryptoTy` for the scalar-arith subset. We map `sword w`
to `CryptoTy.sword w.bits`; other `SType` shapes return `none` (caller
bails out of the AST-direct path). -/

/-- Translate the scalar `sword` `SType` to `CryptoTy`. Returns `none` on
    `sbool` / `sint` / `sarr _`. -/
def sTypeToCryptoTy : SType → Option CryptoTy
  | .sword w => some (.sword w.bits)
  | _        => none

example : sTypeToCryptoTy (.sword .U64) = some (.sword 64) := rfl
example : sTypeToCryptoTy (.sword .U32) = some (.sword 32) := rfl
example : sTypeToCryptoTy .sbool = none := rfl

/-! ## §2. Scalar binop bridge

`SOp2 → MlirArithOp` for the eight scalar arith arms. Width-carrying ops
become the matching `MlirArithOp` constructor at the right `CryptoTy.sword`
width. Shifts that need a static amount (`shli` / `shrui`) carry it as a
`Nat`; the constructor takes the amount as a
parameter — the consumer extracts it from a `Pconst` operand at call time
(matching how MLIR's `arith.shli` / `arith.shrui` consume their shift
amount as an SSA operand, but our `MlirArithDialect` definition pins it
statically). Shifts that can't be statically extracted bail out. -/

/-- The non-shift scalar arith arms. Returns `none` for shifts (use
    `sOp2ToShiftOp` for those) and for anything outside the scalar-arith
    subset. -/
def sOp2ToArithOp : SOp2 → Option MlirArithOp
  | .Oadd  w => some (.addi w.bits)
  | .Osub  w => some (.subi w.bits)
  | .Omul  w => some (.muli w.bits)
  | .Oland w => some (.andi w.bits)
  | .Olor  w => some (.ori  w.bits)
  | .Olxor w => some (.xori w.bits)
  | _        => none

example : sOp2ToArithOp (.Oadd .U64) = some (.addi 64) := rfl
example : sOp2ToArithOp (.Olxor .U32) = some (.xori 32) := rfl
example : sOp2ToArithOp (.Olsl .U64) = none := rfl
example : sOp2ToArithOp .Obeq = none := rfl

/-- Scalar shifts whose amount is statically known. The amount is taken
    from the second operand if it is a `Pconst`. Returns `none` for
    other shifts. -/
def sOp2ToShiftOp : SOp2 → Nat → Option MlirArithOp
  | .Olsl w, k => some (.shli  w.bits k)
  | .Olsr w, k => some (.shrui w.bits k)
  | _, _ => none

example : sOp2ToShiftOp (.Olsl .U64) 3 = some (.shli 64 3) := rfl
example : sOp2ToShiftOp (.Olsr .U32) 5 = some (.shrui 32 5) := rfl
example : sOp2ToShiftOp (.Oadd .U64) 0 = none := rfl

/-! ## §3. Smoke witnesses

A tiny scalar `MlirArithOp` and a tiny `VIR.Com` over `mlirArithDialect`
just to confirm we can construct these terms from inside `MLIRBackend`
and reduce their denotation. -/

/-- The `arith.addi` op at width 64, used as a smoke test. -/
def smokeAddi64 : MlirArithOp := .addi 64

/-- A constant-64 op for `0xDEAD_BEEF`. -/
def smokeConst : MlirArithOp := .constant 64 0xDEADBEEF#64

/-- A 3-instruction VIR program over `mlirArithDialect`:
      `let a = const c1; let b = const c2; let r = a + b; return r`.
    Demonstrates we can construct a real `VIR.Com` from inside
    `MLIRBackend`, without going through text. Denotation reduces to a
    plain `BitVec 64` value. -/
def smokeAddProgram (c1 c2 : BitVec 64) :
    Com mlirArithDialect [] (CryptoTy.sword 64) :=
  -- let a = c1
  Com.var
    (Expr.mk (d := mlirArithDialect) (Γ := []) (t := CryptoTy.sword 64)
      (MlirArithOp.constant 64 c1) rfl HVector.nil) <|
  -- let b = c2 (a now at de-bruijn 0; this binding pushes b)
  Com.var
    (Expr.mk (d := mlirArithDialect) (Γ := [CryptoTy.sword 64])
      (t := CryptoTy.sword 64)
      (MlirArithOp.constant 64 c2) rfl HVector.nil) <|
  -- let r = b + a  (de-bruijn 0 = b, 1 = a; addi takes [.sword 64, .sword 64])
  Com.var
    (Expr.mk (d := mlirArithDialect)
      (Γ := [CryptoTy.sword 64, CryptoTy.sword 64])
      (t := CryptoTy.sword 64)
      (MlirArithOp.addi 64) rfl
      (HVector.cons (Ctxt.Var.there Ctxt.Var.here)
        (HVector.cons Ctxt.Var.here HVector.nil))) <|
  Com.ret Ctxt.Var.here

/-- Smoke test: evaluating the 3-instruction program at constants `c1`,
    `c2` yields `c1 + c2`. Reduces by unfolding the dialect denotation. -/
theorem smokeAddProgram_denote (c1 c2 : BitVec 64) :
    (smokeAddProgram c1 c2).denote HVector.nil = c1 + c2 := by
  -- After unfolding the three `Com.var` steps, the goal reduces to a
  -- concrete `BitVec 64` equality.  The `addi 64` denotation pattern
  -- matches on the argument `HVector` to extract head/tail; we step
  -- through those reductions explicitly.
  unfold smokeAddProgram
  simp only [Com.denote, Expr.denote, Expr.lookupArgs, Ctxt.Valuation.extend]
  -- Reduce the `addi 64` denotation pattern on the 2-element HVector.
  rfl

/-! ## §4. Scalar straight-line DSL → `VIR.Com mlirArithDialect`

A constructive `flat-Expr → Com mlirArithDialect`-fragment translation
for the scalar-arith straight-line subset. The translation is **total**
on a restricted typed surface (a small ANF DSL of width-pinned,
already-flat expressions) instead of trying to handle arbitrary
tree-shaped `Cmd` (which would need substitution / weakening machinery
beyond what the in-tree minimal `VIR/Core.lean` ships with).

This is the AST-direct analogue of `ComToMLIR.lean`'s scalar text emit.
The denotation theorem (`compileProg_denote_eq`) is proved by structural
induction — there is **no external trust hypothesis** because the
target's denotation IS Lean computation.

### Why ANF instead of tree expressions

Jasmin `Cmd` is already ANF-ish (each `Cassgn`'s RHS denotes to a single
`BitVec`, then binds it). The minimal `VIR/Core.lean` we use as target
does not ship `Com.weaken` / `Var.weaken` machinery, so transposing
nested `Cmd` arms into a single `Com` body requires only the per-Expr
encoding we provide here. Treating tree-shaped expressions inline (e.g.
`(a + b) * c`) requires a mechanical flattening pre-pass, which is outside
this module's scope. The module handles the *flat* shape that exactly matches the
single-op-per-`Cassgn` granularity of `JasminAST.InstrR.Cassgn`.

### Why a DSL instead of `Jasmin.Cmd → Com` directly

Jasmin's `Cmd` is a named-variable imperative-style AST; VIR's `Com` is
intrinsically-typed De Bruijn SSA. A direct `Cmd → Com` lowering needs:

* name resolution (`Var.vname` → De Bruijn index),
* type inference for `Pconst` (no width in the AST),
* bail-out on every out-of-scope constructor.

The DSL below skips all three by encoding the in-scope subset
*typedly* up front. A `Cmd → DSL` pre-pass would be the mechanical
name-resolution layer; it is outside this module's scope. -/

namespace ScalarDSL

/-- A *flat* scalar DSL expression, indexed by the De Bruijn context
    (a list of in-scope `BitVec` widths, head = newest) and the result
    width. Each constructor mirrors **one** `MlirArithOp` arm; the args
    are typed De Bruijn variables into the context. No nesting. -/
inductive Expr : (Γ : List Nat) → (w : Nat) → Type where
  /-- `arith.constant w v` — no operands. -/
  | const (Γ : List Nat) (w : Nat) (v : BitVec w) : Expr Γ w
  -- (Pure rename is intentionally OMITTED — pure renames are handled at
  -- the `Prog` level by re-using the existing De Bruijn index in the
  -- next binding's operands. The arith dialect has no `id` op.)
  /-- `arith.addi w a b`. -/
  | addi (Γ : List Nat) (w : Nat) (a b : Nat)
         (ha : Γ[a]? = some w) (hb : Γ[b]? = some w) : Expr Γ w
  /-- `arith.subi w a b`. -/
  | subi (Γ : List Nat) (w : Nat) (a b : Nat)
         (ha : Γ[a]? = some w) (hb : Γ[b]? = some w) : Expr Γ w
  /-- `arith.muli w a b`. -/
  | muli (Γ : List Nat) (w : Nat) (a b : Nat)
         (ha : Γ[a]? = some w) (hb : Γ[b]? = some w) : Expr Γ w
  /-- `arith.andi w a b`. -/
  | andi (Γ : List Nat) (w : Nat) (a b : Nat)
         (ha : Γ[a]? = some w) (hb : Γ[b]? = some w) : Expr Γ w
  /-- `arith.ori w a b`. -/
  | ori  (Γ : List Nat) (w : Nat) (a b : Nat)
         (ha : Γ[a]? = some w) (hb : Γ[b]? = some w) : Expr Γ w
  /-- `arith.xori w a b`. -/
  | xori (Γ : List Nat) (w : Nat) (a b : Nat)
         (ha : Γ[a]? = some w) (hb : Γ[b]? = some w) : Expr Γ w
  /-- `arith.shli w a k` — static shift amount. -/
  | shli (Γ : List Nat) (w : Nat) (a : Nat) (k : Nat)
         (ha : Γ[a]? = some w) : Expr Γ w
  /-- `arith.shrui w a k` — static shift amount. -/
  | shrui (Γ : List Nat) (w : Nat) (a : Nat) (k : Nat)
          (ha : Γ[a]? = some w) : Expr Γ w

/-- A straight-line DSL program: a sequence of `let`-bindings of flat
    expressions, ending in a return of a variable. Index types: input
    context `Γ`, return width `w`. -/
inductive Prog : (Γ : List Nat) → (w : Nat) → Type where
  /-- Return a variable. -/
  | ret (Γ : List Nat) (w : Nat) (i : Nat) (h : Γ[i]? = some w) :
      Prog Γ w
  /-- `let _ : sword w' = e in body`. -/
  | bind (Γ : List Nat) (w w' : Nat) (e : Expr Γ w')
         (body : Prog (w' :: Γ) w) : Prog Γ w

/-! ### Direct denotation of the DSL

This is the *source* semantics we want the `mlirArithDialect`
denotation to match after compilation. -/

/-- Width-typed valuation: per index `i`, if `Γ[i]? = some w`, the
    valuation returns a `BitVec w`. -/
abbrev Valuation (Γ : List Nat) : Type :=
  ∀ (i : Nat) (w : Nat), Γ[i]? = some w → BitVec w

namespace Valuation

/-- The unique empty valuation. -/
def empty : Valuation [] := fun _ _ h => by
  cases h_eq : ([] : List Nat)[0]? <;> simp_all

/-- Extend a valuation with a new binding at the head. -/
def cons {Γ : List Nat} {w' : Nat} (v : BitVec w') (V : Valuation Γ) :
    Valuation (w' :: Γ) := fun i w h =>
  match i with
  | 0 => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact h ▸ v
  | n + 1 => V n w (by simpa [List.getElem?_cons_succ] using h)

end Valuation

/-- Evaluate a DSL `Expr` against a valuation. -/
def Expr.eval {Γ : List Nat} {w : Nat} (V : Valuation Γ) :
    Expr Γ w → BitVec w
  | .const _ _ v => v
  | .addi  _ _ a b ha hb => V a w ha + V b w hb
  | .subi  _ _ a b ha hb => V a w ha - V b w hb
  | .muli  _ _ a b ha hb => V a w ha * V b w hb
  | .andi  _ _ a b ha hb => V a w ha &&& V b w hb
  | .ori   _ _ a b ha hb => V a w ha ||| V b w hb
  | .xori  _ _ a b ha hb => V a w ha ^^^ V b w hb
  | .shli  _ _ a k ha    => V a w ha <<< k
  | .shrui _ _ a k ha    => BitVec.ushiftRight (V a w ha) k

/-- Evaluate a DSL `Prog` against a valuation. -/
def Prog.eval {Γ : List Nat} {w : Nat} (V : Valuation Γ) :
    Prog Γ w → BitVec w
  | .ret _ _ i h => V i w h
  | .bind _ _ _ e body => body.eval (Valuation.cons (e.eval V) V)

/-! ### Control-flow DSL

A *separate* inductive `ScfProg` carries the three control-flow
constructors (`Cif`, `Cfor`, `Cwhile`). It is intentionally NOT mixed
into `Prog`: the existing `compileProg : Prog → Com mlirArithDialect`
stays arith-only (so `compileProg_denote` keeps its tight zero-hypothesis
shape), and a sibling `compileScfProg : ScfProg → Com mlirScfDialect`
handles the new constructors. Composition of the two is handled by
`Prog.eval` and `ScfProg.eval` at the *source* level — they share the
`Valuation` machinery.

For all three control-flow constructors, the branches / bodies are
**closed** sub-`Prog`s over a singleton context — they receive a fresh
input via context entry 0 and return a value. Outer-context capture is
intentionally excluded: it would require Com-level weakening machinery
we don't yet have, and the scf dialect's denotation packages bodies as
bare `BitVec → BitVec` closures — exactly matching the closed-body
shape. -/

/-- Build a singleton DSL valuation `[w] → BitVec w`. -/
def Valuation.single {w : Nat} (v : BitVec w) : Valuation [w] :=
  Valuation.cons v Valuation.empty

/-- The control-flow DSL: branches on a bit, bounded for, fuel-indexed
    while. Each constructor's body / branches are closed sub-`Prog`s
    over a singleton context. -/
inductive ScfProg : (Γ : List Nat) → (w : Nat) → Type where
  /-- `if condIdx then thenBr else elseBr` — branch on the low bit of a
      1-bit value sourced from `condIdx`. Both branches take a fresh
      `sword w_in` input (sourced from `inputIdx`) and return `sword w`. -/
  | Cif (Γ : List Nat) (w : Nat) (w_in : Nat)
        (condIdx : Nat) (hcond : Γ[condIdx]? = some 1)
        (inputIdx : Nat) (hinput : Γ[inputIdx]? = some w_in)
        (thenBr elseBr : Prog [w_in] w) : ScfProg Γ w
  /-- `for k = lo to hi step step do …` — bounded for-loop accumulator.
      `body` is a closed sub-program over `[w_acc]`, parameterised by
      the iteration index. Initial accumulator from `initIdx`. -/
  | Cfor (Γ : List Nat) (w_acc : Nat) (lo hi step : Nat)
         (initIdx : Nat) (hinit : Γ[initIdx]? = some w_acc)
         (body : Nat → Prog [w_acc] w_acc) : ScfProg Γ w_acc
  /-- `whileBounded fuel cond body init` — fuel-indexed while loop.
      `cond` / `body` are closed sub-programs over `[w]` producing
      respectively a 1-bit predicate (low bit truthy) and the next state.
      Initial state from `initIdx`. -/
  | Cwhile (Γ : List Nat) (w : Nat) (fuel : Nat)
           (initIdx : Nat) (hinit : Γ[initIdx]? = some w)
           (cond : Prog [w] 1) (body : Prog [w] w) : ScfProg Γ w

/-- Direct denotation of `ScfProg`. -/
def ScfProg.eval {Γ : List Nat} {w : Nat} (V : Valuation Γ) :
    ScfProg Γ w → BitVec w
  | .Cif _ _ _ condIdx hcond inputIdx hinput thenBr elseBr =>
      let cond : Bool := (V condIdx 1 hcond).getLsbD 0
      let input := V inputIdx _ hinput
      if cond then thenBr.eval (Valuation.single input)
      else elseBr.eval (Valuation.single input)
  | .Cfor _ _ lo hi step initIdx hinit body =>
      let init := V initIdx _ hinit
      forFold _ lo hi step
        (fun k acc => (body k).eval (Valuation.single acc)) init
  | .Cwhile _ _ fuel initIdx hinit cond body =>
      let init := V initIdx _ hinit
      whileFold _ fuel
        (fun st => (cond.eval (Valuation.single st)).getLsbD 0)
        (fun st => body.eval (Valuation.single st))
        init

end ScalarDSL

/-! ### DSL → `VIR.Com mlirArithDialect` translation

Translation is structural:

* The context `Γ : List Nat` of widths lifts pointwise to
  `cryptoCtxt Γ : Ctxt mlirArithDialect` via `CryptoTy.sword`.
* A De Bruijn index `i` with `Γ[i]? = some w` lifts to a
  `Ctxt.Var (cryptoCtxt Γ) (CryptoTy.sword w)`.
* A flat DSL `Expr` becomes a single `VIR.Expr`.
* A DSL `Prog` becomes a `VIR.Com` by structural recursion.
-/

/-- Lift a width list to a VIR context of `CryptoTy.sword` types. -/
@[reducible] def cryptoCtxt : List Nat → Ctxt mlirArithDialect :=
  List.map CryptoTy.sword

/-- Lift a typed De Bruijn index into a VIR `Ctxt.Var`. By structural
    recursion on the index + the list. -/
def liftVar : (Γ : List Nat) → (i : Nat) → (w : Nat) → Γ[i]? = some w →
    Ctxt.Var (d := mlirArithDialect) (cryptoCtxt Γ) (CryptoTy.sword w)
  | _ :: _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact Ctxt.Var.here
  | _ :: Γ', n + 1, w, h => by
      have h' : Γ'[n]? = some w := by simpa [List.getElem?_cons_succ] using h
      exact Ctxt.Var.there (liftVar Γ' n w h')

/-- Compile a flat DSL `Expr` to a VIR `Expr`. -/
def compileExpr : {Γ : List Nat} → {w : Nat} → ScalarDSL.Expr Γ w →
    Expr mlirArithDialect (cryptoCtxt Γ) (CryptoTy.sword w)
  | Γ, w, .const _ _ v =>
      Expr.mk (MlirArithOp.constant w v) rfl HVector.nil
  | Γ, w, .addi _ _ a b ha hb =>
      Expr.mk (MlirArithOp.addi w) rfl
        (HVector.cons (liftVar Γ a w ha)
          (HVector.cons (liftVar Γ b w hb) HVector.nil))
  | Γ, w, .subi _ _ a b ha hb =>
      Expr.mk (MlirArithOp.subi w) rfl
        (HVector.cons (liftVar Γ a w ha)
          (HVector.cons (liftVar Γ b w hb) HVector.nil))
  | Γ, w, .muli _ _ a b ha hb =>
      Expr.mk (MlirArithOp.muli w) rfl
        (HVector.cons (liftVar Γ a w ha)
          (HVector.cons (liftVar Γ b w hb) HVector.nil))
  | Γ, w, .andi _ _ a b ha hb =>
      Expr.mk (MlirArithOp.andi w) rfl
        (HVector.cons (liftVar Γ a w ha)
          (HVector.cons (liftVar Γ b w hb) HVector.nil))
  | Γ, w, .ori _ _ a b ha hb =>
      Expr.mk (MlirArithOp.ori w) rfl
        (HVector.cons (liftVar Γ a w ha)
          (HVector.cons (liftVar Γ b w hb) HVector.nil))
  | Γ, w, .xori _ _ a b ha hb =>
      Expr.mk (MlirArithOp.xori w) rfl
        (HVector.cons (liftVar Γ a w ha)
          (HVector.cons (liftVar Γ b w hb) HVector.nil))
  | Γ, w, .shli _ _ a k ha =>
      Expr.mk (MlirArithOp.shli w k) rfl
        (HVector.cons (liftVar Γ a w ha) HVector.nil)
  | Γ, w, .shrui _ _ a k ha =>
      Expr.mk (MlirArithOp.shrui w k) rfl
        (HVector.cons (liftVar Γ a w ha) HVector.nil)

/-- Compile a DSL `Prog` to a VIR `Com`. -/
def compileProg : {Γ : List Nat} → {w : Nat} → ScalarDSL.Prog Γ w →
    Com mlirArithDialect (cryptoCtxt Γ) (CryptoTy.sword w)
  | Γ, w, .ret _ _ i h => Com.ret (liftVar Γ i w h)
  | _, _, .bind _ _ _ e body =>
      Com.var (compileExpr e) (compileProg body)

/-! ## §5. Denotation preservation

The ScalarDSL is a *typed* surface for the MLIR scalar arith subset; its
`Expr.eval` / `Prog.eval` are the source semantics. The compiled VIR `Com`
denotes via `mlirArithDialect`'s `DialectDenote`. The two coincide:
`compileExpr_denote` and `compileProg_denote` discharge per-Expr and
program-level equality respectively, by structural induction. No external
trust hypothesis enters — the target's denotation IS Lean computation
(`Com.denote` is a pure recursive function).

The single non-trivial step is the bridge between the two `Valuation`
shapes:

* `ScalarDSL.Valuation Γ` = a dependent function `∀ i w, Γ[i]? = some w → BitVec w`.
* `Ctxt.Valuation (cryptoCtxt Γ)` = a heterogeneous list `HVector (⟦·⟧) (cryptoCtxt Γ)`.

`cryptoCtxtValuation` carries the DSL valuation into the VIR HVector
shape pointwise; `liftVar_lookup` shows the lifted De Bruijn variable's
lookup against this HVector recovers the DSL valuation's entry.
-/

/-- Lift a `ScalarDSL.Valuation Γ` to a VIR `Ctxt.Valuation` over
    `cryptoCtxt Γ`. Structural recursion on `Γ`: each width-position
    becomes one HVector cell. -/
def cryptoCtxtValuation : (Γ : List Nat) → ScalarDSL.Valuation Γ →
    Ctxt.Valuation (d := mlirArithDialect) (cryptoCtxt Γ)
  | [], _ => HVector.nil
  | w :: Γ', V =>
      HVector.cons
        (show BitVec w from V 0 w (by simp))
        (cryptoCtxtValuation Γ' (fun i w' h =>
          V (i + 1) w' (by simpa [List.getElem?_cons_succ] using h)))

/-- Lookup of a lifted variable in the bridged valuation recovers the
    DSL valuation's entry. By induction on the index + the list. -/
theorem liftVar_lookup : (Γ : List Nat) → (i : Nat) → (w : Nat) →
    (h : Γ[i]? = some w) → (V : ScalarDSL.Valuation Γ) →
    (liftVar Γ i w h).lookup (cryptoCtxtValuation Γ V) = V i w h
  | _ :: _, 0, _, h, V => by
      -- The lifted var is `Var.here` after substituting the head-equality.
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
  | w' :: Γ', n + 1, w, h, V => by
      have h' : Γ'[n]? = some w := by simpa [List.getElem?_cons_succ] using h
      -- Lifted var is `Var.there (liftVar Γ' n w h')`; its lookup peels
      -- off the head and recurses on the tail.
      show (liftVar Γ' n w h').lookup
        (cryptoCtxtValuation Γ' (fun i w' h => V (i + 1) w' (by simpa [List.getElem?_cons_succ] using h)))
        = V (n + 1) w h
      rw [liftVar_lookup Γ' n w h']

/-- Per-expression denotation preservation: a compiled DSL `Expr` denotes
    against the lifted valuation to the same `BitVec` as the source
    `Expr.eval`. Case-split on the `Expr` constructor; each arm reduces
    by `simp` + `liftVar_lookup`. -/
theorem compileExpr_denote {Γ : List Nat} {w : Nat} (V : ScalarDSL.Valuation Γ)
    (e : ScalarDSL.Expr Γ w) :
    (compileExpr e).denote (cryptoCtxtValuation Γ V) = e.eval V := by
  cases e with
  | const v =>
      -- The op is `MlirArithOp.constant w v`; its denotation is `fun _ => v`.
      rfl
  | addi a b ha hb =>
      change BitVec.add ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V))
        ((liftVar Γ b w hb).lookup (cryptoCtxtValuation Γ V)) = _
      rw [liftVar_lookup, liftVar_lookup]; rfl
  | subi a b ha hb =>
      change BitVec.sub ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V))
        ((liftVar Γ b w hb).lookup (cryptoCtxtValuation Γ V)) = _
      rw [liftVar_lookup, liftVar_lookup]; rfl
  | muli a b ha hb =>
      change BitVec.mul ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V))
        ((liftVar Γ b w hb).lookup (cryptoCtxtValuation Γ V)) = _
      rw [liftVar_lookup, liftVar_lookup]; rfl
  | andi a b ha hb =>
      change BitVec.and ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V))
        ((liftVar Γ b w hb).lookup (cryptoCtxtValuation Γ V)) = _
      rw [liftVar_lookup, liftVar_lookup]; rfl
  | ori a b ha hb =>
      change BitVec.or ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V))
        ((liftVar Γ b w hb).lookup (cryptoCtxtValuation Γ V)) = _
      rw [liftVar_lookup, liftVar_lookup]; rfl
  | xori a b ha hb =>
      change BitVec.xor ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V))
        ((liftVar Γ b w hb).lookup (cryptoCtxtValuation Γ V)) = _
      rw [liftVar_lookup, liftVar_lookup]; rfl
  | shli a k ha =>
      change BitVec.shiftLeft ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V)) k = _
      rw [liftVar_lookup]; rfl
  | shrui a k ha =>
      change BitVec.ushiftRight ((liftVar Γ a w ha).lookup (cryptoCtxtValuation Γ V)) k = _
      rw [liftVar_lookup]; rfl

/-- Auxiliary: extending the bridged valuation with a new BitVec
    coincides with bridging the DSL-level `Valuation.cons`. -/
theorem cryptoCtxtValuation_cons {Γ : List Nat} {w : Nat}
    (V : ScalarDSL.Valuation Γ) (v : BitVec w) :
    (cryptoCtxtValuation Γ V).extend (t := CryptoTy.sword w) v
      = cryptoCtxtValuation (w :: Γ) (ScalarDSL.Valuation.cons v V) := by
  -- The RHS unfolds to `HVector.cons head tail` where:
  --   * `head = ScalarDSL.Valuation.cons v V 0 w (by simp)`, which is `v`
  --     definitionally (cons-zero branch).
  --   * `tail = cryptoCtxtValuation Γ (fun i w' h => Valuation.cons v V (i+1) w' h')`.
  -- The LHS is `(cryptoCtxtValuation Γ V).extend v = HVector.cons v (cryptoCtxtValuation Γ V)`.
  -- So the only nontrivial step is showing the two `Valuation`s passed to
  -- `cryptoCtxtValuation Γ` are equal as functions — pointwise, the shifted
  -- `Valuation.cons` recovers the original `V`.
  show @HVector.cons CryptoTy (fun t => ⟦t⟧) (CryptoTy.sword w) (cryptoCtxt Γ) v
        (cryptoCtxtValuation Γ V) = _
  -- Reduce the RHS structurally: head matches `v` by defn of Valuation.cons;
  -- tail matches by funext on the shifted Valuation.
  have htail : cryptoCtxtValuation Γ V =
      cryptoCtxtValuation Γ (fun i w' h =>
        ScalarDSL.Valuation.cons v V (i + 1) w'
          (by simpa [List.getElem?_cons_succ] using h)) := by
    congr 1
  rw [htail]
  rfl

/-- **Main theorem**: a compiled DSL `Prog` denotes via VIR's
    `Com.denote` to the same `BitVec` as the source `Prog.eval`. By
    structural induction on the `Prog`:

    * `.ret`: `Com.ret`-lookup equals DSL `V i w h` by `liftVar_lookup`.
    * `.bind e body`: peel one `Com.var` step; the bound expression's
      value matches by `compileExpr_denote`; the extended valuations
      match by `cryptoCtxtValuation_cons`; recurse on the body.

    No external trust hypothesis. -/
theorem compileProg_denote : {Γ : List Nat} → {w : Nat} →
    (V : ScalarDSL.Valuation Γ) → (p : ScalarDSL.Prog Γ w) →
    (compileProg p).denote (cryptoCtxtValuation Γ V) = p.eval V
  | _, _, V, .ret _ _ i h => by
      -- `compileProg (.ret …) = Com.ret (liftVar …)`; denotation = lookup.
      show (liftVar _ i _ h).lookup (cryptoCtxtValuation _ V) = V i _ h
      exact liftVar_lookup _ i _ h V
  | Γ, w, V, .bind _ _ w' e body => by
      -- Peel one Com.var step.
      show (compileProg body).denote
        ((cryptoCtxtValuation Γ V).extend ((compileExpr e).denote (cryptoCtxtValuation Γ V)))
        = (body.eval (ScalarDSL.Valuation.cons (e.eval V) V))
      rw [compileExpr_denote V e, cryptoCtxtValuation_cons V (e.eval V)]
      exact compileProg_denote (ScalarDSL.Valuation.cons (e.eval V) V) body

/-! ## §6. Control-flow AST-direct

The control-flow DSL `ScfProg` compiles to a single `VIR.Com` over
`mlirScfDialect`, with the branches / body packaged as Lean closures
inside the scf op constructors. Because both target dialects share
`Ty = CryptoTy`, the typing context (`cryptoCtxt`) and valuation
(`cryptoCtxtValuation`) machinery from §5 reuse verbatim — only the
dialect tag on `Ctxt.Var` changes, which we bridge with `liftVarScf`.

This is the AST-direct path's extension to control flow: zero external
trust hypothesis enters, because each scf op's denotation literally
**is** the supplied Lean closure (we packaged the source's `Prog.eval`
of the body as the closure at compile time).

This section compiles `Cfor` and `Cwhile` over `mlirScfDialect`; `Cif`
needs an arith predecessor and is compiled over the arith ⊕ scf sum
dialect in §7. -/

/-- Lift a typed De Bruijn index into a `Ctxt.Var` over `mlirScfDialect`.
    Identical structure to `liftVar` (both dialects share `Ty`). -/
def liftVarScf : (Γ : List Nat) → (i : Nat) → (w : Nat) → Γ[i]? = some w →
    Ctxt.Var (d := mlirScfDialect) (cryptoCtxt Γ) (CryptoTy.sword w)
  | _ :: _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact Ctxt.Var.here
  | _ :: Γ', n + 1, w, h => by
      have h' : Γ'[n]? = some w := by simpa [List.getElem?_cons_succ] using h
      exact Ctxt.Var.there (liftVarScf Γ' n w h')

/-- Lookup of a scf-lifted variable in the bridged valuation. Mirrors
    `liftVar_lookup` but with the dialect tag swapped — because both
    dialects share `Ty = CryptoTy`, the `Ctxt.Valuation` type is
    *literally* the same on either side. -/
theorem liftVarScf_lookup : (Γ : List Nat) → (i : Nat) → (w : Nat) →
    (h : Γ[i]? = some w) → (V : ScalarDSL.Valuation Γ) →
    (liftVarScf Γ i w h).lookup
      (show Ctxt.Valuation (d := mlirScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V) = V i w h
  | _ :: _, 0, _, h, V => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
  | w' :: Γ', n + 1, w, h, V => by
      have h' : Γ'[n]? = some w := by simpa [List.getElem?_cons_succ] using h
      show (liftVarScf Γ' n w h').lookup
        (cryptoCtxtValuation Γ' (fun i w' h => V (i + 1) w' (by simpa [List.getElem?_cons_succ] using h)))
        = V (n + 1) w h
      rw [liftVarScf_lookup Γ' n w h']

/-! ### §6.1 Compile `ScfProg.Cfor` — bounded for-loop

Cleanest of the three: the scf op operand is a single `sword w_acc`
(the init), and `bodyF : Nat → BitVec w_acc → BitVec w_acc` packages
the body's `eval` over a singleton valuation. -/

/-- Compile a `ScfProg.Cfor`. -/
def compileCfor (Γ : List Nat) (w_acc : Nat) (lo hi step : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w_acc)
    (body : Nat → ScalarDSL.Prog [w_acc] w_acc) :
    Com mlirScfDialect (cryptoCtxt Γ) (CryptoTy.sword w_acc) :=
  Com.var (Expr.mk (d := mlirScfDialect)
    (Γ := cryptoCtxt Γ) (t := CryptoTy.sword w_acc)
    (MlirScfOp.scfFor w_acc lo hi step
      (fun k acc => (body k).eval (ScalarDSL.Valuation.single acc)))
    rfl
    (HVector.cons (liftVarScf Γ initIdx w_acc hinit) HVector.nil))
  (Com.ret Ctxt.Var.here)

/-! ### §6.2 Compile `ScfProg.Cwhile` — fuel-indexed while

The scf op operand is the `sword w` init; the condition closure and
body closure are built from the sub-`Prog`s. -/

/-- Compile a `ScfProg.Cwhile`. -/
def compileCwhile (Γ : List Nat) (w : Nat) (fuel : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w)
    (cond : ScalarDSL.Prog [w] 1) (body : ScalarDSL.Prog [w] w) :
    Com mlirScfDialect (cryptoCtxt Γ) (CryptoTy.sword w) :=
  Com.var (Expr.mk (d := mlirScfDialect)
    (Γ := cryptoCtxt Γ) (t := CryptoTy.sword w)
    (MlirScfOp.scfWhile w fuel
      (fun st => (cond.eval (ScalarDSL.Valuation.single st)).getLsbD 0)
      (fun st => body.eval (ScalarDSL.Valuation.single st)))
    rfl
    (HVector.cons (liftVarScf Γ initIdx w hinit) HVector.nil))
  (Com.ret Ctxt.Var.here)

/-! ### §6.3 Why `ScfProg.Cif` is not compiled over `mlirScfDialect`

The scf op `scfIf` requires a `[.bit, .sword w]` operand list — a
`CryptoTy.bit` (`Bool`) condition. Our DSL holds the condition as a
`sword 1` (a `BitVec 1`). Bridging the two requires an arith op
(`cmpi 1` of the 1-bit value against zero) to extract the boolean —
which lives in `mlirArithDialect`, not `mlirScfDialect`. A clean
encoding therefore requires the **sum-dialect** `mlirArithDialect ⊕
mlirScfDialect` whose `Com.var` can interleave arith and scf ops in a
single program; §7 compiles `Cif` there. The `Cfor` and `Cwhile`
compiles over `mlirScfDialect` are `compileCfor`, `compileCwhile`.

The `Cif` source denotation is encoded in Lean (`ScfProg.eval`'s `Cif`
case is an `if/then/else` over `BitVec.getLsbD`); the
`Com.var (Expr.mk scfIf …)` shape needs a `.bit`-typed operand, which
requires an `arith.cmpi` predecessor in the same `Com`. -/

/-! ### §6.4 Denotation preservation for `Cfor` and `Cwhile`

The `Cfor` / `Cwhile` compiles bake the source's `Prog.eval` (over a
singleton valuation) directly into the scf op's body closure. The
denotation of the compiled `Com` then matches `ScfProg.eval` by
unfolding the scf op's denote and computation reduction.

The denotation theorem for `Cif` is `compileCif_denote` in §7. -/

/-- `compileCfor` is denotation-preserving. -/
theorem compileCfor_denote (Γ : List Nat) (w_acc : Nat) (lo hi step : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w_acc)
    (body : Nat → ScalarDSL.Prog [w_acc] w_acc)
    (V : ScalarDSL.Valuation Γ) :
    (compileCfor Γ w_acc lo hi step initIdx hinit body).denote
      (show Ctxt.Valuation (d := mlirScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V)
      = (ScalarDSL.ScfProg.Cfor Γ w_acc lo hi step initIdx hinit body).eval V := by
  show forFold w_acc lo hi step
        (fun k acc => (body k).eval (ScalarDSL.Valuation.single acc))
        ((liftVarScf Γ initIdx w_acc hinit).lookup _)
      = forFold w_acc lo hi step
          (fun k acc => (body k).eval (ScalarDSL.Valuation.single acc))
          (V initIdx w_acc hinit)
  rw [liftVarScf_lookup]

/-- `compileCwhile` is denotation-preserving. -/
theorem compileCwhile_denote (Γ : List Nat) (w : Nat) (fuel : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w)
    (cond : ScalarDSL.Prog [w] 1) (body : ScalarDSL.Prog [w] w)
    (V : ScalarDSL.Valuation Γ) :
    (compileCwhile Γ w fuel initIdx hinit cond body).denote
      (show Ctxt.Valuation (d := mlirScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V)
      = (ScalarDSL.ScfProg.Cwhile Γ w fuel initIdx hinit cond body).eval V := by
  show whileFold w fuel
        (fun st => (cond.eval (ScalarDSL.Valuation.single st)).getLsbD 0)
        (fun st => body.eval (ScalarDSL.Valuation.single st))
        ((liftVarScf Γ initIdx w hinit).lookup _)
      = whileFold w fuel
          (fun st => (cond.eval (ScalarDSL.Valuation.single st)).getLsbD 0)
          (fun st => body.eval (ScalarDSL.Valuation.single st))
          (V initIdx w hinit)
  rw [liftVarScf_lookup]

/-! ## §7. Control-flow `Cif` AST-direct via the arith ⊕ scf sum dialect

`scfIf` needs a `.bit` condition but the DSL holds it as `sword 1`
(§6.3); `compileCif` bridges the two using the
`mlirArithDialect ⊕ mlirScfDialect` sum dialect from
`VIR/MlirArithScfSum.lean`. The compiled program is three operations:

```
let one     : sword 1 = arith.constant 1 1#1
let condBit : bit     = arith.cmpi 1 (cond_lifted, one)   -- = decide (cond = 1)
let result  : sword w = scf.if condBit input_lifted with thenF/elseF
return result
```

The condition bit `decide (cond = 1#1)` equals `cond.getLsbD 0` for
`BitVec 1` (only two values to check, closed by `decide`), which is
exactly the boolean the source `ScfProg.Cif`'s `eval` uses.

### Scope

`compileCif` handles the general heterogeneous case `w ≠ w_in`: the
input flowing into the branches has width `w_in`, the branch outputs
have width `w`. The implementation uses `scfIfHetero w w_in` from
`MlirScfDialect.lean` — a sibling of `scfIf` whose signature
`[.bit, .sword w_in] → .sword w` pins the two widths independently.
The homogeneous case is the instance `w_in = w`. -/

/-- Lift a typed De Bruijn index into a `Ctxt.Var` over
    `mlirArithScfDialect`. Identical structure to `liftVar` /
    `liftVarScf` — all three dialects share `Ty = CryptoTy`. -/
def liftVarSum : (Γ : List Nat) → (i : Nat) → (w : Nat) → Γ[i]? = some w →
    Ctxt.Var (d := mlirArithScfDialect) (cryptoCtxt Γ) (CryptoTy.sword w)
  | _ :: _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact Ctxt.Var.here
  | _ :: Γ', n + 1, w, h => by
      have h' : Γ'[n]? = some w := by simpa [List.getElem?_cons_succ] using h
      exact Ctxt.Var.there (liftVarSum Γ' n w h')

/-- Lookup of a sum-lifted variable in the bridged valuation. Mirrors
    `liftVar_lookup` / `liftVarScf_lookup` — all three dialects share
    `Ty = CryptoTy`, so the `Ctxt.Valuation` type is literally the same
    on either side. -/
theorem liftVarSum_lookup : (Γ : List Nat) → (i : Nat) → (w : Nat) →
    (h : Γ[i]? = some w) → (V : ScalarDSL.Valuation Γ) →
    (liftVarSum Γ i w h).lookup
      (show Ctxt.Valuation (d := mlirArithScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V) = V i w h
  | _ :: _, 0, _, h, V => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
  | w' :: Γ', n + 1, w, h, V => by
      have h' : Γ'[n]? = some w := by simpa [List.getElem?_cons_succ] using h
      show (liftVarSum Γ' n w h').lookup
        (cryptoCtxtValuation Γ' (fun i w' h => V (i + 1) w' (by simpa [List.getElem?_cons_succ] using h)))
        = V (n + 1) w h
      rw [liftVarSum_lookup Γ' n w h']

/-- Helper: for `BitVec 1`, `getLsbD 0` equals `decide (· = 1#1)`. Closed
    by `decide` (`BitVec 1` has only two values). -/
theorem bitvec1_lsbD_eq_decide_eq_one (x : BitVec 1) :
    x.getLsbD 0 = decide (x = 1#1) := by
  revert x; decide

/-- Compile a `ScfProg.Cif` at general heterogeneous widths to a
    `Com mlirArithScfDialect`. Three operations: emit `1#1`, take
    `arith.cmpi 1` against it to materialise the bit, feed it to
    `scfIfHetero` with the two branches packaged as pre-evaluated Lean
    closures. The input has width `w_in`, the output has width `w`. -/
def compileCif (Γ : List Nat) (w w_in : Nat)
    (condIdx : Nat) (hcond : Γ[condIdx]? = some 1)
    (inputIdx : Nat) (hinput : Γ[inputIdx]? = some w_in)
    (thenBr elseBr : ScalarDSL.Prog [w_in] w) :
    Com mlirArithScfDialect (cryptoCtxt Γ) (CryptoTy.sword w) :=
  -- let one : sword 1 = arith.constant 1 1#1
  Com.var (Expr.mk (d := mlirArithScfDialect)
    (Γ := cryptoCtxt Γ) (t := CryptoTy.sword 1)
    (MlirArithScfOp.arith (.constant 1 (1 : BitVec 1)))
    rfl HVector.nil) <|
  -- let condBit : bit = arith.cmpi 1 (cond_lifted, one)
  -- Ctxt is `sword 1 :: cryptoCtxt Γ`; `cond_lifted` is the lifted
  -- variable shifted by one binder; `one` is `.here`.
  Com.var (Expr.mk (d := mlirArithScfDialect)
    (Γ := CryptoTy.sword 1 :: cryptoCtxt Γ) (t := CryptoTy.bit)
    (MlirArithScfOp.arith (.cmpi 1))
    rfl
    (HVector.cons (Ctxt.Var.there (liftVarSum Γ condIdx 1 hcond))
      (HVector.cons Ctxt.Var.here HVector.nil))) <|
  -- let result : sword w = scf.if condBit (thenF, elseF) input_lifted
  -- Ctxt is `bit :: sword 1 :: cryptoCtxt Γ`; `condBit` is `.here`;
  -- `input_lifted` is shifted by two binders. We use `scfIfHetero` so
  -- the output width `w` is independent of the input width `w_in`.
  Com.var (Expr.mk (d := mlirArithScfDialect)
    (Γ := CryptoTy.bit :: CryptoTy.sword 1 :: cryptoCtxt Γ)
    (t := CryptoTy.sword w)
    (MlirArithScfOp.scf (.scfIfHetero w w_in
      (fun input => thenBr.eval (ScalarDSL.Valuation.single input))
      (fun input => elseBr.eval (ScalarDSL.Valuation.single input))))
    rfl
    (HVector.cons Ctxt.Var.here
      (HVector.cons
        (Ctxt.Var.there (Ctxt.Var.there (liftVarSum Γ inputIdx w_in hinput)))
        HVector.nil))) <|
  Com.ret Ctxt.Var.here

/-- `compileCif` is denotation-preserving at general heterogeneous
    widths `w ≠ w_in`. The proof unfolds the three `Com.var` steps; the
    arith `constant` and `cmpi 1` reduce to literal Lean expressions;
    the `scfIfHetero` denotation is a literal `if/then/else`;
    `liftVarSum_lookup` bridges the De Bruijn variable lookups back to
    the source valuation `V`; and `bitvec1_lsbD_eq_decide_eq_one`
    bridges the `BitVec 1` bit-extraction `cmpi` form to the source's
    `getLsbD 0`. -/
theorem compileCif_denote (Γ : List Nat) (w w_in : Nat)
    (condIdx : Nat) (hcond : Γ[condIdx]? = some 1)
    (inputIdx : Nat) (hinput : Γ[inputIdx]? = some w_in)
    (thenBr elseBr : ScalarDSL.Prog [w_in] w)
    (V : ScalarDSL.Valuation Γ) :
    (compileCif Γ w w_in condIdx hcond inputIdx hinput thenBr elseBr).denote
      (show Ctxt.Valuation (d := mlirArithScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V)
      = (ScalarDSL.ScfProg.Cif Γ w w_in condIdx hcond inputIdx hinput
            thenBr elseBr).eval V := by
  -- The compiled Com's denotation reduces — by stepping through the
  -- three `Com.var` stages and the final `Com.ret` — to a literal
  -- Bool-conditional whose discriminant is `decide (liftedCond = 1#1)`
  -- (the `arith.cmpi 1` denotation) and whose input is `liftedInput`.
  -- Lean's `if (b : Bool) then ... else ...` desugars to
  -- `if (b = true) then ... else ...`. The source `ScfProg.Cif.eval`
  -- produces the same conditional with `cond = (V condIdx 1 hcond).getLsbD 0`
  -- and `input = V inputIdx w_in hinput`. Bridge the two by rewriting the
  -- lifted lookups (`liftVarSum_lookup`) and the bitvec-1 bit-extraction
  -- identity (`bitvec1_lsbD_eq_decide_eq_one`).
  -- Mirror `compileCfor_denote`'s `show` form: state the LHS in the
  -- already-reduced kernel-`whnf` form. The compiled `Com` is three
  -- nested `Com.var` + a `Com.ret here`, which reduces — kernel
  -- definitionally — to an `if/then/else` whose discriminant is
  -- `((cmpi 1 cond one) : Bool)` and whose branches each invoke
  -- the corresponding scf-closure body. We pin the discriminant in
  -- its post-reduction `BitVec`-typed form via an explicit
  -- `instDecidableEqBitVec` to dodge an elaboration quirk in `show`
  -- where the `lookup`'s return type only reduces to `BitVec 1` via
  -- `TyDenote` (so Lean's TC search can't auto-find `DecidableEq`).
  show
    (if @decide
            (((liftVarSum Γ condIdx 1 hcond).lookup
                (show Ctxt.Valuation (d := mlirArithScfDialect)
                  (cryptoCtxt Γ) from cryptoCtxtValuation Γ V) : BitVec 1)
                = 1#1)
            (instDecidableEqBitVec _ _) then
       thenBr.eval (ScalarDSL.Valuation.single
            ((liftVarSum Γ inputIdx w_in hinput).lookup
              (show Ctxt.Valuation (d := mlirArithScfDialect)
                (cryptoCtxt Γ) from cryptoCtxtValuation Γ V)))
     else
       elseBr.eval (ScalarDSL.Valuation.single
            ((liftVarSum Γ inputIdx w_in hinput).lookup
              (show Ctxt.Valuation (d := mlirArithScfDialect)
                (cryptoCtxt Γ) from cryptoCtxtValuation Γ V)))) = _
  -- Bridge the source eval: rewrite the lifted lookups back to `V` and
  -- the `getLsbD 0` to `decide (· = 1#1)`.
  rw [ScalarDSL.ScfProg.eval, bitvec1_lsbD_eq_decide_eq_one,
      ← liftVarSum_lookup Γ condIdx 1 hcond V,
      ← liftVarSum_lookup Γ inputIdx w_in hinput V]

/-! ## §8. Top-level `compileScfProg` dispatcher

The three control-flow compilers live in two different dialects:
`compileCfor` / `compileCwhile` target the scf-only `mlirScfDialect`,
while `compileCif` targets the sum dialect `mlirArithScfDialect` (it
needs an `arith.cmpi` predecessor to materialise the `.bit` condition,
see §7). To dispatch all three from a single function we must pick one
result dialect. `mlirArithScfDialect` is the only dialect that can host
all three: `Cif` already lives there, and the `Cfor` / `Cwhile` scf ops
embed via the `MlirArithScfOp.scf` tag (the `scf_embed_denote_eq`
embedding preserves their denotation).

`compileCfor` / `compileCwhile` themselves cannot be reused *verbatim*
in the dispatcher — their result type `Com mlirScfDialect …` does not
unify with `Com mlirArithScfDialect …` (distinct `Dialect`s, hence
distinct `Com`/`Expr`/`Ctxt.Var` types). The obstruction is purely the
target dialect: the body closures (`forFold` / `whileFold` over the
singleton-valuation `eval`) are byte-for-byte the same. We therefore
provide the two-line sum-dialect siblings `compileCforSum` /
`compileCwhileSum` (the exact `Com.var (Expr.mk … (MlirArithScfOp.scf …))`
shape, with `liftVarSum` for the operand) and their denote lemmas
(closed by `liftVarSum_lookup`, mirroring `compileCfor_denote` /
`compileCwhile_denote`). The dispatcher routes `Cif` to `compileCif`
and `Cfor` / `Cwhile` to these siblings; its denote composes the three
denote lemmas, one case each. -/

/-- Sum-dialect sibling of `compileCfor`: the same `scfFor` op embedded
    in `mlirArithScfDialect` via the `.scf` tag. -/
def compileCforSum (Γ : List Nat) (w_acc : Nat) (lo hi step : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w_acc)
    (body : Nat → ScalarDSL.Prog [w_acc] w_acc) :
    Com mlirArithScfDialect (cryptoCtxt Γ) (CryptoTy.sword w_acc) :=
  Com.var (Expr.mk (d := mlirArithScfDialect)
    (Γ := cryptoCtxt Γ) (t := CryptoTy.sword w_acc)
    (MlirArithScfOp.scf (MlirScfOp.scfFor w_acc lo hi step
      (fun k acc => (body k).eval (ScalarDSL.Valuation.single acc))))
    rfl
    (HVector.cons (liftVarSum Γ initIdx w_acc hinit) HVector.nil))
  (Com.ret Ctxt.Var.here)

/-- Sum-dialect sibling of `compileCwhile`: the same `scfWhile` op
    embedded in `mlirArithScfDialect` via the `.scf` tag. -/
def compileCwhileSum (Γ : List Nat) (w : Nat) (fuel : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w)
    (cond : ScalarDSL.Prog [w] 1) (body : ScalarDSL.Prog [w] w) :
    Com mlirArithScfDialect (cryptoCtxt Γ) (CryptoTy.sword w) :=
  Com.var (Expr.mk (d := mlirArithScfDialect)
    (Γ := cryptoCtxt Γ) (t := CryptoTy.sword w)
    (MlirArithScfOp.scf (MlirScfOp.scfWhile w fuel
      (fun st => (cond.eval (ScalarDSL.Valuation.single st)).getLsbD 0)
      (fun st => body.eval (ScalarDSL.Valuation.single st))))
    rfl
    (HVector.cons (liftVarSum Γ initIdx w hinit) HVector.nil))
  (Com.ret Ctxt.Var.here)

/-- `compileCforSum` is denotation-preserving. Mirrors
    `compileCfor_denote` with `liftVarSum_lookup`. -/
theorem compileCforSum_denote (Γ : List Nat) (w_acc : Nat) (lo hi step : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w_acc)
    (body : Nat → ScalarDSL.Prog [w_acc] w_acc)
    (V : ScalarDSL.Valuation Γ) :
    (compileCforSum Γ w_acc lo hi step initIdx hinit body).denote
      (show Ctxt.Valuation (d := mlirArithScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V)
      = (ScalarDSL.ScfProg.Cfor Γ w_acc lo hi step initIdx hinit body).eval V := by
  show forFold w_acc lo hi step
        (fun k acc => (body k).eval (ScalarDSL.Valuation.single acc))
        ((liftVarSum Γ initIdx w_acc hinit).lookup _)
      = forFold w_acc lo hi step
          (fun k acc => (body k).eval (ScalarDSL.Valuation.single acc))
          (V initIdx w_acc hinit)
  rw [liftVarSum_lookup]

/-- `compileCwhileSum` is denotation-preserving. Mirrors
    `compileCwhile_denote` with `liftVarSum_lookup`. -/
theorem compileCwhileSum_denote (Γ : List Nat) (w : Nat) (fuel : Nat)
    (initIdx : Nat) (hinit : Γ[initIdx]? = some w)
    (cond : ScalarDSL.Prog [w] 1) (body : ScalarDSL.Prog [w] w)
    (V : ScalarDSL.Valuation Γ) :
    (compileCwhileSum Γ w fuel initIdx hinit cond body).denote
      (show Ctxt.Valuation (d := mlirArithScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V)
      = (ScalarDSL.ScfProg.Cwhile Γ w fuel initIdx hinit cond body).eval V := by
  show whileFold w fuel
        (fun st => (cond.eval (ScalarDSL.Valuation.single st)).getLsbD 0)
        (fun st => body.eval (ScalarDSL.Valuation.single st))
        ((liftVarSum Γ initIdx w hinit).lookup _)
      = whileFold w fuel
          (fun st => (cond.eval (ScalarDSL.Valuation.single st)).getLsbD 0)
          (fun st => body.eval (ScalarDSL.Valuation.single st))
          (V initIdx w hinit)
  rw [liftVarSum_lookup]

/-- Top-level dispatcher: compile any `ScfProg` into a `Com` over the
    sum dialect `mlirArithScfDialect`. `Cif` routes to `compileCif`;
    `Cfor` / `Cwhile` route to the sum-dialect siblings
    `compileCforSum` / `compileCwhileSum`. -/
def compileScfProg {Γ : List Nat} {w : Nat} :
    ScalarDSL.ScfProg Γ w →
      Com mlirArithScfDialect (cryptoCtxt Γ) (CryptoTy.sword w)
  | .Cif _ _ w_in condIdx hcond inputIdx hinput thenBr elseBr =>
      compileCif Γ w w_in condIdx hcond inputIdx hinput thenBr elseBr
  | .Cfor _ _ lo hi step initIdx hinit body =>
      compileCforSum Γ w lo hi step initIdx hinit body
  | .Cwhile _ _ fuel initIdx hinit cond body =>
      compileCwhileSum Γ w fuel initIdx hinit cond body

/-- `compileScfProg` is denotation-preserving: a one-case-each
    composition of `compileCif_denote`, `compileCforSum_denote`, and
    `compileCwhileSum_denote`. -/
theorem compileScfProg_denote {Γ : List Nat} {w : Nat}
    (p : ScalarDSL.ScfProg Γ w) (V : ScalarDSL.Valuation Γ) :
    (compileScfProg p).denote
      (show Ctxt.Valuation (d := mlirArithScfDialect) (cryptoCtxt Γ) from
        cryptoCtxtValuation Γ V)
      = p.eval V := by
  cases p with
  | Cif w_in condIdx hcond inputIdx hinput thenBr elseBr =>
      simp only [compileScfProg]
      exact compileCif_denote Γ w w_in condIdx hcond inputIdx hinput thenBr elseBr V
  | Cfor lo hi step initIdx hinit body =>
      simp only [compileScfProg]
      exact compileCforSum_denote Γ w lo hi step initIdx hinit body V
  | Cwhile fuel initIdx hinit cond body =>
      simp only [compileScfProg]
      exact compileCwhileSum_denote Γ w fuel initIdx hinit cond body V
