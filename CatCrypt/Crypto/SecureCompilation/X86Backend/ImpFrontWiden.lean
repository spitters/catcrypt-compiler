/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SecureCompileChain
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified

/-!
# w6 — widening the source front from straight-line arith to {arith + loop + select}

`ImpLowerCTDischarge.lean` lowers a NARROW source fragment (a right-nested
`seq`-chain of `assign dst (app op [var a, var b])` for `op ∈ {add,mul,and,xor}`)
through the scalar-arith backend `lowerSeq`, and proves the capstone's "assumed
middle" `LoweringCTPreserving` for that concrete lowering.

The backend has since been widened (w7, `LowCTUnified.lean`): a single unified
program type `UStmt = arith | mulx | sel | forU body` lowers via `lowerUProg` to
`List (JInstr 64)`, every output is `allDirect` (`lowerUProg_allDirect`), and one
uniform constant-time theorem (`lowerUProg_constant_time`) covers the whole type.

This module widens the SOURCE front to feed that unified backend.  It recognizes,
in addition to the four scalar-arith ops:

* a **bounded literal `for` loop** `forLoop x (lit (.int 0)) (lit (.int n)) body`
  — literal lower bound `0`, literal upper bound `n`, body itself a recognized
  unified program — mapped to the unified `forU x n.toNat body'`.  The bounds are
  literal (`pub` by `exprLevel`), exactly what `impCTSafe` requires public;
* a **public branchless select** in the dedicated source shape
  `assign dst (app "select" [var sel, var src0, var src1])` — mapped to the
  unified `sel { dst, sel, src0, src1 }` (`dst := if sel = 0 then src0 else
  src1`, a branchless `cmov`).  This shape is an ordinary `assign`-of-`app`, so it
  has no source control surface at all — `impCTSafe` accepts it with no
  secret-control reasoning; the branchlessness is structural in the source form.

## What is proved

* `impToU : ImpExpr → Option UProg` — the partial translator over the widened
  subset (seq-chain of arith / select / bounded-loop statements).
* `impLowerU : ImpExpr → Option (List (JInstr 64))` — post-composes `lowerUProg`
  under the identity register map.
* `impLowerU_some_CompilableCT` — every `some`-output of `impLowerU` is
  `allDirect`, i.e. `CompilableCT` (reusing `lowerUProg_allDirect`).
* `impLowerU_CTPreserving` (**the headline**) — `LoweringCTPreserving env
  impLowerU` for every `env`: the assumed middle, now a theorem for the widened
  lowering.
* `impSecureCompileU_constant_time` — the capstone with the middle discharged for
  the widened front.
* worked `example`s exercising the NEW shapes (a bounded `for` loop and a select),
  each shown to pass `impCTSafe` and to obtain the machine-CT conclusion.

## CT conclusion shape

The unified backend's output is **unconditionally** `allDirect`
(`lowerUProg_allDirect`), so `CompilableCT` holds directly and the headline lands
as the genuine `LoweringCTPreserving` interface `SecureCompileChain` consumes —
no fall-back to a bare `blockLeak`-equality was needed.

## Scope notes

The lower bound is required to be the literal `0` (the unified `forU x n` iterates
`x := 0,…,n-1`); a nonzero literal lower bound `lo` would need an index-shift in
the body, outside this on-ramp.  Memory operands stay outside the unified type
(the w7-mem follow-on), so the front returns `none` on them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImpFrontWiden

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.SecureCompileChain
open CatCrypt.Crypto.SecureCompilation.ImpCTGate
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified

/-! ## 1. Recognizing one supported statement (arith or select)

A single non-loop statement: either a scalar-arith assignment (the four
BitVec-faithful ops, as in `ImpLowerCTDischarge`) or the dedicated branchless
select shape `assign dst (app "select" [var sel, var src0, var src1])`. -/

/-- Recognize a single supported NON-loop statement and produce its unified
    statement:

    * `assign dst (app op [var a, var b])` with `op ∈ {add,mul,and,xor}` — a
      scalar-arith `UStmt.arith`;
    * `assign dst (app "select" [var sel, var src0, var src1])` — a branchless
      `UStmt.sel` (`dst := if sel = 0 then src0 else src1`).

    Anything else returns `none`. -/
def impStmtToU : ImpExpr → Option UStmt
  | .assign dst (.app f [.var a, .var b]) =>
      match f with
      | "add" => some (.arith { dst := dst, a := a, op := .add,  b := b })
      | "mul" => some (.arith { dst := dst, a := a, op := .mul_, b := b })
      | "and" => some (.arith { dst := dst, a := a, op := .and_, b := b })
      | "xor" => some (.arith { dst := dst, a := a, op := .xor_, b := b })
      | _     => none
  | .assign dst (.app "select" [.var sel, .var src0, .var src1]) =>
      some (.sel { dst := dst, sel := sel, src0 := src0, src1 := src1 })
  | _ => none

/-! ## 2. The widened partial translator

A right-nested `seq` chain of supported statements, terminated by `unitVal`, with
each statement being arith, select, or a bounded literal `for` loop whose body is
itself a translatable program.  The loop recursion descends into `body`, so the
translator is structurally recursive on the `ImpExpr`. -/

mutual
/-- **The widened partial translator.**  Recognize the widened subset of
    `ImpExpr` and produce the corresponding `UProg`; `none` for any unsupported
    constructor or shape.

    * `unitVal` — the empty block (`some []`);
    * `forLoop x (lit (.int 0)) (lit (.int n)) body` — a bounded literal loop
      `UStmt.forU x n.toNat body'`, where `body'` is the recursive translation of
      `body` (lower bound must be the literal `0`);
    * `seq stmt rest` — a recognized loop/statement head followed by a recognized
      tail;
    * a bare supported non-loop statement — a singleton block;
    * everything else — `none`. -/
def impToU : ImpExpr → Option UProg
  | .unitVal => some []
  | .seq e1 e2 =>
      match impHeadToU e1, impToU e2 with
      | some st, some rest => some (st ++ rest)
      | _, _ => none
  | e => impHeadToU e

/-- A `seq` head (also the bare-statement case): either a single non-loop
    statement, or a bounded literal loop (whose body is recursively translated).
    Returns a (possibly singleton) `UProg` so a loop head folds into the chain. -/
def impHeadToU : ImpExpr → Option UProg
  | .forLoop x (.lit (.int 0)) (.lit (.int n)) body =>
      (impToU body).map (fun b => [UStmt.forU x n.toNat b])
  | e =>
      match impStmtToU e with
      | some st => some [st]
      | none    => none
end

/-! ## 3. The concrete widened lowering `ImpExpr → Option (List (JInstr 64))` -/

/-- **The concrete widened lowering.**  Translate the widened subset to a `UProg`,
    then lower with `lowerUProg` under the identity register map (`idRho`).
    Matches the `ImpExpr → Option (List (JInstr 64))` type the capstone's `lower`
    expects.  `none` outside the translatable fragment. -/
def impLowerU (e : ImpExpr) : Option (List (JInstr 64)) :=
  (impToU e).map (fun p => lowerUProg idRho p)

/-! ## 4. The headline: discharging `LoweringCTPreserving` for `impLowerU`

`impLowerU e = some b` forces `impToU e = some p` with `b = lowerUProg idRho p`,
and `lowerUProg_allDirect` makes any such `b` `allDirect`, i.e. `CompilableCT b`.
The `NoSecretControl` hypothesis is not consumed — the unified backend emits only
direct-addressed register ops (loops are unrolled to direct ops; selects are
branchless `cmov`), so the contract holds unconditionally on the translated
subset. -/

/-- Any `some`-output of `impLowerU` is `allDirect` (i.e. `CompilableCT`): it is
    `lowerUProg idRho p` for some `p : UProg`, and every unified lowering is
    memory-free / branchless. -/
theorem impLowerU_some_CompilableCT (e : ImpExpr) (b : List (JInstr 64))
    (hlow : impLowerU e = some b) : CompilableCT b := by
  unfold impLowerU at hlow
  cases hp : impToU e with
  | none => simp [hp] at hlow
  | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at hlow
      subst hlow
      exact lowerUProg_allDirect idRho p

/-- **The discharge (headline).**  `impLowerU` is CT-preserving for **every**
    secret environment `env`: it carries any source (`NoSecretControl` or not) to
    a `CompilableCT` machine block on its `some`-outputs.  This is exactly
    `SecureCompileChain.LoweringCTPreserving env impLowerU` — the capstone's
    assumed middle, now a **proved fact** for the widened {arith + loop + select}
    lowering.

    As with the narrow lowering, the `NoSecretControl` argument is discharged
    (ignored): the unified backend only ever emits direct-addressed register ops
    (unrolled loops, branchless selects), so the machine-CT contract holds on the
    entire translated subset unconditionally. -/
theorem impLowerU_CTPreserving (env : SecEnv) :
    LoweringCTPreserving env impLowerU := by
  intro e b _hnsc hlow
  exact impLowerU_some_CompilableCT e b hlow

/-! ## 5. The capstone with the middle DISCHARGED (widened front) -/

/-- **Secure compilation, middle discharged (widened front).**  Specialises
    `SecureCompileChain.secure_compile_constant_time` with `hpre :=
    impLowerU_CTPreserving env`.  A source `e` over the widened {arith + bounded
    loop + select} subset that passes the constant-time gate and lowers (via
    `impLowerU`) to a block `b` compiles to a constant-time machine block — with
    **no** assumed `LoweringCTPreserving` hypothesis.  The middle is proved
    (`impLowerU_CTPreserving`), so this is the capstone end-to-end for the widened
    lowering. -/
theorem impSecureCompileU_constant_time {env : SecEnv}
    {e : ImpExpr} {b : List (JInstr 64)}
    (hgate : impCTSafe env e = true) (hlower : impLowerU e = some b)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ b = blockLeak s₂ b :=
  secure_compile_constant_time (impLowerU_CTPreserving env) hgate hlower s₁ s₂

/-! ## 6. Worked instances exercising the NEW shapes

These witness non-vacuity: each uses the for-loop or select path (not arith), is
accepted by `impCTSafe`, lowers, and obtains the machine-CT conclusion. -/

/-! ### 6a. A bounded literal `for` loop -/

/-- A bounded `for` loop `for i in 0..4 { acc := acc + k }` — the NEW loop path.
    Literal bounds `0 .. 4` (public), body a single arith statement. -/
def demoLoop : ImpExpr :=
  .forLoop "i" (.lit (.int 0)) (.lit (.int 4))
    (.assign "acc" (.app "add" [.var "acc", .var "k"]))

/-- The loop passes the source CT gate under any environment: its bounds are
    literal (`pub`), so no control surface is secret — even though the body
    touches a (possibly secret) `k`. -/
theorem demoLoop_gate (env : SecEnv) : impCTSafe env demoLoop = true := rfl

/-- `impLowerU` translates the loop via the `forU` path. -/
theorem demoLoop_lowers :
    impLowerU demoLoop
      = some (lowerUProg idRho
          [UStmt.forU "i" 4 [UStmt.arith { dst := "acc", a := "acc", op := .add, b := "k" }]]) := by
  simp [impLowerU, impToU, impHeadToU, impStmtToU, demoLoop]

/-- **The worked loop instance.**  The bounded `for` loop compiles to a
    constant-time machine block: same leakage trace from any two initial states.
    Obtained from the discharged capstone applied to the concrete loop — this is
    the NEW loop path, not arith. -/
theorem demoLoop_constant_time (env : SecEnv) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerUProg idRho
        [UStmt.forU "i" 4 [UStmt.arith { dst := "acc", a := "acc", op := .add, b := "k" }]])
      = blockLeak s₂ (lowerUProg idRho
        [UStmt.forU "i" 4 [UStmt.arith { dst := "acc", a := "acc", op := .add, b := "k" }]]) :=
  impSecureCompileU_constant_time (env := env) (demoLoop_gate env) demoLoop_lowers s₁ s₂

/-! ### 6b. A branchless select -/

/-- A branchless select `r := if c = 0 then x else y` in the dedicated source
    shape `assign r (app "select" [var c, var x, var y])` — the NEW select path.
    No source control surface (an ordinary `assign`-of-`app`). -/
def demoSelect : ImpExpr :=
  .assign "r" (.app "select" [.var "c", .var "x", .var "y"])

/-- The select passes the source CT gate under any environment: it is an
    `assign`-of-`app`, with no branch/loop control surface. -/
theorem demoSelect_gate (env : SecEnv) : impCTSafe env demoSelect = true := rfl

/-- `impLowerU` translates the select via the `sel` path. -/
theorem demoSelect_lowers :
    impLowerU demoSelect
      = some (lowerUProg idRho
          [UStmt.sel { dst := "r", sel := "c", src0 := "x", src1 := "y" }]) := by
  simp [impLowerU, impToU, impHeadToU, impStmtToU, demoSelect]

/-- **The worked select instance.**  The branchless select compiles to a
    constant-time machine block: same leakage trace from any two initial states.
    Obtained from the discharged capstone applied to the concrete select — this is
    the NEW select path, not arith. -/
theorem demoSelect_constant_time (env : SecEnv) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerUProg idRho
        [UStmt.sel { dst := "r", sel := "c", src0 := "x", src1 := "y" }])
      = blockLeak s₂ (lowerUProg idRho
        [UStmt.sel { dst := "r", sel := "c", src0 := "x", src1 := "y" }]) :=
  impSecureCompileU_constant_time (env := env) (demoSelect_gate env) demoSelect_lowers s₁ s₂

/-! ### 6c. A mixed seq: loop then select then arith (the chain, end to end) -/

/-- A mixed program: a bounded loop, then a select, then an arith assignment,
    chained by `seq` and terminated by `unitVal` — exercising the seq-chain
    translator across all three widened shapes. -/
def demoMixed : ImpExpr :=
  .seq demoLoop
    (.seq demoSelect
      (.seq (.assign "acc" (.app "xor" [.var "acc", .var "r"])) .unitVal))

/-- The mixed program passes the source CT gate (literal loop bounds, no secret
    control surface anywhere). -/
theorem demoMixed_gate (env : SecEnv) : impCTSafe env demoMixed = true := rfl

/-- `impLowerU` translates the mixed program: loop ++ select ++ arith. -/
theorem demoMixed_lowers :
    impLowerU demoMixed
      = some (lowerUProg idRho
          ([UStmt.forU "i" 4 [UStmt.arith { dst := "acc", a := "acc", op := .add, b := "k" }]]
            ++ [UStmt.sel { dst := "r", sel := "c", src0 := "x", src1 := "y" }]
            ++ [UStmt.arith { dst := "acc", a := "acc", op := .xor_, b := "r" }])) := by
  simp [impLowerU, impToU, impHeadToU, impStmtToU, demoMixed, demoLoop, demoSelect]

/-- **The worked mixed instance.**  The whole mixed program compiles to a
    constant-time machine block, via the discharged capstone — the widened front
    feeding the unified backend across loop, select, and arith in one program. -/
theorem demoMixed_constant_time (env : SecEnv) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerUProg idRho
        ([UStmt.forU "i" 4 [UStmt.arith { dst := "acc", a := "acc", op := .add, b := "k" }]]
          ++ [UStmt.sel { dst := "r", sel := "c", src0 := "x", src1 := "y" }]
          ++ [UStmt.arith { dst := "acc", a := "acc", op := .xor_, b := "r" }]))
      = blockLeak s₂ (lowerUProg idRho
        ([UStmt.forU "i" 4 [UStmt.arith { dst := "acc", a := "acc", op := .add, b := "k" }]]
          ++ [UStmt.sel { dst := "r", sel := "c", src0 := "x", src1 := "y" }]
          ++ [UStmt.arith { dst := "acc", a := "acc", op := .xor_, b := "r" }])) :=
  impSecureCompileU_constant_time (env := env) (demoMixed_gate env) demoMixed_lowers s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImpFrontWiden
