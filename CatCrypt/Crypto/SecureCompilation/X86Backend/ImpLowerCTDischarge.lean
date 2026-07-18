/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.SecureCompileChain
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Discharging the assumed middle (`LoweringCTPreserving`) for a concrete lowering

`SecureCompileChain.secure_compile_constant_time` is the secure-compiler
capstone, but it consumes the lowering's CT-preservation as an **explicit
hypothesis** `hpre : LoweringCTPreserving env lower` — the "assumed middle" the
audit flags. This module turns that hypothesis into a **proved fact** for a
concrete `lower`, so the capstone specialised here carries *no* assumed middle.

## What the discharge needs

`LoweringCTPreserving env lower` unfolds to

> `∀ e b, NoSecretControl env e → lower e = some b → CompilableCT b`

and `CompilableCT b` is **definitionally** `allDirect b = true`
(`CompilableCT.lean`). So the obligation is: *every `some`-output of `lower` is
`allDirect`*. Our scalar-arith lowering `lowerSeq` (`LowCTToJInstrCT.lean`) is
memory-free and therefore **always** `allDirect` (`lowerSeq_allDirect`) — so the
contract holds *unconditionally on the `some`-cases*, independent of
`NoSecretControl`. (`NoSecretControl` is the front-gate invariant; it is needed
for the *full*-AST lowering to select direct addressing, but our lowering never
emits an indexed access, so it is not consumed here.)

## The concrete lowering

`impToArith : ImpExpr → Option (List ArithSrc)` is a **partial** translator over
a small recognizable arith subset of the hax `ImpExpr` AST:

* a right-nested `seq` chain of `assign dst (app op [var a, var b])` statements,
  terminated by `unitVal`, where `op ∈ {add, mul, and, xor}` (the BitVec-faithful
  ops `ArithOp`);
* a single bare `assign dst (app op [var a, var b])`.

Every other constructor / shape returns `none` (outside the translatable
fragment — the same fragment limit the audit notes). `impLower` post-composes
with `lowerSeq` under a fixed register map.

## What is proved

* `impLower_CTPreserving` (**the headline**) — `LoweringCTPreserving env impLower`
  for **every** `env`: the assumed middle, now a theorem for `impLower`.
* `impSecureCompile_constant_time` — the capstone with the middle **discharged**:
  `impCTSafe env e = true → impLower e = some b → blockLeak s₁ b = blockLeak s₂ b`,
  with no `LoweringCTPreserving` hypothesis remaining.
* a worked `example`: a concrete supported `ImpExpr` and its CT conclusion.

## Honest scope

`impToArith` handles only the supported scalar-arith subset; the full hax-AST
coverage (control flow, calls, memory, nested expressions) is the
fragment-widening work and returns `none` here. The point of this module is
narrow and exact: the capstone's middle is **no longer an assumption** — it is
proved for `impLower`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImpLowerCTDischarge

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.SecureCompileChain
open CatCrypt.Crypto.SecureCompilation.ImpCTGate
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-! ## 1. Recognizing one supported statement -/

/-- Recognize a single supported arith statement
    `assign dst (app op [var a, var b])` with `op ∈ {add, mul, and, xor}`.
    Anything else (other constructors, other arities, non-`var` operands,
    unsupported op names) returns `none`. -/
def impStmtToArith : ImpExpr → Option ArithSrc
  | .assign dst (.app f [.var a, .var b]) =>
      match f with
      | "add" => some { dst := dst, a := a, op := .add,  b := b }
      | "mul" => some { dst := dst, a := a, op := .mul_, b := b }
      | "and" => some { dst := dst, a := a, op := .and_, b := b }
      | "xor" => some { dst := dst, a := a, op := .xor_, b := b }
      | _     => none
  | _ => none

/-! ## 2. The partial translator over the recognizable subset

A right-nested `seq` chain of supported statements, terminated by `unitVal`, or
a single bare supported statement. -/

/-- **The partial translator.** Recognize the supported arith subset of
    `ImpExpr` and produce the corresponding `List ArithSrc`; `none` for any
    unsupported constructor or shape.

    * `unitVal` — the empty straight-line block (`some []`);
    * `seq stmt rest` — a recognized statement followed by a recognized tail;
    * a bare supported statement — a singleton block;
    * everything else — `none`. -/
def impToArith : ImpExpr → Option (List ArithSrc)
  | .unitVal => some []
  | .seq e1 e2 =>
      match impStmtToArith e1, impToArith e2 with
      | some p, some ps => some (p :: ps)
      | _, _ => none
  | e =>
      match impStmtToArith e with
      | some p => some [p]
      | none   => none

/-! ## 3. The concrete lowering `ImpExpr → Option (List (JInstr 64))` -/

/-- A concrete register map: source slot names are mapped to machine register
    names by the identity-on-strings choice (a genuine allocator would pick
    distinct physical registers; the CT discharge is independent of the choice,
    since `lowerSeq` is `allDirect` for *any* `RegMap`). -/
def impRegMap : RegMap := fun s => s

/-- **The concrete lowering.** Translate the supported arith subset to
    `List ArithSrc`, then lower with `lowerSeq` under `impRegMap`. Matches the
    `ImpExpr → Option (List (JInstr 64))` type the capstone's `lower` expects.
    `none` outside the translatable fragment. -/
def impLower (e : ImpExpr) : Option (List (JInstr 64)) :=
  (impToArith e).map (fun ps => lowerSeq impRegMap ps)

/-! ## 4. The headline: discharging `LoweringCTPreserving` for `impLower`

`impLower e = some b` forces `impToArith e = some ps` with `b = lowerSeq
impRegMap ps`, and `lowerSeq_allDirect` makes any such `b` `allDirect`, i.e.
`CompilableCT b`. The `NoSecretControl` hypothesis is *not* consumed — our
lowering never produces a non-direct block, so the contract holds
unconditionally on the translated subset. -/

/-- Any `some`-output of `impLower` is `allDirect` (i.e. `CompilableCT`),
    regardless of the source: it is `lowerSeq impRegMap ps` for some
    `ps : List ArithSrc`, and `lowerSeq` is always memory-free. -/
theorem impLower_some_CompilableCT (e : ImpExpr) (b : List (JInstr 64))
    (hlow : impLower e = some b) : CompilableCT b := by
  -- `impLower e = (impToArith e).map (lowerSeq impRegMap)`; the `some` forces a `ps`.
  unfold impLower at hlow
  cases hps : impToArith e with
  | none => simp [hps] at hlow
  | some ps =>
      simp only [hps, Option.map_some, Option.some.injEq] at hlow
      -- `b = lowerSeq impRegMap ps`; `CompilableCT b = allDirect b = true`.
      subst hlow
      exact lowerSeq_allDirect impRegMap ps

/-- **The discharge (headline).** `impLower` is CT-preserving for **every**
    secret environment `env`: it carries any source (`NoSecretControl` or not) to
    a `CompilableCT` machine block on its `some`-outputs. This is exactly
    `SecureCompileChain.LoweringCTPreserving env impLower` — the capstone's
    assumed middle, now a **proved fact** for this concrete lowering.

    The `NoSecretControl` argument is discharged (ignored): our lowering only
    ever emits direct-addressed register ops, so the machine-CT contract holds on
    the entire translated subset unconditionally. -/
theorem impLower_CTPreserving (env : SecEnv) :
    LoweringCTPreserving env impLower := by
  intro e b _hnsc hlow
  exact impLower_some_CompilableCT e b hlow

/-! ## 5. The capstone with the middle DISCHARGED -/

/-- **Secure compilation, middle discharged.** Specialises
    `SecureCompileChain.secure_compile_constant_time` with `hpre :=
    impLower_CTPreserving env`. The result: a source `e` that passes the
    constant-time gate and lowers (via `impLower`) to a block `b` compiles to a
    constant-time machine block — with **no** assumed `LoweringCTPreserving`
    hypothesis. The middle is now proved (`impLower_CTPreserving`), so this is
    the capstone end-to-end for our concrete lowering. -/
theorem impSecureCompile_constant_time {env : SecEnv}
    {e : ImpExpr} {b : List (JInstr 64)}
    (hgate : impCTSafe env e = true) (hlower : impLower e = some b)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ b = blockLeak s₂ b :=
  secure_compile_constant_time (impLower_CTPreserving env) hgate hlower s₁ s₂

/-! ## 6. A worked instance

A concrete supported `ImpExpr`: `acc := acc + k` (a single arith statement),
which the gate accepts (no control surface at all) and `impLower` translates,
then the discharged capstone gives its constant-time conclusion directly. -/

/-- A supported source program: a single `add` assignment. -/
def demoArith : ImpExpr :=
  .assign "acc" (.app "add" [.var "acc", .var "k"])

/-- The lowered block for `demoArith`: `mov acc, acc` then `add acc, k`. -/
def demoBlock : List (JInstr 64) :=
  lowerSeq impRegMap [{ dst := "acc", a := "acc", op := .add, b := "k" }]

/-- `impLower` translates the demo program to `demoBlock`. -/
theorem demoArith_impLower : impLower demoArith = some demoBlock := rfl

/-- The demo program passes the source CT gate under any environment (it has no
    control surface — just one assignment). -/
theorem demoArith_gate (env : SecEnv) : impCTSafe env demoArith = true := rfl

/-- **The worked instance.** The demo program compiles to a constant-time
    machine block: its leakage trace is the same from any two initial states.
    Obtained from `impSecureCompile_constant_time` — the capstone with the
    middle discharged — applied to the concrete demo. -/
theorem demoArith_constant_time (env : SecEnv) (s₁ s₂ : JState 64) :
    blockLeak s₁ demoBlock = blockLeak s₂ demoBlock :=
  impSecureCompile_constant_time (env := env) (demoArith_gate env) demoArith_impLower s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImpLowerCTDischarge
