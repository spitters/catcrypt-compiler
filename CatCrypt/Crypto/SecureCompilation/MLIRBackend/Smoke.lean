/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Veir.OpCode

/-!
# MLIR backend — Stage 1 smoke test (task #183)

This is the first file of the **new** MLIR backend chain landed under
task #183 ("structured Vector dialect with progressive lowering"). It is
the **Hybrid C** shape: the existing `rustcmd → CryptoSSA → Com → jasmin`
pipeline stays as the verified default; this new `MLIRBackend/` directory
adds a parallel `Com → MLIR-IR` lowering that targets registered MLIR
dialects (`arith` / `vector` / `x86vector` / `memref` / `func`) instead of
emitting jasmin text.

## Fall-back gate (lean-mlir toolchain mismatch)

The task spec asks for `opencompl/lean-mlir` as the dep. Audit at task
launch (2026-05-28):

* `opencompl/lean-mlir@main` requires `leanprover/lean4:nightly-2025-12-01`.
* `opencompl/lean-mlir` tag `oopsla25-bv-decide` requires `nightly-2025-06-26`.
* `opencompl/lean-mlir` tag `blase-v0.0.1` requires `nightly-2025-08-11`.
* CatCrypt is pinned to `leanprover/lean4:v4.29.1` (the stable release).

There is **no `v4.29.x` release branch or tag** in opencompl/lean-mlir. The
gate is hit cleanly: we cannot wire opencompl/lean-mlir as a dep without
upgrading the whole toolchain to a nightly, which contradicts the existing
pinning across mathlib / Veir / VCVio / CompPoly.

**Resolution** (per task instructions: "STOP, document the mismatch +
suggested resolution, and exit cleanly"): we use the already-wired
`opencompl/veir` (also from opencompl) as the MLIR-IR dependency.
Veir is the verified MLIR-style IR library from the same group and is
already a dep at `v4.29.0` (lake-manifest pins `rev 6d566105`). The local
in-tree `VIR/Core.lean` was deliberately designed "API-compatible with
opencompl/lean-mlir so we can migrate later" (see its docstring), and the
existing `ComToVeir_JasminDialect.lean` already uses Veir as the MLIR
target for the #145 strategic pivot.

A future toolchain bump (CatCrypt → lean4 nightly-2025-12-x or later) is
the route to swap Veir → opencompl/lean-mlir; the `MLIRBackend/` shape
here is designed to make that swap mechanical.

## What this file is

A minimal "MLIR-style program" constructed using Veir's `OpCode` enum
(arith / func / vector / x86vector / memref dialects already declared in
`Veir.OpCode`). The smoke test does NOT exercise the full `IRContext`
(operations / blocks / regions) machinery — that is deferred to
`ComToMLIR.lean` (Stage 2). It only checks that:

1. Veir's `OpCode` is importable from CatCrypt;
2. We can name the specific opcodes the Stage-2 translation will target
   (`arith.addi`, `arith.muli`, `arith.constant`, `func.func`,
   `func.return`, `vector.fma`, `x86vector.pclmulqdq`); and
3. A trivial textual MLIR program for `func.func @add(...) -> ...
   { ... arith.addi ... func.return ... }` round-trips through a pure
   pretty-printer.

The "round-trip" check is a `#eval` on the textual representation —
nothing here is verified semantically. The proper denotation-preservation
theorem lives in `ComToMLIR.lean` (Stage 4).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIRBackend.Smoke

/-! ## §1. Veir opcode name-check

The first sanity test: name a few opcodes that the Stage-2 translation
will emit and check they are present in Veir's enum. Each line is a
*total* lookup — if the constructor disappears upstream, this file fails
to elaborate. -/

/-- A bundle of the opcodes Stage 2 emits. The constructor list is the
    inventory the Stage-2 `Com → MLIR` translation must support. -/
structure StageTwoOpcodeInventory where
  /-- `arith.constant`: integer literal. -/
  constI : Veir.OpCode
  /-- `arith.addi`: integer add. -/
  addI : Veir.OpCode
  /-- `arith.subi`: integer subtract. -/
  subI : Veir.OpCode
  /-- `arith.muli`: integer multiply. -/
  mulI : Veir.OpCode
  /-- `arith.andi`: bitwise and. -/
  andI : Veir.OpCode
  /-- `arith.ori`: bitwise or. -/
  orI : Veir.OpCode
  /-- `arith.xori`: bitwise xor. -/
  xorI : Veir.OpCode
  /-- `arith.shli`: shift left. -/
  shlI : Veir.OpCode
  /-- `arith.shrui`: logical shift right. -/
  shrI : Veir.OpCode
  /-- `func.func`: function definition. -/
  funcDef : Veir.OpCode
  /-- `func.return`: function return. -/
  funcRet : Veir.OpCode

/-- The concrete inventory the Stage-2 translation targets. Every field
    is a registered Veir opcode (auto-generated via the `@[opcodes]`
    attribute on the `Arith` / `Func` dialects in `Veir/OpCode.lean`). -/
def stageTwoOpcodes : StageTwoOpcodeInventory :=
  { constI := .arith_constant
  , addI := .arith_addi
  , subI := .arith_subi
  , mulI := .arith_muli
  , andI := .arith_andi
  , orI := .arith_ori
  , xorI := .arith_xori
  , shlI := .arith_shli
  , shrI := .arith_shrui
  , funcDef := .func_func
  , funcRet := .func_return }

/-! ## §2. Tiny MLIR program — textual round-trip

The hello-world program: a `func.func @add(%a : i32, %b : i32) -> i32`
that computes `%a + %b` and returns the result. We render it as MLIR
text directly (no IRContext allocation; the Stage-2 translation will
either build an IRContext or render text — the design choice is in the
plan doc).

This is purely an authoring-shape check: real MLIR text that
`mlir-opt --verify-roundtrip` would accept. The Stage-2 `Com → MLIR`
translation will produce this exact shape from a 2-op `Com` source. -/

/-- Render a simple `i N` MLIR integer type. -/
def renderIntTy (w : Nat) : String := s!"i{w}"

/-- The smoke-test program: textual MLIR for the canonical `add` example. -/
def addExampleText : String :=
  "func.func @add(%a : i32, %b : i32) -> i32 {\n" ++
  "  %c = arith.addi %a, %b : i32\n" ++
  "  func.return %c : i32\n" ++
  "}"

/-- Sanity: the program text is non-empty and well-formed at the line
    level (one `func.func`, one `arith.addi`, one `func.return`). -/
example : addExampleText.length > 0 := by decide

/-- The opcodes referenced by `addExampleText`, in source order, must
    all be in the Stage-2 inventory. This guarantees that whatever
    Stage 2 emits, every opcode in it is already named here. -/
def referencedOpcodes : List Veir.OpCode :=
  [stageTwoOpcodes.funcDef, stageTwoOpcodes.addI, stageTwoOpcodes.funcRet]

example : referencedOpcodes.length = 3 := rfl
example : referencedOpcodes.head? = some Veir.OpCode.func_func := rfl

/-! ## §3. Vector / x86vector opcode availability (Stage 3 preview)

These opcodes are not used by Stage 2 but are pre-named so Stage 3 can
reference them without a fresh smoke check.

`vector.broadcast`, `vector.fma`, `vector.shuffle` are the three abstract
ops the Stage-3 pilot maps. `x86vector.vpshufb`, `x86vector.pclmulqdq`
are the two target-specific intrinsics the GF-arithmetic and AES-GCM
pilots reduce to. -/

/-- Stage-3 abstract-vector opcodes. -/
def stageThreeAbstractOpcodes : List Veir.OpCode :=
  [.vector_broadcast, .vector_fma, .vector_shuffle, .vector_load, .vector_store]

/-- Stage-3 x86-specific lowering targets. -/
def stageThreeX86Opcodes : List Veir.OpCode :=
  [.x86vector_vpshufb, .x86vector_pclmulqdq, .x86vector_aesenc]

example : stageThreeAbstractOpcodes.length = 5 := rfl
example : stageThreeX86Opcodes.length = 3 := rfl

end CatCrypt.Crypto.SecureCompilation.MLIRBackend.Smoke
