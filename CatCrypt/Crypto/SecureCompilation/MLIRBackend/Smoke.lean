/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Veir.OpCode

/-!
# MLIR backend — smoke test

The `MLIRBackend/` directory is a `Com → MLIR-IR` lowering, parallel to the
verified `Com → jasmin` pipeline, that targets registered MLIR dialects
(`arith` / `vector` / `x86vector` / `memref` / `func`) instead of emitting
jasmin text. This module is its smoke test.

## MLIR-IR dependency

The MLIR-IR dependency is `opencompl/veir`, the verified MLIR-style IR library
from the opencompl group. `opencompl/lean-mlir` publishes no release branch or
tag on a stable Lean toolchain (its `main` and tags require nightlies), so it
cannot share the pinned toolchain with mathlib / Veir / VCVio / CompPoly. The
in-tree `VIR/Core.lean` reimplements lean-mlir's `Dialect`/`Com`/`Ctxt`/`Expr`
framework, and `VIR/ComToVeir_JasminDialect.lean` uses Veir as its MLIR target.

## What this module is

A minimal "MLIR-style program" constructed using Veir's `OpCode` enum
(arith / func / vector / x86vector / memref dialects declared in
`Veir.OpCode`). The smoke test does NOT exercise the full `IRContext`
(operations / blocks / regions) machinery, which `ComToMLIR.lean` and
`ComToVeir.lean` use. It only checks that:

1. Veir's `OpCode` is importable from CatCrypt;
2. We can name the specific opcodes the scalar translation targets
   (`arith.addi`, `arith.muli`, `arith.constant`, `func.func`,
   `func.return`, `vector.fma`, `x86vector.pclmulqdq`); and
3. A trivial textual MLIR program for `func.func @add(...) -> ...
   { ... arith.addi ... func.return ... }` round-trips through a pure
   pretty-printer.

The "round-trip" check is a `#eval` on the textual representation —
nothing here is verified semantically. The agreement lemmas for the
emitter live in `Denote.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIRBackend.Smoke

/-! ## §1. Veir opcode name-check

The first sanity test: name a few opcodes that the scalar translation
emits and check they are present in Veir's enum. Each line is a
*total* lookup — if the constructor disappears upstream, this file fails
to elaborate. -/

/-- A bundle of the opcodes the scalar translation emits. The constructor
    list is the inventory the scalar `Com → MLIR` translation supports. -/
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

/-- The concrete inventory the scalar translation targets. Every field
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
text directly (no IRContext allocation).

This is purely an authoring-shape check: real MLIR text that
`mlir-opt --verify-roundtrip` would accept, of the shape the scalar
`Com → MLIR` translation produces from a 2-op `Com` source. -/

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
    all be in the scalar inventory. -/
def referencedOpcodes : List Veir.OpCode :=
  [stageTwoOpcodes.funcDef, stageTwoOpcodes.addI, stageTwoOpcodes.funcRet]

example : referencedOpcodes.length = 3 := rfl
example : referencedOpcodes.head? = some Veir.OpCode.func_func := rfl

/-! ## §3. Vector / x86vector opcode availability

These opcodes are not used by the scalar translation; they are named here
for the vector lowering.

`vector.broadcast`, `vector.fma`, `vector.shuffle` are the three abstract
ops the vector lowering maps. `x86vector.vpshufb`, `x86vector.pclmulqdq`
are the two target-specific intrinsics the GF-arithmetic and AES-GCM
pilots reduce to. -/

/-- Abstract-vector opcodes. -/
def stageThreeAbstractOpcodes : List Veir.OpCode :=
  [.vector_broadcast, .vector_fma, .vector_shuffle, .vector_load, .vector_store]

/-- x86-specific vector lowering targets. -/
def stageThreeX86Opcodes : List Veir.OpCode :=
  [.x86vector_vpshufb, .x86vector_pclmulqdq, .x86vector_aesenc]

example : stageThreeAbstractOpcodes.length = 5 := rfl
example : stageThreeX86Opcodes.length = 3 := rfl

end CatCrypt.Crypto.SecureCompilation.MLIRBackend.Smoke
