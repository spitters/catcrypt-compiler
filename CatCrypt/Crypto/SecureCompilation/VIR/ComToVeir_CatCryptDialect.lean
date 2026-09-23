/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.VeirPrinterShim
public import Veir.OpCode
public import Veir.IR.OpInfo
public import Veir.IR.Attribute
import all Veir.IR.Attribute
public import Veir.Properties

/-!
# Path (b) Tier 1.1: `CatCryptDialect` → Veir op/type wiring

This file provides the `ToVeirOp catCryptDialect _` and
`ToVeirTy catCryptDialect` instances that let the generic `ComToVeir`
lowering (`lowerClosedCom`, `lowerCom`, `lowerExpr` in
`ComToVeir.lean`) target real CatCrypt programs.

## Status: ACTIVE (instances defined; smoke test compiles)

Previously blocked on a name-collision between Veir's
`Veir/ForLean.lean` and Lean Init / Mathlib over `List.getElem?_idxOf`.
Resolved upstream by Veir PR #626 (rename to `List.getElem_idxOf`).

The lakefile pins Veir at `main` (bumped 2026-05-22) which includes
the fix. Once a Veir release post-PR-#626 is tagged, the dep can be
pinned to that tag instead.

## Goal 1: CatCrypt op inventory

Constructors of `CatCryptOp` (from `CatCryptDialect.lean`) and their
signatures, with the chosen Veir target op-code:

| Constructor              | Args                   | Result      | Veir target              |
|--------------------------|------------------------|-------------|--------------------------|
| `constBit b`             | none                   | `bit`       | `llvm_constant`          |
| `constUnit`              | none                   | `unit`      | `builtin_unregistered`   |
| `xor`/`and`/`or`         | `bit, bit`             | `bit`       | `llvm_xor`/`and`/`or`    |
| `not`                    | `bit`                  | `bit`       | `arith_xori`             |
| `eqBit`                  | `bit, bit`             | `bit`       | `llvm_icmp`              |
| `mkPair a b`             | `a, b`                 | `pair a b`  | `builtin_unregistered`   |
| `fst a b`                | `pair a b`             | `a`         | `builtin_unregistered`   |
| `snd a b`                | `pair a b`             | `b`         | `builtin_unregistered`   |
| `inl a b`                | `a`                    | `sum a b`   | `builtin_unregistered`   |
| `inr a b`                | `b`                    | `sum a b`   | `builtin_unregistered`   |
| `bvConst w v`            | none                   | `sword w`   | `llvm_constant`          |
| `bvXor w`/`And`/`Or`     | `sword w, sword w`     | `sword w`   | `llvm_xor`/`and`/`or`    |
| `bvNot w`                | `sword w`              | `sword w`   | `arith_xori`             |
| `bvAdd w`/`Sub w`/`Mul w`| `sword w, sword w`     | `sword w`   | `llvm_add`/`sub`/`mul`   |
| `bvEq w`                 | `sword w, sword w`     | `bit`       | `llvm_icmp`              |
| `bvShiftL w k`           | `sword w`              | `sword w`   | `llvm_shl`               |
| `bvShiftR w k`           | `sword w`              | `sword w`   | `llvm_lshr`              |
| `ite t`                  | `bit, t, t`            | `t`         | `arith_select`           |
| `bitToSword n`           | `bit`                  | `sword n`   | `llvm_zext` (placeholder; lossy sign-extend) |
| `memrefZero n`           | none                   | `memref n`  | `builtin_unregistered`   |
| `memrefSet n i`          | `memref n, sword 64`   | `memref n`  | `builtin_unregistered`   |
| `memrefGet n i`          | `memref n`             | `sword 64`  | `builtin_unregistered`   |
| `extCall …`              | varies                 | varies      | `builtin_unregistered`   |

Type mapping (`CryptoTy → Veir.TypeAttr`):

| CryptoTy   | TypeAttr                            |
|------------|-------------------------------------|
| `bit`      | `IntegerType.mk 1`                  |
| `unit`     | `default` (== `IntegerType.mk 0`)   |
| `sword n`  | `IntegerType.mk n`                  |
| `pair _ _` | `default` (structural placeholder)  |
| `sum _ _`  | `default` (structural placeholder)  |
| `memref _` | `default` (structural placeholder)  |

Notes on the op mapping:

* `bitToSword n` ("if c then allOnes else 0") is morally an
  `arith.extsi i1 → iN` plus a negate. Veir's `OpCode` enum has
  `llvm_zext` / `arith_extui` but no `extsi`. Using `llvm_zext`
  preserves the SSA shape but loses the sign-extend information; an
  accurate lowering needs Veir to gain `extsi`.
* Pair / sum / memref / `extCall` have no Veir-native counterpart in
  the current op-code enum, so they all lower to
  `OpCode.builtin_unregistered`. This is Veir's standard escape hatch
  for ops from a dialect it does not know about, and it produces a
  shape-correct IR (operands and results in the right places) that
  fails on any Veir pass that wants to inspect op semantics.

## Goal 2: Veir op-code mechanism

`Veir.OpCode` is a single flat enum generated by `#generate_op_codes`
from per-dialect `@[opcodes]` inductives in `Veir/OpCode.lean`. Each
op-code is a constructor of the form `<dialect>_<op>`, e.g.
`arith_addi`, `llvm_xor`.

* **Properties** per op-code are given by a top-level pattern match
  `Veir.propertiesOf : OpCode → Type` in `Veir/Properties.lean`. The
  result is either a specific property structure (`NswNuwProperties`,
  `LLVMConstantProperties`, …) or `Unit` for ops without properties.
  All property structures are `Inhabited`, so `default` always
  produces a value.
* **Unregistered fallback**: `OpCode.builtin_unregistered` is the
  canonical "I'm an op from a dialect Veir does not know about" tag.
  Its `propertiesOf` is `Unit`.
* **No per-user extension**: there is no `registerOpCode` mechanism;
  the enum is fixed at Veir build-time. Adding CatCrypt-native
  op-codes requires extending `Veir/OpCode.lean` with a
  `@[opcodes] inductive CatCrypt` block and re-generating.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect (LatticeOp)

-- The upstream `HasOpInfo Veir.OpCode` instance from `Veir.Properties`
-- provides per-op-code property types (`NswNuwProperties`,
-- `LLVMConstantProperties`, …) and is the one expected by
-- `Veir.Printer.printModule`. We inherit it directly via `inferInstance`
-- in the `ToVeirOp` instance below, rather than defining a local
-- `Unit`-everywhere variant; this means `defaultProps` has to supply
-- the correct property type for each op-code our `toOp` produces. All
-- property types are `Inhabited`, so `default` always works.

/-- Map each `CatCryptOp` constructor to a Veir `OpCode`.

    Ops with no direct Veir counterpart (pair/sum/memref construction,
    `constUnit`) route to `catcrypt.unknown` — a local Veir dialect
    extension whose only purpose is to give MLIR a non-`builtin`
    prefix it can accept under `--allow-unregistered-dialect`. -/
def CatCryptOp.toVeirOp : CatCryptOp → Veir.OpCode
  | .constBit _ => .llvm_constant
  | .constUnit => .catcrypt_unknown
  | .xor => .llvm_xor
  | .and => .llvm_and
  | .or => .llvm_or
  | .not => .arith_xori
  | .eqBit => .llvm_icmp
  | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _ =>
      .catcrypt_unknown
  | .bvConst _ _ => .llvm_constant
  | .bvXor _ => .llvm_xor
  | .bvAnd _ => .llvm_and
  | .bvOr _ => .llvm_or
  | .bvNot _ => .arith_xori
  | .bvAdd _ => .llvm_add
  | .bvSub _ => .llvm_sub
  | .bvMul _ => .llvm_mul
  | .bvEq _ => .llvm_icmp
  | .bvShiftL _ _ => .llvm_shl
  | .bvShiftR _ _ => .llvm_lshr
  -- Variable-amount logical shifts (shift count read from a register operand).
  | .bvShiftLV _ => .llvm_shl
  | .bvShiftRV _ => .llvm_lshr
  -- Word-native crypto ops with no single Veir opcode (rotates, sign-shift,
  -- andn) route to the unregistered escape (lowered later to `llvm.fshr`/etc).
  | .bvRor _ _ | .bvRol _ _ | .bvShiftRA _ _ | .andn _ => .catcrypt_unknown
  -- Multi-output add-with-carry: no single Veir opcode produces both the
  -- carry-out and sum, so route to the unregistered escape (as with sampling).
  | .bvAdd64 _ | .bvAdc _ => .catcrypt_unknown
  -- Bignum ALU word splits: no single Veir opcode, unregistered escape.
  | .bvMulHi _ | .bvAddCarryLo _ | .bvAddCarryHi _ => .catcrypt_unknown
  | .ite _ => .arith_select
  | .bitToSword _ => .llvm_zext
  | .memrefZero _ | .memrefSet _ _ | .memrefGet _ _
  | .memrefSetDyn _ | .memrefGetDyn _ | .memrefGetDyn128 _
  | .memrefWSetDyn _ _ | .memrefWGetDyn _ _ =>
      .catcrypt_unknown
  | .extCall _ _ _ => .func_call
  | .sampleBit | .sampleBv _ => .catcrypt_unknown
  -- 128-bit SIMD ops: no single registered Veir opcode, unregistered escape.
  | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _
  | .vconst128 _
  | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2 =>
      .catcrypt_unknown

/-- **MLIR `arith`-dialect lowering pass.** Maps each arithmetic / bit / control
    `CatCryptOp` to a REGISTERED MLIR **`arith.*`** (or `func.*`) opcode — the
    standard mid-level integer dialect — rather than the LLVM-dialect forms
    `toVeirOp` uses. Lowering to `arith` (not `llvm`) keeps the emitted MLIR at
    the level upstream MLIR passes operate on (`-canonicalize`, `-cse`,
    `arith-*`, `-int-range-optimizations`), before any `arith→llvm` conversion.

    Coverage: every BitVec/bit/`ite`/`extCall` op → an `arith`/`func` opcode, and
    the memory ops → the registered MLIR **`memref`** dialect (`memref.alloca/
    load/store`), now that Veir's `OpCode` enum carries a `Memref` block. The only
    ops still WITHOUT a registered counterpart are the algebraic-datatype ops
    (pair/sum/`constUnit`) → `catcrypt.unknown` (would need an MLIR `tuple`/`index`
    lowering or a richer `catcrypt` dialect). All mappings `rfl`-checked below. -/
def CatCryptOp.toArithOpCode : CatCryptOp → Veir.OpCode
  | .constBit _ => .arith_constant
  | .constUnit => .catcrypt_unknown
  | .xor => .arith_xori
  | .and => .arith_andi
  | .or => .arith_ori
  | .not => .arith_xori           -- `not x = xor x true`
  | .eqBit => .arith_cmpi
  | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _ => .catcrypt_unknown
  | .bvConst _ _ => .arith_constant
  | .bvXor _ => .arith_xori
  | .bvAnd _ => .arith_andi
  | .bvOr _ => .arith_ori
  | .bvNot _ => .arith_xori        -- `bvNot x = xor x allOnes`
  | .bvAdd _ => .arith_addi
  | .bvSub _ => .arith_subi
  | .bvMul _ => .arith_muli
  | .bvEq _ => .arith_cmpi
  | .bvShiftL _ _ => .arith_shli
  | .bvShiftR _ _ => .arith_shrui
  -- Variable-amount logical shifts map to the same registered `arith` shifts.
  | .bvShiftLV _ => .arith_shli
  | .bvShiftRV _ => .arith_shrui
  -- Arithmetic right shift by immediate → registered `arith.shrsi`.
  | .bvShiftRA _ _ => .arith_shrsi
  -- Rotates / `andn`: no single registered `arith.*` op, unregistered escape.
  | .bvRor _ _ | .bvRol _ _ | .andn _ => .catcrypt_unknown
  -- Multi-output add-with-carry: no registered `arith.*` op produces both
  -- carry-out and sum in one go, so route to the unregistered escape.
  | .bvAdd64 _ | .bvAdc _ => .catcrypt_unknown
  -- Bignum ALU word splits: no registered `arith.*` op, unregistered escape.
  | .bvMulHi _ | .bvAddCarryLo _ | .bvAddCarryHi _ => .catcrypt_unknown
  | .ite _ => .arith_select
  | .bitToSword _ => .arith_extui
  -- memory ops → registered MLIR `memref` dialect (Veir gained the block).
  | .memrefZero _ => .memref_alloca
  | .memrefGet _ _ | .memrefGetDyn _ | .memrefGetDyn128 _
  | .memrefWGetDyn _ _ => .memref_load
  | .memrefSet _ _ | .memrefSetDyn _ | .memrefWSetDyn _ _ => .memref_store
  | .extCall _ _ _ => .func_call
  | .sampleBit | .sampleBv _ => .catcrypt_unknown
  -- 128-bit SIMD ops: no registered `arith`/`memref` opcode, unregistered escape.
  | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _
  | .vconst128 _
  | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2 =>
      .catcrypt_unknown

/-! The `arith`-lowering maps each arithmetic op to its registered MLIR opcode
    (verified by `rfl`); no arithmetic op falls back to the unregistered escape. -/
example : CatCryptOp.toArithOpCode (.bvAdd 32) = .arith_addi := rfl
example : CatCryptOp.toArithOpCode (.bvSub 32) = .arith_subi := rfl
example : CatCryptOp.toArithOpCode (.bvMul 16) = .arith_muli := rfl
example : CatCryptOp.toArithOpCode (.bvXor 64) = .arith_xori := rfl
example : CatCryptOp.toArithOpCode (.bvShiftL 32 3) = .arith_shli := rfl
example : CatCryptOp.toArithOpCode (.bvShiftR 32 3) = .arith_shrui := rfl
example : CatCryptOp.toArithOpCode (.bvEq 16) = .arith_cmpi := rfl
example : CatCryptOp.toArithOpCode (.ite (.sword 64)) = .arith_select := rfl
example : CatCryptOp.toArithOpCode (.bitToSword 64) = .arith_extui := rfl
example : CatCryptOp.toArithOpCode (.extCall "fp_mul" [] (.sword 64)) = .func_call := rfl

/-- **MLIR `polynomial`-dialect lowering pass** for the `latticeDialect` (the
    ML-KEM/Dilithium NTT layer). Maps each `LatticeOp` to a REGISTERED MLIR
    `polynomial.*` opcode (Veir's new `Polynomial` block) — the upstream dialect
    for `Z_q[X]/(f)` arithmetic — instead of treating the NTT ops as opaque
    `func.call` leaves. `basemul` (NTT-domain) and `polyMulC` (coefficient) both
    lower to `polynomial.mul` (the ring is the dialect's ring attribute). -/
def LatticeOp.toPolynomialOpCode : LatticeOp → Veir.OpCode
  | .ntt _ _ => .polynomial_ntt
  | .invntt _ _ => .polynomial_intt
  | .basemul _ _ => .polynomial_mul
  | .polyAddN _ _ => .polynomial_add
  | .polyMulC _ _ => .polynomial_mul

example : LatticeOp.toPolynomialOpCode (.ntt 3329 256) = .polynomial_ntt := rfl
example : LatticeOp.toPolynomialOpCode (.invntt 3329 256) = .polynomial_intt := rfl
example : LatticeOp.toPolynomialOpCode (.basemul 3329 256) = .polynomial_mul := rfl
example : LatticeOp.toPolynomialOpCode (.polyAddN 3329 256) = .polynomial_add := rfl

/-- Per-op attribute payload. Today only `extCall` carries one — the
    callee symbol-ref attribute `callee = @<name>`. The remaining ops
    have no attribute payload; their semantics live entirely in their
    op-code + operands. -/
def CatCryptOp.attrsOfOp : CatCryptOp → Array (ByteArray × Veir.Attribute)
  | .extCall name _ _ =>
      #[("callee".toUTF8,
         Veir.Attribute.unregisteredAttr ⟨"@" ++ name, false⟩)]
  | _ => #[]

instance : ToVeirOp catCryptDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  -- Lower to the registered MLIR `arith`/`func` mid-level dialect (upstream-pass
  -- compatible), not the LLVM-dialect forms in the legacy `toVeirOp`.
  toOp := CatCryptOp.toArithOpCode
  defaultProps _ := default
    -- For each `Veir.OpCode` we map to, the upstream `propertiesOf`
    -- returns an `Inhabited` type (specific property struct or
    -- `Unit`), so `default` is always well-typed.
  attrsOf := CatCryptOp.attrsOfOp

/-- Build an `UnregisteredAttr` carrying MLIR-textual type syntax for
    structural types that have no native Veir `TypeAttr` (memref,
    pair, sum). The string is emitted verbatim by Veir's printer. -/
def mkTextType (s : String) : Veir.TypeAttr :=
  ⟨.unregisteredAttr ⟨s, true⟩, by simp [Veir.Attribute.isType]⟩

/-- Map each `CryptoTy` to a Veir `TypeAttr`.

    * `sword n` and `bit` use Veir's native `IntegerType`.
    * `memref n` is "n × i64" per `CryptoTy.denote` (`Fin n → BitVec 64`),
      so it prints as `memref<n×i64>`.
    * `pair`/`sum` are recursive structural; we recurse into the
      operands and emit MLIR-style tuple text (`tuple<a, b>`,
      `tuple<sum, a, b>`).
    * `unit` is the empty tuple. -/
def CryptoTy.toVeirTy : CryptoTy → Veir.TypeAttr
  | .bit => (Veir.IntegerType.mk 1 : Veir.IntegerType)
  | .unit => mkTextType "tuple<>"
  | .sword n => (Veir.IntegerType.mk n : Veir.IntegerType)
  | .pair a b =>
      mkTextType s!"tuple<{toVeirTy a}, {toVeirTy b}>"
  | .sum a b =>
      mkTextType s!"tuple<sum, {toVeirTy a}, {toVeirTy b}>"
  | .memref n => mkTextType s!"memref<{n}xi64>"
  | .memrefW w n => mkTextType s!"memref<{n}xi{w}>"

instance : ToVeirTy catCryptDialect where
  toTy := CryptoTy.toVeirTy

/-! ## Extern collection (for module-with-externs emission) -/

/-- Externs referenced by a single `CatCryptOp`. Today only
    `CatCryptOp.extCall` contributes; everything else returns `[]`. -/
def CatCryptOp.externOfOp :
    (op : CatCryptOp) → List (String × List CryptoTy × CryptoTy)
  | .extCall name argTys retTy => [(name, argTys, retTy)]
  | _ => []

/-- All externs referenced by `Com`, in source order, with duplicates.
    Caller can dedup. -/
def Com.catcryptExterns :
    {Γ : Ctxt catCryptDialect} → {t : CryptoTy} →
      Com catCryptDialect Γ t →
      List (String × List CryptoTy × CryptoTy)
  | _, _, .ret _ => []
  | _, _, .var e body =>
      CatCryptOp.externOfOp e.op ++ Com.catcryptExterns body

/-- Dedup externs by callee name (first occurrence wins). Stable. -/
def dedupExternsByName :
    List (String × List CryptoTy × CryptoTy) →
      List (String × List CryptoTy × CryptoTy)
  | [] => []
  | x :: rest =>
      let restDedup := dedupExternsByName rest
      if restDedup.any (fun y => y.1 = x.1) then restDedup
      else x :: restDedup

/-! ## Smoke test

A tiny `Com` over `CatCryptDialect` (a single `bvAdd 32`) is lowered
via the generic `lowerClosedCom`. The type-check itself is the smoke
signal — Veir's `HashMap`-backed `IRContext` doesn't reduce via Lean's
kernel for `decide`. -/

namespace SmokeTestCatCrypt

open CatCryptDialect

/-- A one-`var` `Com` over `CatCryptDialect`: bind a `bvConst 32 0` and
    return its result. We deliberately use a constant rather than a
    binary op so the smoke test stays closed (no free variables for
    operands).

    Note: the existing nullary `Expr.mk` shape (`args := .nil`) matches
    a `DialectSignature.sig` that returns `[]`, so we need a nullary
    op — `bvConst 32 0` qualifies. -/
def exampleCom : Com catCryptDialect [] (CryptoTy.sword 32) :=
  .var (Expr.mk (op := CatCryptOp.bvConst 32 (0 : BitVec 32))
                (retTy_eq := rfl) (args := .nil))
       (.ret .here)

/-- Smoke test: the lowering type-checks end-to-end and produces a
    concrete `IRContext × BlockPtr × RegionPtr × ValuePtr` value. -/
example : Veir.IRContext Veir.OpCode × Veir.BlockPtr × Veir.RegionPtr ×
    Veir.ValuePtr :=
  lowerClosedCom (d := catCryptDialect) exampleCom

/-- End-to-end pipeline: lower a closed `Com` over `CatCryptDialect`
    through `lowerClosedCom` (Veir IRContext), then through the
    `VeirPrinterShim.printModuleToString` to capture MLIR text.

    For real wrapping prefer `lowerClosedComToModule` (or, for
    function-shaped output, the X25519EmitVeir-side `func.func`
    wrapper). This helper extracts the producing op pointer from the
    final `ValuePtr` purely for the legacy smoke test below. -/
def lowerCatCryptComToMLIRText {t : CryptoTy} (com : Com catCryptDialect [] t) :
    IO String := do
  let (ctx, _blk, _reg, finalResult) :=
    lowerClosedCom (d := catCryptDialect) com
  let rootOp : Veir.OperationPtr :=
    match finalResult with
    | .opResult r => r.op
    | .blockArgument _ => default
  VeirPrinterShim.printModuleToString ctx rootOp

/-- Smoke check that the printer wiring type-checks. We do NOT
    `#eval` it — that would require Veir's printer to actually run
    against the lowered shape, which is left as follow-up. -/
example : Com catCryptDialect [] (CryptoTy.sword 32) → IO String :=
  lowerCatCryptComToMLIRText

end SmokeTestCatCrypt

end CatCrypt.Crypto.SecureCompilation.VIR
