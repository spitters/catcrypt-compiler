/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Print
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import CatCrypt.Crypto.SecureCompilation.VIR.CryptoToVIR

/-!
# DialectPrint instance for catCryptDialect

Maps our `CatCryptOp` tags to textual MLIR using the `arith`, `memref`,
and `scf` dialects. Result: `Com.printModule` on a CatCrypt program
produces syntactically valid input for `mlir-opt --convert-* -to-llvm`
and onward to LLVM IR via `mlir-translate`.

## Op mapping

| CatCryptOp | MLIR op | Notes |
|---|---|---|
| `constBit v` | `arith.constant {value = <v> : i1}` | |
| `constUnit` | `arith.constant {value = 0 : i1}` | unit erased to i1 = 0 |
| `xor`/`and`/`or`/`not` | `arith.xori`/`andi`/`ori`/... | on i1 |
| `eqBit` | `arith.cmpi {predicate = 0} : i1` | |
| `bvConst w v` | `arith.constant {value = v : i<w>}` | |
| `bvXor/bvAnd/bvOr/bvNot` | `arith.xori/andi/ori/xor -1` | |
| `bvAdd/bvSub/bvMul` | `arith.addi/subi/muli` | |
| `bvEq` | `arith.cmpi {predicate = 0}` | |
| `bvShiftL/bvShiftR` | `arith.shli/shrui` | needs amount constant |
| `ite t` | `scf.if` or `arith.select` | select for simple types |
| `bitToSword n` | `arith.extsi` | i1 → iN, sign-extend = allOnes-or-zero mask |
| `memrefZero n` | `memref.alloca` + zero-fill loop | may inline as alloc + fills |
| `memrefSet n i` | `memref.store` + yield | |
| `memrefGet n i` | `memref.load` | |

Pair/sum/mkPair/inl/inr emit `llvm.struct`/`llvm.insertvalue` ops from
the LLVM dialect (not covered here in detail — see upstream's
`Dialects/LLVM/Syntax/Pretty/*.lean` for exact grammar).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## Type printer -/

/-- Print a `CryptoTy` as a textual MLIR type. -/
def printCryptoTy : CryptoTy → String
  | .bit => "i1"
  | .unit => "i1"   -- erased
  | .sword n => "i" ++ toString n
  | .memref n => "memref<" ++ toString n ++ "xi64>"
  | .pair _ _ => "!llvm.struct<(...)>"   -- simplified
  | .sum _ _ => "!llvm.struct<(i1, ...)>"   -- tag + payload

/-! ## Op printer

Each `CatCryptOp` produces:
- the quoted MLIR op name (`"arith.addi"` or `"arith.constant"`)
- an inline attribute dictionary when needed (`{value = N : iW}`)

The operand list, operand type signature, and result type are added by
`Expr.printLine`. -/

/-- Quoted op-name only (no operands, no attributes, no types). -/
def printCatCryptOp : CatCryptOp → String
  | .constBit _ | .constUnit | .bvConst _ _ => "\"arith.constant\""
  | .xor | .bvXor _ | .not | .bvNot _ => "\"arith.xori\""
  | .and | .bvAnd _ => "\"arith.andi\""
  | .or | .bvOr _ => "\"arith.ori\""
  | .eqBit | .bvEq _ => "\"arith.cmpi\""
  | .bvAdd _ => "\"arith.addi\""
  | .bvSub _ => "\"arith.subi\""
  | .bvMul _ => "\"arith.muli\""
  | .bvShiftL _ _ => "\"arith.shli\""
  | .bvShiftR _ _ => "\"arith.shrui\""
  -- Variable-amount logical shifts (shift count is a second register operand).
  | .bvShiftLV _ => "\"arith.shli\""
  | .bvShiftRV _ => "\"arith.shrui\""
  -- Arithmetic (sign-extending) right shift by immediate.
  | .bvShiftRA _ _ => "\"arith.shrsi\""
  -- Rotates by immediate. No direct `arith.*` rotate; emit as named crypto ops
  -- (lowered later to `llvm.fshr`/`llvm.fshl`).
  | .bvRor _ _ => "\"crypto.rotr\""
  | .bvRol _ _ => "\"crypto.rotl\""
  -- BMI1 `andn` = `(~a) & b`. No single `arith.*` op; named crypto op.
  | .andn _ => "\"crypto.andn\""
  -- Bignum ALU word splits: high-multiply word and carry-chain words.
  | .bvMulHi _ => "\"crypto.mulhi\""
  | .bvAddCarryLo _ => "\"crypto.addcarry_lo\""
  | .bvAddCarryHi _ => "\"crypto.addcarry_hi\""
  -- Multi-output add-with-carry (carry-out + sum). No single `arith.*` op
  -- produces both results; emit as a named crypto op (mirrors the
  -- `crypto.sample_*` convention), lowered later to `llvm.uadd.with.overflow`.
  | .bvAdd64 _ => "\"crypto.add64\""
  | .bvAdc _ => "\"crypto.adc64\""
  | .ite _ => "\"arith.select\""
  -- `bitToSword n`: lower to `arith.extsi` (sign-extend i1 → iN). For
  -- `true : i1`, signed extension produces `-1 : iN` (all ones). For
  -- `false : i1`, it produces `0 : iN`. This is the standard LLVM
  -- pattern for constructing the cmov mask.
  | .bitToSword _ => "\"arith.extsi\""
  | .mkPair _ _ => "\"llvm.mlir.undef\""
  | .fst _ _ => "\"llvm.extractvalue\""
  | .snd _ _ => "\"llvm.extractvalue\""
  | .inl _ _ => "\"llvm.mlir.undef\""
  | .inr _ _ => "\"llvm.mlir.undef\""
  | .memrefZero _ => "\"memref.alloca\""
  | .memrefSet _ _ => "\"memref.store\""
  | .memrefGet _ _ => "\"memref.load\""
  | .memrefSetDyn _ => "\"memref.store\""
  | .memrefGetDyn _ => "\"memref.load\""
  -- 128-bit dynamic-index gather (two-limb XMM load); same memref.load op, i128 result.
  | .memrefGetDyn128 _ => "\"memref.load\""
  | .extCall name _ _ => "\"func.call\""
  | .sampleBit => "\"crypto.sample_bit\""
  | .sampleBv n => s!"\"crypto.sample_bv {n}\""
  -- 128-bit SIMD ops. No direct `arith.*`/`memref.*` op; emit as named crypto ops
  -- (mirrors the `crypto.rotr`/`crypto.andn`/`crypto.add64` convention), matching
  -- their x86 mnemonics. These are byte-emit residuals lowered later by the owned
  -- vsimd backend, not through `mlir-opt --convert-*`.
  | .vsimd _ => "\"crypto.vsimd\""
  | .vpshufdC _ => "\"crypto.vpshufd\""
  | .vaeskeygenC _ => "\"crypto.vaeskeygenassist\""
  | .vpsrldqC _ => "\"crypto.vpsrldq\""
  | .vpslldqC _ => "\"crypto.vpslldq\""
  | .vconst128 _ => "\"crypto.vconst128\""
  | .vsha256rnds2 => "\"crypto.sha256rnds2\""
  | .vsha256msg1 => "\"crypto.sha256msg1\""
  | .vsha256msg2 => "\"crypto.sha256msg2\""

/-- Inline attribute dict (with leading space) or empty string. -/
def printCatCryptAttrs : CatCryptOp → String
  | .constBit false => " {value = 0 : i1}"
  | .constBit true  => " {value = 1 : i1}"
  | .constUnit      => " {value = 0 : i1}"
  | .bvConst w v    =>
      " {value = " ++ toString v.toNat ++ " : i" ++ toString w ++ "}"
  | .eqBit | .bvEq _ => " {predicate = 0 : i64}"
  | .bvShiftL _ k | .bvShiftR _ k =>
      " {shift_amount = " ++ toString k ++ " : i64}"
  | .memrefSet _ i | .memrefGet _ i =>
      " {index = " ++ toString i.val ++ "}"
  | .fst _ _ => " {position = array<i64: 0>}"
  | .snd _ _ => " {position = array<i64: 1>}"
  | .extCall name _ _ => " {callee = @" ++ name ++ "}"
  | _ => ""

instance : DialectPrint catCryptDialect where
  printOp := printCatCryptOp
  printAttrs := printCatCryptAttrs
  printTy := printCryptoTy

/-! ## Smoke test: emit add_3_4 as .mlir -/

namespace Test

open CryptoSSA

/-- `let x = 3 : sword 8; let y = 4 : sword 8; let z = x + y; ret z`, authored
    directly as a `Com catCryptDialect`. The print and `opCount` smoke tests in
    `CatCryptPrintCorrect` depend on this exact op structure. -/
def add_3_4_vir : Com catCryptDialect [] (.sword 8) :=
  .var { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var { op := .bvConst 8 (4 : BitVec 8), retTy_eq := rfl, args := .nil }
      (.var { op := .bvAdd 8, retTy_eq := rfl,
              args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)))

/-- The textual MLIR. -/
def add_3_4_mlir : String :=
  Com.printModule add_3_4_vir "add_3_4"

-- Runtime check: `#eval!` prints the MLIR at elaboration.
-- Uses `#eval!` because `toVIRCom` has `@[reducible]` but needs some sorry-free
-- metaprogramming.
#eval! add_3_4_mlir

end Test

end CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint
