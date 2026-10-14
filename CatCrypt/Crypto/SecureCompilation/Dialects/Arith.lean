/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The `arith` dialect (D0 gate — CatCrypt-side, not in `VIR/`)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The first upstream-aligned neutral dialect of the MLIR dialect-alignment restructure
(D0). It is the
target-neutral integer-arithmetic fragment — upstream MLIR's `arith` — defined over
the CatCrypt VIR `Com`/`Dialect` framework.

## Why CatCrypt-side, not in `VIR/`

`VIR/` is our **vendored copy of Veir**, re-synced on stable releases. A dialect
added inside `VIR/` would be clobbered on the next sync (and Veir already ships an
`Arith` op-set). So the new neutral dialects live in
`Crypto/SecureCompilation/Dialects/`, **consuming** the VIR `Dialect`/
`DialectSignature`/`DialectDenote` framework. Op/type names mirror Veir's `Arith`
`OpCode` (`addi`/`subi`/`muli`/`andi`/`ori`/`xori`/`constant`/`mului_extended`/
shifts) as a migration contract (plan §0.3).

## Scope of this gate

The op set is exactly the `ScalarLinDeBruijn.SupportedOp` neutral fragment — binary
ALU, widening-high multiply, immediate shifts, materialised constant — under
upstream names, so it is the lowering target the `SupportedOp` firewall re-points to
(the first such locus in D0). `ArithOp.toJasmin` is the verified-lowering image map
into the existing `jasminDialect`; the `Com arith → Com jasmin` recursion + its
denotation-preservation proof (the `LatticeToJasmin` mirror) is the next step.

In the D1 reading these neutral ops are the **legalization baseline**: `addi`
chains, `mului_extended`, immediate shifts are the always-valid forms; native
selections (ADCX/MULX/…) are perf-only ISel below the `llvm` waist.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Arith

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Types — `i<w>` -/

/-- `arith` value types: a `w`-bit integer `i<w>`, `⟦·⟧ = BitVec w` (mirrors Veir
    `IntegerType{w}` / jasmin `reg w`). -/
inductive ArithTy where
  | int (w : Nat)
  deriving DecidableEq

/-- Total denotation of `ArithTy`. -/
@[reducible] def ArithTy.denote : ArithTy → Type
  | .int w => BitVec w

instance : TyDenote ArithTy where
  denote := ArithTy.denote

/-! ## 2. Ops — the neutral-`arith` fragment (Veir `Arith` names) -/

/-- The neutral integer-arithmetic op set — exactly the `SupportedOp` fragment under
    upstream `arith` names. No target instruction selection is baked in (that is
    per-ISA ISel below the waist, D1/D3). -/
inductive ArithOp where
  | addi (w : Nat)
  | subi (w : Nat)
  | muli (w : Nat)
  | andi (w : Nat)
  | ori  (w : Nat)
  | xori (w : Nat)
  /-- The high half of the widening multiply (`arith.mului_extended` hi). The low
      half is `muli`; jasmin image is `mulhi`. -/
  | mului_extended_hi (w : Nat)
  /-- Logical right shift by a compile-time immediate (`arith.shrui` const-amount),
      by the masked count `shiftMask w n`. -/
  | shrui_imm (w n : Nat)
  /-- Logical left shift by a compile-time immediate (`arith.shli` const-amount),
      by the masked count `shiftMask w n`. -/
  | shli_imm (w n : Nat)
  /-- Materialised compile-time constant (`arith.constant`). -/
  | constant (w n : Nat)
  deriving DecidableEq

/-- The `arith` dialect over the CatCrypt VIR framework. -/
@[reducible] def arithDialect : Dialect := { Op := ArithOp, Ty := ArithTy }

/-! ## 3. Signatures -/

instance : DialectSignature arithDialect where
  sig op := match op with
    | .addi w => [.int w, .int w]
    | .subi w => [.int w, .int w]
    | .muli w => [.int w, .int w]
    | .andi w => [.int w, .int w]
    | .ori  w => [.int w, .int w]
    | .xori w => [.int w, .int w]
    | .mului_extended_hi w => [.int w, .int w]
    | .shrui_imm w _ => [.int w]
    | .shli_imm w _ => [.int w]
    | .constant _ _ => []
  ret op := match op with
    | .addi w => .int w
    | .subi w => .int w
    | .muli w => .int w
    | .andi w => .int w
    | .ori  w => .int w
    | .xori w => .int w
    | .mului_extended_hi w => .int w
    | .shrui_imm w _ => .int w
    | .shli_imm w _ => .int w
    | .constant w _ => .int w

/-! ## 4. Denotation (matches the jasmin image exactly, for a clean D0 lowering) -/

instance arithDenote : DialectDenote arithDialect where
  denote op := match op with
    | .addi w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a + b
    | .subi w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a - b
    | .muli w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a * b
    | .andi w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a &&& b
    | .ori  w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a ||| b
    | .xori w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a ^^^ b
    | .mului_extended_hi w => fun args => let a : BitVec w := args.head; let b : BitVec w := args.tail.head; mulHiW a b
    | .shrui_imm w n => fun args => let a : BitVec w := args.head; a >>> shiftMask w n
    | .shli_imm w n => fun args => let a : BitVec w := args.head; a <<< shiftMask w n
    | .constant w n => fun _ => BitVec.ofNat w n

/-! ## 5. The lowering image into `jasminDialect` (the D0 template's op/type maps)

Each neutral `arith` op maps 1:1 to its current `jasmin` image. In the D1 reading the
target-native selections are perf-only ISel, so this 1:1 map is the legalization
baseline. The full `Com arith → Com jasmin` recursion + denotation-preservation proof
(mirroring `LatticeToJasmin`) is the next D0 step. -/

/-- Type image: `i<w>` ↦ jasmin `reg w`. (`⟦i w⟧ = BitVec w = ⟦reg w⟧` definitionally,
    so the arg/result transport across this map is the identity.) -/
def ArithTy.toJasmin : ArithTy → JasminTy
  | .int w => .reg w

/-- Op image into `jasminDialect`. -/
def ArithOp.toJasmin : ArithOp → JasminOp
  | .addi w => .regArith .add w
  | .subi w => .regArith .sub w
  | .muli w => .regArith .mul w
  | .andi w => .regArith .and w
  | .ori  w => .regArith .or  w
  | .xori w => .regArith .xor w
  | .mului_extended_hi w => .mulhi w
  | .shrui_imm w n => .shrImm w n
  | .shli_imm w n => .shlImm w n
  | .constant w n => .regConst w n

/-- The op image preserves the signature: arg types map pointwise via `ArithTy.toJasmin`
    and the result type matches. (The witnessed correspondences D0's `Com→Com` lowering
    consumes; checked by `rfl` per op.) -/
theorem toJasmin_ret (op : ArithOp) :
    DialectSignature.ret (d := jasminDialect) op.toJasmin
      = (DialectSignature.ret (d := arithDialect) op).toJasmin := by
  cases op <;> rfl

theorem toJasmin_sig (op : ArithOp) :
    DialectSignature.sig (d := jasminDialect) op.toJasmin
      = (DialectSignature.sig (d := arithDialect) op).map ArithTy.toJasmin := by
  cases op <;> rfl

/-! ## 6. The range restriction on constants -/

/-- An `arith` op whose constant, if any, is below `2 ^ w`: `constant w n` with
    `n < 2 ^ w`, and every other op. On these ops `constant w n` is determined by its
    value `BitVec.ofNat w n`. -/
def ArithOp.InRange : ArithOp → Prop
  | .constant w n => n < 2 ^ w
  | _ => True

instance (op : ArithOp) : Decidable op.InRange := by
  cases op <;> unfold ArithOp.InRange <;> infer_instance

/-! ## 7. The extension ops

`ArithExtOp` holds the integer operations beside `ArithOp` that the scalar fragments
of `catCryptDialect` and `jasminDialect` share: and-not, variable-amount shifts, the
arithmetic right shift by an immediate, equality comparison and select (upstream
`arith.cmpi eq` and `arith.select`). The boolean is the 1-bit integer `int 1`, read
as `1#1` for true. The denotations are those of the `jasminDialect` images. -/

/-- The extension ops of the `arith` dialect. -/
inductive ArithExtOp where
  /-- And-not `(~~~a) &&& b`. -/
  | andni (w : Nat)
  /-- Left shift by the masked count `shiftMask w b` of a variable amount `b`. -/
  | shli (w : Nat)
  /-- Logical right shift by the masked count `shiftMask w b` of a variable amount
      `b`. -/
  | shrui (w : Nat)
  /-- Arithmetic right shift by the immediate `n` (unmasked `sshiftRight`). -/
  | shrsi_imm (w n : Nat)
  /-- Equality comparison `[int w, int w] → int 1` (`arith.cmpi eq`). -/
  | cmpi_eq (w : Nat)
  /-- Select `[int 1, int w, int w] → int w` (`arith.select`). -/
  | select (w : Nat)
  deriving DecidableEq

/-- The extension dialect over the `arith` type alphabet. -/
@[reducible] def arithExtDialect : Dialect := { Op := ArithExtOp, Ty := ArithTy }

instance : DialectSignature arithExtDialect where
  sig op := match op with
    | .andni w => [.int w, .int w]
    | .shli w => [.int w, .int w]
    | .shrui w => [.int w, .int w]
    | .shrsi_imm w _ => [.int w]
    | .cmpi_eq w => [.int w, .int w]
    | .select w => [.int 1, .int w, .int w]
  ret op := match op with
    | .andni w => .int w
    | .shli w => .int w
    | .shrui w => .int w
    | .shrsi_imm w _ => .int w
    | .cmpi_eq _ => .int 1
    | .select w => .int w

instance arithExtDenote : DialectDenote arithExtDialect where
  denote op := match op with
    | .andni w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.andn.apply a b
    | .shli w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.shl.apply a b
    | .shrui w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.shr.apply a b
    | .shrsi_imm w n => fun args => let a : BitVec w := args.head; BitVec.sshiftRight a n
    | .cmpi_eq w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        cmpBit .eq a b
    | .select w => fun args =>
        let c : BitVec 1 := args.head; let a : BitVec w := args.tail.head
        let b : BitVec w := args.tail.tail.head
        selectW c a b

/-- Op image of the extension ops into `jasminDialect`. -/
def ArithExtOp.toJasmin : ArithExtOp → JasminOp
  | .andni w => .regArith .andn w
  | .shli w => .regArith .shl w
  | .shrui w => .regArith .shr w
  | .shrsi_imm w n => .sarImm w n
  | .cmpi_eq w => .cmp .eq w
  | .select w => .select w

/-- The image of an extension op has the mapped return type. -/
theorem ArithExtOp.toJasmin_ret (op : ArithExtOp) :
    DialectSignature.ret (d := jasminDialect) op.toJasmin
      = (DialectSignature.ret (d := arithExtDialect) op).toJasmin := by
  cases op <;> rfl

/-- The image of an extension op has the mapped argument types. -/
theorem ArithExtOp.toJasmin_sig (op : ArithExtOp) :
    DialectSignature.sig (d := jasminDialect) op.toJasmin
      = (DialectSignature.sig (d := arithExtDialect) op).map ArithTy.toJasmin := by
  cases op <;> rfl

/-! ## 8. Smoke test — the dialect denotes -/

/-- Two-op smoke program `(a + b)` over `[i32, i32]`, mirroring the jasmin smoke test. -/
def smokeProg : Com arithDialect [.int 32, .int 32] (.int 32) :=
  .var (.mk (.addi 32) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to `a + b`; checked on `7, 35 ↦ 42`. -/
example :
    smokeProg.denote (.cons (7 : BitVec 32) (.cons (35 : BitVec 32) .nil))
      = (42 : BitVec 32) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.Arith
