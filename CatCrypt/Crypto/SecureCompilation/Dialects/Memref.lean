/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The `memref` dialect (D0 fan-out — CatCrypt-side, not in `VIR/`)

The memory fragment of the MLIR dialect-alignment restructure
(D0 fan-out). It is the
target-neutral indexed-buffer fragment — upstream MLIR's `memref` — defined over
the CatCrypt VIR `Com`/`Dialect` framework, mirroring the proven `arith` template
(`Dialects/Arith.lean`).

## Why CatCrypt-side, not in `VIR/`

`VIR/` is our **vendored copy of Veir**, re-synced on stable releases. A dialect
added inside `VIR/` would be clobbered on the next sync (and Veir already ships a
`Memref` op-set). So the new neutral dialects live in
`Crypto/SecureCompilation/Dialects/`, **consuming** the VIR `Dialect`/
`DialectSignature`/`DialectDenote` framework. Op/type names mirror Veir's `Memref`
`OpCode` (`load`/`store`) and upstream MLIR `memref` as a migration contract.

## Scope of this gate

Two indexed-buffer ops — `memref.load %a[%i]` and `memref.store %v, %a[%i]` — over a
`buf w n` memref type (an `n`-element `w`-bit buffer) and an `int w` scalar type. The
denotation is defined to equal the `jasminDialect` image's denotation on every op
(`stackLoad`/`stackStore` via `stackGet`/`stackSet`), so the D0 lowering
(`MemrefToJasmin.lean`) preserves denotation by construction. `MemrefOp.toJasmin`
is the verified-lowering image map into the existing `jasminDialect`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Memref

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Types — `int<w>` scalar and `buf<w,n>` memref -/

/-- `memref` value types:
    * `int w`  — a `w`-bit scalar (index/value), `⟦·⟧ = BitVec w` (= jasmin `reg w`);
    * `buf w n` — an `n`-element `w`-bit memref, `⟦·⟧ = Fin n → BitVec w`
      (= jasmin `stackArr w n`). -/
inductive MemrefTy where
  | int (w : Nat)
  | buf (w n : Nat)
  deriving DecidableEq

/-- Total denotation of `MemrefTy`. -/
@[reducible] def MemrefTy.denote : MemrefTy → Type
  | .int w => BitVec w
  | .buf w n => Fin n → BitVec w

instance : TyDenote MemrefTy where
  denote := MemrefTy.denote

/-! ## 2. Ops — the neutral-`memref` fragment (Veir `Memref` / MLIR `memref` names) -/

/-- The neutral memory op set — indexed load / store on a `buf`, matching the
    jasmin `stackLoad`/`stackStore` shape exactly. The index is a 64-bit scalar
    (`int 64`), mirroring jasmin's `reg u64` array indices. -/
inductive MemrefOp where
  /-- `memref.load %a[%i]` — load element `%i` of buffer `%a`
      (`[buf w n, int 64] → int w`). Jasmin image is `stackLoad`. -/
  | load (w n : Nat)
  /-- `memref.store %v, %a[%i]` — store `%v` into element `%i` of buffer `%a`,
      yielding the updated buffer (`[buf w n, int 64, int w] → buf w n`). Jasmin
      image is `stackStore`. -/
  | store (w n : Nat)
  deriving DecidableEq

/-- The `memref` dialect over the CatCrypt VIR framework. -/
@[reducible] def memrefDialect : Dialect := { Op := MemrefOp, Ty := MemrefTy }

/-! ## 3. Signatures (match the jasmin `stackLoad`/`stackStore` sig exactly) -/

instance : DialectSignature memrefDialect where
  sig op := match op with
    | .load w n => [.buf w n, .int 64]
    | .store w n => [.buf w n, .int 64, .int w]
  ret op := match op with
    | .load w _ => .int w
    | .store w n => .buf w n

/-! ## 4. Denotation (matches the jasmin image exactly, for a clean D0 lowering)

`load` reads element `i mod n` via `stackGet`; `store` updates element `i mod n` via
`stackSet`. These are exactly the `JasminDialect.stackLoad`/`stackStore` denotations,
so the lowering preserves denotation by construction. -/

instance memrefDenote : DialectDenote memrefDialect where
  denote op := match op with
    | .load w n => fun args =>
        let arr : Fin n → BitVec w := args.head
        let i : BitVec 64 := args.tail.head
        stackGet arr i.toNat
    | .store w n => fun args =>
        let arr : Fin n → BitVec w := args.head
        let i : BitVec 64 := args.tail.head
        let v : BitVec w := args.tail.tail.head
        stackSet arr i.toNat v

/-! ## 5. The lowering image into `jasminDialect` (the D0 template's op/type maps)

Each neutral `memref` op maps 1:1 to its current `jasmin` memory image. The full
`Com memref → Com jasmin` recursion (mirroring `ArithToJasmin`) is in
`MemrefToJasmin.lean`. -/

/-- Type image: `int w ↦` jasmin `reg w`, `buf w n ↦` jasmin `stackArr w n`.
    (`⟦int w⟧ = BitVec w = ⟦reg w⟧` and `⟦buf w n⟧ = (Fin n → BitVec w) = ⟦stackArr w n⟧`
    definitionally, so the arg/result transport across this map is the identity.) -/
def MemrefTy.toJasmin : MemrefTy → JasminTy
  | .int w => .reg w
  | .buf w n => .stackArr w n

/-- Op image into `jasminDialect`. -/
def MemrefOp.toJasmin : MemrefOp → JasminOp
  | .load w n => .stackLoad w n
  | .store w n => .stackStore w n

/-- The op image preserves the result type: it maps through `MemrefTy.toJasmin`.
    (Checked by `rfl` per op.) -/
theorem toJasmin_ret (op : MemrefOp) :
    DialectSignature.ret (d := jasminDialect) op.toJasmin
      = (DialectSignature.ret (d := memrefDialect) op).toJasmin := by
  cases op <;> rfl

theorem toJasmin_sig (op : MemrefOp) :
    DialectSignature.sig (d := jasminDialect) op.toJasmin
      = (DialectSignature.sig (d := memrefDialect) op).map MemrefTy.toJasmin := by
  cases op <;> rfl

/-! ## 6. Smoke test — the dialect denotes -/

/-- One-op smoke program `load %a[%i]` over `[buf 32 4, int 64]`, mirroring the
    arith smoke test. -/
def smokeProg : Com memrefDialect [.buf 32 4, .int 64] (.int 32) :=
  .var (.mk (.load 32 4) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to `arr[i mod 4]`; checked on the array `j ↦ 10*j`
    at index `2 ↦ 20`. -/
example :
    smokeProg.denote
        (.cons (fun (j : Fin 4) => (10 * j.val : BitVec 32))
          (.cons (2 : BitVec 64) .nil))
      = (20 : BitVec 32) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.Memref
