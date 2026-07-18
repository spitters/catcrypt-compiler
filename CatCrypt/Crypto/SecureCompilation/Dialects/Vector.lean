/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The `vector` dialect (D0 fan-out — CatCrypt-side, not in `VIR/`)

An upstream-aligned neutral dialect of the MLIR dialect-alignment restructure
(D0), mirroring the
verified `arith` triple. It is the target-neutral packed-SIMD fragment — upstream
MLIR's `vector` / Veir's `Vector` — restricted to the single ZMM-lowerable type and
its packed per-lane binary op, defined over the CatCrypt VIR `Com`/`Dialect`
framework.

## Why CatCrypt-side, not in `VIR/`

`VIR/` is our **vendored copy of Veir**, re-synced on stable releases. A dialect
added inside `VIR/` would be clobbered on the next sync. So the new neutral dialects
live in `Crypto/SecureCompilation/Dialects/`, **consuming** the VIR `Dialect`/
`DialectSignature`/`DialectDenote` framework.

## Scope of this gate (v1)

A single value type `v512` — an 8×u64 AVX-512 ZMM register (`⟦·⟧ = BitVec 512`) — and
a single op `pack bop`, the packed per-64-bit-lane binary op `[v512, v512] → v512`
with **no cross-lane carry** (`#VPADD_8u64` / `#VPSUB_8u64` / `#VPMULL_8u64` /
`#VPSRL_8u64` for `bop = .add/.sub/.mul/.shr`). Its denotation is `zmmPackQ bop`,
**imported and reused** from `JasminDialect`, so the lowering preserves the
denotation EXACTLY. `pack` is binary on `BitVec 512`, so the dialect is
**arith-shaped**: `VectorOp.toJasmin` maps `pack bop ↦ JasminOp.vpackZMM bop` 1:1,
and the `Com vector → Com jasmin` recursion + its denotation-preservation proof
mirror the `arith` triple.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Vector

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Types — `v512` -/

/-- `vector` value types: a single 8×u64 ZMM register `v512`, `⟦·⟧ = BitVec 512`
    (mirrors Veir `VectorType` / jasmin `reg 512`). -/
inductive VectorTy where
  | v512
  /-- A 128-bit XMM register (`⟦·⟧ = BitVec 128 = ⟦reg 128⟧`). -/
  | v128
  deriving DecidableEq

/-- Total denotation of `VectorTy`. -/
@[reducible] def VectorTy.denote : VectorTy → Type
  | .v512 => BitVec 512
  | .v128 => BitVec 128

instance : TyDenote VectorTy where
  denote := VectorTy.denote

/-! ## 2. Ops — the packed-lane fragment (Veir `Vector` names) -/

/-- The neutral packed-SIMD op set (v1): the packed per-64-bit-lane binary op
    `pack bop` over two ZMM registers, `[v512, v512] → v512`, with no cross-lane
    carry. No target instruction selection is baked in (the lane width / ISA is
    fixed by the ZMM type). -/
inductive VectorOp where
  | pack (bop : JasminBinOp)
  /-- Parametrized 128-bit SIMD machine op (target `x86vector`), `[v128, v128] →
      v128`, dispatched by the SAME `JasminDialect.SimdOp` as the jasmin waist —
      so the lowering reuses the waist denotation with no value drift, exactly
      like `pack`/`vpackZMM`. -/
  | vsimd (op : SimdOp)
  deriving DecidableEq

/-- The `vector` dialect over the CatCrypt VIR framework. -/
@[reducible] def vectorDialect : Dialect := { Op := VectorOp, Ty := VectorTy }

/-! ## 3. Signatures -/

instance : DialectSignature vectorDialect where
  sig op := match op with
    | .pack _ => [.v512, .v512]
    -- Mirror the jasmin waist arity (`SimdOp.argTys`) faithfully: the SIMD family
    -- is XMM-only, so every arg type is `reg 128 = v128.toJasmin`. Unary arms
    -- (`vaeskeygen`, `vpshufd`) take a single operand, binary arms take two — so
    -- a hardcoded `[.v128, .v128]` would mismatch `op.argTys` for the unary arms
    -- and break the `toJasmin_sig` enumeration. Replicating `op.argTys`'s length
    -- with `v128` keeps `(sig).map toJasmin = op.argTys` definitionally per arm.
    | .vsimd op => (SimdOp.argTys op).map (fun _ => VectorTy.v128)
  ret op := match op with
    | .pack _ => .v512
    | .vsimd _ => .v128

/-! ## 4. Denotation (matches the jasmin image exactly, for a clean D0 lowering)

The denote is `zmmPackQ bop`, **reused** from `JasminDialect`, so it is the *same*
function as `JasminOp.vpackZMM bop`'s denotation — the lowering has no value drift. -/

instance vectorDenote : DialectDenote vectorDialect where
  denote op := match op with
    | .pack bop => fun args =>
        let a : BitVec 512 := args.head
        let b : BitVec 512 := args.tail.head
        zmmPackQ bop a b
    -- Match on the inner `SimdOp` first so the arg arity (`SimdOp.argTys op`) is a
    -- concrete list per arm: binary arms expose `args.head`/`args.tail.head`, the
    -- unary arms (`vaeskeygen`, `vpshufd`) expose only `args.head` and the waist
    -- denote ignores the second operand (passing `src` as the dummy, exactly as the
    -- jasmin waist denote does).
    | .vsimd op => match op with
        | .gf2p8mulb | .vpshufb | .clmul _ | .affineqb _ | .bitwise _ | .packed _ _
        | .mulhi16 | .vaesenc | .vaesenclast => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            op.denote a b
        | .vaeskeygen rcon => fun args =>
            let src : BitVec 128 := args.head
            SimdOp.denote (.vaeskeygen rcon) src src
        | .vpshufd imm => fun args =>
            let src : BitVec 128 := args.head
            SimdOp.denote (.vpshufd imm) src src

/-! ## 5. The lowering image into `jasminDialect` (the D0 template's op/type maps)

`pack bop` maps 1:1 to its jasmin image `vpackZMM bop`. The full `Com vector → Com
jasmin` recursion + denotation-preservation proof live in `VectorToJasmin.lean` /
`VectorToJasminDenote.lean`. -/

/-- Type image: `v512` ↦ jasmin `reg 512`. (`⟦v512⟧ = BitVec 512 = ⟦reg 512⟧`
    definitionally, so the arg/result transport across this map is the identity.) -/
def VectorTy.toJasmin : VectorTy → JasminTy
  | .v512 => .reg 512
  | .v128 => .reg 128

/-- Op image into `jasminDialect`. -/
def VectorOp.toJasmin : VectorOp → JasminOp
  | .pack bop => .vpackZMM bop
  | .vsimd op => .vsimd op

/-- The op image preserves the result type: `pack`'s result `v512` maps to jasmin
    `reg 512`. Checked by `rfl` per op. -/
theorem toJasmin_ret (op : VectorOp) :
    DialectSignature.ret (d := jasminDialect) op.toJasmin
      = (DialectSignature.ret (d := vectorDialect) op).toJasmin := by
  cases op with
  | pack => rfl
  | vsimd op' => cases op' <;> rfl

/-- The op image preserves the signature: arg types map pointwise via
    `VectorTy.toJasmin`. Checked by `rfl` per op. -/
theorem toJasmin_sig (op : VectorOp) :
    DialectSignature.sig (d := jasminDialect) op.toJasmin
      = (DialectSignature.sig (d := vectorDialect) op).map VectorTy.toJasmin := by
  cases op with
  | pack => rfl
  | vsimd op' => cases op' <;> rfl

/-! ## 6. Smoke test — the dialect denotes -/

/-- One-op smoke program `pack .add a b` over `[v512, v512]`, mirroring the jasmin
    `vpackZMM` smoke test. -/
def smokeProg : Com vectorDialect [.v512, .v512] .v512 :=
  .var (.mk (.pack .add) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to the packed-add of its two inputs; checked on the
    all-lanes-`1` and all-lanes-`2` ZMM registers (each lane sums to `3`). -/
example :
    smokeProg.denote
        (.cons (zmmOfLanes (fun _ => (1 : BitVec 64)))
          (.cons (zmmOfLanes (fun _ => (2 : BitVec 64))) .nil))
      = zmmPackQ .add (zmmOfLanes (fun _ => 1)) (zmmOfLanes (fun _ => 2)) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.Vector
