/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-!
# `Com catCryptDialect → Com jasminDialect` lowering

This map lowers the dialect-native straight-line program `Com catCryptDialect`
into the typed Jasmin dialect `Com jasminDialect`.

```
LowCT ──translateDialectControlTop──▶ Com catCryptDialect
      ──cryptoDialectToJasminCom──────▶ Com jasminDialect
      ──JasminPrint.emitJazz──────────▶ .jazz
```

The `lowCTToJasminComD` front composes
`TranslateDialectDirectControl.translateDialectControlTop` with this map, taking
`LowCT` to `Com jasminDialect` in one step.

## Shared type and context maps

`catCryptDialect.Ty = CryptoTy` (by construction in `CatCryptDialect.lean`), so
a `Com catCryptDialect`'s De Bruijn context `Γ : Ctxt catCryptDialect` is
literally `List CryptoTy = CryptoSSA.Ctx`.
Therefore the type map `mapTy` and context map `mapCtx` are the ones
`CryptoToJasminCom` defines; we import and reuse them. This module defines
the variable translation `toJVarD`, `toJExprD` (the
`Expr catCryptDialect → Expr jasminDialect` op-level translation) and the
structural `Com` recursion.

## Op coverage

| `CatCryptOp`                 | `JasminOp`             |
|------------------------------|------------------------|
| `bvAdd/bvSub/bvMul w`        | `regArith add/sub/mul` |
| `bvAnd/bvOr/bvXor w`         | `regArith and/or/xor`  |
| `bvConst w v`                | `regConst w v.toNat`   |
| `extCall name argTys retTy`  | `extCall name …`       |
| `memrefGetDyn/SetDyn n`      | `stackLoad/stackStore` |
| `bvRor w n`                  | `rorImm w n`           |
| `bvShiftRA w n`              | `sarImm w n`           |
| `andn w`                     | `regArith andn`        |
| `bvShiftLV/bvShiftRV w`      | `regArith shl/shr`     |
| `bvShiftL/bvShiftR w k`      | `shlImm/shrImm w k`    |
| `bvMulHi w`                  | `mulhi w`              |
| `bvAddCarryLo w`             | `addCarryLo w`         |
| `bvAddCarryHi w`             | `addCarryHi w`         |
| `bvEq w`                     | `cmp .eq w`            |
| `ite (.sword w)`             | `select w`             |

The arith/const/extCall/dynamic-memref rows are the base
fragment; the rotate/variable-shift/`andn` rows are the word-native crypto
extension (SHA/Keccak/ChaCha/bignum); the immediate-shift and bignum-ALU
(`mulhi`/`addCarry*`) rows complete the word-native scalar op set, lowering
instead of surviving as opaque leaves; the `bvEq`/`ite` rows carry the word
select as a comparison feeding a conditional move. Every other `CatCryptOp`
returns `none`:
`bvNot`/`bvAdd64`/`bvAdc`/`ite` at a non-word type/`bitToSword`/the pair/sum ops/the bit
ops/`sampleBit`/`sampleBv`, plus `bvRol` (jasmin has no scalar left-rotate op,
so the dialect carries it as a faithful denotation but declines to lower it).

## Status

Front and smoke test. The `fp_add` leaf kernel lowers to a single `regArith add`
over two `reg 64` inputs, checked by `native_decide`.
-/

@[expose] public section

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
  (mapTy mapCtx)

/-! ## 1. Variable and argument-vector translation (dialect `Expr` shape)

A `Com catCryptDialect`/dialect `Expr` carries `Ctxt.Var (d := catCryptDialect)`
variables, so we cannot reuse `CryptoToJasminCom`'s
`toJVar` (which is `CVar`-shaped). The structure is the same:
because `mapCtx (s :: Γ) = mapTy s :: mapCtx Γ` reduces (`mapCtx = List.map
mapTy`), the dependent indices line up and the translation is the clean
`here ↦ here`, `there ↦ there`. -/

/-- Recursive worker for `toJVarD`: the mapped target context `Δ` is an
    explicit argument, destructured alongside the variable, so each output
    `.there` node stores a tail of the one shared `Δ` list. Keeps whole-block
    lowering linear in the variable-chain length: the `mapCtx Γ` list is built
    once (by `toJVarD`) instead of once per `.there` level. -/
def toJVarDAux {t : CryptoTy} : {Γ : Ctx} →
    Ctxt.Var (d := catCryptDialect) Γ t →
    (Δ : Ctxt jasminDialect) → mapCtx Γ = Δ →
    Ctxt.Var (d := jasminDialect) Δ (mapTy t)
  | _, .here, _, h => h ▸ .here
  | _, .there _, [], h => nomatch h
  | _, .there v, _ :: Δ', h => .there (toJVarDAux v Δ' (by injection h))

/-- Translate a `catCryptDialect` De Bruijn variable to a `jasminDialect`
    variable, transporting along `mapTy`/`mapCtx`. The dialect-`Ctxt.Var`
    analogue of `CryptoToJasminCom.toJVar`. Computes `mapCtx Γ` once and hands
    it to `toJVarDAux`, which threads it structurally down the `.there`
    spine. -/
def toJVarD {Γ : Ctx} {t : CryptoTy}
    (v : Ctxt.Var (d := catCryptDialect) Γ t) :
    Ctxt.Var (d := jasminDialect) (mapCtx Γ) (mapTy t) :=
  toJVarDAux v (mapCtx Γ) rfl

/-- Worker for `toJArgsD`: shares one mapped context `Δ` across all argument
    translations. -/
def toJArgsDAux {Γ : Ctx} (Δ : Ctxt jasminDialect) (h : mapCtx Γ = Δ) :
    {tys : List CryptoTy} →
    HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) Δ ty) (tys.map mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (toJVarDAux v Δ h) (toJArgsDAux Δ h rest)

/-- Translate a dialect `Expr`'s argument `HVector` of `Ctxt.Var`s into a
    Jasmin `HVector` of `Ctxt.Var`s, indexed by the pointwise-mapped types.
    Computes `mapCtx Γ` once, shared across the whole vector. -/
def toJArgsD {Γ : Ctx} {tys : List CryptoTy}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys) :
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (mapCtx Γ) ty) (tys.map mapTy) :=
  toJArgsDAux (mapCtx Γ) rfl args

/-! ## 2. Binary-arithmetic builder

For a `[.sword w, .sword w]`-signature dialect op whose two operand vars are
already in hand (extracted from `e.args` after rewriting along the op-equation),
build the two-operand `regArith` Jasmin `Expr`. `mapTy (.sword w) = .reg w`, so
`retTy_eq` is `rfl`. -/

/-- Build a binary `regArith` Jasmin `Expr` over two `sword w` operand vars. -/
def mkBin {Γ : Ctx} (bop : JasminBinOp) (w : Nat)
    (a b : Ctxt.Var (d := catCryptDialect) Γ (.sword w)) :
    Expr jasminDialect (mapCtx Γ) (.reg w) :=
  { op := .regArith bop w, retTy_eq := rfl,
    args := .cons (toJVarD a) (.cons (toJVarD b) .nil) }

/-! ## 3. Expression translation (dialect `Expr` → Jasmin `Expr`)

The dialect-`Expr` analogue of `CryptoToJasminCom.toJExpr`. We case on the op
tag; the dependent `retTy_eq`/`args` are rewritten along `h : e.op = …`.
Coverage is identical to `toJExpr`. -/

/-- Translate a `catCryptDialect` expression into a Jasmin-dialect `Expr`.
    Returns `none` for everything outside the lowered straight-line fragment,
    matching `CryptoToJasminCom.toJExpr`'s coverage exactly. -/
def toJExprD {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t) :
    Option (Expr jasminDialect (mapCtx Γ) (mapTy t)) :=
  match h : e.op with
  | .bvAdd w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .add w args.head args.tail.head)
  | .bvSub w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .sub w args.head args.tail.head)
  | .bvMul w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .mul w args.head args.tail.head)
  | .bvAnd w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .and w args.head args.tail.head)
  | .bvOr w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .or w args.head args.tail.head)
  | .bvXor w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .xor w args.head args.tail.head)
  | .bvConst w v =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      some (hr ▸ { op := .regConst w v.toNat, retTy_eq := rfl, args := .nil })
  -- An `extCall` returning a width-carrying array is not lowered. The jasmin
  -- external semantics reads a `stackArr 16` return as a lattice leaf whatever
  -- the callee is named, so the opaque-default law the lowering relies on does
  -- not hold at that width; declining the shape keeps the law unconditional.
  | .extCall name argTys (.memrefW _ _) => none
  | .extCall name argTys retTy =>
      have hr : mapTy t = mapTy retTy := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          argTys := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .extCall name (argTys.map mapTy) (mapTy retTy), retTy_eq := rfl,
          args := toJArgsD (Γ := Γ) (tys := argTys) args })
  -- **Dynamic-index memref load.** `memref.load %a[%i]` (runtime index `i`)
  -- ↦ jasmin `stackLoad 64 n`. The dialect op's `[.memref n, .sword 64]`
  -- operands map pointwise to `[.stackArr 64 n, .reg 64]` — exactly the jasmin
  -- `stackLoad` signature — and the `arrIdx`-fold in `opToLinstrR` then emits
  -- the x86 SIB `(%base,%idx,scale)` `LOADIDX`. `ret t = .sword 64`, so
  -- `mapTy t = .reg 64` and `retTy_eq` is `rfl`. (#M1)
  | .memrefGetDyn n =>
      have hr : mapTy t = JasminTy.reg 64 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.memref n, .sword 64] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .stackLoad 64 n, retTy_eq := rfl,
          args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
  -- **Dynamic-index memref store.** `memref.store %v, %a[%i]` ↦ jasmin
  -- `stackStore 64 n`. The dialect op's `[.memref n, .sword 64, .sword 64]`
  -- (array, runtime index, value) maps to `[.stackArr 64 n, .reg 64, .reg 64]`,
  -- the jasmin `stackStore` signature; `opToLinstrR` then emits `STOREIDX` with
  -- the SIB destination. `ret t = .memref n`, so `mapTy t = .stackArr 64 n`. (#M1)
  | .memrefSetDyn n =>
      have hr : mapTy t = JasminTy.stackArr 64 n := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.memref n, .sword 64, .sword 64] := by
        have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .stackStore 64 n, retTy_eq := rfl,
          args := .cons (toJVarD args.head)
            (.cons (toJVarD args.tail.head) (.cons (toJVarD args.tail.tail.head) .nil)) })
  -- **Width-carrying dynamic-index memref load.** `memrefWGetDyn w n` ↦ jasmin
  -- `stackLoad w n`. The dialect op's `[.memrefW w n, .sword 64]` operands map
  -- pointwise to `[.stackArr w n, .reg 64]`, the jasmin `stackLoad` signature.
  -- `ret t = .sword w`, so `mapTy t = .reg w`.
  | .memrefWGetDyn w n =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.memrefW w n, .sword 64] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .stackLoad w n, retTy_eq := rfl,
          args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
  -- **Width-carrying dynamic-index memref store.** `memrefWSetDyn w n` ↦ jasmin
  -- `stackStore w n`. The dialect op's `[.memrefW w n, .sword 64, .sword w]`
  -- (array, runtime index, value) maps to `[.stackArr w n, .reg 64, .reg w]`.
  -- `ret t = .memrefW w n`, so `mapTy t = .stackArr w n`.
  | .memrefWSetDyn w n =>
      have hr : mapTy t = JasminTy.stackArr w n := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.memrefW w n, .sword 64, .sword w] := by
        have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .stackStore w n, retTy_eq := rfl,
          args := .cons (toJVarD args.head)
            (.cons (toJVarD args.tail.head) (.cons (toJVarD args.tail.tail.head) .nil)) })
  -- **Word/crypto rotates and variable shifts.** These are the word-native
  -- primitives (SHA/Keccak/ChaCha/bignum) that lower instead of surviving
  -- as opaque `extCall` leaves.
  --
  -- `bvRor w n` (rotate-right by immediate) ↦ jasmin `rorImm w n`. Single-input
  -- `[.sword w]` ↦ `[.reg w]`, `ret = .sword w`, so `retTy_eq` is `rfl`. (#WCRYPTO)
  | .bvRor w n =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .rorImm w n, retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  -- `bvShiftRA w n` (arithmetic right shift by immediate) ↦ jasmin `sarImm w n`.
  | .bvShiftRA w n =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .sarImm w n, retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  -- `andn w` (BMI1 `(~~~a) &&& b`) ↦ jasmin `regArith .andn w` (one op, no `NOT`).
  | .andn w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .andn w args.head args.tail.head)
  -- `bvShiftLV w` (variable logical left shift) ↦ jasmin `regArith .shl w`
  -- (the shift amount is the `.toNat` of the second register operand).
  | .bvShiftLV w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .shl w args.head args.tail.head)
  -- `bvShiftRV w` (variable logical right shift) ↦ jasmin `regArith .shr w`.
  | .bvShiftRV w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸ mkBin .shr w args.head args.tail.head)
  -- **Immediate logical shifts.** `bvShiftL w k` (logical left shift by the
  -- compile-time immediate `k`) ↦ jasmin `shlImm w k`; `bvShiftR w k` (logical
  -- right shift) ↦ jasmin `shrImm w k`. Single-input `[.sword w] ↦ [.reg w]`,
  -- `ret = .sword w`, so `retTy_eq` is `rfl`. The immediate-count shift jasminc
  -- x86 linearizes (vs. a variable `regArith .shl/.shr` reading a register).
  | .bvShiftL w k =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .shlImm w k, retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  | .bvShiftR w k =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .shrImm w k, retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  -- **Bignum ALU word splits.** `bvMulHi w` (high word of the widening multiply)
  -- ↦ jasmin `mulhi w`; `bvAddCarryLo w` (carry-chain data word) ↦ jasmin
  -- `addCarryLo w`; `bvAddCarryHi w` (carry-out bit) ↦ jasmin `addCarryHi w`.
  -- The carry-chain ops take a third `.sword 1 ↦ .reg 1` carry-in operand; the
  -- denotations (`mulHiC`/`addCarryWordC`/`carryOutBitC`) are defined identically
  -- to the jasmin twins (`mulHiW`/`addCarryWord`/`carryOutBit`).
  | .bvMulHi w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .mulhi w, retTy_eq := rfl,
          args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
  | .bvAddCarryLo w =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w, .sword 1] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .addCarryLo w, retTy_eq := rfl,
          args := .cons (toJVarD args.head)
            (.cons (toJVarD args.tail.head) (.cons (toJVarD args.tail.tail.head) .nil)) })
  | .bvAddCarryHi w =>
      have hr : mapTy t = JasminTy.reg 1 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w, .sword 1] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .addCarryHi w, retTy_eq := rfl,
          args := .cons (toJVarD args.head)
            (.cons (toJVarD args.tail.head) (.cons (toJVarD args.tail.tail.head) .nil)) })
  -- **128-bit SIMD ops (SIMD Tier-3 front).** `vsimd op` (binary) lowers 1:1 to
  -- the jasmin `JasminOp.vsimd op`; the front sig `[.sword 128, .sword 128]` maps
  -- to `[.reg 128, .reg 128] = SimdOp.argTys op` for the binary ops, so the args
  -- typecheck against the jasmin `op.argTys` after casing `op` to a concrete
  -- binary constructor. `ret = .sword 128`, `mapTy = .reg 128 = SimdOp.retTy op`,
  -- so `retTy_eq` is `rfl`. The UNARY `SimdOp`s (`vpshufd`/`vaeskeygen`/`packedImm`)
  -- decline here: `vpshufd` and `vaeskeygen` come in through the dedicated unary
  -- front ops below, and `packedImm` has no front op.
  | .vsimd op =>
      have hr : mapTy t = JasminTy.reg 128 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword 128, .sword 128] := by have a := e.args; rw [h] at a; exact a
      match op with
      | .gf2p8mulb => some (hr ▸
          { op := .vsimd .gf2p8mulb, retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .vpshufb => some (hr ▸
          { op := .vsimd .vpshufb, retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .clmul i => some (hr ▸
          { op := .vsimd (.clmul i), retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .affineqb i => some (hr ▸
          { op := .vsimd (.affineqb i), retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .bitwise b => some (hr ▸
          { op := .vsimd (.bitwise b), retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .packed b lw => some (hr ▸
          { op := .vsimd (.packed b lw), retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .mulhi16 => some (hr ▸
          { op := .vsimd .mulhi16, retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .vaesenc => some (hr ▸
          { op := .vsimd .vaesenc, retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .vaesenclast => some (hr ▸
          { op := .vsimd .vaesenclast, retTy_eq := rfl,
            args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
      | .vaeskeygen _ => none
      | .vpshufd _ => none
      | .packedImm _ _ _ => none
  -- `vpshufdC imm` ↦ jasmin `JasminOp.vsimd (.vpshufd imm)` (unary).
  | .vpshufdC imm =>
      have hr : mapTy t = JasminTy.reg 128 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword 128] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .vsimd (.vpshufd imm), retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  -- `vaeskeygenC rcon` ↦ jasmin `JasminOp.vsimd (.vaeskeygen rcon)` (unary).
  | .vaeskeygenC rcon =>
      have hr : mapTy t = JasminTy.reg 128 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword 128] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .vsimd (.vaeskeygen rcon), retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  -- `vpsrldqC n` ↦ jasmin `JasminOp.vpsrldq n`; `vpslldqC n` ↦ `JasminOp.vpslldq n`.
  | .vpsrldqC n =>
      have hr : mapTy t = JasminTy.reg 128 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword 128] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .vpsrldq n, retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  | .vpslldqC n =>
      have hr : mapTy t = JasminTy.reg 128 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword 128] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .vpslldq n, retTy_eq := rfl,
          args := .cons (toJVarD args.head) .nil })
  -- **Baked 128-bit XMM immediate.** `vconst128 v` (nullary) ↦ jasmin
  -- `regConst 128 v.toNat`, the existing width-parametric immediate op. Its sig
  -- is `[]` and ret `.reg 128`; `mapTy (.sword 128) = .reg 128`, so `retTy_eq` is
  -- `rfl`. The owned `VsimdAsmPrint` printer renders the width-128 `regConst` as a
  -- `movabsq`/`vmovq`/`vpinsrq` two-half XMM build (no scalar-GP `UNHANDLED`). This
  -- lets a SIMD kernel bake a 128-bit constant (FAEST GF(2^128) modulus / AES round
  -- constant / shuffle mask) instead of ABI-loading it. (#G1)
  | .vconst128 v =>
      have hr : mapTy t = JasminTy.reg 128 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      some (hr ▸ { op := .regConst 128 v.toNat, retTy_eq := rfl, args := .nil })
  -- **Word equality and word select.** `bvEq w` ↦ jasmin `cmp .eq w`: the
  -- `.bit` result maps to `.reg 1`, and `cmpBit .eq a b` is `BitVec.ofBool` of
  -- the dialect's `decide (a = b)`. `ite (.sword w)` ↦ jasmin `select w`, whose
  -- `[.reg 1, .reg w, .reg w]` signature is the pointwise image of
  -- `[.bit, .sword w, .sword w]`. An `ite` at any other type is not lowered.
  | .bvEq w =>
      have hr : mapTy t = JasminTy.reg 1 := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .cmp .eq w, retTy_eq := rfl,
          args := .cons (toJVarD args.head) (.cons (toJVarD args.tail.head) .nil) })
  | .ite (.sword w) =>
      have hr : mapTy t = JasminTy.reg w := by
        have hret := e.retTy_eq; rw [h] at hret; rw [← hret]; rfl
      let args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
          [.bit, .sword w, .sword w] := by have a := e.args; rw [h] at a; exact a
      some (hr ▸
        { op := .select w, retTy_eq := rfl,
          args := .cons (toJVarD args.head)
            (.cons (toJVarD args.tail.head) (.cons (toJVarD args.tail.tail.head) .nil)) })
  -- Everything else is outside the lowered straight-line fragment:
  -- `bvNot`/`bvAdd64`/`bvAdc`/`bitToSword`, `ite` at a non-word type,
  -- the pair/sum ops, the bit ops, the static-index memref ops, the sampling
  -- ops, and `bvRol` (jasmin has no scalar left-rotate op; `bvRol` is faithful
  -- in the dialect denotation but declines here).
  | _ => none

/-! ## 4. Program translation -/

/-- Lower a `Com catCryptDialect` into a `Com jasminDialect`. Returns `none` if
    any expression falls outside the lowered straight-line fragment. -/
def cryptoDialectToJasminCom {Γ : Ctx} {t : CryptoTy} :
    Com catCryptDialect Γ t → Option (Com jasminDialect (mapCtx Γ) (mapTy t))
  | .ret v => some (.ret (toJVarD v))
  | .var e body =>
      match toJExprD e with
      | some e' =>
          match cryptoDialectToJasminCom body with
          | some body' => some (.var e' body')
          | none => none
      | none => none

/-! ## 5. The composed front

`lowCTToJasminComD := translateDialectControlTop >=> cryptoDialectToJasminCom`.
It is a `LowCT → Com jasminDialect` front. The front `translateDialectControlTop`
emits a `Com catCryptDialect _ .unit` at some final context `Γ'`; we lower it,
landing a `Com jasminDialect (mapCtx Γ') (.reg 0)` (`mapTy .unit = .reg 0`). -/

/-- The composed `LowCT → Com jasminDialect` front: run the direct
    control-flow dialect front `translateDialectControlTop`, then lower its
    `Com catCryptDialect` to `Com jasminDialect` with `cryptoDialectToJasminCom`. -/
def lowCTToJasminComD {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (Σ Γ' : Ctxt jasminDialect, Com jasminDialect Γ' (.reg 0)) :=
  match Dialects.TranslateDialectDirectControl.translateDialectControlTop vm c with
  | some ⟨Γ', com⟩ =>
      match cryptoDialectToJasminCom com with
      | some jcom => some ⟨mapCtx Γ', jcom⟩
      | none => none
  | none => none

/-! ## 6. Smoke test: the `fp_add` leaf kernel

We build the `addKernel` as a `Com catCryptDialect`, lower it through this front,
and confirm it lands a `some (Com jasminDialect …)` carrying a single
`regArith add` over the two `reg 64` inputs. -/

namespace SmokeTest

open CatCryptDialect

/-- `let s = a + b; ret s` over `[sword 64, sword 64]`, built natively as a
    `Com catCryptDialect`. -/
def addComCD : Com catCryptDialect [.sword 64, .sword 64] (.sword 64) :=
  .var
    { op := .bvAdd 64, retTy_eq := rfl,
      args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- The dialect kernel lowers (the front succeeds on the `regArith` fragment). -/
theorem addComCD_isSome : (cryptoDialectToJasminCom addComCD).isSome := by
  native_decide

/-- The lowered Jasmin-dialect program. -/
def addComJ : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  (cryptoDialectToJasminCom addComCD).get addComCD_isSome

/- The lowered program emits a `+` in `.jazz`, end-to-end through the
    `JasminPrint.emitJazz` printer. -/
#guard (JasminPrint.strContains (JasminPrint.emitJazz "fp_add_arith_d" addComJ) "+")

/-- Two parameters (the two `reg 64` inputs) and one body instruction. -/
theorem addComJ_shape :
    ((JasminPrint.lowerComToProg "fp_add_arith_d" addComJ).funcs.head?.map
      (fun fd => (fd.params.length, fd.body.length))) = some (2, 1) := by
  native_decide

/-! ### `extCall` smoke (the `fp_add` leaf survives) -/

/-- `let c = fp_add(a, b); ret c` over two `sword 64` inputs, native dialect. -/
def extComCD : Com catCryptDialect [.sword 64, .sword 64] (.sword 64) :=
  .var
    { op := .extCall "fp_add" [.sword 64, .sword 64] (.sword 64), retTy_eq := rfl,
      args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- The extern dialect kernel lowers. -/
theorem extComCD_isSome : (cryptoDialectToJasminCom extComCD).isSome := by
  native_decide

/- The lowered `extCall` program names `fp_add` in `.jazz` (the leaf survives
    the whole `Com catCryptDialect → Com jasminDialect → .jazz` chain). -/
#guard (JasminPrint.strContains (JasminPrint.emitJazz "fp_add_ext_d" ((cryptoDialectToJasminCom extComCD).get extComCD_isSome)) "fp_add")

end SmokeTest

end CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
