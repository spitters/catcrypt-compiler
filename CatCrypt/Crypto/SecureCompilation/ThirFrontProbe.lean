/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# Probe: a denotation-preserving `thirDialect → catCryptDialect` op lowering

The two verified hax/THIR ingestion lanes both terminate at `Com jasminDialect`
(`ThirToComFront.thirToJasmin`, `lowerThir`), **bypassing** the high crypto
dialect stack (`catCryptDialect` / `fieldDialect` / `modArithDialect`) and its
certified descent (`fieldComToJasmin`, `DialectLoweringChain`). The high dialects
are fed only by *hand-authored* `Com`s (`FieldDialectPerm.lean`,
`RelationalCompileHigh.lean`). The MLIR-correct convergence requires a verified
edge **from the front dialect into a high crypto dialect**, so a hax body can
descend the algebraic stack rather than landing flat at jasmin.

This file is a minimal **probe** of that missing edge: a single-op,
denotation-preserving lowering `thBin .add w → bvAdd w` from `thirDialect` up into
`catCryptDialect`. It is the smallest honest witness that the edge is reachable.

## Why this op is the friction-free case

`thirDialect.Ty = JasminTy` and `catCryptDialect.Ty = CryptoTy`, so the edge
needs a type map. But `(.reg w).denote = BitVec w` and `(.sword w).denote =
BitVec w` are the **same** type, so the type map `mapTy (.reg w) := .sword w`
carries the **identity** value transport on `BitVec w`. And `thBin .add w` and
`bvAdd w` both denote to `a + b`. So the leaf square (the `OpLowerTransports`
obligation of the `LoweringData` engine) is `rfl` for this op.

## Honest scope

This is **one op** on a **one-binding** example program — a probe, not the pass.
The real edge (a `LoweringData thirDialect catCryptDialect` over the whole
`ThirOp` set, with the `JasminTy → CryptoTy` type map and per-op squares) is the
work this probe scopes; that pass would then chain into the existing certified
`fieldComToJasmin` / `DialectLoweringChain` descent. The shift/rotate/cast/select
`ThirOp`s have direct `catCryptDialect` images (`bvShiftR`, `bvShiftL`, …); the
genuinely new obligations are the carry/mul-hi/vpack ops without a 1:1
`CatCryptOp`, and `thBinLit` (op-expansion, exactly as in `lowerThir`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirFrontProbe

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect JasminTy)
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (ThirOp thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (CatCryptOp catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-! ## 1. The type map (identity value transport) -/

/-- The type map `thirDialect.Ty → catCryptDialect.Ty` on the register-word
    fragment: a `w`-bit register becomes a `w`-bit machine word. Both denote to
    `BitVec w`, so the induced value transport is the identity. -/
def mapTy : JasminTy → CryptoTy
  | .reg w => .sword w
  | _ => .sword 0

/-- The type map preserves the denotation type: `⟦t⟧ = ⟦mapTy t⟧` definitionally
    on the register fragment (`BitVec w` on both sides). -/
theorem mapTy_denote (w : Nat) :
    (TyDenote.denote (JasminTy.reg w)) = (TyDenote.denote (mapTy (.reg w))) := rfl

/-! ## 2. The single-op lowering on a one-binding program

The source: `let s = thBin .add w x y; ret s` over `Γ = [reg w, reg w]`.
The target: `let s = bvAdd w x y; ret s` over `mapCtx Γ = [sword w, sword w]`.
The two denote to the same `BitVec w` value `x + y` for every valuation. -/

/-- Source `thirDialect` program: one `thBin .add` over two `reg w` inputs. -/
def srcAdd (w : Nat) : Com thirDialect [.reg w, .reg w] (.reg w) :=
  .var (.mk (.thBin .add w) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Target `catCryptDialect` program: the matching `bvAdd` over two `sword w`
    inputs. The structural image of `srcAdd` under `mapTy`. -/
def tgtAdd (w : Nat) : Com catCryptDialect [.sword w, .sword w] (.sword w) :=
  .var (.mk (.bvAdd w) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-! ## 3. Denotation preservation (the leaf square, lifted to the program)

A `catCryptDialect` valuation of `[sword w, sword w]` is an
`HVector (fun t => ⟦t⟧) [sword w, sword w]`, i.e. a pair of `BitVec w` — the
SAME data as a `thirDialect` valuation of `[reg w, reg w]` (both `⟦·⟧ = BitVec
w`). So one valuation `V` serves both. The theorem: the target program denotes
to exactly the source program's denotation, on every input. -/

/-- **The probe's preservation theorem.** For every width `w` and every pair of
    `BitVec w` inputs `x`, `y`, the target `catCryptDialect` program denotes to
    the same `BitVec w` value as the source `thirDialect` program — namely `x +
    y`. The op square (`thBin .add ↦ bvAdd`) is `rfl`; lifting it over the
    one-binding `ret`/`var` skeleton is `rfl` too, because the value transport is
    the identity. This is the smallest witness that the front-dialect →
    high-crypto-dialect edge is denotation-preserving. -/
theorem srcAdd_tgtAdd_denote (w : Nat) (x y : BitVec w) :
    (tgtAdd w).denote (.cons x (.cons y .nil))
      = (srcAdd w).denote (.cons x (.cons y .nil)) := rfl

/-- Concrete cross-check at `w = 32`: both programs compute `5 + 1 = 6`. -/
example :
    (tgtAdd 32).denote (.cons (5 : BitVec 32) (.cons (1 : BitVec 32) .nil))
      = (6 : BitVec 32) := rfl

/-- Both programs denote to the abstract sum `x + y`, confirming the lowering's
    target really computes the source's intended value (not just that the two
    coincide). -/
theorem tgtAdd_denote_eq_add (w : Nat) (x y : BitVec w) :
    (tgtAdd w).denote (.cons x (.cons y .nil)) = x + y := rfl

end CatCrypt.Crypto.SecureCompilation.ThirFrontProbe
