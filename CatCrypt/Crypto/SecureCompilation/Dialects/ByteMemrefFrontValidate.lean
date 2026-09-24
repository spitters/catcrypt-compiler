/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

@[expose] public section

set_option autoImplicit false

/-!
# Byte-width (scale-1, `uint8_t`) memref store/load — front + lowering validation

This module validates the **byte-cell** dynamic-index memref store/load path
end-to-end: a `uint8_t out[N]` byte buffer, a runtime index, a `movb`-granular
store that writes exactly one byte (no overrun of the neighbouring element), and
the read-back load. It is the byte-width companion of `MemrefArrayFrontValidate`
(which validates the 64-bit-cell `.memref n` path).

## Design: the byte path reuses the already-width-parametric machinery

The byte store needs **no new op constructor and no widened predicate**. Every
layer of the pipeline is already parametric in the cell width `w`, so byte width
(`w = 8`) is just another instantiation:

* **Dialect.** `Memref.MemrefOp.store w n` / `.load w n` over the byte buffer type
  `MemrefTy.buf 8 n` (`⟦·⟧ = Fin n → BitVec 8`). The `w = 64` case is the existing
  `.memref n` path; `w = 8` is the byte path — same constructor.
* **Verified lowering.** `Memref.lowerMemrefToJasmin` maps `.store 8 n ↦` jasmin
  `stackStore 8 n` and `.buf 8 n ↦ stackArr 8 n` (via the width-preserving
  `MemrefOp.toJasmin` / `MemrefTy.toJasmin`). Denotation preservation is
  `Memref.lowerMemrefToJasmin_denote`, proved **unconditionally for all `w`** — so
  the byte case is already covered at equal strength (`byteStore_lowering_denote`
  below is its `w = 8` instance; no open goals, no new axiom).
* **Jasmin op.** `JasminOp.stackStore 8 n` is the *existing* width-parametric
  constructor. No new `JasminOp`/`catCryptDialect` op is introduced, so every
  exhaustive `match op` across the tree (optimizer passes, `ComInline`,
  `WholeFnLowering`, `JasminCTPredicate.opIndexPublic`, the `StraightLine`
  proofs, …) stays exhaustive automatically.
* **`ExprNotStackStore` / `StraightLine` (unchanged).** A byte store *is* a
  `stackStore w n` (`w = 8`), so it is already an instance of the predicate's
  `∀ w n, e.op ≠ .stackStore w n`. `StraightLine` therefore already excludes it —
  exactly as it excludes a 64-bit stackStore — and **every existing straight-line
  proof is untouched** (no `noConfusion` obligation changes shape). Byte-store
  kernels use the store-aware mem-export path, identical to 64-bit stackStore
  kernels; the predicate needed no widening and got none.
* **CT predicate.** `opIndexPublic` matches `.stackStore _ _` with a width
  wildcard, so a byte store's index-publicness judgement is width-independent.
* **x86 export (scale 1).** `opToLinstrR (.stackStore 8 n)` emits
  `STOREIDX [.arrIdx base idx (8/8 = 1), val]` — SIB scale **1**, the `uint8_t`
  stride (`byteStore_export_scale1`). `LOADIDX` for the load likewise uses scale 1.
* **Asm render (`movb`, no overrun).** `LprogAsmPrinter.renderLinstrR` sizes the
  `STOREIDX` mov by `scale * 8`: scale 1 ⇒ `movb %val8, (%base,%idx,1)`, a
  width-exact one-byte write that does **not** overrun the adjacent element; the
  `LOADIDX` load is `movzbl (%base,%idx,1), %dst32`. The runtime no-overrun check
  is the C KAT sketched at the end of this file.

## Why not a byte cell in `catCryptDialect`

`catCryptDialect`'s buffer type is `CryptoTy.memref n = Fin n → BitVec 64`, hard-
wired to 64-bit cells and matched exhaustively in ~30 modules (`CryptoTy.denote`,
`RustStateSubstrate`, `JasminValTransport`, `mapTy`, …). Widening it (or adding a
byte `CryptoTy`) is the large blast radius — the byte cell instead lives in the
standalone width-parametric `Memref` dialect, whose `MemrefTy`/`MemrefOp` are
matched in only a handful of files. This is the byte-capable front arm.

Invoke (cheap in-model gate only; the correctness gate is the C KAT):
  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/ByteMemrefFrontValidate.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ByteMemrefFrontValidate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.Memref
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 0. Dimensions -/

/-- The byte buffer length (number of `uint8_t` cells). -/
def memN : Nat := 4

/-- Input context: a byte buffer `out : uint8_t[memN]`, a runtime index `i`, and a
    byte value `v`. Head-first de Bruijn order. -/
abbrev inΓ : Ctxt memrefDialect := [.buf 8 memN, .int 64, .int 8]

/-! ## 1. The byte kernels (store-only, and store→load roundtrip)

Both are built directly over the `Memref` dialect — the byte-capable front. (A
dialect *validate* legitimately constructs small `Com`s to exercise the dialect +
verified lowering, exactly as `Memref.smokeProg` does; it is not an emit kernel
that must be sourced through a language front.) -/

/-- `out[i] := v; return out` — a single byte store. In `inΓ`, `out = .here`,
    `i = .there .here`, `v = .there (.there .here)`. -/
def byteStoreKernel : Com memrefDialect inΓ (.buf 8 memN) :=
  .var (.mk (.store 8 memN) rfl
         (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
    (.ret .here)

/-- `out[i] := v; return out[i]` — store then read-back, exercising the byte
    store→load roundtrip through the real `stackStore 8`/`stackLoad 8`. -/
def byteRoundtripKernel : Com memrefDialect inΓ (.int 8) :=
  .var (.mk (.store 8 memN) rfl
         (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
    (.var (.mk (.load 8 memN) rfl
            (.cons .here (.cons (.there (.there .here)) .nil)))
      (.ret .here))

/-! ## 2. Independent byte-view reference (no `stackSet`/`stackGet`)

The spec is written directly as a byte-array update, *not* by reference to the
dialect's `stackSet`/`stackGet` — so `denote = spec` is an independent cross-check
that the byte store writes cell `i mod memN` and leaves every other cell
untouched (the no-overrun property, at the denotational level). -/

/-- The stored buffer: byte `v` at index `i mod memN`, all other cells unchanged. -/
def specStore (buf : Fin memN → BitVec 8) (i : BitVec 64) (v : BitVec 8) :
    Fin memN → BitVec 8 :=
  fun j => if j.val = i.toNat % memN then v else buf j

/-- Byte equality of two `memN`-cell buffers as a decidable `Bool`. -/
def bufEqB (f g : Fin memN → BitVec 8) : Bool :=
  (List.finRange memN).all (fun j => f j == g j)

/-- Input valuation `out, i, v`. -/
def val (buf : Fin memN → BitVec 8) (i : BitVec 64) (v : BitVec 8) :
    Ctxt.Valuation (d := memrefDialect) inΓ :=
  .cons buf (.cons i (.cons v .nil))

/-! ## 3. `denote = spec` gates (the byte store writes one cell, no overrun) -/

/-- **Store, all-zero buffer.** `denote (out[0] := 7)` = the byte-view spec. -/
example : bufEqB ((byteStoreKernel.denote (val (fun _ => 0) 0 7))) (specStore (fun _ => 0) 0 7)
    = true := by native_decide

/-- **Store at a non-zero runtime index** (exercises the SIB index ≠ 0). -/
example :
    bufEqB (byteStoreKernel.denote (val (fun j => BitVec.ofNat 8 (j.val + 1)) 2 0xAB))
      (specStore (fun j => BitVec.ofNat 8 (j.val + 1)) 2 0xAB) = true := by native_decide

/-- **Store at an out-of-range index** (exercises the `mod memN` wrap). -/
example :
    bufEqB (byteStoreKernel.denote (val (fun j => BitVec.ofNat 8 (7 * j.val + 3)) 9 0x5C))
      (specStore (fun j => BitVec.ofNat 8 (7 * j.val + 3)) 9 0x5C) = true := by native_decide

/-- **Roundtrip.** Reading back the just-stored byte returns `v` — independent of
    the initial buffer (the load hits exactly the cell the store wrote). -/
example : @Eq (BitVec 8)
    (byteRoundtripKernel.denote (val (fun j => BitVec.ofNat 8 (10 * j.val)) 3 0x42)) 0x42 := by
  native_decide

/-- The roundtrip is `v` for any representative index (no cross-cell bleed). -/
example : @Eq (BitVec 8) (byteRoundtripKernel.denote (val (fun _ => 0xFF) 1 0x01)) 0x01 := by
  native_decide

/-! ## 4. Byte lowering-preservation (equal-strength `w = 8` instance)

`Memref.lowerMemrefToJasmin_denote` is proved unconditionally for all widths, so
the byte case needs no separate proof — it is the `w = 8` instantiation. These
name it explicitly (no open goals, no new axiom). -/

/-- **Byte store lowering preserves denotation.** The jasmin image of the byte
    store (`stackStore 8 memN`) denotes to `transTy` of the memref store's
    denotation. Instance of the general width-parametric theorem. -/
theorem byteStore_lowering_denote (V : Ctxt.Valuation (d := memrefDialect) inΓ) :
    (lowerMemrefToJasmin byteStoreKernel).denote (mapVal V)
      = transTy (byteStoreKernel.denote V) :=
  lowerMemrefToJasmin_denote byteStoreKernel V

/-- **Byte roundtrip lowering preserves denotation.** -/
theorem byteRoundtrip_lowering_denote (V : Ctxt.Valuation (d := memrefDialect) inΓ) :
    (lowerMemrefToJasmin byteRoundtripKernel).denote (mapVal V)
      = transTy (byteRoundtripKernel.denote V) :=
  lowerMemrefToJasmin_denote byteRoundtripKernel V

/-! ## 5. Syntactic witness: the lowered jasmin uses byte-width `stackStore 8` -/

/-- Does any node carry `stackStore 8` / `stackLoad 8` (byte-width, not 64-bit)? -/
def comHasByteStackOp {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Bool
  | .ret _ => false
  | .var e body =>
      (match e.op with
       | .stackStore 8 _ => true
       | .stackLoad 8 _ => true
       | _ => false) || comHasByteStackOp body

/-- **The lowered store kernel emits a byte-width `stackStore 8`** (not the
    64-bit `stackStore 64` the `.memref` path would give). -/
theorem byteStore_lowers_to_stackStore8 :
    comHasByteStackOp (lowerMemrefToJasmin byteStoreKernel) = true := by native_decide

/-- **The lowered roundtrip kernel emits byte-width `stackStore 8` + `stackLoad 8`.** -/
theorem byteRoundtrip_lowers_to_byteStackOps :
    comHasByteStackOp (lowerMemrefToJasmin byteRoundtripKernel) = true := by native_decide

/-! ## 6. x86 export witness: `STOREIDX` / `LOADIDX` at SIB scale 1 (`uint8_t`)

`opToLinstrR` selects the SIB scale from the op width `w` as `w / 8`; byte width
gives scale `1` — the `uint8_t` stride — which `LprogAsmPrinter` renders as a
`movb` (store) / `movzbl` (load), a one-byte access with no overrun. -/

/-- The exported byte store is a `STOREIDX` with SIB **scale 1**. -/
theorem byteStore_export_scale1 :
    opToLinstrR (.stackStore 8 memN) "out" [.reg "base", .reg "idx", .reg "val"]
      = .Lopn [.reg "out"] "STOREIDX" [.arrIdx "base" "idx" 1, .reg "val"] := rfl

/-- The exported byte load is a `LOADIDX` with SIB **scale 1**. -/
theorem byteLoad_export_scale1 :
    opToLinstrR (.stackLoad 8 memN) "dst" [.reg "base", .reg "idx"]
      = .Lopn [.reg "dst"] "LOADIDX" [.arrIdx "base" "idx" 1] := rfl

/-- Contrast: the 64-bit store keeps SIB **scale 8** — the two widths diverge
    exactly at the SIB stride, confirming the scale is width-driven. -/
theorem wordStore_export_scale8 :
    opToLinstrR (.stackStore 64 memN) "out" [.reg "base", .reg "idx", .reg "val"]
      = .Lopn [.reg "out"] "STOREIDX" [.arrIdx "base" "idx" 8, .reg "val"] := rfl

/-! Scale 1 renders (in `LprogAsmPrinter.renderLinstrR`) as a `movb`: the
`STOREIDX` mov size is `scale * 8 = 8` bits, so the store is
`movb %val8, (%base,%idx,1)` — a width-exact one-byte write — and the `LOADIDX`
is `movzbl (%base,%idx,1), %dst32`. (Verified by reading the printer; the runtime
no-overrun check is the C KAT below.) -/

/-! ## 7. Bench KAT harness sketch — the no-overrun `movb` test

The binding correctness gate is a byte-identity KAT against a C reference
(in-Lean gates stay cheap; the C KAT is the ground truth). The distinguishing test
is **no overrun**: a byte store at index `i` must leave bytes `i-1` and `i+1`
untouched; a bug that emits `movq`/`movl` instead of `movb` would clobber the
7 / 3 neighbouring bytes and the test fails.

```c
/* bench/bytememref_compare/kat_movb_no_overrun.c */
#include <stdint.h>
#include <string.h>
#include <assert.h>

/* Emitted kernel: void byte_store(uint8_t *out, uint64_t i, uint8_t v);
 * out[i] = v;  (a single movb %val8, (%out,%i,1))                       */
extern void byte_store(uint8_t *out, uint64_t i, uint8_t v);

int main(void) {
  uint8_t buf[8];
  for (int i = 1; i < 7; i++) {
    memset(buf, 0xEE, sizeof buf);        /* sentinel every cell */
    byte_store(buf, (uint64_t)i, 0x5C);   /* write ONE byte at i */
    assert(buf[i]     == 0x5C);           /* the stored byte     */
    assert(buf[i - 1] == 0xEE);           /* left neighbour intact  (movb, not movl/movq) */
    assert(buf[i + 1] == 0xEE);           /* right neighbour intact */
  }
  /* wrap / roundtrip: out[i] := v; r := out[i]; r == v */
  memset(buf, 0, sizeof buf);
  byte_store(buf, 3, 0x42);
  assert(buf[3] == 0x42);
  return 0;
}
```

Makefile wiring (orchestrator-side): assemble the exported `.s` (`byte_store:` the
`movb`-rendered `STOREIDX`), link with `kat_movb_no_overrun.c`, run — exit 0 iff
every one-byte write left its neighbours' sentinel bytes intact.
-/

end CatCrypt.Crypto.SecureCompilation.Dialects.ByteMemrefFrontValidate
