/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# ML-KEM 16-bit signed high-multiply (`VPMULHW`) on the UNIFIED `Com jasminDialect`

This is the SIMD-dialect-unification migration of the ML-KEM/FIPS-203 NTT
Montgomery high-multiply tile leaf. The pre-existing tile realisation
(`TileS16HighMul.lean`) expresses the 8-lane signed 16-bit high multiply over the
**bespoke** per-ISA vector machines (`Vec128.VInst8x16.vpmulhw`,
`Neon.NInst8x16.mulhs`, `Rvv.VInst8x16.vmulh`), each transported to the
shape-generic `TileModel.evalTileOp (lowerRegInstr (.mulhs …))`. The realising
hardware op is one packed signed high-multiply per ISA:

* **x86 AVX2** — `VPMULHW` (packed 8×i16 signed high-16 multiply)
* **ARM NEON** — `SQDMULH` / `SMULL;SMULL2;UZP2` high-half
* **RISC-V RVV** — `vmulh.vv` (`SEW = 16`, `VL = 8`)

The unified SIMD ops now live in `jasminDialect` as
`JasminOp.vsimd (op : SimdOp)` (SIMD-dialect-unification). The packed signed
high-16 multiply maps EXACTLY onto the unified op set:

* `VPMULHW`  ↦  `JasminOp.vsimd .mulhi16`   (denote `vpmulhw16W`,
  copied verbatim from `Vec128Model.laneMulHiS16` per lane)

so this module re-expresses the SAME 8-lane signed high-multiply step as a
straight-line `Com jasminDialect` over `reg 128` registers, off the bespoke
`Vec128`/`Neon`/`Rvv` machines (which the `*_is_tile_lowering` bridges in
`TileS16HighMul.lean` continue to cover). The op semantics (`SimdOp.denote
.mulhi16 = vpmulhw16W`) are byte-identical to the bespoke model's per-lane
`laneMulHiS16`.

`SimdOp.mulhi16` is the packed high-half only — the FIPS-203 `fqmul` Montgomery
reduction also uses the low product (`VPMULLW = packed .mul 16`), a subtract and
an arithmetic shift; those compose with this high-multiply at the NTT-butterfly
level. This module owns the dialect-native **high-multiply** leaf (the SIMD op
the §4 `TileS16HighMul` bridges realise) and its denotation.

## What is proved here

`s16HighMulCom` is the dialect-native VPMULHW step. `s16HighMulCom_denote`
characterizes its denotation on any `(a, b)` input valuation as

```
vpmulhw16W a b
```

— exactly the packed 8×i16 signed high-multiply the bespoke `vpmulhw` /
`SQDMULH` / `vmulh.vv` ops compute lane-by-lane (`laneMulHiS16` per lane). The
denote lemma elaborates by `rfl` (the `Com.denote` of a one-binding straight-line
program unfolds definitionally to the `SimdOp.denote .mulhi16` waist call).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMulCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register types and the input context

A single `reg 128` (one XMM lane-vector holding 8 × i16) is the kernel's working
type. The high-multiply step has two inputs, in de-Bruijn order `[a, b]`:

* `a` — the first 8×i16 operand (de Bruijn `0`, `.here`);
* `b` — the second 8×i16 operand (de Bruijn `1`, `.there .here`). -/

/-- The `reg 128` dialect type (one 16-byte XMM lane-vector = 8 × i16), abbreviated. -/
abbrev r128 : JasminTy := .reg 128

/-- The input context of the high-multiply step: `[a, b]`, each `reg 128`. -/
abbrev mulCtx : Ctxt jasminDialect := [r128, r128]

/-! ## 2. The dialect-native high-multiply step `Com jasminDialect`

```
let hi = vsimd mulhi16 a b          -- hi := vpmulhw(a, b)   (packed 8×i16 signed high-16)
ret hi
```

Binding 1 (`mulhi16`) consumes `a` (`.here` in `mulCtx`) and `b` (`.there .here`),
producing `hi` at the front. Under the extended context `[hi, a, b]`, the return
yields `hi` (`.here`). -/

/-- The migrated 8-lane signed 16-bit high-multiply step as a `Com jasminDialect`
    over `reg 128` registers — the dialect-native equivalent of the bespoke
    `Vec128.VInst8x16.vpmulhw` / `Neon.mulhs` / `Rvv.vmulh` that
    `TileS16HighMul.lean`'s §4 bridges realise. -/
def s16HighMulCom : Com jasminDialect mulCtx r128 :=
  -- hi := vpmulhw(a, b)
  .var (.mk (.vsimd .mulhi16) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-! ## 3. Denotation characterization

`s16HighMulCom` computes `vpmulhw16W a b` — the same 8-lane signed high-multiply
the bespoke ops produce, with `vpmulhw16W` the KAT-pinned waist function
(`laneMulHiS16W` per lane `= Vec128Model.laneMulHiS16`). The proof is `rfl`:
`Com.denote` of the one-binding program unfolds definitionally through the
`vsimd .mulhi16` denote arm to the `SimdOp.denote .mulhi16` waist call. -/

/-- **High-multiply-step denotation pin.** On any input valuation `⟨a, b⟩`,
    `s16HighMulCom` denotes to `vpmulhw16W a b` — exactly the packed 8×i16
    signed high-16 multiply the bespoke `vpmulhw` / `SQDMULH` / `vmulh.vv` ops
    compute lane-by-lane. -/
theorem s16HighMulCom_denote (a b : BitVec 128) :
    s16HighMulCom.denote (.cons a (.cons b .nil))
      = vpmulhw16W a b :=
  rfl

/-- Spelled with `SimdOp.denote` directly (the dialect's denote dispatch target),
    confirming the migrated step rides the SAME unified `SimdOp.mulhi16`
    semantics the lowering and emit consume. -/
theorem s16HighMulCom_denote_simdOp (a b : BitVec 128) :
    s16HighMulCom.denote (.cons a (.cons b .nil))
      = (SimdOp.mulhi16).denote a b :=
  rfl

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMulCom
