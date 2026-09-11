/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint

/-!
# Owned `.s` emit for `vpack_add8` migrated onto the unified `Com jasminDialect` (512-bit ZMM)

`bench/thir_front_vpack` exposes a homogeneous 8-lane packed add
`vpack_add8(x, y) = thVpack .add x y` over two 512-bit ZMM inputs (one 512-bit
output): per lane `k ∈ 0..7`, `out[k] = x[k] + y[k] (mod 2^64)`, **no cross-lane
carry**.

The pre-migration emit (`VpackAdd8Emit.lean`) expresses this as a single
`Avx512Model.ZInstr.vpaddq` over the bespoke AVX-512 register machine
(`ZState`/`runZBlock`), rendered by `Avx512AsmPrinter.renderZInstr`. This module
is the **SIMD-dialect-unification** twin: the same one-`vpaddq` kernel as a
straight-line `Com jasminDialect` program over `reg 512` (ZMM) registers, off the
bespoke `Avx512Model` machine, rendered through
`VpackZmmAsmPrint.renderVpackZmmCom` + `VsimdAsmPrint.frameAsmFunction`.

```
vpackAdd8Com  (Com jasminDialect, one vpackZMM .add)
        │  XAlloc (caller-supplied: param + SSA-result → %zmm)
        ▼  VpackZmmAsmPrint.renderVpackZmmCom
   List String  (owned AT&T %zmm body line)
        │  VsimdAsmPrint.frameAsmFunction  (SysV ABI load/store glue)
        ▼
   String        (a complete owned `.s`, symbol `vpack_add8`)
```

The import set is exactly `VpackZmmAsmPrint` (→ `JasminPrint`/`JasminDialect`, the
de-Bruijn→name walk + the `%zmm` operand renderer; `VsimdAsmPrint`'s `XAlloc` /
`frameAsmFunction` reused transitively). The bespoke `Avx512Model`
(`ZInstr`/`ZState`/`runZBlock`) and its `Avx512AsmPrinter` are **not** in the
lowering or printing path of this emit — it is the no-jasminc, no-`Avx512Model`
route.

## Op mapping

The body is exactly one op, the single `.add` ZOp of the pre-migration block:

| `Avx512Model.ZInstr` | `Com jasminDialect` op       | denote        |
|----------------------|------------------------------|---------------|
| `.vpaddq "out" "x" "y"` | `JasminOp.vpackZMM .add` | `zmmPackQ .add` |

`zmmPackQ .add` is the carry-free 8×u64 packed-lane add — the verified-dialect
image of `#VPADD_8u64`, the same lane semantics the bespoke `ZInstr.vpaddq`
(`VectorTy.map₂ laneAddQ`) computes. The single `.add` op has the `vpackZMM`
equivalent, so the migration is complete (no out-of-fragment op).

ABI (matches `bench/thir_front_vpack/vpack_kat.c` exactly):
  `void vpack_add8(uint64_t *out /*%rdi*/, const uint64_t *inp /*%rsi*/);`
    out  = 8 × u64  (lane 0 = low 64 bits, little-endian)
    inp  = 16 × u64 = x[0..7] then y[0..7]

The 128-bit baseline-AVX `vpack_add8_ymm.s` fallback (four 128-bit `Vec128`
`vpaddq`) is a different (128-bit) machine and stays on the pre-migration emit;
this twin migrates the AVX-512 ZMM `.s`.

Invoke:
`lake build CatCrypt.Crypto.SecureCompilation.X86Backend.VpackAdd8VpackZmmEmit`
or `lake env lean --run
  CatCrypt/Crypto/SecureCompilation/X86Backend/VpackAdd8VpackZmmEmit.lean`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VpackAdd8VpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
  (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-! ## 1. The dialect-native `vpack_add8` program `Com jasminDialect`

A single `reg 512` (one ZMM 8×u64 lane-vector) is the kernel's working type. The
packed add has two inputs, in de-Bruijn order `[x, y]`:

* `x` — the first addend (de Bruijn `0`, `.here`);
* `y` — the second addend (de Bruijn `1`, `.there .here`).

```
let out = vpackZMM add x y     -- out := x + y   (per-lane, no cross-lane carry)
ret out
```
-/

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- The input context of `vpack_add8`: `[x, y]`, each `reg 512`. -/
abbrev vpackCtx : Ctxt jasminDialect := [r512, r512]

/-- The migrated `vpack_add8` body as a `Com jasminDialect` over `reg 512`
    registers — the dialect-native equivalent of the bespoke single
    `ZInstr.vpaddq "out" "x" "y"`: `out = x + y` per 64-bit lane (no cross-lane
    carry). `x = .here`, `y = .there .here`. -/
def vpackAdd8Com : Com jasminDialect vpackCtx r512 :=
  -- out := x + y   (x = .here, y = .there .here)
  .var (.mk (.vpackZMM .add) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-! ## 2. Denotation characterization

The program computes the verified-dialect packed add, with `zmmPackQ` the 8×u64
packed-lane semantics. The proof is `rfl`: `Com.denote` of the single-binding
program unfolds definitionally through the `vpackZMM` denote arm to the one
`zmmPackQ` call. -/

/-- **`vpack_add8` denotation pin.** On any input valuation `⟨x, y⟩`,
    `vpackAdd8Com` denotes to `zmmPackQ .add x y` — the verified-dialect packed
    `x + y`, exactly the value the bespoke `ZInstr.vpaddq` writes into `"out"`
    lane-by-lane (no cross-lane carry). -/
theorem vpackAdd8Com_denote (x y : BitVec 512) :
    vpackAdd8Com.denote (.cons x (.cons y .nil))
      = zmmPackQ .add x y :=
  rfl

/-! ## 3. The owned `.s`, parametric over the caller-supplied `XAlloc`

`emitVpackAdd8` takes the `%zmm` allocation as an argument: it renders the
migrated `Com` body via `renderVpackZmmCom` and frames it with the SysV-ABI glue
under the owned export symbol `vpack_add8` (matching the pre-migration emit's
symbol and the `vpack_kat.c` harness).

`inp[0..7] = x` at `(%rsi)`, `inp[8..15] = y` at `64(%rsi)`; the 8-lane result
stores to `(%rdi)`. -/

/-- The ABI **load** prologue: pull `x`/`y` from `(%rsi)`/`64(%rsi)` into
    `%zmm0`/`%zmm1`. -/
def vpackAbiLoads : List String :=
  [ "\tvmovdqu64\t(%rsi), %zmm0"
  , "\tvmovdqu64\t64(%rsi), %zmm1" ]

/-- The ABI **store** epilogue: write the packed-add result (`%zmm0`) back through
    the output pointer `%rdi`. -/
def vpackAbiStore : List String := [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The owned `.s` for `vpack_add8` (`out = x + y`, 8×u64, no cross-lane carry),
    under the caller-supplied `%zmm` allocation `alloc`. Renders `vpackAdd8Com`'s
    single `vpackZMM .add` binding to an owned `%zmm` AT&T line and frames it with
    the SysV-ABI load/store glue. No `Avx512Model`, no jasminc. -/
def emitVpackAdd8 (alloc : XAlloc) : String :=
  frameAsmFunction "vpack_add8"
    vpackAbiLoads (renderVpackZmmCom alloc vpackAdd8Com).1 vpackAbiStore

/-! ## 4. A concrete allocation + the emitted artifact

A representative caller allocation: the two params `p0`/`p1` (`x`/`y`, head-first
per `paramsAndMap`) to `%zmm0`/`%zmm1`, and the result `v0` to `%zmm0` (so the
ABI store of `%zmm0` writes the packed-add output, overwriting the consumed
`x`). -/

/-- A concrete `%zmm` allocation for `vpack_add8`: params `x`/`y` → `%zmm0`/`%zmm1`,
    result → `%zmm0`. -/
def vpackAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("v0", "%zmm0")]

/-- The emitted owned `.s` for `vpack_add8` (owned AVX-512 ZMM, via `Com`). -/
def vpack_add8_vpackzmm_asm : String := emitVpackAdd8 vpackAlloc

-- Print the emitted owned `.s` for visual inspection.
-- #eval IO.println vpack_add8_vpackzmm_asm

/-! ## 5. `native_decide` pin on the rendered body line

The rendered `vpackZMM` body is fixed exactly (a renderer or de-Bruijn regression
flips this). AT&T EVEX order is `op src2, src1, dst`. -/

/-- The body renders to exactly the one owned AT&T `%zmm` line
    `vpaddq %zmm1, %zmm0, %zmm0` (out = x + y). -/
theorem body_lines :
    (renderVpackZmmCom vpackAlloc vpackAdd8Com).1
      = ["\tvpaddq %zmm1, %zmm0, %zmm0"] := by
  native_decide

/-! ## 6. Structural smoke pins on the emitted `.s` text

These reproduce the pre-migration emit's smoke pins (export symbol present, the
single `vpaddq` issued), now over the `Com`-rendered `.s`. -/

/-- The emit names the export symbol. -/
theorem asm_has_export :
    strContains vpack_add8_vpackzmm_asm "vpack_add8:" = true := by native_decide

/- The emit carries the packed add (lowercase owned `%zmm` mnemonic). -/
#guard (strContains vpack_add8_vpackzmm_asm "vpaddq")

/- The body uses 512-bit `%zmm` registers (not the 128-bit `%xmm` of the
    `VsimdAsmPrint` fragment). -/
#guard (strContains vpack_add8_vpackzmm_asm "%zmm")

/- No UPPERCASE jasmin intrinsic survives — this is the owned (no-jasminc)
    lowercase-mnemonic path. -/
#guard !(strContains vpack_add8_vpackzmm_asm "#VPADD_8u64")

/-! ## 7. Emit driver -/

/-- Write the owned-backend (`Com`-rendered AVX-512 ZMM) `.s` to
    `bench/thir_front_vpack/gen_com/`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/thir_front_vpack/gen_com"
  IO.FS.writeFile "bench/thir_front_vpack/gen_com/vpack_add8.s" vpack_add8_vpackzmm_asm
  IO.println "wrote bench/thir_front_vpack/gen_com/vpack_add8.s (owned Com vpackZMM .add, 8x u64)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.VpackAdd8VpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.VpackAdd8VpackZmmEmit in
/-- `lake env lean --run` entry point: emit the owned `Com`-rendered `vpack_add8`. -/
private def main : IO Unit := emit
