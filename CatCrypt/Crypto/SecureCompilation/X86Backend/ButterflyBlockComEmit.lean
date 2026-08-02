/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
import CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom

/-!
# Public owned `.s` emit for the migrated NTT radix-2 butterfly (`Com jasminDialect`, 512-bit ZMM)

This is the **public emit entry point** for the SIMD-dialect-unified NTT radix-2
Cooley–Tukey butterfly leaf (`ButterflyBlockCom.butterflyHiCom` /
`butterflyLoCom`): it renders the migrated `Com jasminDialect` (`vpackZMM`
fragment, `reg 512` ZMM registers) to **owned AT&T `.s`** through
`VpackZmmAsmPrint.renderVpackZmmCom` + `VsimdAsmPrint.frameAsmFunction`, with a
**caller-supplied `XAlloc`** mapping the params (`p0`/`p1`/`p2` = `w`/`a`/`b`)
and the SSA temps (`v0` = `prod`, `v1` = result) to `%zmm` registers.

```
ButterflyBlockCom.butterflyHiCom  (Com jasminDialect, vpackZMM)
        │  XAlloc (caller-supplied: param + SSA-temp → %zmm)
        ▼  VpackZmmAsmPrint.renderVpackZmmCom
   List String  (owned AT&T %zmm body lines)
        │  VsimdAsmPrint.frameAsmFunction  (SysV ABI load/store glue)
        ▼
   String        (a complete owned `.s`, symbol `ntt_butterfly_hi_vpackzmm`)
```

This is the **no-jasminc, no-`Avx512Model`** route: the import set is exactly
`VpackZmmAsmPrint` (→ `JasminPrint`/`JasminDialect`, the de-Bruijn→name walk and
the `%zmm` operand renderer) and `ButterflyBlockCom` (the migrated `Com`). The
bespoke `Avx512Model` (`ZInstr`/`ZState`/`runZBlock`) AVX-512 machine — which the
pre-migration `ButterflyBlockRealized.lean` rode — is **not** in the lowering or
printing path of this emit.

## What this module adds over the printer's worked example

`VpackZmmAsmPrint.lean` pins one fixed allocation (`bflyAlloc`) inline as a
demonstration. This module exposes the emit as a **function of the allocation**
(`emitButterflyHi`/`emitButterflyLo : XAlloc → String`), so a register allocator
upstream supplies the `%zmm` assignment, and frames the SysV-ABI glue (`vmovdqu64`
loads from `(%rdi)`/`(%rsi)`/`(%rdx)`, store to `(%rdi)`) around the rendered
body. The concrete `bflyHiAlloc`/`bflyLoAlloc` + `native_decide` pins below fix
the rendered body lines so a renderer/de-Bruijn regression is caught at compile
time.

Invoke:
`lake build CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockComEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockComEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom renderVpackZmmComAutoZmm)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
  (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom
  (butterflyHiCom butterflyLoCom)

/-! ## 1. The SysV-ABI glue (register-width agnostic, shared by `hi`/`lo`)

Three `reg 512` inputs `w`/`a`/`b` arrive as pointers in `%rdi`/`%rsi`/`%rdx`
(SysV integer args 0/1/2); the result is stored back through `%rdi`. The
allocation must therefore pin `p0`/`p1`/`p2` (the head-first `paramsAndMap` names
for `w`/`a`/`b`) to the `%zmm` registers these loads target, and the result SSA
name to the `%zmm` the store reads. -/

/-- The ABI **load** prologue: pull `w`/`a`/`b` from `(%rdi)`/`(%rsi)`/`(%rdx)`
    into `%zmm0`/`%zmm1`/`%zmm2`. -/
def bflyAbiLoads : List String :=
  [ "\tvmovdqu64\t(%rdi), %zmm0"
  , "\tvmovdqu64\t(%rsi), %zmm1"
  , "\tvmovdqu64\t(%rdx), %zmm2" ]

/-- The ABI **store** epilogue: write the butterfly result (`%zmm0`) back through
    the first argument pointer `%rdi`. -/
def bflyAbiStore : List String := [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-! ## 2. The public emit, parametric over the caller-supplied `XAlloc`

`emitButterflyHi`/`emitButterflyLo` take the `%zmm` allocation as an argument:
they render the migrated `Com` body via `renderVpackZmmCom` and frame it with the
ABI glue under the owned export symbol. The symbol the `hi` slice exports is
`ntt_butterfly_hi_vpackzmm`; the `lo` slice exports `ntt_butterfly_lo_vpackzmm`. -/

/-- The owned `.s` for the NTT butterfly **`hi`** slice (`hi = a + (w ⊙ b)`),
    under the caller-supplied `%zmm` allocation `alloc`. Renders
    `butterflyHiCom`'s two `vpackZMM` bindings to owned `%zmm` AT&T lines and
    frames them with the SysV-ABI load/store glue. No `Avx512Model`, no jasminc. -/
def emitButterflyHi (alloc : XAlloc) : String :=
  frameAsmFunction "ntt_butterfly_hi_vpackzmm"
    bflyAbiLoads (renderVpackZmmCom alloc butterflyHiCom).1 bflyAbiStore

/-- The owned `.s` for the NTT butterfly **`lo`** slice (`lo = a − (w ⊙ b)`),
    under the caller-supplied `%zmm` allocation `alloc`. -/
def emitButterflyLo (alloc : XAlloc) : String :=
  frameAsmFunction "ntt_butterfly_lo_vpackzmm"
    bflyAbiLoads (renderVpackZmmCom alloc butterflyLoCom).1 bflyAbiStore

/-! ### 2b. The auto-allocated emit (no hand-written `%zmm` map)

`emitButterflyHiAuto`/`emitButterflyLoAuto` need no caller `XAlloc`: the `%zmm`
assignment is computed by `VpackZmmAsmPrint.renderVpackZmmComAutoZmm` (params →
`%zmm0..`, temps linear-scanned over `%zmm0..31`). The auto-allocator draws the
next free `%zmm4` for the result (where the hand `bflyHiAlloc` aliased it back
onto `%zmm0`), so the ABI **store** is built from the returned ret register
(`.2`) — `vmovdqu64 retReg, (%rdi)` — rather than the fixed `bflyAbiStore`. The
two `vpackZMM` mnemonics + their src/dst data flow are byte-identical to the
hand-allocated render; only the result/store register differs (both valid,
spill-free, no `<UNALLOCATED>`). -/

/-- The ABI store of a butterfly result that landed on `retReg`. -/
def bflyAbiStoreOf (retReg : String) : List String :=
  [ "\tvmovdqu64\t" ++ retReg ++ ", (%rdi)" ]

/-- The owned `.s` for the NTT butterfly **`hi`** slice with the `%zmm`
    allocation computed automatically — no hand-written map. The result register
    (from `renderVpackZmmComAutoZmm`'s `.2`) drives the ABI store. -/
def emitButterflyHiAuto : String :=
  let (body, retReg) := renderVpackZmmComAutoZmm butterflyHiCom
  frameAsmFunction "ntt_butterfly_hi_vpackzmm" bflyAbiLoads body (bflyAbiStoreOf retReg)

/-- The owned `.s` for the NTT butterfly **`lo`** slice with the `%zmm`
    allocation computed automatically — no hand-written map. -/
def emitButterflyLoAuto : String :=
  let (body, retReg) := renderVpackZmmComAutoZmm butterflyLoCom
  frameAsmFunction "ntt_butterfly_lo_vpackzmm" bflyAbiLoads body (bflyAbiStoreOf retReg)

/-! ## 3. The emitted artifacts (auto-allocated — no hand `%zmm` map)

The concrete artifacts are emitted through the auto-allocator
(`emitButterflyHiAuto`/`emitButterflyLoAuto`), retiring the per-file hand
`bflyHiAlloc`/`bflyLoAlloc`. The §4 `native_decide` pins fix the rendered body
lines so a renderer/de-Bruijn regression is caught at compile time. -/

/-- The emitted owned `.s` for the NTT butterfly `hi` step (auto-allocated). -/
def ntt_butterfly_hi_vpackzmm_asm : String := emitButterflyHiAuto

/-- The emitted owned `.s` for the NTT butterfly `lo` step (auto-allocated). -/
def ntt_butterfly_lo_vpackzmm_asm : String := emitButterflyLoAuto

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println ntt_butterfly_hi_vpackzmm_asm
#eval IO.println ntt_butterfly_lo_vpackzmm_asm

/-! ## 4. `native_decide` pins on the rendered body lines

The auto-allocated `vpackZMM` body of each slice is fixed exactly (a renderer or
de-Bruijn regression flips these). AT&T EVEX order is `op src2, src1, dst`. The
auto-allocator draws the next free `%zmm4` for the result; the result register
is also the `.2` the ABI store reads. -/

/-- The auto-allocated `hi` body renders to exactly the two owned AT&T `%zmm`
    lines `vpmullq %zmm2, %zmm0, %zmm3` (prod = w ⊙ b) and
    `vpaddq %zmm3, %zmm1, %zmm4` (hi = a + prod), with the result on `%zmm4`. -/
theorem hi_body_lines :
    renderVpackZmmComAutoZmm butterflyHiCom
      = (["\tvpmullq %zmm2, %zmm0, %zmm3", "\tvpaddq %zmm3, %zmm1, %zmm4"], "%zmm4") := by
  native_decide

/-- The auto-allocated `lo` body renders to exactly the two owned AT&T `%zmm`
    lines `vpmullq %zmm2, %zmm0, %zmm3` (prod = w ⊙ b) and
    `vpsubq %zmm3, %zmm1, %zmm4` (lo = a − prod), with the result on `%zmm4`. -/
theorem lo_body_lines :
    renderVpackZmmComAutoZmm butterflyLoCom
      = (["\tvpmullq %zmm2, %zmm0, %zmm3", "\tvpsubq %zmm3, %zmm1, %zmm4"], "%zmm4") := by
  native_decide

/-! ## 5. Structural smoke pins on the emitted `.s` text -/

/- The `hi` emit carries the packed multiply (lowercase owned mnemonic). -/
#guard (strContains ntt_butterfly_hi_vpackzmm_asm "vpmullq")

/- The `hi` emit carries the packed add (lowercase owned mnemonic). -/
#guard (strContains ntt_butterfly_hi_vpackzmm_asm "vpaddq")

/- The `lo` emit carries the packed subtract (lowercase owned mnemonic). -/
#guard (strContains ntt_butterfly_lo_vpackzmm_asm "vpsubq")

/- The exported `hi` symbol is present. -/
#guard (strContains ntt_butterfly_hi_vpackzmm_asm "ntt_butterfly_hi_vpackzmm:")

/- The exported `lo` symbol is present. -/
#guard (strContains ntt_butterfly_lo_vpackzmm_asm "ntt_butterfly_lo_vpackzmm:")

/- The body uses 512-bit `%zmm` registers (not the 128-bit `%xmm` of the
    `VsimdAsmPrint` fragment). -/
#guard (strContains ntt_butterfly_hi_vpackzmm_asm "%zmm")

/- No UPPERCASE jasmin intrinsic survives in the `hi` emit — this is the owned
    (no-jasminc) lowercase-mnemonic path. -/
#guard !(strContains ntt_butterfly_hi_vpackzmm_asm "#VPMULL_8u64")

end CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockComEmit
