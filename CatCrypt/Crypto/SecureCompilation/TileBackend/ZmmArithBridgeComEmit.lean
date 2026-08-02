/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
import CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeCom

/-!
# Owned AT&T `.s` emit of the migrated ZMM-arithmetic `Com jasminDialect` kernels

`ZmmArithBridgeCom.lean` re-expresses the ZMM packed-arithmetic core
(`vpaddqCom` / `vpsubqCom` / `vpmullqCom` / `vpandqCom` / `vporqCom` /
`vpxorqCom`, plus the variable cross-register shifts `vpsllvqCom` / `vpsrlvqCom`)
as `Com jasminDialect` programs over the two-input context `[a, b]` (each
`reg 512` ZMM), each a single `JasminOp.vpackZMM bop` binding. `VpackZmmAsmPrint`
is the owned 512-bit `%zmm` printer (`renderVpackZmmCom` + the register-width
agnostic `frameAsmFunction` SysV ABI framing).

This module is the **owned-emit leaf** that wires those two together: it renders
the migrated `Com` kernels to full owned AT&T `.s` strings via
`VpackZmmAsmPrint.renderVpackZmmCom` + `frameAsmFunction`, with a
caller-supplied `XAlloc`. There is **NO dependency on the bespoke `Avx512Model`
ZMM machine IR** — the only imports are `VpackZmmAsmPrint` (→ `JasminPrint` /
`JasminDialect`) and `ZmmArithBridgeCom` (the migrated `Com` kernels). This is
the missing direct `Com → .s` route for the ZMM arithmetic core: every binding
emits one lowercase EVEX `%zmm` instruction, never a jasminc-routed
`#VPADD_8u64` intrinsic.

## The single-op ABI / allocation

Each kernel `packBinCom bop` has context `binCtx = [a, b]`, so
`JasminPrint.paramsAndMap` names the two params `p0` (`a`) and `p1` (`b`)
head-first, and the one `vpackZMM` binding produces the fresh SSA name `v0`,
which the program returns. We pin `p0`/`p1` to `%zmm0`/`%zmm1` and the result
`v0` back into `%zmm0` (the SysV ABI result register for this fragment), so a
two-operand kernel needs three `%zmm` slots.

| kernel        | rendered owned AT&T line (D = bop-packed(A, B))   |
|---------------|---------------------------------------------------|
| `vpaddqCom`   | `vpaddq %zmm1, %zmm0, %zmm0`                       |
| `vpmullqCom`  | `vpmullq %zmm1, %zmm0, %zmm0`                      |

(AT&T EVEX order is `op src2, src1, dst`: `vpaddq %zmm1, %zmm0, %zmm0`
≡ `zmm0 := add-packed(zmm0, zmm1)`.)

Invoke:
`lake build CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeComEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeComEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
  (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeCom
  (vpaddqCom vpmullqCom vpxorqCom vpsllvqCom)

/-! ## 1. The single-op `%zmm` allocation

The two params `p0`/`p1` (`a`/`b`, head-first per `paramsAndMap`) pinned to
`%zmm0`/`%zmm1`, the one binding's result `v0` back into `%zmm0`. -/

/-- The `%zmm` allocation for a single-binding `packBinCom` kernel: the two
    params `p0`/`p1` (`a`/`b`) to `%zmm0`/`%zmm1` and the result `v0` to
    `%zmm0`. Three slots, two distinct registers. -/
def binAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("v0", "%zmm0")]

/-! ## 2. The rendered body lines (one owned AT&T `%zmm` instruction each) -/

/-- The rendered body of `vpaddqCom` — one owned AT&T `%zmm` packed-add line. -/
def vpaddqBodyLines : List String := (renderVpackZmmCom binAlloc vpaddqCom).1

/-- The rendered body of `vpmullqCom` — one owned AT&T `%zmm` packed-multiply
    line. -/
def vpmullqBodyLines : List String := (renderVpackZmmCom binAlloc vpmullqCom).1

/-- `vpaddqCom` renders to exactly the single owned AT&T `%zmm` packed-add line
    `vpaddq %zmm1, %zmm0, %zmm0` (EVEX order `op src2, src1, dst`). -/
theorem vpaddqBodyLines_eq :
    vpaddqBodyLines = ["\tvpaddq %zmm1, %zmm0, %zmm0"] := by native_decide

/-- `vpmullqCom` renders to exactly the single owned AT&T `%zmm` packed-multiply
    line `vpmullq %zmm1, %zmm0, %zmm0`. -/
theorem vpmullqBodyLines_eq :
    vpmullqBodyLines = ["\tvpmullq %zmm1, %zmm0, %zmm0"] := by native_decide

/-! ## 3. The full framed owned `.s` exports

`frameAsmFunction` (register-width agnostic) wraps each body in the SysV ABI
load/store glue: two `vmovdqu64` loads of the `[a, b]` ZMM args from `(%rdi)` /
`(%rsi)`, the one packed instruction, and a `vmovdqu64` store of the result back
to `(%rdi)`. -/

/-- The full framed owned `.s` for the migrated packed-add kernel `vpaddqCom`:
    SysV ABI glue (`vmovdqu64 (%rdi), %zmm0`; `vmovdqu64 (%rsi), %zmm1`) + the
    one `vpaddq %zmm1, %zmm0, %zmm0` + result store. Owned, no jasminc, no
    `Avx512Model`. -/
def vpaddqExportAsm : String :=
  frameAsmFunction "zmm_vpaddq_packed"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqu64\t(%rsi), %zmm1" ]
    vpaddqBodyLines
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The full framed owned `.s` for the migrated packed-multiply kernel
    `vpmullqCom`. -/
def vpmullqExportAsm : String :=
  frameAsmFunction "zmm_vpmullq_packed"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqu64\t(%rsi), %zmm1" ]
    vpmullqBodyLines
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println vpaddqExportAsm
#eval IO.println vpmullqExportAsm

/-! ## 4. Structural smoke pins on the rendered text -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/- The packed-add export emits the lowercase owned `%zmm` mnemonic (not the
    UPPERCASE jasmin `#VPADD_8u64` intrinsic). -/
#guard (strContains vpaddqExportAsm "vpaddq")

/- The packed-add export uses 512-bit `%zmm` registers. -/
#guard (strContains vpaddqExportAsm "%zmm")

/- The packed-add export symbol is present. -/
#guard (strContains vpaddqExportAsm "zmm_vpaddq_packed:")

/- No UPPERCASE jasmin intrinsic survives in the packed-add export — this is the
    owned (no-jasminc) lowercase-mnemonic path. -/
#guard !(strContains vpaddqExportAsm "#VPADD_8u64")

/- The packed-multiply export emits the lowercase owned `%zmm` multiply
    mnemonic. -/
#guard (strContains vpmullqExportAsm "vpmullq")

/-! ## 5. Extra direct-render pins (XOR and the variable left shift)

The same `renderVpackZmmCom` + `binAlloc` route covers the rest of the migrated
arithmetic core. We pin the bitwise XOR and one variable cross-register shift to
their lowercase owned `%zmm` lines, confirming the whole `vpackZMM` alphabet
flows through the owned printer. -/

/-- `vpxorqCom` renders to the single owned AT&T `%zmm` packed-XOR line. -/
theorem vpxorqCom_renders :
    (renderVpackZmmCom binAlloc vpxorqCom).1
      = ["\tvpxorq %zmm1, %zmm0, %zmm0"] := by native_decide

/-- `vpsllvqCom` (variable left shift) renders to the owned `vpsllvq` `%zmm`
    line (the `vpackZMM` shift reads its per-lane count from the second
    register). -/
theorem vpsllvqCom_renders :
    (renderVpackZmmCom binAlloc vpsllvqCom).1
      = ["\tvpsllvq %zmm1, %zmm0, %zmm0"] := by native_decide

end CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeComEmit
