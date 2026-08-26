/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
import CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom

/-!
# Owned AT&T `.s` emit for the migrated Keccak θ `vpackZMM` kernels

This is the **owned-emit leaf** for the `Com jasminDialect` Keccak θ kernels of
`KeccakThetaPiCom.lean` (`parityCom` / `dCom`). It renders them to owned
512-bit `%zmm` AT&T `.s` through `VpackZmmAsmPrint.renderVpackZmmCom`, with a
caller-supplied `XAlloc` register assignment and `frameAsmFunction` SysV-ABI
glue — the complete `Com → .s` route for the θ block off the bespoke
`Avx512Model` machine.

```
Com jasminDialect  (θ vpackZMM kernels)  ──renderVpackZmmCom──▶  .s  (%zmm AT&T)
```

The θ column-parity fold (`parityCom`, four `vpackZMM .xor`) and the diffusion
mix (`dCom`, `.shl`/`.shr`/`.or`/`.xor` — the rotate-by-1 decomposition) are
exactly the carry-free `vpackZMM` fragment the printer covers, so both emit
directly to lowercase owned `%zmm` machine mnemonics:

* every `.xor` → `vpxorq`, the `.or` → `vporq`,
* the variable per-lane shifts `.shl` / `.shr` → `vpsllvq` / `vpsrlvq`
  (NOT the immediate `vpsllq`/`vpsrlq`), matching `zmmPackQ`'s
  `a.qword[k] <<< b.qword[k]` per-lane semantics.

The only imports are `VpackZmmAsmPrint` (renderer + framing) and
`KeccakThetaPiCom` (the `Com` kernels) — **no `Avx512Model` / `ZInstr`**
anywhere in this lowering/printing path.

## SSA naming (matches `lowerVpackZmmCom`'s `v{next}` counter)

`renderVpackZmmCom` runs `paramsAndMap Γ` to name the context head-first as
`p0, p1, …`, then walks the body allocating a fresh `v{next}` per `Com.var`:

* `parityCom` (`Γ = [c0,c1,c2,c3,c4]`): params `p0..p4`, four `.xor` bindings
  `v0..v3`, returns `v3` (= `C[x]`).
* `dCom` (`Γ = [cm,cp,one,c63]`): params `p0..p3`, four bindings `v0..v3`
  (`dsl = cp≪one`, `dsr = cp≫c63`, `drot = dsl|dsr`, `dout = cm⊕drot`),
  returns `v3` (= `D[x]`).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaComEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaComEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom renderVpackZmmInstr)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
  (parityCom dCom)

/-! ## 1. θ column parity → owned `.s`

The five column registers `c0..c4` (params `p0..p4`) pinned to `%zmm0..%zmm4`;
the three accumulator temps `v0/v1/v2` reuse `%zmm5` (single-use, dead after the
next xor) and the final result `v3` lands in `%zmm0`. -/

/-- A worked `%zmm` allocation for `parityCom`: the five column inputs `p0..p4`
    pinned to `%zmm0..%zmm4`, the three running-accumulator temps `v0/v1/v2`
    folded through `%zmm5`, and the `C[x]` result `v3` written to `%zmm0`. The
    caller may supply any other budget-respecting `XAlloc`. -/
def parityAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
   ("p4", "%zmm4"),
   ("v0", "%zmm5"), ("v1", "%zmm5"), ("v2", "%zmm5"), ("v3", "%zmm0")]

/-- The rendered body lines of `parityCom` (the four `vpxorq` of the θ column
    fold) under `parityAlloc`. -/
def parityBodyLines : List String := (renderVpackZmmCom parityAlloc parityCom).1

/-- `parityCom` renders to exactly the four owned AT&T `vpxorq` lines of the θ
    column-parity left fold (EVEX order `op src2, src1, dst`):
    `v0 = c0⊕c1`, `v1 = v0⊕c2`, `v2 = v1⊕c3`, `v3 = v2⊕c4`. -/
example :
    (renderVpackZmmCom parityAlloc parityCom).1
      = ["\tvpxorq %zmm1, %zmm0, %zmm5",
         "\tvpxorq %zmm2, %zmm5, %zmm5",
         "\tvpxorq %zmm3, %zmm5, %zmm5",
         "\tvpxorq %zmm4, %zmm5, %zmm0"] := by
  native_decide

/-- The full framed owned `.s` for the θ column-parity fold, with SysV-ABI
    `vmovdqu64` load/store glue (five column-pointer loads, one result store) —
    the owned, no-jasminc, no-`Avx512Model` rendering of the migrated Keccak θ
    column-parity leaf. -/
def parityExportAsm : String :=
  frameAsmFunction "keccak_theta_parity_vpackzmm"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqu64\t(%rsi), %zmm1"
    , "\tvmovdqu64\t(%rdx), %zmm2"
    , "\tvmovdqu64\t(%rcx), %zmm3"
    , "\tvmovdqu64\t(%r8), %zmm4" ]
    parityBodyLines
    [ "\tvmovdqu64\t%zmm0, (%r9)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println parityExportAsm

/-! ## 2. θ diffusion → owned `.s`

`cm/cp/one/c63` (params `p0..p3`) pinned to `%zmm0..%zmm3`; the three temps
`v0 = dsl (cp≪one)`, `v1 = dsr (cp≫c63)`, `v2 = drot (dsl|dsr)` go to
`%zmm4/%zmm5/%zmm4`, and the `D[x]` result `v3` to `%zmm0`. -/

/-- A worked `%zmm` allocation for `dCom`: inputs `p0..p3` (`cm/cp/one/c63`) to
    `%zmm0..%zmm3`, temps `v0/v1/v2` (`dsl/dsr/drot`) to `%zmm4/%zmm5/%zmm4`, and
    the `D[x]` result `v3` to `%zmm0`. -/
def dAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
   ("v0", "%zmm4"), ("v1", "%zmm5"), ("v2", "%zmm4"), ("v3", "%zmm0")]

/-- The rendered body lines of `dCom` (the `vpsllvq`/`vpsrlvq`/`vporq`/`vpxorq`
    rotate-by-1 decomposition) under `dAlloc`. -/
def dBodyLines : List String := (renderVpackZmmCom dAlloc dCom).1

/-- `dCom` renders to exactly the four owned AT&T θ-diffusion lines:
    `v0 = vpsllvq cp,one` (`cp≪1`), `v1 = vpsrlvq cp,c63` (`cp≫63`),
    `v2 = vporq v0,v1`, `v3 = vpxorq cm,v2` — the variable per-lane shifts
    `vpsllvq`/`vpsrlvq` (NOT immediate `vpsllq`/`vpsrlq`). -/
example :
    (renderVpackZmmCom dAlloc dCom).1
      = ["\tvpsllvq %zmm2, %zmm1, %zmm4",
         "\tvpsrlvq %zmm3, %zmm1, %zmm5",
         "\tvporq %zmm5, %zmm4, %zmm4",
         "\tvpxorq %zmm4, %zmm0, %zmm0"] := by
  native_decide

/-- The full framed owned `.s` for the θ diffusion mix, with SysV-ABI
    `vmovdqu64` glue (`cm/cp/one/c63` loads, one result store) — the owned,
    no-jasminc, no-`Avx512Model` rendering of the migrated Keccak θ diffusion
    leaf. -/
def dExportAsm : String :=
  frameAsmFunction "keccak_theta_diffusion_vpackzmm"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqu64\t(%rsi), %zmm1"
    , "\tvmovdqu64\t(%rdx), %zmm2"
    , "\tvmovdqu64\t(%rcx), %zmm3" ]
    dBodyLines
    [ "\tvmovdqu64\t%zmm0, (%r8)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println dExportAsm

/-! ## 3. Structural smoke pins on the rendered text -/

/- The θ parity kernel emits the packed XOR (lowercase owned `%zmm` mnemonic,
    not the UPPERCASE jasmin `#VPXOR` intrinsic). -/
#guard (strContains parityExportAsm "vpxorq")

/- The θ parity export symbol is present. -/
#guard (strContains parityExportAsm "keccak_theta_parity_vpackzmm:")

/- The θ diffusion kernel emits the VARIABLE per-lane left shift `vpsllvq`
    (matching `zmmPackQ .shl`, not the immediate `vpsllq`). -/
#guard (strContains dExportAsm "vpsllvq")

/- The θ diffusion kernel emits the VARIABLE per-lane right shift `vpsrlvq`
    (matching `zmmPackQ .shr`, not the immediate `vpsrlq`). -/
#guard (strContains dExportAsm "vpsrlvq")

/- The θ diffusion kernel emits the packed OR (the rotate recombination). -/
#guard (strContains dExportAsm "vporq")

/- The θ diffusion export symbol is present. -/
#guard (strContains dExportAsm "keccak_theta_diffusion_vpackzmm:")

/- Both kernels use 512-bit `%zmm` registers (not 128-bit `%xmm`). -/
#guard (strContains parityExportAsm "%zmm") && (strContains dExportAsm "%zmm")

/- No UPPERCASE jasmin intrinsic survives in either kernel — this is the owned
    (no-jasminc) lowercase-mnemonic path. -/
#guard !(strContains parityExportAsm "#VPXOR") && !(strContains dExportAsm "#VPSLL_8u64")

end CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaComEmit
