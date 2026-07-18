/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
import CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom

/-!
# Owned AT&T `.s` printer for the `vpackZMM` (512-bit ZMM) fragment of `Com jasminDialect`

This is the **512-bit analogue** of `VsimdAsmPrint.lean` (which only renders the
128-bit `JasminOp.vsimd` fragment over `%xmm` registers). The `Com jasminDialect`
ops that ride `JasminOp.vpackZMM (bop : JasminBinOp)` — the carry-free 8×u64
packed-lane op `zmmPackQ bop` over two `reg 512` (ZMM) registers, the
verified-dialect image of `#VPADD_8u64` / `#VPSUB_8u64` / `#VPMULL_8u64` /
`#VPAND` / `#VPOR` / `#VPXOR` / `#VPSLL_8u64` / `#VPSRL_8u64` — currently reach
assembly only through `JasminPrint.lowerExpr`'s jasmin `#VPADD_8u64`-intrinsic
`Ccall` (which only becomes machine code through the **jasminc** OCaml reader).

This module is the missing direct route: an **owned AT&T `.s` renderer**

```
Com jasminDialect  (vpackZMM fragment)  ──renderVpackZmmCom──▶  List String  (.s lines)
```

mapping each `JasminBinOp` to its real lowercase AT&T mnemonic + `%zmm` operands
(EVEX, 3-operand AT&T order `op src2, src1, dst`), with **zero** dependency on
the bespoke `Vec128.VCryptOp` / `Avx512Model` ZMM machine IR. The only imports
are `JasminPrint` (→ `JasminDialect`), `VsimdAsmPrint` (whose `XAlloc` /
`frameAsmFunction` framing we reuse verbatim), and the example's `Com` module
`ButterflyBlockCom`. The de-Bruijn→name walk (`VarMap` / `argName` /
`resultName` / `VarMap.extend` / `paramsAndMap`) is reused from `JasminPrint` —
so a `vpackZMM` kernel needs nothing from the bespoke crypto-SIMD/AVX-512 IR in
its lowering/printing path.

The migrated `ButterflyBlockCom` (NTT radix-2 butterfly), `ZmmArithBridgeCom`
(ZMM packed arithmetic core), and the Keccak `vpackZMM` kernels are exactly the
fragment this renderer covers, so they now have a complete owned `Com → .s` path.

## Scope

The renderer covers the **straight-line `vpackZMM`-only fragment**: a `Com`
whose every `Com.var` binding is a `JasminOp.vpackZMM bop` op over `reg 512`
registers. A non-`vpackZMM` op in the body is rendered as an explicit
`# <unsupported …>` comment line (so an out-of-fragment program is visibly
rejected by `gas`, never silently mis-emitted) — the scalar/word/128-bit ops
keep their existing jasmin / owned-x86 / `VsimdAsmPrint` routes.

## Mnemonic mapping (`JasminBinOp.zmmAttMnemonic`)

`JasminPrint`'s `mnemonic8u64` returns the UPPERCASE jasmin-intrinsic name
(`"#VPADD_8u64"`); the gas/AT&T owned printer needs the lowercase machine
mnemonic for the `%zmm` (EVEX) form:

| `JasminBinOp` | `zmmAttMnemonic` | AT&T line (D = bop-packed(A, B))           |
|---------------|------------------|--------------------------------------------|
| `.add`        | `vpaddq`         | `vpaddq %zmmB, %zmmA, %zmmD`                |
| `.sub`        | `vpsubq`         | `vpsubq %zmmB, %zmmA, %zmmD`                |
| `.mul`        | `vpmullq`        | `vpmullq %zmmB, %zmmA, %zmmD`               |
| `.and`        | `vpandq`         | `vpandq %zmmB, %zmmA, %zmmD`                |
| `.or`         | `vporq`          | `vporq %zmmB, %zmmA, %zmmD`                 |
| `.xor`        | `vpxorq`         | `vpxorq %zmmB, %zmmA, %zmmD`                |
| `.shl`        | `vpsllvq`        | `vpsllvq %zmmB, %zmmA, %zmmD`               |
| `.shr`        | `vpsrlvq`        | `vpsrlvq %zmmB, %zmmA, %zmmD`               |
| `.andn`       | `vpandnq`        | `vpandnq %zmmB, %zmmA, %zmmD`               |

(`.shl` / `.shr` are the per-lane VARIABLE shifts `vpsllvq` / `vpsrlvq` — the
`vpackZMM` shifts read the per-lane count from the second register, matching
`zmmPackQ .shl` / `.shr`'s `a.qword[k] <<< b.qword[k].toNat` semantics — not the
immediate-count `vpsllq` / `vpsrlq`.)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
  (VarMap argName resultName)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
  (XAlloc frameAsmFunction)

/-! ## 1. The lowercase AT&T mnemonic of a `vpackZMM` `JasminBinOp` -/

/-- The lowercase **AT&T/gas** mnemonic of the `JasminBinOp` carried by a
    `JasminOp.vpackZMM` op (for the owned `%zmm` printer). `JasminPrint`'s
    `mnemonic8u64` is the UPPERCASE jasmin-intrinsic name (`"#VPADD_8u64"`)
    routed through jasminc; this is the EVEX machine mnemonic gas assembles
    (the `q`-suffixed AVX-512 64-bit-lane form). -/
def JasminBinOp.zmmAttMnemonic : JasminBinOp → String
  | .add  => "vpaddq"
  | .sub  => "vpsubq"
  | .mul  => "vpmullq"
  | .and  => "vpandq"
  | .or   => "vporq"
  | .xor  => "vpxorq"
  | .shl  => "vpsllvq"
  | .shr  => "vpsrlvq"
  | .andn => "vpandnq"

/-! ## 2. AT&T `%zmm` register/operand formatting (self-contained, no `Avx512Model`)

`zmmReg` is the AT&T 512-bit register renderer: a name already denoting a
physical register (`%`-prefixed) renders as itself; otherwise it is an SSA name
looked up in the allocation `alloc` (a `VsimdAsmPrint.XAlloc`, i.e. an
association list name → `"%zmmN"`), with an unmapped name producing the explicit
`<UNALLOCATED:n>` sentinel so an over-budget block is rejected by gas rather than
silently aliasing. This is the `%zmm` twin of `VsimdAsmPrint.xmmReg`. -/

/-- The `%zmmN` register a name is assigned. A `%`-prefixed name is a pre-colored
    physical register and renders as itself; otherwise it is an SSA name looked
    up in `alloc`; an unmapped one yields the explicit `<UNALLOCATED:n>` sentinel.
    The 512-bit twin of `VsimdAsmPrint.xmmReg` (no `Avx512Model` dependency). -/
def zmmReg (alloc : XAlloc) (n : String) : String :=
  if n.startsWith "%" then n
  else (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-! ## 3. Per-instruction renderer: a `vpackZMM` op + dst/src names → one AT&T line

AT&T EVEX order is `op src2, src1, dst` for the three-operand form
(`vpaddq %zmmB, %zmmA, %zmmD` ≡ `D = add-packed(A, B)`). Identical syntax to
`VsimdAsmPrint.renderVsimdInstr`'s non-immediate arm, but over `%zmm` registers
and keyed by the `JasminBinOp` rather than the `SimdOp`. -/

/-- Render one `vpackZMM` binding `dst := bop-packed(a, b)` to its AT&T asm line
    (`%zmm` operands, AVX-512 EVEX 3-operand order `op src2, src1, dst`). -/
def renderVpackZmmInstr (alloc : XAlloc) (bop : JasminBinOp) (dst a b : String) :
    String :=
  let rd := zmmReg alloc dst
  let ra := zmmReg alloc a
  let rb := zmmReg alloc b
  "\t" ++ JasminBinOp.zmmAttMnemonic bop ++ " " ++ rb ++ ", " ++ ra ++ ", " ++ rd

/-! ## 4. The `Com jasminDialect → List String` walk (owned AT&T, vpackZMM fragment)

We mirror `JasminPrint.lowerCom`'s structure exactly: thread a `VarMap`
resolving each typed De Bruijn variable to its emitted name, allocate a fresh
SSA name `v{next}` per `Com.var`, and recurse. The difference is the per-binding
emission: each `JasminOp.vpackZMM bop` binding emits **one owned AT&T `%zmm`
line** via `renderVpackZmmInstr` (reading its two argument names off `e.args`
with the reused `argName`), instead of a jasmin `InstrR`. A non-`vpackZMM` op
emits a visible `# <unsupported …>` comment, documenting the fragment boundary. -/

/-- Lower one `Expr` of the vpackZMM fragment to its owned AT&T line. Only the
    `JasminOp.vpackZMM` arm produces a real instruction; every other op produces
    an explicit `# <unsupported owned-AT&T op …>` comment line (the fragment is
    `vpackZMM`-only). -/
def lowerVpackZmmExpr {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (alloc : XAlloc) (e : Expr jasminDialect Γ t) (dst : String) :
    String :=
  match e.op with
  | .vpackZMM bop =>
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      renderVpackZmmInstr alloc bop dst a b
  | _ => "\t# <unsupported owned-AT&T op; not in the vpackZMM fragment>"

/-- Walk a `Com jasminDialect Γ t` to its owned AT&T instruction lines plus the
    name of its return value. `next` is the fresh-SSA counter (`v{next}`).
    Structure-for-structure identical to `JasminPrint.lowerCom`, but emitting
    AT&T `.s` `%zmm` lines for the `vpackZMM` fragment. -/
def lowerVpackZmmCom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (alloc : XAlloc) (next : Nat) :
    Com jasminDialect Γ t → (List String × String)
  | .ret v => ([], vm t v)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let line := lowerVpackZmmExpr vm alloc e bound
      let (rest, res) := lowerVpackZmmCom (vm.extend (t := tEx) bound) alloc (next + 1) body
      (line :: rest, res)

/-- Render a closed `Com jasminDialect Γ t` to its owned AT&T `.s` body lines.
    `Γ` becomes named parameters `p0, p1, …` (via `JasminPrint.paramsAndMap`),
    each `vpackZMM` binding becomes one AT&T `%zmm` line. Returns the instruction
    lines and the return-value name (for the caller's ABI store). -/
def renderVpackZmmCom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (alloc : XAlloc) (com : Com jasminDialect Γ t) : (List String × String) :=
  let (_, vm) := JasminPrint.paramsAndMap Γ
  lowerVpackZmmCom vm alloc 0 com

/-! ### 4b. The render-side ZMM auto-allocator (retire the hand `%zmm` map)

`VsimdAsmPrint.vsimdAutoAllocZmm` computes the full `%zmm0..31` `XAlloc` for a
`vpackZMM` `Com` (params pinned to `%zmm0..`, temps linear-scanned over the rest
of `zmmPool` with last-use recycling — the §4b `allocXmmSeeded` engine).
`renderVpackZmmComAutoZmm` is the render-side wiring promised in
`VsimdAsmPrint.vsimdAutoAllocZmm`'s docstring: it feeds that computed map into
`lowerVpackZmmCom`, so a `vpackZMM` kernel lowers to fully physical-register
owned `%zmm` `.s` with **no hand-written `%zmm` map** (dropping the per-file
`bflyAlloc`-style hand allocation). The second component is the physical `%zmmN`
the ret value landed on (via `vsimdAutoRetRegZmm`) — what a store-bearing
AVX-512 leaf names for its `vmovdqu64 retReg, (%rdi)` ABI store. -/

/-- Render a `vpackZMM` `Com jasminDialect Γ t` to its owned AT&T `%zmm` `.s`
    body lines with the ZMM register allocation computed automatically by
    `VsimdAsmPrint.vsimdAutoAllocZmm` (params → `%zmm0..`, temps linear-scanned
    over `%zmm0..31` with last-use recycling). No hand-written `%zmm` map. The
    returned `String` is the physical `%zmmN` the ret value was allocated to
    (via `VsimdAsmPrint.vsimdAutoRetRegZmm`), for the caller's ABI store. -/
def renderVpackZmmComAutoZmm {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : List String × String :=
  let (_, vm) := JasminPrint.paramsAndMap Γ
  ((lowerVpackZmmCom vm (VsimdAsmPrint.vsimdAutoAllocZmm com) 0 com).1,
   VsimdAsmPrint.vsimdAutoRetRegZmm com)

/-! ## 5. Worked example: the NTT butterfly `hi` output rendered to owned `.s`

`ButterflyBlockCom.butterflyHiCom` is the migrated radix-2 butterfly `hi` slice,
two `vpackZMM` bindings over the input context `[w, a, b]` (each `reg 512`):

```
prod := vpackZMM mul w b      -- prod := w ⊙ b   (the twiddle multiply)
hi   := vpackZMM add a prod   -- hi   := a + prod
ret hi
```

We pin the input registers `p0/p1/p2` (`w`/`a`/`b`) to `%zmm0/1/2`, the temp
`v0` (`prod`) to `%zmm3`, and the result `v1` (`hi`) to `%zmm0`. The renderer
emits exactly the two owned AT&T `%zmm` lines `vpmullq %zmm2, %zmm0, %zmm3`
(prod = w ⊙ b) and `vpaddq %zmm3, %zmm1, %zmm0` (hi = a + prod) — the
`vpaddq`-to-`%zmm` `.s` the task asks for. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom (butterflyHiCom)

/-- The `%zmm` allocation for the worked butterfly example: the three params
    `p0/p1/p2` (`w`/`a`/`b`, head-first per `paramsAndMap`) pinned to
    `%zmm0/1/2`, the twiddle temp `v0` (`prod`) to `%zmm3`, and the `hi` result
    `v1` to `%zmm0`. -/
def bflyAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"),
   ("v0", "%zmm3"), ("v1", "%zmm0")]

/-- The rendered body lines of the butterfly `hi` slice (the two `vpackZMM`
    instructions). -/
def bflyBodyLines : List String := (renderVpackZmmCom bflyAlloc butterflyHiCom).1

/-- The butterfly `hi` body renders to exactly the two expected owned AT&T `%zmm`
    lines: `vpmullq %zmm2, %zmm0, %zmm3` (prod = w ⊙ b) and
    `vpaddq %zmm3, %zmm1, %zmm0` (hi = a + prod). AT&T EVEX order is
    `op src2, src1, dst`. -/
example :
    (renderVpackZmmCom bflyAlloc butterflyHiCom).1
      = ["\tvpmullq %zmm2, %zmm0, %zmm3", "\tvpaddq %zmm3, %zmm1, %zmm0"] := by
  native_decide

/-! ### Auto-allocated render of the same butterfly (no hand `bflyAlloc`)

`renderVpackZmmComAutoZmm` (§4b) renders `butterflyHiCom` with the ZMM register
allocation computed by `VsimdAsmPrint.vsimdAutoAllocZmm` instead of the hand
`bflyAlloc` map. The two `vpackZMM` mnemonics + their src/dst data flow are
identical; the only difference is the result register pick — the auto-allocator
draws the next free `%zmm4` for `hi`(`v1`) where the hand map aliased it back
onto `%zmm0`. Both are valid spill-free allocations with no `<UNALLOCATED>`. -/

/-- The auto-allocated butterfly `hi` body: same two mnemonics + same
    src/dst SSA flow as the hand-`bflyAlloc` render, only `hi`(`v1`) lands on
    the next free `%zmm4` rather than the hand map's `%zmm0` alias. -/
example :
    (renderVpackZmmComAutoZmm butterflyHiCom).1
      = ["\tvpmullq %zmm2, %zmm0, %zmm3", "\tvpaddq %zmm3, %zmm1, %zmm4"] := by
  native_decide

/-- The auto-allocator reports the ret value (`hi`) on `%zmm4` — the register a
    store-bearing butterfly leaf names for its `vmovdqu64 %zmm4, (%rdi)` store. -/
example : (renderVpackZmmComAutoZmm butterflyHiCom).2 = "%zmm4" := by native_decide

/-- The first binding (`prod = w ⊙ b`) is byte-identical to the hand-`bflyAlloc`
    render: the multiply and all three operands agree. -/
example :
    (renderVpackZmmComAutoZmm butterflyHiCom).1.head?
      = (renderVpackZmmCom bflyAlloc butterflyHiCom).1.head? := by native_decide

/-- The second binding (`hi = a + prod`) shares the `vpaddq %zmm3, %zmm1,`
    mnemonic + source-operand prefix with the hand render — the data flow is
    identical, only the destination register pick differs (auto `%zmm4` vs the
    hand map's `%zmm0` alias). -/
example :
    ((renderVpackZmmComAutoZmm butterflyHiCom).1.getLast? = some "\tvpaddq %zmm3, %zmm1, %zmm4")
      ∧ ((renderVpackZmmCom bflyAlloc butterflyHiCom).1.getLast?
          = some "\tvpaddq %zmm3, %zmm1, %zmm0") := by native_decide

/-- The full framed `.s` for the worked NTT butterfly `hi` step, with the SysV
    ABI load/store glue (`vmovdqu64 (%rdi), %zmm0` …) — the owned, no-jasminc,
    no-`Avx512Model` rendering of the migrated NTT radix-2 butterfly `hi` leaf.
    Reuses `VsimdAsmPrint.frameAsmFunction` (the `.text`/`.globl`/`ret` framing
    is register-width agnostic). -/
def bflyHiExportAsm : String :=
  let body := (renderVpackZmmCom bflyAlloc butterflyHiCom).1
  frameAsmFunction "ntt_butterfly_hi_vpackzmm"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqu64\t(%rsi), %zmm1"
    , "\tvmovdqu64\t(%rdx), %zmm2" ]
    body
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println bflyHiExportAsm

/-! ## 6. Structural smoke pins on the rendered text -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The butterfly kernel emits the packed multiply (lowercase owned `%zmm`
    mnemonic, not the UPPERCASE jasmin `#VPMULL_8u64` intrinsic). -/
theorem asm_has_vpmullq : strContains bflyHiExportAsm "vpmullq" = true := by
  native_decide

/-- The butterfly kernel emits the packed add (lowercase owned `%zmm` mnemonic). -/
theorem asm_has_vpaddq : strContains bflyHiExportAsm "vpaddq" = true := by
  native_decide

/-- The owned export symbol is present. -/
theorem asm_has_export :
    strContains bflyHiExportAsm "ntt_butterfly_hi_vpackzmm:" = true := by
  native_decide

/-- The body uses 512-bit `%zmm` registers (not the 128-bit `%xmm` of the
    `VsimdAsmPrint` fragment). -/
theorem asm_has_zmm : strContains bflyHiExportAsm "%zmm" = true := by native_decide

/-- No UPPERCASE jasmin intrinsic survives — this is the owned (no-jasminc)
    lowercase-mnemonic path. -/
theorem asm_no_jasmin_intrinsic :
    strContains bflyHiExportAsm "#VPADD_8u64" = false := by native_decide

/-- A `vpxorq` binding renders as the lowercase packed XOR over `%zmm`
    (EVEX order `src2, src1, dst`). -/
example :
    renderVpackZmmInstr [("d", "%zmm2"), ("a", "%zmm0"), ("b", "%zmm1")]
      .xor "d" "a" "b"
      = "\tvpxorq %zmm1, %zmm0, %zmm2" := by native_decide

/-- A `.shl` (variable left shift) binding renders as `vpsllvq` over `%zmm`. -/
example :
    renderVpackZmmInstr [("d", "%zmm2"), ("a", "%zmm0"), ("b", "%zmm1")]
      .shl "d" "a" "b"
      = "\tvpsllvq %zmm1, %zmm0, %zmm2" := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
