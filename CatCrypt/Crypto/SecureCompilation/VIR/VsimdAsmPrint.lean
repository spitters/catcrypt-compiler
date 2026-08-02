/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Owned AT&T `.s` printer for the `vsimd` fragment of `Com jasminDialect` (no jasminc, no `VCryptOp`)

A `Com jasminDialect` whose ops ride `JasminOp.vsimd (op : SimdOp)` currently
reaches assembly by one of two routes, **both** unsuitable for the owned
(no-jasminc) artifact:

* `JasminPrint.lowerExpr` / `JasminAbiEmit` lower the `vsimd` arm to a jasmin
  `Ccall` to the UPPERCASE intrinsic (`op.mnemonic = "VGF2P8MULB"`, …), which
  only becomes assembly through the **jasminc** OCaml reader; or
* `MatProdComEmitAsm` bridges each `vsimd` binding through `simdToVCryptOp` into
  the **bespoke** `Vec128.VCryptOp` machine IR, then prints with the owned
  `renderVCryptInst`. That keeps the dependency on the `Vec128*` IR we want to
  delete.

This module is the missing direct route: an **owned AT&T `.s` renderer**

```
Com jasminDialect  (vsimd fragment)  ──renderVsimdCom──▶  List String  (AT&T .s lines)
```

mapping each `SimdOp` to its real lowercase AT&T mnemonic + `%xmm` operands, with
**zero** dependency on `Vec128.VCryptOp` / `Vec128Lowering` / `Vec128AsmPrinter`.
The only import is `JasminPrint` (→ `JasminDialect`), whose de-Bruijn→name walk
(`VarMap` / `argName` / `VarMap.extend` / `paramsAndMap`) we reuse verbatim — so a
`vsimd` kernel needs nothing from the bespoke crypto-SIMD IR in its
lowering/printing path. The AT&T register/operand formatting (`%xmmN`,
three-operand VEX order `op src2, src1, dst`, leading `$imm` for
`clmul`/`affineqb`) is re-implemented as a few self-contained string helpers
(`xmmReg`, `renderVsimdInstr`) that mirror the *syntax* of
`Vec128AsmPrinter.renderVCryptInst` without importing it.

## Scope

The renderer covers the **straight-line `vsimd`-only fragment**: a `Com` whose
every `Com.var` binding is a `JasminOp.vsimd` op over `reg 128` registers (the
shape every migrated SIMD kernel — UOV GF(256) MAC, the AES/GHASH leaves — takes).
A non-`vsimd` op in the body is rendered as an explicit `# <unsupported …>` comment
line (so an out-of-fragment program is visibly rejected by `gas`, never silently
mis-emitted) — the scalar/word ops keep their existing jasmin/owned-x86 routes.
This is the deletion-enabler for the bespoke SIMD models: a `vsimd` kernel now has
a complete owned `Com → .s` path that does not touch `VCryptOp`.

## Mnemonic mapping (`SimdOp.attMnemonic`)

`SimdOp.mnemonic` (in `JasminDialect`) returns the UPPERCASE jasmin-intrinsic
name (`"VGF2P8MULB"`); the gas/AT&T owned printer needs the lowercase machine
mnemonic. `SimdOp.attMnemonic` is that lowercasing, matching the mnemonics the
proven `renderVCryptInst` emits byte-for-byte:

| `SimdOp`             | `attMnemonic`     | AT&T line (D = op(A,B))                       |
|----------------------|-------------------|----------------------------------------------|
| `.gf2p8mulb`         | `vgf2p8mulb`      | `vgf2p8mulb %xmmB, %xmmA, %xmmD`              |
| `.vpshufb`           | `vpshufb`         | `vpshufb %xmmB, %xmmA, %xmmD`                 |
| `.clmul imm`         | `vpclmulqdq`      | `vpclmulqdq $imm, %xmmB, %xmmA, %xmmD`        |
| `.affineqb imm`      | `vgf2p8affineqb`  | `vgf2p8affineqb $imm, %xmmB, %xmmA, %xmmD`    |
| `.bitwise .and`      | `vpand`           | `vpand %xmmB, %xmmA, %xmmD`                   |
| `.bitwise .or`       | `vpor`            | `vpor %xmmB, %xmmA, %xmmD`                    |
| `.bitwise .xor`      | `vpxor`           | `vpxor %xmmB, %xmmA, %xmmD`                   |
| `.packed .add 32`    | `vpaddd`          | `vpaddd %xmmB, %xmmA, %xmmD`                  |
| `.packed .add 64`    | `vpaddq`          | `vpaddq %xmmB, %xmmA, %xmmD`                  |
| `.packed .sub 32`    | `vpsubd`          | `vpsubd %xmmB, %xmmA, %xmmD`                  |
| `.packed .sub 64`    | `vpsubq`          | `vpsubq %xmmB, %xmmA, %xmmD`                  |
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
  (VarMap argName resultName)

/-! ## 1. The lowercase AT&T mnemonic of a `SimdOp` -/

/-- The lowercase **AT&T/gas** mnemonic of a `SimdOp` (for the owned printer).
    `SimdOp.mnemonic` is the UPPERCASE jasmin-intrinsic name routed through
    jasminc; this is the machine mnemonic gas assembles, matching the strings
    `Vec128AsmPrinter.renderVCryptInst` emits byte-for-byte. The `clmul`/`affineqb`
    immediates are NOT part of the mnemonic — they are rendered as a leading
    `$imm` operand by `renderVsimdInstr`. -/
def SimdOp.attMnemonic : SimdOp → String
  | .gf2p8mulb => "vgf2p8mulb"
  | .vpshufb => "vpshufb"
  | .clmul _ => "vpclmulqdq"
  | .affineqb _ => "vgf2p8affineqb"
  | .bitwise .and => "vpand"
  | .bitwise .or => "vpor"
  | .bitwise .xor => "vpxor"
  | .bitwise _ => "vpbitwise"
  | .packed .add 32 => "vpaddd"
  | .packed .add 64 => "vpaddq"
  | .packed .sub 32 => "vpsubd"
  | .packed .sub 64 => "vpsubq"
  | .packed .mul 16 => "vpmullw"
  | .packed .add 16 => "vpaddw"
  | .packed .sub 16 => "vpsubw"
  | .packed .shl 32 => "vpslld"
  | .packed .shr 32 => "vpsrld"
  | .packed _ _ => "vppacked"
  | .varShift .shl 32 => "vpsllvd"
  | .varShift .shl 64 => "vpsllvq"
  | .varShift .shr 32 => "vpsrlvd"
  | .varShift .shr 64 => "vpsrlvq"
  | .varShift _ _ => "vpvarshift"
  | .mulhi16 => "vpmulhw"
  | .vaesenc => "vaesenc"
  | .vaesenclast => "vaesenclast"
  | .vaeskeygen _ => "vaeskeygenassist"
  | .vpshufd _ => "vpshufd"

/-! ## 2. AT&T register/operand formatting (self-contained, no `Vec128*`)

`xmmReg` is the AT&T register renderer: a name already denoting a physical
register (`%`-prefixed) renders as itself; otherwise it is an SSA name looked up
in the allocation `alloc` (an association list name → `"%xmmN"`), with an
unmapped name producing the explicit `<UNALLOCATED:n>` sentinel so an
over-budget block is rejected by gas rather than silently aliasing. This mirrors
`Vec128AsmPrinter.xmmOf` exactly, but is re-implemented here so the module
imports nothing from the bespoke `Vec128*` IR. -/

/-- A register assignment: an association list name → `"%xmmN"`. -/
abbrev XAlloc := List (String × String)

/-- The `%xmmN` register a name is assigned. A `%`-prefixed name is a pre-colored
    physical register and renders as itself; otherwise it is an SSA name looked
    up in `alloc`; an unmapped one yields the explicit `<UNALLOCATED:n>` sentinel.
    Mirrors `Vec128AsmPrinter.xmmOf` (no `Vec128*` dependency). -/
def xmmReg (alloc : XAlloc) (n : String) : String :=
  if n.startsWith "%" then n
  else (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-! ## 3. Per-instruction renderer: a `vsimd` op + dst/src names → one AT&T line

AT&T VEX order is `op src2, src1, dst` for the three-operand form
(`vgf2p8mulb %xmmB, %xmmA, %xmmD` ≡ `D = gf2p8mulb(A, B)`); `clmul`/`affineqb`
take a leading `$imm`. Identical syntax to `renderVCryptInst`'s
`.vgf2p8mulb` / `.vpxor` / `.vpclmul` / `.vgf2p8affineqb` arms. -/

/-- Render one `vsimd` binding `dst := op(a, b)` to its AT&T asm line
    (`%xmm` operands, AVX VEX 3-operand order `op src2, src1, dst`). The
    `clmul`/`affineqb` arms emit a leading `$imm`. -/
def renderVsimdInstr (alloc : XAlloc) (op : SimdOp) (dst a b : String) : String :=
  let rd := xmmReg alloc dst
  let ra := xmmReg alloc a
  let rb := xmmReg alloc b
  match op with
  | .clmul imm =>
      "\tvpclmulqdq $" ++ toString imm ++ ", " ++ rb ++ ", " ++ ra ++ ", " ++ rd
  | .affineqb imm =>
      "\tvgf2p8affineqb $" ++ toString imm.toNat ++ ", " ++ rb ++ ", " ++ ra ++ ", " ++ rd
  | .vaeskeygen rcon =>
      -- unary + leading `$imm8` (the rcon byte), source = `a`. Byte-identical to
      -- `Vec128AsmPrinter.renderVCryptInst`'s `.vaeskeygen` arm
      -- (`vaeskeygenassist $rcon, %xmmsrc, %xmmdst`).
      "\tvaeskeygenassist $" ++ toString rcon.toNat ++ ", " ++ ra ++ ", " ++ rd
  | .vpshufd imm =>
      -- unary + leading `$imm8` control byte, source = `a`. Byte-identical to
      -- `Vec128AsmPrinter.renderVCryptInst`'s `.vpshufd` arm
      -- (`vpshufd $imm, %xmmsrc, %xmmdst`).
      "\tvpshufd $" ++ toString imm ++ ", " ++ ra ++ ", " ++ rd
  | other =>
      -- 3-operand VEX form (`vaesenc`/`vaesenclast` included): `op src2, src1, dst`.
      "\t" ++ SimdOp.attMnemonic other ++ " " ++ rb ++ ", " ++ ra ++ ", " ++ rd

/-! ### 3b. SHA-NI (Intel SHA extensions) AT&T renderers

`SHA256RNDS2`/`SHA256MSG1`/`SHA256MSG2` are legacy-SSE two-operand ops. In AT&T
they read `op src, dst`; `SHA256RNDS2` additionally takes its round-constant
operand implicitly in `%xmm0`, which `gas` accepts written explicitly as a
leading `%xmm0`. The renderers below produce the exact lines the byte encoder
`VsimdByteEncoder.encSha256*` assembles to (gas-pinned) and that the hand
schedule `Sha2ShaniEmit.renderQuartet` emits.

For `vsha256rnds2 abef cdgh mk` the dialect denote is `vsha256rnds2W abef cdgh mk`;
the machine mapping (validated by the byte KAT) is `src = abef`, `dst = cdgh`,
`%xmm0 = mk`, result (new ABEF) in `dst`. The round-const `mk` must be **staged
into `%xmm0`** before the instruction — the register-allocation constraint the
hand schedule handles by staging `W+K` directly into `%xmm0`. `stageShaRnds2Mk`
emits that move (`vmovdqa %xmmMk, %xmm0`); the caller elides it when `mk` already
lives in `%xmm0`. -/

/-- Stage the round-const (in `%xmmMk`) into `%xmm0`, the implicit `SHA256RNDS2`
    operand: `vmovdqa %xmmMk, %xmm0`. The %xmm0-staging is correctness-critical —
    a wrong stage yields a wrong hash (only the byte KAT catches it). -/
def stageShaRnds2Mk (mk : String) : String := "\tvmovdqa\t" ++ mk ++ ", %xmm0"

/-- `SHA256RNDS2 %xmm0, %src, %dst` — two SHA-256 rounds with the round-const
    implicit in `%xmm0`. `src` provides ABEF, `dst` provides CDGH and receives
    the updated ABEF. Emitted with `%xmm0` named explicitly (gas-accepted). -/
def renderSha256Rnds2 (src dst : String) : String :=
  "\tsha256rnds2\t%xmm0, " ++ src ++ ", " ++ dst

/-- `SHA256MSG1 %src, %dst` — σ0 partial message-schedule (AT&T `op src, dst`). -/
def renderSha256Msg1 (src dst : String) : String := "\tsha256msg1\t" ++ src ++ ", " ++ dst

/-- `SHA256MSG2 %src, %dst` — σ1 message-schedule completion (AT&T `op src, dst`). -/
def renderSha256Msg2 (src dst : String) : String := "\tsha256msg2\t" ++ src ++ ", " ++ dst

-- The renderers reproduce the exact SHA-NI lines of the hand schedule
-- `Sha2ShaniEmit.renderQuartet`/`renderMsg1`/`renderMsg2` (which the
-- whole-compression FIPS-180-4 KAT `bench/sha2_compare/sha2_shani_kat.c`
-- validates), and the byte encoder `VsimdByteEncoder.encSha256*` assembles them.
example : renderSha256Rnds2 "%xmm2" "%xmm1" = "\tsha256rnds2\t%xmm0, %xmm2, %xmm1" := by
  native_decide
example : renderSha256Rnds2 "%xmm1" "%xmm2" = "\tsha256rnds2\t%xmm0, %xmm1, %xmm2" := by
  native_decide
example : renderSha256Msg1 "%xmm4" "%xmm7" = "\tsha256msg1\t%xmm4, %xmm7" := by native_decide
example : renderSha256Msg2 "%xmm6" "%xmm7" = "\tsha256msg2\t%xmm6, %xmm7" := by native_decide
example : stageShaRnds2Mk "%xmm4" = "\tvmovdqa\t%xmm4, %xmm0" := by native_decide

/-! ## 4. The `Com jasminDialect → List String` walk (owned AT&T, vsimd fragment)

We mirror `JasminPrint.lowerCom`'s structure exactly: thread a `VarMap` resolving
each typed De Bruijn variable to its emitted name, allocate a fresh SSA name
`v{next}` per `Com.var`, and recurse. The difference is the per-binding emission:
each `JasminOp.vsimd op` binding emits **one owned AT&T line** via
`renderVsimdInstr` (reading its two argument names off `e.args` with the reused
`argName`), instead of a jasmin `InstrR`. A non-`vsimd` op emits a visible
`# <unsupported …>` comment, documenting the fragment boundary. -/

/-- Lower one `Expr` of the vsimd fragment to its owned AT&T line. Only the
    `JasminOp.vsimd` arm produces a real instruction; every other op produces an
    explicit `# <unsupported owned-AT&T op …>` comment line (the fragment is
    SIMD-only). -/
def lowerVsimdExpr {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (alloc : XAlloc) (e : Expr jasminDialect Γ t) (dst : String) :
    String :=
  match e.op with
  | .vsimd op =>
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      renderVsimdInstr alloc op dst a b
  | .vpslldq n =>
      -- 128-bit byte left-shift, single source (arg 0). Byte-identical to
      -- `X86Backend.Vec128AsmPrinter.renderVCryptInst`'s `.vpslldq` arm.
      "\tvpslldq $" ++ toString n ++ ", " ++ xmmReg alloc (argName vm e.args 0)
        ++ ", " ++ xmmReg alloc dst
  | .vpsrldq n =>
      -- 128-bit byte right-shift, single source (arg 0). Byte-identical to
      -- `X86Backend.Vec128AsmPrinter.renderVCryptInst`'s `.vpsrldq` arm.
      "\tvpsrldq $" ++ toString n ++ ", " ++ xmmReg alloc (argName vm e.args 0)
        ++ ", " ++ xmmReg alloc dst
  | .regConst 128 v =>
      -- **BAKED 128-bit XMM immediate** (the lowering image of the dialect
      -- `vconst128`). Materialized with a self-contained `movabsq`/`vmovq`/
      -- `vpinsrq` two-64-bit-half build (NO `.rodata` pool): the low 64 bits go
      -- into the low lane with `vmovq`, the high 64 bits are inserted into lane 1
      -- with `vpinsrq $1`, both routed through the caller-saved GP scratch `%r11`.
      -- One dialect binding renders as this 4-line block (embedded `\n`s), so the
      -- framing's line join emits real gas-assemblable const-load — no scalar-GP
      -- `UNHANDLED`. Only width 128 is a vector const; other `regConst` widths are
      -- scalar and fall through to the fragment-boundary comment below.
      let rd := xmmReg alloc dst
      let lo := v % (2 ^ 64)
      let hi := v / (2 ^ 64)
      "\tmovabsq $" ++ toString lo ++ ", %r11\n" ++
      "\tvmovq %r11, " ++ rd ++ "\n" ++
      "\tmovabsq $" ++ toString hi ++ ", %r11\n" ++
      "\tvpinsrq $1, %r11, " ++ rd ++ ", " ++ rd
  | _ => "\t# <unsupported owned-AT&T op; not in the vsimd fragment>"

/-- Walk a `Com jasminDialect Γ t` to its owned AT&T instruction lines plus the
    name of its return value. `next` is the fresh-SSA counter (`v{next}`).
    Structure-for-structure identical to `JasminPrint.lowerCom`, but emitting
    AT&T `.s` lines for the `vsimd` fragment. -/
def lowerVsimdCom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (alloc : XAlloc) (next : Nat) :
    Com jasminDialect Γ t → (List String × String)
  | .ret v => ([], vm t v)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let line := lowerVsimdExpr vm alloc e bound
      let (rest, res) := lowerVsimdCom (vm.extend (t := tEx) bound) alloc (next + 1) body
      (line :: rest, res)

/-- Render a closed `Com jasminDialect Γ t` to its owned AT&T `.s` body lines.
    `Γ` becomes named parameters `p0, p1, …` (via `JasminPrint.paramsAndMap`),
    each `vsimd` binding becomes one AT&T line. Returns the instruction lines and
    the return-value name (for the caller's ABI store). -/
def renderVsimdCom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (alloc : XAlloc) (com : Com jasminDialect Γ t) : (List String × String) :=
  let (_, vm) := JasminPrint.paramsAndMap Γ
  lowerVsimdCom vm alloc 0 com

/-! ## 4b. General XMM register allocation for the `vsimd` fragment

`renderVsimdCom` (and the per-kernel emit files) take a **hand-supplied**
`XAlloc` (name → `%xmmN`). That hand allocation is the one piece every migrated
SIMD kernel still writes by hand. This section is the missing **general
allocator**: a linear scan with last-use liveness over the 16 XMM registers,
the x86 analogue of `ARMBackend.Neon.allocV` (NEON's `vN` allocator) — built
directly off the dialect `Com`, with no `Vec128*` dependency.

The pipeline is then the exact NEON shape:

```
Com jasminDialect (vsimd fragment)  ──collectVsimdDefs──▶  block : List (dst, srcs)
                                    ──allocXmm reserved──▶  XAlloc
                                    ──renderVsimdCom──────▶  AT&T .s lines
```

so `renderVsimdComAuto` turns a `vsimd` `Com` into fully-register-allocated
owned `.s` with **no hand-written allocation map**. The walk reuses the same
SSA naming (`p{i}` params, `v{next}` temps) and the same per-op argument reads
as `lowerVsimdCom`/`lowerVsimdExpr`, so the produced `XAlloc` is exactly the
map those renderers consume. -/

/-- The (dst, srcs) read-set of one `vsimd`-fragment binding `dst := op(args)`.
    Reads exactly the argument names `lowerVsimdExpr` reads: the binary `vsimd`
    ops read args 0,1; the unary `vsimd` ops (`vaeskeygen`/`vpshufd`) and the
    `vpslldq`/`vpsrldq` byte-shifts read only arg 0. An out-of-fragment op has
    no sources (it renders as the `# <unsupported …>` comment). Mirror of
    `ARMBackend.Neon.ninstDstSrcs`. -/
def vsimdExprDstSrcs {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (e : Expr jasminDialect Γ t) (dst : String) :
    String × List String :=
  match e.op with
  | .vsimd op =>
      match op with
      | .vaeskeygen _ => (dst, [argName vm e.args 0])
      | .vpshufd _ => (dst, [argName vm e.args 0])
      | _ => (dst, [argName vm e.args 0, argName vm e.args 1])
  | .vpslldq _ => (dst, [argName vm e.args 0])
  | .vpsrldq _ => (dst, [argName vm e.args 0])
  | _ => (dst, [])

/-- Walk a `Com jasminDialect Γ t` to its straight-line `(dst, srcs)` block plus
    the return-value name, using the **same** fresh-SSA naming (`v{next}`) and
    `resultName` shaping as `lowerVsimdCom` — so the names here are exactly the
    names the renderer emits. -/
def collectVsimdDefs {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (next : Nat) :
    Com jasminDialect Γ t → (List (String × List String) × String)
  | .ret v => ([], vm t v)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let ds := vsimdExprDstSrcs vm e bound
      let (rest, res) := collectVsimdDefs (vm.extend (t := tEx) bound) (next + 1) body
      (ds :: rest, res)

/-- The XMM register pool we allocate from: `%xmm0 … %xmm15` (16 SSE/AVX
    vector registers). -/
def xmmPool : List String := (List.range 16).map (fun i => "%xmm" ++ toString i)

/-- The index of the last binding that *reads* `n` (its last use), or 0. The
    liveness signal that lets `allocXmm` recycle a register once its last
    consumer has executed. Analogue of `Neon.vLastUse`. -/
def xmmLastUse (block : List (String × List String)) (n : String) : Nat :=
  (block.zipIdx.foldl (fun acc (entry, idx) =>
    if entry.2.contains n then idx else acc) 0)

/-- Linear-scan XMM allocation over `xmmPool` with last-use liveness recycling.
    `reserved` names (the function's `Γ` parameters) are pinned to `%xmm0..` for
    the whole function and never freed; remaining temps draw from
    `%xmm{|reserved|}..%xmm15`, a register being returned to the free pool once
    its last reader has run. An over-budget block leaves later temps unmapped, so
    `xmmReg` emits the explicit `<UNALLOCATED:…>` sentinel (gas-rejected, never
    silently aliased) — the same discipline as `Neon.allocV`. -/
def allocXmm (reserved : List String) (block : List (String × List String)) :
    XAlloc :=
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%xmm" ++ toString i))
  let pool0 : List String := xmmPool.drop nres
  let step : (XAlloc × List String) → ((String × List String) × Nat) →
      (XAlloc × List String) :=
    fun (alloc, free) (entry, idx) =>
      let dst := entry.1
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := entry.2.filter (fun s =>
        ¬ reserved.contains s ∧ xmmLastUse block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (pinned, pool0)
  alloc

/-- Owned AT&T `.s` body lines for a `vsimd` `Com`, **register-allocated
    automatically**: the `Γ` parameters are pinned to `%xmm0..`, the temps are
    linear-scanned over the remaining XMM pool, and the resulting `XAlloc` feeds
    `renderVsimdCom`. This is the `vsimd` analogue of the scalar
    `Com.toLprogPhysAbi` GP allocator (and the x86 analogue of
    `Neon.renderLeafFn`'s `allocV` step): a `vsimd` kernel now lowers to fully
    physical-register owned `.s` with no hand-written allocation map. -/
def renderVsimdComAuto {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let alloc := allocXmm reserved block
  lowerVsimdCom vm alloc 0 com

/-! ## 4c. Allocator capability extensions: ret-register, reserved, pinned

`renderVsimdComAuto` returns only the rendered lines and the ret SSA *name*, and
always pins exactly the `Γ` parameters. Three gaps blocked migrating most vsimd
leaves off their hand-written register maps:

* **(C) ret register.** A store-bearing leaf needs the *physical* `%xmmN` its
  result landed on to name its ABI store; `renderVsimdComAuto` gives only the SSA
  name, forcing the leaf to reconstruct the register with a boilerplate
  `autoXAlloc` helper. `renderVsimdComAutoWithReg` returns `(lines, retReg)`
  directly, and `vsimdAutoAlloc` exposes the full computed `XAlloc`.
* **(B) reserved registers.** A surrounding driver may hold live values across
  repeated renderings (e.g. an accumulator in `%xmm3`, temps starting at
  `%xmm4`). `renderVsimdComAutoReserved` removes those driver-held registers from
  the temp free pool so the linear scan never clobbers them.
* **(A) fixed output pin.** An in-place ABI (AEGIS `vaesenc …,%xmm0,%xmm0`)
  needs the result back on a fixed input register. `renderVsimdComAutoPinned`
  forces the ret SSA value onto a requested `%xmmN` (seeding the alloc map and
  holding that register out of the temp pool), so the in-place register survives
  the linear scan.

Gaps A and B share a single generalized allocator, `allocXmmSeeded`, of which
the original `allocXmm` is the no-seed / full-pool special case. All three are
additive — `renderVsimdComAuto` is unchanged and byte-identical. -/

/-- Linear-scan XMM allocation generalized over a **pre-seeded** alloc map
    `seed` (names already pinned to a chosen `%xmmN`) and an explicit `pool` of
    free registers. The body is identical to `allocXmm`'s fold — a binding whose
    `dst` is already in `seed` keeps its seeded register (`(alloc.lookup dst).isSome`),
    others draw from `pool` with last-use recycling. `allocXmm reserved block` is
    the special case `seed = (reserved pinned to %xmm0..)`, `pool = xmmPool.drop
    |reserved|`; this version additionally lets a caller force a specific binding
    onto a specific register and hold that register out of the temp pool (the
    in-place / fixed-output pin), or hold driver-live registers out of the pool
    (the reserved case). -/
def allocXmmSeeded (reserved : List String) (seed : XAlloc) (pool : List String)
    (block : List (String × List String)) : XAlloc :=
  let step : (XAlloc × List String) → ((String × List String) × Nat) →
      (XAlloc × List String) :=
    fun (alloc, free) (entry, idx) =>
      let dst := entry.1
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := entry.2.filter (fun s =>
        ¬ reserved.contains s ∧ xmmLastUse block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (seed, pool)
  alloc

/-- The full computed `XAlloc` `renderVsimdComAuto` feeds to `renderVsimdCom`:
    the `Γ` parameters pinned to `%xmm0..`, the temps linear-scanned over the
    rest of `xmmPool`. Exposed so a store-bearing leaf can read the ret value's
    physical register off the map directly (gap C) — e.g.
    `xmmReg (vsimdAutoAlloc com) retName` — instead of reconstructing it with a
    hand-written `autoXAlloc` helper. Identical to the alloc `renderVsimdComAuto`
    builds internally. -/
def vsimdAutoAlloc {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : XAlloc :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  allocXmm reserved block

/-- Like `renderVsimdComAuto`, but additionally returns the **physical
    `%xmmN` register** the ret SSA value was allocated to (gap C). A
    store-bearing leaf uses `retReg` to name its ABI store
    (`vmovdqu retReg, (%rdi)`) without the `autoXAlloc` boilerplate. The
    `lines` are byte-identical to `renderVsimdComAuto`'s. -/
def renderVsimdComAutoWithReg {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let alloc := allocXmm reserved block
  let (lines, retName) := lowerVsimdCom vm alloc 0 com
  (lines, xmmReg alloc retName)

/-- Auto-allocate a `vsimd` `Com` while **reserving** physical registers a
    surrounding driver holds live across this rendering (gap B): `heldRegs` (e.g.
    `["%xmm3"]` for a driver-held accumulator) are removed from the temp free
    pool, so the temps start at the next free register (`%xmm4`) and never clobber
    the driver's live values. The `Γ` parameters are still pinned to `%xmm0..`.
    Returns `(lines, retReg)` like `renderVsimdComAutoWithReg`. -/
def renderVsimdComAutoReserved {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (heldRegs : List String) (com : Com jasminDialect Γ t) :
    (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%xmm" ++ toString i))
  let pool : List String := (xmmPool.drop nres).filter (fun r => ¬ heldRegs.contains r)
  let alloc := allocXmmSeeded reserved pinned pool block
  let (lines, retName) := lowerVsimdCom vm alloc 0 com
  (lines, xmmReg alloc retName)

/-- Auto-allocate a `vsimd` `Com` with the ret SSA value **pinned** to a fixed
    output register `retReg` (gap A): the in-place ABI (AEGIS
    `vaesenc …,%xmm0,%xmm0`) needs the result back on a specific input register.
    We seed the allocation map with `(retName ↦ retReg)` and **remove `retReg`
    from the temp free pool**, so no other temp aliases it and `allocXmmSeeded`
    renders the ret binding onto `retReg`. The `Γ` parameters are still pinned to
    `%xmm0..`; remaining temps draw from the rest of the pool minus `retReg`.
    Returns `(lines, retReg)`. -/
def renderVsimdComAutoPinned {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (retReg : String) (com : Com jasminDialect Γ t) : (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, retName) := collectVsimdDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%xmm" ++ toString i))
  -- seed the ret name onto `retReg`; hold `retReg` out of the temp pool
  let seed : XAlloc := (retName, retReg) :: pinned
  let pool : List String := (xmmPool.drop nres).filter (fun r => r ≠ retReg)
  let alloc := allocXmmSeeded reserved seed pool block
  let (lines, _) := lowerVsimdCom vm alloc 0 com
  (lines, retReg)

/-! ### 4d. Custom parameter placement: `renderVsimdComAutoParamPinned`

`renderVsimdComAuto` / `…Reserved` / `…Pinned` all pin the `Γ` parameters
**head-first to `%xmm0..`** in declaration order, and only ever reserve registers
out of the *temp* free pool. Several vsimd leaves need a **custom parameter
layout** the existing entries can't express:

* **ZkHash1283** pins params `p0→%xmm2, p1→%xmm1, p2→%xmm0` (custom order, not
  `%xmm0..`) and reserves `%xmm3/4/5`.
* **QsBatchDot** pins params to `%xmm13/14/15` (high) with a GF accumulator
  reserved at `%xmm0` (low) — params high, a held register low.
* **AEGIS keystream** must read live state registers `%xmm2/%xmm3` as its
  operands (not `%xmm0/1`).
* **AESCCM/AESSIV** hold 11 round keys live in `%xmm0..%xmm10` plus an in-place
  state at `%xmm11`, so `ecbCom`'s `inp` param lands on `%xmm11` and each `rk_i`
  on `%xmm_i` — a fully custom param→register map.

`renderVsimdComAutoParamPinned paramRegs heldRegs com` seeds the i-th parameter
onto `paramRegs[i]` (an explicit `%xmmN`, **not** `%xmm{i}`), holds **both**
`paramRegs` AND `heldRegs` out of the temp free pool (so temps fill only the
remaining registers, never clobbering a custom-placed param or a driver-held
register), runs `allocXmmSeeded`, and returns `(lines, retReg)`. This one entry
covers custom param order, high-pinned params, AND a low reserved accumulator.
A parameter index `i` with no `paramRegs[i]` (more params than `paramRegs`)
falls back to the head-first `%xmm{i}` default, so passing `paramRegs = []`
degenerates to `renderVsimdComAutoReserved heldRegs`. The §1–§4c entries are
untouched and byte-identical. -/

/-- The seeded param→register `XAlloc` of `renderVsimdComAutoParamPinned`: the
    i-th `Γ` parameter pinned to `paramRegs[i]` (custom register, not `%xmm{i}`),
    falling back to the head-first `%xmm{i}` default when `paramRegs` runs out.
    Exposed as the map variant (gap C, custom-param tier) so a store-bearing leaf
    reads a value's physical register off the full computed map directly —
    `xmmReg (vsimdAutoAllocParamPinned paramRegs heldRegs com) name`. -/
def vsimdAutoAllocParamPinned {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (paramRegs : List String) (heldRegs : List String)
    (com : Com jasminDialect Γ t) : XAlloc :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  -- seed each param onto its requested register, defaulting to `%xmm{i}`
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) =>
      (n, (paramRegs[i]?).getD ("%xmm" ++ toString i)))
  -- hold both the custom param registers AND the driver-held registers out of
  -- the temp free pool, so temps never alias a placed param or a held register
  let heldAll : List String := pinned.map (fun pr => pr.2) ++ heldRegs
  let pool : List String := xmmPool.filter (fun r => ¬ heldAll.contains r)
  allocXmmSeeded reserved pinned pool block

/-- Auto-allocate a `vsimd` `Com` with a **custom parameter layout**: the i-th
    `Γ` parameter is pinned to `paramRegs[i]` (an explicit `%xmmN`, not the
    head-first `%xmm{i}`), and **both** `paramRegs` AND `heldRegs` are held out of
    the temp free pool so the linear scan fills only the remaining registers. This
    single entry expresses custom param order (ZkHash1283 `p0→%xmm2,p1→%xmm1,
    p2→%xmm0`), high-pinned params (QsBatchDot `%xmm13/14/15`) with a low reserved
    accumulator (`%xmm0`), live-state operand registers (AEGIS `%xmm2/%xmm3`), and
    the 11-round-key + in-place-state map (AESCCM/AESSIV). Returns `(lines,
    retReg)` like the other §4c entries. With `paramRegs = []` it degenerates to
    `renderVsimdComAutoReserved heldRegs` (head-first params, held temps). -/
def renderVsimdComAutoParamPinned {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (paramRegs : List String) (heldRegs : List String)
    (com : Com jasminDialect Γ t) : (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) =>
      (n, (paramRegs[i]?).getD ("%xmm" ++ toString i)))
  let heldAll : List String := pinned.map (fun pr => pr.2) ++ heldRegs
  let pool : List String := xmmPool.filter (fun r => ¬ heldAll.contains r)
  let alloc := allocXmmSeeded reserved pinned pool block
  let (lines, retName) := lowerVsimdCom vm alloc 0 com
  (lines, xmmReg alloc retName)

/-! ### 4e. In-place register-recycling chains: `renderVsimdComAutoInPlaceChain`

The §4b–§4d auto-allocators all give each SSA temp a *fresh* register (last-use
recycling reclaims a register only after its consumer runs), and `…Pinned` /
`…ParamPinned` only force the **ret** value (or the **params**) onto fixed
registers. The AES-round-chain leaves (AESCCM/AESSIV/GgmExpand) need the
**opposite** discipline: a long sequential dependency chain
`s := aesenc(s, rk_0); s := aesenc(s, rk_1); …` keeps the rolling state in **one
fixed register** across every round (each op's result aliases the previous op's
register, so the chain occupies a single XMM the whole time), while the 11 round
keys stay **live** in a fixed block of registers (`%xmm0..%xmm10`) that the
chain temps must never touch.

`renderVsimdComAutoInPlaceChain stateReg heldRegs com` expresses exactly that:

* the first `Γ` parameter (the input state `s`) is pinned to `stateReg`;
* the remaining `Γ` parameters (the round keys `rk_i`) are pinned to `heldRegs`
  in declaration order (so `rk_i ↦ heldRegs[i]`);
* **every** chain temp `v{k}` is seeded onto `stateReg` too — so the rolling
  result of op `k` lands on `stateReg` and is reused as op `k+1`'s state input,
  the in-place recycle;
* `stateReg` AND `heldRegs` are held out of the temp free pool, so nothing else
  can alias the state register or clobber a live round key.

Because each chain node's `dst` is pre-seeded, `allocXmmSeeded`'s
`(alloc.lookup dst).isSome` branch keeps every node on `stateReg` — the whole
linear-SSA chain collapses onto the one register, exactly the hand-written
`ecbCom`/`keyRoundAlloc`/`ecbAlloc` layout (`inp`/state on `%xmm11`, all temps
`v0..v10 ↦ %xmm11`, keys `rk_i ↦ %xmm_i`). With `heldRegs = []` it degenerates
to a pure in-place chain on `stateReg` with no held keys. Returns
`(lines, stateReg)`. The §1–§4d entries are untouched and byte-identical. -/

/-- The seeded `XAlloc` of `renderVsimdComAutoInPlaceChain`: the first `Γ`
    parameter (input state) and every chain temp pinned to `stateReg`, the
    remaining parameters (round keys) pinned to `heldRegs` in order. Exposed as
    the map variant so a store-bearing chain leaf reads a value's physical
    register off the full computed map directly. -/
def vsimdAutoAllocInPlaceChain {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (stateReg : String) (heldRegs : List String)
    (com : Com jasminDialect Γ t) : XAlloc :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  -- first param = input state → `stateReg`; remaining params = round keys → `heldRegs`
  let stateParamSeed : XAlloc :=
    match reserved with
    | [] => []
    | s :: _ => [(s, stateReg)]
  let keyParamSeed : XAlloc := (reserved.drop 1).zip heldRegs
  -- every chain temp def aliases `stateReg` (the in-place rolling result)
  let chainSeed : XAlloc := block.map (fun entry => (entry.1, stateReg))
  let seed : XAlloc := stateParamSeed ++ keyParamSeed ++ chainSeed
  let heldAll : List String := stateReg :: heldRegs
  let pool : List String := xmmPool.filter (fun r => ¬ heldAll.contains r)
  allocXmmSeeded reserved seed pool block

/-- Auto-allocate a `vsimd` `Com` whose body is an **in-place dependency chain**
    `s := f(s, rk_0); s := f(s, rk_1); …` (the AESCCM/AESSIV/GgmExpand AES round
    chain): the rolling state stays on the single register `stateReg` across every
    op (each result aliases `stateReg`, reused by the next op), while the round
    keys are held live in `heldRegs` (`rk_i ↦ heldRegs[i]`) and never used as a
    temp. The first `Γ` parameter (input state) is pinned to `stateReg`, the rest
    (the keys) to `heldRegs`; both `stateReg` and `heldRegs` are held out of the
    temp free pool. Returns `(lines, stateReg)`. With `heldRegs = []` it is a pure
    in-place chain on `stateReg`. This is the allocator the AES-chain leaves use to
    drop their hand-written `ecbAlloc`/`keyRoundAlloc` maps (state `%xmm11`, keys
    `%xmm0..%xmm10`). -/
def renderVsimdComAutoInPlaceChain {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (stateReg : String) (heldRegs : List String)
    (com : Com jasminDialect Γ t) : (List String × String) :=
  let (_, vm) := JasminPrint.paramsAndMap Γ
  let alloc := vsimdAutoAllocInPlaceChain stateReg heldRegs com
  let (lines, _) := lowerVsimdCom vm alloc 0 com
  (lines, stateReg)

/-! ### 4e pins: the AES round chain stays on one register

Exercised on a small AES round chain over `[state, rk0, rk1]`
(`s1 := aesenc(state, rk0); s2 := aesenc(s1, rk1)`), the shape every
AESCCM/AESSIV/GgmExpand round takes. The state stays on `%xmm11`; the two keys
are read from `%xmm0`/`%xmm1`; the result is back on `%xmm11`. -/

/-- The input context of the worked AES round chain: `[state, rk0, rk1]`, each
    `reg 128`. -/
abbrev aesChainCtx : Ctxt jasminDialect := [.reg 128, .reg 128, .reg 128]

/-- A two-round AES chain `s1 := aesenc(state, rk0); s2 := aesenc(s1, rk1)` —
    the in-place chain shape of the AESCCM/AESSIV/GgmExpand round bodies. `state`
    is `p0`, `rk0` is `p1`, `rk1` is `p2`; `s1` (`v0`) reads `state`,`rk0`; `s2`
    (`v1`) reads the previous result `s1` and `rk1`. -/
def aesChainExample : Com jasminDialect aesChainCtx (.reg 128) :=
  -- s1 := aesenc(state, rk0)
  .var (.mk (.vsimd .vaesenc) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- s2 := aesenc(s1, rk1)   (s1 = .here, rk1 = .there.there.there.here)
    (.var (.mk (.vsimd .vaesenc) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      (.ret .here))

/-- The in-place chain allocator keeps the rolling state on `stateReg = %xmm11`
    across both rounds: each `vaesenc` writes its result back to `%xmm11` (the
    in-place recycle), the round keys are read from the held `%xmm0`/`%xmm1`, and
    the returned register is `%xmm11`. This is the AESCCM/AESSIV/GgmExpand
    in-place layout, produced with no hand-written `ecbAlloc`/`keyRoundAlloc`. -/
example :
    renderVsimdComAutoInPlaceChain "%xmm11" ["%xmm0", "%xmm1"] aesChainExample
      = (["\tvaesenc %xmm0, %xmm11, %xmm11", "\tvaesenc %xmm1, %xmm11, %xmm11"],
         "%xmm11") := by native_decide

/-- Every chain node — input state `p0`, both temps `v0`/`v1` — maps to the single
    `stateReg = %xmm11` (the in-place recycle: the rolling result never moves). -/
example :
    ((vsimdAutoAllocInPlaceChain "%xmm11" ["%xmm0", "%xmm1"] aesChainExample).lookup "p0"
        = some "%xmm11")
    ∧ ((vsimdAutoAllocInPlaceChain "%xmm11" ["%xmm0", "%xmm1"] aesChainExample).lookup "v0"
        = some "%xmm11")
    ∧ ((vsimdAutoAllocInPlaceChain "%xmm11" ["%xmm0", "%xmm1"] aesChainExample).lookup "v1"
        = some "%xmm11") := by native_decide

/-- The round keys land on their held registers in declaration order
    (`rk0 = p1 ↦ %xmm0`, `rk1 = p2 ↦ %xmm1`) and are never reused as the rolling
    temp. -/
example :
    ((vsimdAutoAllocInPlaceChain "%xmm11" ["%xmm0", "%xmm1"] aesChainExample).lookup "p1"
        = some "%xmm0")
    ∧ ((vsimdAutoAllocInPlaceChain "%xmm11" ["%xmm0", "%xmm1"] aesChainExample).lookup "p2"
        = some "%xmm1") := by native_decide

/-- With `heldRegs = []` the entry is a pure in-place chain on `stateReg`: the
    state stays on `%xmm11`, but the (unheld) keys draw fresh pool registers — the
    chain-recycle on `stateReg` is independent of how the keys are placed. The two
    `vaesenc` results still both land on `%xmm11`. -/
example :
    (renderVsimdComAutoInPlaceChain "%xmm11" [] aesChainExample).2 = "%xmm11"
    ∧ ((renderVsimdComAutoInPlaceChain "%xmm11" [] aesChainExample).1.all
        (fun l => CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint.strContains l "%xmm11")) := by
  native_decide

/-! ## 5. A `.text`/`.globl`/`ret` `.s` framing helper

A self-contained SysV-ABI wrapper that loads the `Γ` parameters from XMM
registers (pinned by `alloc`), runs the rendered `vsimd` body, and returns. This
mirrors `MatProdComEmitAsm.macExportAsmCom`'s framing but produced directly from
the dialect (no `VCryptOp`). The load/store ABI lines are left to the caller via
`pre`/`post` so the framing stays kernel-agnostic; the function name is the
export symbol. -/

/-- Frame rendered body `lines` as an AT&T `.s` function `name` with `.text` /
    `.globl` / `ret`. `pre` (e.g. `vmovdqu`-loads from arg pointers into the
    pinned input registers) and `post` (e.g. a `vmovdqu`-store of the result)
    are caller-supplied ABI lines. -/
def frameAsmFunction (name : String) (pre : List String) (lines : List String)
    (post : List String) : String :=
  let allLines := pre ++ lines ++ post ++ ["\tret"]
  "\t.att_syntax\n" ++
  "\t.text\n" ++
  "\t.p2align\t5\n" ++
  "\t.globl\t" ++ name ++ "\n" ++
  "\t.type\t" ++ name ++ ", %function\n" ++
  name ++ ":\n" ++
  String.intercalate "\n" allLines ++ "\n"

/-! ## 6. Worked example: the UOV GF(256) MAC step rendered to owned `.s`

The two-binding `vsimd` MAC step
`prod := gf2p8mulb(achunk, bbcast); res := acc ^ prod` rendered with the input
registers pinned to `%xmm0/%xmm1/%xmm2` (acc/achunk/bbcast) and the temp `prod`
to `%xmm3`. The `Com` is built inline (so the example needs no import beyond
`JasminPrint`); its shape is identical to `MatProdComEmit.matProdCom`. -/

/-- The input context of the worked MAC step: `[acc, achunk, bbcast]`, each
    `reg 128`. -/
abbrev macCtx : Ctxt jasminDialect := [.reg 128, .reg 128, .reg 128]

/-- The two-binding `vsimd` GF(256) MAC step
    `prod := gf2p8mulb(achunk, bbcast); res := acc ^ prod`, identical in shape to
    `MatProdComEmit.matProdCom`. Built inline here to keep the example's only
    import `JasminPrint`. -/
def macExample : Com jasminDialect macCtx (.reg 128) :=
  -- prod := gf2p8mulb(achunk, bbcast)
  .var (.mk (.vsimd .gf2p8mulb) rfl
          (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    -- res := acc ^ prod   (acc is now `.there .here`, prod is `.here`)
    (.var (.mk (.vsimd (.bitwise .xor)) rfl
            (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- The XMM allocation for the worked example: the three params `p0/p1/p2`
    (acc/achunk/bbcast, head-first per `paramsAndMap`) pinned to `%xmm0/1/2`, the
    temp `v0` (`prod`) to `%xmm3`. -/
def macAlloc : XAlloc :=
  [("p0", "%xmm0"), ("p1", "%xmm1"), ("p2", "%xmm2"), ("v0", "%xmm3")]

/-- The rendered body lines (just the two SIMD instructions). -/
def macBodyLines : List String := (renderVsimdCom macAlloc macExample).1

/-- The body renders to exactly the two expected owned AT&T lines:
    `vgf2p8mulb %xmm2, %xmm1, %xmm3` (prod = gf2p8mulb(achunk, bbcast)) and
    `vpxor %xmm3, %xmm0, %xmm0` (res = acc ^ prod). The XOR's result reuses
    `%xmm0` because the example's allocation maps the result name to the acc
    register — here the return name `v1` is unmapped, so this pins the renderer
    against an explicit allocation instead. -/
example :
    (renderVsimdCom
      [("p0", "%xmm0"), ("p1", "%xmm1"), ("p2", "%xmm2"),
       ("v0", "%xmm3"), ("v1", "%xmm0")] macExample).1
      = ["\tvgf2p8mulb %xmm2, %xmm1, %xmm3", "\tvpxor %xmm3, %xmm0, %xmm0"] := by
  native_decide

/-- `renderVsimdComAuto` (the general allocator, §4b) reproduces the worked MAC
    step with a valid spill-free XMM assignment **without** the hand-written
    `macAlloc`: the three params pinned to `%xmm0/1/2`, the temp `prod` (`v0`)
    to `%xmm3`, the XOR result (`v1`) to the next free `%xmm4`. -/
example :
    (renderVsimdComAuto macExample).1
      = ["\tvgf2p8mulb %xmm2, %xmm1, %xmm3", "\tvpxor %xmm3, %xmm0, %xmm4"] := by
  native_decide

/-- The general allocator pins the parameters to the low XMM registers exactly
    as a hand-written param map would: `p0 ↦ %xmm0`. -/
example :
    (allocXmm ["p0", "p1", "p2"]
      (collectVsimdDefs (JasminPrint.paramsAndMap macCtx).2 0 macExample).1).lookup "p0"
      = some "%xmm0" := by native_decide

/-! ### §4c capability pins: ret-register (C), reserved (B), pinned (A)

The three allocator extensions, exercised on `macExample` (params
`acc/achunk/bbcast` → `%xmm0/1/2`, temp `prod`(`v0`) → `%xmm3`, ret `res`(`v1`)).
Pins are on short register strings / two-line bodies, so `native_decide`
stays cheap. -/

/-- (C) `renderVsimdComAutoWithReg` returns `(lines, retReg)`; `retReg` matches
    the line that defines the ret — the allocator puts the XOR result (`v1`) on
    the next free `%xmm4`, and that is exactly the register named back. A
    store-bearing leaf reads `%xmm4` here for its ABI store instead of
    reconstructing it with an `autoXAlloc` helper. -/
example :
    renderVsimdComAutoWithReg macExample
      = (["\tvgf2p8mulb %xmm2, %xmm1, %xmm3", "\tvpxor %xmm3, %xmm0, %xmm4"],
         "%xmm4") := by native_decide

/-- (C) `vsimdAutoAlloc` exposes the full map; the ret name `v1`'s physical
    register read off it agrees with `renderVsimdComAutoWithReg`'s `retReg`. -/
example : xmmReg (vsimdAutoAlloc macExample) "v1" = "%xmm4" := by native_decide

/-- (B) `renderVsimdComAutoReserved ["%xmm3"]` holds the driver-live `%xmm3` out
    of the temp pool, so the temps start at `%xmm4` (`prod`) / `%xmm5` (`res`) —
    the reserved register never appears as a temp assignment. -/
example :
    renderVsimdComAutoReserved ["%xmm3"] macExample
      = (["\tvgf2p8mulb %xmm2, %xmm1, %xmm4", "\tvpxor %xmm4, %xmm0, %xmm5"],
         "%xmm5") := by native_decide

/-- (A) `renderVsimdComAutoPinned "%xmm0"` forces the ret (`res`/`v1`) onto
    `%xmm0`, the in-place ABI register (AEGIS `…,%xmm0,%xmm0`): the XOR writes
    back to `%xmm0` and the returned `retReg` is `%xmm0`. -/
example :
    renderVsimdComAutoPinned "%xmm0" macExample
      = (["\tvgf2p8mulb %xmm2, %xmm1, %xmm3", "\tvpxor %xmm3, %xmm0, %xmm0"],
         "%xmm0") := by native_decide

/-! ### §4d pins: custom param order, high-pinned params + low accumulator

Exercised on `macExample` (params `acc/achunk/bbcast` = `p0/p1/p2`, temp
`prod`(`v0`), ret `res`(`v1`)). Pins are on two-line bodies, so `native_decide`
stays cheap. -/

/-- (custom order) `renderVsimdComAutoParamPinned ["%xmm2","%xmm1","%xmm0"] []`
    places `p0→%xmm2`, `p1→%xmm1`, `p2→%xmm0` (the ZkHash1283 reversed param
    order). The `gf2p8mulb(p1=achunk, p2=bbcast)` reads `%xmm0,%xmm1`; the temp
    `prod`(`v0`) lands on the first free register `%xmm3` (params hold `%xmm0/1/2`
    out of the pool); the XOR `res = acc(p0=%xmm2) ^ prod(%xmm3)` writes the next
    free `%xmm4`. -/
example :
    renderVsimdComAutoParamPinned ["%xmm2", "%xmm1", "%xmm0"] [] macExample
      = (["\tvgf2p8mulb %xmm0, %xmm1, %xmm3", "\tvpxor %xmm3, %xmm2, %xmm4"],
         "%xmm4") := by native_decide

/-- (custom order, map) the param→register map places `p0 ↦ %xmm2` (custom,
    not the head-first `%xmm0`). -/
example :
    (vsimdAutoAllocParamPinned ["%xmm2", "%xmm1", "%xmm0"] [] macExample).lookup "p0"
      = some "%xmm2" := by native_decide

/-- (high params + low accumulator) `renderVsimdComAutoParamPinned
    ["%xmm13","%xmm14","%xmm15"] ["%xmm0"]` pins the params **high**
    (`%xmm13/14/15`, the QsBatchDot layout) and holds the low GF-accumulator
    register `%xmm0` out of the temp pool. The temps therefore avoid `%xmm0`
    entirely — `prod`(`v0`) draws the first free `%xmm1`, `res`(`v1`) the next
    `%xmm2`. -/
example :
    renderVsimdComAutoParamPinned ["%xmm13", "%xmm14", "%xmm15"] ["%xmm0"] macExample
      = (["\tvgf2p8mulb %xmm15, %xmm14, %xmm1", "\tvpxor %xmm1, %xmm13, %xmm2"],
         "%xmm2") := by native_decide

/-- (high params + low accumulator) the held `%xmm0` is never handed to a temp:
    neither `v0` nor `v1` maps to it. -/
example :
    ((vsimdAutoAllocParamPinned ["%xmm13", "%xmm14", "%xmm15"] ["%xmm0"] macExample).lookup "v0"
      = some "%xmm1")
    ∧ ((vsimdAutoAllocParamPinned ["%xmm13", "%xmm14", "%xmm15"] ["%xmm0"] macExample).lookup "v1"
      = some "%xmm2") := by native_decide

/-- (degeneracy) with `paramRegs = []` the entry reduces to head-first params
    (`%xmm0/1/2`) with the held temp registers — i.e. `renderVsimdComAutoReserved
    ["%xmm3"]`: temps start at `%xmm4`. -/
example :
    renderVsimdComAutoParamPinned [] ["%xmm3"] macExample
      = renderVsimdComAutoReserved ["%xmm3"] macExample := by native_decide

/-- The full framed `.s` for the worked MAC step, with the SysV ABI load/store
    glue (`vmovdqu (%rdi), %xmm0` …) — the owned, no-jasminc, no-`VCryptOp`
    rendering of the migrated UOV GF(256) MAC kernel. -/
def macExportAsm : String :=
  let alloc : XAlloc :=
    [("p0", "%xmm0"), ("p1", "%xmm1"), ("p2", "%xmm2"),
     ("v0", "%xmm3"), ("v1", "%xmm0")]
  let body := (renderVsimdCom alloc macExample).1
  frameAsmFunction "uov_gf256mac16_vsimd"
    [ "\tvmovdqu\t(%rdi), %xmm0"
    , "\tvmovdqu\t(%rsi), %xmm1"
    , "\tvmovdqu\t(%rdx), %xmm2" ]
    body
    [ "\tvmovdqu\t%xmm0, (%rdi)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println macExportAsm

/-! ## 7. Structural smoke pins on the rendered text -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/- The kernel emits the GFNI multiply (lowercase owned mnemonic, not the
    UPPERCASE jasmin intrinsic). -/
#guard (strContains macExportAsm "vgf2p8mulb")

/- The accumulator is XOR-folded (the MAC), lowercase owned mnemonic. -/
#guard (strContains macExportAsm "vpxor")

/-- The owned export symbol is present. -/
theorem asm_has_export :
    strContains macExportAsm "uov_gf256mac16_vsimd:" = true := by native_decide

/- No UPPERCASE jasmin intrinsic survives — this is the owned (no-jasminc)
    lowercase-mnemonic path. -/
#guard !(strContains macExportAsm "VGF2P8MULB")

/-- A `clmul` binding renders with a leading `$imm` and the `vpclmulqdq`
    mnemonic (AT&T order `$imm, src2, src1, dst`). -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]
      (.clmul 0) "d" "a" "b"
      = "\tvpclmulqdq $0, %xmm1, %xmm0, %xmm2" := by native_decide

/-- An `affineqb` binding renders with a leading `$imm` and the `vgf2p8affineqb`
    mnemonic. -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("A", "%xmm1")]
      (.affineqb 7) "d" "a" "A"
      = "\tvgf2p8affineqb $7, %xmm1, %xmm0, %xmm2" := by native_decide

/-- A `packed .add 32` binding renders as `vpaddd` (dword-lane add). -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]
      (.packed .add 32) "d" "a" "b"
      = "\tvpaddd %xmm1, %xmm0, %xmm2" := by native_decide

/-! ## 7b. AES round render pins (`vaesenc` / `vaesenclast` / `vaeskeygenassist`)

The three AES-round `SimdOp` arms render byte-identically to the bespoke
`X86Backend.Vec128AsmPrinter.renderVCryptInst` `.vaesenc`/`.vaesenclast`/
`.vaeskeygen` arms: `vaesenc`/`vaesenclast` are 3-operand VEX (`op src2, src1, dst`
= `D = op(state=A, rk=B)`); `vaeskeygenassist` is unary with a leading `$rcon`
(`vaeskeygenassist $rcon, %xmmsrc, %xmmdst`). This is the FAEST/AES owned-emit
migration off the bespoke `Vec128.VCryptOp` AES arms. -/

/-- `vaesenc` renders as the 3-operand `vaesenc %xmmrk, %xmmstate, %xmmdst`
    (state = `a`, rk = `b`), byte-identical to `renderVCryptInst`'s `.vaesenc`. -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]
      .vaesenc "d" "a" "b"
      = "\tvaesenc %xmm1, %xmm0, %xmm2" := by native_decide

/-- `vaesenclast` renders as `vaesenclast %xmmrk, %xmmstate, %xmmdst`,
    byte-identical to `renderVCryptInst`'s `.vaesenclast`. -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]
      .vaesenclast "d" "a" "b"
      = "\tvaesenclast %xmm1, %xmm0, %xmm2" := by native_decide

/-- `vaeskeygen 1` renders as the unary `vaeskeygenassist $1, %xmmsrc, %xmmdst`
    (leading `$rcon`, source = `a`; `b` is ignored), byte-identical to
    `renderVCryptInst`'s `.vaeskeygen` arm. -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]
      (.vaeskeygen 1) "d" "a" "b"
      = "\tvaeskeygenassist $1, %xmm0, %xmm2" := by native_decide

/-- `vpshufd 0xFF` renders as the unary `vpshufd $255, %xmmsrc, %xmmdst`
    (leading `$imm8` control byte, source = `a`; `b` is ignored), byte-identical
    to `renderVCryptInst`'s `.vpshufd` arm. This is the key-schedule dword
    broadcast (`VPSHUFD $0xFF`) the Owf128/AesNiLeaf/PrgLambda kernels emit. -/
example :
    renderVsimdInstr [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]
      (.vpshufd 0xFF) "d" "a" "b"
      = "\tvpshufd $255, %xmm0, %xmm2" := by native_decide

/-! ## 8. Byte-shift render pins (`vpslldq` / `vpsrldq`)

The 128-bit byte-shifts are single-source ops (`JasminOp.vpslldq`/`vpsrldq`,
sig `[.reg 128]`). `lowerVsimdExpr` reads only arg 0 and emits one owned AT&T
line, byte-identical to `X86Backend.Vec128AsmPrinter.renderVCryptInst`'s
`.vpslldq`/`.vpsrldq` arms (`\tvpslldq $<n>, <src>, <dst>`). This is what
unblocks the byte-faithful FAEST GF(2^384) emit — every Karatsuba clmul block
folds with `vpsrldq`/`vpslldq`. The pins drive `lowerVsimdExpr` directly on a
constructed single-arg `Expr` over the one-element context `[.reg 128]`. -/

/-- The one-source context for a byte-shift pin: a single `reg 128` operand. -/
abbrev shiftCtx : Ctxt jasminDialect := [.reg 128]

/-- `lowerVsimdExpr` on a `vpslldq 4` binding (single source = arg 0) renders
    byte-identically to `renderVCryptInst`'s `.vpslldq` arm:
    `vpslldq $4, %xmm0, %xmm2`. -/
example :
    lowerVsimdExpr (Γ := shiftCtx)
      (JasminPrint.paramsAndMap shiftCtx).2
      [("p0", "%xmm0"), ("v0", "%xmm2")]
      (.mk (.vpslldq 4) rfl (.cons .here .nil)) "v0"
      = "\tvpslldq $4, %xmm0, %xmm2" := by native_decide

/-- `lowerVsimdExpr` on a `vpsrldq 8` binding (single source = arg 0) renders
    byte-identically to `renderVCryptInst`'s `.vpsrldq` arm (the GHASH/Karatsuba
    byte-shift): `vpsrldq $8, %xmm0, %xmm2`. -/
example :
    lowerVsimdExpr (Γ := shiftCtx)
      (JasminPrint.paramsAndMap shiftCtx).2
      [("p0", "%xmm0"), ("v0", "%xmm2")]
      (.mk (.vpsrldq 8) rfl (.cons .here .nil)) "v0"
      = "\tvpsrldq $8, %xmm0, %xmm2" := by native_decide

/-! ## 9. The YMM (256-bit / AVX2) auto-allocator tier

Sections 4b/4c build the **XMM** (128-bit) auto-allocator. The AVX2 `vsimd`
kernels — the `Avx2Instr` VEX.L=1 path: ChaCha-4way, the 8-way SHA hashes, the
AVX2 NTT butterfly — ride the *same* `SimdOp`/`Com jasminDialect` substrate but
emit over the 256-bit `%ymm0..15` file. Today each such leaf carries a
hand-written `allocYmm`/`ymmOf` map (e.g. `MLKEM.NttEmit.allocYmm`,
`MLDSA.InvNttPointwiseSimdEmit.allocYmm`, `Sha2MultiBufAvx2Emit`).

This section extends the §4b linear scan to the YMM tier verbatim:

* the **allocation** half is prefix-agnostic — `collectVsimdDefs` /
  `xmmLastUse` / `allocXmmSeeded` operate only on SSA *names* and produce a
  `name → register-string` map, so they are reused unchanged; the YMM
  allocator just feeds them a `%ymm`-seeded pinned map and the `ymmPool`;
* the **render** half differs only in the register prefix — `ymmReg` /
  `renderVsimdInstrY` / `lowerVsimdExprY` / `lowerVsimdComY` are the byte-for-byte
  `%ymm` analogues of `xmmReg` / `renderVsimdInstr` / `lowerVsimdExpr` /
  `lowerVsimdCom` (AVX2 mnemonics are width-agnostic: `vpmullw`/`vpaddw`/`vpxor`
  emit identically; the VEX prefix carries the `.L=1` 256-bit width, selected by
  the `%ymm` operand, so the only textual change is `%xmm`→`%ymm`).

The XMM path of §1–§8 is untouched and byte-identical. -/

/-- The `%ymmN` register a name is assigned — the 256-bit (AVX2) analogue of
    `xmmReg`. A `%`-prefixed name is a pre-colored physical register and renders
    as itself; otherwise it is an SSA name looked up in `alloc`; an unmapped one
    yields the explicit `<UNALLOCATED:n>` sentinel (gas-rejected, never silently
    aliased). Mirror of `MLKEM.NttEmit.ymmOf`, but `%`-passthrough-aware. -/
def ymmReg (alloc : XAlloc) (n : String) : String :=
  if n.startsWith "%" then n
  else (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- Render one `vsimd` binding `dst := op(a, b)` to its AVX2 (256-bit) AT&T line
    — the `%ymm` analogue of `renderVsimdInstr`. The mnemonic and VEX 3-operand
    order (`op src2, src1, dst`) are width-agnostic; the `%ymm` operands carry the
    `.L=1` 256-bit width. The `clmul`/`affineqb`/`vaeskeygen`/`vpshufd` arms emit
    their leading `$imm` exactly as the XMM renderer. -/
def renderVsimdInstrY (alloc : XAlloc) (op : SimdOp) (dst a b : String) : String :=
  let rd := ymmReg alloc dst
  let ra := ymmReg alloc a
  let rb := ymmReg alloc b
  match op with
  | .clmul imm =>
      "\tvpclmulqdq $" ++ toString imm ++ ", " ++ rb ++ ", " ++ ra ++ ", " ++ rd
  | .affineqb imm =>
      "\tvgf2p8affineqb $" ++ toString imm.toNat ++ ", " ++ rb ++ ", " ++ ra ++ ", " ++ rd
  | .vaeskeygen rcon =>
      "\tvaeskeygenassist $" ++ toString rcon.toNat ++ ", " ++ ra ++ ", " ++ rd
  | .vpshufd imm =>
      "\tvpshufd $" ++ toString imm ++ ", " ++ ra ++ ", " ++ rd
  | other =>
      "\t" ++ SimdOp.attMnemonic other ++ " " ++ rb ++ ", " ++ ra ++ ", " ++ rd

/-- Lower one `Expr` of the vsimd fragment to its AVX2 (256-bit) AT&T line — the
    `%ymm` analogue of `lowerVsimdExpr`. Only the `JasminOp.vsimd` /
    `vpslldq` / `vpsrldq` arms produce a real instruction; every other op
    produces the explicit `# <unsupported …>` comment line. -/
def lowerVsimdExprY {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (alloc : XAlloc) (e : Expr jasminDialect Γ t) (dst : String) :
    String :=
  match e.op with
  | .vsimd op =>
      let a := argName vm e.args 0
      let b := argName vm e.args 1
      renderVsimdInstrY alloc op dst a b
  | .vpslldq n =>
      "\tvpslldq $" ++ toString n ++ ", " ++ ymmReg alloc (argName vm e.args 0)
        ++ ", " ++ ymmReg alloc dst
  | .vpsrldq n =>
      "\tvpsrldq $" ++ toString n ++ ", " ++ ymmReg alloc (argName vm e.args 0)
        ++ ", " ++ ymmReg alloc dst
  | _ => "\t# <unsupported owned-AT&T op; not in the vsimd fragment>"

/-- Walk a `Com jasminDialect Γ t` to its AVX2 (256-bit) AT&T instruction lines
    plus the name of its return value — the `%ymm` analogue of `lowerVsimdCom`.
    Same fresh-SSA naming (`v{next}`) and `resultName` shaping, so the names here
    are exactly the names the YMM renderer emits. -/
def lowerVsimdComY {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (alloc : XAlloc) (next : Nat) :
    Com jasminDialect Γ t → (List String × String)
  | .ret v => ([], vm t v)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let line := lowerVsimdExprY vm alloc e bound
      let (rest, res) := lowerVsimdComY (vm.extend (t := tEx) bound) alloc (next + 1) body
      (line :: rest, res)

/-- The YMM register pool we allocate from: `%ymm0 … %ymm15` (16 AVX 256-bit
    vector registers). The 256-bit analogue of `xmmPool`. -/
def ymmPool : List String := (List.range 16).map (fun i => "%ymm" ++ toString i)

/-- AVX2 (256-bit) AT&T `.s` body lines for a `vsimd` `Com`, **register-allocated
    automatically** over the `%ymm0..15` file — the YMM analogue of
    `renderVsimdComAuto`. The `Γ` parameters are pinned to `%ymm0..`, the temps
    are linear-scanned over the remaining YMM pool with last-use recycling (the
    *exact* §4b scan: `collectVsimdDefs` + `allocXmmSeeded`, which are
    prefix-agnostic and reused unchanged), and the resulting `XAlloc` feeds the
    YMM renderer. An AVX2 vsimd kernel (ChaCha-4way, 8-way SHA, AVX2 NTT) now
    lowers to fully physical-register owned `.s` with **no hand-written `%ymm`
    map** — dropping the per-file `allocYmm`/`ymmOf`. -/
def renderVsimdComAutoYmm {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%ymm" ++ toString i))
  let pool : List String := ymmPool.drop nres
  let alloc := allocXmmSeeded reserved pinned pool block
  lowerVsimdComY vm alloc 0 com

/-- The full computed YMM `XAlloc` `renderVsimdComAutoYmm` feeds to the renderer:
    the `Γ` parameters pinned to `%ymm0..`, the temps linear-scanned over the rest
    of `ymmPool`. Exposed (gap C, YMM tier) so a store-bearing AVX2 leaf reads its
    ret value's physical register off the map — `ymmReg (vsimdAutoAllocYmm com)
    retName` — for its ABI store (`vmovdqu retReg, (%rdi)`). -/
def vsimdAutoAllocYmm {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : XAlloc :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%ymm" ++ toString i))
  allocXmmSeeded reserved pinned (ymmPool.drop nres) block

/-- Like `renderVsimdComAutoYmm`, but additionally returns the **physical
    `%ymmN` register** the ret SSA value was allocated to (gap C, YMM tier). A
    store-bearing AVX2 leaf uses `retReg` to name its `vmovdqu retReg, (%rdi)`
    ABI store without an `ymmOf` boilerplate helper. The `lines` are
    byte-identical to `renderVsimdComAutoYmm`'s. -/
def renderVsimdComAutoYmmWithReg {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : (List String × String) :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVsimdDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%ymm" ++ toString i))
  let alloc := allocXmmSeeded reserved pinned (ymmPool.drop nres) block
  let (lines, retName) := lowerVsimdComY vm alloc 0 com
  (lines, ymmReg alloc retName)

/-! ### YMM-tier pins (on `macExample`, retargeted to `%ymm`)

The same two-binding `vsimd` step (`prod := gf2p8mulb(achunk, bbcast);
res := acc ^ prod`) renders over the 256-bit file: params pinned to
`%ymm0/1/2`, temp `prod`(`v0`) → `%ymm3`, XOR result (`v1`) → next free
`%ymm4`. The allocator decisions (which SSA value lands on which register
index) are identical to the XMM pins in §6 — only the prefix differs, which is
the whole point of the YMM tier. (The kernel shape stands in for the AVX2
leaves; `gf2p8mulb`/`vpxor` are width-agnostic mnemonics.) -/

/-- The YMM auto-allocator reproduces the worked step over `%ymm`: params →
    `%ymm0/1/2`, temp → `%ymm3`, result → `%ymm4`. Byte-for-byte the §6
    `renderVsimdComAuto` pin with `%xmm`→`%ymm`. -/
example :
    (renderVsimdComAutoYmm macExample).1
      = ["\tvgf2p8mulb %ymm2, %ymm1, %ymm3", "\tvpxor %ymm3, %ymm0, %ymm4"] := by
  native_decide

/-- The YMM allocator pins the first parameter to the low YMM register, exactly
    as a hand-written `allocYmm` would: `p0 ↦ %ymm0`. -/
example : (vsimdAutoAllocYmm macExample).lookup "p0" = some "%ymm0" := by
  native_decide

/-- (gap C, YMM) `renderVsimdComAutoYmmWithReg` returns `(lines, retReg)` with
    `retReg` = `%ymm4`, the register the ret (`v1`) was allocated to — what a
    store-bearing AVX2 leaf names for its `vmovdqu %ymm4, (%rdi)` ABI store. -/
example :
    renderVsimdComAutoYmmWithReg macExample
      = (["\tvgf2p8mulb %ymm2, %ymm1, %ymm3", "\tvpxor %ymm3, %ymm0, %ymm4"],
         "%ymm4") := by native_decide

/-- The pool is the 16 AVX `%ymm` registers (the `%xmm`→`%ymm` retargeting of
    `xmmPool`). -/
example : ymmPool.length = 16 := by native_decide

/-- A `packed .add 32` binding renders as `vpaddd` over `%ymm` operands (the AVX2
    dword-lane add the NTT/ChaCha kernels emit). -/
example :
    renderVsimdInstrY [("d", "%ymm2"), ("a", "%ymm0"), ("b", "%ymm1")]
      (.packed .add 32) "d" "a" "b"
      = "\tvpaddd %ymm1, %ymm0, %ymm2" := by native_decide

/-- A `packed .mul 16` binding renders as `vpmullw` over `%ymm` operands (the
    AVX2 NTT Montgomery low-product). -/
example :
    renderVsimdInstrY [("d", "%ymm2"), ("a", "%ymm0"), ("b", "%ymm1")]
      (.packed .mul 16) "d" "a" "b"
      = "\tvpmullw %ymm1, %ymm0, %ymm2" := by native_decide

/-- A `mulhi16` binding renders as `vpmulhw` over `%ymm` operands (the AVX2 NTT
    signed high-product). -/
example :
    renderVsimdInstrY [("d", "%ymm2"), ("a", "%ymm0"), ("b", "%ymm1")]
      .mulhi16 "d" "a" "b"
      = "\tvpmulhw %ymm1, %ymm0, %ymm2" := by native_decide

/-! ## 10. The ZMM (512-bit / AVX-512) auto-allocator tier

Sections 4b/4c build the **XMM** (128-bit) auto-allocator; §9 the **YMM**
(256-bit) tier. The AVX-512 `vsimd` kernels — the `vpackZMM`/`vpackZMMd`/
`vprordZMM` family over `reg 512` (Keccak-x8, the ZMM NTT butterfly,
Poseidon2-AVX512) — emit over the 512-bit `%zmm0..31` file (AVX-512 widens the
vector register file from 16 to **32** registers). Today each such leaf carries a
hand-written `%zmm` map (e.g. `VpackZmmAsmPrint.bflyAlloc`).

The 512-bit ops are **not** `JasminOp.vsimd op` (over `SimdOp`) but
`JasminOp.vpackZMM bop` / `JasminOp.vpackZMMd bop` (over `JasminBinOp`, both with
signature `[.reg 512, .reg 512] → .reg 512`). The *render* half for that fragment
(`zmmReg` / `renderVpackZmmInstr` / `lowerVpackZmmExpr` / `lowerVpackZmmCom`)
lives in `VpackZmmAsmPrint.lean`, which imports this module. So this section
builds the **allocator** half — the `%zmm0..31` `XAlloc` that
`VpackZmmAsmPrint.lowerVpackZmmCom` consumes — leaving the line-rendering one
import-level up. The allocation engine (`xmmLastUse` / `allocXmmSeeded`) is
prefix- and pool-agnostic and reused verbatim; the only new piece is a
`vpackZMM`-aware def-collector (the §4b `collectVsimdDefs` reads the `.vsimd`
arg-set, which is empty for a `.vpackZMM` op).

The XMM/YMM paths of §1–§9 are untouched and byte-identical. -/

/-- The ZMM register pool we allocate from: `%zmm0 … %zmm31` (32 AVX-512 512-bit
    vector registers — AVX-512 doubles the vector file from the 16 of `xmmPool`/
    `ymmPool`). -/
def zmmPool : List String := (List.range 32).map (fun i => "%zmm" ++ toString i)

/-- The (dst, srcs) read-set of one `vpackZMM`-fragment binding `dst := bop(a, b)`.
    The 512-bit analogue of `vsimdExprDstSrcs`: the binary `vpackZMM` / `vpackZMMd`
    ops read args 0,1; an out-of-fragment op has no sources (it renders as the
    `# <unsupported …>` comment in `VpackZmmAsmPrint.lowerVpackZmmExpr`). The
    `.vsimd`-based `vsimdExprDstSrcs` cannot be reused here — it returns `(dst, [])`
    for a `.vpackZMM` op, so liveness would see no reads and recycle live inputs. -/
def vpackZmmExprDstSrcs {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (e : Expr jasminDialect Γ t) (dst : String) :
    String × List String :=
  match e.op with
  | .vpackZMM _  => (dst, [argName vm e.args 0, argName vm e.args 1])
  | .vpackZMMd _ => (dst, [argName vm e.args 0, argName vm e.args 1])
  | _ => (dst, [])

/-- Walk a `Com jasminDialect Γ t` to its straight-line `(dst, srcs)` block plus
    the return-value name, using the **same** fresh-SSA naming (`v{next}`) and
    `resultName` shaping as `VpackZmmAsmPrint.lowerVpackZmmCom` — so the names here
    are exactly the names the ZMM renderer emits. The `vpackZMM`-fragment twin of
    `collectVsimdDefs`. -/
def collectVpackZmmDefs {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (vm : VarMap Γ) (next : Nat) :
    Com jasminDialect Γ t → (List (String × List String) × String)
  | .ret v => ([], vm t v)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let ds := vpackZmmExprDstSrcs vm e bound
      let (rest, res) := collectVpackZmmDefs (vm.extend (t := tEx) bound) (next + 1) body
      (ds :: rest, res)

/-- The full computed ZMM `XAlloc` over `%zmm0..31`: the `Γ` parameters pinned to
    `%zmm0..`, the temps linear-scanned over the rest of `zmmPool` with last-use
    recycling (the §4b `allocXmmSeeded` engine, pool-agnostic and reused). This is
    the map `VpackZmmAsmPrint.lowerVpackZmmCom` consumes — a `vpackZMM` kernel
    (Keccak-x8, ZMM NTT butterfly, Poseidon2-AVX512) lowers to fully
    physical-register owned `%zmm` `.s` with **no hand-written `%zmm` map**,
    dropping the per-file `bflyAlloc`-style hand allocation.

    The render `def renderVsimdComAutoZmm` lives one import-level up, in
    `VpackZmmAsmPrint.lean`, wiring this alloc into `lowerVpackZmmCom`:
    ```
    def renderVpackZmmComAutoZmm (com : Com jasminDialect Γ t) : List String × String :=
      let (_, vm) := JasminPrint.paramsAndMap Γ
      VpackZmmAsmPrint.lowerVpackZmmCom vm (vsimdAutoAllocZmm com) 0 com
    ```
    (it cannot live here — `lowerVpackZmmCom` is in the module that imports this
    one). -/
def vsimdAutoAllocZmm {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : XAlloc :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, _) := collectVpackZmmDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%zmm" ++ toString i))
  allocXmmSeeded reserved pinned (zmmPool.drop nres) block

/-- The physical `%zmmN` register the ret SSA value of a `vpackZMM` `Com` was
    allocated to, read off `vsimdAutoAllocZmm` (gap C, ZMM tier). A store-bearing
    AVX-512 leaf uses this to name its `vmovdqu64 retReg, (%rdi)` ABI store
    without a hand-written `zmmOf` helper. (`zmmReg`/`xmmReg` are `%`-passthrough
    lookups against the same `XAlloc`; the ret name is the `.2` of
    `collectVpackZmmDefs`.) -/
def vsimdAutoRetRegZmm {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) : String :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let reserved : List String := params.map (fun p => p.var.var.vname)
  let (block, retName) := collectVpackZmmDefs vm 0 com
  let nres := reserved.length
  let pinned : XAlloc :=
    reserved.zipIdx.map (fun (n, i) => (n, "%zmm" ++ toString i))
  let alloc := allocXmmSeeded reserved pinned (zmmPool.drop nres) block
  xmmReg alloc retName

/-! ### ZMM-tier pins (on `butterflyHiCom`-shaped block, here re-collected over
the dialect directly)

The §5/§6 worked NTT butterfly `hi` slice (`prod := vpackZMM mul w b;
hi := vpackZMM add a prod`) auto-allocated over the 512-bit file: params
`w`/`a`/`b` → `%zmm0/1/2`, temp `prod`(`v0`) → `%zmm3`, result `hi`(`v1`) →
next free `%zmm4`. We exercise the allocator on the §6 `macExample` *shape*
re-typed as a `vpackZMM` block below, plus pin `zmmPool`'s size (32 ≠ the 16 of
`xmmPool`/`ymmPool` — the AVX-512 register-file widening). The full
`renderVsimdComAutoZmm` end-to-end pin (rendered `%zmm` lines) lives in
`VpackZmmAsmPrint.lean`, which has the `lowerVpackZmmCom` renderer. -/

/-- A minimal two-binding `vpackZMM` block over the input context `[w, a, b]`
    (each `reg 512`): `prod := vpackZMM mul w b; hi := vpackZMM add a prod`. The
    same shape as `ButterflyBlockCom.butterflyHiCom`, built inline so this
    allocator pin needs no import beyond `JasminPrint`. -/
def zmmBflyExample : Com jasminDialect [.reg 512, .reg 512, .reg 512] (.reg 512) :=
  -- prod := vpackZMM mul w b   (w = head, b = third)
  .var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
    -- hi := vpackZMM add a prod   (a is now `.there (.there .here)`, prod is `.here`)
    (.var (.mk (.vpackZMM .add) rfl
            (.cons (.there (.there (.there .here))) (.cons .here .nil)))
      (.ret .here))

/-- The ZMM auto-allocator pins the params to the low ZMM registers and linear-
    scans the temps over the rest of `%zmm0..31`: `w`/`a`/`b`(`p0/p1/p2`) →
    `%zmm0/1/2`, `prod`(`v0`) → `%zmm3`, `hi`(`v1`) → next free `%zmm4` — exactly
    the §9 YMM / §6 XMM allocator decisions, only the `%zmm` prefix and 32-reg
    pool differ. -/
example :
    vsimdAutoAllocZmm zmmBflyExample
      = [("v1", "%zmm4"), ("v0", "%zmm3"),
         ("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2")] := by native_decide

/-- The ZMM allocator pins the first parameter to the low ZMM register, exactly
    as a hand-written `bflyAlloc` would: `p0 ↦ %zmm0`. -/
example : (vsimdAutoAllocZmm zmmBflyExample).lookup "p0" = some "%zmm0" := by
  native_decide

/-- The temp `prod`(`v0`) draws `%zmm3` (first free after the three pinned
    params); the result `hi`(`v1`) the next free `%zmm4`. The reserved params are
    never recycled, so the live input registers survive. -/
example : (vsimdAutoAllocZmm zmmBflyExample).lookup "v0" = some "%zmm3" := by
  native_decide

/-- (gap C, ZMM) the ret value's physical register read off the alloc is
    `%zmm4` — what a store-bearing AVX-512 leaf names for its
    `vmovdqu64 %zmm4, (%rdi)` ABI store. -/
example : vsimdAutoRetRegZmm zmmBflyExample = "%zmm4" := by native_decide

/-- The ZMM pool is the 32 AVX-512 `%zmm` registers — double the 16 of `xmmPool`
    / `ymmPool` (the AVX-512 vector-register-file widening). -/
example : zmmPool.length = 32 := by native_decide

/-- `zmmPool` indeed starts at `%zmm0` and the widening is real: `%zmm31` (index
    31) is in the pool, unlike the 16-reg `xmmPool`/`ymmPool`. -/
example : zmmPool.getLast? = some "%zmm31" := by native_decide

/-- A `vpackZMMd` (dword-lane) binding is also recognized by the ZMM
    def-collector (SHA-256/ChaCha20 ride the dword analogue), reading both source
    args for liveness. A single-`vpackZMMd` block pins `p0 ↦ %zmm0`. -/
example :
    (vsimdAutoAllocZmm
      (Γ := [.reg 512, .reg 512]) (t := .reg 512)
      (.var (.mk (.vpackZMMd .xor) rfl
              (.cons .here (.cons (.there .here) .nil)))
        (.ret .here))).lookup "p0" = some "%zmm0" := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
