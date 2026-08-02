/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint

/-!
# OWNED AES-128 ECB single-block emit on the UNIFIED `Com jasminDialect`

`SimdBytes.lean` (§7) emits the AES-128 single-block ECB encrypt through the
**bespoke** `Vec128`/`VCryptOp` crypto-SIMD IR: its round chain
`aesEcbBlk : List VCryptOp` (`VPXOR` whitening, nine `VAESENC`, one
`VAESENCLAST`) is lowered by `Vec128Lowering.lowerVCryptBlock`, byte-encoded by
`Vec128Encoder.encodeVCryptInst`, and stitched into a relocatable `.o`.

This module re-authors the SAME AES-128 ECB single-block kernel on the
**unified** stack

```
Com jasminDialect  (vsimd fragment)  ──renderVsimdCom──▶  AT&T .s lines
```

with **zero** dependency on `Vec128Lowering` / `Vec128Model` / `Vec128Encoder` /
`Vec128AsmPrinter`. The only crypto-SIMD import is `VIR.VsimdAsmPrint` (the
committed owned AT&T renderer, whose `.bitwise .xor`/`.vaesenc`/`.vaesenclast`
arms are byte-identical to `renderVCryptInst`).

## The AES round semantics, dialect-native

Each AES op rides `JasminOp.vsimd (op : SimdOp)`:

| bespoke `VCryptOp`     | unified `SimdOp`        | denote        |
|------------------------|-------------------------|---------------|
| `.xorq`                | `vsimd (.bitwise .xor)` | `^^^`         |
| `.aesenc`              | `vsimd .vaesenc`        | `wAESENCW`    |
| `.aesenclast`          | `vsimd .vaesenclast`    | `wAESENCLASTW`|

The `SimdOp` AES denotes (`wAESENCW`/`wAESENCLASTW` in `JasminDialect`) are the
verbatim-copied bespoke `Vec128Model.vaesenc`/… (= the carried `Jasmin.wAESENC`
/ FIPS-197 / Sail-x86 anchor, `SailX86Lean.aesenc_eq_sail`), so the migrated
kernel computes the SAME AES as the bespoke `aesEcbBlk`.

## What is emitted

`aes128_ecb_block(buf=%rdi)` over the SAME 208-byte single-struct ABI as the
bespoke driver: the 11 pre-expanded round keys at `(%rdi + 16·k)` (`k = 0..10`),
the plaintext block at `(%rdi + 176)`, and the ciphertext output at
`(%rdi + 192)`. The round chain is rendered by `renderVsimdCom` (the owned AT&T
`vsimd` printer); the `vmovdqu` round-key/plaintext loads and the ciphertext
store are the SAME straight-line ABI glue as `SimdBytes.encodeAesEcbBlock`.
Round keys / state are pinned to the SAME XMM slots as the bespoke
`aesEcbAlloc` (`ct ↦ %xmm0`, `st ↦ %xmm1`, `rk_k ↦ %xmm(2+k)`).

## Status

The Com program is pinned `denote = spec` by a whole-program `rfl` (unfolding
the `Com`/`Expr` smart constructors resolves the `vsimd` denote arms to the same
`wAESENCW`/`wAESENCLASTW`/`^^^` fold the bespoke `aesEcbBlk` threads through
`evalVCryptInst`). The structural `strContains` smoke pins match the bespoke
driver's. The acceptance gate is the `aes128_ecb_block_owned_kat.c` FIPS-197
Appendix B / C.1 KAT re-run on the new `.s`. Fully proved, no new axiom.

Invoke:  lake env lean --run
         CatCrypt/Crypto/SecureCompilation/X86Backend/SimdBytesVsimd.lean
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SimdBytesVsimd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint

/-! ## 1. `Expr` smart-constructors for the AES `vsimd` fragment -/

/-- `r128` abbreviation. -/
abbrev r128 : JasminTy := .reg 128

/-- `vaesenc(state, rk)` Expr at two source vars. -/
private def eAesenc {Γ : Ctxt jasminDialect} (vs vk : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd .vaesenc) rfl (.cons vs (.cons vk .nil))

/-- `vaesenclast(state, rk)` Expr at two source vars. -/
private def eAesenclast {Γ : Ctxt jasminDialect} (vs vk : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd .vaesenclast) rfl (.cons vs (.cons vk .nil))

/-- `xorq` (whole-128 bitwise xor) Expr at two source vars. -/
private def eXor {Γ : Ctxt jasminDialect} (va vb : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd (.bitwise .xor)) rfl (.cons va (.cons vb .nil))

/-! ## 2. The AES-128 ECB single-block body as a `Com` program

`ecbCom` takes the plaintext block `ct` (`#0`) and the 11 round keys
`rk0..rk10` (`#1 … #11`), and computes one AES-128-ECB block:

```
st = ct ⊕ rk0
for i = 1..9: st = aesenc(st, rk_i)
st = aesenclast(st, rk10)
```

mirroring the bespoke `SimdBytes.aesEcbBlk`. -/

/-- The ECB input context: `[ct, rk0, rk1, …, rk10]` (12 × `reg 128`).
    `ct = #0`, `rk0 = #1`, …, `rk10 = #11`. -/
abbrev ecbCtx : Ctxt jasminDialect :=
  [r128, r128, r128, r128, r128, r128, r128, r128, r128, r128, r128, r128]

/-- One AES-128-ECB block over `ecbCtx = [ct, rk0, …, rk10]`:
    `st = ct ⊕ rk0`, 9 `aesenc(st, rk_i)`, one `aesenclast(st, rk10)`. The single
    output `st` is the head of the returned program. Each binding pushes one fresh
    `r128`, so the running `st` is always `.here`. After `k` bindings `ct` sits at
    depth `k` and `rk_i` at depth `k + i + 1` (de Bruijn nests written inline). -/
def ecbCom : Com jasminDialect ecbCtx r128 :=
  -- b0  st = ct ⊕ rk0        ; ct=#0 ; rk0=#1
  .var (eXor .here (.there .here))
  -- b1  st = aesenc(st, rk1)  ; rk1 at depth 1+1+1 = 3
  (.var (eAesenc .here (.there (.there (.there .here))))
  -- b2  st = aesenc(st, rk2)  ; rk2 at depth 2+2+1 = 5
  (.var (eAesenc .here (.there (.there (.there (.there (.there .here))))))
  -- b3  st = aesenc(st, rk3)  ; rk3 at depth 3+3+1 = 7
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there .here))))))))
  -- b4  st = aesenc(st, rk4)  ; rk4 at depth 4+4+1 = 9
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  -- b5  st = aesenc(st, rk5)  ; rk5 at depth 5+5+1 = 11
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  -- b6  st = aesenc(st, rk6)  ; rk6 at depth 6+6+1 = 13
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
  -- b7  st = aesenc(st, rk7)  ; rk7 at depth 7+7+1 = 15
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
  -- b8  st = aesenc(st, rk8)  ; rk8 at depth 8+8+1 = 17
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))
  -- b9  st = aesenc(st, rk9)  ; rk9 at depth 9+9+1 = 19
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))
  -- b10 st = aesenclast(st, rk10) ; rk10 at depth 10+10+1 = 21
  (.var (eAesenclast .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))
  (.ret .here)))))))))))

/-! ## 3. The ECB spec -/

/-- The AES-128-ECB value the bespoke `aesEcbBlk` computes on plaintext block
    `ct` and round keys `rk`. -/
def ecbSpec (ct : BitVec 128) (rk : Nat → BitVec 128) : BitVec 128 :=
  let s0 := ct ^^^ rk 0
  let s1 := wAESENCW s0 (rk 1)
  let s2 := wAESENCW s1 (rk 2)
  let s3 := wAESENCW s2 (rk 3)
  let s4 := wAESENCW s3 (rk 4)
  let s5 := wAESENCW s4 (rk 5)
  let s6 := wAESENCW s5 (rk 6)
  let s7 := wAESENCW s6 (rk 7)
  let s8 := wAESENCW s7 (rk 8)
  let s9 := wAESENCW s8 (rk 9)
  wAESENCLASTW s9 (rk 10)

/-- A concrete valuation builder for `ecbCtx` from `ct` and the 11 round keys. -/
def ecbVal (ct : BitVec 128) (rk : Nat → BitVec 128) : Ctxt.Valuation ecbCtx :=
  .cons ct (.cons (rk 0) (.cons (rk 1) (.cons (rk 2) (.cons (rk 3) (.cons (rk 4)
    (.cons (rk 5) (.cons (rk 6) (.cons (rk 7) (.cons (rk 8) (.cons (rk 9)
    (.cons (rk 10) .nil)))))))))))

set_option maxRecDepth 100000 in
/-- **ECB denotation pin.** The migrated Com computes the SAME AES-128-ECB block
    as the bespoke `aesEcbBlk` (whitening `^^^`, nine `wAESENCW`, one
    `wAESENCLASTW`). -/
theorem ecbCom_denote (ct : BitVec 128) (rk : Nat → BitVec 128) :
    ecbCom.denote (ecbVal ct rk) = ecbSpec ct rk := by
  simp only [ecbCom, ecbSpec, ecbVal, eXor, eAesenc, eAesenclast]
  rfl

/-! ## 4. Pinning round keys / state to fixed XMM slots (the bespoke `aesEcbAlloc`)

The bespoke `SimdBytes.aesEcbReserved = ["ct","st", rk0..rk10]` with
`allocXmmCrypto` pins `ct ↦ %xmm0`, `st ↦ %xmm1`, `rk_k ↦ %xmm(2+k)`. Here the
running state SSA chain is all in `%xmm1` (the bespoke `st`), the plaintext
param `p0 = ct` in `%xmm0`, and `p_{k+1} = rk_k` in `%xmm(2+k)`. -/

/-- `%xmmN`. -/
def xmmName (i : Nat) : String := "%xmm" ++ toString i

/-- The fixed register for round key `rk_k` (`k = 0..10`): `%xmm(2+k)`. -/
def rkXmm (k : Nat) : String := xmmName (2 + k)

/-- The fixed register for the state `st`: `%xmm1`. -/
def stXmm : String := xmmName 1

/-- The fixed register for the plaintext block `ct`: `%xmm0`. -/
def ctXmm : String := xmmName 0

/-- The XMM allocation for the ECB body: plaintext param `p0 ↦ %xmm0`, round-key
    params `p_{k+1} ↦ %xmm(2+k)`, and every in-place SSA state temp `v{n} ↦ %xmm1`
    (the running chain stays in the `st` register). -/
def ecbAlloc : XAlloc :=
  [ ("p0", ctXmm) ] ++
  ((List.range 11).map (fun k => ("p" ++ toString (k + 1), rkXmm k))) ++
  ((List.range 11).map (fun n => ("v" ++ toString n, stXmm)))

/-- The rendered AT&T lines for the ECB body (11 lines: 1 whiten, 9 `vaesenc`,
    1 `vaesenclast`). -/
def ecbLines : List String := (renderVsimdCom ecbAlloc ecbCom).1

/-! ## 5. The emitted `.s` text (owned backend, single-struct ABI)

`aes128_ecb_block(buf=%rdi)` over the SAME 208-byte struct ABI as the bespoke
`SimdBytes` driver: round keys at `(%rdi + 16·k)`, plaintext at `(%rdi + 176)`,
ciphertext out at `(%rdi + 192)`. -/

/-- The 12 `vmovdqu` input loads: the 11 round keys `rk_k ↦ %xmm(2+k)` from
    `(%rdi + 16·k)`, then the plaintext block `ct ↦ %xmm0` from `(%rdi + 176)`. -/
def aesEcbLoadLines : List String :=
  ((List.range 11).map (fun k =>
    "\tvmovdqu\t" ++ toString (16 * k) ++ "(%rdi), " ++ rkXmm k)) ++
  [ "\tvmovdqu\t176(%rdi), " ++ ctXmm ]

/-- The ciphertext store: `st ↦ %xmm1` to `(%rdi + 192)`. -/
def aesEcbStoreLine : String := "\tvmovdqu\t" ++ stXmm ++ ", 192(%rdi)"

/-- The emitted `aes128_ecb_block` function text: `.text`/`.globl` framing, the
    round-key + plaintext loads, the verified Com-rendered round chain, the
    ciphertext store, `ret`. -/
def aesEcbExportAsm : String :=
  frameAsmFunction "aes128_ecb_block"
    aesEcbLoadLines
    ecbLines
    [aesEcbStoreLine]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println aesEcbExportAsm

/-! ## 6. Structural smoke pins (matching the bespoke driver) -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The export entry point is present. -/
theorem asm_has_export :
    strContains aesEcbExportAsm "aes128_ecb_block:" = true := by native_decide

/- The whitening + the AES round chain is emitted: the `VPXOR` whitening, the
    `VAESENC` rounds, and the final `VAESENCLAST`. -/
#guard (strContains aesEcbExportAsm "vpxor ")
    && (strContains aesEcbExportAsm "vaesenc ")
    && (strContains aesEcbExportAsm "vaesenclast ")

/- The single-struct ABI is emitted: round-key/plaintext loads from `%rdi` and
    the ciphertext store to `(%rdi + 192)`. -/
#guard (strContains aesEcbExportAsm "(%rdi), %xmm2")
    && (strContains aesEcbExportAsm "176(%rdi), %xmm0")
    && (strContains aesEcbExportAsm ", 192(%rdi)")

/- No register name escaped allocation (the 11 round keys + state + plaintext
    fit in 13 XMM, no spill). -/
#guard !(strContains aesEcbExportAsm "UNALLOCATED")

/- No UPPERCASE jasmin intrinsic survives — the owned (no-jasminc)
    lowercase-mnemonic path. -/
#guard !(strContains aesEcbExportAsm "VAESENC") && !(strContains aesEcbExportAsm "VPXOR")

/-! ## 7. Emit driver -/

/-- Write the owned-backend `.s` to `bench/aes_compare/gen_owned_simd/aes128_ecb_block_owned.s`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/aes_compare/gen_owned_simd"
  let path := "bench/aes_compare/gen_owned_simd/aes128_ecb_block_owned.s"
  IO.FS.writeFile path aesEcbExportAsm
  IO.println s!"wrote {path}"

end CatCrypt.Crypto.SecureCompilation.X86Backend.SimdBytesVsimd

open CatCrypt.Crypto.SecureCompilation.X86Backend.SimdBytesVsimd in
/-- `lake env lean --run` entry point: emit the owned-backend AES-128-ECB
    single-block `.s` on the unified `Com jasminDialect`. `private` so it does
    not collide with other `main`s in the `EmitAll` rot-guard aggregator. -/
private def main : IO Unit := emit
