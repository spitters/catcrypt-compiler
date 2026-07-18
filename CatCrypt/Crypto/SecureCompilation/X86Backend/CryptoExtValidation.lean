/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExtEncoder

/-!
# Differential validation of the crypto-extension byte encoder against `gas`

`ScalarValidation.lean` pins the GP-ALU encoder to the exact bytes `gas` produces;
`Avx512Validation.lean` does the same for the EVEX encoder. This module is the
**crypto-extension counterpart**: it pins `CryptoExtEncoder.lean`'s SHA-NI / PCLMUL
/ VAES / GFNI / AVX2-VEX encoders to `gas`'s output for each mnemonic.

The right-hand byte strings below are the **exact output of `gas`** (`as --64`,
decoded with `objdump -d -M intel`) for the matching mnemonic. Each `example`
checks the encoder reproduces those bytes. The trusted edge shrinks from "`gas`
encodes each mnemonic per the SDM" to "our encoder matches `gas`'s bytes".

Unlike the GP-ALU forms (#444), there is **no Sail-x86 decode round-trip** for
these families — the ACL2/Sail-x86 model has no SHA-NI / VAES / GFNI / PCLMUL
decode tables — so they remain at this gas-pinned validation tier.

## The allocations under test

`aLow` pins names to low XMM registers (`%xmm1`/`%xmm2`/`%xmm3`), `aHigh` to the
high-8 registers (`%xmm5`/`%xmm8` for the legacy REX forms, `%ymm13`..`%ymm15`
for the VEX extension bits) so the `R`/`B`/`vvvv` extension fields are exercised.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-- Low-register allocation: `d↦%xmm1 s↦%xmm2`. -/
def aLow : VAlloc := [("d", "%xmm1"), ("s", "%xmm2")]

/-- High-register allocation for the legacy REX forms: `d↦%xmm5 s↦%xmm8`. -/
def aHigh : VAlloc := [("d", "%xmm5"), ("s", "%xmm8")]

/-! ## 1. SHA-NI (`0F 38 cb/cc/cd`) -/

-- gas: `sha256rnds2 xmm1,xmm2,xmm0`  →  0f 38 cb ca   (implicit xmm0, no REX)
example : encodeSha aLow (.rnds2 "d" "s")
    = [0x0f, 0x38, 0xcb, 0xca].map (BitVec.ofNat 8) := by native_decide

-- gas: `sha256rnds2 xmm5,xmm8,xmm0`  →  41 0f 38 cb e8   (REX.B for xmm8 source)
example : encodeSha aHigh (.rnds2 "d" "s")
    = [0x41, 0x0f, 0x38, 0xcb, 0xe8].map (BitVec.ofNat 8) := by native_decide

-- gas: `sha256msg1 xmm1,xmm2`  →  0f 38 cc ca
example : encodeSha aLow (.msg1 "d" "s")
    = [0x0f, 0x38, 0xcc, 0xca].map (BitVec.ofNat 8) := by native_decide

-- gas: `sha256msg1 xmm5,xmm8`  →  41 0f 38 cc e8
example : encodeSha aHigh (.msg1 "d" "s")
    = [0x41, 0x0f, 0x38, 0xcc, 0xe8].map (BitVec.ofNat 8) := by native_decide

-- gas: `sha256msg2 xmm1,xmm2`  →  0f 38 cd ca
example : encodeSha aLow (.msg2 "d" "s")
    = [0x0f, 0x38, 0xcd, 0xca].map (BitVec.ofNat 8) := by native_decide

-- gas: `sha256msg2 xmm5,xmm8`  →  41 0f 38 cd e8
example : encodeSha aHigh (.msg2 "d" "s")
    = [0x41, 0x0f, 0x38, 0xcd, 0xe8].map (BitVec.ofNat 8) := by native_decide

/-! ### A whole SHA-256 round-couple block witness

The four-instruction sequence a SHA-256 round emits (`MSG1; MSG2; RNDS2; RNDS2`)
encodes to the concatenation of the per-instruction bytes — the contiguous stream
a `.text` section consumes. We pin it to the exact concatenated `gas` bytes. -/

/-- A representative SHA-256 round-couple instruction sequence. -/
def shaRound : List ShaInstr :=
  [.msg1 "d" "s", .msg2 "d" "s", .rnds2 "d" "s", .rnds2 "d" "s"]

example :
    shaRound.flatMap (encodeSha aLow)
      = [0x0f, 0x38, 0xcc, 0xca,
         0x0f, 0x38, 0xcd, 0xca,
         0x0f, 0x38, 0xcb, 0xca,
         0x0f, 0x38, 0xcb, 0xca].map (BitVec.ofNat 8) := by native_decide

/-! ## 2. PCLMUL (`66 0F 3A 44 /r ib` legacy, VEX `0F3A 44`)

`a3` is a three-register low allocation (`d↦%xmm1 v↦%xmm2 m↦%xmm3`); `aY3` the
256-bit `ymm` analogue; `aYHi` exercises the VEX extension bits with high `ymm`
registers (`d↦%ymm5 v↦%ymm6 m↦%ymm13`). -/

/-- Three-register low XMM allocation: `d↦%xmm1 v↦%xmm2 m↦%xmm3`. -/
def a3 : VAlloc := [("d", "%xmm1"), ("v", "%xmm2"), ("m", "%xmm3")]

/-- Three-register low YMM allocation. -/
def aY3 : VAlloc := [("d", "%ymm1"), ("v", "%ymm2"), ("m", "%ymm3")]

/-- High YMM allocation: `d↦%ymm5 v↦%ymm6 m↦%ymm13` (exercises VEX `B̄`). -/
def aYHi : VAlloc := [("d", "%ymm5"), ("v", "%ymm6"), ("m", "%ymm13")]

-- gas: `pclmulqdq xmm1,xmm2,0x00`  →  66 0f 3a 44 ca 00
example : encodePclmul aLow (.pclmulqdq "d" "s" 0x00)
    = [0x66, 0x0f, 0x3a, 0x44, 0xca, 0x00].map (BitVec.ofNat 8) := by native_decide

-- gas: `pclmulqdq xmm1,xmm2,0x11`  →  66 0f 3a 44 ca 11
example : encodePclmul aLow (.pclmulqdq "d" "s" 0x11)
    = [0x66, 0x0f, 0x3a, 0x44, 0xca, 0x11].map (BitVec.ofNat 8) := by native_decide

-- gas: `pclmulqdq xmm5,xmm8,0x10`  →  66 41 0f 3a 44 e8 10   (REX.B for xmm8)
example : encodePclmul aHigh (.pclmulqdq "d" "s" 0x10)
    = [0x66, 0x41, 0x0f, 0x3a, 0x44, 0xe8, 0x10].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpclmulqdq xmm1,xmm2,xmm3,0x00`  →  c4 e3 69 44 cb 00
example : encodePclmul a3 (.vpclmulqdq false "d" "v" "m" 0x00)
    = [0xc4, 0xe3, 0x69, 0x44, 0xcb, 0x00].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpclmulqdq ymm1,ymm2,ymm3,0x11`  →  c4 e3 6d 44 cb 11   (L=1)
example : encodePclmul aY3 (.vpclmulqdq true "d" "v" "m" 0x11)
    = [0xc4, 0xe3, 0x6d, 0x44, 0xcb, 0x11].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpclmulqdq ymm5,ymm6,ymm13,0x10`  →  c4 c3 4d 44 ed 10   (B̄=0 for ymm13)
example : encodePclmul aYHi (.vpclmulqdq true "d" "v" "m" 0x10)
    = [0xc4, 0xc3, 0x4d, 0x44, 0xed, 0x10].map (BitVec.ofNat 8) := by native_decide

/-! ## 3. VAES (VEX `0F38` DC/DD/DE/DF) -/

-- gas: `vaesenc xmm1,xmm2,xmm3`  →  c4 e2 69 dc cb
example : encodeVaes a3 (.enc false "d" "v" "m")
    = [0xc4, 0xe2, 0x69, 0xdc, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vaesenc ymm1,ymm2,ymm3`  →  c4 e2 6d dc cb   (L=1)
example : encodeVaes aY3 (.enc true "d" "v" "m")
    = [0xc4, 0xe2, 0x6d, 0xdc, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vaesenclast xmm1,xmm2,xmm3`  →  c4 e2 69 dd cb
example : encodeVaes a3 (.enclast false "d" "v" "m")
    = [0xc4, 0xe2, 0x69, 0xdd, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vaesdec xmm1,xmm2,xmm3`  →  c4 e2 69 de cb
example : encodeVaes a3 (.dec false "d" "v" "m")
    = [0xc4, 0xe2, 0x69, 0xde, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vaesdeclast ymm5,ymm6,ymm13`  →  c4 c2 4d df ed   (B̄=0 for ymm13, L=1)
example : encodeVaes aYHi (.declast true "d" "v" "m")
    = [0xc4, 0xc2, 0x4d, 0xdf, 0xed].map (BitVec.ofNat 8) := by native_decide

/-! ## 4. GFNI (`66 0F 38 CF` / `66 0F 3A CE` legacy, VEX forms) -/

-- gas: `gf2p8mulb xmm1,xmm2`  →  66 0f 38 cf ca
example : encodeGfni aLow (.mulb "d" "s")
    = [0x66, 0x0f, 0x38, 0xcf, 0xca].map (BitVec.ofNat 8) := by native_decide

-- gas: `gf2p8affineqb xmm1,xmm2,0x07`  →  66 0f 3a ce ca 07
example : encodeGfni aLow (.affineqb "d" "s" 0x07)
    = [0x66, 0x0f, 0x3a, 0xce, 0xca, 0x07].map (BitVec.ofNat 8) := by native_decide

-- gas: `vgf2p8mulb xmm1,xmm2,xmm3`  →  c4 e2 69 cf cb
example : encodeGfni a3 (.vmulb false "d" "v" "m")
    = [0xc4, 0xe2, 0x69, 0xcf, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vgf2p8mulb ymm1,ymm2,ymm3`  →  c4 e2 6d cf cb   (L=1)
example : encodeGfni aY3 (.vmulb true "d" "v" "m")
    = [0xc4, 0xe2, 0x6d, 0xcf, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vgf2p8affineqb xmm1,xmm2,xmm3,0x07`  →  c4 e3 e9 ce cb 07   (W=1)
example : encodeGfni a3 (.vaffineqb false "d" "v" "m" 0x07)
    = [0xc4, 0xe3, 0xe9, 0xce, 0xcb, 0x07].map (BitVec.ofNat 8) := by native_decide

-- gas: `vgf2p8affineqb ymm1,ymm2,ymm3,0x07`  →  c4 e3 ed ce cb 07   (W=1, L=1)
example : encodeGfni aY3 (.vaffineqb true "d" "v" "m" 0x07)
    = [0xc4, 0xe3, 0xed, 0xce, 0xcb, 0x07].map (BitVec.ofNat 8) := by native_decide

/-! ## 5. AVX2 VEX.256 packed-integer general set

`aX3` low XMM, `aY3` low YMM (defined above); `aYTop` exercises the high-register
2-byte→3-byte VEX fallback (`d↦%ymm13 v↦%ymm14 m↦%ymm15`). -/

/-- Low XMM 3-register allocation (= `a3`, re-aliased for clarity). -/
def aX3 : VAlloc := a3

/-- All-high YMM allocation forcing the 3-byte VEX form: `d↦%ymm13 v↦%ymm14
    m↦%ymm15`. -/
def aYTop : VAlloc := [("d", "%ymm13"), ("v", "%ymm14"), ("m", "%ymm15")]

-- gas: `vpmuludq xmm1,xmm2,xmm3`  →  c5 e9 f4 cb   (2-byte VEX, 0F map, low rm)
example : encodeAvx2 aX3 (.vpmuludq false "d" "v" "m")
    = [0xc5, 0xe9, 0xf4, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpmuludq ymm1,ymm2,ymm3`  →  c5 ed f4 cb
example : encodeAvx2 aY3 (.vpmuludq true "d" "v" "m")
    = [0xc5, 0xed, 0xf4, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddq ymm1,ymm2,ymm3`  →  c5 ed d4 cb
example : encodeAvx2 aY3 (.vpaddq true "d" "v" "m")
    = [0xc5, 0xed, 0xd4, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddd ymm1,ymm2,ymm3`  →  c5 ed fe cb
example : encodeAvx2 aY3 (.vpaddd true "d" "v" "m")
    = [0xc5, 0xed, 0xfe, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddw ymm1,ymm2,ymm3`  →  c5 ed fd cb
example : encodeAvx2 aY3 (.vpaddw true "d" "v" "m")
    = [0xc5, 0xed, 0xfd, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddb ymm1,ymm2,ymm3`  →  c5 ed fc cb
example : encodeAvx2 aY3 (.vpaddb true "d" "v" "m")
    = [0xc5, 0xed, 0xfc, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpsubq ymm1,ymm2,ymm3`  →  c5 ed fb cb
example : encodeAvx2 aY3 (.vpsubq true "d" "v" "m")
    = [0xc5, 0xed, 0xfb, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpsubd ymm1,ymm2,ymm3`  →  c5 ed fa cb
example : encodeAvx2 aY3 (.vpsubd true "d" "v" "m")
    = [0xc5, 0xed, 0xfa, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpsubw ymm1,ymm2,ymm3`  →  c5 ed f9 cb
example : encodeAvx2 aY3 (.vpsubw true "d" "v" "m")
    = [0xc5, 0xed, 0xf9, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpmullw ymm1,ymm2,ymm3`  →  c5 ed d5 cb
example : encodeAvx2 aY3 (.vpmullw true "d" "v" "m")
    = [0xc5, 0xed, 0xd5, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpmulhw ymm1,ymm2,ymm3`  →  c5 ed e5 cb
example : encodeAvx2 aY3 (.vpmulhw true "d" "v" "m")
    = [0xc5, 0xed, 0xe5, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpsubw ymm13,ymm14,ymm15`  →  c4 41 0d f9 ef   (high rm ⇒ 3-byte VEX)
example : encodeAvx2 aYTop (.vpsubw true "d" "v" "m")
    = [0xc4, 0x41, 0x0d, 0xf9, 0xef].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpmulhw ymm13,ymm14,ymm15`  →  c4 41 0d e5 ef   (high rm ⇒ 3-byte VEX)
example : encodeAvx2 aYTop (.vpmulhw true "d" "v" "m")
    = [0xc4, 0x41, 0x0d, 0xe5, 0xef].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpmulld ymm1,ymm2,ymm3`  →  c4 e2 6d 40 cb   (0F38 map ⇒ 3-byte VEX)
example : encodeAvx2 aY3 (.vpmulld true "d" "v" "m")
    = [0xc4, 0xe2, 0x6d, 0x40, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpshufb ymm1,ymm2,ymm3`  →  c4 e2 6d 00 cb   (0F38 map)
example : encodeAvx2 aY3 (.vpshufb true "d" "v" "m")
    = [0xc4, 0xe2, 0x6d, 0x00, 0xcb].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpermq ymm1,ymm2,0x1b`  →  c4 e3 fd 00 ca 1b   (0F3A, W=1, vvvv unused;
-- source is ymm2, so the ModRM.rm reads the `v↦%ymm2` allocation slot)
example : encodeAvx2 aY3 (.vpermq true "d" "v" 0x1b)
    = [0xc4, 0xe3, 0xfd, 0x00, 0xca, 0x1b].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpblendd ymm1,ymm2,ymm3,0xaa`  →  c4 e3 6d 02 cb aa   (0F3A)
example : encodeAvx2 aY3 (.vpblendd true "d" "v" "m" 0xaa)
    = [0xc4, 0xe3, 0x6d, 0x02, 0xcb, 0xaa].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddq ymm13,ymm14,ymm15`  →  c4 41 0d d4 ef   (high rm ⇒ 2→3-byte VEX)
example : encodeAvx2 aYTop (.vpaddq true "d" "v" "m")
    = [0xc4, 0x41, 0x0d, 0xd4, 0xef].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpshufb ymm5,ymm6,ymm13`  →  c4 c2 4d 00 ed   (0F38, high rm)
example : encodeAvx2 aYHi (.vpshufb true "d" "v" "m")
    = [0xc4, 0xc2, 0x4d, 0x00, 0xed].map (BitVec.ofNat 8) := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt
