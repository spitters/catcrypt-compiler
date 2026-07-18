/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# A verified byte encoder for the x86 crypto-extension instruction families

`ScalarEncoder.lean` (#438) byte-encodes the scalar GP-ALU `JInstr` set and
`Avx512Encoder.lean` the AVX-512 packed-integer EVEX subset. Neither covers the
**crypto-extension instruction families** that several benched primitives emit:

* **SHA-NI** — `SHA256RNDS2`/`SHA256MSG1`/`SHA256MSG2` (SHA-256 hash core),
* **PCLMUL** — `PCLMULQDQ`/`VPCLMULQDQ` (GHASH, FAEST GF(2^128) dot products),
* **VAES** — `VAESENC`/`VAESENCLAST`/`VAESDEC`/`VAESDECLAST` (AES-GCM / AEAD),
* **GFNI** — `GF2P8MULB`/`GF2P8AFFINEQB` (GF(2^8) multivariate / S-box),
* the **AVX2 VEX.256** packed-integer general set the SIMD primitives use
  (`VPMULUDQ`/`VPSHUFB`/`VPERMQ`/`VPBLENDD`/`VPADD*`/`VPSUB*`/`VPMULL*`).

This module is the third owned-backend byte encoder: it encodes each instruction
directly to its x86-64 machine bytes in Lean, field by field per the Intel SDM
(Vol. 2 opcode tables + the VEX/EVEX formats of §2), so the kernel body is emitted
as bytes by a function whose output we audit against the SDM and differentially
validate against `gas` (`CryptoExtValidation.lean`).

## The trust posture (gas-pinned tier)

Like `ScalarEncoder`, every output byte is determined by the legacy/VEX prefix
construction below, auditable against the SDM, and:

* **structurally** — `encode…_length` theorems pin the byte length of each shape
  unconditionally for all inputs (the well-formedness half);
* **differentially** — each encoder output is pinned (`CryptoExtValidation.lean`)
  to the exact bytes `gas` produces for the same mnemonic.

A *stronger* Sail-x86 decode round-trip (`decode (encode i) ≡ i`, as #444 did for
the GP-ALU forms) is **not possible** for these families' *byte encodings*: the
ACL2/Sail-x86 model has no SHA-NI / VAES / GFNI / PCLMUL decode tables (the same
ceiling #444 hit for MULX/ADCX/ADOX). The *byte encoders* here therefore stay at
the **gas-pinned validation tier**, which is the honest status for them.

The instruction *semantics* (value-level), by contrast, now do have a Sail-x86
anchor: `model/cryptoext_spec.sail` (#492) transcribes the AES-NI / PCLMUL / GFNI
operations from the Intel SDM + FIPS 197 and `SailX86Lean.lean` proves the owned
model reproduces them (`aesenc_eq_sail`, `clmul_eq_sail*`, `gf256_mul_eq_sail*`,
…). That covers the *meaning* of the instructions; this module covers their
*encoding*.

## Shared register / bit machinery

XMM/YMM register names `%xmmN`/`%ymmN` (0..15) resolve through a `VAlloc`
association list, mirroring `Avx512`'s `ZAlloc`/`zmmOf`. Bit 3 of a register
number routes to the (inverted) VEX `R̄`/`B̄`/`v̄v̄v̄v̄` extension fields, so all 16
XMM/YMM registers are addressable.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-! ## 1. Register-name → number, and bit helpers -/

/-- A register assignment: an association list name → `"%xmmN"` / `"%ymmN"`. -/
abbrev VAlloc := List (String × String)

/-- The `%xmmN` / `%ymmN` register a name is assigned. Unknown → `%xmm0`. -/
def vOf (alloc : VAlloc) (n : String) : String :=
  (alloc.lookup n).getD "%xmm0"

/-- The numeric index `N` of a `%xmmN` / `%ymmN` register name (0..15): drop the
    4-char `%xmm`/`%ymm` prefix and parse the rest. A malformed name reads as 0. -/
def vNum (r : String) : Nat := ((r.drop 4).toNat?).getD 0

/-- Bit `i` of `n` (0 or 1). -/
@[simp] def bit (n i : Nat) : Nat := (n >>> i) &&& 1

/-- Boolean-complement of a 0/1 value (the VEX inversion `R̄ = 1−R`). -/
@[simp] def cbit (b : Nat) : Nat := 1 - b

/-! ## 2. Shared prefix / ModRM byte builders

`REX` for the legacy-encoded forms (`0x40 | W<<3 | R<<2 | X<<1 | B`); a
register-direct `ModRM` (`mod=11`); and the two-byte and three-byte VEX prefixes. -/

/-- The `REX` prefix `0x40 | W<<3 | R<<2 | X<<1 | B`. -/
def rex (w r x b : Nat) : Nat :=
  64 + w * 8 + r * 4 + x * 2 + b

/-- A register-direct `ModRM` byte (`mod=11`): low 3 bits of `reg` and `rm`. -/
def modRMReg (reg rm : Nat) : Nat :=
  192 + ((reg &&& 7) * 8) + (rm &&& 7)

/-! ### Three-byte VEX prefix (`C4`)

```
 byte 0 : 0xC4
 byte 1 : R̄ X̄ B̄ m m m m m      mmmmm = opcode map (00001=0F, 00010=0F38, 00011=0F3A)
 byte 2 : W  v̄ v̄ v̄ v̄ L  p p     pp = mandatory prefix (00=none, 01=66, 10=F3, 11=F2)
```

`R̄`/`B̄` are the inverted bit-3 extensions of the ModRM.reg / ModRM.rm registers,
`X̄=1` (no SIB index for the reg-direct forms), `v̄v̄v̄v̄` the inverted `vvvv` (src1,
low 4 bits), `L` the vector length (0=128, 1=256), `W` the operand-width bit. -/

/-- VEX byte 1: `R̄ X̄ B̄ mmmmm`. `r`/`b` are the *logical* bit-3 extensions of
    ModRM.reg / ModRM.rm; `X̄=1` (no index). -/
def vex3p1 (r b mm : Nat) : Nat :=
  (cbit r) * 128 + 1 * 64 + (cbit b) * 32 + mm

/-- VEX byte 2: `W v̄v̄v̄v̄ L pp`. `vvvv` is src1 (low 4 bits), `l` the length bit,
    `pp` the mandatory prefix selector, `w` the W bit. -/
def vex3p2 (w vvvv l pp : Nat) : Nat :=
  w * 128 + ((15 - (vvvv &&& 15)) * 8) + l * 4 + pp

/-- A 3-byte-VEX three-register op (`dst = src1 ⟨op⟩ src2`), reg-direct ModRM with
    `reg`=dst, `vvvv`=src1, `rm`=src2. `mm` the map, `pp` the prefix, `w`/`l` the
    width/length bits. An optional trailing `imm8` (`some i`) is appended. -/
def encVex3 (mm pp w l op d v m : Nat) (imm : Option Nat) : List (BitVec 8) :=
  let core : List Nat :=
    [0xc4, vex3p1 (bit d 3) (bit m 3) mm, vex3p2 w v l pp, op, modRMReg d m]
  let bytes := match imm with | some i => core ++ [i &&& 0xff] | none => core
  bytes.map (BitVec.ofNat 8)

/-! ### Two-byte VEX prefix (`C5`)

`gas` uses the 2-byte form `C5 P1` whenever the 3-byte form's byte-1 would be
`R̄=1, X̄=1, B̄=1, mmmmm=00001` (the `0F` map with no register-extension on `rm`).
`P1` = `R̄ v̄v̄v̄v̄ L pp`. For the `0F38`/`0F3A` maps, or when `B̄=0` (high `rm`),
gas must fall back to the 3-byte form. -/

/-- VEX byte 1 of the 2-byte (`C5`) form: `R̄ v̄v̄v̄v̄ L pp`. -/
def vex2p1 (r vvvv l pp : Nat) : Nat :=
  (cbit r) * 128 + ((15 - (vvvv &&& 15)) * 8) + l * 4 + pp

/-- A 2-byte-VEX three-register op on the `0F` map (`reg`=dst, `vvvv`=src1,
    `rm`=src2). Requires `bit m 3 = 0` (else the 3-byte form is needed); the
    encoder caller selects the right form per `gas`'s rule. -/
def encVex2 (pp l op d v m : Nat) : List (BitVec 8) :=
  [0xc5, vex2p1 (bit d 3) v l pp, op, modRMReg d m].map (BitVec.ofNat 8)

/-- A three-register VEX op picking the shape `gas` does: the compact 2-byte
    (`C5`) form when the map is `0F` (`mm=00001`) *and* `W=0` *and* the `rm`
    register is low (`bit m 3 = 0`, so `B̄=1`); otherwise the 3-byte (`C4`) form.
    The `0F38`/`0F3A` maps and `W=1` always require the 3-byte form. -/
def encVexAuto (mm pp w l op d v m : Nat) : List (BitVec 8) :=
  if mm = 0b00001 ∧ w = 0 ∧ bit m 3 = 0 then
    encVex2 pp l op d v m
  else
    encVex3 mm pp w l op d v m none

/-! ## 3. SHA-NI (legacy `0F 38 cb/cc/cd`)

All three are legacy two-byte-map ops with a register-direct ModRM, `reg`=dst,
`rm`=src. `SHA256RNDS2` has an *implicit* third operand `XMM0` (the round
constants), which is not part of the encoding. A high `rm` register (xmm8..15)
takes a `REX.B` (`0x41`) prefix; a high `reg` would take `REX.R`. No `REX.W`
(`W=0`). The map prefix is `0F 38`, opcodes `CB`/`CC`/`CD`. -/

/-- A SHA-NI op (`0F 38 op`, `reg`=dst, `rm`=src). Emits an optional `REX` only
    when a high register (bit 3 set) needs the `R`/`B` extension — `gas` omits the
    REX byte entirely when both registers are low (xmm0..7). -/
def encShaNI (op d s : Nat) : List (BitVec 8) :=
  let r := bit d 3
  let b := bit s 3
  let rexByte : List Nat := if r = 0 ∧ b = 0 then [] else [rex 0 r 0 b]
  (rexByte ++ [0x0f, 0x38, op, modRMReg d s]).map (BitVec.ofNat 8)

/-- The three SHA-NI mnemonics. -/
inductive ShaInstr where
  | rnds2 (d s : String)   -- SHA256RNDS2 (implicit xmm0)
  | msg1  (d s : String)
  | msg2  (d s : String)
  deriving Repr, DecidableEq

/-- Encode one SHA-NI instruction to its machine bytes. Opcodes: `RNDS2 CB`,
    `MSG1 CC`, `MSG2 CD` (all on the `0F 38` map). -/
def encodeSha (alloc : VAlloc) : ShaInstr → List (BitVec 8)
  | .rnds2 d s => encShaNI 0xcb (vNum (vOf alloc d)) (vNum (vOf alloc s))
  | .msg1 d s  => encShaNI 0xcc (vNum (vOf alloc d)) (vNum (vOf alloc s))
  | .msg2 d s  => encShaNI 0xcd (vNum (vOf alloc d)) (vNum (vOf alloc s))

/-! ## 4. PCLMUL (carry-less multiply)

`PCLMULQDQ` legacy form is `66 0F 3A 44 /r ib`: a register-direct ModRM
(`reg`=dst, `rm`=src), an `imm8` lane selector, and an optional `REX.B` for a high
`rm`. `VPCLMULQDQ` is the VEX three-register form on the `0F3A` map (opcode `44`,
`pp=01`, `W=0`), with `l=0` for the 128-bit (`xmm`) and `l=1` for the 256-bit
(`ymm`) variants. -/

/-- `PCLMULQDQ xmm_d, xmm_s, imm8` (legacy `66 0F 3A 44 /r ib`). Emits `66`, an
    optional `REX` when a high register needs the `R`/`B` extension, then
    `0F 3A 44`, ModRM, `imm8`. -/
def encPclmul (d s imm : Nat) : List (BitVec 8) :=
  let r := bit d 3
  let b := bit s 3
  let rexByte : List Nat := if r = 0 ∧ b = 0 then [] else [rex 0 r 0 b]
  (0x66 :: rexByte ++ [0x0f, 0x3a, 0x44, modRMReg d s, imm &&& 0xff]).map (BitVec.ofNat 8)

/-- `VPCLMULQDQ dst, src1, src2, imm8` (VEX `0F3A 44`, `pp=01`, `W=0`). `l=0` for
    the `xmm` (128-bit) form, `l=1` for the `ymm` (256-bit) form. Always the
    3-byte VEX form (the `0F3A` map cannot use the 2-byte `C5` prefix). -/
def encVpclmul (l d v m imm : Nat) : List (BitVec 8) :=
  encVex3 0b00011 0b01 0 l 0x44 d v m (some imm)

/-! ## 5. VAES (vector AES round)

`VAESENC`/`VAESENCLAST`/`VAESDEC`/`VAESDECLAST` are VEX three-register forms on
the `0F38` map (opcodes `DC`/`DD`/`DE`/`DF`, `pp=01`, `W=0`), with `l=0`/`l=1`
selecting the 128/256-bit (`xmm`/`ymm`) widths. -/

/-- A VAES round op (`dst = AESround(src1, src2)`). `op` is the opcode (`DC`..`DF`),
    `l` the length bit. VEX `0F38`, `pp=01`, `W=0`. -/
def encVaes (op l d v m : Nat) : List (BitVec 8) :=
  encVex3 0b00010 0b01 0 l op d v m none

/-! ## 6. Instruction datatypes + dispatchers for PCLMUL / VAES

The `l` (length) field of the VEX forms is carried as a Boolean `wide` flag
(`true` = 256-bit `ymm`, `false` = 128-bit `xmm`) in the AST. -/

/-- PCLMUL instructions: the legacy `pclmulqdq` and the VEX `vpclmulqdq`. -/
inductive PclmulInstr where
  | pclmulqdq (d s : String) (imm : Nat)                  -- legacy 2-operand
  | vpclmulqdq (wide : Bool) (d v m : String) (imm : Nat) -- VEX 3-operand
  deriving Repr, DecidableEq

/-- Encode one PCLMUL instruction. -/
def encodePclmul (alloc : VAlloc) : PclmulInstr → List (BitVec 8)
  | .pclmulqdq d s imm => encPclmul (vNum (vOf alloc d)) (vNum (vOf alloc s)) imm
  | .vpclmulqdq wide d v m imm =>
      encVpclmul (if wide then 1 else 0)
        (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m)) imm

/-! ## 6b. GFNI (Galois-field affine / multiply over GF(2^8))

`GF2P8MULB` legacy form is `66 0F 38 CF /r`; `GF2P8AFFINEQB` legacy is
`66 0F 3A CE /r ib`. Their VEX forms `VGF2P8MULB` / `VGF2P8AFFINEQB` are the
three-register VEX shapes — `MULB` on `0F38 CF` with `W=0`, `AFFINEQB` on
`0F3A CE` with `W=1` (the 64-bit-element affine transform). -/

/-- `GF2P8MULB xmm_d, xmm_s` (legacy `66 0F 38 CF /r`), optional REX for a high
    register, register-direct ModRM (`reg`=dst, `rm`=src). -/
def encGf2p8mulb (d s : Nat) : List (BitVec 8) :=
  let r := bit d 3
  let b := bit s 3
  let rexByte : List Nat := if r = 0 ∧ b = 0 then [] else [rex 0 r 0 b]
  (0x66 :: rexByte ++ [0x0f, 0x38, 0xcf, modRMReg d s]).map (BitVec.ofNat 8)

/-- `GF2P8AFFINEQB xmm_d, xmm_s, imm8` (legacy `66 0F 3A CE /r ib`). -/
def encGf2p8affineqb (d s imm : Nat) : List (BitVec 8) :=
  let r := bit d 3
  let b := bit s 3
  let rexByte : List Nat := if r = 0 ∧ b = 0 then [] else [rex 0 r 0 b]
  (0x66 :: rexByte ++ [0x0f, 0x3a, 0xce, modRMReg d s, imm &&& 0xff]).map (BitVec.ofNat 8)

/-- `VGF2P8MULB dst, src1, src2` (VEX `0F38 CF`, `pp=01`, `W=0`). -/
def encVgf2p8mulb (l d v m : Nat) : List (BitVec 8) :=
  encVex3 0b00010 0b01 0 l 0xcf d v m none

/-- `VGF2P8AFFINEQB dst, src1, src2, imm8` (VEX `0F3A CE`, `pp=01`, `W=1`). -/
def encVgf2p8affineqb (l d v m imm : Nat) : List (BitVec 8) :=
  encVex3 0b00011 0b01 1 l 0xce d v m (some imm)

/-- VAES instructions, each on the `0F38` map. -/
inductive VaesInstr where
  | enc     (wide : Bool) (d v m : String)
  | enclast (wide : Bool) (d v m : String)
  | dec     (wide : Bool) (d v m : String)
  | declast (wide : Bool) (d v m : String)
  deriving Repr, DecidableEq

/-- Encode one VAES instruction. Opcodes: `enc DC`, `enclast DD`, `dec DE`,
    `declast DF`. -/
def encodeVaes (alloc : VAlloc) : VaesInstr → List (BitVec 8)
  | .enc wide d v m =>
      encVaes 0xdc (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .enclast wide d v m =>
      encVaes 0xdd (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .dec wide d v m =>
      encVaes 0xde (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .declast wide d v m =>
      encVaes 0xdf (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))

/-- GFNI instructions: legacy and VEX forms of `GF2P8MULB` / `GF2P8AFFINEQB`. -/
inductive GfniInstr where
  | mulb       (d s : String)                         -- legacy 66 0F 38 CF
  | affineqb   (d s : String) (imm : Nat)             -- legacy 66 0F 3A CE ib
  | vmulb      (wide : Bool) (d v m : String)         -- VEX 0F38 CF
  | vaffineqb  (wide : Bool) (d v m : String) (imm : Nat) -- VEX 0F3A CE ib, W=1
  deriving Repr, DecidableEq

/-- Encode one GFNI instruction. -/
def encodeGfni (alloc : VAlloc) : GfniInstr → List (BitVec 8)
  | .mulb d s => encGf2p8mulb (vNum (vOf alloc d)) (vNum (vOf alloc s))
  | .affineqb d s imm => encGf2p8affineqb (vNum (vOf alloc d)) (vNum (vOf alloc s)) imm
  | .vmulb wide d v m =>
      encVgf2p8mulb (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vaffineqb wide d v m imm =>
      encVgf2p8affineqb (if wide then 1 else 0)
        (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m)) imm

/-! ## 7. The AVX2 VEX.256 packed-integer general set

The SIMD primitives use a general AVX2 set: the `0F`-map three-register ALU ops
(`VPADD*`/`VPSUB*`/`VPMULUDQ`/`VPMULLW`) which `gas` emits with the compact 2-byte
VEX where possible; the `0F38`-map ops (`VPSHUFB`/`VPMULLD`); and the `0F3A`-map
immediate ops (`VPERMQ` — a 2-operand `dst, src, imm8` permute with `W=1` and an
unused `vvvv`; `VPBLENDD` — a 3-operand blend with an `imm8` mask).

Each `wide` flag selects `ymm` (`l=1`) vs `xmm` (`l=0`). All are `pp=01` (`66`). -/

/-- A `0F`-map three-register ALU op via the auto 2/3-byte VEX selector. -/
def encAvx2Alu (op l d v m : Nat) : List (BitVec 8) :=
  encVexAuto 0b00001 0b01 0 l op d v m

/-- A `0F38`-map three-register op (always 3-byte VEX): `VPSHUFB 00`, `VPMULLD 40`. -/
def encAvx2_0F38 (op l d v m : Nat) : List (BitVec 8) :=
  encVex3 0b00010 0b01 0 l op d v m none

/-- `VPERMQ dst, src, imm8` (VEX `0F3A 00`, `W=1`, `vvvv` unused = 0, then imm8). -/
def encVpermq (l d s imm : Nat) : List (BitVec 8) :=
  encVex3 0b00011 0b01 1 l 0x00 d 0 s (some imm)

/-- `VPBLENDD dst, src1, src2, imm8` (VEX `0F3A 02`, `W=0`, then imm8). -/
def encVpblendd (l d v m imm : Nat) : List (BitVec 8) :=
  encVex3 0b00011 0b01 0 l 0x02 d v m (some imm)

/-- The AVX2 VEX general-set instructions. `wide` = 256-bit (`ymm`). -/
inductive Avx2Instr where
  | vpaddq   (wide : Bool) (d v m : String)
  | vpaddd   (wide : Bool) (d v m : String)
  | vpaddw   (wide : Bool) (d v m : String)
  | vpaddb   (wide : Bool) (d v m : String)
  | vpsubq   (wide : Bool) (d v m : String)
  | vpsubd   (wide : Bool) (d v m : String)
  | vpsubw   (wide : Bool) (d v m : String)
  | vpmuludq (wide : Bool) (d v m : String)
  | vpmullw  (wide : Bool) (d v m : String)
  | vpmulhw  (wide : Bool) (d v m : String)
  | vpmulld  (wide : Bool) (d v m : String)
  | vpshufb  (wide : Bool) (d v m : String)
  | vpermq   (wide : Bool) (d s : String) (imm : Nat)
  | vpblendd (wide : Bool) (d v m : String) (imm : Nat)
  deriving Repr, DecidableEq

/-- Encode one AVX2 VEX instruction. Opcodes per the SDM: `VPADDQ D4`, `VPADDD FE`,
    `VPADDW FD`, `VPADDB FC`, `VPSUBQ FB`, `VPSUBD FA`, `VPSUBW F9`, `VPMULUDQ F4`,
    `VPMULLW D5`, `VPMULHW E5`, `VPMULLD (0F38) 40`, `VPSHUFB (0F38) 00`,
    `VPERMQ (0F3A) 00`, `VPBLENDD (0F3A) 02`. -/
def encodeAvx2 (alloc : VAlloc) : Avx2Instr → List (BitVec 8)
  | .vpaddq wide d v m   => encAvx2Alu 0xd4 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpaddd wide d v m   => encAvx2Alu 0xfe (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpaddw wide d v m   => encAvx2Alu 0xfd (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpaddb wide d v m   => encAvx2Alu 0xfc (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpsubq wide d v m   => encAvx2Alu 0xfb (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpsubd wide d v m   => encAvx2Alu 0xfa (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpsubw wide d v m   => encAvx2Alu 0xf9 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpmuludq wide d v m => encAvx2Alu 0xf4 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpmullw wide d v m  => encAvx2Alu 0xd5 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpmulhw wide d v m  => encAvx2Alu 0xe5 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpmulld wide d v m  => encAvx2_0F38 0x40 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpshufb wide d v m  => encAvx2_0F38 0x00 (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m))
  | .vpermq wide d s imm => encVpermq (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc s)) imm
  | .vpblendd wide d v m imm => encVpblendd (if wide then 1 else 0) (vNum (vOf alloc d)) (vNum (vOf alloc v)) (vNum (vOf alloc m)) imm

end CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-! ## Structural well-formedness — SHA-NI -/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-- A SHA-NI op encodes to 4 bytes (no REX) or 5 bytes (with REX), depending on
    whether either register is high. -/
theorem encShaNI_length (op d s : Nat) :
    (encShaNI op d s).length = (if bit d 3 = 0 ∧ bit s 3 = 0 then 4 else 5) := by
  unfold encShaNI
  by_cases h : bit d 3 = 0 ∧ bit s 3 = 0 <;>
    simp only [bit] at h <;> simp only [bit, h, if_false] <;> rfl

/-- A `VPCLMULQDQ` (VEX 3-byte) form always encodes to 6 bytes (C4 + 2 VEX + opcode
    + ModRM + imm8), independent of register choice or width. -/
theorem encVpclmul_length (l d v m imm : Nat) :
    (encVpclmul l d v m imm).length = 6 := by
  simp [encVpclmul, encVex3]

/-- A `VAES` (VEX 3-byte, no imm) form always encodes to 5 bytes. -/
theorem encVaes_length (op l d v m : Nat) :
    (encVaes op l d v m).length = 5 := by
  simp [encVaes, encVex3]

/-- A `0F38`-map AVX2 op (always 3-byte VEX, no imm) encodes to 5 bytes. -/
theorem encAvx2_0F38_length (op l d v m : Nat) :
    (encAvx2_0F38 op l d v m).length = 5 := by
  simp [encAvx2_0F38, encVex3]

/-- The auto 2/3-byte AVX2 ALU op encodes to 4 bytes (2-byte VEX form) or 5 bytes
    (3-byte VEX form), per the `gas` shape-selection rule. -/
theorem encAvx2Alu_length (op l d v m : Nat) :
    (encAvx2Alu op l d v m).length =
      (if (0b00001 : Nat) = 0b00001 ∧ (0 : Nat) = 0 ∧ bit m 3 = 0 then 4 else 5) := by
  unfold encAvx2Alu encVexAuto
  split <;> simp [encVex2, encVex3]

end CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt
