/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore

/-!
# Jasmin VIR dialect (spike)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A minimal `VIR.Dialect` whose `Op`/`Ty` model the word-level, register/stack,
two-address fragment of Jasmin that `RustEmitJazz` emits empirically. It moves
the optimizer onto a typed `Com` substrate, so that every backend (jasminc, Veir,
MLIR text) hangs off the shared `Com`.

It mirrors `CatCryptDialect.lean` exactly in structure: an `Op` tag inductive,
a `Dialect`, a `TyDenote`, a `DialectSignature`, and a total `DialectDenote`.
Kept deliberately minimal — no property structs (cf. `CatCryptOpProperties` /
`CatCryptOpInfo`), no control-flow regions.

## Types (`JasminTy`)

* `reg w`        — a `w`-bit register, `⟦·⟧ = BitVec w`
* `stackArr w n` — an `n`-element stack array of `w`-bit words,
                   `⟦·⟧ = Fin n → BitVec w`
* `inlineInt`    — a compile-time integer, `⟦·⟧ = Nat`
* `bool`         — a flag, `⟦·⟧ = Bool`

The reg-vs-stack and width distinctions that `RustEmitJazz` infers by hand
become *dialect types*, so they are checked rather than re-discovered.

## Ops (`JasminOp`)

* `regArith`           — two-address binary op on `reg w`
* `stackLoad` / `stackStore` — scalar-indexed element load / store on a stack
                         array (index is a `reg 64`, mirroring Jasmin's
                         `reg u64` array indices)
* `castW`              — width cast via `BitVec.zeroExtend` / truncate
* `extCall`            — external leaf, mirrors `CatCryptDialect.extCall`. The
                         16-bit stack-array leaves emitted by the lattice→jasmin
                         lowering get a real (data-oblivious) semantics via
                         `jasminExtSem`; every other leaf keeps the opaque default
* `callN`              — multi-result external call: a single op for a `k`-output
                         leaf call carrying its whole `retTys` list, lining up
                         1:1 onto a `func.call` lowering with `k` results

## Pure-only

Like `CatCryptDialect`, this dialect is restricted to VIR's pure denotation;
loads/stores are modelled functionally (no separate memory effect). The
`stackLoad` index is interpreted modulo `n` (via the `stackGet` / `stackSet`
helpers) so the denotation is total even for `n = 0` (empty array).

## Future work

A `Com jasminDialect → CatCrypt.Crypto.Jasmin.LowCT.JasminProg` lowering
(printed by `ppJasminProg`) is the next deliverable per phase (a) of the plan;
it is intentionally not attempted in this spike, whose core is the dialect plus
a `Com.denote` smoke test.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Types -/

/-- The Jasmin dialect's value-type alphabet. -/
inductive JasminTy where
  /-- A `w`-bit register. -/
  | reg (w : Nat)
  /-- An `n`-element stack array of `w`-bit words. -/
  | stackArr (w n : Nat)
  /-- A compile-time (inline) integer. -/
  | inlineInt
  /-- A boolean flag. -/
  | bool
  deriving DecidableEq

/-- Total denotation of `JasminTy` into Lean types. -/
@[reducible] instance : TyDenote JasminTy where
  denote
    | .reg w => BitVec w
    | .stackArr w n => Fin n → BitVec w
    | .inlineInt => Nat
    | .bool => Bool

/-! ## 2. Binary register-arithmetic operators -/

/-- The two-address binary operators on registers `regArith` supports.

    `shl`/`shr` are the **logical** left / right shifts (additive, 2026-05-25):
    they let the dialect express the ARX rotate `(x <<< n) ||| (x >>> (w-n))`
    needed by ChaCha20 and other shift-using ciphers. The shift *amount* is the
    `.toNat` of the second register operand (jasmin's `<<` / `>>` over words).
    Width truncation is handled by `BitVec`'s `<<<` / `>>>` (logical, keeps the
    operand width). All pre-existing arms (`add/sub/mul/and/or/xor`) are
    unchanged. -/
inductive JasminBinOp where
  | add
  | sub
  | mul
  | and
  | or
  | xor
  /-- Logical left shift by `b.toNat` (additive). -/
  | shl
  /-- Logical right shift by `b.toNat` (additive). -/
  | shr
  /-- BMI1 `andn`: `(¬a) ∧ b` in ONE op (no separate `NOT`). This is the
      first source complemented and AND-ed with the second, matching the
      x86 `ANDN dst, a, b` ⇒ `dst := (~a) & b`. It collapses the Keccak χ
      idiom `B[x] ^ ((¬B[x+1]) ∧ B[x+2])` from a `NOT;AND` pair to a single
      instruction. Denotation: `(~~~a) &&& b`. -/
  | andn
  deriving DecidableEq, Repr

/-- Apply a `JasminBinOp` at a fixed width. The `shl`/`shr` arms are the logical
    shifts by the `.toNat` of the second operand (additive; pre-existing arms
    unchanged). -/
def JasminBinOp.apply : JasminBinOp → {w : Nat} → BitVec w → BitVec w → BitVec w
  | .add, _, a, b => a + b
  | .sub, _, a, b => a - b
  | .mul, _, a, b => a * b
  | .and, _, a, b => a &&& b
  | .or,  _, a, b => a ||| b
  | .xor, _, a, b => a ^^^ b
  | .shl, _, a, b => a <<< b.toNat
  | .shr, _, a, b => a >>> b.toNat
  | .andn, _, a, b => (~~~a) &&& b

/-! ### AVX-512 ZMM packed-lane semantics (task #286)

A `reg 512` ZMM register holds **8 × u64** lanes. The packed AVX-512 ops
(`#VPADD_8u64`, `#VPSUB_8u64`, `#VPMULL_8u64`, `#VPSRL_8u64`, …) apply a
per-64-bit-lane scalar op with **no cross-lane carry / borrow**, unlike the
full-width `regArith _ 512` add (which is a single 512-bit ripple add). This is
the AVX-512 analogue of how the AVX2 `u256` register carries `#VPADD_4u64` /
`#VPADD_16u16` packed ops. The per-lane meaning is differentially validated
against `MpnAvx512Emit.denoteVPaddQ8` / `denoteVPsubQ8` (the functional AVX-512
model whose lane bridges go through `LaneMap.vmap₂_eq_scalar`). -/

/-- Read lane `k` (a 64-bit qword) of a 512-bit ZMM register, little-endian
    (lane 0 = low 64 bits). Mirrors `MpnAvx512Emit.lanesOf512`. -/
def zmmLane (v : BitVec 512) (k : Fin 8) : BitVec 64 :=
  BitVec.extractLsb' (64 * k.val) 64 v

/-- Assemble a `BitVec 512` ZMM register from 8 × u64 lanes (little-endian:
    lane 0 in the low 64 bits). Inverse of `zmmLane`. -/
def zmmOfLanes (f : Fin 8 → BitVec 64) : BitVec 512 :=
  (f 7) ++ (f 6) ++ (f 5) ++ (f 4) ++ (f 3) ++ (f 2) ++ (f 1) ++ (f 0)

/-- The 8×u64 packed-lane denotation of a `JasminBinOp` over two ZMM registers:
    apply `bop` at width 64 in each of the 8 lanes independently, then reassemble.
    This is the verified-dialect semantics of `#VPADD_8u64` (`.add`),
    `#VPSUB_8u64` (`.sub`), `#VPMULL_8u64` (`.mul`), `#VPSRL_8u64` (`.shr`), etc. -/
def zmmPackQ (bop : JasminBinOp) (a b : BitVec 512) : BitVec 512 :=
  zmmOfLanes (fun k => bop.apply (zmmLane a k) (zmmLane b k))

/-- Read lane `k` (a 32-bit dword) of a 512-bit ZMM register (16×u32 view). -/
def zmmLane32 (v : BitVec 512) (k : Fin 16) : BitVec 32 :=
  BitVec.extractLsb' (32 * k.val) 32 v

/-- Assemble a `BitVec 512` ZMM from 16 × u32 lanes (little-endian). Inverse of `zmmLane32`. -/
def zmmOfLanes32 (f : Fin 16 → BitVec 32) : BitVec 512 :=
  (f 15) ++ (f 14) ++ (f 13) ++ (f 12) ++ (f 11) ++ (f 10) ++ (f 9) ++ (f 8) ++
  (f 7) ++ (f 6) ++ (f 5) ++ (f 4) ++ (f 3) ++ (f 2) ++ (f 1) ++ (f 0)

/-- The 16×u32 packed-lane denotation of a `JasminBinOp` over two ZMM registers
    (`#VPADDD`/`#VPSUBD`/`#VPXORD`/`#VPANDD`/`#VPORD`). Dword analogue of `zmmPackQ`. -/
def zmmPackD (bop : JasminBinOp) (a b : BitVec 512) : BitVec 512 :=
  zmmOfLanes32 (fun k => bop.apply (zmmLane32 a k) (zmmLane32 b k))

/-- The 16×u32 packed right-rotate-by-immediate (`#VPRORD`; `#VPROLD m` = `zmmRorD (32-m)`).
    Mirrors `Avx512DwordModel.laneRorD = (a>>>n)|||(a<<<(32-n)) = BitVec.rotateRight a n`. -/
def zmmRorD (n : Nat) (a : BitVec 512) : BitVec 512 :=
  zmmOfLanes32 (fun k => (zmmLane32 a k).rotateRight n)

/-! ### Parametrized 128-bit SIMD ops (SIMD-dialect-unification, Batch 1)

The waist holds the semantics of the target `x86vector` machine ops as KAT-pinned
pure `BitVec` functions, copied verbatim from `X86Backend/Vec128Model.lean` (the
`W` suffix avoids a name clash with that model, which cannot be imported here —
`JasminDialect` imports only `VIR.Core`). The 128-bit ops are gathered under a
single inductive `SimdOp` so a *parametrized* `JasminOp.vsimd op` constructor
adds new SIMD ops WITHOUT cascading to every exhaustive `JasminOp` consumer:
uniform consumers match `| .vsimd _` once; only the per-op-behavior sites
(denote / mnemonic / emit / denote-spec) read the inner `SimdOp`.

The bodies are byte-identical to the model's `gf256MulByte`/`vByteOf`/
`vPackBytes`/`gf2p8mulb`/`vpshufb`, so the existing KATs that pin those
functions transfer onto the unified path. -/

/-- GF(2^8) multiply on one byte under the AES polynomial (`0x1b`), schoolbook
    shift-and-add. Copied verbatim from `Vec128Model.gf256MulByte`
    (= `AesBitslice.gfMul` = pqov `gf256_mul`). -/
def gf256MulByteW (a b : BitVec 8) : BitVec 8 :=
  Id.run do
    let mut r : BitVec 8 := 0
    let mut sh : BitVec 8 := a
    for i in [0:8] do
      let bitI := (b >>> (i : Nat)) &&& 1
      let mask := 0#8 - bitI
      r := r ^^^ (sh &&& mask)
      let msb := sh >>> 7
      let shifted := sh <<< 1
      sh := shifted ^^^ (msb * 0x1b#8)
    pure r

/-- The `k`-th byte (little-endian) of a `BitVec 128`. Copied from
    `Vec128Model.vByteOf`. -/
def vByteOfW (v : BitVec 128) (k : Fin 16) : BitVec 8 :=
  BitVec.extractLsb' (8 * k.val) 8 v

/-- Reassemble 16 `BitVec 8` lanes into a `BitVec 128` little-endian. Copied from
    `Vec128Model.vPackBytes`. -/
def vPackBytesW (bs : Fin 16 → BitVec 8) : BitVec 128 :=
  Fin.foldl 16 (init := (0 : BitVec 128))
    (fun acc k => acc ||| ((bs k).setWidth 128 <<< (8 * k.val)))

/-- `GF2P8MULB a, b`: byte-wise GF(2^8) multiply across all 16 lanes. Copied from
    `Vec128Model.gf2p8mulb`. -/
def gf2p8mulbW (a b : BitVec 128) : BitVec 128 :=
  vPackBytesW (fun k => gf256MulByteW (vByteOfW a k) (vByteOfW b k))

/-- `PSHUFB a, idx`: per-byte table lookup. Copied from `Vec128Model.vpshufb`.
    For each destination byte `i`, control byte `idx[i]` selects: if its top bit
    is set the result byte is `0`; otherwise it is source byte `a[idx[i] & 0x0F]`. -/
def vpshufbW (a idx : BitVec 128) : BitVec 128 :=
  vPackBytesW (fun i =>
    let c := vByteOfW idx i
    if (c &&& 0x80#8) ≠ 0 then 0#8
    else vByteOfW a ⟨(c &&& 0x0F#8).toNat % 16, Nat.mod_lt _ (by decide)⟩)

/-- One bit-step of the carry-less product. Copied verbatim from
    `Vec128Model.clmul64Step` (KAT-pinned). -/
def clmul64StepW (a : BitVec 64) (b : BitVec 128) (acc : BitVec 128) (i : Nat) : BitVec 128 :=
  let bitI : BitVec 128 := ((a >>> i) &&& 1).setWidth 128
  let mask : BitVec 128 := 0#128 - bitI
  acc ^^^ ((b <<< i) &&& mask)

/-- Carry-less product of two 64-bit halves (one `PCLMULQDQ` on selected halves),
    no modular reduction. Copied verbatim from `Vec128Model.clmul64`. -/
def clmul64W (a b : BitVec 64) : BitVec 128 :=
  let b128 : BitVec 128 := b.setWidth 128
  Fin.foldl 64 (init := (0 : BitVec 128)) (fun acc i => clmul64StepW a b128 acc i.val)

/-- The `imm8`-selected 64-bit half of a 128-bit XMM value. Copied verbatim from
    `Vec128Model.clmulHalf`. -/
def clmulHalfW (v : BitVec 128) (hi : Bool) : BitVec 64 :=
  if hi then (v >>> 64).setWidth 64 else v.setWidth 64

/-- `VPCLMULQDQ a, b, imm8`: carry-less product of the `imm8`-selected 64-bit
    halves of `a` and `b` (`imm8` bit 0 picks `a`'s half, bit 4 picks `b`'s).
    Copied verbatim from `Vec128Model.clmul128`. -/
def clmul128W (a b : BitVec 128) (imm : Nat) : BitVec 128 :=
  clmul64W (clmulHalfW a ((imm &&& 1) ≠ 0)) (clmulHalfW b ((imm &&& 0x10) ≠ 0))

/-- Parity (XOR-reduction) of a byte's 8 bits. Copied verbatim from
    `Vec128Model.byteParity`. -/
def byteParityW (b : BitVec 8) : BitVec 1 :=
  Fin.foldl 8 (init := (0 : BitVec 1)) (fun acc i => acc ^^^ ((b >>> i.val) &&& 1).setWidth 1)

/-- GF(2) affine transform on one byte. Copied verbatim from `Vec128Model.gfAffineByte`. -/
def gfAffineByteW (aRows : Fin 8 → BitVec 8) (imm x : BitVec 8) : BitVec 8 :=
  Fin.foldl 8 (init := (0 : BitVec 8)) (fun acc k =>
    let rowIdx : Fin 8 := ⟨7 - k.val, by omega⟩
    let obit : BitVec 1 := byteParityW (aRows rowIdx &&& x) ^^^ ((imm >>> k.val) &&& 1).setWidth 1
    acc ||| (obit.setWidth 8 <<< k.val))

/-- `GF2P8AFFINEQB a, A, imm`: byte-wise GF(2) affine transform across all 16 lanes.
    Copied verbatim from `Vec128Model.gf2p8affineqb`. -/
def gf2p8affineqbW (a A : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  vPackBytesW (fun k =>
    let q := k.val / 8
    let aRows : Fin 8 → BitVec 8 := fun i =>
      vByteOfW A ⟨q * 8 + i.val, by
        have hk : k.val < 16 := k.isLt
        have hi : i.val < 8 := i.isLt
        omega⟩
    gfAffineByteW aRows imm (vByteOfW a k))

/-- Packed per-lane binary op on a 128-bit (XMM) register: split into `128/laneW`
    lanes of width `laneW`, apply `bop` per lane (no cross-lane carry beyond the
    lane), reassemble. `VPADDD` = `packed .add 32`, `VPADDQ` = `packed .add 64`, etc.
    The 128-bit analogue of `zmmPackQ` (which is fixed 8×u64 at 512). Total: `laneW=0`
    gives `128/0 = 0` lanes → `0`. -/
def v128PackLanesW (laneW : Nat) (bop : JasminBinOp) (a b : BitVec 128) : BitVec 128 :=
  (List.range (128 / laneW)).foldl
    (fun acc k =>
      acc |||
        ((bop.apply (BitVec.extractLsb' (laneW * k) laneW a)
                    (BitVec.extractLsb' (laneW * k) laneW b)).setWidth 128 <<< (laneW * k)))
    0

/-- Variable per-lane shift on a 128-bit (XMM) register at lane width `laneW`
    (`VPSLLVD` = `.shl 32`, `VPSLLVQ` = `.shl 64`, `VPSRLVD` = `.shr 32`,
    `VPSRLVQ` = `.shr 64`): split `a` (data) and `b` (per-lane counts) into
    `128 / laneW` lanes of width `laneW`; result lane `i` is lane `i` of `a`
    shifted by the `.toNat` of lane `i` of `b`. Each lane uses its own count from
    `b`, unlike a uniform packed shift where every lane uses one count. `bop` is
    `.shl` (left) or `.shr` (right); the per-lane operation is `bop.apply` at width
    `laneW`. The per-lane fold mirrors `v128PackLanesW`. Total: `laneW = 0` gives
    `128 / 0 = 0` lanes → `0`. -/
def simdVarShiftW (bop : JasminBinOp) (laneW : Nat) (a b : BitVec 128) : BitVec 128 :=
  (List.range (128 / laneW)).foldl
    (fun acc k =>
      acc |||
        ((bop.apply (BitVec.extractLsb' (laneW * k) laneW a)
                    (BitVec.extractLsb' (laneW * k) laneW b)).setWidth 128 <<< (laneW * k)))
    0

/-- One lane of `VPMULHW`: packed SIGNED 16-bit HIGH multiply. Copied verbatim from
    `Vec128Model.laneMulHiS16` (KAT-pinned, ML-KEM NTT Montgomery). -/
def laneMulHiS16W (a b : BitVec 16) : BitVec 16 :=
  ((a.signExtend 32 * b.signExtend 32).sshiftRight 16).truncate 16

/-- `VPMULHW`: packed 8×i16 signed high-16 multiply across the 128-bit register. -/
def vpmulhw16W (a b : BitVec 128) : BitVec 128 :=
  (List.range 8).foldl
    (fun acc k =>
      acc ||| ((laneMulHiS16W (BitVec.extractLsb' (16 * k) 16 a)
                              (BitVec.extractLsb' (16 * k) 16 b)).setWidth 128 <<< (16 * k)))
    0

/-! ### AES round primitives (`VAESENC` / `VAESENCLAST` / `VAESKEYGENASSIST`)

The data effect of the AES-NI round instructions, **copied verbatim** (with a
`W` suffix) from `CatCrypt.Crypto.Jasmin.JasminOps` (`wAESENC`/`wAESENCLAST`/
`wAESKEYGENASSIST` and their helpers), which the bespoke `Vec128Model.vaesenc`
denote already calls — so the unified `SimdOp` arms are byte- and
semantics-identical to the bespoke crypto-IR they replace. Kept local + computable (no upward import
into the AES layer, which lives in a `noncomputable section`), matching the
`gf2p8mulbW`/`clmul128W` verbatim-copy waist above. The FIPS-197 S-box table is
the same as `JasminOps.sboxArray`. -/

/-- AES S-Box forward table (FIPS 197, Table 4). Identical to `JasminOps.sboxArray`. -/
def aesSboxArrayW : Array (BitVec 8) := #[
  0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
  0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
  0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
  0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
  0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
  0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
  0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
  0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
  0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
  0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
  0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
  0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
  0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
  0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
  0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
  0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16]

set_option maxRecDepth 2000 in
@[simp] theorem aesSboxArrayW_size : aesSboxArrayW.size = 256 := rfl

/-- AES S-Box: SubBytes on a single byte. Identical to `JasminOps.aesSBox`. -/
def aesSBoxW (b : BitVec 8) : BitVec 8 :=
  aesSboxArrayW[b.toNat]'(aesSboxArrayW_size ▸ BitVec.isLt b)

/-- Extract byte `i` from a 128-bit state (little-endian). = `JasminOps.getByte128`. -/
def getByte128W (state : BitVec 128) (i : Nat) : BitVec 8 :=
  (state >>> (i * 8)).truncate 8

/-- Set byte `i` in a 128-bit state. = `JasminOps.setByte128`. -/
def setByte128W (state : BitVec 128) (i : Nat) (b : BitVec 8) : BitVec 128 :=
  let mask := ~~~((0xFF : BitVec 128) <<< (i * 8))
  (state &&& mask) ||| ((b.zeroExtend 128) <<< (i * 8))

/-- SubBytes: apply S-Box to each byte. = `JasminOps.aesSubBytes`. -/
def aesSubBytesW (state : BitVec 128) : BitVec 128 :=
  (List.range 16).foldl (fun s i => setByte128W s i (aesSBoxW (getByte128W state i))) 0

/-- Extract 32-bit column `j` (little-endian). = `JasminOps.getCol128`. -/
def getCol128W (state : BitVec 128) (j : Nat) : BitVec 32 :=
  (state >>> (j * 32)).truncate 32

/-- Set 32-bit column `j`. = `JasminOps.setCol128`. -/
def setCol128W (state : BitVec 128) (j : Nat) (col : BitVec 32) : BitVec 128 :=
  let mask := ~~~((0xFFFFFFFF : BitVec 128) <<< (j * 32))
  (state &&& mask) ||| ((col.zeroExtend 128) <<< (j * 32))

/-- ShiftRows (column-major). = `JasminOps.aesShiftRows`. -/
def aesShiftRowsW (state : BitVec 128) : BitVec 128 :=
  let get (row col : Nat) := getByte128W state (col * 4 + row)
  let set' (s : BitVec 128) (row col : Nat) (b : BitVec 8) := setByte128W s (col * 4 + row) b
  let s := (0 : BitVec 128)
  let s := (List.range 4).foldl (fun s col => set' s 0 col (get 0 col)) s
  let s := (List.range 4).foldl (fun s col => set' s 1 col (get 1 ((col + 1) % 4))) s
  let s := (List.range 4).foldl (fun s col => set' s 2 col (get 2 ((col + 2) % 4))) s
  (List.range 4).foldl (fun s col => set' s 3 col (get 3 ((col + 3) % 4))) s

/-- Multiply by x (= 2) in GF(2^8), poly `x^8+x^4+x^3+x+1`. = `JasminOps.gf256Xtime`. -/
def gf256XtimeW (b : BitVec 8) : BitVec 8 :=
  let shifted := b <<< 1
  if b &&& 0x80 != 0 then shifted ^^^ 0x1B else shifted

/-- Multiply two bytes in GF(2^8). = `JasminOps.gf256Mul`. -/
def gf256MulW (a b : BitVec 8) : BitVec 8 :=
  let b0 := if b &&& 0x01 != 0 then a else 0
  let b1 := if b &&& 0x02 != 0 then gf256XtimeW a else 0
  let b2 := if b &&& 0x04 != 0 then gf256XtimeW (gf256XtimeW a) else 0
  let b3 := if b &&& 0x08 != 0 then gf256XtimeW (gf256XtimeW (gf256XtimeW a)) else 0
  b0 ^^^ b1 ^^^ b2 ^^^ b3

/-- MixColumns (MDS matrix over GF(2^8)). = `JasminOps.aesMixColumns`. -/
def aesMixColumnsW (state : BitVec 128) : BitVec 128 :=
  (List.range 4).foldl (fun result j =>
    let b0 := getByte128W state (j * 4 + 0)
    let b1 := getByte128W state (j * 4 + 1)
    let b2 := getByte128W state (j * 4 + 2)
    let b3 := getByte128W state (j * 4 + 3)
    let r0 := gf256MulW b0 2 ^^^ gf256MulW b1 3 ^^^ b2 ^^^ b3
    let r1 := b0 ^^^ gf256MulW b1 2 ^^^ gf256MulW b2 3 ^^^ b3
    let r2 := b0 ^^^ b1 ^^^ gf256MulW b2 2 ^^^ gf256MulW b3 3
    let r3 := gf256MulW b0 3 ^^^ b1 ^^^ b2 ^^^ gf256MulW b3 2
    let result := setByte128W result (j * 4 + 0) r0
    let result := setByte128W result (j * 4 + 1) r1
    let result := setByte128W result (j * 4 + 2) r2
    setByte128W result (j * 4 + 3) r3) 0

/-- RotWord: rotate a 32-bit word left by one byte. = `JasminOps.rotWord`. -/
def rotWordW (w : BitVec 32) : BitVec 32 := (w <<< 8) ||| (w >>> 24)

/-- SubWord: apply the S-Box to each byte of a 32-bit word. = `JasminOps.subWord`. -/
def subWordW (w : BitVec 32) : BitVec 32 :=
  let b0 := aesSBoxW ((w >>> 0).truncate 8)
  let b1 := aesSBoxW ((w >>> 8).truncate 8)
  let b2 := aesSBoxW ((w >>> 16).truncate 8)
  let b3 := aesSBoxW ((w >>> 24).truncate 8)
  (b3.zeroExtend 32 <<< 24) ||| (b2.zeroExtend 32 <<< 16) |||
  (b1.zeroExtend 32 <<< 8)  ||| b0.zeroExtend 32

/-- `VAESENC state, key = MixColumns(ShiftRows(SubBytes(state))) ⊕ key`.
    = `JasminOps.wAESENC` (= bespoke `Vec128Model.vaesenc`). -/
def wAESENCW (state key : BitVec 128) : BitVec 128 :=
  aesMixColumnsW (aesShiftRowsW (aesSubBytesW state)) ^^^ key

/-- `VAESENCLAST state, key = ShiftRows(SubBytes(state)) ⊕ key` (no MixColumns).
    = `JasminOps.wAESENCLAST` (= bespoke `Vec128Model.vaesenclast`). -/
def wAESENCLASTW (state key : BitVec 128) : BitVec 128 :=
  aesShiftRowsW (aesSubBytesW state) ^^^ key

/-- `VAESKEYGENASSIST src, rcon`: SubWord/RotWord of the odd columns ⊕ Rcon.
    = `JasminOps.wAESKEYGENASSIST` (= bespoke `Vec128Model.vaeskeygen`). -/
def wAESKEYGENASSISTW (src : BitVec 128) (rcon : BitVec 8) : BitVec 128 :=
  let w1 := getCol128W src 1
  let w3 := getCol128W src 3
  let x1 := subWordW w1
  let x3 := subWordW w3
  let r3 := rotWordW x3 ^^^ (rcon.zeroExtend 32)
  setCol128W (setCol128W (setCol128W (setCol128W 0 0 x1) 1 r3) 2 x1) 3 r3

/-- `VPSHUFD src, imm8`: per-128-bit-lane dword shuffle. Destination dword `i`
    is source dword `((imm >>> (2*i)) &&& 3)`. Copied verbatim (with a `W` suffix
    and a `Nat` immediate) from `JasminOps.wVPSHUFD` (= bespoke
    `Vec128Model.vpshufd`) — the key-schedule `VPSHUFD $0xFF` broadcast the
    Owf128/AesNiLeaf/PrgLambda kernels emit. -/
def wVPSHUFDW (src : BitVec 128) (imm : Nat) : BitVec 128 :=
  let sel (i : Nat) := (imm >>> (i * 2)) &&& 3
  let d0 := getCol128W src (sel 0)
  let d1 := getCol128W src (sel 1)
  let d2 := getCol128W src (sel 2)
  let d3 := getCol128W src (sel 3)
  setCol128W (setCol128W (setCol128W (setCol128W 0 0 d0) 1 d1) 2 d2) 3 d3

/-- The parametrized 128-bit SIMD machine-op alphabet (target `x86vector`).
    `JasminOp.vsimd` is parametrized by this so adding a SIMD op never cascades
    to the uniform `JasminOp` consumers. -/
inductive SimdOp where
  /-- `VGF2P8MULB`: byte-wise GF(2^8) multiply across all 16 lanes. -/
  | gf2p8mulb
  /-- `VPSHUFB`: per-byte table lookup / shuffle. -/
  | vpshufb
  /-- `VPCLMULQDQ a, b, imm8`: carry-less product of the `imm8`-selected 64-bit
      halves (GHASH / AES-GCM). The `imm8` selector is baked into the op. -/
  | clmul (imm : Nat)
  /-- `GF2P8AFFINEQB a, A, imm8`: byte-wise GF(2) affine transform (AES SubBytes /
      bit-matrix maps). The `imm8` constant is baked into the op. -/
  | affineqb (imm : BitVec 8)
  /-- A carry-free 128-bit bitwise op (`VPAND`/`VPOR`/`VPXOR`): `bop.apply` at the
      whole 128-bit width. Sound ONLY for `and`/`or`/`xor` (no cross-lane carry, so
      whole-register = lane-wise at any lane width). Packed ARITHMETIC (add/sub at a
      lane width) is the `packed` op below. -/
  | bitwise (bop : JasminBinOp)
  /-- Packed per-lane binop on a 128-bit register at lane width `laneW`
      (`VPADDD` = `packed .add 32`, `VPADDQ` = `packed .add 64`). Denote = `v128PackLanesW`.
      Unblocks the dword-lane kernels (ChaCha-4way etc.). -/
  | packed (bop : JasminBinOp) (laneW : Nat)
  /-- Variable per-lane shift on a 128-bit register at lane width `laneW`
      (`VPSLLVD` = `varShift .shl 32`, `VPSLLVQ` = `varShift .shl 64`,
      `VPSRLVD` = `varShift .shr 32`, `VPSRLVQ` = `varShift .shr 64`). Each lane of
      the first operand is shifted by its own count taken from the corresponding
      lane of the second operand, unlike the uniform `packed` shift. `bop` is
      `.shl` / `.shr`. Denote = `simdVarShiftW`. -/
  | varShift (bop : JasminBinOp) (laneW : Nat)
  /-- `VPMULHW`: packed 8×i16 SIGNED high-16 multiply (ML-KEM NTT Montgomery).
      Distinct from `packed .mul 16` (which is the unsigned LOW product = VPMULLW). -/
  | mulhi16
  /-- `VAESENC state, rk`: one AES round `MixColumns ∘ ShiftRows ∘ SubBytes`
      then XOR the round key (`AesNi` FAEST/AES kernels). Binary: state, rk.
      Denote = `Jasmin.wAESENC` (the bespoke `Vec128Model.vaesenc` semantics). -/
  | vaesenc
  /-- `VAESENCLAST state, rk`: last AES round `ShiftRows ∘ SubBytes` then XOR the
      round key (no MixColumns). Binary: state, rk. Denote = `Jasmin.wAESENCLAST`. -/
  | vaesenclast
  /-- `VAESKEYGENASSIST src, imm8`: key-schedule assist (RotWord/SubWord + Rcon).
      UNARY in the register operand; the `rcon` byte is the baked `imm8` (like
      `clmul`/`affineqb`). Denote = `Jasmin.wAESKEYGENASSIST`. -/
  | vaeskeygen (rcon : BitVec 8)
  /-- `VPSHUFD src, imm8`: per-128-bit-lane dword shuffle (dst dword `i` =
      src dword `((imm >>> 2*i) &&& 3)`). UNARY in the register operand; the
      `imm8` control byte is the baked `Nat` immediate (like `clmul`/`vaeskeygen`).
      Denote = `wVPSHUFDW` (= bespoke `Vec128Model.vpshufd`). The key-schedule
      `VPSHUFD $0xFF` broadcast (Owf128/AesNiLeaf/PrgLambda). -/
  | vpshufd (imm : Nat)
  deriving DecidableEq, Repr

/-- Argument types of a `SimdOp`. -/
def SimdOp.argTys : SimdOp → List JasminTy
  | .gf2p8mulb => [.reg 128, .reg 128]
  | .vpshufb => [.reg 128, .reg 128]
  | .clmul _ => [.reg 128, .reg 128]
  | .affineqb _ => [.reg 128, .reg 128]
  | .bitwise _ => [.reg 128, .reg 128]
  | .packed _ _ => [.reg 128, .reg 128]
  | .varShift _ _ => [.reg 128, .reg 128]
  | .mulhi16 => [.reg 128, .reg 128]
  | .vaesenc => [.reg 128, .reg 128]
  | .vaesenclast => [.reg 128, .reg 128]
  | .vaeskeygen _ => [.reg 128]
  | .vpshufd _ => [.reg 128]

/-- Result type of a `SimdOp`. -/
def SimdOp.retTy : SimdOp → JasminTy
  | .gf2p8mulb => .reg 128
  | .vpshufb => .reg 128
  | .clmul _ => .reg 128
  | .affineqb _ => .reg 128
  | .bitwise _ => .reg 128
  | .packed _ _ => .reg 128
  | .varShift _ _ => .reg 128
  | .mulhi16 => .reg 128
  | .vaesenc => .reg 128
  | .vaesenclast => .reg 128
  | .vaeskeygen _ => .reg 128
  | .vpshufd _ => .reg 128

/-- The jasmin/x86 mnemonic of a `SimdOp` (for asm emit). -/
def SimdOp.mnemonic : SimdOp → String
  | .gf2p8mulb => "VGF2P8MULB"
  | .vpshufb => "VPSHUFB"
  | .clmul _ => "VPCLMULQDQ"
  | .affineqb _ => "VGF2P8AFFINEQB"
  | .bitwise .and => "VPAND"
  | .bitwise .or => "VPOR"
  | .bitwise .xor => "VPXOR"
  | .bitwise _ => "VPBITWISE"
  | .packed .add 32 => "VPADDD"
  | .packed .add 64 => "VPADDQ"
  | .packed .sub 32 => "VPSUBD"
  | .packed .sub 64 => "VPSUBQ"
  | .packed .mul 16 => "VPMULLW"
  | .packed .add 16 => "VPADDW"
  | .packed .sub 16 => "VPSUBW"
  | .packed .shl 32 => "VPSLLD"
  | .packed .shr 32 => "VPSRLD"
  | .packed _ _ => "VPPACKED"
  | .varShift .shl 32 => "VPSLLVD"
  | .varShift .shl 64 => "VPSLLVQ"
  | .varShift .shr 32 => "VPSRLVD"
  | .varShift .shr 64 => "VPSRLVQ"
  | .varShift _ _ => "VPVARSHIFT"
  | .mulhi16 => "VPMULHW"
  | .vaesenc => "VAESENC"
  | .vaesenclast => "VAESENCLAST"
  | .vaeskeygen _ => "VAESKEYGENASSIST"
  | .vpshufd _ => "VPSHUFD"

/-- The two-input denotation of a `SimdOp`, dispatching to the KAT-pinned waist
    functions. Most arms are `[reg 128, reg 128] → reg 128`; `vaeskeygen` is unary
    (`[reg 128]`) and ignores the second operand (the YmmOp mixed-arity pattern). -/
def SimdOp.denote : SimdOp → BitVec 128 → BitVec 128 → BitVec 128
  | .gf2p8mulb => gf2p8mulbW
  | .vpshufb => vpshufbW
  | .clmul imm => fun a b => clmul128W a b imm
  | .affineqb imm => fun a A => gf2p8affineqbW a A imm
  | .bitwise bop => fun a b => bop.apply a b
  | .packed bop laneW => fun a b => v128PackLanesW laneW bop a b
  | .varShift bop laneW => fun a b => simdVarShiftW bop laneW a b
  | .mulhi16 => vpmulhw16W
  -- AES round ops: denote = the verbatim-copied bespoke `Vec128Model.vaesenc`
  -- semantics (= `Jasmin.wAESENC` etc.), so kernels migrate semantics-identically.
  -- `vaeskeygen` is unary in the register operand (`rcon` is the baked `imm8`); the
  -- second operand is ignored (the YmmOp mixed-arity pattern).
  | .vaesenc => fun state rk => wAESENCW state rk
  | .vaesenclast => fun state rk => wAESENCLASTW state rk
  | .vaeskeygen rcon => fun src _ => wAESKEYGENASSISTW src rcon
  -- `vpshufd` is unary (`imm8` baked); the second operand is ignored.
  | .vpshufd imm => fun src _ => wVPSHUFDW src imm

/-! ### Widening multiply + carry-chain primitives (task #477)

The carry-FREE `JasminBinOp` alphabet (`add/sub/mul/and/or/xor/shl/shr`) cannot
express a multi-limb Montgomery / pairing-field multiply: that idiom needs the
**BMI2/ADX trio** `MULX` (64×64→128, two outputs) + the two **independent
carry chains** `ADCX` (CF) / `ADOX` (OF). #474 was blocked on exactly this.

The pure (flag-free, state-free) BitVec functions below are the *data* effect of
those instructions, **ported byte-for-byte from the owned x86 model**
(`X86Backend/Model.lean`, commit `25f61fe8`): `mulHiW` mirrors `Model.mulHi`
(= Jasmin `wumul`'s high word), and `addCarryWord` / `carryOutBit` mirror the
`+ src + (if c then 1 else 0)` data result and the `addCarry` carry predicate of
`Model.step`'s `.adcx`/`.adox` arms.

A `Com` op is single-output (`DialectSignature.ret` is one `JasminTy`), so each
two-output / carry-producing x86 instruction is modelled by a small family of
single-output ops whose denotations are these functions:

* `MULX (hi, lo) = a * b` ↦ the pair `mulHi a b` (`mulhi` arm) + the existing
  low word `a * b` (`regArith mul`);
* `ADCX/ADOX dst := dst + src + carry` ↦ `addCarryWord` (data, `addCarryLo`
  arm) + `carryOutBit` (the propagated carry, `addCarryHi` arm). The carry-in
  and carry-out are a 1-bit register (`reg 1`), so a multi-limb chain is just a
  data-flow thread of `reg 1` values — no hidden flag state, faithful to the two
  independent CF/OF accumulators (the *chain* an `ADCX`-only or `ADOX`-only
  sequence realises). -/

/-- High word of the full unsigned product `a * b` — the `hi` output of `MULX`.
    Identical to `X86Backend.Model.mulHi`: `(a.toNat * b.toNat) / 2 ^ w`. -/
def mulHiW {w : Nat} (a b : BitVec w) : BitVec w :=
  BitVec.ofNat w (a.toNat * b.toNat / 2 ^ w)

/-- The data result of one carry-chain add `dst + src + carry-in` at width `w`
    (`carry-in` a 1-bit register, `0`/`1`). Identical to the `dst + src.eval +
    (if c then 1 else 0)` written by `X86Backend.Model.step`'s `.adcx`/`.adox`
    arms (here the carry-in is the explicit `cin` operand rather than `CF`/`OF`). -/
def addCarryWord {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec w :=
  a + b + BitVec.ofNat w cin.toNat

/-- The carry-out bit of one carry-chain add `a + b + carry-in` at width `w`:
    `1` iff the unbounded sum reached `2 ^ w` (it wrapped). Identical to
    `X86Backend.Model.addCarry a b (cin = 1)`, packaged as a `reg 1` so it threads
    into the next limb's `addCarryWord` / `carryOutBit` as the carry-in. -/
def carryOutBit {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec 1 :=
  if a.toNat + b.toNat + cin.toNat ≥ 2 ^ w then 1 else 0

/-- The data result of one borrow-chain subtract `dst - src - borrow-in` at width
    `w` (`borrow-in` a 1-bit register, `0`/`1`). The dual of `addCarryWord`;
    identical mod `2 ^ w` to `X86Backend`'s `sub_borrow a b bin.toNat`
    (`= BitVec.ofInt w (a.toNat - b.toNat - bin)`), the word `x86_SBB` writes. -/
def subBorrowWord {w : Nat} (a b : BitVec w) (bin : BitVec 1) : BitVec w :=
  a - b - BitVec.ofNat w bin.toNat

/-- The borrow-out bit of one borrow-chain subtract `a - b - borrow-in` at width
    `w`: `1` iff the unbounded difference went negative (`a < b + bin`). The dual
    of `carryOutBit`, packaged as a `reg 1` so it threads into the next limb's
    `subBorrowWord` / `borrowOutBit` as the borrow-in. Identical to the borrow bit
    `x86_SBB` records in `CF`. -/
def borrowOutBit {w : Nat} (a b : BitVec w) (bin : BitVec 1) : BitVec 1 :=
  if a.toNat < b.toNat + bin.toNat then 1 else 0

/-! ### Constant-time SELECT / cmov (task #594, E2)

A branch-free conditional move: `selectW cond a b = if cond = 1 then a else b`,
with the condition a 1-bit register (`reg 1`, the same `0`/`1` convention as the
carry words `carryOutBit` threads). It is the data effect of an x86 `CMOVcc`
(conditional move) or the branchless mask idiom
`(a & mask) | (b & ~mask)` with `mask = 0 - cond` — both compute the same value
with **no secret-dependent branch**, so the SELECT op is the constant-time
primitive the front emits for the canonical conditional-subtract, the `cswap` of
a Montgomery / X25519 ladder, and a rejection sampler's conditional core. The
1-bit condition threads through the register file like any other word (no hidden
flag state). -/

/-- Constant-time select: `if cond = 1 then a else b`, the data effect of a
    `CMOVcc` / branchless mask-select. The condition is a 1-bit register (`reg 1`,
    `0`/`1`); both `a` and `b` are always evaluated, so there is no
    secret-dependent branch. -/
def selectW {w : Nat} (cond : BitVec 1) (a b : BitVec w) : BitVec w :=
  if cond = 1#1 then a else b

/-! ### Native right-rotate (task #497)

`rorImm` denotes `BitVec.rotateRight`, the **same** value the emit path currently
spells as the three-op idiom `(src >>> n) ||| (src <<< (w - n))` (`emitRotr`'s
`shr; shl; or`). The lemma below proves the rotate-insn-selection is semantics
preserving: for an in-range amount `0 < n < w` (every SHA-512 Σ/σ and Keccak ρ
rotate is in range), `rotateRight n` equals the shift-or form **bit-for-bit**.
It is the `BitVec` law `BitVec.rotateRight_def` specialised to `n % w = n`. -/

/-- **Rotate insn-selection soundness.** For an in-range amount `0 < n < w` (so
    `n % w = n`), the native rotate `src.rotateRight n` equals the shift-or idiom
    `(src >>> n) ||| (src <<< (w - n))` the emit path currently produces. This is
    the `BitVec`-algebra fact that licenses collapsing the `shr; shl; or` triple
    to the single `rorImm` op without changing the denotation. -/
theorem rorImm_denote_eq_shiftOr {w : Nat} (n : Nat) (hn : n < w) (src : BitVec w) :
    src.rotateRight n = (src >>> n) ||| (src <<< (w - n)) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn]

/-! ## 3. Op tags -/

/-- Operation tags for the Jasmin dialect. Each models a construct
    `RustEmitJazz` emits, but as a typed op with a denotation. -/
inductive JasminOp where
  /-- Two-address binary op on `reg w`. -/
  | regArith (op : JasminBinOp) (w : Nat)
  /-- Scalar-indexed element load from a stack array. -/
  | stackLoad (w n : Nat)
  /-- Scalar-indexed element store into a stack array (functional update). -/
  | stackStore (w n : Nat)
  /-- Width cast `reg w → reg w'` via zero-extend / truncate. -/
  | castW (w w' : Nat)
  /-- Opaque external leaf (e.g. an intrinsic / inline asm call). Signature
      is given by the `argTys` / `retTy` fields. Mirrors
      `CatCryptDialect.extCall`. -/
  | extCall (name : String) (argTys : List JasminTy) (retTy : JasminTy)
  /-- Nullary compile-time constant `n : Nat` materialised as a `reg w` value
      (= `BitVec.ofNat w n`). Mirrors `CryptoSSA.CExpr.bvConst` and lowers
      one-to-one to jasmin's `Cassgn (Lvar dst) AT_none (sword w) (Pconst n)`
      shape. Added 2026-05-28 to close the `RFor`-loop-counter gap (#203):
      `CryptoSSA.loopRFor` emits `letBind (bvConst i)` per iteration, and
      this arm is the matching `Com[jasminDialect]` image used by
      `CryptoToJasminCom.toJExpr`. -/
  | regConst (w : Nat) (n : Nat)
  /-- AVX-512 ZMM packed 8×u64 lane op (task #286): two `reg 512` operands,
      one `reg 512` result, the per-64-bit-lane `bop` with no cross-lane
      carry. The verified-chain image of `#VPADD_8u64` / `#VPSUB_8u64` /
      `#VPMULL_8u64` / `#VPSRL_8u64` (`bop = .add/.sub/.mul/.shr`). -/
  | vpackZMM (bop : JasminBinOp)
  /-- AVX-512 ZMM packed 16×u32 lane op (dword): `#VPADDD`/`#VPSUBD`/`#VPXORD`/
      `#VPANDD`/`#VPORD` (`bop`). Dword analogue of `vpackZMM`; SHA-256/ChaCha20 ride it. -/
  | vpackZMMd (bop : JasminBinOp)
  /-- AVX-512 ZMM packed 16×u32 rotate-right by immediate `n` (`#VPRORD`;
      `#VPROLD m` = `vprordZMM (32-m)`). The SHA-256/ChaCha20 dword rotate. -/
  | vprordZMM (n : Nat)
  /-- `VPSLLDQ`: whole 128-bit register left byte-shift by `n` bytes (`src <<< n*8`). -/
  | vpslldq (n : Nat)
  /-- `VPSRLDQ`: whole 128-bit register right byte-shift by `n` bytes (`src >>> n*8`). -/
  | vpsrldq (n : Nat)
  /-- Parametrized 128-bit SIMD machine op (SIMD-dialect-unification, Batch 1):
      two `reg 128` operands, one `reg 128` result, dispatched by the inner
      `SimdOp`. Adding a SIMD op extends `SimdOp` (not `JasminOp`), so uniform
      `JasminOp` consumers match `| .vsimd _` once and never change. -/
  | vsimd (op : SimdOp)
  /-- High word of the widening multiply `a * b` (the `hi` output of `MULX`):
      two `reg w` operands, one `reg w` result (`mulHiW`). The low word is the
      existing `regArith .mul w`; together they are MULX's `(hi, lo)`. (#477) -/
  | mulhi (w : Nat)
  /-- Carry-chain add **data** word `a + b + cin` (the data effect of `ADCX`/
      `ADOX`): `[reg w, reg w, reg 1] → reg w` (`addCarryWord`). (#477) -/
  | addCarryLo (w : Nat)
  /-- Carry-chain add **carry-out** bit of `a + b + cin` (the propagated carry of
      `ADCX`/`ADOX`): `[reg w, reg w, reg 1] → reg 1` (`carryOutBit`). The
      `reg 1` result threads into the next limb's carry-in. (#477) -/
  | addCarryHi (w : Nat)
  /-- Native right-rotate by a compile-time immediate `n`: `[reg w] → reg w`,
      `out = src.rotateRight n`. Single-input, carry-free (does not read or write
      flags), so it threads in a data-flow chain exactly like the `shr`/`shl`
      `regArith` ops. The data effect of x86 `ROR r64, imm` (flag-clobbering) and
      BMI2 `RORX r64, r64, imm` (flag-free). Added 2026-06-04 (#497) as the
      single-op image of the rotate idiom `(src >>> n) ||| (src <<< (w-n))`
      that SHA-512 Σ/σ and Keccak ρ emit as a `shr; shl; or` triple; the
      rotate insn-selection (`rorImm_denote_eq_shiftOr`) collapses the triple to
      this one op. The rotate amount is a dialect immediate (not a register), so
      there is no shift-amount input word. -/
  | rorImm (w n : Nat)
  /-- Native logical right-shift by a compile-time immediate `n`: `[reg w] → reg
      w`, `out = src >>> n`. Single-input (the shift amount is a dialect
      immediate, **not** a register-file read), so it threads in a data-flow
      chain like `rorImm`. The data effect of x86 `SHR r, imm`. Added (#605) so
      a constant shift (SHA-256/BLAKE2 `x >> 3` etc.) emits as an immediate-count
      shift `dst = src >> n;` — which jasminc x86 linearizes — instead of a
      variable shift `dst = src >> rcx;` (a `regArith .shr` reading the amount
      from a register, which jasminc rejects). -/
  | shrImm (w n : Nat)
  /-- Native **arithmetic** right-shift by a compile-time immediate `n`:
      `[reg w] → reg w`, `out = src.sshiftRight n` (sign-extending). The
      sign-aware twin of `shrImm` — same single-input immediate-shift shape, but
      denoting `BitVec.sshiftRight` rather than `>>>`. The data effect of x86
      `SAR r, imm`. Added (#606) so a constant **signed** shift emits as an
      immediate-count arithmetic shift `dst = (signed)src >> n;` (ML-DSA
      `reduce32`/`montgomery_reduce`/`decompose`/`make_hint`) — which jasminc x86
      linearizes — instead of a variable shift `regArith` reads from a register. -/
  | sarImm (w n : Nat)
  /-- Native logical left-shift by a compile-time immediate `n`: `[reg w] → reg
      w`, `out = src <<< n`. The left-shift counterpart of `shrImm` (#605). -/
  | shlImm (w n : Nat)
  /-- Constant-time SELECT / conditional move: `[reg 1, reg w, reg w] → reg w`,
      `out = if cond = 1 then a else b` (`selectW`). The condition is a 1-bit
      register; both operands are always evaluated, so the op is branch-free.
      The data effect of x86 `CMOVcc` (or the branchless mask idiom
      `(a & mask) | (b & ~mask)`, `mask = 0 - cond`). Added (#594, E2) as the
      constant-time primitive for the canonical conditional-subtract, the
      ladder `cswap`, and a sampler's conditional core. -/
  | select (w : Nat)
  /-- Multi-result external call: a single op for a `k`-output leaf call
      `name` with operand types `argTys` and the full result-type list
      `retTys`. The multi-result call op intended for the `func.call` lowering:
      a `k`-result call is one op carrying its whole `retTys`, lining up 1:1
      onto a `func.call` with `k` results — rather than `k` name-mangled
      single-result `extCall "callN:f"` ops. Its denotation is the opaque
      default of each result type (`callNDefaults`), the multi-result analogue
      of `extCall`'s single opaque default; the framework's single-`ret`
      `Expr` arm projects this tuple to its head slot (`retTys.headD`). -/
  | callN (name : String) (argTys : List JasminTy) (retTys : List JasminTy)
  /-- Parametrized 256-bit YMM (AVX2/VEX.256) op: mixed arity dispatched by the
      inner `YmmOp` — unary ops take one `reg 256` operand, binary ops two, and
      the result is always a `reg 256`. Adding a YMM op extends `YmmOp` (not
      `JasminOp`), so uniform `JasminOp` consumers match `| .vymm _` once and
      never change. -/
  | vymm (op : YmmDialect.YmmOp)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The Jasmin dialect: `Op` is `JasminOp`, `Ty` is `JasminTy`. -/
@[reducible] def jasminDialect : Dialect :=
  { Op := JasminOp, Ty := JasminTy }

/-- A default inhabitant for each `JasminTy`, used to give `extCall` a total
    (opaque) denotation. -/
def JasminTy.default : (t : JasminTy) → ⟦t⟧
  | .reg w => (0 : BitVec w)
  | .stackArr w _ => (fun _ => (0 : BitVec w))
  | .inlineInt => (0 : Nat)
  | .bool => false

/-- The opaque-default tuple of results for a multi-result `callN`: an
    `HVector` with `JasminTy.default` in each `retTys` slot. This is the
    multi-result value the `func.call` lowering consumes; the single-`ret`
    `Expr` denotation projects it to its head slot. -/
def callNDefaults : (retTys : List JasminTy) → HVector (fun t => ⟦t⟧) retTys
  | [] => .nil
  | t :: ts => .cons (JasminTy.default t) (callNDefaults ts)

/-- The single representative result type a multi-result `callN` exposes at the
    framework's single-`ret` `Expr` level (the call's head/primary result slot).
    The full `retTys` list is retained as `callN` op-data for the `func.call`
    lowering. -/
def callNRet (retTys : List JasminTy) : JasminTy := retTys.headD (.reg 0)

/-! ### Total stack-array access

`Fin`-indexed access reduced modulo `n`, total even for `n = 0`. -/

/-- Read element `k mod n` of a stack array; `0` for an empty array. -/
def stackGet {w n : Nat} (arr : Fin n → BitVec w) (k : Nat) : BitVec w :=
  match n, arr with
  | 0, _ => 0
  | (m + 1), arr => arr ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- Functionally update element `k mod n` of a stack array; identity (the
    everywhere-`0` array) for an empty array. -/
def stackSet {w n : Nat} (arr : Fin n → BitVec w) (k : Nat) (v : BitVec w) :
    Fin n → BitVec w :=
  match n, arr with
  | 0, _ => fun _ => 0
  | (m + 1), arr =>
      fun j => if j = ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ then v else arr j

/-- On an in-range index `j : Fin n`, the total `stackGet` reads exactly the
    underlying entry: `stackGet arr j.val = arr j`. (The `% n` reduction is the
    identity because `j.val < n`.) -/
theorem stackGet_id {w n : Nat} (arr : Fin n → BitVec w) (j : Fin n) :
    stackGet arr j.val = arr j := by
  cases n with
  | zero => exact absurd j.isLt (by omega)
  | succ m =>
      simp only [stackGet]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

/-! ### Leaf semantics for lattice-lowered `extCall`s

The lattice→jasmin lowering (`LatticeToJasmin.lean`) emits each NTT op as an
`extCall` to a named 16-bit stack-array leaf. `jasminExtSem` gives those leaves
their real (data-oblivious) semantics so the lowering is denotation-preserving
(discharged in `LatticeToJasminDenoteUncond.lean`):

* unary `[stackArr 16 _] → stackArr 16 m` (`ntt_*`, `ntt_invntt_*`): identity,
  read totally via `stackGet`;
* binary `[stackArr 16 _, stackArr 16 _] → stackArr 16 m`: pointwise **sum** when
  the leaf is `"poly_add"`, pointwise **product** otherwise (`ntt_basemul_*`,
  `"poly_mul"`).

Every other `extCall` keeps the opaque default (`JasminTy.default`), so an
external leaf (e.g. a CryptoSSA `fp_*` intrinsic) is still treated as opaque —
its agreement remains a separate obligation. -/
/-- Offset `o` parsed from a `"slice@{o}"` leaf name (`0` if malformed). A
    sub-array-slice leaf `slice@{o} : [stackArr w n] → stackArr w m` is the
    length-`m` window `a[o : o+m]`; it lets a single bundled buffer (e.g. a
    contiguous `polyvec`) feed per-component leaves without exceeding the
    register-arg ABI. `JasminAbiEmit` emits it as a jasmin sub-array `src[o:m]`.
    The offset is compile-time, so the leaf is constant-time; like the `fp_*`
    leaves it is denotation-opaque here (window-agreement is a leaf obligation,
    kept out of `jasminExtSem` so the lattice arms reduce unchanged). -/
def sliceWindow {w n : Nat} (o m : Nat) (arr : Fin n → BitVec w) : Fin m → BitVec w :=
  fun (j : Fin m) => stackGet arr (o + j.val)

def sliceOffset (name : String) : Nat :=
  match name.splitOn "@" with
  | [_, o] => o.toNat?.getD 0
  | _ => 0

def jasminExtSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧
  | _, [.stackArr 16 _], .stackArr 16 m => fun args =>
      (fun (j : Fin m) => stackGet args.head j.val)
  | name, [.stackArr 16 _, .stackArr 16 _], .stackArr 16 m => fun args =>
      if name = "poly_add" then
        (fun (j : Fin m) => stackGet args.head j.val + stackGet args.tail.head j.val)
      else
        (fun (j : Fin m) => stackGet args.head j.val * stackGet args.tail.head j.val)
  | _, _, retTy => fun _ => JasminTy.default retTy

/-! ## 5. Op signatures (arg types + return type) -/

instance : DialectSignature jasminDialect where
  sig op := match op with
    | .regArith _ w => [.reg w, .reg w]
    -- array, index register
    | .stackLoad w n => [.stackArr w n, .reg 64]
    -- array, index register, value
    | .stackStore w n => [.stackArr w n, .reg 64, .reg w]
    | .castW w _ => [.reg w]
    | .extCall _ argTys _ => argTys
    | .regConst _ _ => []
    | .vpackZMM _ => [.reg 512, .reg 512]
    | .vpackZMMd _ => [.reg 512, .reg 512]
    | .vprordZMM _ => [.reg 512]
    | .vpslldq _ => [.reg 128]
    | .vpsrldq _ => [.reg 128]
    | .vsimd op => op.argTys
    | .vymm op => if op.isBinary then [.reg 256, .reg 256] else [.reg 256]
    | .mulhi w => [.reg w, .reg w]
    | .addCarryLo w => [.reg w, .reg w, .reg 1]
    | .addCarryHi w => [.reg w, .reg w, .reg 1]
    | .rorImm w _ => [.reg w]
    | .shrImm w _ => [.reg w]
    | .sarImm w _ => [.reg w]
    | .shlImm w _ => [.reg w]
    | .select w => [.reg 1, .reg w, .reg w]
    | .callN _ argTys _ => argTys
  ret op := match op with
    | .regArith _ w => .reg w
    | .stackLoad w _ => .reg w
    | .stackStore w n => .stackArr w n
    | .castW _ w' => .reg w'
    | .extCall _ _ retTy => retTy
    | .regConst w _ => .reg w
    | .vpackZMM _ => .reg 512
    | .vpackZMMd _ => .reg 512
    | .vprordZMM _ => .reg 512
    | .vpslldq _ => .reg 128
    | .vpsrldq _ => .reg 128
    | .vsimd op => op.retTy
    | .vymm _ => .reg 256
    | .mulhi w => .reg w
    | .addCarryLo w => .reg w
    | .addCarryHi _ => .reg 1
    | .rorImm w _ => .reg w
    | .shrImm w _ => .reg w
    | .sarImm w _ => .reg w
    | .shlImm w _ => .reg w
    | .select w => .reg w
    | .callN _ _ retTys => callNRet retTys

/-! ## 6. Op denotation -/

/-- Project a `vymm` op's operands from its arity-dependent argument vector and
    denote them: binary ops read two `reg 256` operands, unary ops read one.
    The plain-`Bool` parameter `b = op.isBinary` refines the argument-vector
    type, so the `JasminOp.vymm` denote arm passes `op.isBinary` and the raw
    argument vector directly. -/
def vymmDenote (op : YmmDialect.YmmOp) :
    (b : Bool) →
    HVector (fun t => ⟦t⟧)
      (if b then [JasminTy.reg 256, JasminTy.reg 256] else [JasminTy.reg 256]) →
    BitVec 256
  | true, .cons a (.cons b .nil) => op.denoteBinary a b
  | false, .cons a _ => op.denoteUnary a

instance jasminDenote : DialectDenote jasminDialect where
  denote op := match op with
    | .regArith bop w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        bop.apply a b
    | .stackLoad w n => fun args =>
        let arr : Fin n → BitVec w := args.head
        let i : BitVec 64 := args.tail.head
        stackGet arr i.toNat
    | .stackStore w n => fun args =>
        let arr : Fin n → BitVec w := args.head
        let i : BitVec 64 := args.tail.head
        let v : BitVec w := args.tail.tail.head
        stackSet arr i.toNat v
    | .castW _ w' => fun args =>
        show BitVec w' from (args.head : BitVec _).zeroExtend w'
    | .extCall name argTys retTy => fun args => jasminExtSem name argTys retTy args
    | .regConst w n => fun _ => (BitVec.ofNat w n)
    | .vpackZMM bop => fun args =>
        let a : BitVec 512 := args.head
        let b : BitVec 512 := args.tail.head
        zmmPackQ bop a b
    | .vpackZMMd bop => fun args =>
        let a : BitVec 512 := args.head
        let b : BitVec 512 := args.tail.head
        zmmPackD bop a b
    | .vprordZMM n => fun args =>
        let a : BitVec 512 := args.head
        zmmRorD n a
    | .vpslldq n => fun args =>
        let a : BitVec 128 := args.head
        a <<< (n * 8)
    | .vpsrldq n => fun args =>
        let a : BitVec 128 := args.head
        a >>> (n * 8)
    | .vsimd op => match op with
        | .gf2p8mulb => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote .gf2p8mulb a b
        | .vpshufb => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote .vpshufb a b
        | .clmul imm => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote (.clmul imm) a b
        | .affineqb imm => fun args =>
            let a : BitVec 128 := args.head
            let A : BitVec 128 := args.tail.head
            SimdOp.denote (.affineqb imm) a A
        | .bitwise bop => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote (.bitwise bop) a b
        | .packed bop laneW => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote (.packed bop laneW) a b
        | .varShift bop laneW => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote (.varShift bop laneW) a b
        | .mulhi16 => fun args =>
            let a : BitVec 128 := args.head
            let b : BitVec 128 := args.tail.head
            SimdOp.denote .mulhi16 a b
        | .vaesenc => fun args =>
            let state : BitVec 128 := args.head
            let rk : BitVec 128 := args.tail.head
            SimdOp.denote .vaesenc state rk
        | .vaesenclast => fun args =>
            let state : BitVec 128 := args.head
            let rk : BitVec 128 := args.tail.head
            SimdOp.denote .vaesenclast state rk
        | .vaeskeygen rcon => fun args =>
            -- unary: `argTys = [reg 128]`, so only `args.head` exists; the denote
            -- ignores its second operand, so pass `src` again as a dummy.
            let src : BitVec 128 := args.head
            SimdOp.denote (.vaeskeygen rcon) src src
        | .vpshufd imm => fun args =>
            -- unary: `argTys = [reg 128]`, only `args.head`; denote ignores op 2.
            let src : BitVec 128 := args.head
            SimdOp.denote (.vpshufd imm) src src
    | .vymm op => fun args => vymmDenote op op.isBinary args
    | .mulhi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        mulHiW a b
    | .addCarryLo w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        addCarryWord a b cin
    | .addCarryHi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        carryOutBit a b cin
    | .rorImm w n => fun args =>
        let a : BitVec w := args.head
        a.rotateRight n
    | .shrImm w n => fun args =>
        let a : BitVec w := args.head
        a >>> n
    | .sarImm w n => fun args =>
        let a : BitVec w := args.head
        BitVec.sshiftRight a n
    | .shlImm w n => fun args =>
        let a : BitVec w := args.head
        a <<< n
    | .select w => fun args =>
        let cond : BitVec 1 := args.head
        let a : BitVec w := args.tail.head
        let b : BitVec w := args.tail.tail.head
        selectW cond a b
    | .callN _ _ retTys => fun _ => JasminTy.default (callNRet retTys)

/-- Leaf-parametric denotation: identical to `jasminDenote` except opaque `extCall`
    leaves consult `leafSem` instead of the fixed default-returning `jasminExtSem`;
    every other op delegates to `jasminDenote` verbatim. Driving a kernel's `Com.denote`
    through `jasminDenoteWith leafSem` (an abstract oracle) makes opaque-leaf correctness
    faithful to the leaf oracle — see `Pairing.Eip197Denote`. (`callN` multi-return leaves are
    not yet oracle-parametric; they stay `default`.) -/
def jasminDenoteWith
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧) :
    DialectDenote jasminDialect where
  denote op := match op with
    | .extCall name argTys retTy => fun args => leafSem name argTys retTy args
    | o => jasminDenote.denote o

/-! ### Multi-result leaf oracle

`jasminDenoteWith` makes the single-result `extCall` leaf consult an abstract
oracle. The multi-result `callN` leaf has the same opaque-default denotation in
`jasminDenote`; `jasminDenoteWithN` below extends the leaf-parametric family so
that `callN` also consults an oracle, letting a kernel whose leaves are
`k`-output `func.call`s be denoted faithfully to a leaf semantics.

A `callN` op exposes its head/primary result slot at the framework's single-`ret`
`Expr` level (`ret (callN _ _ retTys) = callNRet retTys`), so its oracle returns
that head slot's value: `⟦callNRet retTys⟧`. The full `retTys` list is passed to
the oracle so a multi-result leaf can decide its head value from the whole
signature. -/

/-- The `callN` leaf oracle shape: given a leaf `name`, the operand types
    `argTys`, the full result-type list `retTys`, and the operand values, produce
    the value of the call's head/primary result slot (`⟦callNRet retTys⟧`), the
    type a `callN` exposes at the framework's single-`ret` `Expr` level. -/
abbrev CallNLeafSem :=
  (name : String) → (argTys : List JasminTy) → (retTys : List JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦callNRet retTys⟧

/-- The default `callN` oracle: reproduces `jasminDenote`'s opaque-default
    denotation of `callN` (the head slot of `callNDefaults`), i.e.
    `JasminTy.default (callNRet retTys)`. Passing it to `jasminDenoteWithN`
    recovers `jasminDenoteWith`'s `callN` behaviour exactly. -/
def callNDefaultSem : CallNLeafSem :=
  fun _ _ retTys _ => JasminTy.default (callNRet retTys)

/-- Leaf-parametric denotation over BOTH leaf kinds: identical to `jasminDenote`
    except opaque `extCall` leaves consult `leafSem` and opaque multi-result
    `callN` leaves consult `callNSem`; every other op delegates to `jasminDenote`
    verbatim. This extends `jasminDenoteWith` (which parametrises only the
    single-result `extCall` leaf) with a `callN` oracle, so a kernel whose leaves
    are `k`-output `func.call`s is oracle-parametric on those leaves too.

    Taking `callNSem := callNDefaultSem` recovers `jasminDenoteWith leafSem`
    exactly (see `jasminDenoteWithN_extCall`, `jasminDenoteWithN_callN_default`),
    so the committed single-oracle callers keep their behaviour. -/
def jasminDenoteWithN
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (callNSem : CallNLeafSem) :
    DialectDenote jasminDialect where
  denote op := match op with
    | .extCall name argTys retTy => fun args => leafSem name argTys retTy args
    | .callN name argTys retTys => fun args => callNSem name argTys retTys args
    | o => jasminDenote.denote o

/-- The `extCall` arm of `jasminDenoteWithN` consults `leafSem`, unchanged from
    `jasminDenoteWith`: the multi-result extension leaves the single-result leaf
    behaviour intact. -/
theorem jasminDenoteWithN_extCall
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (callNSem : CallNLeafSem)
    (name : String) (argTys : List JasminTy) (retTy : JasminTy) :
    (jasminDenoteWithN leafSem callNSem).denote (.extCall name argTys retTy)
      = fun args => leafSem name argTys retTy args :=
  rfl

/-- The `callN` arm of `jasminDenoteWithN` consults `callNSem`. -/
theorem jasminDenoteWithN_callN
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (callNSem : CallNLeafSem)
    (name : String) (argTys : List JasminTy) (retTys : List JasminTy) :
    (jasminDenoteWithN leafSem callNSem).denote (.callN name argTys retTys)
      = fun args => callNSem name argTys retTys args :=
  rfl

/-- Backwards compatibility: `jasminDenoteWithN` with the default `callN` oracle
    agrees with the committed `jasminDenoteWith` on the `extCall` leaf. -/
theorem jasminDenoteWithN_extCall_agrees
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (name : String) (argTys : List JasminTy) (retTy : JasminTy) :
    (jasminDenoteWithN leafSem callNDefaultSem).denote (.extCall name argTys retTy)
      = (jasminDenoteWith leafSem).denote (.extCall name argTys retTy) :=
  rfl

/-- Backwards compatibility: on the `callN` op, `jasminDenoteWithN` with the
    default oracle reproduces `jasminDenoteWith`'s opaque-default denotation. -/
theorem jasminDenoteWithN_callN_default
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧)
    (name : String) (argTys : List JasminTy) (retTys : List JasminTy) :
    (jasminDenoteWithN leafSem callNDefaultSem).denote (.callN name argTys retTys)
      = (jasminDenoteWith leafSem).denote (.callN name argTys retTys) :=
  rfl

/-! ## 7. Smoke test

Build a tiny two-op `Com jasminDialect` and check `Com.denote` computes the
expected value. The program is self-contained over `regArith` and `castW`,
fed by an input valuation. On inputs `a b : BitVec 32`:

    let s = regArith add a b   -- s = a + b   : reg 32
    let t = castW 32 64 s      -- t = zext s  : reg 64
    ret t

so `denote ⟨a, b⟩ = (a + b).zeroExtend 64`. We check it on concrete inputs. -/

/-- Two-op smoke program over `[reg 32, reg 32]`. -/
def smokeProg : Com jasminDialect [.reg 32, .reg 32] (.reg 64) :=
  .var (.mk (.regArith .add 32) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.var (.mk (.castW 32 64) rfl (.cons .here .nil))
      (.ret .here))

/-- The smoke program denotes to `(a + b).zeroExtend 64` on the input
    valuation `⟨a, b⟩`; checked on concrete inputs `7, 35 ↦ 42`. -/
example :
    smokeProg.denote
      (.cons (7 : BitVec 32) (.cons (35 : BitVec 32) .nil))
      = ((42 : BitVec 32).zeroExtend 64) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
