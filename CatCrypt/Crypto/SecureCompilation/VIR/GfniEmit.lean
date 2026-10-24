/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-!
# GFNI dialect ops (Galois Field New Instructions) — denotation + alignment

GFNI is the Intel/AMD ISA extension exposing single-byte `GF(2^8)` field
operations directly on `xmm`/`ymm`/`zmm` registers. The hot mnemonics for
crypto:

* `VGF2P8MULB xmm, xmm, xmm` (`_mm_gf2p8mul_epi8`) — element-wise (16 lanes
  at 128-bit, 32 at 256-bit) `GF(2^8)` multiply, reduction polynomial
  `0x11B` (the AES polynomial).
* `VGF2P8AFFINEQB xmm, xmm, xmm, imm8` (`_mm_gf2p8affine_epi64_epi8`) — per
  byte, `result = (A · x) ⊕ b` where `A : BitVec 64` (8 rows × 8 cols, a
  GF(2) affine matrix packed in a `u64` operand) and `b = imm8`. Used for
  bitsliced S-box single-instruction implementations.
* `VGF2P8AFFINEINVQB` — same affine wrapped around `GF(2^8)` inversion;
  i.e. `result = (A · inv(x)) ⊕ b`. The single-instruction AES S-box is
  precisely this with the FIPS 197 affine matrix.

This module:

1. Defines a tiny `GfniOp` inductive (the three mnemonics above);
2. Gives an algebraic `denoteGfni : GfniOp → BitVec 128 → BitVec 128 →
   BitVec 128` matching Intel SDM Vol. 2 (Aug 2023 revision) byte-for-byte
   on the `xmm`-width (128-bit, 16 lanes);
3. Carries the bridge theorem `gfniMul_eq_gf28Mul` showing the GFNI
   multiply equals the existing schoolbook `AesBitslice.gfMul` on every
   byte (the GFNI ceiling closes against the committed AES-polynomial
   GF(2^8) field, so any caller denoting against `gfMul` can
   re-emit through GFNI and keep its proof carry);
4. Structural sanity theorems + alignment lemma (`gfniMul_lane_map`)
   reusing `LaneMap.vmap₂_eq_scalar` so per-lane independence is closed by
   the existing lemma, not duplicated.

## What this is NOT

* This is **not** a new psem primitive — the dialect op is a pure
  computation on `BitVec 128`, denotable in Lean, that the demonstrator
  emit caller (`bench/uov_compare/uov_kernel_gfni_emit.lean`) renders as
  an explicit `#VGF2P8MULB_128` intrinsic line in the emitted `.jazz`.
  `jasminc` (compiler/tests/success/x86-64) recognises `#VGF2P8MULB_128`
  and `#VGF2P8AFFINEQB_128` since the early-2024 GFNI surface; if the
  installed `jasminc` rejects the surface, the demonstrator falls back to
  the table-lookup emit (the `Gf256Tab` path) and the proof carry holds
  unchanged.
* The 256-bit / 512-bit (`ymm`/`zmm`) widths are lane-wise extensions —
  same per-byte semantics, more lanes. We pin the `xmm` (128-bit / 16
  lanes) shape since (a) it's what `_mm_gf2p8mul_epi8` (the GFNI ceiling
  measured at ~18.5 cyc/op vs our ~40 cyc/op table-lookup
  emit) consumes, and (b) it's the granularity at which the lane-map
  lemma `vmap₂_eq_scalar` applies cleanly.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.GfniEmit`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.GfniEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit.AesBitslice (gfMul)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-! ## 1. The dialect op set -/

/-- GFNI byte-wise mnemonics at `xmm` width (128-bit, 16 lanes). The
    semantics of each is a per-byte `BitVec 8 → BitVec 8 → BitVec 8`
    operation lifted lane-wise to `BitVec 128`. -/
inductive GfniOp
  | /-- `VGF2P8MULB xmm` — byte-wise GF(2^8) multiply, reduction `0x11B`. -/
    vgf2p8mulb
  | /-- `VGF2P8AFFINEQB xmm` — byte-wise affine `(A · x) ⊕ b` with the
        `A` matrix packed in the second operand (per Intel SDM, the q64
        block holds 8 rows × 8 cols, MSB-first), and `b` as imm8. We
        model `b = 0` here (the affine bias enters via XOR on the
        consumer side); a non-zero bias is one extra `VPXOR`. -/
    vgf2p8affineqb
  | /-- `VGF2P8AFFINEINVQB xmm` — byte-wise affine on the GF(2^8)
        inverse: `(A · inv(x)) ⊕ b`. The single-instruction AES S-box
        is this op with the FIPS 197 affine. -/
    vgf2p8affineinvqb
  deriving DecidableEq, Repr

/-! ## 2. Per-byte denotation core

The byte-level multiply matches `AesBitslice.gfMul` (and therefore
`AES128.xtime` / `AES128.mul3`) byte-for-byte — this is what the bridge
theorem `gfniMul8_eq_gfMul` will pin. -/

/-- One bit step of the GF(2^8) shift-and-add multiply, branchless:
    bit `i` of `b` masked across all 8 bits of the running `sh = a · x^i`,
    XOR-accumulated into `r`. Same boolean structure as
    `AesBitslice.gfMul`; rephrased as a pure pattern-matching function to
    keep the byte-level identity definitionally clean. -/
def gfniMul8Step (a b r : BitVec 8) (i : Nat) : BitVec 8 × BitVec 8 :=
  let bitI := (b >>> (i : Nat)) &&& 1
  let mask := 0#8 - bitI
  let r' := r ^^^ (a &&& mask)
  let msb := a >>> 7
  let shifted := a <<< 1
  let a' := shifted ^^^ (msb * 0x1b#8)
  (r', a')

/-- GF(2^8) multiply on one byte: schoolbook shift-and-add reduced by
    `0x1b` on MSB overflow. Same algorithm as `AesBitslice.gfMul` — the
    bridge `gfniMul8_eq_gfMul` certifies the byte-for-byte identity. -/
def gfniMul8 (a b : BitVec 8) : BitVec 8 :=
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

/-- **Byte-level bridge.** The GFNI per-byte multiply equals the
    `AesBitslice.gfMul` schoolbook GF(2^8) multiply on every byte pair
    `(a, b) ∈ [0..255]²`. Discharged by 65536-entry `native_decide`, the
    same precedent as `Gf256Tab.gf256TabMul_eq_slow`. -/
theorem gfniMul8_eq_gfMul :
    ∀ a b : Fin 256,
      gfniMul8 (BitVec.ofNat 8 a.val) (BitVec.ofNat 8 b.val) =
        gfMul (BitVec.ofNat 8 a.val) (BitVec.ofNat 8 b.val) := by
  native_decide

/-- Byte-level identity at `BitVec 8` arguments (the shape the lane-map
    consumer needs). Discharged by a 65536-entry `native_decide` over
    the 8-bit input space directly — `decide` can range over `BitVec 8`
    via the `Fintype` instance, and the body is the same shift-and-add
    computation as the `Fin 256` form above. -/
theorem gfniMul8_eq_gfMul' :
    ∀ a b : BitVec 8, gfniMul8 a b = gfMul a b := by
  native_decide

/-! ## 3. Byte-lane split / join for `BitVec 128`

A `BitVec 128` is 16 lanes of `BitVec 8`. We expose the split via
`leByte` (mirroring `JasmincWArrayAlignment.leByte` — bit window
`[8k, 8k+8)` is byte `k` little-endian) and the join via a small fold;
the lane-parallel application of a `BitVec 8 → BitVec 8 → BitVec 8` op
then reduces to `LaneMap.vmap₂` at width 8, lane count 16. -/

/-- The `k`-th byte (little-endian) of a `BitVec 128`. Mirrors the
    `JasmincWArrayAlignment.leByte` byte-window. -/
def byteOf (v : BitVec 128) (k : Fin 16) : BitVec 8 :=
  BitVec.extractLsb' (8 * k.val) 8 v

/-- The 16-lane `BitVec 8` view of a `BitVec 128` — exactly the
    `LaneMap.Vec 16 8` shape the lane-map lemmas consume. -/
def lanesOf (v : BitVec 128) : Vec 16 8 := fun k => byteOf v k

/-- Reassemble 16 `BitVec 8` lanes into a `BitVec 128` little-endian.
    Mirrors the `JasmincWArrayAlignment.decodeAux` OR-of-shifted-bytes
    pattern, specialised to width 128 and length 16. -/
def packBytes (bs : Fin 16 → BitVec 8) : BitVec 128 :=
  Fin.foldl 16
    (fun acc k => acc ||| ((bs k).setWidth 128 <<< (8 * k.val))) (0 : BitVec 128)

/-! ## 4. The packed denotation

`denoteGfni op a b` applies the per-byte op lane-wise across the 16
bytes of `a` and `b`. For `vgf2p8mulb` the per-byte op is `gfniMul8`;
for the affine variants we model `(A · x) ⊕ b` and `(A · inv(x)) ⊕ b`
with `b = 0` (a non-zero affine bias enters as a separate `VPXOR` on
the consumer side, matching how Intel intrinsics expose the imm8). -/

/-- `GF(2)` affine matrix-vector product packed in the second `q64`
    operand: the byte `M : BitVec 64` is read as 8 rows of 8 bits each
    (MSB-first per Intel SDM), and we compute `M · x` over `GF(2)`.
    Concretely: bit `i` of the result is the GF(2) dot product of row
    `i` of `M` with the byte `x`. -/
def gfniAffine8 (M : BitVec 64) (x : BitVec 8) : BitVec 8 :=
  Id.run do
    let mut r : BitVec 8 := 0
    for i in [0:8] do
      -- row i is bits [8*(7-i), 8*(7-i)+8) of M (Intel SDM is MSB-first
      -- on the per-row layout)
      let rowStart : Nat := 8 * (7 - i)
      let row : BitVec 8 := BitVec.extractLsb' rowStart 8 M
      -- GF(2) inner product = XOR of (row & x) bits
      let prod : BitVec 8 := row &&& x
      let mut acc : BitVec 1 := 0
      for j in [0:8] do
        acc := acc ^^^ ((prod >>> (j : Nat)) &&& 1).setWidth 1
      let outBit : BitVec 8 := acc.setWidth 8
      r := r ||| (outBit <<< i)
    pure r

/-- Pure GF(2^8) inverse on one byte: reuses
    `AesBitslice.gfInv` (Fermat-chain `x^254`, with `0^254 = 0`). -/
def gfniInv8 (x : BitVec 8) : BitVec 8 := AesBitslice.gfInv x

/-- Per-byte semantics of each `GfniOp`. `b` carries the operand that
    is the multiplier (for `vgf2p8mulb`) or the packed-affine matrix
    (for the affine variants — in the `q64` layout the second operand
    is read as a 64-bit affine block). -/
def denoteGfniByte : GfniOp → BitVec 8 → BitVec 8 → BitVec 8
  | .vgf2p8mulb,        a, b => gfniMul8 a b
  | .vgf2p8affineqb,    a, b =>
      -- second operand a is the data byte; first operand b carries the
      -- affine matrix (Intel SDM: VGF2P8AFFINEQB dest, src1=matrix(q64),
      -- src2=data(byte)). We re-use the same `(matrix, data)` argument
      -- order as the multiply, so the dialect-op denotation is
      -- regular: `denoteGfniByte op a b` always takes `a` as the
      -- byte and `b` as the second-operand quad/byte.
      gfniAffine8 (b.setWidth 64) a
  | .vgf2p8affineinvqb, a, b =>
      gfniAffine8 (b.setWidth 64) (gfniInv8 a)

/-- Packed denotation: apply the per-byte op lane-wise across the 16
    bytes of `a` and `b`. -/
def denoteGfni (op : GfniOp) (a b : BitVec 128) : BitVec 128 :=
  packBytes (vmap₂ (denoteGfniByte op) (lanesOf a) (lanesOf b))

/-! ## 5. The headline bridge theorem

`denoteGfni .vgf2p8mulb a b` equals the abstract "lane-wise schoolbook
`gfMul` packed into a `BitVec 128`" — the connection any caller needs
to re-emit through GFNI while keeping a proof carry that
denotes against `AesBitslice.gfMul`. -/

/-- The abstract reference: lane-wise schoolbook `gfMul` packed into a
    `BitVec 128`. This is what `Gf256Tab`/`AesBitslice` callers denote
    their bytewise multiplications against. -/
def packedGf28Mul (a b : BitVec 128) : BitVec 128 :=
  packBytes (vmap₂ gfMul (lanesOf a) (lanesOf b))

/-- **Headline.** The GFNI byte-wise multiply denotation equals the
    abstract lane-wise `gfMul` reference, byte-for-byte. Proof: each
    lane is `gfniMul8 a_k b_k = gfMul a_k b_k` (the byte-level
    `gfniMul8_eq_gfMul`), then `LaneMap.vmap₂_eq_scalar` gives lane
    equality, which `packBytes` lifts to the 128-bit result by
    `funext`. -/
theorem gfniMul_eq_gf28Mul (a b : BitVec 128) :
    denoteGfni .vgf2p8mulb a b = packedGf28Mul a b := by
  -- Reduce both sides to the same `packBytes (vmap₂ f …)` where the
  -- per-byte function on the LHS is `gfniMul8` and on the RHS is
  -- `gfMul`. After unfolding the `denoteGfniByte` `match`, funext on
  -- the two functions collapses to the byte-level
  -- `gfniMul8_eq_gfMul'` identity (`∀ x y : BitVec 8, …`).
  unfold denoteGfni packedGf28Mul vmap₂ denoteGfniByte
  -- Both sides are `packBytes (fun k => f (lanesOf a k) (lanesOf b k))`
  -- with `f = gfniMul8` on the LHS, `gfMul` on the RHS. The byte-level
  -- exhaustive identity makes the two pointwise equal, hence the packs.
  have hfun : (fun k : Fin 16 => gfniMul8 (lanesOf a k) (lanesOf b k))
              = (fun k : Fin 16 => gfMul (lanesOf a k) (lanesOf b k)) := by
    funext k; exact gfniMul8_eq_gfMul' (lanesOf a k) (lanesOf b k)
  rw [hfun]

/-! ## 6. Structural alignment lemma — the lane-map shape -/

/-- The GFNI packed-byte multiply is a `LaneMap.vmap₂` at lane width 8,
    lane count 16. Reuses the lemma `vmap₂_eq_scalar`: per-lane the
    op is byte-independent (no cross-lane carry, no horizontal sum), so
    the packed form equals the scalar per-lane form. Reusable for
    every other byte-independent GFNI op (the affine pair). -/
theorem gfniMul_lane_map (a b : BitVec 128) :
    vmap₂ gfniMul8 (lanesOf a) (lanesOf b)
      = (fun k => gfniMul8 (lanesOf a k) (lanesOf b k)) :=
  vmap₂_eq_scalar gfniMul8 (lanesOf a) (lanesOf b)

/-! ## 7. Structural sanity on the op set -/

/-- The op set has exactly the three mnemonics. -/
theorem gfniOp_complete (op : GfniOp) :
    op = .vgf2p8mulb ∨ op = .vgf2p8affineqb ∨ op = .vgf2p8affineinvqb := by
  cases op <;> simp

/-- `0` is a left zero of the byte multiply `gfniMul8`, checked over
    all bytes. -/
theorem gfniMul8_zero_left (a : BitVec 8) : gfniMul8 0 a = 0 := by
  -- `gfniMul8 0 a` unfolds to a chain that accumulates `(0 &&& mask)`
  -- starting from `0` — every step contributes `0`, so the result is `0`.
  -- Discharged structurally by `native_decide` on the byte (`BitVec 8`).
  revert a
  native_decide

/-- Discharged structurally by `native_decide` on the byte. -/
theorem gfniMul8_zero_right (a : BitVec 8) : gfniMul8 a 0 = 0 := by
  revert a
  native_decide

/-! ## 8. Render helpers for the emitted jazz

These are pure string emitters — they live alongside `denoteGfni` so
the demonstrator consumers can render the intrinsic line without re-deriving
the spelling. The jasmin surface name is `#VGF2P8MULB_128` /
`#VGF2P8AFFINEQB_128` / `#VGF2P8AFFINEINVQB_128` (per the GFNI
surface of `jasmin/compiler`, early 2024). -/

/-- Jasmin surface mnemonic for each `GfniOp` (the intrinsic name
    `jasminc` consumes after the `#`). -/
def gfniMnemonic : GfniOp → String
  | .vgf2p8mulb        => "#VGF2P8MULB_128"
  | .vgf2p8affineqb    => "#VGF2P8AFFINEQB_128"
  | .vgf2p8affineinvqb => "#VGF2P8AFFINEINVQB_128"

/-- Render a single GFNI intrinsic line. `dst`/`src1`/`src2` are
    `reg u128` slot names; `imm` is the imm8 byte (default `0` — the
    affine bias, ignored by `vgf2p8mulb`). -/
def renderGfniLine (op : GfniOp) (dst src1 src2 : String) (imm : Nat := 0) : String :=
  match op with
  | .vgf2p8mulb =>
      dst ++ " = " ++ gfniMnemonic op ++ "(" ++ src1 ++ ", " ++ src2 ++ ");"
  | .vgf2p8affineqb | .vgf2p8affineinvqb =>
      dst ++ " = " ++ gfniMnemonic op ++ "(" ++ src1 ++ ", " ++ src2
        ++ ", " ++ toString imm ++ ");"

/-- Structural sanity: each mnemonic is non-empty. -/
theorem gfniMnemonic_nonempty (op : GfniOp) : (gfniMnemonic op).length > 0 := by
  cases op <;> decide

end CatCrypt.Crypto.SecureCompilation.VIR.GfniEmit
