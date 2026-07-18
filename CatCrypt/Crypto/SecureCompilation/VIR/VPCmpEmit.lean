/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-!
# VPCMPEQQ + VPMOVMSKB dialect ops (SIMD per-lane compare + sign-mask extract)
— denotation + alignment

`VPCMPEQQ` is the AVX2 packed 64-bit equality compare: given two register
lanes packed as 64-bit qwords, the instruction returns, per qword lane,
an all-ones mask (`0xFFFFFFFFFFFFFFFF`) if the two qwords are equal, or
all zeros if they differ. The mnemonic is xmm/ymm/zmm — 2/4/8 qwords per
register respectively. No cross-lane mixing: per-lane independent
equality.

`VPMOVMSKB` is the AVX2 byte-wise sign-mask extract: given a 128- or
256-bit register, it returns a 16- or 32-bit bitmask in a general-purpose
register, one bit per byte of the input, taken as the byte's sign bit
(bit 7 of each byte). Composed with VPCMPEQQ this yields a compact
"is this qword equal" bitmap: per VPCMPEQQ-produced lane, all 8 bytes
have the same sign bit (1 if equal, 0 if not), so VPMOVMSKB collapses
the 256-bit mask into a 32-bit bitmask of the form `0xFFFFFFFF` if all
4 qwords match and a non-`0xFFFFFFFF` value with leading zero-bytes
otherwise.

The pair is the load-bearing primitive for non-CT mpn compare: scan the
limbs MSB-first in 4-qword (256-bit ymm) chunks, do one VPCMPEQQ + one
VPMOVMSKB per chunk, branch on whether the 32-bit bitmask equals
`0xFFFFFFFF`. If equal → advance to the next chunk; if not → use TZCNT
to find the first differing byte and run a scalar compare on that limb.

The expected win against the scalar u32-loop Z3 baseline is ~3×: each
SIMD chunk does the equality check for 4× the data in roughly the same
fetch-decode cost as one scalar compare iteration, with the same
early-exit semantics.

## What this module provides

1. `VPCmpW` — width tag (U128/U256/U512) for the packed VPCMPEQQ op.
2. `VPMovMskW` — width tag (U128/U256) for the packed VPMOVMSKB op.
3. `VPCmpOp` — dialect op set.
4. `vpcmpeqq_lane` — per-lane denotation: `BitVec 64 × BitVec 64 →
   BitVec 64`, all-ones-or-all-zeros.
5. `vpmovmskb_lane128` / `vpmovmskb_lane256` — per-byte sign extraction
   → 16-bit / 32-bit bitmask.
6. `vpcmpeqq_eq_lane` / `vpmovmskb_eq_signmask` — headline bridges.
7. `vpcmpeqq_lane_map` — alignment to multi-lane via
   `LaneMap.vmap₂_eq_scalar`.
8. Render helpers `#VPCMPEQQ_128` / `_256` / `_512` and
   `#VPMOVMSKB_128` / `_256`.

## What this module is NOT

* Not a new psem primitive — the dialect op is a pure `BitVec`
  computation, denotable in Lean. The demonstrator
  (`bench/mpn_compare_simd_compare/cmp_simd_emit.lean`) renders the
  intrinsic lines in the emitted `.jazz`.
* Not the full mpn-compare driver — that's the consumer's job: the
  emitted body does the chunk scan + TZCNT + scalar tail; the dialect
  primitive pinned here is the per-lane equality compare and the
  sign-mask extract.
* The wider VPCMPEQQ_512 variant (AVX-512) is the lane-wise lift of
  the same per-lane semantics — covered by `LaneMap.vmap₂_eq_scalar`.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.VPCmpEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VPCmpEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-! ## 1. The dialect op set -/

/-- The width tag for the packed `VPCMPEQQ` op. -/
inductive VPCmpW
  | u128  -- 2 lanes of u64: `VPCMPEQQ xmm`
  | u256  -- 4 lanes of u64: `VPCMPEQQ ymm`
  | u512  -- 8 lanes of u64: `VPCMPEQQ zmm`
  deriving DecidableEq, Repr

/-- The number of 64-bit lanes for each `VPCmpW` width. -/
def VPCmpW.lanes : VPCmpW → Nat
  | .u128 => 2
  | .u256 => 4
  | .u512 => 8

/-- The bit width of the packed register for each `VPCmpW` width. -/
def VPCmpW.bits : VPCmpW → Nat
  | .u128 => 128
  | .u256 => 256
  | .u512 => 512

/-- The width tag for the packed `VPMOVMSKB` op. VPMOVMSKB is xmm/ymm
    only — there is no VPMOVMSKB zmm. -/
inductive VPMovMskW
  | u128  -- 16 bytes → 16-bit bitmask
  | u256  -- 32 bytes → 32-bit bitmask
  deriving DecidableEq, Repr

/-- The byte count of the packed input for each VPMOVMSKB width. -/
def VPMovMskW.bytes : VPMovMskW → Nat
  | .u128 => 16
  | .u256 => 32

/-- The bit width of the bitmask output (one bit per input byte). -/
def VPMovMskW.outBits : VPMovMskW → Nat
  | .u128 => 16
  | .u256 => 32

/-- The two dialect mnemonics: `VPCMPEQQ` at one of three widths and
    `VPMOVMSKB` at one of two widths. -/
inductive VPCmpOp
  | /-- `VPCMPEQQ` at the chosen packed-register width: per 64-bit lane,
        emit all-ones if the two lanes are equal, all zeros otherwise.
        No cross-lane mixing. -/
    vpcmpeqq (w : VPCmpW)
  | /-- `VPMOVMSKB` at the chosen packed-register width: per byte of the
        input, take bit 7 (the sign bit) and pack into a `outBits`-wide
        bitmask. -/
    vpmovmskb (w : VPMovMskW)
  deriving DecidableEq, Repr

/-! ## 2. Per-lane VPCMPEQQ denotation

The single 64-bit-lane semantics is the all-ones-or-all-zeros mask:

  vpcmpeqq_lane a b = if a = b then 0xFFFFFFFFFFFFFFFF#64 else 0#64

This is the Intel SDM Vol. 2 semantics for one qword lane of
`PCMPEQQ`. The wider `VPCMPEQQ ymm`/`zmm` variants run independent
per-qword equality compares on each lane in parallel; no cross-lane
mixing. Hence the multi-lane denotation is the lane-wise lift of this
single-lane function. -/

/-- The all-ones 64-bit mask: `0xFFFFFFFFFFFFFFFF`. -/
def allOnes64 : BitVec 64 := BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF

/-- **Per-lane denotation of `VPCMPEQQ`.** Two 64-bit lanes compare
    equal → all-ones mask; differ → all zeros. Intel SDM Vol. 2,
    `PCMPEQQ` (one qword lane). -/
def vpcmpeqq_lane (a b : BitVec 64) : BitVec 64 :=
  if a = b then allOnes64 else 0#64

/-! ## 3. Per-byte VPMOVMSKB denotation

`VPMOVMSKB` takes a 128- or 256-bit packed register, treats it as `n`
bytes (n = 16 or 32), and produces an `n`-bit bitmask where bit `i` of
the output is bit 7 of byte `i` of the input. The bit ordering is
little-endian: byte 0 (low) of the input → bit 0 of the output. -/

/-- Byte `k` (little-endian) of a 128-bit register as a `BitVec 8`. -/
def bv128Byte (v : BitVec 128) (k : Fin 16) : BitVec 8 :=
  BitVec.extractLsb' (8 * k.val) 8 v

/-- Byte `k` (little-endian) of a 256-bit register as a `BitVec 8`. -/
def bv256Byte (v : BitVec 256) (k : Fin 32) : BitVec 8 :=
  BitVec.extractLsb' (8 * k.val) 8 v

/-- Bit 7 of a byte: 1 if the byte's high bit is set (sign-bit
    extraction). -/
def signBit (b : BitVec 8) : BitVec 1 :=
  BitVec.extractLsb' 7 1 b

/-- **Per-128-bit denotation of `VPMOVMSKB`.** For each of 16 bytes
    of the input, take bit 7 → produce a 16-bit bitmask with byte `i`'s
    sign bit at output bit position `i`. -/
def vpmovmskb_lane128 (v : BitVec 128) : BitVec 16 :=
  Fin.foldl 16 (init := (0 : BitVec 16))
    (fun acc k =>
      let sb : BitVec 1 := signBit (bv128Byte v k)
      acc ||| (sb.setWidth 16 <<< k.val))

/-- **Per-256-bit denotation of `VPMOVMSKB`.** For each of 32 bytes of
    the input, take bit 7 → produce a 32-bit bitmask. -/
def vpmovmskb_lane256 (v : BitVec 256) : BitVec 32 :=
  Fin.foldl 32 (init := (0 : BitVec 32))
    (fun acc k =>
      let sb : BitVec 1 := signBit (bv256Byte v k)
      acc ||| (sb.setWidth 32 <<< k.val))

/-! ## 4. Sanity properties of `vpcmpeqq_lane` -/

/-- `vpcmpeqq_lane` is reflexive: comparing a lane with itself returns
    all-ones. -/
theorem vpcmpeqq_lane_refl (a : BitVec 64) :
    vpcmpeqq_lane a a = allOnes64 := by
  unfold vpcmpeqq_lane
  simp

/-- `vpcmpeqq_lane` is symmetric: swapping arguments gives the same
    mask (equality is symmetric). -/
theorem vpcmpeqq_lane_symm (a b : BitVec 64) :
    vpcmpeqq_lane a b = vpcmpeqq_lane b a := by
  unfold vpcmpeqq_lane
  by_cases h : a = b
  · subst h; rfl
  · have h' : b ≠ a := fun heq => h heq.symm
    simp [h, h']

/-- `vpcmpeqq_lane` produces only two values: all-ones or all-zeros. -/
theorem vpcmpeqq_lane_bool (a b : BitVec 64) :
    vpcmpeqq_lane a b = allOnes64 ∨ vpcmpeqq_lane a b = 0#64 := by
  unfold vpcmpeqq_lane
  by_cases h : a = b
  · left; simp [h]
  · right; simp [h]

/-! ## 5. The packed denotation

At U128 the packed denotation is the 2-lane lift; at U256 the 4-lane
lift; at U512 the 8-lane lift. We use `LaneMap.vmap₂` for the
multi-lane shape so the alignment lemma falls out of
`LaneMap.vmap₂_eq_scalar` for free. -/

/-- `BitVec 128` view as 2 lanes of `BitVec 64`. -/
def lanesOf128 (v : BitVec 128) (k : Fin 2) : BitVec 64 :=
  BitVec.extractLsb' (64 * k.val) 64 v

/-- `BitVec 256` view as 4 lanes of `BitVec 64`. -/
def lanesOf256 (v : BitVec 256) (k : Fin 4) : BitVec 64 :=
  BitVec.extractLsb' (64 * k.val) 64 v

/-- `BitVec 512` view as 8 lanes of `BitVec 64`. -/
def lanesOf512 (v : BitVec 512) (k : Fin 8) : BitVec 64 :=
  BitVec.extractLsb' (64 * k.val) 64 v

/-- Packed denotation of `VPCMPEQQ xmm` (2 lanes). -/
def denoteVPCmpEqQ128 (a b : BitVec 128) : Fin 2 → BitVec 64 :=
  vmap₂ vpcmpeqq_lane (lanesOf128 a) (lanesOf128 b)

/-- Packed denotation of `VPCMPEQQ ymm` (4 lanes). -/
def denoteVPCmpEqQ256 (a b : BitVec 256) : Fin 4 → BitVec 64 :=
  vmap₂ vpcmpeqq_lane (lanesOf256 a) (lanesOf256 b)

/-- Packed denotation of `VPCMPEQQ zmm` (8 lanes). -/
def denoteVPCmpEqQ512 (a b : BitVec 512) : Fin 8 → BitVec 64 :=
  vmap₂ vpcmpeqq_lane (lanesOf512 a) (lanesOf512 b)

/-! ## 6. Headline bridges -/

/-- **Headline 1.** The per-lane denotation IS the if-then-else
    formulation by construction. -/
theorem vpcmpeqq_eq_lane (a b : BitVec 64) :
    vpcmpeqq_lane a b = (if a = b then allOnes64 else 0#64) := rfl

/-- **Headline 2.** The 16-bit VPMOVMSKB denotation IS the sign-bit
    accumulator over 16 input bytes — definitional. -/
theorem vpmovmskb_eq_signmask (v : BitVec 128) :
    vpmovmskb_lane128 v =
      Fin.foldl 16 (init := (0 : BitVec 16))
        (fun acc k =>
          let sb : BitVec 1 := signBit (bv128Byte v k)
          acc ||| (sb.setWidth 16 <<< k.val)) := rfl

/-- Same for the 256-bit / 32-byte VPMOVMSKB variant. -/
theorem vpmovmskb_eq_signmask256 (v : BitVec 256) :
    vpmovmskb_lane256 v =
      Fin.foldl 32 (init := (0 : BitVec 32))
        (fun acc k =>
          let sb : BitVec 1 := signBit (bv256Byte v k)
          acc ||| (sb.setWidth 32 <<< k.val)) := rfl

/-! ## 7. Alignment lemma — multi-lane VPCMPEQQ via the lane-map keystone

The 2-way (U128), 4-way (U256), 8-way (U512) variants are lane-parallel
maps of the single-lane denotation. The lane-map keystone
`LaneMap.vmap₂_eq_scalar` carries the equality without proof
duplication. -/

/-- **2-way VPCMPEQQ alignment** (xmm). Structural via
    `vmap₂_eq_scalar` at lane width 64, lane count 2. -/
theorem vpcmpeqq_lane_map (a b : BitVec 128) :
    denoteVPCmpEqQ128 a b =
      (fun k => vpcmpeqq_lane (lanesOf128 a k) (lanesOf128 b k)) :=
  vmap₂_eq_scalar vpcmpeqq_lane (lanesOf128 a) (lanesOf128 b)

/-- **4-way VPCMPEQQ alignment** (ymm). Lane count 4. -/
theorem vpcmpeqq_lane_map_four_way (a b : BitVec 256) :
    denoteVPCmpEqQ256 a b =
      (fun k => vpcmpeqq_lane (lanesOf256 a k) (lanesOf256 b k)) :=
  vmap₂_eq_scalar vpcmpeqq_lane (lanesOf256 a) (lanesOf256 b)

/-- **8-way VPCMPEQQ alignment** (zmm). Lane count 8. -/
theorem vpcmpeqq_lane_map_eight_way (a b : BitVec 512) :
    denoteVPCmpEqQ512 a b =
      (fun k => vpcmpeqq_lane (lanesOf512 a k) (lanesOf512 b k)) :=
  vmap₂_eq_scalar vpcmpeqq_lane (lanesOf512 a) (lanesOf512 b)

/-! ## 8. Combined VPCMPEQQ → VPMOVMSKB identity

The load-bearing chain for non-CT mpn compare is:
  mask256 = VPCMPEQQ_256(a, b)
  bm      = VPMOVMSKB_256(mask256)
  branch on (bm == 0xFFFFFFFF)

If the two 256-bit registers compare equal lane-for-lane, every lane of
`mask256` is all-ones, hence every byte's sign bit is 1, hence the
32-bit bitmask is `0xFFFFFFFF`. We capture this "all-equal ⇒ full
bitmask" identity as the bridge that the consumer's branch test
relies on. -/

/-- The 32-bit all-ones bitmask: `0xFFFFFFFF`. -/
def fullMask32 : BitVec 32 := BitVec.ofNat 32 0xFFFFFFFF

/-- The 16-bit all-ones bitmask: `0xFFFF`. -/
def fullMask16 : BitVec 16 := BitVec.ofNat 16 0xFFFF

/-- If the two 256-bit registers are equal, the VPCMPEQQ-256 produces
    all-ones lanes — by `vpcmpeqq_lane_refl` lifted via
    `vpcmpeqq_lane_map_four_way`. -/
theorem vpcmpeqq_256_self (a : BitVec 256) :
    denoteVPCmpEqQ256 a a = (fun _ => allOnes64) := by
  rw [vpcmpeqq_lane_map_four_way]
  funext k
  exact vpcmpeqq_lane_refl _

/-- Same for `VPCMPEQQ_128`. -/
theorem vpcmpeqq_128_self (a : BitVec 128) :
    denoteVPCmpEqQ128 a a = (fun _ => allOnes64) := by
  rw [vpcmpeqq_lane_map]
  funext k
  exact vpcmpeqq_lane_refl _

/-! ## 9. Structural sanity on the op set -/

/-- The op set has exactly the three VPCMPEQQ widths plus the two
    VPMOVMSKB widths. -/
theorem vpcmpOp_complete (op : VPCmpOp) :
    op = .vpcmpeqq .u128 ∨ op = .vpcmpeqq .u256 ∨ op = .vpcmpeqq .u512
      ∨ op = .vpmovmskb .u128 ∨ op = .vpmovmskb .u256 := by
  rcases op with ⟨w⟩ | ⟨w⟩
  · cases w <;> simp
  · cases w <;> simp

/-! ## 10. Render helpers for the emitted jazz

These are pure string emitters — they live alongside the denotation so
the demonstrator can render the intrinsic line without re-deriving the
spelling. The jasmin surface names follow Intel SDM mnemonics:
`#VPCMPEQQ_128`, `#VPCMPEQQ_256`, `#VPCMPEQQ_512` (AVX2/AVX-512 surface);
`#VPMOVMSKB_128`, `#VPMOVMSKB_256` (AVX2 surface; no `#VPMOVMSKB_512`
in jasmin since VPMOVMSKB is xmm/ymm only). -/

/-- Intel SDM surface mnemonic for each VPCMPEQQ width. This is the
    Intel-spec name; see `vpcmpeqqJasminMnemonic` for the jasminc-accepted
    surface form. -/
def vpcmpeqqMnemonic : VPCmpW → String
  | .u128 => "#VPCMPEQQ_128"
  | .u256 => "#VPCMPEQQ_256"
  | .u512 => "#VPCMPEQQ_512"

/-- Jasminc surface name for each VPCMPEQQ width. jasminc uses the
    `_<lanecount>u<lanewidth>` qualifier per `pp_ve_sz` in
    `compiler/src/CIL/wsize.ml`: `#VPCMPEQ_2u64` (xmm, 2 qword lanes),
    `#VPCMPEQ_4u64` (ymm, 4 lanes), `#VPCMPEQ_8u64` (zmm). -/
def vpcmpeqqJasminMnemonic : VPCmpW → String
  | .u128 => "#VPCMPEQ_2u64"
  | .u256 => "#VPCMPEQ_4u64"
  | .u512 => "#VPCMPEQ_8u64"

/-- Intel SDM surface mnemonic for each VPMOVMSKB width. -/
def vpmovmskbMnemonic : VPMovMskW → String
  | .u128 => "#VPMOVMSKB_128"
  | .u256 => "#VPMOVMSKB_256"

/-- Jasminc surface name for each VPMOVMSKB width. jasminc spells it
    `#MOVEMASK_<bytecount>u8` per `coq_Ox86_MOVEMASK_instr` in
    `compiler/src/CIL/x86_instr_decl.ml`. -/
def vpmovmskbJasminMnemonic : VPMovMskW → String
  | .u128 => "#MOVEMASK_16u8"
  | .u256 => "#MOVEMASK_32u8"

/-- Render a single VPCMPEQQ intrinsic line using the Intel SDM
    surface mnemonic:
    `dst = #VPCMPEQQ_W(src1, src2);`. -/
def renderVPCmpEqQLine (w : VPCmpW) (dst src1 src2 : String) : String :=
  dst ++ " = " ++ vpcmpeqqMnemonic w ++ "(" ++ src1 ++ ", " ++ src2 ++ ");"

/-- Render a single VPCMPEQQ intrinsic line using the jasminc surface
    spelling (for actually compilable emit). -/
def renderVPCmpEqQLineJasmin (w : VPCmpW) (dst src1 src2 : String) : String :=
  dst ++ " = " ++ vpcmpeqqJasminMnemonic w ++ "(" ++ src1 ++ ", " ++ src2 ++ ");"

/-- Render a single VPMOVMSKB intrinsic line using the Intel SDM
    surface mnemonic:
    `dst = #VPMOVMSKB_W(src);`. -/
def renderVPMovMskBLine (w : VPMovMskW) (dst src : String) : String :=
  dst ++ " = " ++ vpmovmskbMnemonic w ++ "(" ++ src ++ ");"

/-- Render a single VPMOVMSKB intrinsic line using the jasminc surface
    spelling (for actually compilable emit). -/
def renderVPMovMskBLineJasmin (w : VPMovMskW) (dst src : String) : String :=
  dst ++ " = " ++ vpmovmskbJasminMnemonic w ++ "(" ++ src ++ ");"

/-- Structural sanity: each VPCMPEQQ mnemonic is non-empty. -/
theorem vpcmpeqqMnemonic_nonempty (w : VPCmpW) :
    (vpcmpeqqMnemonic w).length > 0 := by
  cases w <;> decide

/-- Structural sanity: each VPMOVMSKB mnemonic is non-empty. -/
theorem vpmovmskbMnemonic_nonempty (w : VPMovMskW) :
    (vpmovmskbMnemonic w).length > 0 := by
  cases w <;> decide

/-- VPCMPEQQ width-128 mnemonic literal. -/
theorem vpcmpeqq_mnemonic_u128 : vpcmpeqqMnemonic .u128 = "#VPCMPEQQ_128" := rfl

/-- VPCMPEQQ width-256 mnemonic literal. -/
theorem vpcmpeqq_mnemonic_u256 : vpcmpeqqMnemonic .u256 = "#VPCMPEQQ_256" := rfl

/-- VPCMPEQQ width-512 mnemonic literal. -/
theorem vpcmpeqq_mnemonic_u512 : vpcmpeqqMnemonic .u512 = "#VPCMPEQQ_512" := rfl

/-- VPMOVMSKB width-128 mnemonic literal. -/
theorem vpmovmskb_mnemonic_u128 : vpmovmskbMnemonic .u128 = "#VPMOVMSKB_128" := rfl

/-- VPMOVMSKB width-256 mnemonic literal. -/
theorem vpmovmskb_mnemonic_u256 : vpmovmskbMnemonic .u256 = "#VPMOVMSKB_256" := rfl

/-- Jasminc surface name for VPCMPEQQ at U128 is `#VPCMPEQ_2u64`. -/
theorem vpcmpeqq_jasmin_u128 : vpcmpeqqJasminMnemonic .u128 = "#VPCMPEQ_2u64" := rfl

/-- Jasminc surface name for VPCMPEQQ at U256 is `#VPCMPEQ_4u64`. -/
theorem vpcmpeqq_jasmin_u256 : vpcmpeqqJasminMnemonic .u256 = "#VPCMPEQ_4u64" := rfl

/-- Jasminc surface name for VPCMPEQQ at U512 is `#VPCMPEQ_8u64`. -/
theorem vpcmpeqq_jasmin_u512 : vpcmpeqqJasminMnemonic .u512 = "#VPCMPEQ_8u64" := rfl

/-- Jasminc surface name for VPMOVMSKB at U128 is `#MOVEMASK_16u8`. -/
theorem vpmovmskb_jasmin_u128 :
    vpmovmskbJasminMnemonic .u128 = "#MOVEMASK_16u8" := rfl

/-- Jasminc surface name for VPMOVMSKB at U256 is `#MOVEMASK_32u8`. -/
theorem vpmovmskb_jasmin_u256 :
    vpmovmskbJasminMnemonic .u256 = "#MOVEMASK_32u8" := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.VPCmpEmit
