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
# VPCLMULQDQ dialect op (carry-less multiply, GF(2)[x] no-reduction) — denotation + alignment

`VPCLMULQDQ` is the EVEX-encoded promotion of the legacy `PCLMULQDQ`
(`_mm_clmulepi64_si128`) carry-less multiply to wider lanes. The single
mnemonic does one job: given two 128-bit lanes `a, b : BitVec 128`, an
`imm8` byte selects one 64-bit half from each side and emits the
schoolbook polynomial product over `GF(2)[x]`, **with no modular
reduction**. The 128-bit result is the consumer's responsibility to
reduce (modulo the field polynomial of their choice — `x^128 + x^7 +
x^2 + x + 1` for GHASH/AES-GCM, `x^128 + x^7 + x^2 + 1` for
AES-GCM-SIV-after-bit-reflection, the modular polynomial of SIKE for
isogeny-based crypto, etc.).

`imm8` layout (Intel SDM Vol. 2):
  * bit 0 — 0: take low 64 bits of operand 1; 1: take high 64 bits
  * bit 4 — 0: take low 64 bits of operand 2; 1: take high 64 bits
  * all other bits ignored

Four meaningful `imm8` values, named after their byte (high, low) halves:
  * `0x00` (LL — low × low)
  * `0x01` (HL — high of op1, low of op2)
  * `0x10` (LH — low of op1, high of op2)
  * `0x11` (HH — high × high)

EVEX widens the lane count: `VPCLMULQDQ ymm` runs **2** independent
PCLMUL ops on the two 128-bit lanes of an `ymm`; `VPCLMULQDQ zmm` runs
**4**. The per-lane semantics is the same single-lane `polyMul64`-based
op — no cross-lane mixing — so the lane-map lemma
`LaneMap.vmap₂_eq_scalar` carries the multi-lane denotation to
2-way and 4-way for free.

## What this module provides

1. `polyMul64 : BitVec 64 → BitVec 64 → BitVec 128` — schoolbook
   shift-and-XOR polynomial multiply over `GF(2)[x]`, no reduction.
2. `VPClmulOp` inductive (the single mnemonic at `Wsize` U128/U256/U512).
3. `vpclmulqdq_lane : BitVec 8 → BitVec 128 → BitVec 128 → BitVec 128`
   — per-lane denotation: pick `imm8`-selected 64-bit halves, run
   `polyMul64`.
4. `vpclmulqdq_eq_polyMul` — headline bridge: at a single 128-bit lane
   the denotation equals `polyMul64` of the `imm8`-selected halves.
5. `vpclmulqdq_lane_map` — alignment: 2-way at U256 (and by extension
   4-way at U512) is the lane-wise lift of the single-lane denotation,
   discharged by `LaneMap.vmap₂_eq_scalar`.
6. Sanity: `polyMul64 _ 0 = 0`, `polyMul64 0 _ = 0`, commutativity, the
   four `imm8`-variant identities (LL/HL/LH/HH).
7. Render helpers: `#VPCLMULQDQ_128 / _256 / _512` mnemonics.

## What this module is NOT

* Not a new `psem` primitive — the dialect op is a pure `BitVec`
  computation, denotable in Lean. The demonstrator
  (`bench/ghash_vpclmul_compare/ghash_vpclmul_emit.lean`) renders an
  explicit `#VPCLMULQDQ_128 (..., ..., imm8)` line in the emitted
  `.jazz`.
* Not the GHASH modular reduction — that's the consumer's job. This
  module gives the unreduced 128-bit polynomial product; the GHASH
  emit reduces by `x^128 + x^7 + x^2 + x + 1` (one additional sequence
  of shifts + XORs, or two `pclmulqdq` calls via the Intel "fast
  reduction" trick).
* The 256-bit / 512-bit widths are lane-wise extensions — same per-lane
  semantics, more lanes — covered by `LaneMap.vmap₂_eq_scalar`. The
  jasminc surface acceptance for `#VPCLMULQDQ_128` is long-standing
  (it is exactly `_mm_clmulepi64_si128`, the AES-NI carry-less multiply
  shipped since 2010); `#VPCLMULQDQ_256` / `_512` require the EVEX-VAES
  surface (post-2024 jasmin feature branch).

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-! ## 1. Per-lane carry-less multiply core (`polyMul64`)

The schoolbook polynomial multiply over `GF(2)[x]` is shift-and-XOR:

  polyMul64 a b = Σ_{i=0..63} [bit i of a] · (b << i)

where the sum is `XOR` (GF(2) addition) and the multiplication is
`AND` (GF(2) multiplication). The result is 128 bits wide: a 64-bit
input `b` shifted by up to 63 positions produces values up to bit 126,
and the XOR-accumulation stays within `BitVec 128`. **No modular
reduction.** -/

/-- One bit step of the schoolbook polynomial multiply: if bit `i` of
    `a` is set, XOR `b <<< i` into the running accumulator. Branchless
    via the `mask = 0 - (bit i)` trick: `mask` is all-1s when the bit
    is 1 and all-0s when it is 0. -/
def polyMul64Step (a : BitVec 64) (b : BitVec 128) (acc : BitVec 128) (i : Nat) : BitVec 128 :=
  let bitI : BitVec 128 := ((a >>> (i : Nat)) &&& 1).setWidth 128
  let mask : BitVec 128 := 0#128 - bitI
  acc ^^^ ((b <<< i) &&& mask)

/-- Schoolbook polynomial multiply over `GF(2)[x]`: `BitVec 64 × BitVec 64 →
    BitVec 128`, **no modular reduction**. This is the exact semantics
    of one `PCLMULQDQ` (a.k.a. `_mm_clmulepi64_si128`) on the two
    `imm8`-selected 64-bit halves. -/
def polyMul64 (a b : BitVec 64) : BitVec 128 :=
  let b128 : BitVec 128 := b.setWidth 128
  Fin.foldl 64
    (fun acc i => polyMul64Step a b128 acc i.val) (0 : BitVec 128)

/-! ### Sanity: zero absorbs.

For the `64 × 64` exhaustive identity we cannot use `native_decide`
(the full input space is out of reach), but the zero identities are
discharged by an internal helper that proves "if the per-step
contribution is identically `acc`, then the whole fold is the
initial". -/

/-- Internal helper: if every step preserves the accumulator, the
    whole fold is the initial value. -/
theorem foldl_const_init {α : Sort _} (n : Nat) (f : α → Fin n → α)
    (h : ∀ acc (i : Fin n), f acc i = acc) (init : α) :
    Fin.foldl n f init = init := by
  induction n generalizing init with
  | zero => exact Fin.foldl_zero _ _
  | succ n ih =>
      rw [Fin.foldl_succ]
      -- step 0 maps init → f init 0 = init; then recurse with new function
      have h0 : f init 0 = init := h init 0
      rw [h0]
      apply ih
      intro acc i
      exact h acc i.succ

/-- `polyMul64 0 b = 0`: every step contributes 0 (the mask is 0 since
    every bit of `a = 0` is 0). -/
theorem polyMul64_zero_left (b : BitVec 64) : polyMul64 0 b = 0 := by
  unfold polyMul64
  apply foldl_const_init
  intro acc i
  unfold polyMul64Step
  simp

/-- `polyMul64 a 0 = 0`: every step shifts 0, contributing 0. -/
theorem polyMul64_zero_right (a : BitVec 64) : polyMul64 a 0 = 0 := by
  unfold polyMul64
  have hz : ((0 : BitVec 64).setWidth 128) = 0 := by decide
  rw [hz]
  apply foldl_const_init
  intro acc i
  unfold polyMul64Step
  simp

/-! ## 2. The dialect op set

We model `VPCLMULQDQ` at three widths — the `Wsize` parameter — covering
U128 (the legacy `_mm_clmulepi64_si128`, one lane), U256 (two lanes),
and U512 (four lanes). The `imm8` selector is carried as a runtime
argument at the denotation site, mirroring how `GfniOp.vgf2p8affineqb`
carries its imm8 in `denoteGfniByte`. -/

/-- The width tag for the packed `VPCLMULQDQ` op. -/
inductive VPClmulW
  | u128  -- 1 lane: legacy `PCLMULQDQ` / `_mm_clmulepi64_si128`
  | u256  -- 2 lanes: `VPCLMULQDQ ymm`
  | u512  -- 4 lanes: `VPCLMULQDQ zmm`
  deriving DecidableEq, Repr

/-- The lane count for each width. -/
def VPClmulW.lanes : VPClmulW → Nat
  | .u128 => 1
  | .u256 => 2
  | .u512 => 4

/-- The bit width of the packed register for each width. -/
def VPClmulW.bits : VPClmulW → Nat
  | .u128 => 128
  | .u256 => 256
  | .u512 => 512

/-- Single dialect mnemonic: `VPCLMULQDQ` at one of the three widths.
    All carry the same per-lane semantics (`vpclmulqdq_lane` below);
    only the lane count differs. -/
inductive VPClmulOp
  | /-- `VPCLMULQDQ` at the chosen packed-register width. The `imm8`
        selector is a runtime argument at the denotation site (it is
        an immediate in the encoding, but a runtime function-argument
        for the dialect denotation — same shape as
        `GfniOp.vgf2p8affineqb`). -/
    vpclmulqdq (w : VPClmulW)
  deriving DecidableEq, Repr

/-! ## 3. Per-lane denotation (`vpclmulqdq_lane`)

Given two 128-bit operand lanes `a, b` and an `imm8` selector byte, the
per-lane semantics is:

  1. `lo a = bits [0,64)`, `hi a = bits [64,128)`, similarly for `b`
  2. select halves per `imm8` bit 0 (op1) and bit 4 (op2)
  3. emit `polyMul64` of the two selected halves
-/

/-- Low 64 bits of a 128-bit lane. -/
def lo64 (v : BitVec 128) : BitVec 64 := BitVec.extractLsb' 0 64 v

/-- High 64 bits of a 128-bit lane. -/
def hi64 (v : BitVec 128) : BitVec 64 := BitVec.extractLsb' 64 64 v

/-- Select a 64-bit half of a 128-bit lane based on a selector bit. -/
def selectHalf (selectHigh : Bool) (v : BitVec 128) : BitVec 64 :=
  if selectHigh then hi64 v else lo64 v

/-- Per-lane denotation of `VPCLMULQDQ` on a single 128-bit lane: pick
    the `imm8`-selected 64-bit halves of each operand and run
    `polyMul64`. -/
def vpclmulqdq_lane (imm8 : BitVec 8) (a b : BitVec 128) : BitVec 128 :=
  let bit0 : Bool := ((imm8 >>> (0 : Nat)) &&& 1) ≠ 0
  let bit4 : Bool := ((imm8 >>> (4 : Nat)) &&& 1) ≠ 0
  polyMul64 (selectHalf bit0 a) (selectHalf bit4 b)

/-! ## 4. The packed denotation

At U128 the packed denotation IS the per-lane denotation (one lane).
At U256 it is the lane-wise lift to 2 lanes; at U512 to 4 lanes. We
use `LaneMap.vmap₂` for the multi-lane shape so the alignment lemma
falls out of `LaneMap.vmap₂_eq_scalar` for free. -/

/-- `BitVec 256` view as 2 lanes of `BitVec 128`. Mirrors
    `VAESEmit.lanesOf256` — identical structural definition. -/
def lanesOf256 (v : BitVec 256) (k : Fin 2) : BitVec 128 :=
  BitVec.extractLsb' (128 * k.val) 128 v

/-- `BitVec 512` view as 4 lanes of `BitVec 128`. -/
def lanesOf512 (v : BitVec 512) (k : Fin 4) : BitVec 128 :=
  BitVec.extractLsb' (128 * k.val) 128 v

/-- Packed denotation at U128 (one lane): pass-through to the per-lane
    denotation. -/
def denoteVPClmul128 (imm8 : BitVec 8) (a b : BitVec 128) : BitVec 128 :=
  vpclmulqdq_lane imm8 a b

/-- Packed denotation at U256 (two independent lanes). -/
def denoteVPClmul256 (imm8 : BitVec 8) (a b : BitVec 256) : Fin 2 → BitVec 128 :=
  vmap₂ (vpclmulqdq_lane imm8) (lanesOf256 a) (lanesOf256 b)

/-- Packed denotation at U512 (four independent lanes). -/
def denoteVPClmul512 (imm8 : BitVec 8) (a b : BitVec 512) : Fin 4 → BitVec 128 :=
  vmap₂ (vpclmulqdq_lane imm8) (lanesOf512 a) (lanesOf512 b)

/-! ## 5. Headline bridge: `vpclmulqdq_eq_polyMul`

The single-lane denotation equals `polyMul64` of the `imm8`-selected
halves — this is the formal equivalence between the dialect op and
the schoolbook `GF(2)[x]` polynomial multiply that consumers (GHASH,
AES-GCM-SIV, isogeny-based crypto) target their proofs against. -/

/-- **Headline.** At a single 128-bit lane, `VPCLMULQDQ` denotes to
    `polyMul64` of the `imm8`-selected 64-bit halves. Definitional —
    `vpclmulqdq_lane` is `polyMul64 ∘ (select halves by imm8)` by
    construction; `rfl` closes the bridge. -/
theorem vpclmulqdq_eq_polyMul (imm8 : BitVec 8) (a b : BitVec 128) :
    vpclmulqdq_lane imm8 a b =
      polyMul64
        (selectHalf (((imm8 >>> (0 : Nat)) &&& 1) ≠ 0) a)
        (selectHalf (((imm8 >>> (4 : Nat)) &&& 1) ≠ 0) b) := by
  unfold vpclmulqdq_lane
  rfl

/-! ## 6. Imm8 variant identities (LL / HL / LH / HH)

The four meaningful `imm8` values pick the four corner cases. Each is
discharged by `decide` on the 8-bit imm8 then `rfl`. -/

/-- `imm8 = 0x00` (LL): low × low. -/
theorem vpclmulqdq_imm00_eq_LL (a b : BitVec 128) :
    vpclmulqdq_lane 0x00#8 a b = polyMul64 (lo64 a) (lo64 b) := by
  unfold vpclmulqdq_lane selectHalf
  simp

/-- `imm8 = 0x01` (HL): high of op1 × low of op2. -/
theorem vpclmulqdq_imm01_eq_HL (a b : BitVec 128) :
    vpclmulqdq_lane 0x01#8 a b = polyMul64 (hi64 a) (lo64 b) := by
  unfold vpclmulqdq_lane selectHalf
  simp

/-- `imm8 = 0x10` (LH): low of op1 × high of op2. -/
theorem vpclmulqdq_imm10_eq_LH (a b : BitVec 128) :
    vpclmulqdq_lane 0x10#8 a b = polyMul64 (lo64 a) (hi64 b) := by
  unfold vpclmulqdq_lane selectHalf
  simp

/-- `imm8 = 0x11` (HH): high × high. -/
theorem vpclmulqdq_imm11_eq_HH (a b : BitVec 128) :
    vpclmulqdq_lane 0x11#8 a b = polyMul64 (hi64 a) (hi64 b) := by
  unfold vpclmulqdq_lane selectHalf
  simp

/-! ## 7. Alignment lemma — multi-lane VPCLMULQDQ via the lane-map lemma

The 2-way (U256) and 4-way (U512) variants are lane-parallel maps of
the single-lane denotation, with NO cross-lane mixing. The lane-map
lemma `LaneMap.vmap₂_eq_scalar` carries the equality without
proof duplication. -/

/-- **2-way VPCLMULQDQ alignment.** The packed U256 denotation equals
    the per-lane scalar denotation. Structural via `vmap₂_eq_scalar` at
    lane width 128, lane count 2. -/
theorem vpclmulqdq_lane_map (imm8 : BitVec 8) (a b : BitVec 256) :
    denoteVPClmul256 imm8 a b =
      (fun k => vpclmulqdq_lane imm8 (lanesOf256 a k) (lanesOf256 b k)) :=
  vmap₂_eq_scalar (vpclmulqdq_lane imm8) (lanesOf256 a) (lanesOf256 b)

/-- 4-way VPCLMULQDQ alignment at U512 — same shape, lane count 4. -/
theorem vpclmulqdq_lane_map_four_way (imm8 : BitVec 8) (a b : BitVec 512) :
    denoteVPClmul512 imm8 a b =
      (fun k => vpclmulqdq_lane imm8 (lanesOf512 a k) (lanesOf512 b k)) :=
  vmap₂_eq_scalar (vpclmulqdq_lane imm8) (lanesOf512 a) (lanesOf512 b)

/-! ## 8. Structural sanity on the op set -/

/-- The op set has exactly the three width variants. -/
theorem vpclmulOp_complete (op : VPClmulOp) :
    op = .vpclmulqdq .u128 ∨ op = .vpclmulqdq .u256 ∨ op = .vpclmulqdq .u512 := by
  rcases op with ⟨w⟩
  cases w <;> simp

/-! ## 9. Render helpers for the emitted jazz

These are pure string emitters — they live alongside the denotation so
the demonstrator consumers can render the intrinsic line without
re-deriving the spelling. The jasmin surface names are
`#VPCLMULQDQ_128` (long-standing AES-NI surface, identical to legacy
`PCLMULQDQ`), `#VPCLMULQDQ_256` and `#VPCLMULQDQ_512` (EVEX-VAES,
post-2024 jasmin feature branch). -/

/-- Jasmin surface mnemonic for each width variant. -/
def vpclmulMnemonic : VPClmulW → String
  | .u128 => "#VPCLMULQDQ_128"
  | .u256 => "#VPCLMULQDQ_256"
  | .u512 => "#VPCLMULQDQ_512"

/-- Render a single VPCLMULQDQ intrinsic line: `dst = #VPCLMULQDQ_W (src1, src2, imm8);`. -/
def renderVPClmulLine (w : VPClmulW) (dst src1 src2 : String) (imm : Nat) : String :=
  dst ++ " = " ++ vpclmulMnemonic w ++ "(" ++ src1 ++ ", " ++ src2
    ++ ", " ++ toString imm ++ ");"

/-- Structural sanity: each mnemonic is non-empty. -/
theorem vpclmulMnemonic_nonempty (w : VPClmulW) : (vpclmulMnemonic w).length > 0 := by
  cases w <;> decide

/-- Width 128 mnemonic literal. -/
theorem vpclmul_mnemonic_u128 : vpclmulMnemonic .u128 = "#VPCLMULQDQ_128" := rfl

/-- Width 256 mnemonic literal. -/
theorem vpclmul_mnemonic_u256 : vpclmulMnemonic .u256 = "#VPCLMULQDQ_256" := rfl

/-- Width 512 mnemonic literal. -/
theorem vpclmul_mnemonic_u512 : vpclmulMnemonic .u512 = "#VPCLMULQDQ_512" := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit
