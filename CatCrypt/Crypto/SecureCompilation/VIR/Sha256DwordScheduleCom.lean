/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
public import Mathlib.Data.List.Induction

/-!
# SHA-256 message-schedule expansion on the UNIFIED packed dword spec, BIT-EXACT

SIMD-dialect-unification companion to `Sha256DwordRoundCom.lean` (the
compression round on the packed `zmmPackD`/`zmmRorD` waist). This module supplies
the **message schedule** `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`
(FIPS-180-4 §6.2.2 step 1) over the same 16×u32 packed dword waist, and ties it
bit-exactly to the abstract `UInt32` FIPS-180-4 spec — model-free, reproducing
the abstract recurrence tie of the bespoke
`X86Backend/Sha256DwordScheduleRealization.lean` (`newScheduleWord` /
`newScheduleWord_bitExact`) on the verified-dialect waist.

## What is delivered

| result | content | bit-exact? |
|--------|---------|-----------|
| `sigma0Packed` / `sigma0Packed_lane` | packed `σ₀ = ρ⁷ ⊕ ρ¹⁸ ⊕ (≫3)`, lane-wise `smallSigma0D` | yes (width 32) |
| `sigma1Packed` / `sigma1Packed_lane` | packed `σ₁ = ρ¹⁷ ⊕ ρ¹⁹ ⊕ (≫10)`, lane-wise `smallSigma1D` | yes (width 32) |
| `newScheduleWordPacked` / `newScheduleWordPacked_lane` | packed schedule word, lane-wise `newScheduleWordLane` | yes |
| `newScheduleWordPacked_bitExact` | one packed lane `=` the abstract FIPS-180-4 recurrence word | **yes — FIPS-180-4** |
| `sha256DwordScheduleNPacked` / `..._lane` | the `N`-step `W[16..63]` expansion fold, per lane | yes (per step) |

## The packed waist

Each register is a `reg 512` ZMM holding 16 independent SHA-256 schedule lanes
(`16 × u32`, `zmmLane32`). The packed σ bodies are the verified-dialect
`zmmRorD n` (`VPRORD`, per-lane right rotate, wraps mod 32) xored with the
per-lane logical right shift `zmmPackD .shr a (bcastD k)` (`VPSRLD` by the
broadcast immediate `k`). `newScheduleWordPacked` chains four `zmmPackD .add`
(`VPADDD`) — the same op coverage as the round, **no new op**.

The lane lemmas reduce each packed op to its per-lane action via
`ZmmDwordLane.zmmPackD_lane` / `zmmRorD_lane` / `zmmOfLanes32_zmmLane32`, then
the bit-exact ties `Sha256DwordLane.smallSigma0_dword_bitExact` /
`smallSigma1_dword_bitExact` lift `newScheduleWordPacked_lane` to
`newScheduleWordPacked_bitExact` — the equal-strength reproduction of the
bespoke `newScheduleWord_bitExact`, with **no heavy `native_decide` over
`BitVec 512`** (lane-projection + the committed σ ties only).

## Scope

The packed spec quantifies over **every** `BitVec 512` and lane — no KAT, no
concrete state. The σ rotate/shift are the 32-bit dword ops (wrap mod
32, `VPSRLD`), so each tie is bit-exact at width 32. No jasminc, no
`jasminc_preserves_ct`.

## References
* FIPS 180-4 — Secure Hash Standard (§4.1.2 — `σ₀`/`σ₁`; §6.2.2 step 1 — the
  message schedule).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
open CatCrypt.Crypto.Primitives.SHA256 (smallSigma0 smallSigma1)

/-! ## 1. The broadcast shift-count register and its lane reader

The per-lane logical right shift `VPSRLD a, k` is the verified-dialect packed
op `zmmPackD .shr a (bcastD k)`, where `bcastD k` holds the immediate `k` in
every 32-bit lane. The lane reader gives `k` back. -/

/-- Broadcast a `u32` into all 16 lanes of a `reg 512` ZMM (the `VPSRLD`
    broadcast shift-count register). -/
def bcastD (n : BitVec 32) : BitVec 512 := zmmOfLanes32 (fun _ => n)

/-- Reading any lane of `bcastD n` recovers `n`. -/
@[simp] theorem bcastD_lane (n : BitVec 32) (k : Fin 16) :
    zmmLane32 (bcastD n) k = n := by
  unfold bcastD
  rw [zmmOfLanes32_zmmLane32]

/-! ## 2. The packed `σ₀` / `σ₁` schedule bodies and their lane ties

`σ₀(x) = ρ⁷(x) ⊕ ρ¹⁸(x) ⊕ (x ≫ 3)` and `σ₁(x) = ρ¹⁷(x) ⊕ ρ¹⁹(x) ⊕ (x ≫ 10)`
(FIPS-180-4 §4.1.2), each register a `reg 512` carrying 16 independent lanes. The
rotate is `zmmRorD` (`VPRORD`, per-lane mod-32 right rotate); the right shift is
`zmmPackD .shr · (bcastD k)` (`VPSRLD` by the broadcast immediate `k`). -/

/-- Packed `σ₀(x) = ρ⁷(x) ⊕ ρ¹⁸(x) ⊕ (x ≫ 3)` (16×u32, `zmmRorD`/`zmmPackD`). -/
def sigma0Packed (x : BitVec 512) : BitVec 512 :=
  zmmPackD .xor (zmmPackD .xor (zmmRorD 7 x) (zmmRorD 18 x))
    (zmmPackD .shr x (bcastD 3))

/-- Packed `σ₁(x) = ρ¹⁷(x) ⊕ ρ¹⁹(x) ⊕ (x ≫ 10)`. -/
def sigma1Packed (x : BitVec 512) : BitVec 512 :=
  zmmPackD .xor (zmmPackD .xor (zmmRorD 17 x) (zmmRorD 19 x))
    (zmmPackD .shr x (bcastD 10))

/-- **`sigma0Packed` is lane-wise `smallSigma0D`.** Reading lane `k` of the packed
    `σ₀` equals the dword-lane `σ₀` body `smallSigma0D` applied to lane `k` of the
    input — the `VPRORD`/`VPSRLD`/`VPXORD` ops act per 32-bit lane. -/
theorem sigma0Packed_lane (x : BitVec 512) (k : Fin 16) :
    zmmLane32 (sigma0Packed x) k = smallSigma0D (zmmLane32 x k) := by
  unfold sigma0Packed smallSigma0D
  rw [zmmPackD_lane, zmmPackD_lane, zmmRorD_lane, zmmRorD_lane, zmmPackD_lane,
    bcastD_lane]
  simp only [JasminBinOp.applyLane]
  rw [rorD_eq_rotateRight _ 7 (by norm_num), rorD_eq_rotateRight _ 18 (by norm_num),
    show ((3 : BitVec 32)).toNat = 3 from by decide]

/-- **`sigma1Packed` is lane-wise `smallSigma1D`.** -/
theorem sigma1Packed_lane (x : BitVec 512) (k : Fin 16) :
    zmmLane32 (sigma1Packed x) k = smallSigma1D (zmmLane32 x k) := by
  unfold sigma1Packed smallSigma1D
  rw [zmmPackD_lane, zmmPackD_lane, zmmRorD_lane, zmmRorD_lane, zmmPackD_lane,
    bcastD_lane]
  simp only [JasminBinOp.applyLane]
  rw [rorD_eq_rotateRight _ 17 (by norm_num), rorD_eq_rotateRight _ 19 (by norm_num),
    show ((10 : BitVec 32)).toNat = 10 from by decide]

/-! ## 3. The packed message-schedule word and its lane / bit-exact ties

The FIPS-180-4 §6.2.2 recurrence `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) +
W[t-16]`. The four schedule words enter as four `reg 512` ZMM registers
`w2 = W[t-2]`, `w7 = W[t-7]`, `w15 = W[t-15]`, `w16 = W[t-16]`; the word is the
chained `zmmPackD .add` (`VPADDD`) of `σ₁(w2) + w7 + σ₀(w15) + w16`. The operand
order matches the bespoke `newScheduleWord` (`σ₁ + W[t-7] + σ₀ + W[t-16]`). -/

/-- Packed `W[t] = σ₁(w2) + w7 + σ₀(w15) + w16` (four `zmmPackD .add`). -/
def newScheduleWordPacked (w2 w7 w15 w16 : BitVec 512) : BitVec 512 :=
  zmmPackD .add
    (zmmPackD .add (zmmPackD .add (sigma1Packed w2) w7) (sigma0Packed w15)) w16

/-- The bespoke dword-lane schedule word `σ₁(s14) + s9 + σ₀(s1) + s0` written
    directly on `BitVec 32` lanes (model-free; the `+` is per-lane mod-2³², the
    image of the bespoke `newScheduleWord`'s `laneAddD`). -/
def newScheduleWordLane (s14 s9 s1 s0 : BitVec 32) : BitVec 32 :=
  smallSigma1D s14 + s9 + smallSigma0D s1 + s0

/-- **`newScheduleWordPacked` is lane-wise the dword-lane schedule word.** Reading
    lane `k` of the packed schedule word equals the per-lane recurrence
    `σ₁(s14) + s9 + σ₀(s1) + s0` (with `s14 = W[t-2]`, `s9 = W[t-7]`,
    `s1 = W[t-15]`, `s0 = W[t-16]`) — the `VPADDD` is the per-lane mod-2³² add. -/
theorem newScheduleWordPacked_lane (w2 w7 w15 w16 : BitVec 512) (k : Fin 16) :
    zmmLane32 (newScheduleWordPacked w2 w7 w15 w16) k
      = newScheduleWordLane (zmmLane32 w2 k) (zmmLane32 w7 k)
          (zmmLane32 w15 k) (zmmLane32 w16 k) := by
  unfold newScheduleWordPacked newScheduleWordLane
  rw [zmmPackD_lane, zmmPackD_lane, zmmPackD_lane, sigma1Packed_lane,
    sigma0Packed_lane]
  simp only [JasminBinOp.applyLane]

/-- **The packed schedule word is BIT-EXACT to the abstract FIPS-180-4 recurrence.**
    With the four window words held as `UInt32`-bit-vectors in lane `k` of the four
    schedule registers, lane `k` of `newScheduleWordPacked` equals the bit-vector
    of `σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]` (`UInt32` adds, mod 2³²) — the
    FIPS-180-4 §6.2.2 schedule recurrence, bit-exact at width 32. This is the
    equal-strength reproduction of the bespoke `newScheduleWord_bitExact`, proved
    by lane-projection plus the committed σ ties (no `native_decide` over
    `BitVec 512`). -/
theorem newScheduleWordPacked_bitExact (w2 w7 w15 w16 : BitVec 512) (k : Fin 16)
    (wm2 wm7 wm15 wm16 : UInt32)
    (h2 : zmmLane32 w2 k = wm2.toBitVec) (h7 : zmmLane32 w7 k = wm7.toBitVec)
    (h15 : zmmLane32 w15 k = wm15.toBitVec) (h16 : zmmLane32 w16 k = wm16.toBitVec) :
    zmmLane32 (newScheduleWordPacked w2 w7 w15 w16) k
      = (smallSigma1 wm2 + wm7 + smallSigma0 wm15 + wm16).toBitVec := by
  rw [newScheduleWordPacked_lane, newScheduleWordLane, h2, h7, h15, h16,
    smallSigma1_dword_bitExact, smallSigma0_dword_bitExact]
  simp only [UInt32.toBitVec_add]

/-! ## 4. The `N`-step `W[16..63]` expansion fold (packed, per lane)

The full schedule expansion is 48 steps. We model the 16 most-recent schedule
words as a packed ring buffer of 16 `reg 512` registers and fold one expansion
step. The fold is the mechanical induction over the per-step
`newScheduleWordPacked_lane` tie; each step is bit-exact per lane (the lane is
`BitVec 32`, no width caveat). -/

/-- The 16 most-recent packed schedule registers `s0 = W[t-16], …, s15 = W[t-1]`. -/
structure PackedSched16 where
  s0  : BitVec 512
  s1  : BitVec 512
  s2  : BitVec 512
  s3  : BitVec 512
  s4  : BitVec 512
  s5  : BitVec 512
  s6  : BitVec 512
  s7  : BitVec 512
  s8  : BitVec 512
  s9  : BitVec 512
  s10 : BitVec 512
  s11 : BitVec 512
  s12 : BitVec 512
  s13 : BitVec 512
  s14 : BitVec 512
  s15 : BitVec 512

/-- One packed ring-buffer expansion step: form `W[t] = σ₁(s14) + s9 + σ₀(s1) +
    s0` (the FIPS-180-4 recurrence, `s14 = W[t-2]`, `s9 = W[t-7]`, `s1 = W[t-15]`,
    `s0 = W[t-16]`) and shift the window left, appending `W[t]` at `s15`. -/
def onePackedScheduleStep (w : PackedSched16) : PackedSched16 :=
  { s0 := w.s1, s1 := w.s2, s2 := w.s3, s3 := w.s4, s4 := w.s5, s5 := w.s6
  , s6 := w.s7, s7 := w.s8, s8 := w.s9, s9 := w.s10, s10 := w.s11, s11 := w.s12
  , s12 := w.s13, s13 := w.s14, s14 := w.s15
  , s15 := newScheduleWordPacked w.s14 w.s9 w.s1 w.s0 }

/-- The lane-level (`BitVec 32`) schedule window — the per-lane image of a packed
    window (model-free). -/
structure LaneSched16 where
  s0  : BitVec 32
  s1  : BitVec 32
  s2  : BitVec 32
  s3  : BitVec 32
  s4  : BitVec 32
  s5  : BitVec 32
  s6  : BitVec 32
  s7  : BitVec 32
  s8  : BitVec 32
  s9  : BitVec 32
  s10 : BitVec 32
  s11 : BitVec 32
  s12 : BitVec 32
  s13 : BitVec 32
  s14 : BitVec 32
  s15 : BitVec 32

/-- One lane-level ring-buffer step: form `newScheduleWordLane` and shift left. -/
def oneLaneScheduleStep (w : LaneSched16) : LaneSched16 :=
  { s0 := w.s1, s1 := w.s2, s2 := w.s3, s3 := w.s4, s4 := w.s5, s5 := w.s6
  , s6 := w.s7, s7 := w.s8, s8 := w.s9, s9 := w.s10, s10 := w.s11, s11 := w.s12
  , s12 := w.s13, s13 := w.s14, s14 := w.s15
  , s15 := newScheduleWordLane w.s14 w.s9 w.s1 w.s0 }

/-- The lane-`k` window read off a packed window. -/
def laneSched16 (k : Fin 16) (w : PackedSched16) : LaneSched16 :=
  { s0 := zmmLane32 w.s0 k, s1 := zmmLane32 w.s1 k, s2 := zmmLane32 w.s2 k
  , s3 := zmmLane32 w.s3 k, s4 := zmmLane32 w.s4 k, s5 := zmmLane32 w.s5 k
  , s6 := zmmLane32 w.s6 k, s7 := zmmLane32 w.s7 k, s8 := zmmLane32 w.s8 k
  , s9 := zmmLane32 w.s9 k, s10 := zmmLane32 w.s10 k, s11 := zmmLane32 w.s11 k
  , s12 := zmmLane32 w.s12 k, s13 := zmmLane32 w.s13 k, s14 := zmmLane32 w.s14 k
  , s15 := zmmLane32 w.s15 k }

/-- **One packed step realizes one lane step.** Projecting lane `k` after one
    packed expansion step equals `oneLaneScheduleStep` of the lane-`k` window —
    the new word lane-`k` is `newScheduleWordLane` (per `newScheduleWordPacked_lane`),
    the window shifts identically. -/
theorem onePackedScheduleStep_lane (w : PackedSched16) (k : Fin 16) :
    laneSched16 k (onePackedScheduleStep w)
      = oneLaneScheduleStep (laneSched16 k w) := by
  unfold laneSched16 onePackedScheduleStep oneLaneScheduleStep
  simp only [newScheduleWordPacked_lane]

/-- The `N`-step packed schedule fold. -/
def sha256DwordScheduleNPacked (steps : List Unit) (w : PackedSched16) : PackedSched16 :=
  steps.foldl (fun w _ => onePackedScheduleStep w) w

/-- The `N`-step lane-level schedule fold. -/
def sha256DwordScheduleNLane (steps : List Unit) (w : LaneSched16) : LaneSched16 :=
  steps.foldl (fun w _ => oneLaneScheduleStep w) w

/-- **The `N`-step packed schedule expansion realizes the `N`-step lane fold.** For
    every step list (length `N`) and lane `k`, projecting lane `k` after the
    `N`-step packed expansion equals the `N`-fold lane-level schedule of the
    lane-`k` window. Bit-exact per step (the lane is `BitVec 32`). Proved by
    induction on `N` (`List.reverseRecOn`): the last step is
    `onePackedScheduleStep_lane`. -/
theorem sha256DwordScheduleNPacked_lane (steps : List Unit) (w : PackedSched16)
    (k : Fin 16) :
    laneSched16 k (sha256DwordScheduleNPacked steps w)
      = sha256DwordScheduleNLane steps (laneSched16 k w) := by
  induction steps using List.reverseRecOn generalizing w with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [sha256DwordScheduleNPacked, sha256DwordScheduleNLane,
      List.foldl_append, List.foldl_cons, List.foldl_nil] at *
    rw [onePackedScheduleStep_lane, ih]

/-- A 48-element step list — the full `W[16..63]` SHA-256 message expansion. -/
def sha256DwordSchedule48 : List Unit := List.replicate 48 ()

/-- **The full 48-step packed message-schedule expansion realization.** The
    general-`N` realization specialized to 48 steps — the bit-exact 32-bit
    `W[16..63]` expansion (each step bit-exact, no width caveat), per lane. -/
theorem sha256DwordSchedule48Packed_lane (w : PackedSched16) (k : Fin 16) :
    laneSched16 k (sha256DwordScheduleNPacked sha256DwordSchedule48 w)
      = sha256DwordScheduleNLane sha256DwordSchedule48 (laneSched16 k w) :=
  sha256DwordScheduleNPacked_lane sha256DwordSchedule48 w k

end CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom
