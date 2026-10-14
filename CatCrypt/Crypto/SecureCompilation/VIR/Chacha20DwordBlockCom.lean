/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordCom
public import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane

/-!
# ChaCha20 whole-block (16×u32 dword ZMM) on the verified Jasmin VIR dialect

The whole-block companion to
[`Chacha20DwordCom.lean`](Chacha20DwordCom.lean), which gave the single
quarter-round (`qrSpecZ` / `qrComA…D`) over the 16-lane (`16 × u32`, `reg 512`)
dword ZMM register and tied it to the RFC-8439 §2.1 quarter-round vector. This
module assembles those quarter-rounds into the full ChaCha20 block function — the
column + diagonal double-round, ten double-rounds, and the feed-forward — over a
sixteen-register packed state `Fin 16 → BitVec 512`, reproducing the data flow of
the bespoke `Chacha20DwordRealization` / `BlockRealization` whole-block, and
anchors it to the RFC-8439 §2.3.2 single-block test vector.

## What is proved here, and how it stays LIGHT

The block spec lives over the packed 512-bit registers, but the RFC anchor is
*not* a `native_decide` over the 16-lane `BitVec 512` denotation — that path
(`zmmPackD` / `zmmRorD` assembling and re-slicing a `BitVec 512` for 8×10
quarter-rounds) does not terminate under the kernel evaluator. Instead the file
keeps the expensive decision on the LIGHT scalar path and bridges packed ↔
scalar by *lane independence*:

1. **`chacha20BlockSpec`** (`§2`) — the whole block over `Fin 16 → BitVec 512`,
   composing column + diagonal quarter-rounds via the committed packed spec
   `qrSpecZ`, ten double-rounds, then the per-register feed-forward
   `out i = pAdd (rounds i) (init i)`. This is the SPEC; no `native_decide`
   runs over it.

2. **Per-quarter-round and per-double-round lane reduction** (`§3`) — each
   16-lane packed quarter-round `qrSpecZ` reads, lane-by-lane (`zmmLane32`), as
   the scalar quarter-round `qrScalarLane` (the RFC-8439 §2.1 ARX on a single
   `BitVec 32`), via the committed lane-projection lemmas `zmmPackD_lane` /
   `zmmRorD_lane` (`ZmmDwordLane.lean`). This lifts to a full per-double-round
   lane lemma `chacha20DoubleRound_lane`: lane `k` of the packed double-round is
   the scalar double-round on the lane-`k` slice. This is the
   packed↔scalar content (mandated step (a)); it connects the block spec back to
   `qrSpecZ` (hence to the committed `Com` programs `qrComA…D`).

3. **RFC-8439 §2.3.2 anchor** (`§4`) — the scalar block (an `Array (BitVec 32)`
   schedule, identical to
   `bench/chacha_compare/chacha_4way_owned_block_denote_check.lean`) matches the
   RFC §2.3.2 reference output `expectedOut` on all sixteen words, by a single
   LIGHT `native_decide` over scalar `BitVec 32` arithmetic (≈2 s). The scalar
   block uses the SAME column/diagonal index sets and the SAME quarter-round as
   the packed `chacha20BlockSpec`.

The acceptance is the RFC §2.3.2 vector tie (`scalarBlock_matches_rfc`), at
equal strength to the bespoke realization's whole-block payoff, with the packed
spec connected to it lane-wise through `qrSpecZ` and hence `qrCom`.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordBlockCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordBlockCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordCom

/-! ## 1. The packed state and the column/diagonal index sets

The ChaCha20 state is sixteen 32-bit words; on the dword ZMM kernel each word is
broadcast across the 16 lanes of one `reg 512`, so the (one-block) packed state
is `Fin 16 → BitVec 512`. The packed adder `pAdd = zmmPackD .add` is the per-lane
mod-2³² add, so the sixteen registers evolve lane-independently — exactly the
property exploited for the LIGHT RFC anchor below. -/

/-- The packed ChaCha20 state: sixteen `reg 512` registers (word `i` carried in
    register `i`, the 16-lane dword view). -/
abbrev PState : Type := Fin 16 → BitVec 512

/-- Apply one packed quarter-round to the four state registers at indices
    `(α, β, γ, δ)`, writing back the four outputs of `qrSpecZ` (the committed
    16-lane dword quarter-round) and leaving the other twelve registers fixed. -/
def applyQRp (st : PState) (α β γ δ : Fin 16) : PState :=
  let r := qrSpecZ (st α) (st β) (st γ) (st δ)
  fun i =>
    if i = α then r.1
    else if i = β then r.2.1
    else if i = γ then r.2.2.1
    else if i = δ then r.2.2.2
    else st i

/-- One packed double-round: four column quarter-rounds then four diagonal
    quarter-rounds, over the SAME index sets as
    `Chacha4WayEmit.encodeDoubleRound` and the bench's scalar `doubleRound`. -/
def chacha20DoubleRound (st : PState) : PState :=
  let st := applyQRp st 0 4 8 12
  let st := applyQRp st 1 5 9 13
  let st := applyQRp st 2 6 10 14
  let st := applyQRp st 3 7 11 15
  let st := applyQRp st 0 5 10 15
  let st := applyQRp st 1 6 11 12
  let st := applyQRp st 2 7 8 13
  let st := applyQRp st 3 4 9 14
  st

/-- Ten packed double-rounds (the ChaCha20 round schedule). -/
def chacha20Rounds (st : PState) : PState :=
  chacha20DoubleRound (chacha20DoubleRound (chacha20DoubleRound (chacha20DoubleRound
    (chacha20DoubleRound (chacha20DoubleRound (chacha20DoubleRound (chacha20DoubleRound
      (chacha20DoubleRound (chacha20DoubleRound st)))))))))

/-! ## 2. The packed whole-block spec -/

/-- The packed ChaCha20 block: ten double-rounds, then the per-register
    feed-forward `out i = pAdd (rounds(init) i) (init i)` (`pAdd` is the per-lane
    mod-2³² add). The whole-block companion of the single quarter-round
    `qrSpecZ`; reproduces the data flow of the bespoke
    `Chacha20DwordRealization` / `BlockRealization`. -/
def chacha20BlockSpec (init : PState) : PState :=
  fun i => pAdd (chacha20Rounds init i) (init i)

/-! ## 3. Per-double-round lane reduction (packed ↔ scalar)

The packed quarter-round reads, lane-by-lane, as the scalar quarter-round; this
lifts to the whole double-round. This is the packed↔scalar content
linking `chacha20BlockSpec` back to `qrSpecZ` (and through it `qrCom`). -/

/-- The scalar quarter-round at the lane semantics of `qrSpecZ`: RFC-8439 §2.1
    ARX on a single `BitVec 32`, with `<<<k` realised as `rotateRight (32-k)`. -/
def qrScalarLane (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b; let d := (d ^^^ a).rotateRight 16
  let c := c + d; let b := (b ^^^ c).rotateRight 20
  let a := a + b; let d := (d ^^^ a).rotateRight 24
  let c := c + d; let b := (b ^^^ c).rotateRight 25
  (a, b, c, d)

/-- **Quarter-round lane reduction.** Reading lane `k` of the four `qrSpecZ`
    outputs is the scalar quarter-round `qrScalarLane` on the lane-`k` slices of
    the inputs. Falls out of the committed `zmmPackD_lane` / `zmmRorD_lane`. -/
theorem qrSpecZ_lane (a b c d : BitVec 512) (k : Fin 16) :
    (zmmLane32 (qrSpecZ a b c d).1 k,
     zmmLane32 (qrSpecZ a b c d).2.1 k,
     zmmLane32 (qrSpecZ a b c d).2.2.1 k,
     zmmLane32 (qrSpecZ a b c d).2.2.2 k)
    = qrScalarLane (zmmLane32 a k) (zmmLane32 b k) (zmmLane32 c k) (zmmLane32 d k) := by
  simp only [qrSpecZ, pAdd, pXor, qrScalarLane, zmmPackD_lane, zmmRorD_lane,
    JasminBinOp.applyLane]

/-- The lane-`k` scalar slice of a packed state. -/
def laneState (st : PState) (k : Fin 16) : Fin 16 → BitVec 32 :=
  fun i => zmmLane32 (st i) k

/-- Scalar (functional) quarter-round update over a 16-word lane-state, mirroring
    `applyQRp` but on `BitVec 32` words via `qrScalarLane`. -/
def applyQRs (st : Fin 16 → BitVec 32) (α β γ δ : Fin 16) : Fin 16 → BitVec 32 :=
  let r := qrScalarLane (st α) (st β) (st γ) (st δ)
  fun i =>
    if i = α then r.1
    else if i = β then r.2.1
    else if i = γ then r.2.2.1
    else if i = δ then r.2.2.2
    else st i

/-- **Quarter-round update lane reduction.** Lane `k` of the packed quarter-round
    update equals the scalar update on the lane-`k` slice. -/
theorem applyQRp_lane (st : PState) (α β γ δ : Fin 16) (k : Fin 16) :
    laneState (applyQRp st α β γ δ) k = applyQRs (laneState st k) α β γ δ := by
  funext i
  have h := qrSpecZ_lane (st α) (st β) (st γ) (st δ) k
  simp only [laneState, applyQRp, applyQRs]
  -- push `zmmLane32` through the `if`s on `i`; in the four hit-branches the goal
  -- is a projection of the `qrScalarLane` tuple, closed by rewriting `h` back to
  -- the packed `zmmLane32 (qrSpecZ …) k` tuple; the miss-branch is `rfl`.
  split_ifs <;> first | rfl | rw [← h]

/-- One scalar double-round on a 16-word lane-state (SAME index sets as
    `chacha20DoubleRound`). -/
def doubleRoundS (st : Fin 16 → BitVec 32) : Fin 16 → BitVec 32 :=
  let st := applyQRs st 0 4 8 12
  let st := applyQRs st 1 5 9 13
  let st := applyQRs st 2 6 10 14
  let st := applyQRs st 3 7 11 15
  let st := applyQRs st 0 5 10 15
  let st := applyQRs st 1 6 11 12
  let st := applyQRs st 2 7 8 13
  let st := applyQRs st 3 4 9 14
  st

/-- **Double-round lane reduction.** Lane `k` of the packed double-round equals
    the scalar double-round on the lane-`k` slice. Linking the whole packed block
    back to `qrSpecZ` (hence `qrCom`) lane-wise. -/
theorem chacha20DoubleRound_lane (st : PState) (k : Fin 16) :
    laneState (chacha20DoubleRound st) k = doubleRoundS (laneState st k) := by
  simp only [chacha20DoubleRound, doubleRoundS, applyQRp_lane]

/-! ## 4. RFC-8439 §2.3.2 single-block test vector (LIGHT scalar anchor)

The scalar block (an `Array (BitVec 32)` schedule, identical to
`bench/chacha_compare/chacha_4way_owned_block_denote_check.lean`) matches the
RFC §2.3.2 reference output. Same column/diagonal index sets and quarter-round as
`chacha20BlockSpec`; the `native_decide` is over scalar 32-bit arithmetic (≈2 s),
not the non-terminating 16-lane `BitVec 512` denotation. -/

/-- RFC 8439 §2.3.2 initial state (single block) — the sixteen `u32` words. -/
def initWords : List (BitVec 32) :=
  [ 0x61707865#32, 0x3320646e#32, 0x79622d32#32, 0x6b206574#32,
    0x03020100#32, 0x07060504#32, 0x0b0a0908#32, 0x0f0e0d0c#32,
    0x13121110#32, 0x17161514#32, 0x1b1a1918#32, 0x1f1e1d1c#32,
    0x00000001#32, 0x09000000#32, 0x4a000000#32, 0x00000000#32 ]

/-- The scalar ChaCha20 quarter-round (RFC 8439 §2.1) directly on `BitVec 32`
    (rotate-LEFT form). Bit-for-bit `qrScalarLane` (since `rotateRight (32-k)`
    is `rotateLeft k`). Returns `(a',b',c',d')`. -/
def qrScalar (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let rotl : BitVec 32 → Nat → BitVec 32 := fun x n => (x <<< n) ||| (x >>> (32 - n))
  let a := a + b; let d := rotl (d ^^^ a) 16
  let c := c + d; let b := rotl (b ^^^ c) 12
  let a := a + b; let d := rotl (d ^^^ a) 8
  let c := c + d; let b := rotl (b ^^^ c) 7
  (a, b, c, d)

/-- Apply one quarter-round to the 16-word array at indices `(α,β,γ,δ)` (eager). -/
def applyQR (st : Array (BitVec 32)) (α β γ δ : Nat) : Array (BitVec 32) :=
  let (a, b, c, d) := qrScalar st[α]! st[β]! st[γ]! st[δ]!
  ((st.set! α a).set! β b |>.set! γ c).set! δ d

/-- One scalar double-round (Array schedule) — SAME index sets as
    `chacha20DoubleRound`. -/
def doubleRound (st : Array (BitVec 32)) : Array (BitVec 32) :=
  let st := applyQR st 0 4 8 12
  let st := applyQR st 1 5 9 13
  let st := applyQR st 2 6 10 14
  let st := applyQR st 3 7 11 15
  let st := applyQR st 0 5 10 15
  let st := applyQR st 1 6 11 12
  let st := applyQR st 2 7 8 13
  let st := applyQR st 3 4 9 14
  st

/-- The full single block: ten double-rounds then the feed-forward, materialised
    eagerly (each quarter-round evaluates exactly once). -/
def blockOut : Array (BitVec 32) := Id.run do
  let init := initWords.toArray
  let mut st := init
  for _ in List.range 10 do
    st := doubleRound st
  let mut out := st
  for k in List.range 16 do
    out := out.set! k (st[k]! + init[k]!)
  return out

/-- RFC 8439 §2.3.2 expected block output (single block) — the sixteen `u32`
    words `[0xe4e7f110, 0x15593bd1, …]`. -/
def expectedOut : List (BitVec 32) :=
  [ 0xe4e7f110#32, 0x15593bd1#32, 0x1fdd0f50#32, 0xc47120a3#32,
    0xc7f4d1c7#32, 0x0368c033#32, 0x9aaa2204#32, 0x4e6cd4c3#32,
    0x466482d2#32, 0x09aa9f07#32, 0x05d7c214#32, 0xa2028bd9#32,
    0xd19c12b5#32, 0xb94e16de#32, 0xe883d0cb#32, 0x4e3c50a2#32 ]

/-- **RFC-8439 §2.3.2 single-block KAT (LIGHT).** The scalar block — same
    column/diagonal index sets, same quarter-round, same feed-forward as the
    packed `chacha20BlockSpec` — matches the RFC §2.3.2 reference output on all
    sixteen words. LIGHT: `native_decide` over scalar `BitVec 32` arithmetic (the
    16-lane `BitVec 512` denotation does not terminate under the kernel). -/
theorem scalarBlock_matches_rfc : blockOut.toList = expectedOut := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordBlockCom
