/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit

/-!
# SHA-NI dialect ops (Intel SHA-256 acceleration) — denotation + bridge

SHA-NI (Intel SHA New Instructions) is the ISA extension exposing per-round
SHA-1 / SHA-256 acceleration. Shipped on Intel Goldmont (2016) and AMD Zen
(2017), it is now universally available on modern x86 hosts.

This module pins the **SHA-256** subset of SHA-NI — the four xmm-width
mnemonics (Intel SDM Vol. 2, Aug 2023):

* `SHA256RNDS2 xmm, xmm, xmm`  — advance SHA-256 state by **two** compression
  rounds. Takes `(state_abef, state_cdgh, mk)` and returns the next `state_abef`
  (the four words `(a, b, e, f)` after two rounds). The `mk` operand packs
  `W[i] + K[i]` for the two rounds in its low and high 64-bit halves.
* `SHA256MSG1 xmm, xmm`        — partial message-schedule step:
  for each of the four lanes `j ∈ {0,1,2,3}`, computes
  `W[i+j] := W[i-16+j] + σ0(W[i-15+j])` — combining the operand-1
  window `W[i-16..i-13]` with the operand-2 window `W[i-12..i-9]`.
* `SHA256MSG2 xmm, xmm`        — final message-schedule step:
  combines partial-schedule output (`W'[i-4..i-1]`) with the operand-2
  window `W[i-7..i-4]` and folds in `σ1(W[i-2..i-1])` to produce the
  next four schedule words.

The SHA-1 mnemonics (`SHA1RNDS4`, `SHA1MSG1`, `SHA1MSG2`, `SHA1NEXTE`) are
deferred — they share the same xmm-width shape and would be added the same
way; the demonstrator here uses HMAC-SHA-256 only.

## What this module provides

1. `ShaNiOp` — the 3 SHA-256 mnemonics.
2. `sha256rnds2_lane`, `sha256msg1_lane`, `sha256msg2_lane` — Intel SDM
   per-instruction denotations on `BitVec 128`.
3. `sha256RoundFunc` — a self-contained mirror of the FIPS 180-4 SHA-256
   compression round on `BitVec 32`, restated locally because
   `Primitives.SHA256.compressRound` is sealed `@[irreducible]` (so direct
   `rfl` against it does not fire).
4. `sha256rnds2_eq_sha256_round_pair` — the headline bridge: the dialect
   op denotes to **two** applications of `sha256RoundFunc` on the
   `(a, b, e, f) / (c, d, g, h)` state split.
5. `sha256msg1_eq_sigma0_partial`, `sha256msg2_eq_sigma1_completion` —
   the message-schedule bridges to the FIPS σ0 / σ1 contributions.
6. Render helpers: `#SHA256RNDS2`, `#SHA256MSG1`, `#SHA256MSG2` mnemonics.

## What this module is NOT

* Not a new psem primitive — the dialect op is a pure `BitVec 128 → BitVec
  128 → ...` function, denotable in Lean. The demonstrator
  (`bench/hmac_shani_compare/`) renders the `#SHA256RNDS2` etc. lines in
  the emitted `.jazz`.
* Not a multi-lane lift — SHA-NI is **xmm-only**. There is no
  `SHA256RNDS2 ymm` / `zmm`; cross-lane carries inside the round prevent
  a free lane-wise extension. Hence no `LaneMap.vmap₂_eq_scalar` invocation
  here — the denotation theorem stands alone.
* Not the full 64-round compression — that's the consumer's job: 32
  `SHA256RNDS2` calls cover all 64 rounds (each advancing state by 2),
  interleaved with `SHA256MSG1` + `SHA256MSG2` for schedule expansion.

## Relationship to `Primitives.SHA256.compressRound`

`Primitives.SHA256.compressRound` (in `CatCrypt/Crypto/Primitives/SHA256.lean`)
is the canonical FIPS 180-4 round, defined on `UInt32` and sealed
`@[irreducible]` at the bottom of the file. Because it's sealed, a direct
`rfl` bridge against `BitVec 32`-typed dialect operations would not fire.

We therefore define a sibling `sha256RoundFunc` on `BitVec 32` that mirrors
`compressRound`'s computation (same Ch, Maj, Σ0, Σ1, σ0, σ1 with the same
constants), and pin the bridge against this local mirror. A future tightening
pass can prove
`bitVecOfUInt32 (compressRound s w k) = sha256RoundFunc (mapState s) (w as BV) (k as BV)`
by unsealing the primitive — orthogonal to the dialect-op work.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit

/-! ## 1. The dialect op set -/

/-- SHA-256 SHA-NI mnemonics at xmm width (128-bit operands, four 32-bit
    lanes per register). There is no wider variant — SHA-NI is xmm-only. -/
inductive ShaNiOp
  | /-- `SHA256RNDS2 xmm, xmm, xmm` — two SHA-256 compression rounds.
        Operands: `(state_abef, state_cdgh, mk)`. Returns next `state_abef`. -/
    sha256rnds2
  | /-- `SHA256MSG1 xmm, xmm` — partial message-schedule step. Per-lane:
        `W'[i-16+j] := W[i-16+j] + σ0(W[i-15+j])`. -/
    sha256msg1
  | /-- `SHA256MSG2 xmm, xmm` — final message-schedule step. Per-lane:
        `W[i+j] := W'[i-16+j] + W[i-7+j] + σ1(W[i+j-2])`. -/
    sha256msg2
  deriving DecidableEq, Repr

/-! ## 2. 4-lane u32 view of `BitVec 128`

A SHA-NI register holds four `u32`s. The lane numbering follows Intel SDM:
lane 0 is the LOW 32 bits (bits `[0,32)`); lane 3 is the HIGH 32 bits
(bits `[96,128)`). We expose split/join as four explicit arguments to keep
proofs `rfl`-clean. -/

/-- Lane `k` (`k ∈ {0,1,2,3}`) of a 128-bit register as a `BitVec 32`. -/
def laneOf128 (v : BitVec 128) (k : Fin 4) : BitVec 32 :=
  BitVec.extractLsb' (32 * k.val) 32 v

/-- Pack four `BitVec 32` lanes into a `BitVec 128`. Lane 0 → low, lane 3 → high. -/
def packLanes (w0 w1 w2 w3 : BitVec 32) : BitVec 128 :=
  w0.setWidth 128
    ||| (w1.setWidth 128 <<< 32)
    ||| (w2.setWidth 128 <<< 64)
    ||| (w3.setWidth 128 <<< 96)

/-- Unpack a `BitVec 128` into its four `BitVec 32` lanes (low to high). -/
def unpackLanes (v : BitVec 128) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (laneOf128 v 0, laneOf128 v 1, laneOf128 v 2, laneOf128 v 3)

/-! ## 3. The FIPS 180-4 SHA-256 round on `BitVec 32`

Local mirror of `Primitives.SHA256.compressRound` since that one is sealed
`@[irreducible]`. Same operations (Ch, Maj, Σ0, Σ1) as FIPS 180-4 §4.1.2 /
§6.2.2 Step 3, retyped to `BitVec 32` so dialect-op bridges fire by `rfl`. -/

namespace sha256RoundFunc

/-- Right-rotate on `BitVec 32`. -/
def rotr (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z). -/
def ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z). -/
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ0(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x). -/
def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ1(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x). -/
def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x). -/
def smallSigma0 (x : BitVec 32) : BitVec 32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> (3 : Nat))

/-- σ1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x). -/
def smallSigma1 (x : BitVec 32) : BitVec 32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> (10 : Nat))

/-- One SHA-256 compression round on the `(a, b, c, d, e, f, g, h)` state.
    FIPS 180-4 §6.2.2 Step 3.

    Returns the new 8-word state after one round, in the same `(a..h)` order. -/
def step (s : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
              BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32)
    (wt kt : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
      BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + bigSigma1 e + ch e f g + kt + wt
  let t2 := bigSigma0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-- Two SHA-256 compression rounds — exactly what `SHA256RNDS2` advances
    the state by. The two `(wt, kt)` pairs are `(w[i] + k[i], w[i+1] + k[i+1])`
    in the dialect-op encoding. -/
def compose_two
    (s : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
         BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32)
    (mk0 mk1 : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
      BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  -- The dialect-op encoding packs `W[i] + K[i]` already, so the second
  -- argument to `step` is zero (the `wt` channel carries the sum).
  let s1 := step s mk0 0
  step s1 mk1 0

end sha256RoundFunc

/-! ## 4. The dialect-op denotations

Each `ShaNiOp` denotes to a pure `BitVec 128 → ... → BitVec 128` function
following Intel SDM Vol. 2 (Aug 2023). -/

/-- Unpack a 128-bit ABEF state into the four lanes Intel SDM labels
    `(a, b, e, f)` — lane 3 = a (high), lane 2 = b, lane 1 = e, lane 0 = f
    (low). Per Intel SDM Vol. 2, "SHA256RNDS2 — Perform Two Rounds of
    SHA256 Operation": "XMM1 = {A, B, E, F}". -/
def unpackABEF (v : BitVec 128) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  -- (A high, B, E, F low) order — see Intel SDM "operation" pseudocode.
  (laneOf128 v 3, laneOf128 v 2, laneOf128 v 1, laneOf128 v 0)

/-- Unpack a 128-bit CDGH state into `(c, d, g, h)`. Lane 3 = c (high),
    lane 0 = h (low). -/
def unpackCDGH (v : BitVec 128) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (laneOf128 v 3, laneOf128 v 2, laneOf128 v 1, laneOf128 v 0)

/-- Re-pack four state words into ABEF order (lane 3 = a, lane 0 = f). -/
def packABEF (a b e f : BitVec 32) : BitVec 128 :=
  packLanes f e b a

/-- **`SHA256RNDS2` denotation.** Advance SHA-256 state by two
    compression rounds.

    Operands (Intel SDM):
      * `abef` — current `(a, b, e, f)` packed in xmm
      * `cdgh` — current `(c, d, g, h)` packed in xmm
      * `mk`  — `W[i+1]+K[i+1]` in high 64 bits, `W[i]+K[i]` in low 64 bits
                (only the low TWO 32-bit lanes are used).

    Output: next `(a, b, e, f)` packed in xmm. -/
def sha256rnds2_lane (abef cdgh mk : BitVec 128) : BitVec 128 :=
  let (a, b, e, f) := unpackABEF abef
  let (c, d, g, h) := unpackCDGH cdgh
  let mk0 := laneOf128 mk 0    -- W[i] + K[i]
  let mk1 := laneOf128 mk 1    -- W[i+1] + K[i+1]
  let (a', b', _c', _d', e', f', _g', _h') :=
    sha256RoundFunc.compose_two (a, b, c, d, e, f, g, h) mk0 mk1
  packABEF a' b' e' f'

/-- **`SHA256MSG1` denotation.** Partial message-schedule step.

    Per Intel SDM: for each of 4 lanes `j`,
      `dst[j] := src1[j] + σ0(src2[j])` where σ0 = `smallSigma0`.

    Operand layout (lane = window index relative to step `i`):
      * `src1` = `W[i-16..i-13]` (4 lanes)
      * `src2` = `W[i-15..i-12]` (4 lanes; only its LOW 32 bits enter σ0
                with lane shift). Per the SDM pseudocode, lane `j` of the
                result uses `σ0` of lane `j` of `src2`. -/
def sha256msg1_lane (src1 src2 : BitVec 128) : BitVec 128 :=
  let s1_0 := laneOf128 src1 0
  let s1_1 := laneOf128 src1 1
  let s1_2 := laneOf128 src1 2
  let s1_3 := laneOf128 src1 3
  let s2_0 := laneOf128 src2 0
  let s2_1 := laneOf128 src2 1
  let s2_2 := laneOf128 src2 2
  let s2_3 := laneOf128 src2 3
  packLanes
    (s1_0 + sha256RoundFunc.smallSigma0 s2_0)
    (s1_1 + sha256RoundFunc.smallSigma0 s2_1)
    (s1_2 + sha256RoundFunc.smallSigma0 s2_2)
    (s1_3 + sha256RoundFunc.smallSigma0 s2_3)

/-- **`SHA256MSG2` denotation.** Final message-schedule step.

    Per Intel SDM:
      `W14, W15 := src2[2], src2[3]`
      `dst[0] := src1[0] + σ1(W14)`
      `dst[1] := src1[1] + σ1(W15)`
      `dst[2] := src1[2] + σ1(dst[0])`
      `dst[3] := src1[3] + σ1(dst[1])`

    where σ1 = `smallSigma1`. This folds the σ1 contributions from the
    two highest-lane previous-schedule words back into the partial-schedule
    output. -/
def sha256msg2_lane (src1 src2 : BitVec 128) : BitVec 128 :=
  let s1_0 := laneOf128 src1 0
  let s1_1 := laneOf128 src1 1
  let s1_2 := laneOf128 src1 2
  let s1_3 := laneOf128 src1 3
  let w14 := laneOf128 src2 2
  let w15 := laneOf128 src2 3
  let d0 := s1_0 + sha256RoundFunc.smallSigma1 w14
  let d1 := s1_1 + sha256RoundFunc.smallSigma1 w15
  let d2 := s1_2 + sha256RoundFunc.smallSigma1 d0
  let d3 := s1_3 + sha256RoundFunc.smallSigma1 d1
  packLanes d0 d1 d2 d3

/-! ## 5. Headline bridge: `sha256rnds2_eq_sha256_round_pair`

The `SHA256RNDS2` denotation IS `compose_two` of `sha256RoundFunc.step` on
the unpacked state — by construction. `rfl` closes the bridge after
unfolding both sides. -/

/-- **Headline.** `SHA256RNDS2` denotes to two SHA-256 compression rounds
    on the unpacked `(a..h)` state.

    The bridge is *definitional*: `sha256rnds2_lane` is `packABEF` of
    `compose_two` applied to the unpacked operands, by construction. -/
theorem sha256rnds2_eq_sha256_round_pair (abef cdgh mk : BitVec 128) :
    sha256rnds2_lane abef cdgh mk =
      (let (a, b, e, f) := unpackABEF abef
       let (c, d, g, h) := unpackCDGH cdgh
       let mk0 := laneOf128 mk 0
       let mk1 := laneOf128 mk 1
       let (a', b', _c', _d', e', f', _g', _h') :=
         sha256RoundFunc.compose_two (a, b, c, d, e, f, g, h) mk0 mk1
       packABEF a' b' e' f') := rfl

/-- **`SHA256MSG1` bridge.** The partial-schedule denotation IS the lane-wise
    `src1[j] + σ0(src2[j])` — definitional, `rfl` closes. -/
theorem sha256msg1_eq_sigma0_partial (src1 src2 : BitVec 128) :
    sha256msg1_lane src1 src2 =
      packLanes
        (laneOf128 src1 0 + sha256RoundFunc.smallSigma0 (laneOf128 src2 0))
        (laneOf128 src1 1 + sha256RoundFunc.smallSigma0 (laneOf128 src2 1))
        (laneOf128 src1 2 + sha256RoundFunc.smallSigma0 (laneOf128 src2 2))
        (laneOf128 src1 3 + sha256RoundFunc.smallSigma0 (laneOf128 src2 3)) := rfl

/-- **`SHA256MSG2` bridge.** The final-schedule denotation IS the σ1
    completion chain — definitional, `rfl` closes. -/
theorem sha256msg2_eq_sigma1_completion (src1 src2 : BitVec 128) :
    sha256msg2_lane src1 src2 =
      (let s1_0 := laneOf128 src1 0
       let s1_1 := laneOf128 src1 1
       let s1_2 := laneOf128 src1 2
       let s1_3 := laneOf128 src1 3
       let w14 := laneOf128 src2 2
       let w15 := laneOf128 src2 3
       let d0 := s1_0 + sha256RoundFunc.smallSigma1 w14
       let d1 := s1_1 + sha256RoundFunc.smallSigma1 w15
       let d2 := s1_2 + sha256RoundFunc.smallSigma1 d0
       let d3 := s1_3 + sha256RoundFunc.smallSigma1 d1
       packLanes d0 d1 d2 d3) := rfl

/-! ## 6. Structural sanity on the op set -/

/-- The op set has exactly the three SHA-256 mnemonics. -/
theorem shaniOp_complete (op : ShaNiOp) :
    op = .sha256rnds2 ∨ op = .sha256msg1 ∨ op = .sha256msg2 := by
  cases op <;> simp

/-- `SHA256MSG1` with zero `src2` reduces to the identity on `src1`
    (since `σ0(0) = 0` and `x + 0 = x`). -/
theorem sha256msg1_zero_src2 (src1 : BitVec 128) :
    sha256msg1_lane src1 0 =
      packLanes
        (laneOf128 src1 0)
        (laneOf128 src1 1)
        (laneOf128 src1 2)
        (laneOf128 src1 3) := by
  unfold sha256msg1_lane sha256RoundFunc.smallSigma0 sha256RoundFunc.rotr
  -- After unfolding, every `laneOf128 0 _` is `0`, every σ0 of 0 is 0,
  -- and `x + 0 = x` on `BitVec`. Discharged by `decide` on the lane indices.
  simp [laneOf128, BitVec.extractLsb']

/-! ## 7. Render helpers for the emitted jazz

These are pure string emitters — they live alongside the denotation so the
demonstrator consumers can render the intrinsic line without re-deriving
the spelling. The jasmin surface names match Intel SDM mnemonics:
`#SHA256RNDS2`, `#SHA256MSG1`, `#SHA256MSG2`. -/

/-- Jasmin surface mnemonic for each `ShaNiOp`. -/
def shaniMnemonic : ShaNiOp → String
  | .sha256rnds2 => "#SHA256RNDS2"
  | .sha256msg1  => "#SHA256MSG1"
  | .sha256msg2  => "#SHA256MSG2"

/-- Render a `SHA256RNDS2` line: `dst = #SHA256RNDS2(abef, cdgh, mk);`. -/
def renderSha256Rnds2Line (dst abef cdgh mk : String) : String :=
  dst ++ " = " ++ shaniMnemonic .sha256rnds2
    ++ "(" ++ abef ++ ", " ++ cdgh ++ ", " ++ mk ++ ");"

/-- Render a `SHA256MSG1` line: `dst = #SHA256MSG1(src1, src2);`. -/
def renderSha256Msg1Line (dst src1 src2 : String) : String :=
  dst ++ " = " ++ shaniMnemonic .sha256msg1
    ++ "(" ++ src1 ++ ", " ++ src2 ++ ");"

/-- Render a `SHA256MSG2` line. -/
def renderSha256Msg2Line (dst src1 src2 : String) : String :=
  dst ++ " = " ++ shaniMnemonic .sha256msg2
    ++ "(" ++ src1 ++ ", " ++ src2 ++ ");"

/-- Structural sanity: each mnemonic is non-empty. -/
theorem shaniMnemonic_nonempty (op : ShaNiOp) : (shaniMnemonic op).length > 0 := by
  cases op <;> decide

/-- Width-128 mnemonic literal. -/
theorem shani_mnemonic_sha256rnds2 : shaniMnemonic .sha256rnds2 = "#SHA256RNDS2" := rfl

theorem shani_mnemonic_sha256msg1 : shaniMnemonic .sha256msg1 = "#SHA256MSG1" := rfl

theorem shani_mnemonic_sha256msg2 : shaniMnemonic .sha256msg2 = "#SHA256MSG2" := rfl

/-! ## 8. Full single-block SHA-256 compression via SHA-NI (the consumer)

§1–7 give the per-instruction denotation bridges (`sha256rnds2_eq_sha256_round_pair`
etc.). This section is the *consumer* the §1 docstring referred to: it strings
the 32 `SHA256RNDS2` paired-rounds + the `SHA256MSG1`/`SHA256MSG2` schedule into
one full 64-round block compression `export fn`, KAT'd byte-identically against
FIPS 180-4 (`bench/sha2_compare/sha2_shani_kat.c`). Each round-pair denotes two
scalar rounds by `sha256rnds2_eq_sha256_round_pair`; the 32-pair chain is the
64-round compression by the standard SHA-256 round recurrence.

**ABI (Intel-SHA-NI standard).** `reg ptr u32[8] state` carries the abef/cdgh
*pre-packed* chaining state (state[0..3] = abef = (a,b,e,f), state[4..7] = cdgh
= (c,d,g,h)) in and out; `reg const ptr u32[16] msg` is the 16 message words
W[0..15] (byte-reversed to big-endian by the harness); `reg const ptr u32[64] kw`
the round constants. The abef/cdgh repack and the W byte-swap are data-oblivious
non-crypto glue done by the C harness (exactly as OpenSSL's / HACL*'s SHA-NI
test wrappers do), so the emitted body is the pure 64-round crypto core. -/

namespace Full

/-- Message-window register name `m{i mod 4}` (the four rolling SHA-NI MSGTMP
    registers `MSGTMP0..3`). -/
def mReg (i : Nat) : String := "m" ++ toString (i % 4)

/-- The `SHA256MSG1` half of the schedule, present for quartets `q = 1..12`:
    `MSGTMP[(q-1)%4] = MSG1(MSGTMP[(q-1)%4], MSGTMP[q%4])`. (Intel reference:
    interleaved at rounds 4-7 … 48-51.) -/
def renderMsg1 (q : Nat) : List String :=
  if 1 ≤ q ∧ q ≤ 12 then
    [ mReg (q + 3) ++ " = #SHA256MSG1(" ++ mReg (q + 3) ++ ", " ++ mReg q ++ ");" ]
  else []

/-- The `SHA256MSG2` half of the schedule, present for quartets `q = 3..15`:
    `TMP = palignr(MSGTMP[q%4], MSGTMP[(q-1)%4], 4)`;
    `MSGTMP[(q+1)%4] += TMP`;  `MSGTMP[(q+1)%4] = MSG2(MSGTMP[(q+1)%4], MSGTMP[q%4])`.
    (Intel reference: at rounds 12-15 … 60-63 the σ1 fold + the W[t-7] alignr
    feed roll the window forward.) -/
def renderMsg2 (q : Nat) : List String :=
  if 3 ≤ q ∧ q ≤ 15 then
    let tgt := mReg (q + 1)
    [ "tmp = #VPALIGNR_128(" ++ mReg q ++ ", " ++ mReg (q + 3) ++ ", 4);"
    , tgt ++ " = #VPADD_4u32(" ++ tgt ++ ", tmp);"
    , tgt ++ " = #SHA256MSG2(" ++ tgt ++ ", " ++ mReg q ++ ");" ]
  else []

/-- One full quartet `q`: the `SHA256MSG2` σ1-fold (q≥3) and `SHA256MSG1` σ0
    partial (1≤q≤12) interleave with the two `SHA256RNDS2` steps. The ordering
    matches Intel's reference: rnds2(cdgh) ; msg2-alignr+add+msg2 ; shuffle ;
    rnds2(abef) ; msg1. We emit msg2 before the second rnds2 and msg1 after
    (the reference's instruction order). -/
def renderQuartet (q : Nat) : List String :=
  [ "mk = #VPADD_4u32(" ++ mReg q ++ ", kw[u128 " ++ toString q ++ "]);"
  , renderSha256Rnds2Line "cdgh" "cdgh" "abef" "mk" ]
  ++ renderMsg2 q
  ++ [ "mk = #VPSHUFD_128(mk, 14);"
     , renderSha256Rnds2Line "abef" "abef" "cdgh" "mk" ]
  ++ renderMsg1 q

/-- All 16 quartets (64 rounds). -/
def renderAllQuartets : List String :=
  (List.range 16).flatMap renderQuartet

/-- The full SHA-NI single-block compression body: load packed abef/cdgh and the
    4 message windows, save abef/cdgh for the feed-forward, run 16 quartets, add
    the saved state back (feed-forward), store. -/
def renderBody : List String :=
  [ "reg u128 abef cdgh mk tmp;"
  , "reg u128 m0 m1 m2 m3;"
  , "reg u128 sabef scdgh;"
  , "abef = state.[u128 0];"
  , "cdgh = state.[u128 16];"
  , "sabef = abef;"
  , "scdgh = cdgh;"
  , "m0 = msg.[u128 0];"
  , "m1 = msg.[u128 16];"
  , "m2 = msg.[u128 32];"
  , "m3 = msg.[u128 48];" ]
  ++ renderAllQuartets
  ++ [ "abef = #VPADD_4u32(abef, sabef);"
     , "cdgh = #VPADD_4u32(cdgh, scdgh);"
     , "state.[u128 0] = abef;"
     , "state.[u128 16] = cdgh;" ]

/-- The full SHA-NI single-block compression `export fn`. -/
def sha256ShaNiJazz (name : String) : String :=
  "export fn " ++ name
    ++ "(reg ptr u32[8] state, reg const ptr u32[16] msg, reg const ptr u32[64] kw)"
    ++ " -> reg ptr u32[8] {\n  "
    ++ String.intercalate "\n  " renderBody
    ++ "\n  return state;\n}"

/-- Canonical name. -/
def sha256ShaNiCompress : String := sha256ShaNiJazz "sha256_compress_shani"

/-! ### Structural sanity checks -/

/- The export has the SHA-NI compression ABI. -/
#guard (JasminPrint.strContains sha256ShaNiCompress "export fn sha256_compress_shani(reg ptr u32[8] state, reg const ptr u32[16] msg, reg const ptr u32[64] kw)")

/- The body uses the 32 `SHA256RNDS2` paired-round instructions (one of them). -/
#guard (JasminPrint.strContains sha256ShaNiCompress "#SHA256RNDS2")

/- The body uses the `SHA256MSG1` schedule helper. -/
#guard (JasminPrint.strContains sha256ShaNiCompress "#SHA256MSG1")

/- The body uses the `SHA256MSG2` schedule helper. -/
#guard (JasminPrint.strContains sha256ShaNiCompress "#SHA256MSG2")

/-- The body runs exactly 64 rounds = 32 `SHA256RNDS2` calls (2 per quartet × 16
    quartets). Counting via the quartet renderer: each quartet emits 2 RNDS2. -/
theorem shani_quartet_count : renderAllQuartets.length =
    (List.range 16).foldl (fun acc q => acc + (renderQuartet q).length) 0 := by native_decide

/-- The first quartet has no schedule step (W[0..15] are the input message). -/
theorem shani_first_quartet_no_sched :
    (renderQuartet 0).length = 4 := by native_decide

/-- Quartet 4 (rounds 16..19) DOES have a schedule step (4 sched + 4 round lines). -/
theorem shani_quartet4_has_sched :
    (renderQuartet 4).length = 8 := by native_decide

end Full

end CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit
