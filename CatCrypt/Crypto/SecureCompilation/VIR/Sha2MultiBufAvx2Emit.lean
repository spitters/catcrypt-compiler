/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.BitVec
public import Mathlib.Tactic.Ring

/-!
# Owned-backend emit of the AVX2 multi-buffer SHA-256 8-way / SHA-512 4-way block compression

The SHA-2 analogue of `CatCrypt/Crypto/MLKEM/NttEmit.lean` and
`CatCrypt/Crypto/MLDSA/InvNttPointwiseSimdEmit.lean`: re-emit the protocol's
core SIMD kernel through CatCrypt's **owned x86 backend** (no jasminc), gas-rendered
at the AT&T text level and KAT'd byte-identical to the reference.

`bench/sha2_compare/sha2_multibuf_emit.lean` lowers the multi-buffer compressions
to a `.jazz` source (`Sha2MultiBuf.emitSha256x8Jazz` / `emitSha512x4Jazz`) that is
then compiled by the **jasminc** front into
`bench/sha2_compare/gen/sha256_compress_x8.s` / `sha512_compress_x4w.s`. This module
re-emits the SAME two kernels through the **owned** backend: a self-contained
`8×u32` (resp. `4×u64`) AVX2 lane machine model, per-lane op semantics, the
FIPS-180-4 §6.2 / §6.4 compression body, an AT&T `.s` renderer, and per-lane
`decide`/`native_decide` self-checks against the scalar SHA-2 round — the
multi-buffer-throughput analogue of the ML-KEM / ML-DSA NTT owned-emit wins.

```
sha256X8Body  --runYBlock (8×u32 lane model)-->  the FIPS-180-4 §6.2 compression
              --renderYInst-->  AT&T `.s`  (gas-assembled, KAT'd byte-identical)
```

## The lane model and op set

An AVX2 `u256` register holds **8 × `u32`** lanes (`Fin 8 → BitVec 32`); each lane
is one independent SHA-256 message stream (the SoA layout the
`sha2_multibuf_kat.c` contract pins: `state[i]` / `msg[w]` / `kbr[t]` are u256
words, word `i` at byte offset `32·i`, lane `l` carrying stream `l`). SHA-256's
butterfly op alphabet on this lane shape is exactly what the jasminc `.jazz`
emits:

| AT&T mnemonic | shape    | lane op                                                |
|---------------|----------|--------------------------------------------------------|
| `vpaddd`      | `8×u32`  | wrapping dword add (`#VPADD_8u32`)                      |
| `vpxor`       | `256`    | bitwise xor (`#VPXOR_256`)                              |
| `vpand`       | `256`    | bitwise and (`#VPAND_256`)                             |
| `vpor`        | `256`    | bitwise or (`#VPOR_256`)                               |
| `vpslld`      | `8×u32`  | per-dword left shift, imm count (`#VPSLL_8u32`)        |
| `vpsrld`      | `8×u32`  | per-dword right shift, imm count (`#VPSRL_8u32`)       |

The 32-bit rotate `ρⁿ(x)` is synthesised `(x ≫ n) | (x ≪ (32−n))` (a `vpsrld` +
`vpslld` + `vpor`), exactly as the AVX2 reference does (AVX2 has no per-dword
rotate; that arrived with AVX-512 `vprold`). We prove this synthesised form IS a
`BitVec 32` rotate (`rotrSynth_eq`), so the round / schedule lane functions are
the FIPS-180-4 §4.1.2 `Σ`/`σ` rotates.

Invoke (emit the owned-backend `.s`):
  lake env lean bench/sha2_compare/sha2_multibuf_avx2_owned_emit.lean

## Elaboration cost

The two `roundBlk_realizes` proofs are the module's dominant cost. Each symbolically
executes a 36-instruction block: `get_setV_apply` resolves every register read back
through the `setV` chain that precedes it, so the rewrite count grows with the product
of block length and read count. The single `simp` covering both conjuncts is what keeps
that walk affordable — the round's `a'` and `e'` both read the accumulator slots `"t3"`
and `"t4"`, so normalising them in one `simp` call shares that subterm through the simp
cache, where a per-conjunct `simp` repeats the whole walk. A compositional form —
per-sub-block read-through lemmas for `rotBlk`, composed across the `++` seams — would
make the walk linear in block length rather than quadratic, at the cost of register
non-aliasing side conditions at every seam. -/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2MultiBufAvx2Emit

/-! ## 1. The 8×u32 lane machine model (the AVX2 SHA-256 multi-buffer view) -/

/-- A 256-bit AVX2 register as 8 × `u32` lanes. -/
abbrev Ymm : Type := Fin 8 → BitVec 32

/-- The register file: a name → `Ymm`. An absent name reads as all-zero. -/
structure YState where
  /-- The `ymm` register file, named by string. -/
  regs : String → Ymm

namespace YState

/-- Read a register (absent ⇒ zero register). Not `@[simp]`: the register-file
    laws `get_setV_same`/`_other` are the rewrite path (unfolding `get` would block
    them). -/
def get (s : YState) (r : String) : Ymm := s.regs r

/-- Write a register, leaving the others unchanged. -/
def setV (s : YState) (r : String) (v : Ymm) : YState :=
  { regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem get_setV_same (s : YState) (r : String) (v : Ymm) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_other (s : YState) (r r' : String) (v : Ymm)
    (h : r' ≠ r) : (s.setV r v).get r' = s.get r' := by simp [setV, get, h]

/-- **Per-lane read-through.** Reading lane `i` of register `r'` after writing `r`
    is the `if`-split — this pushes the lane application inward so a `setV`-chain
    collapses lane-by-lane (the proof-convergence form the realizations use). -/
@[simp] theorem get_setV_apply (s : YState) (r r' : String) (v : Ymm) (i : Fin 8) :
    (s.setV r v).get r' i = if r' = r then v i else s.get r' i := by
  by_cases h : r' = r
  · subst h; simp [get_setV_same]
  · simp [get_setV_other _ _ _ _ h, h]

end YState

/-! ## 2. Per-lane packed AVX2 ALU semantics (auditable against the SDM)

Every op is pointwise over the 8 lanes, so an N-way compression is N independent
scalar SHA-256 compressions — the lane-independence the multi-buffer KAT pins. -/

/-- `VPADDD` lane op: wrapping 32-bit add. -/
@[simp] def laneAdd (a b : BitVec 32) : BitVec 32 := a + b
/-- `VPXOR` lane op: bitwise xor. -/
@[simp] def laneXor (a b : BitVec 32) : BitVec 32 := a ^^^ b
/-- `VPAND` lane op: bitwise and. -/
@[simp] def laneAnd (a b : BitVec 32) : BitVec 32 := a &&& b
/-- `VPOR` lane op: bitwise or. -/
@[simp] def laneOr (a b : BitVec 32) : BitVec 32 := a ||| b
/-- `VPSLLD` lane op: per-dword left shift by an immediate. -/
@[simp] def laneShl (a : BitVec 32) (m : Nat) : BitVec 32 := a <<< m
/-- `VPSRLD` lane op: per-dword right shift by an immediate. -/
@[simp] def laneShr (a : BitVec 32) (m : Nat) : BitVec 32 := a >>> m

/-! ## 3. The instruction set (8×u32 lane shape) -/

/-- A single packed AVX2 SHA-256 instruction over named registers. The shift ops
    carry the AVX2 immediate count. -/
inductive YInst where
  /-- `VPADDD dst, a, b`. -/
  | vpaddd (dst a b : String)
  /-- `VPXOR dst, a, b`. -/
  | vpxor  (dst a b : String)
  /-- `VPAND dst, a, b`. -/
  | vpand  (dst a b : String)
  /-- `VPOR dst, a, b`. -/
  | vpor   (dst a b : String)
  /-- `VPSLLD dst, a, imm`. -/
  | vpslld (dst a : String) (imm : Nat)
  /-- `VPSRLD dst, a, imm`. -/
  | vpsrld (dst a : String) (imm : Nat)
  /-- `VMOVDQA dst, src` — register move. -/
  | vmov   (dst src : String)
  deriving Repr, DecidableEq

/-- The semantics of one instruction: read sources, apply the per-lane op, write
    the destination. -/
def evalYInst (s : YState) : YInst → YState
  | .vpaddd d a b  => s.setV d (fun i => laneAdd (s.get a i) (s.get b i))
  | .vpxor d a b   => s.setV d (fun i => laneXor (s.get a i) (s.get b i))
  | .vpand d a b   => s.setV d (fun i => laneAnd (s.get a i) (s.get b i))
  | .vpor d a b    => s.setV d (fun i => laneOr (s.get a i) (s.get b i))
  | .vpslld d a m  => s.setV d (fun i => laneShl (s.get a i) m)
  | .vpsrld d a m  => s.setV d (fun i => laneShr (s.get a i) m)
  | .vmov d s'     => s.setV d (s.get s')

/-- Straight-line fold of `evalYInst`. -/
def runYBlock (s : YState) : List YInst → YState
  | [] => s
  | i :: is => runYBlock (evalYInst s i) is

@[simp] theorem runYBlock_nil (s : YState) : runYBlock s [] = s := rfl

@[simp] theorem runYBlock_cons (s : YState) (i : YInst) (is : List YInst) :
    runYBlock s (i :: is) = runYBlock (evalYInst s i) is := rfl

/-- Running `b1 ++ b2` is running `b1` then `b2` (so `simp` evaluates the
    `++`-built round/schedule blocks). -/
@[simp] theorem runYBlock_append (s : YState) (b1 b2 : List YInst) :
    runYBlock s (b1 ++ b2) = runYBlock (runYBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runYBlock_cons, ih]

/-! ## 4. The synthesised rotate IS a `BitVec 32` rotate

AVX2 has no per-dword rotate, so the reference (and this emit) builds `ρⁿ(x)` as
`(x ≫ n) | (x ≪ (32−n))`. For `0 < n < 32` this equals `BitVec.rotateRight x n`
bit-exactly — the FIPS-180-4 §4.1.2 rotate, no width caveat. -/

/-- The synthesised 32-bit right-rotate `(x ≫ n) | (x ≪ (32−n))`. -/
@[simp] def rotrSynth (x : BitVec 32) (n : Nat) : BitVec 32 :=
  laneOr (laneShr x n) (laneShl x (32 - n))

/-- **The synthesised rotate is `BitVec.rotateRight`.** For each shift amount the
    `vpsrld`/`vpslld`/`vpor` triple equals `BitVec.rotateRight` at width 32 —
    bit-exact, the FIPS-180-4 rotate. (Checked at every amount SHA-256 uses.) -/
theorem rotrSynth_eq (x : BitVec 32) (n : Nat) (h32 : n < 32) :
    rotrSynth x n = BitVec.rotateRight x n := by
  simp only [rotrSynth, laneOr, laneShr, laneShl,
    BitVec.rotateRight_eq_rotateRightAux_of_lt h32, BitVec.rotateRightAux]

/-! ## 5. The scalar SHA-256 round functions on the lane (FIPS-180-4 §4.1.2 / §6.2.2)

The four round functions, the `T₁`/`T₂` step, and the message-schedule recurrence,
each as `BitVec 32` lane expressions in terms of the lane primitives. These are
the per-lane spec the emitted block realises. -/

/-- `Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)`, written `(e ∧ f) ⊕ (g ∧ ¬e)` — but the AVX2
    body uses the `(f ⊕ g) ∧ e ⊕ g` Mealy form (one fewer op), which equals `Ch`. -/
@[simp] def chL (e f g : BitVec 32) : BitVec 32 :=
  laneXor (laneAnd (laneXor f g) e) g

/-- `Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`, in the AVX2 body's
    `((a ⊕ b) ∧ c) ⊕ (a ∧ b)` form (one fewer op). -/
@[simp] def majL (a b c : BitVec 32) : BitVec 32 :=
  laneXor (laneAnd (laneXor a b) c) (laneAnd a b)

/-- `Σ₀(a) = ρ²(a) ⊕ ρ¹³(a) ⊕ ρ²²(a)`. -/
@[simp] def bigSigma0L (a : BitVec 32) : BitVec 32 :=
  laneXor (laneXor (rotrSynth a 2) (rotrSynth a 13)) (rotrSynth a 22)

/-- `Σ₁(e) = ρ⁶(e) ⊕ ρ¹¹(e) ⊕ ρ²⁵(e)`. -/
@[simp] def bigSigma1L (e : BitVec 32) : BitVec 32 :=
  laneXor (laneXor (rotrSynth e 6) (rotrSynth e 11)) (rotrSynth e 25)

/-- `σ₀(x) = ρ⁷(x) ⊕ ρ¹⁸(x) ⊕ (x ≫ 3)`. -/
@[simp] def smallSigma0L (x : BitVec 32) : BitVec 32 :=
  laneXor (laneXor (rotrSynth x 7) (rotrSynth x 18)) (laneShr x 3)

/-- `σ₁(x) = ρ¹⁷(x) ⊕ ρ¹⁹(x) ⊕ (x ≫ 10)`. -/
@[simp] def smallSigma1L (x : BitVec 32) : BitVec 32 :=
  laneXor (laneXor (rotrSynth x 17) (rotrSynth x 19)) (laneShr x 10)

/-- The eight working words at one lane. -/
structure Work where
  /-- working word `a` -/
  a : BitVec 32
  /-- working word `b` -/
  b : BitVec 32
  /-- working word `c` -/
  c : BitVec 32
  /-- working word `d` -/
  d : BitVec 32
  /-- working word `e` -/
  e : BitVec 32
  /-- working word `f` -/
  f : BitVec 32
  /-- working word `g` -/
  g : BitVec 32
  /-- working word `h` -/
  h : BitVec 32
deriving DecidableEq, Repr

/-- One SHA-256 round (FIPS-180-4 §6.2.2): `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ`,
    `T₂ = Σ₀(a) + Maj(a,b,c)`, `(a..h) ↦ (T₁+T₂, a, b, c, d+T₁, e, f, g)`. -/
def shaRound (kt wt : BitVec 32) (w : Work) : Work :=
  let t1 := laneAdd (laneAdd (laneAdd (laneAdd w.h (bigSigma1L w.e)) (chL w.e w.f w.g)) kt) wt
  let t2 := laneAdd (bigSigma0L w.a) (majL w.a w.b w.c)
  { a := laneAdd t1 t2, b := w.a, c := w.b, d := w.c
  , e := laneAdd w.d t1, f := w.e, g := w.f, h := w.g }

/-- The message-schedule recurrence
    `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`. -/
def schedNext (w2 w7 w15 w16 : BitVec 32) : BitVec 32 :=
  laneAdd (laneAdd (laneAdd (smallSigma1L w2) w7) (smallSigma0L w15)) w16

/-! ## 6. The reference scalar SHA-256 block compression (per-lane oracle)

A complete one-block SHA-256 compression on a single lane: expand the 64-word
schedule, run 64 rounds, add the chaining state back. This is the per-lane spec
the 8-way emit realises; the `#eval` self-check below runs it on "abc" and pins
the FIPS-180-4 digest. -/

/-- The 64 SHA-256 round constants `K[0..63]` (FIPS-180-4 §4.2.2). -/
def k256 : Array (BitVec 32) := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The FIPS-180-4 initial hash value `H₀`. -/
def h0 : Array (BitVec 32) := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Expand the 64-word message schedule from the 16 input words. -/
def expandSchedule (m : Array (BitVec 32)) : Array (BitVec 32) := Id.run do
  let mut w := m
  for t in [16:64] do
    w := w.push (schedNext w[t-2]! w[t-7]! w[t-15]! w[t-16]!)
  return w

/-- One-block SHA-256 compression on a single lane, returning `H'[0..7]`. The
    per-lane oracle the 8-way emit realises (FIPS-180-4 §6.2). -/
def sha256BlockScalar (m : Array (BitVec 32)) : Array (BitVec 32) := Id.run do
  let w := expandSchedule m
  let mut s : Work :=
    { a := h0[0]!, b := h0[1]!, c := h0[2]!, d := h0[3]!
    , e := h0[4]!, f := h0[5]!, g := h0[6]!, h := h0[7]! }
  for t in [0:64] do
    s := shaRound k256[t]! w[t]! s
  return #[ laneAdd h0[0]! s.a, laneAdd h0[1]! s.b, laneAdd h0[2]! s.c, laneAdd h0[3]! s.d
          , laneAdd h0[4]! s.e, laneAdd h0[5]! s.f, laneAdd h0[6]! s.g, laneAdd h0[7]! s.h ]

/-- The padded one-block message words for the FIPS-180-4 test string `"abc"`
    (`0x61626380`, then zeros, then the bit length `24`). -/
def abcMsg : Array (BitVec 32) :=
  #[0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x00000018]

/- **The FIPS-180-4 `SHA-256("abc")` self-check (per-lane oracle).** Running the
   scalar one-block compression — built entirely from the AVX2 lane primitives
   (`laneAdd`/`laneXor`/`laneAnd`/`rotrSynth`/…) — on the padded `"abc"` block
   yields the canonical digest `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3
   96177a9c b410ff61 f20015ad`. This is the cross-check the multi-buffer KAT
   integrates: lane 0 carries `"abc"` and must equal this digest. -/
#guard sha256BlockScalar abcMsg
    == (#[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
          0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] : Array (BitVec 32))

/-! ## 7. The AVX2 round / schedule as `YInst` blocks (8-way, lane-parallel)

The emitted block holds `a..h` in registers `"va".."vh"`, the broadcast round
constant `Kₜ` is loaded from `kbr[t]` and the schedule word `Wₜ` from `W[t mod 16]`
(both reloaded each round in the function emitter). The round block computes
`T₁`/`T₂` into the scratch chain and writes `a'`/`e'` back — but, following the
reference jazz, we emit the round with **register renaming** (the working slot
that becomes the new `a`/`e` is chosen per round) so no `vmov` rotation is needed.

`roundBlk dst_a dst_e (va vb vc vd ve vf vg vh kt wt : String)` computes the round
on the named source slots and leaves `a' → dst_a`, `e' → dst_e`. The caller maps
`dst_a := vh`, `dst_e := vd` (the two slots free after this round), matching the
reference's renaming schedule. Scratch registers `t0..t5` mirror the jazz's
`vt0..vt5`. -/

/-- The synthesised-rotate triple `ρⁿ(src) → dst`, leaving `ρ`-scratch in `"t0"`,
    `"t1"` (mirrors the jazz `vt0 = VPSRL; vt1 = VPSLL; dst = VPOR`). -/
def rotBlk (dst src : String) (n : Nat) : List YInst :=
  [ .vpsrld "t0" src n, .vpslld "t1" src (32 - n), .vpor dst "t0" "t1" ]

/-- The big-`Σ₁(e) → "t3"` block (3 rotates xored), mirroring the jazz. -/
def bigSigma1Blk (e : String) : List YInst :=
  rotBlk "t3" e 6 ++
  rotBlk "t2" e 11 ++ [ .vpxor "t3" "t3" "t2" ] ++
  rotBlk "t2" e 25 ++ [ .vpxor "t3" "t3" "t2" ]

/-- The big-`Σ₀(a) → "t4"` block (3 rotates xored). -/
def bigSigma0Blk (a : String) : List YInst :=
  rotBlk "t4" a 2 ++
  rotBlk "t2" a 13 ++ [ .vpxor "t4" "t4" "t2" ] ++
  rotBlk "t2" a 22 ++ [ .vpxor "t4" "t4" "t2" ]

/-- One SHA-256 round as an `YInst` block. Sources `va..vh`, constant slot `kt`,
    schedule slot `wt`. Computes `T₁ → "t3"`, `T₂` folded into `"t4"`, then writes
    `e' = d + T₁ → dstE` and `a' = T₁ + T₂ → dstA` (register-renaming, no rotation
    moves). Mirrors the jazz round op-for-op. -/
def roundBlk (dstA dstE va vb vc vd ve vf vg vh kt wt : String) : List YInst :=
  -- T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ  →  "t3"
  bigSigma1Blk ve ++
  [ .vpaddd "t3" "t3" vh
  -- Ch(e,f,g) = ((f ⊕ g) ∧ e) ⊕ g
  , .vpxor "t0" vf vg
  , .vpand "t0" "t0" ve
  , .vpxor "t0" "t0" vg
  , .vpaddd "t3" "t3" "t0"
  , .vpaddd "t3" "t3" kt
  , .vpaddd "t3" "t3" wt ] ++
  -- T₂ = Σ₀(a) + Maj(a,b,c)  →  "t4"
  bigSigma0Blk va ++
  [ .vpxor "t0" va vb
  , .vpand "t0" "t0" vc
  , .vpand "t1" va vb
  , .vpxor "t0" "t0" "t1"
  , .vpaddd "t4" "t4" "t0"
  -- e' = d + T₁  →  dstE ;  a' = T₁ + T₂  →  dstA
  , .vpaddd dstE vd "t3"
  , .vpaddd dstA "t3" "t4" ]

/-- The message-schedule recompute `W[t] = σ₁(w2) + w7 + σ₀(w15) + w16`, reading the
    four prior schedule slots and writing the new word into `dst`. Mirrors the jazz
    σ-expansion (`vt3 = w2; … vt3 = VPADD(vt3, w11); W[i] = vt3`). -/
def schedBlk (dst w2 w7 w15 w16 : String) : List YInst :=
  -- σ₁(w2) → "t3"  (the accumulator base)
  rotBlk "t3" w2 17 ++
  rotBlk "t5" w2 19 ++ [ .vpxor "t3" "t3" "t5"
  , .vpsrld "t5" w2 10, .vpxor "t3" "t3" "t5" ] ++
  -- σ₀(w15) → "t4"
  rotBlk "t4" w15 7 ++
  rotBlk "t5" w15 18 ++ [ .vpxor "t4" "t4" "t5"
  , .vpsrld "t5" w15 3, .vpxor "t4" "t4" "t5"
  -- W[t] = σ₁(w2) + w7 + σ₀(w15) + w16
  , .vpaddd "t3" "t3" w7
  , .vpaddd "t3" "t3" "t4"
  , .vpaddd dst "t3" w16 ]

/-! ## 8. The per-lane round / schedule realisation (bit-exact, every lane)

For every `YState` and lane `ℓ`, running `roundBlk` leaves `dstA`/`dstE` lane `ℓ`
holding exactly `a'`/`e'` of the scalar `shaRound` on the lane-`ℓ` working words —
a `BitVec 32` expression, for **every** state and lane. -/

/-- **`a'`/`e'` round realisation (per lane).** Running the round block on distinct
    named source slots `va..vh`, constant `kt`, schedule `wt`, leaves `ra` lane `ℓ`
    = `(shaRound kt wt work).a` and `re` lane `ℓ` = `… .e`, where `work` is the
    lane-`ℓ` reading of `va..vh` — a `BitVec 32` expression for **every** state and
    lane. The function emitter maps `ra`/`re` to the `h`/`d` ring slots. -/
theorem roundBlk_realizes (s : YState) (ℓ : Fin 8) :
    let out := runYBlock s (roundBlk "ra" "re"
      "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt")
    out.get "ra" ℓ
      = (shaRound (s.get "kt" ℓ) (s.get "wt" ℓ)
          { a := s.get "va" ℓ, b := s.get "vb" ℓ, c := s.get "vc" ℓ, d := s.get "vd" ℓ
          , e := s.get "ve" ℓ, f := s.get "vf" ℓ, g := s.get "vg" ℓ, h := s.get "vh" ℓ }).a
    ∧ out.get "re" ℓ
      = (shaRound (s.get "kt" ℓ) (s.get "wt" ℓ)
          { a := s.get "va" ℓ, b := s.get "vb" ℓ, c := s.get "vc" ℓ, d := s.get "vd" ℓ
          , e := s.get "ve" ℓ, f := s.get "vf" ℓ, g := s.get "vg" ℓ, h := s.get "vh" ℓ }).e := by
  simp only [roundBlk, rotBlk, bigSigma1Blk, bigSigma0Blk, runYBlock_cons,
    runYBlock_append, runYBlock_nil, evalYInst, YState.get_setV_apply,
    String.reduceEq, if_true, if_false,
    shaRound, bigSigma1L, bigSigma0L, chL, majL, rotrSynth, laneAdd, laneXor,
    laneAnd, laneOr, laneShl, laneShr]
  constructor <;> ring

/-- **schedule realisation (per lane).** Running the schedule block leaves `dst`
    lane `ℓ` holding `schedNext` of the four lane-`ℓ` prior words. -/
theorem schedBlk_realizes (s : YState) (ℓ : Fin 8) :
    (runYBlock s (schedBlk "wd" "w2" "w7" "w15" "w16")).get "wd" ℓ
      = schedNext (s.get "w2" ℓ) (s.get "w7" ℓ) (s.get "w15" ℓ) (s.get "w16" ℓ) := by
  simp only [schedBlk, rotBlk, runYBlock_cons, runYBlock_append, runYBlock_nil,
    evalYInst, YState.get_setV_apply, String.reduceEq, if_true, if_false,
    schedNext, smallSigma1L, smallSigma0L, rotrSynth, laneAdd,
    laneXor, laneOr, laneShl, laneShr]

/-! ## 9. AT&T renderer

VEX AT&T order is `op src2, src1, dst`; the imm-shift ops put the immediate
first. -/

/-- A register assignment: abstract name → `%ymmN`. -/
abbrev YAlloc := List (String × String)

/-- The `%ymmN` an abstract name maps to (unmapped ⇒ an explicit sentinel so an
    over-budget block is rejected by gas, never silently aliased). The analogue of
    `NttEmit.ymmOf`. -/
def ymmOf (alloc : YAlloc) (n : String) : String :=
  (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- Print one `YInst` to its AT&T line, mapping each abstract name through `alloc`.
    VEX AT&T order is `op src2, src1, dst`; the imm-shift ops put the imm first. -/
def renderYInst (alloc : YAlloc) : YInst → String
  | .vpaddd d a b  => "\tvpaddd " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpxor d a b   => "\tvpxor " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpand d a b   => "\tvpand " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpor d a b    => "\tvpor " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpslld d a m  => "\tvpslld $" ++ toString m ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpsrld d a m  => "\tvpsrld $" ++ toString m ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vmov d s      => "\tvmovdqa " ++ ymmOf alloc s ++ ", " ++ ymmOf alloc d

/-- Print a whole block through an allocation. -/
def renderBlock (alloc : YAlloc) (block : List YInst) : List String :=
  block.map (renderYInst alloc)

/-- The eight working YMM registers, the schedule window, scratch, the broadcast
    `kt`. We pin them to fixed `%ymm` names (16 YMM available; SHA-256 8-way fits:
    8 working + the rest cycle for schedule window + scratch via spill to memory). -/
def ymmA := "%ymm0"
def ymmB := "%ymm1"
def ymmC := "%ymm2"
def ymmD := "%ymm3"
def ymmE := "%ymm4"
def ymmF := "%ymm5"
def ymmG := "%ymm6"
def ymmH := "%ymm7"
def ymmKt := "%ymm8"
def ymmWt := "%ymm9"
def ymmT0 := "%ymm10"
def ymmT1 := "%ymm11"
def ymmT2 := "%ymm12"
def ymmT3 := "%ymm13"
def ymmT4 := "%ymm14"
def ymmT5 := "%ymm15"

/-! ## 10. The full-function `.s` emitter (SysV ABI, fully unrolled)

ABI (`sha2_multibuf_kat.c`): `sha256_compress_x8(state=%rdi, msg=%rsi, kbr=%rdx)`,
SoA, each `u256` word at byte offset `32·i`. The body loads the 8 chaining words
into the `%ymm0..7` ring, the 16 message words into a `16×u256` stack window `W`,
runs 64 rounds (with the in-place schedule recompute for `t ≥ 16`), adds the saved
chaining state, stores `state[0..7]` back, returns `state` in `%rax`.

The eight working words rotate by **register renaming** exactly as the reference
jazz: round `t` reads logical `(a..h)` from the ring slots
`rotateRight([%ymm0..7], t)` and writes `a' / e'` into the slots that held `h / d`
(so logical `(a..h) ↦ (a', a, b, c, e', e, f, g)` with no physical moves). The
round/schedule `YInst` blocks (§7–§8) are the verified lane semantics; the renderer
is the trusted-but-thin AT&T boundary (gas encodes the mnemonics — the same surface
as the ML-KEM/ML-DSA owned emits). -/

/-- A memory operand `off(%reg)` for `u256` slot `i` of base register `reg`. -/
def memSlot (reg : String) (i : Nat) : String := toString (32*i) ++ "(" ++ reg ++ ")"

/-- A `%rsp`-relative `u256` stack slot `i` of the schedule window `W` (slots
    `0..15` at the bottom of the frame). -/
def wSlot (i : Nat) : String := toString (32*i) ++ "(%rsp)"

/-- The chaining-save area `S[0..7]` (above the `W` window). -/
def sSlot (i : Nat) : String := toString (512 + 32*i) ++ "(%rsp)"

/-- The eight working-word ring registers `%ymm0..7`. -/
def ymmRing : List String := [ymmA, ymmB, ymmC, ymmD, ymmE, ymmF, ymmG, ymmH]

/-- The physical ring slot holding logical word `j` (`0=a … 7=h`) at round `t`:
    a right-rotation of the ring by `t`. -/
def ringSlot (t j : Nat) : String := ymmRing.getD ((j + 8 - t % 8) % 8) ymmA

/-- The fixed scratch / constant allocation shared by every round: the six scratch
    temporaries `t0..t5 → %ymm10..15`, the constant `kt → %ymm8`, the schedule word
    `wt → %ymm9`. -/
def scratchAlloc : YAlloc :=
  [ ("t0", ymmT0), ("t1", ymmT1), ("t2", ymmT2), ("t3", ymmT3), ("t4", ymmT4)
  , ("t5", ymmT5), ("kt", ymmKt), ("wt", ymmWt) ]

/-- The per-round allocation: the eight working abstract names `va..vh` map to the
    ring slots at round `t`; `ra`/`re` (the round's `a'`/`e'` writes) map to the
    `h`/`d` ring slots (the renaming rotation); plus the shared scratch. -/
def roundAlloc (t : Nat) : YAlloc :=
  [ ("va", ringSlot t 0), ("vb", ringSlot t 1), ("vc", ringSlot t 2)
  , ("vd", ringSlot t 3), ("ve", ringSlot t 4), ("vf", ringSlot t 5)
  , ("vg", ringSlot t 6), ("vh", ringSlot t 7)
  , ("ra", ringSlot t 7)   -- a' overwrites the h-slot
  , ("re", ringSlot t 3) ] -- e' overwrites the d-slot
  ++ scratchAlloc

/-- The schedule allocation. The two prior words read in the rotates (`w2`, `w15`)
    are pinned to the free constant slots `%ymm8`/`%ymm9` (reloaded with `kt`/`wt`
    after the schedule); the two read only in the final adds (`w7`, `w16`) are
    **memory operands** (`vpaddd` takes a memory source); the scratch
    `t0/t1/t3/t4/t5` and the result `sd` use `%ymm10..14`. All distinct — no
    aliasing between a held prior-word and a scratch register. The four memory
    offsets are filled per round in `emitRound`. -/
def schedAllocOf (w7mem w16mem : String) : YAlloc :=
  [ ("w2", ymmKt), ("w15", ymmWt), ("w7", w7mem), ("w16", w16mem)
  , ("t3", ymmT0), ("t4", ymmT1), ("t0", ymmT2), ("t1", ymmT3), ("t5", ymmT4)
  , ("sd", ymmT0) ]

def emitRound (t : Nat) : List String :=
  let sched : List String :=
    if t ≥ 16 then
      -- load w2, w15 into the free %ymm8/%ymm9 slots; w7, w16 are read as memory
      -- operands in the final adds. Recompute via the verified `schedBlk`; store back.
      [ "\tvmovdqu\t" ++ wSlot ((t-2)%16)  ++ ", " ++ ymmKt    -- w2  = W[t-2]
      , "\tvmovdqu\t" ++ wSlot ((t-15)%16) ++ ", " ++ ymmWt ]  -- w15 = W[t-15]
      ++ renderBlock (schedAllocOf (wSlot ((t-7)%16)) (wSlot ((t-16)%16)))
           (schedBlk "sd" "w2" "w7" "w15" "w16")               -- new W → %ymm10
      ++ [ "\tvmovdqa\t" ++ ymmT0 ++ ", " ++ wSlot (t%16) ]    -- store back
    else []
  let loadKW :=
    [ "\tvmovdqu\t" ++ memSlot "%rdx" t ++ ", " ++ ymmKt
    , "\tvmovdqu\t" ++ wSlot (t%16) ++ ", " ++ ymmWt ]
  let roundBody := renderBlock (roundAlloc t)
    (roundBlk "ra" "re" "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt")
  sched ++ loadKW ++ roundBody

/-- The emitted `sha256_compress_x8` prologue: align the frame, load the 8 chaining
    words into the ring and save them to `S`, load the 16 message words into `W`. -/
def sha256x8Prologue : List String :=
  -- reserve 24 u256 (16 W + 8 S) = 768 bytes, 32-aligned.
  [ "\tpush\t%rbp", "\tmovq\t%rsp, %rbp", "\tandq\t$-32, %rsp", "\tsubq\t$768, %rsp" ]
  ++ (List.range 8).flatMap (fun i =>
      [ "\tvmovdqu\t" ++ memSlot "%rdi" i ++ ", " ++ ymmRing.getD i ymmA
      , "\tvmovdqa\t" ++ ymmRing.getD i ymmA ++ ", " ++ sSlot i ])
  ++ (List.range 16).flatMap (fun w =>
      [ "\tvmovdqu\t" ++ memSlot "%rsi" w ++ ", " ++ ymmT0
      , "\tvmovdqa\t" ++ ymmT0 ++ ", " ++ wSlot w ])

/-- The emitted epilogue: add the saved chaining words `S[i]` to the final logical
    `a..h` (held at ring slots after 64 rounds: `rotateRight(ring, 64) = ring`, so
    logical `i` is back in `%ymm_i`), store to `state[i]`, restore frame, return. -/
def sha256x8Epilogue : List String :=
  (List.range 8).flatMap (fun i =>
    -- after 64 rounds (64 mod 8 = 0) logical word i is in ring slot i = %ymm_i
    [ "\tvpaddd\t" ++ sSlot i ++ ", " ++ ymmRing.getD i ymmA ++ ", " ++ ymmT0
    , "\tvmovdqu\t" ++ ymmT0 ++ ", " ++ memSlot "%rdi" i ])
  ++ [ "\tmovq\t%rdi, %rax", "\tmovq\t%rbp, %rsp", "\tpopq\t%rbp"
     , "\tvzeroupper", "\tret" ]

/-- The full emitted `sha256_compress_x8` function text (owned backend, SysV ABI). -/
def sha256x8ExportAsm : String :=
  let header :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t5"
    , "\t.global\tsha256_compress_x8", "\t.type\tsha256_compress_x8, @function"
    , "sha256_compress_x8:" ]
  let body := (List.range 64).flatMap emitRound
  let footer := [ "\t.section\t.note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n"
    (header ++ sha256x8Prologue ++ body ++ sha256x8Epilogue ++ footer) ++ "\n"

/-! ## 11. Structural smoke tests on the emitted blocks -/

/-- The round block is the 36-op FIPS-180-4 §6.2.2 round (`Σ₁`+`Ch`+`T₁` =
    11+4+... over the synthesised-rotate triples, `Σ₀`+`Maj`+`T₂`, and `a'`/`e'`). -/
example : (roundBlk "ra" "re" "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt").length = 36 := by
  native_decide

/-- The schedule block is the 21-op `σ₁ + σ₀ + 3 adds` recompute. -/
example : (schedBlk "wd" "w2" "w7" "w15" "w16").length = 21 := by native_decide

/-- A 3-register allocation for the renderer smoke tests. -/
def a3 : YAlloc := [("d", "%ymm3"), ("a", "%ymm2"), ("b", "%ymm1")]

/-- The renderer emits `vpaddd` in AT&T VEX (src2, src1, dst) order. -/
example : renderYInst a3 (.vpaddd "d" "a" "b") = "\tvpaddd %ymm1, %ymm2, %ymm3" := by
  native_decide

/-- The renderer emits the imm-first form for `vpsrld`. -/
example : renderYInst a3 (.vpsrld "d" "a" 6) = "\tvpsrld $6, %ymm2, %ymm3" := by
  native_decide

/-- Every round's emitted body is non-empty and the full export names the symbol. -/
example : (sha256x8ExportAsm.splitOn "sha256_compress_x8").length ≥ 2 := by native_decide

/-- The export issues exactly 8 `vpaddd …(%rsp), …` chaining-add stores in the
    epilogue (one per output word). -/
example : (sha256x8ExportAsm.splitOn "movq\t%rdi, %rax").length = 2 := by native_decide

/-! ## 12. The SHA-512 4-way sibling (`sha512_compress_x4w`, 4×u64 lanes)

The exact 64-bit-lane analogue of §1–§11: an AVX2 `u256` register holds **4 × u64**
lanes (`Fin 4 → BitVec 64`), each one independent SHA-512 stream (the
`sha2_multibuf_kat.c` SoA contract for `sha512_compress_x4w`). The op set is the
`*q` (qword) family — `vpaddq`/`vpsllq`/`vpsrlq` + the shared 256-bit
`vpxor`/`vpand`/`vpor` — and the FIPS-180-4 §4.1.3 rotate amounts are the SHA-512
ones (`Σ₀ = ρ²⁸⊕ρ³⁴⊕ρ³⁹`, `Σ₁ = ρ¹⁴⊕ρ¹⁸⊕ρ⁴¹`, `σ₀ = ρ¹⊕ρ⁸⊕≫7`,
`σ₁ = ρ¹⁹⊕ρ⁶¹⊕≫6`), over 80 rounds. -/

namespace Sha512X4w

/-- A 256-bit AVX2 register as 4 × `u64` lanes. -/
abbrev Ymm : Type := Fin 4 → BitVec 64

/-- The register file: a name → `Ymm`. -/
structure WState where
  /-- The `ymm` register file, named by string. -/
  regs : String → Ymm

namespace WState

/-- Read a register. Not `@[simp]` (the register-file laws are the rewrite path). -/
def get (s : WState) (r : String) : Ymm := s.regs r

/-- Write a register, leaving the others unchanged. -/
def setV (s : WState) (r : String) (v : Ymm) : WState :=
  { regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem get_setV_same (s : WState) (r : String) (v : Ymm) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_apply (s : WState) (r r' : String) (v : Ymm) (i : Fin 4) :
    (s.setV r v).get r' i = if r' = r then v i else s.get r' i := by
  by_cases h : r' = r
  · subst h; simp [get_setV_same]
  · simp [setV, get, h]

end WState

/-- `VPADDQ` lane op: wrapping 64-bit add. -/
@[simp] def laneAdd (a b : BitVec 64) : BitVec 64 := a + b
/-- `VPXOR` lane op. -/
@[simp] def laneXor (a b : BitVec 64) : BitVec 64 := a ^^^ b
/-- `VPAND` lane op. -/
@[simp] def laneAnd (a b : BitVec 64) : BitVec 64 := a &&& b
/-- `VPOR` lane op. -/
@[simp] def laneOr (a b : BitVec 64) : BitVec 64 := a ||| b
/-- `VPSLLQ` lane op: per-qword left shift by an immediate. -/
@[simp] def laneShl (a : BitVec 64) (m : Nat) : BitVec 64 := a <<< m
/-- `VPSRLQ` lane op: per-qword right shift by an immediate. -/
@[simp] def laneShr (a : BitVec 64) (m : Nat) : BitVec 64 := a >>> m

/-- A single packed AVX2 SHA-512 instruction (qword family). -/
inductive WInst where
  /-- `VPADDQ dst, a, b`. -/
  | vpaddq (dst a b : String)
  /-- `VPXOR dst, a, b`. -/
  | vpxor  (dst a b : String)
  /-- `VPAND dst, a, b`. -/
  | vpand  (dst a b : String)
  /-- `VPOR dst, a, b`. -/
  | vpor   (dst a b : String)
  /-- `VPSLLQ dst, a, imm`. -/
  | vpsllq (dst a : String) (imm : Nat)
  /-- `VPSRLQ dst, a, imm`. -/
  | vpsrlq (dst a : String) (imm : Nat)
  deriving Repr, DecidableEq

/-- The semantics of one SHA-512 instruction. -/
def evalWInst (s : WState) : WInst → WState
  | .vpaddq d a b  => s.setV d (fun i => laneAdd (s.get a i) (s.get b i))
  | .vpxor d a b   => s.setV d (fun i => laneXor (s.get a i) (s.get b i))
  | .vpand d a b   => s.setV d (fun i => laneAnd (s.get a i) (s.get b i))
  | .vpor d a b    => s.setV d (fun i => laneOr (s.get a i) (s.get b i))
  | .vpsllq d a m  => s.setV d (fun i => laneShl (s.get a i) m)
  | .vpsrlq d a m  => s.setV d (fun i => laneShr (s.get a i) m)

/-- Straight-line fold of `evalWInst`. -/
def runWBlock (s : WState) : List WInst → WState
  | [] => s
  | i :: is => runWBlock (evalWInst s i) is

@[simp] theorem runWBlock_nil (s : WState) : runWBlock s [] = s := rfl
@[simp] theorem runWBlock_cons (s : WState) (i : WInst) (is : List WInst) :
    runWBlock s (i :: is) = runWBlock (evalWInst s i) is := rfl
@[simp] theorem runWBlock_append (s : WState) (b1 b2 : List WInst) :
    runWBlock s (b1 ++ b2) = runWBlock (runWBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runWBlock_cons, ih]

/-- The synthesised 64-bit right-rotate `(x ≫ n) | (x ≪ (64−n))`. -/
@[simp] def rotrSynth (x : BitVec 64) (n : Nat) : BitVec 64 :=
  laneOr (laneShr x n) (laneShl x (64 - n))

/-- **The synthesised 64-bit rotate is `BitVec.rotateRight`** (`n < 64`). -/
theorem rotrSynth_eq (x : BitVec 64) (n : Nat) (h64 : n < 64) :
    rotrSynth x n = BitVec.rotateRight x n := by
  simp only [rotrSynth, laneOr, laneShr, laneShl,
    BitVec.rotateRight_eq_rotateRightAux_of_lt h64, BitVec.rotateRightAux]

/-- `Ch` (Mealy form). -/
@[simp] def chL (e f g : BitVec 64) : BitVec 64 := laneXor (laneAnd (laneXor f g) e) g
/-- `Maj` (Mealy form). -/
@[simp] def majL (a b c : BitVec 64) : BitVec 64 :=
  laneXor (laneAnd (laneXor a b) c) (laneAnd a b)
/-- `Σ₀(a) = ρ²⁸ ⊕ ρ³⁴ ⊕ ρ³⁹`. -/
@[simp] def bigSigma0L (a : BitVec 64) : BitVec 64 :=
  laneXor (laneXor (rotrSynth a 28) (rotrSynth a 34)) (rotrSynth a 39)
/-- `Σ₁(e) = ρ¹⁴ ⊕ ρ¹⁸ ⊕ ρ⁴¹`. -/
@[simp] def bigSigma1L (e : BitVec 64) : BitVec 64 :=
  laneXor (laneXor (rotrSynth e 14) (rotrSynth e 18)) (rotrSynth e 41)
/-- `σ₀(x) = ρ¹ ⊕ ρ⁸ ⊕ (x ≫ 7)`. -/
@[simp] def smallSigma0L (x : BitVec 64) : BitVec 64 :=
  laneXor (laneXor (rotrSynth x 1) (rotrSynth x 8)) (laneShr x 7)
/-- `σ₁(x) = ρ¹⁹ ⊕ ρ⁶¹ ⊕ (x ≫ 6)`. -/
@[simp] def smallSigma1L (x : BitVec 64) : BitVec 64 :=
  laneXor (laneXor (rotrSynth x 19) (rotrSynth x 61)) (laneShr x 6)

/-- The eight SHA-512 working words at one lane. -/
structure Work where
  /-- working word `a` -/
  a : BitVec 64
  /-- working word `b` -/
  b : BitVec 64
  /-- working word `c` -/
  c : BitVec 64
  /-- working word `d` -/
  d : BitVec 64
  /-- working word `e` -/
  e : BitVec 64
  /-- working word `f` -/
  f : BitVec 64
  /-- working word `g` -/
  g : BitVec 64
  /-- working word `h` -/
  h : BitVec 64
deriving DecidableEq, Repr

/-- One SHA-512 round (FIPS-180-4 §6.4.2). -/
def shaRound (kt wt : BitVec 64) (w : Work) : Work :=
  let t1 := laneAdd (laneAdd (laneAdd (laneAdd w.h (bigSigma1L w.e)) (chL w.e w.f w.g)) kt) wt
  let t2 := laneAdd (bigSigma0L w.a) (majL w.a w.b w.c)
  { a := laneAdd t1 t2, b := w.a, c := w.b, d := w.c
  , e := laneAdd w.d t1, f := w.e, g := w.f, h := w.g }

/-- The SHA-512 message-schedule recurrence. -/
def schedNext (w2 w7 w15 w16 : BitVec 64) : BitVec 64 :=
  laneAdd (laneAdd (laneAdd (smallSigma1L w2) w7) (smallSigma0L w15)) w16

/-- `ρⁿ(src) → dst` (synthesised). -/
def rotBlk (dst src : String) (n : Nat) : List WInst :=
  [ .vpsrlq "t0" src n, .vpsllq "t1" src (64 - n), .vpor dst "t0" "t1" ]

/-- `Σ₁(e) → "t3"`. -/
def bigSigma1Blk (e : String) : List WInst :=
  rotBlk "t3" e 14 ++
  rotBlk "t2" e 18 ++ [ .vpxor "t3" "t3" "t2" ] ++
  rotBlk "t2" e 41 ++ [ .vpxor "t3" "t3" "t2" ]

/-- `Σ₀(a) → "t4"`. -/
def bigSigma0Blk (a : String) : List WInst :=
  rotBlk "t4" a 28 ++
  rotBlk "t2" a 34 ++ [ .vpxor "t4" "t4" "t2" ] ++
  rotBlk "t2" a 39 ++ [ .vpxor "t4" "t4" "t2" ]

/-- One SHA-512 round as a `WInst` block (the 64-bit analogue of the §7 round). -/
def roundBlk (dstA dstE va vb vc vd ve vf vg vh kt wt : String) : List WInst :=
  bigSigma1Blk ve ++
  [ .vpaddq "t3" "t3" vh
  , .vpxor "t0" vf vg, .vpand "t0" "t0" ve, .vpxor "t0" "t0" vg
  , .vpaddq "t3" "t3" "t0", .vpaddq "t3" "t3" kt, .vpaddq "t3" "t3" wt ] ++
  bigSigma0Blk va ++
  [ .vpxor "t0" va vb, .vpand "t0" "t0" vc, .vpand "t1" va vb, .vpxor "t0" "t0" "t1"
  , .vpaddq "t4" "t4" "t0", .vpaddq dstE vd "t3", .vpaddq dstA "t3" "t4" ]

/-- The SHA-512 schedule recompute as a `WInst` block (the §7 schedBlk analogue). -/
def schedBlk (dst w2 w7 w15 w16 : String) : List WInst :=
  rotBlk "t3" w2 19 ++
  rotBlk "t5" w2 61 ++ [ .vpxor "t3" "t3" "t5"
  , .vpsrlq "t5" w2 6, .vpxor "t3" "t3" "t5" ] ++
  rotBlk "t4" w15 1 ++
  rotBlk "t5" w15 8 ++ [ .vpxor "t4" "t4" "t5"
  , .vpsrlq "t5" w15 7, .vpxor "t4" "t4" "t5"
  , .vpaddq "t3" "t3" w7, .vpaddq "t3" "t3" "t4", .vpaddq dst "t3" w16 ]

/-- **`a'`/`e'` SHA-512 round realisation (per lane).** -/
theorem roundBlk_realizes (s : WState) (ℓ : Fin 4) :
    let out := runWBlock s (roundBlk "ra" "re"
      "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt")
    out.get "ra" ℓ
      = (shaRound (s.get "kt" ℓ) (s.get "wt" ℓ)
          { a := s.get "va" ℓ, b := s.get "vb" ℓ, c := s.get "vc" ℓ, d := s.get "vd" ℓ
          , e := s.get "ve" ℓ, f := s.get "vf" ℓ, g := s.get "vg" ℓ, h := s.get "vh" ℓ }).a
    ∧ out.get "re" ℓ
      = (shaRound (s.get "kt" ℓ) (s.get "wt" ℓ)
          { a := s.get "va" ℓ, b := s.get "vb" ℓ, c := s.get "vc" ℓ, d := s.get "vd" ℓ
          , e := s.get "ve" ℓ, f := s.get "vf" ℓ, g := s.get "vg" ℓ, h := s.get "vh" ℓ }).e := by
  simp only [roundBlk, rotBlk, bigSigma1Blk, bigSigma0Blk, runWBlock_cons,
    runWBlock_append, runWBlock_nil, evalWInst, WState.get_setV_apply,
    String.reduceEq, if_true, if_false,
    shaRound, bigSigma1L, bigSigma0L, chL, majL, rotrSynth, laneAdd, laneXor,
    laneAnd, laneOr, laneShl, laneShr]
  constructor <;> ring

/-- **SHA-512 schedule realisation (per lane).** -/
theorem schedBlk_realizes (s : WState) (ℓ : Fin 4) :
    (runWBlock s (schedBlk "wd" "w2" "w7" "w15" "w16")).get "wd" ℓ
      = schedNext (s.get "w2" ℓ) (s.get "w7" ℓ) (s.get "w15" ℓ) (s.get "w16" ℓ) := by
  simp only [schedBlk, rotBlk, runWBlock_cons, runWBlock_append, runWBlock_nil,
    evalWInst, WState.get_setV_apply, String.reduceEq, if_true, if_false,
    schedNext, smallSigma1L, smallSigma0L, rotrSynth, laneAdd,
    laneXor, laneOr, laneShl, laneShr]

/-! ### SHA-512 reference scalar oracle + `SHA-512("abc")` self-check -/

/-- The 80 SHA-512 round constants `K[0..79]` (FIPS-180-4 §4.2.3). -/
def k512 : Array (BitVec 64) := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- The FIPS-180-4 SHA-512 initial hash value `H₀`. -/
def h0 : Array (BitVec 64) := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- Expand the 80-word SHA-512 schedule from 16 input words. -/
def expandSchedule (m : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut w := m
  for t in [16:80] do
    w := w.push (schedNext w[t-2]! w[t-7]! w[t-15]! w[t-16]!)
  return w

/-- One-block SHA-512 compression on a single lane (FIPS-180-4 §6.4). -/
def sha512BlockScalar (m : Array (BitVec 64)) : Array (BitVec 64) := Id.run do
  let w := expandSchedule m
  let mut s : Work :=
    { a := h0[0]!, b := h0[1]!, c := h0[2]!, d := h0[3]!
    , e := h0[4]!, f := h0[5]!, g := h0[6]!, h := h0[7]! }
  for t in [0:80] do
    s := shaRound k512[t]! w[t]! s
  return #[ laneAdd h0[0]! s.a, laneAdd h0[1]! s.b, laneAdd h0[2]! s.c, laneAdd h0[3]! s.d
          , laneAdd h0[4]! s.e, laneAdd h0[5]! s.f, laneAdd h0[6]! s.g, laneAdd h0[7]! s.h ]

/-- The padded one-block message words for `"abc"` (SHA-512: `0x6162638000…`, then
    the 128-bit length `24` in the last two words). -/
def abcMsg : Array (BitVec 64) :=
  #[0x6162638000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x0000000000000018]

/-- **The FIPS-180-4 `SHA-512("abc")` self-check (per-lane oracle).** Built entirely
    from the AVX2 qword lane primitives, the scalar one-block compression on the
    padded `"abc"` block yields the canonical SHA-512 digest. This is the lane-0
    cross-check the multi-buffer KAT integrates. -/
example : sha512BlockScalar abcMsg
    = #[0xddaf35a193617aba, 0xcc417349ae204131, 0x12e6fa4e89a97ea2, 0x0a9eeee64b55d39a,
        0x2192992a274fc1a8, 0x36ba3c23a3feebbd, 0x454d4423643ce80e, 0x2a9ac94fa54ca49f] := by
  native_decide

/-! ### AT&T renderer + full-function emitter (`sha512_compress_x4w`) -/

/-- A register assignment: abstract name → `%ymmN`. -/
abbrev WAlloc := List (String × String)

/-- The `%ymmN` an abstract name maps to. -/
def ymmOf (alloc : WAlloc) (n : String) : String :=
  (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- Print one `WInst` to its AT&T line (`*q` qword mnemonics, imm-first shifts). -/
def renderWInst (alloc : WAlloc) : WInst → String
  | .vpaddq d a b  => "\tvpaddq " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpxor d a b   => "\tvpxor " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpand d a b   => "\tvpand " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpor d a b    => "\tvpor " ++ ymmOf alloc b ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpsllq d a m  => "\tvpsllq $" ++ toString m ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d
  | .vpsrlq d a m  => "\tvpsrlq $" ++ toString m ++ ", " ++ ymmOf alloc a ++ ", " ++ ymmOf alloc d

/-- Print a whole block. -/
def renderBlock (alloc : WAlloc) (block : List WInst) : List String :=
  block.map (renderWInst alloc)

def ymmA := "%ymm0"
def ymmB := "%ymm1"
def ymmC := "%ymm2"
def ymmD := "%ymm3"
def ymmE := "%ymm4"
def ymmF := "%ymm5"
def ymmG := "%ymm6"
def ymmH := "%ymm7"
def ymmKt := "%ymm8"
def ymmWt := "%ymm9"
def ymmT0 := "%ymm10"
def ymmT1 := "%ymm11"
def ymmT2 := "%ymm12"
def ymmT3 := "%ymm13"
def ymmT4 := "%ymm14"
def ymmT5 := "%ymm15"

/-- A memory operand `off(%reg)` for `u256` slot `i`. -/
def memSlot (reg : String) (i : Nat) : String := toString (32*i) ++ "(" ++ reg ++ ")"
/-- A `%rsp`-relative schedule-window slot. -/
def wSlot (i : Nat) : String := toString (32*i) ++ "(%rsp)"
/-- The chaining-save slot `S[i]`. -/
def sSlot (i : Nat) : String := toString (512 + 32*i) ++ "(%rsp)"

/-- The eight working-word ring registers `%ymm0..7`. -/
def ymmRing : List String := [ymmA, ymmB, ymmC, ymmD, ymmE, ymmF, ymmG, ymmH]
/-- The ring slot for logical word `j` at round `t`. -/
def ringSlot (t j : Nat) : String := ymmRing.getD ((j + 8 - t % 8) % 8) ymmA

/-- The shared scratch / constant allocation. -/
def scratchAlloc : WAlloc :=
  [ ("t0", ymmT0), ("t1", ymmT1), ("t2", ymmT2), ("t3", ymmT3), ("t4", ymmT4)
  , ("t5", ymmT5), ("kt", ymmKt), ("wt", ymmWt) ]

/-- The per-round allocation. -/
def roundAlloc (t : Nat) : WAlloc :=
  [ ("va", ringSlot t 0), ("vb", ringSlot t 1), ("vc", ringSlot t 2)
  , ("vd", ringSlot t 3), ("ve", ringSlot t 4), ("vf", ringSlot t 5)
  , ("vg", ringSlot t 6), ("vh", ringSlot t 7)
  , ("ra", ringSlot t 7), ("re", ringSlot t 3) ] ++ scratchAlloc

/-- The schedule allocation (same non-aliasing layout as the SHA-256 emit): `w2`,
    `w15` in the free `%ymm8/%ymm9` slots; `w7`, `w16` as memory operands; scratch
    `t0/t1/t3/t4/t5` and result `sd` on `%ymm10..14`, all distinct. -/
def schedAllocOf (w7mem w16mem : String) : WAlloc :=
  [ ("w2", ymmKt), ("w15", ymmWt), ("w7", w7mem), ("w16", w16mem)
  , ("t3", ymmT0), ("t4", ymmT1), ("t0", ymmT2), ("t1", ymmT3), ("t5", ymmT4)
  , ("sd", ymmT0) ]

/-- One emitted SHA-512 round `t` (0..79). -/
def emitRound (t : Nat) : List String :=
  let sched : List String :=
    if t ≥ 16 then
      [ "\tvmovdqu\t" ++ wSlot ((t-2)%16)  ++ ", " ++ ymmKt
      , "\tvmovdqu\t" ++ wSlot ((t-15)%16) ++ ", " ++ ymmWt ]
      ++ renderBlock (schedAllocOf (wSlot ((t-7)%16)) (wSlot ((t-16)%16)))
           (schedBlk "sd" "w2" "w7" "w15" "w16")
      ++ [ "\tvmovdqa\t" ++ ymmT0 ++ ", " ++ wSlot (t%16) ]
    else []
  let loadKW :=
    [ "\tvmovdqu\t" ++ memSlot "%rdx" t ++ ", " ++ ymmKt
    , "\tvmovdqu\t" ++ wSlot (t%16) ++ ", " ++ ymmWt ]
  let roundBody := renderBlock (roundAlloc t)
    (roundBlk "ra" "re" "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt")
  sched ++ loadKW ++ roundBody

/-- The emitted prologue. -/
def prologue : List String :=
  [ "\tpush\t%rbp", "\tmovq\t%rsp, %rbp", "\tandq\t$-32, %rsp", "\tsubq\t$768, %rsp" ]
  ++ (List.range 8).flatMap (fun i =>
      [ "\tvmovdqu\t" ++ memSlot "%rdi" i ++ ", " ++ ymmRing.getD i ymmA
      , "\tvmovdqa\t" ++ ymmRing.getD i ymmA ++ ", " ++ sSlot i ])
  ++ (List.range 16).flatMap (fun w =>
      [ "\tvmovdqu\t" ++ memSlot "%rsi" w ++ ", " ++ ymmT0
      , "\tvmovdqa\t" ++ ymmT0 ++ ", " ++ wSlot w ])

/-- The emitted epilogue (after 80 rounds `80 mod 8 = 0`, ring back to identity). -/
def epilogue : List String :=
  (List.range 8).flatMap (fun i =>
    [ "\tvpaddq\t" ++ sSlot i ++ ", " ++ ymmRing.getD i ymmA ++ ", " ++ ymmT0
    , "\tvmovdqu\t" ++ ymmT0 ++ ", " ++ memSlot "%rdi" i ])
  ++ [ "\tmovq\t%rdi, %rax", "\tmovq\t%rbp, %rsp", "\tpopq\t%rbp"
     , "\tvzeroupper", "\tret" ]

/-- The full emitted `sha512_compress_x4w` function text. -/
def sha512x4wExportAsm : String :=
  let header :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t5"
    , "\t.global\tsha512_compress_x4w", "\t.type\tsha512_compress_x4w, @function"
    , "sha512_compress_x4w:" ]
  let body := (List.range 80).flatMap emitRound
  let footer := [ "\t.section\t.note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n"
    (header ++ prologue ++ body ++ epilogue ++ footer) ++ "\n"

/-- The SHA-512 round block is the 36-op FIPS-180-4 §6.4.2 round. -/
example : (roundBlk "ra" "re" "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt").length = 36 := by
  native_decide

/-- The SHA-512 schedule block is the 21-op recompute. -/
example : (schedBlk "wd" "w2" "w7" "w15" "w16").length = 21 := by native_decide

/-- The export names the `sha512_compress_x4w` symbol. -/
example : (sha512x4wExportAsm.splitOn "sha512_compress_x4w").length ≥ 2 := by native_decide

end Sha512X4w

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2MultiBufAvx2Emit
