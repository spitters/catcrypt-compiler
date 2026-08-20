/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# BLAKE2 compression (BLAKE2b + BLAKE2s) emitted through the OWNED x86 backend

A clean pipeline-coverage gap: until now the bench had **no** BLAKE2 emit of any
kind. This module emits the BLAKE2 compression function `F` — the round loop over
the mixing function `G` on the 16-word work vector `v` — as a straight-line
`List (JInstr w)` block in the **owned** x86 backend
(`X86Backend/{JasminModel, X86Dialect, AsmPrinter}`), *not* through the
`Com jasminDialect → .jazz → external jasminc` path. It is the direct BLAKE2
analogue of `BLAKE3/CompressEmit.lean`: BLAKE2's `G` is the same
ChaCha-style quarter-round skeleton with two message-word injections.

## BLAKE2 is two width instances of one ARX core (RFC 7693)

BLAKE2 comes in two word widths, captured here as the width parameter `w` of the
owned model's `JInstr w` / `BitVec w` semantics — so a single emit core covers
both with no per-width masking:

* **BLAKE2b** — `w = 64`, 12 rounds, G rotations `(R1,R2,R3,R4) = (32,24,16,63)`;
* **BLAKE2s** — `w = 32`, 10 rounds, G rotations `(16,12,8,7)`.

The mixing function `G(a,b,c,d, x,y)` (RFC 7693 §3.1) is

    a = a + b + x;   d = (d ^ a) >>> R1
    c = c + d;       b = (b ^ c) >>> R2
    a = a + b + y;   d = (d ^ a) >>> R3
    c = c + d;       b = (b ^ c) >>> R4

Each round applies `G` over the 4 columns then the 4 diagonals, reading the 16
message words `m[0..15]` under the round's permutation `σ` (RFC 7693 §2.7; BLAKE2b
reuses rows 0,1 for its extra rounds 10,11). The compression `F` builds the work
vector `v[0..15] = h[0..7] ‖ IV[0..7]` with the counter/finalization xors folded
into `v[12..15]` (driver/harness-level, like BLAKE3's state initialisation), runs
the rounds, then the output feed-forward

    for i in 0..8:  h[i] = h[i] ^ v[i] ^ v[i+8]

— the BLAKE2 finalization (note: BLAKE2 feeds `v[i] ^ v[i+8]` over the saved
`h[i]`, where BLAKE3 instead writes `v[i] ^ v[i+8]` / `v[i+8] ^ cv[i]`).

## Rotate via `shr; shl; or` (no native opcode; same as SHA-2/BLAKE3)

The owned model has no native rotate opcode, so the right-rotate is the
backend's existing `shr; shl; or` synthesis — exactly the SHA-2/BLAKE3 path.
In `BitVec w` it is precisely `BitVec.rotateRight` (`blake2_ror_synth`).

## What is verified vs. trusted

* **Verified**: the rotate synthesis equals `BitVec.rotateRight w`
  (`blake2_ror_synth`); one emitted `G` block, lowered through
  `X86Dialect.lowerBlock` and run via `runBlock`, computes the reference `gSpec`
  on concrete words at both widths (`blake2s_G_computes_spec`,
  `blake2b_G_computes_spec`, `native_decide` — a single G, REV-12-safe, not a
  whole-message KAT); `lowerBlock` of the whole body denotes `runBlock`
  (`blake2s_lower_denote` / `blake2b_lower_denote`, the `X86Dialect` tie).
  The whole-message known-answer test against the official BLAKE2 vectors is an
  external C harness around this emitted compression core.
* **Trusted (thin)**: the AT&T mnemonic printer (one line per `JInstr`) and the
  System V ABI glue — the same trusted-scaffold status as `AsmPrinter`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2Emit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The BLAKE2 reference compression spec (width-parametric, on `BitVec w`)

A direct transcription of the reference `G`/`round`/`F`, the value-correctness
target for the emitted block. The four G-rotation amounts are passed as a tuple
so the same spec serves both BLAKE2b `(32,24,16,63)` and BLAKE2s `(16,12,8,7)`. -/

/-- `w`-bit rotate-right by `n` (the reference `rotr`). -/
def rotr {w : Nat} (x : BitVec w) (n : Nat) : BitVec w := x.rotateRight n

/-- The 16-word work vector as a `Fin 16 → BitVec w`. -/
abbrev St (w : Nat) := Fin 16 → BitVec w

/-- Update slot `i` of a work vector with value `v`. -/
def St.set {w : Nat} (s : St w) (i : Fin 16) (v : BitVec w) : St w :=
  fun j => if j = i then v else s j

/-- The reference BLAKE2 `G` (RFC 7693 §3.1) on slots `a b c d`, injecting the two
    message words `mx my`, with the four right-rotation amounts `r1 r2 r3 r4`
    (`(32,24,16,63)` for BLAKE2b, `(16,12,8,7)` for BLAKE2s). -/
def gSpec {w : Nat} (s : St w) (a b c d : Fin 16) (mx my : BitVec w)
    (r1 r2 r3 r4 : Nat) : St w :=
  let va := s a + s b + mx
  let vd := rotr (s d ^^^ va) r1
  let vc := s c + vd
  let vb := rotr (s b ^^^ vc) r2
  let va := va + vb + my
  let vd := rotr (vd ^^^ va) r3
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) r4
  (((s.set a va).set d vd).set c vc).set b vb

/-! ## 2. The BLAKE2 message permutation σ (RFC 7693 §2.7) -/

/-- σ[r][p] — the message-word index used at column/diagonal slot `p` in round
    `r`. Ten rows; BLAKE2b's extra rounds 10,11 reuse rows 0,1 (`r % 10`). -/
def sigma : Nat → Nat → Nat
  | 0,  p => #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15].getD p 0
  | 1,  p => #[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3].getD p 0
  | 2,  p => #[11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4].getD p 0
  | 3,  p => #[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8].getD p 0
  | 4,  p => #[9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13].getD p 0
  | 5,  p => #[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9].getD p 0
  | 6,  p => #[12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11].getD p 0
  | 7,  p => #[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10].getD p 0
  | 8,  p => #[6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5].getD p 0
  | 9,  p => #[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0].getD p 0
  | (r+10), p => sigma (r % 10) p

/-! ## 3. The emitted `JInstr w` block

Work-vector slots live in register names `v0 .. v15`; message words are loaded on
demand (`m0 .. m15`); the read-only saved chaining state in `h0 .. h7`. The
rotate is the `shr; shl; or` synthesis at width `w`. -/

/-- A work-vector-slot register name (`v0 .. v15`). -/
def vReg (i : Nat) : String := "v" ++ toString i

/-- A message-word register name (`m0 .. m15`). -/
def mReg (i : Nat) : String := "m" ++ toString i

/-- A saved chaining-word register name (`h0 .. h7`). -/
def hReg (i : Nat) : String := "h" ++ toString i

/-- Synthesize a width-`w` rotate-right of register `dst` by `n` using a scratch
    register `tmp`: `tmp = dst; dst >>= n; tmp <<= (w-n); dst |= tmp`. The owned
    model's `BitVec w` semantics make this exactly `dst.rotateRight n`
    (`blake2_ror_synth`). -/
def rorSynth (w : Nat) (dst tmp : String) (n : Nat) : List (JInstr w) :=
  [ .mov tmp (.reg dst)
  , .shr dst (.imm n)
  , .shl tmp (.imm (w - n))
  , .or_ dst (.reg tmp) ]

/-- The `G` mixing on register names for slots `a b c d`, injecting message
    registers `mx my`, with rotation amounts `r1 r2 r3 r4`. Mirrors `gSpec`.
    Uses a fresh scratch register `g_t` (the rotate result is fully computed
    before the next rotate). -/
def emitG (w : Nat) (a b c d : Nat) (mx my : Nat) (r1 r2 r3 r4 : Nat) :
    List (JInstr w) :=
  let A := vReg a; let B := vReg b; let C := vReg c; let D := vReg d
  let MX := mReg mx; let MY := mReg my
  -- a = a + b + mx
  [ .add A (.reg B), .add A (.reg MX) ] ++
  -- d = (d ^ a) >>> r1
  [ .xor_ D (.reg A) ] ++ rorSynth w D "g_t" r1 ++
  -- c = c + d
  [ .add C (.reg D) ] ++
  -- b = (b ^ c) >>> r2
  [ .xor_ B (.reg C) ] ++ rorSynth w B "g_t" r2 ++
  -- a = a + b + my
  [ .add A (.reg B), .add A (.reg MY) ] ++
  -- d = (d ^ a) >>> r3
  [ .xor_ D (.reg A) ] ++ rorSynth w D "g_t" r3 ++
  -- c = c + d
  [ .add C (.reg D) ] ++
  -- b = (b ^ c) >>> r4
  [ .xor_ B (.reg C) ] ++ rorSynth w B "g_t" r4

/-- `Fin 16` from a `Nat` (mod 16). -/
def fin16 (n : Nat) : Fin 16 := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

/-- One BLAKE2 round `r`: `G` over the 4 columns then the 4 diagonals, reading the
    message words under `σ[r]`. Rotation amounts `r1 r2 r3 r4`. -/
def emitRound (w : Nat) (r : Nat) (r1 r2 r3 r4 : Nat) : List (JInstr w) :=
  emitG w 0 4 8  12 (sigma r 0)  (sigma r 1)  r1 r2 r3 r4 ++
  emitG w 1 5 9  13 (sigma r 2)  (sigma r 3)  r1 r2 r3 r4 ++
  emitG w 2 6 10 14 (sigma r 4)  (sigma r 5)  r1 r2 r3 r4 ++
  emitG w 3 7 11 15 (sigma r 6)  (sigma r 7)  r1 r2 r3 r4 ++
  emitG w 0 5 10 15 (sigma r 8)  (sigma r 9)  r1 r2 r3 r4 ++
  emitG w 1 6 11 12 (sigma r 10) (sigma r 11) r1 r2 r3 r4 ++
  emitG w 2 7 8  13 (sigma r 12) (sigma r 13) r1 r2 r3 r4 ++
  emitG w 3 4 9  14 (sigma r 14) (sigma r 15) r1 r2 r3 r4

/-! ## 4. Value correctness

The rotate synthesis equals `BitVec.rotateRight`, and one emitted `G` block,
lowered and run, computes `gSpec` on concrete words at both widths. -/

/-- **Rotate synthesis is `rotateRight`.** For any `w`-bit `x` and `n < w`,
    `(x >>> n) ||| (x <<< (w-n)) = x.rotateRight n`. This is the per-rotate
    correctness of `rorSynth` (the `shr; shl; or` triple) in `BitVec w`. -/
theorem blake2_ror_synth {w : Nat} (x : BitVec w) (n : Nat) (h : n < w) :
    (x >>> n) ||| (x <<< (w - n)) = x.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

/-- A concrete machine state seeding `v0..v15 = 1..16`, `m0 = mx`, `m1 = my`. -/
def gInit (w : Nat) (mx my : BitVec w) : JState w :=
  { regs := fun r =>
      (List.range 16).foldl
        (fun acc i => if r = vReg i then BitVec.ofNat w (i + 1) else acc)
        (if r = mReg 0 then mx else if r = mReg 1 then my else 0) }

/-- The reference initial work vector matching `gInit`. -/
def gInitSt (w : Nat) : St w := fun i => BitVec.ofNat w (i.val + 1)

/-- **One emitted BLAKE2s `G` computes the reference `gSpec`** (width 32, rotations
    `16,12,8,7`). On a concrete input the four updated slots of the run-`G`
    machine state equal `gSpec`. `native_decide` over a single G (REV-12-safe). -/
theorem blake2s_G_computes_spec :
    let mx : BitVec 32 := 0x11111111
    let my : BitVec 32 := 0x22222222
    let s := runBlock (gInit 32 mx my) (emitG 32 0 4 8 12 0 1 16 12 8 7)
    let spec := gSpec (gInitSt 32) 0 4 8 12 mx my 16 12 8 7
    s.get (vReg 0) = spec 0 ∧ s.get (vReg 12) = spec 12
      ∧ s.get (vReg 8) = spec 8 ∧ s.get (vReg 4) = spec 4 := by
  native_decide

/-- **One emitted BLAKE2b `G` computes the reference `gSpec`** (width 64, rotations
    `32,24,16,63`). `native_decide` over a single G (REV-12-safe). -/
theorem blake2b_G_computes_spec :
    let mx : BitVec 64 := 0x1111111111111111
    let my : BitVec 64 := 0x2222222222222222
    let s := runBlock (gInit 64 mx my) (emitG 64 0 4 8 12 0 1 32 24 16 63)
    let spec := gSpec (gInitSt 64) 0 4 8 12 mx my 32 24 16 63
    s.get (vReg 0) = spec 0 ∧ s.get (vReg 12) = spec 12
      ∧ s.get (vReg 8) = spec 8 ∧ s.get (vReg 4) = spec 4 := by
  native_decide

/-! ## 5. The full compression body as `JInstr w`

Load the 16 work-vector words `v0..v15` from `inp[0..15]`, the 16 message words
`m0..m15` from `inp[16..31]`, and the 8 saved chaining words `h0..h7` from
`inp[32..39]` (the counter/finalization xors are already folded into `v[12..15]`
at the input frame — driver-level, exactly like BLAKE3's state init). Run the
rounds, then the BLAKE2 feed-forward `h[i] = h[i] ^ v[i] ^ v[i+8]`, store the 8
new chaining words to `out[0..7]`. -/

/-- The `inp` base register name (System V arg1). -/
def inpBase : String := "inp"

/-- The `out` base register name (System V arg0). -/
def outBase : String := "out"

/-- Byte stride per word (`4` for BLAKE2s, `8` for BLAKE2b). -/
def stride (w : Nat) : Int := Int.ofNat (w / 8)

/-- Load `v0..v15` (`inp[0..15]`), `m0..m15` (`inp[16..31]`), `h0..h7`
    (`inp[32..39]`). Word `i` is at byte `stride·i` (packed). -/
def loadInputs (w : Nat) : List (JInstr w) :=
  (List.range 16).map (fun i => .loadMem (vReg i) inpBase (stride w * Int.ofNat i)) ++
  (List.range 16).map (fun i => .loadMem (mReg i) inpBase (stride w * Int.ofNat (16 + i))) ++
  (List.range 8).map  (fun i => .loadMem (hReg i) inpBase (stride w * Int.ofNat (32 + i)))

/-- All rounds (`emitRound 0 .. nr-1`) with rotations `r1 r2 r3 r4`. -/
def allRounds (w : Nat) (nr : Nat) (r1 r2 r3 r4 : Nat) : List (JInstr w) :=
  (List.range nr).flatMap (fun r => emitRound w r r1 r2 r3 r4)

/-- The BLAKE2 output feed-forward: `h[i] = h[i] ^ v[i] ^ v[i+8]` for `i < 8`. -/
def feedForward (w : Nat) : List (JInstr w) :=
  (List.range 8).flatMap (fun i =>
    [ .xor_ (hReg i) (.reg (vReg i)), .xor_ (hReg i) (.reg (vReg (8 + i))) ])

/-- Store the 8 new chaining words `h0..h7` to `out[0..7]`. -/
def storeOutputs (w : Nat) : List (JInstr w) :=
  (List.range 8).map (fun i => .storeMem outBase (stride w * Int.ofNat i) (.reg (hReg i)))

/-- The full BLAKE2 compression body: load, rounds, feed-forward, store. -/
def blake2CompressBlock (w : Nat) (nr : Nat) (r1 r2 r3 r4 : Nat) : List (JInstr w) :=
  loadInputs w ++ allRounds w nr r1 r2 r3 r4 ++ feedForward w ++ storeOutputs w

/-- **BLAKE2s** compression body: width 32, 10 rounds, rotations `16,12,8,7`. -/
def blake2sCompressBlock : List (JInstr 32) := blake2CompressBlock 32 10 16 12 8 7

/-- **BLAKE2b** compression body: width 64, 12 rounds, rotations `32,24,16,63`. -/
def blake2bCompressBlock : List (JInstr 64) := blake2CompressBlock 64 12 32 24 16 63

/-- **BLAKE2s body lowered denotes `runBlock`** (the owned-backend tie for the
    full straight-line compression at width 32). -/
theorem blake2s_lower_denote (s : JState 32) :
    (lowerBlock (Γ := []) blake2sCompressBlock).denote (.cons s .nil)
      = runBlock s blake2sCompressBlock :=
  lowerBlock_denote_closed _ s

/-- **BLAKE2b body lowered denotes `runBlock`** (the owned-backend tie for the
    full straight-line compression at width 64). -/
theorem blake2b_lower_denote (s : JState 64) :
    (lowerBlock (Γ := []) blake2bCompressBlock).denote (.cons s .nil)
      = runBlock s blake2bCompressBlock :=
  lowerBlock_denote_closed _ s

/-- Instruction count for BLAKE2s: 40 loads + 10·(8·26) round ops + 16 ff
    + 8 stores. Each G is 26 ops; ×8 G ×10 rounds = 2080; +40 +16 +8 = 2144. -/
theorem blake2s_block_length : blake2sCompressBlock.length = 2144 := by native_decide

/-- Instruction count for BLAKE2b: 40 loads + 12·(8·26) round ops + 16 ff
    + 8 stores. ×8 G ×12 rounds = 2496; +40 +16 +8 = 2560. -/
theorem blake2b_block_length : blake2bCompressBlock.length = 2560 := by native_decide

/-! ## 5b. Constant time, at every width and round count

The compression body reads and writes only through the two pointer bases
`inp`/`out` at word-indexed literal displacements, and the round/feed-forward
mixing is register ALU (`add`/`xor`/`shr`/`shl`/`or`). No instruction takes a
register-indexed address, so the whole family is in the direct-addressing
class, uniformly in the width `w`, the round count `nr`, and the rotation
amounts. -/

/-- The load prefix is in the direct-addressing class: each word is read at the
    literal displacement `stride w * i` off `inp`. -/
theorem loadInputs_allDirect (w : Nat) : allDirect (loadInputs w) = true := by
  simp [allDirect, loadInputs, IsDirect]

/-- The synthesized rotate is register ALU only. -/
theorem rorSynth_allDirect (w : Nat) (dst tmp : String) (n : Nat) :
    allDirect (rorSynth w dst tmp n) = true := by
  simp [allDirect, rorSynth, IsDirect]

/-- One `G` mixing is register ALU only. -/
theorem emitG_allDirect (w a b c d mx my r1 r2 r3 r4 : Nat) :
    allDirect (emitG w a b c d mx my r1 r2 r3 r4) = true := by
  simp [allDirect, emitG, rorSynth, IsDirect]

/-- One round — eight `G` mixings — is register ALU only. -/
theorem emitRound_allDirect (w r r1 r2 r3 r4 : Nat) :
    allDirect (emitRound w r r1 r2 r3 r4) = true := by
  have hA : ∀ a b : List (JInstr w),
      allDirect (a ++ b) = (allDirect a && allDirect b) := fun _ _ => List.all_append
  simp [emitRound, hA, emitG_allDirect]

/-- The whole round loop is register ALU only, for any round count. -/
theorem allRounds_allDirect (w nr r1 r2 r3 r4 : Nat) :
    allDirect (allRounds w nr r1 r2 r3 r4) = true := by
  have hA : ∀ a b : List (JInstr w),
      allDirect (a ++ b) = (allDirect a && allDirect b) := fun _ _ => List.all_append
  simp only [allRounds]
  induction List.range nr with
  | nil => rfl
  | cons _ _ ih => simp [hA, emitRound_allDirect, ih]

/-- The feed-forward is register `xor` only. -/
theorem feedForward_allDirect (w : Nat) : allDirect (feedForward w) = true := by
  simp [allDirect, feedForward, IsDirect]

/-- The store suffix writes at literal displacements off `out`. -/
theorem storeOutputs_allDirect (w : Nat) : allDirect (storeOutputs w) = true := by
  simp [allDirect, storeOutputs, IsDirect]

/-- The full compression body is in the direct-addressing class at every width,
    round count, and rotation schedule. -/
theorem blake2CompressBlock_allDirect (w nr r1 r2 r3 r4 : Nat) :
    allDirect (blake2CompressBlock w nr r1 r2 r3 r4) = true := by
  have hA : ∀ a b : List (JInstr w),
      allDirect (a ++ b) = (allDirect a && allDirect b) := fun _ _ => List.all_append
  simp [blake2CompressBlock, hA, loadInputs_allDirect, allRounds_allDirect,
    feedForward_allDirect, storeOutputs_allDirect]

/-- **Constant time, width- and round-parametric.** Every BLAKE2 compression
    body this module emits produces the same machine leakage trace from any two
    starting states, via `ConstantTimeCoverage.allDirect_constant_time`. -/
theorem blake2CompressBlock_constant_time (w nr r1 r2 r3 r4 : Nat)
    (s₁ s₂ : JState w) :
    blockLeak s₁ (blake2CompressBlock w nr r1 r2 r3 r4)
      = blockLeak s₂ (blake2CompressBlock w nr r1 r2 r3 r4) :=
  allDirect_constant_time _ (blake2CompressBlock_allDirect w nr r1 r2 r3 r4) s₁ s₂

/-- `blake2sCompressBlock` is in the direct-addressing class. -/
theorem blake2sCompressBlock_allDirect : allDirect blake2sCompressBlock = true :=
  blake2CompressBlock_allDirect 32 10 16 12 8 7

/-- **Constant time.** The emitted BLAKE2s compression produces the same machine
    leakage trace from any two starting states. -/
theorem blake2sCompressBlock_constant_time (s₁ s₂ : JState 32) :
    blockLeak s₁ blake2sCompressBlock = blockLeak s₂ blake2sCompressBlock :=
  blake2CompressBlock_constant_time 32 10 16 12 8 7 s₁ s₂

/-- `blake2bCompressBlock` is in the direct-addressing class. -/
theorem blake2bCompressBlock_allDirect : allDirect blake2bCompressBlock = true :=
  blake2CompressBlock_allDirect 64 12 32 24 16 63

/-- **Constant time.** The emitted BLAKE2b compression produces the same machine
    leakage trace from any two starting states. -/
theorem blake2bCompressBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ blake2bCompressBlock = blockLeak s₂ blake2bCompressBlock :=
  blake2CompressBlock_constant_time 64 12 32 24 16 63 s₁ s₂

/-! ## 6. Per-round denote-agreement (the round-fold composition)

Running the emitted body through `runBlock` factors exactly through running the
prefix then folding the remaining rounds — the round-fold composition that ties
the emitted kernel's structure to the `emitRound`/`allRounds` round loop. -/

/-- `runBlock` over a concatenation is the fold: run the prefix, then run the
    suffix on the resulting state. The structural composition lemma the round
    loop relies on. -/
theorem blake2_runBlock_append {w : Nat} (s : JState w) (b1 b2 : List (JInstr w)) :
    runBlock s (b1 ++ b2) = runBlock (runBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i t ih => simp [runBlock, ih]

/-- **The round loop folds over `runBlock`.** Running `allRounds` of `(nr+1)`
    rounds equals running the first `nr` rounds then `emitRound nr` on the
    result — `allRounds` is the left-fold of `emitRound` under `runBlock`. -/
theorem blake2_allRounds_succ {w : Nat} (s : JState w) (nr r1 r2 r3 r4 : Nat) :
    runBlock s (allRounds w (nr + 1) r1 r2 r3 r4)
      = runBlock (runBlock s (allRounds w nr r1 r2 r3 r4)) (emitRound w nr r1 r2 r3 r4) := by
  unfold allRounds
  rw [List.range_succ, List.flatMap_append, blake2_runBlock_append]
  simp

/-! ## 7. Frame-resident AT&T rendering (trusted thin scaffold)

The owned compression body uses 16 work-vector + 16 message + 8 saved-chaining
+ 1 rotate-scratch = 41 distinct value names, far above the GP pool, so it is
rendered **frame-resident** (the same load/compute/store discipline as
`BLAKE3/CompressEmit.lean`): every value name lives in a `cellW`-byte stack
cell off `%rsp`, and each `JInstr w` reloads its operands into the fixed working
registers, computes, and stores the destination cell. `inp`/`out` stay in their
argument registers `%rsi`/`%rdi`.

The renderer is width-parametric: BLAKE2s uses the 32-bit `l`-suffix / `%eXX`
working registers / 4-byte cells; BLAKE2b uses the 64-bit `q`-suffix / `%rXX`
working registers / 8-byte cells. The instruction `BitVec w` semantics already
auto-mask to the chosen width, so the same `blake2CompressBlock` lowers to the
correct AT&T at either width. -/

/-- The full ordered list of value names the body uses (work vector, message,
    saved chaining, rotate scratch), in a fixed layout order. The pointer bases
    `inp`/`out` are *not* cells (they live in argument registers). -/
def cellNames : List String :=
  (List.range 16).map vReg ++ (List.range 16).map mReg ++
  (List.range 8).map hReg ++ ["g_t"]

/-- A width's printer configuration: AT&T size suffix, working registers
    (dst/src/spare), pointer-relative size suffix for memory loads, and the
    cell size in bytes. -/
structure PrinterCfg where
  suf  : String  -- size suffix: "l" (32) or "q" (64)
  wax  : String  -- dst working register: "%eax" / "%rax"
  wcx  : String  -- src working register: "%ecx" / "%rcx"
  cellW : Int    -- cell size in bytes: 4 / 8

/-- BLAKE2s printer config (32-bit). -/
def cfg32 : PrinterCfg := { suf := "l", wax := "%eax", wcx := "%ecx", cellW := 4 }

/-- BLAKE2b printer config (64-bit). -/
def cfg64 : PrinterCfg := { suf := "q", wax := "%rax", wcx := "%rcx", cellW := 8 }

/-- The cell-frame offset of a value name (off `%rsp`), or `0` for the pointer
    bases (which never reach the cell path). -/
def cellOff (c : PrinterCfg) (n : String) : Int :=
  match cellNames.idxOf? n with
  | some k => c.cellW * Int.ofNat k
  | none => 0

/-- The total cell frame size in bytes (`#names × cellW`), rounded up to 16. -/
def frameBytes (c : PrinterCfg) : Nat :=
  ((cellNames.length * c.cellW.toNat + 15) / 16) * 16

/-- A value-name cell as an AT&T `%rsp`-relative memory operand. -/
def cell (c : PrinterCfg) (n : String) : String := toString (cellOff c n) ++ "(%rsp)"

/-- A width-`w` operand: an immediate `$v`, or a *cell load* of a register name
    into a given working register. Returns the operand string and the (possibly
    empty) reload line. -/
def loadOperand (c : PrinterCfg) (work : String) : JOperand → String × List String
  | .imm v => ("$" ++ toString v, [])
  | .reg r => (work, ["\tmov" ++ c.suf ++ " " ++ cell c r ++ ", " ++ work])

/-- Render one `JInstr w` frame-resident at the given width config: reload
    operands into working registers, compute, store the destination cell.
    `wax` holds the dst value, `wcx` the src value. `loadMem`/`storeMem` go
    through the `inp`/`out` pointer registers (`%rsi`/`%rdi`). Only the ARX +
    memory ops the compression body actually emits are handled; the rest are a
    defensive sentinel that the `_total` theorem proves never fires. -/
def renderJInstrFR {w : Nat} (c : PrinterCfg) : JInstr w → List String
  | .mov d s =>
      let (so, sl) := loadOperand c c.wax s
      sl ++ ["\tmov" ++ c.suf ++ " " ++ so ++ ", " ++ cell c d]
  | .add d s =>
      let (so, sl) := loadOperand c c.wcx s
      ["\tmov" ++ c.suf ++ " " ++ cell c d ++ ", " ++ c.wax] ++ sl ++
        ["\tadd" ++ c.suf ++ " " ++ so ++ ", " ++ c.wax, "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .xor_ d s =>
      let (so, sl) := loadOperand c c.wcx s
      ["\tmov" ++ c.suf ++ " " ++ cell c d ++ ", " ++ c.wax] ++ sl ++
        ["\txor" ++ c.suf ++ " " ++ so ++ ", " ++ c.wax, "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .or_ d s =>
      let (so, sl) := loadOperand c c.wcx s
      ["\tmov" ++ c.suf ++ " " ++ cell c d ++ ", " ++ c.wax] ++ sl ++
        ["\tor" ++ c.suf ++ " " ++ so ++ ", " ++ c.wax, "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .and_ d s =>
      let (so, sl) := loadOperand c c.wcx s
      ["\tmov" ++ c.suf ++ " " ++ cell c d ++ ", " ++ c.wax] ++ sl ++
        ["\tand" ++ c.suf ++ " " ++ so ++ ", " ++ c.wax, "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .shl d (.imm n) =>
      ["\tmov" ++ c.suf ++ " " ++ cell c d ++ ", " ++ c.wax, "\tshl" ++ c.suf ++ " $" ++ toString n ++ ", " ++ c.wax,
       "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .shr d (.imm n) =>
      ["\tmov" ++ c.suf ++ " " ++ cell c d ++ ", " ++ c.wax, "\tshr" ++ c.suf ++ " $" ++ toString n ++ ", " ++ c.wax,
       "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .loadMem d _ off =>
      ["\tmov" ++ c.suf ++ " " ++ toString off ++ "(%rsi), " ++ c.wax, "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .storeMem _ off (.reg s) =>
      ["\tmov" ++ c.suf ++ " " ++ cell c s ++ ", " ++ c.wax, "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ toString off ++ "(%rdi)"]
  | _ => ["\t# unsupported in BLAKE2 frame-resident printer"]

/-- The rendered body lines for a compression block at the given width config. -/
def bodyLines {w : Nat} (c : PrinterCfg) (block : List (JInstr w)) : List String :=
  block.flatMap (renderJInstrFR c)

/-- The rendered BLAKE2s body. -/
def blake2sBodyLines : List String := bodyLines cfg32 blake2sCompressBlock

/-- The rendered BLAKE2b body. -/
def blake2bBodyLines : List String := bodyLines cfg64 blake2bCompressBlock

/-- **No `unsupported` sentinel in the BLAKE2s body** — every emitted `JInstr`
    is one of the ARX/memory ops the frame-resident printer handles. -/
theorem blake2sBodyLines_total :
    (blake2sBodyLines.any (fun l => (l.splitOn "unsupported").length > 1)) = false := by
  native_decide

/-- **No `unsupported` sentinel in the BLAKE2b body.** -/
theorem blake2bBodyLines_total :
    (blake2bBodyLines.any (fun l => (l.splitOn "unsupported").length > 1)) = false := by
  native_decide

/-- The BLAKE2s body carries the 32-bit ARX alphabet and pointer-frame I/O. -/
theorem blake2sBodyLines_shape :
    (blake2sBodyLines.any (fun l => (l.splitOn "addl").length > 1)) = true
      ∧ (blake2sBodyLines.any (fun l => (l.splitOn "xorl").length > 1)) = true
      ∧ (blake2sBodyLines.any (fun l => (l.splitOn "shrl").length > 1)) = true
      ∧ (blake2sBodyLines.any (fun l => (l.splitOn "shll").length > 1)) = true
      ∧ (blake2sBodyLines.any (fun l => (l.splitOn "orl").length > 1)) = true
      ∧ (blake2sBodyLines.any (fun l => (l.splitOn "(%rsi)").length > 1)) = true
      ∧ (blake2sBodyLines.any (fun l => (l.splitOn "(%rdi)").length > 1)) = true := by
  native_decide

/-- The BLAKE2b body carries the 64-bit ARX alphabet and pointer-frame I/O. -/
theorem blake2bBodyLines_shape :
    (blake2bBodyLines.any (fun l => (l.splitOn "addq").length > 1)) = true
      ∧ (blake2bBodyLines.any (fun l => (l.splitOn "xorq").length > 1)) = true
      ∧ (blake2bBodyLines.any (fun l => (l.splitOn "shrq").length > 1)) = true
      ∧ (blake2bBodyLines.any (fun l => (l.splitOn "shlq").length > 1)) = true
      ∧ (blake2bBodyLines.any (fun l => (l.splitOn "orq").length > 1)) = true
      ∧ (blake2bBodyLines.any (fun l => (l.splitOn "(%rsi)").length > 1)) = true
      ∧ (blake2bBodyLines.any (fun l => (l.splitOn "(%rdi)").length > 1)) = true := by
  native_decide

/-! ## 8. The System V leaf functions

`out` arrives in `%rdi`, `inp` in `%rsi` (System V AMD64). The body is leaf
(makes no call), so we adjust `%rsp` by the cell-frame size on entry and restore
on exit; no callee-saved registers are clobbered (only the working/argument
registers). The C harness ignores the return value.

ABI:  void blake2{s,b}_compress(uint{32,64}_t *out /%rdi/, const uint{32,64}_t *inp /%rsi/)
  inp[0..15]  : the 16 initialized work-vector words v[0..15]
                (counter/finalization xors already folded into v[12..15])
  inp[16..31] : the 16 message words m[0..15]
  inp[32..39] : a read-only copy of the saved chaining words h[0..7]
  out[0..7]   : the 8 new chaining words. -/

/-- Assemble a single labelled System V leaf: frame setup, the frame-resident
    body, frame teardown, `ret`, non-executable-stack note. -/
def renderLeaf (name : String) (c : PrinterCfg) (lines : List String) : String :=
  let header :=
    [ "\t.text", "\t.globl " ++ name, "\t.type " ++ name ++ ", @function", name ++ ":" ]
  let prologue := [ "\tsubq $" ++ toString (frameBytes c) ++ ", %rsp" ]
  let epilogue := [ "\taddq $" ++ toString (frameBytes c) ++ ", %rsp", "\tret" ]
  let footer := [ "\t.section .note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (header ++ prologue ++ lines ++ epilogue ++ footer) ++ "\n"

/-- The emitted BLAKE2s compression `.s` text. -/
def blake2sCompressAsm : String := renderLeaf "blake2s_compress" cfg32 blake2sBodyLines

/-- The emitted BLAKE2b compression `.s` text. -/
def blake2bCompressAsm : String := renderLeaf "blake2b_compress" cfg64 blake2bBodyLines

/-- The BLAKE2s leaf has the ABI label and the frame setup/teardown. -/
theorem blake2sCompressAsm_shape :
    (blake2sCompressAsm.splitOn "blake2s_compress:").length > 1
      ∧ (blake2sCompressAsm.splitOn ".globl blake2s_compress").length > 1
      ∧ (blake2sCompressAsm.splitOn "subq $").length > 1
      ∧ (blake2sCompressAsm.splitOn "ret").length > 1 := by
  native_decide

/-- The BLAKE2b leaf has the ABI label and the frame setup/teardown. -/
theorem blake2bCompressAsm_shape :
    (blake2bCompressAsm.splitOn "blake2b_compress:").length > 1
      ∧ (blake2bCompressAsm.splitOn ".globl blake2b_compress").length > 1
      ∧ (blake2bCompressAsm.splitOn "subq $").length > 1
      ∧ (blake2bCompressAsm.splitOn "ret").length > 1 := by
  native_decide

/-- Emit driver: write the owned-backend BLAKE2s + BLAKE2b compression `.s` for
    the bench. The orchestrator runs this (`lake env lean --run`) to produce the
    files the Makefile assembles + KATs against the official RFC 7693 vectors. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/blake2_compare/gen"
  IO.FS.writeFile "bench/blake2_compare/gen/blake2s_compress.s" blake2sCompressAsm
  IO.FS.writeFile "bench/blake2_compare/gen/blake2b_compress.s" blake2bCompressAsm
  IO.println "wrote bench/blake2_compare/gen/blake2{s,b}_compress.s (owned x86 scalar backend)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Blake2Emit
