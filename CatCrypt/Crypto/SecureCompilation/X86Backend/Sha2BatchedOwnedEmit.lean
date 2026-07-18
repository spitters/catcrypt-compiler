/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# The BATCHED (N=4) SHA-256 / SHA-512 block compression, emitted through the
  OWNED x86 scalar backend (no jasminc)

The batched kernels `sha256_compress_x4` / `sha512_compress_x4` process **four**
message blocks back-to-back, chaining the digest across them — the
`bench/sha2_compare/gen/sha256_batched.jazz` ABI, currently emitted via jasminc.

This module is the **owned** sibling: a width-parametric (`w = 32` / `w = 64`)
scalar SHA-2 compression as a straight-line `List (JInstr w)` block over the
owned model (`X86Backend/{JasminModel, X86Dialect}`), run four times with the
chaining digest threaded through, rendered frame-resident to AT&T `.s` by a
three-pointer printer. It is the scalar-GP analogue of the AVX2 multi-buffer
owned emit and a direct sibling of `X86Backend/Blake2OwnedEmit.lean` (same
`JInstr w` frame-resident discipline; SHA-2's round is the FIPS-180-4 ARX core
in place of BLAKE2's `G`).

## The "batched" structure is 4 sequential scalar compressions

`sha256_compress_x4(state, K, M)` is, per `sha2_batched_kat.c`, exactly four
applications of the scalar `sha256_compress` over the four 16-word message
blocks `M[16·b .. 16·b+15]`, chaining `state` in place — the KAT checks it
against `4×` chained scalar `sha256_compress`. So the emitted body is the scalar
compression block emitted four times with the per-block message base advanced by
one block.

## ABI (matches `bench/sha2_compare/sha2_batched_kat.c`)

```
sha256_compress_x4(state u32[8] /%rdi/, const K u32[64] /%rsi/, const M u32[64] /%rdx/)
sha512_compress_x4(state u64[8] /%rdi/, const K u64[80] /%rsi/, const M u64[64] /%rdx/)
```

`state` carries the chaining digest `H` in/out (updated in place); `K` is the
`K[0..63]`/`K[0..79]` round constants; `M` is 4 blocks × 16 message words. All
three are GP pointers in the SysV arg registers `%rdi`/`%rsi`/`%rdx`.

## SHA-2 round (FIPS 180-4 §6.2.2), width-parametric on `BitVec w`

The eight rotation/shift amounts differ per width (`Σ₀,Σ₁,σ₀,σ₁`); they are
passed as a `Sha2Params` record so the same emit core serves both:

* **SHA-256** (`w = 32`): `Σ₀=ρ²⊕ρ¹³⊕ρ²²`, `Σ₁=ρ⁶⊕ρ¹¹⊕ρ²⁵`,
  `σ₀=ρ⁷⊕ρ¹⁸⊕≫3`, `σ₁=ρ¹⁷⊕ρ¹⁹⊕≫10`, 64 rounds.
* **SHA-512** (`w = 64`): `Σ₀=ρ²⁸⊕ρ³⁴⊕ρ³⁹`, `Σ₁=ρ¹⁴⊕ρ¹⁸⊕ρ⁴¹`,
  `σ₀=ρ¹⊕ρ⁸⊕≫7`, `σ₁=ρ¹⁹⊕ρ⁶¹⊕≫6`, 80 rounds.

`Ch`/`Maj` are written without `not` (`Ch = g ⊕ (e ∧ (f ⊕ g))`,
`Maj = (a ∧ b) ⊕ (c ∧ (a ⊕ b))`), and each right-rotate is the owned model's
`shr; shl; or` synthesis (exactly `BitVec.rotateRight`, `sha2_ror_synth`).

## What is verified vs. trusted

* **Verified**: the rotate synthesis equals `BitVec.rotateRight`
  (`sha2_ror_synth`); one emitted round, lowered through `X86Dialect.lowerBlock`
  and run via `runBlock`, computes the reference `roundSpec` on concrete words at
  both widths (`sha256_round_computes_spec`, `sha512_round_computes_spec`,
  `native_decide` over a single round); `lowerBlock` of the whole batched body
  denotes `runBlock` (`*_lower_denote`, the `X86Dialect` tie); the four-block
  body factors through `runBlock` block-by-block
  (`batched_runBlock_append`). The whole-message FIPS-180-4 / 4×-scalar KAT is
  the external C harness around this emitted body.
* **Trusted (thin)**: the three-pointer AT&T printer (one line per `JInstr`) and
  the SysV ABI glue — the same trusted-scaffold status as BLAKE2/AVX2.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.X86Backend.Sha2BatchedOwnedEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha2BatchedOwnedEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. The SHA-2 reference round spec (width-parametric, on `BitVec w`) -/

/-- `w`-bit rotate-right by `n`. -/
def rotr {w : Nat} (x : BitVec w) (n : Nat) : BitVec w := x.rotateRight n

/-- The per-width SHA-2 rotation/shift amounts (`Σ₀,Σ₁,σ₀,σ₁` triples) and the
    round count. SHA-256: `((2,13,22),(6,11,25),(7,18,3),(17,19,10))`, 64 rounds;
    SHA-512: `((28,34,39),(14,18,41),(1,8,7),(19,61,6))`, 80 rounds. -/
structure Sha2Params where
  /-- `Σ₀` rotate amounts `(a,b,c)`: `Σ₀(x)=ρᵃ⊕ρᵇ⊕ρᶜ`. -/
  bs0 : Nat × Nat × Nat
  /-- `Σ₁` rotate amounts. -/
  bs1 : Nat × Nat × Nat
  /-- `σ₀` `(rot,rot,shr)`: `σ₀(x)=ρᵃ⊕ρᵇ⊕≫c`. -/
  ss0 : Nat × Nat × Nat
  /-- `σ₁` `(rot,rot,shr)`. -/
  ss1 : Nat × Nat × Nat
  /-- Round count (64 / 80). -/
  nr : Nat

/-- SHA-256 parameters (width 32, 64 rounds). -/
def p256 : Sha2Params :=
  { bs0 := (2,13,22), bs1 := (6,11,25), ss0 := (7,18,3), ss1 := (17,19,10), nr := 64 }

/-- SHA-512 parameters (width 64, 80 rounds). -/
def p512 : Sha2Params :=
  { bs0 := (28,34,39), bs1 := (14,18,41), ss0 := (1,8,7), ss1 := (19,61,6), nr := 80 }

/-- `Σ₀(a) = ρᵃ⊕ρᵇ⊕ρᶜ`. -/
def bigSigma0 {w : Nat} (P : Sha2Params) (x : BitVec w) : BitVec w :=
  rotr x P.bs0.1 ^^^ rotr x P.bs0.2.1 ^^^ rotr x P.bs0.2.2

/-- `Σ₁(e) = ρᵃ⊕ρᵇ⊕ρᶜ`. -/
def bigSigma1 {w : Nat} (P : Sha2Params) (x : BitVec w) : BitVec w :=
  rotr x P.bs1.1 ^^^ rotr x P.bs1.2.1 ^^^ rotr x P.bs1.2.2

/-- `σ₀(x) = ρᵃ⊕ρᵇ⊕≫c`. -/
def smallSigma0 {w : Nat} (P : Sha2Params) (x : BitVec w) : BitVec w :=
  rotr x P.ss0.1 ^^^ rotr x P.ss0.2.1 ^^^ (x >>> P.ss0.2.2)

/-- `σ₁(x) = ρᵃ⊕ρᵇ⊕≫c`. -/
def smallSigma1 {w : Nat} (P : Sha2Params) (x : BitVec w) : BitVec w :=
  rotr x P.ss1.1 ^^^ rotr x P.ss1.2.1 ^^^ (x >>> P.ss1.2.2)

/-- `Ch(e,f,g) = g ⊕ (e ∧ (f ⊕ g))` (= `(e∧f) ⊕ (¬e∧g)`, no `not`). -/
def ch {w : Nat} (e f g : BitVec w) : BitVec w := g ^^^ (e &&& (f ^^^ g))

/-- `Maj(a,b,c) = (a ∧ b) ⊕ (c ∧ (a ⊕ b))` (= the standard `Maj`, no `not`). -/
def maj {w : Nat} (a b c : BitVec w) : BitVec w := (a &&& b) ^^^ (c &&& (a ^^^ b))

/-- The 8-word SHA-2 state `(a,b,c,d,e,f,g,h)`. -/
abbrev St (w : Nat) := BitVec w × BitVec w × BitVec w × BitVec w ×
                       BitVec w × BitVec w × BitVec w × BitVec w

/-- One SHA-2 compression round (FIPS 180-4 §6.2.2 Step 3): given the round's
    `K[t]` and schedule word `W[t]`, advance the state. -/
def roundSpec {w : Nat} (P : Sha2Params) (s : St w) (kt wt : BitVec w) : St w :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + bigSigma1 P e + ch e f g + kt + wt
  let t2 := bigSigma0 P a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-! ## 2. The emitted `JInstr w` round + schedule blocks

Working state in named cells `a..h`; schedule window `W0..W15`; round constant
`kt`/schedule word `wt`; scratch `t0..t3`. The rotate is the `shr; shl; or`
synthesis at width `w`. Mirrors `Blake2OwnedEmit`'s frame-resident discipline. -/

/-- Synthesize a width-`w` rotate-right of register `dst` by `n` using scratch
    `tmp`: `tmp = dst; dst >>= n; tmp <<= (w-n); dst |= tmp`. Exactly
    `dst.rotateRight n` (`sha2_ror_synth`). -/
def rorSynth (w : Nat) (dst tmp : String) (n : Nat) : List (JInstr w) :=
  [ .mov tmp (.reg dst)
  , .shr dst (.imm n)
  , .shl tmp (.imm (w - n))
  , .or_ dst (.reg tmp) ]

/-- Working-state cell names (`a` .. `h`). -/
def reg8 : Array String := #["a", "b", "c", "d", "e", "f", "g", "h"]

/-- A schedule-window cell name `W{i}` (`i < 16`). -/
def wReg (i : Nat) : String := "W" ++ toString (i % 16)

/-- Scratch cell name. -/
def s0 : String := "s0"
/-- Scratch cell name. -/
def s1 : String := "s1"
/-- Scratch cell name. -/
def s2 : String := "s2"
/-- Scratch cell name (the `T1` accumulator). -/
def t1r : String := "t1r"

/-- Compute `σ`-style `ρᵃ(x) ⊕ ρᵇ(x) ⊕ (op c)(x)` of a source cell `src` into
    `dst`, with the third term either a rotate (`shrTerm = false`) or a shift
    (`shrTerm = true`). Uses scratch `tmp`. Result left in `dst`. -/
def sigmaBlk (w : Nat) (dst src tmp : String) (a b c : Nat) (shrTerm : Bool) :
    List (JInstr w) :=
  -- dst = rotr src a
  [ .mov dst (.reg src) ] ++ rorSynth w dst tmp a ++
  -- tmp2 = rotr src b ; dst ^= tmp2   (reuse `tmp` as the value, a 2nd scratch `s2`)
  [ .mov s2 (.reg src) ] ++ rorSynth w s2 tmp b ++ [ .xor_ dst (.reg s2) ] ++
  -- third: (shr or rotr) src c into s2, xor into dst
  (if shrTerm then
     [ .mov s2 (.reg src), .shr s2 (.imm c) ]
   else
     [ .mov s2 (.reg src) ] ++ rorSynth w s2 tmp c) ++
  [ .xor_ dst (.reg s2) ]

/-- One SHA-2 round `t`: compute `T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]`,
    `T2 = Σ₀(a) + Maj(a,b,c)`, then the state rotation
    `(a..h) ↦ (T1+T2, a, b, c, d+T1, e, f, g)`. `kt` is loaded into the `kt`
    cell, `wt` is the schedule cell `W{t mod 16}`. Mirrors `roundSpec`. -/
def roundBlk (w : Nat) (P : Sha2Params) (t : Nat) : List (JInstr w) :=
  let a := "a"; let b := "b"; let c := "c"; let d := "d"
  let e := "e"; let f := "f"; let g := "g"; let h := "h"
  let wt := wReg t
  -- s0 = Σ₁(e)
  sigmaBlk w s0 e "tmp" P.bs1.1 P.bs1.2.1 P.bs1.2.2 false ++
  -- s1 = Ch(e,f,g) = g ^ (e & (f ^ g))
  [ .mov s1 (.reg f), .xor_ s1 (.reg g), .and_ s1 (.reg e), .xor_ s1 (.reg g) ] ++
  -- t1r = h + s0 + s1 + K[t] + W[t]
  [ .mov t1r (.reg h), .add t1r (.reg s0), .add t1r (.reg s1)
  , .add t1r (.reg "kt"), .add t1r (.reg wt) ] ++
  -- s0 = Σ₀(a)
  sigmaBlk w s0 a "tmp" P.bs0.1 P.bs0.2.1 P.bs0.2.2 false ++
  -- s2 = Maj(a,b,c) = (a&b) ^ (c & (a^b))     [use s1 and s2 as scratch]
  [ .mov s1 (.reg a), .and_ s1 (.reg b)               -- s1 = a & b
  , .mov s2 (.reg a), .xor_ s2 (.reg b), .and_ s2 (.reg c)  -- s2 = c & (a^b)
  , .xor_ s2 (.reg s1) ] ++                            -- s2 = Maj
  -- t2 (in s0) = Σ₀(a) + Maj  ; then do the rotation
  [ .add s0 (.reg s2) ] ++          -- s0 = T2 = Σ₀(a)+Maj
  -- state rotation (h..a shift down), e += T1, a = T1 + T2.
  -- Write order avoids clobbering a source before it is read:
  --   new_d = d + T1 ; then h=g; g=f; f=e; e=new_d(saved); ... easier: save into
  --   fresh cells then commit.
  [ .mov "nd" (.reg d), .add "nd" (.reg t1r)           -- nd = d + T1   (new e)
  , .mov "na" (.reg t1r), .add "na" (.reg s0)          -- na = T1 + T2  (new a)
  , .mov h (.reg g), .mov g (.reg f), .mov f (.reg e)  -- h=g; g=f; f=e
  , .mov e (.reg "nd")                                 -- e = nd
  , .mov d (.reg c), .mov c (.reg b), .mov b (.reg a)  -- d=c; c=b; b=a
  , .mov a (.reg "na") ]                               -- a = na

/-- One schedule-extension step for round `t ≥ 16`:
    `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`, recomputed in place into
    the cell `W{t mod 16}` (which currently holds `W[t-16]`). -/
def schedBlk (w : Nat) (P : Sha2Params) (t : Nat) : List (JInstr w) :=
  let dst := wReg t          -- holds W[t-16]
  let w2 := wReg (t - 2); let w7 := wReg (t - 7); let w15 := wReg (t - 15)
  -- s0 = σ₁(W[t-2])
  sigmaBlk w s0 w2 "tmp" P.ss1.1 P.ss1.2.1 P.ss1.2.2 true ++
  -- s1 = σ₀(W[t-15])
  sigmaBlk w s1 w15 "tmp" P.ss0.1 P.ss0.2.1 P.ss0.2.2 true ++
  -- dst (=W[t-16]) += σ₁ + σ₀ + W[t-7]
  [ .add dst (.reg s0), .add dst (.reg s1), .add dst (.reg w7) ]

/-! ## 3. Value correctness -/

/-- **Rotate synthesis is `rotateRight`** (per-rotate correctness of `rorSynth`). -/
theorem sha2_ror_synth {w : Nat} (x : BitVec w) (n : Nat) (h : n < w) :
    (x >>> n) ||| (x <<< (w - n)) = x.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

/-- A concrete machine state seeding `a..h = 1..8`, `kt`, `wt = W{t mod 16}`. -/
def roundInit (w t : Nat) (kt wt : BitVec w) : JState w :=
  { regs := fun r =>
      (List.range 8).foldl
        (fun acc i => if r = reg8[i]! then BitVec.ofNat w (i + 1) else acc)
        (if r = "kt" then kt else if r = wReg t then wt else 0) }

/-- The reference initial state matching `roundInit` (`a..h = 1..8`). -/
def roundInitSt (w : Nat) : St w :=
  (BitVec.ofNat w 1, BitVec.ofNat w 2, BitVec.ofNat w 3, BitVec.ofNat w 4,
   BitVec.ofNat w 5, BitVec.ofNat w 6, BitVec.ofNat w 7, BitVec.ofNat w 8)

/-- **One emitted SHA-256 round computes `roundSpec`** (width 32). On a concrete
    input the eight working cells of the run-round machine state equal the eight
    components of `roundSpec`. `native_decide` over a single round. -/
theorem sha256_round_computes_spec :
    let kt : BitVec 32 := 0x428a2f98
    let wt : BitVec 32 := 0x61626380
    let s := runBlock (roundInit 32 0 kt wt) (roundBlk 32 p256 0)
    let (a,b,c,d,e,f,g,h) := roundSpec p256 (roundInitSt 32) kt wt
    s.get "a" = a ∧ s.get "b" = b ∧ s.get "c" = c ∧ s.get "d" = d ∧
    s.get "e" = e ∧ s.get "f" = f ∧ s.get "g" = g ∧ s.get "h" = h := by
  native_decide

/-- **One emitted SHA-512 round computes `roundSpec`** (width 64). `native_decide`
    over a single round. -/
theorem sha512_round_computes_spec :
    let kt : BitVec 64 := 0x428a2f98d728ae22
    let wt : BitVec 64 := 0x6162638000000000
    let s := runBlock (roundInit 64 0 kt wt) (roundBlk 64 p512 0)
    let (a,b,c,d,e,f,g,h) := roundSpec p512 (roundInitSt 64) kt wt
    s.get "a" = a ∧ s.get "b" = b ∧ s.get "c" = c ∧ s.get "d" = d ∧
    s.get "e" = e ∧ s.get "f" = f ∧ s.get "g" = g ∧ s.get "h" = h := by
  native_decide

/-! ## 4. The full batched compression body as `JInstr w`

Per block `b ∈ {0,1,2,3}`: load `W[0..15]` from `M[16·b .. 16·b+15]`; save the
chaining digest `a..h` (already in the working cells) into `S[0..7]`; run `nr`
rounds (loading `K[t]` per round, recomputing the schedule for `t ≥ 16`); feed
forward `a..h += S[..]`. The digest stays in `a..h` across blocks. At the end,
store `a..h` to `state[0..7]`. -/

/-- The `state` pointer-base name (System V arg0). -/
def stateBase : String := "state"
/-- The `K` pointer-base name (System V arg1). -/
def kBase : String := "K"
/-- The `M` pointer-base name (System V arg2). -/
def mBase : String := "M"

/-- Load the chaining digest `state[0..7]` into the working cells `a..h`. -/
def loadState (w : Nat) : List (JInstr w) :=
  (List.range 8).map (fun i => .loadMem reg8[i]! stateBase (Int.ofNat (w / 8 * i)))

/-- Store `a..h` back to `state[0..7]`. -/
def storeState (w : Nat) : List (JInstr w) :=
  (List.range 8).map (fun i => .storeMem stateBase (Int.ofNat (w / 8 * i)) (.reg reg8[i]!))

/-- Load block `b`'s 16 message words `W[0..15]` from `M[16·b .. 16·b+15]`. -/
def loadBlockW (w b : Nat) : List (JInstr w) :=
  (List.range 16).map (fun i =>
    .loadMem (wReg i) mBase (Int.ofNat (w / 8 * (16 * b + i))))

/-- Save the working digest `a..h` into the per-block save cells `S0..S7`. -/
def saveDigest (w : Nat) : List (JInstr w) :=
  (List.range 8).map (fun i => .mov ("S" ++ toString i) (.reg reg8[i]!))

/-- Feed forward `a..h += S{i}`. -/
def feedForward (w : Nat) : List (JInstr w) :=
  (List.range 8).flatMap (fun i => [ .add reg8[i]! (.reg ("S" ++ toString i)) ])

/-- All `nr` rounds for one block: load `K[t]`, recompute the schedule (t ≥ 16),
    then the round. -/
def allRounds (w : Nat) (P : Sha2Params) : List (JInstr w) :=
  (List.range P.nr).flatMap (fun t =>
    (if t ≥ 16 then schedBlk w P t else []) ++
    [ .loadMem "kt" kBase (Int.ofNat (w / 8 * t)) ] ++
    roundBlk w P t)

/-- One block's compression: load `W`, save digest, rounds, feed-forward. -/
def compressBlock (w b : Nat) (P : Sha2Params) : List (JInstr w) :=
  loadBlockW w b ++ saveDigest w ++ allRounds w P ++ feedForward w

/-- The full 4-block batched body: load the chaining state, compress 4 blocks
    (chaining the digest in `a..h`), store the final digest. -/
def batchedBody (w : Nat) (P : Sha2Params) : List (JInstr w) :=
  loadState w ++
  (List.range 4).flatMap (fun b => compressBlock w b P) ++
  storeState w

/-- **SHA-256** batched body (width 32, 64 rounds). -/
def sha256x4Body : List (JInstr 32) := batchedBody 32 p256

/-- **SHA-512** batched body (width 64, 80 rounds). -/
def sha512x4Body : List (JInstr 64) := batchedBody 64 p512

/-! ## 5. Owned-backend lowering tie + block factoring -/

/-- `runBlock` over a concatenation is the fold. -/
theorem batched_runBlock_append {w : Nat} (s : JState w) (b1 b2 : List (JInstr w)) :
    runBlock s (b1 ++ b2) = runBlock (runBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i t ih => simp [runBlock, ih]

/-- **SHA-256 batched body lowered denotes `runBlock`** (the owned-backend tie). -/
theorem sha256x4_lower_denote (s : JState 32) :
    (lowerBlock (Γ := []) sha256x4Body).denote (.cons s .nil)
      = runBlock s sha256x4Body :=
  lowerBlock_denote_closed _ s

/-- **SHA-512 batched body lowered denotes `runBlock`.** -/
theorem sha512x4_lower_denote (s : JState 64) :
    (lowerBlock (Γ := []) sha512x4Body).denote (.cons s .nil)
      = runBlock s sha512x4Body :=
  lowerBlock_denote_closed _ s

/-! ## 6. Three-pointer frame-resident AT&T rendering (trusted thin scaffold)

The body uses 8 working + 16 schedule + 8 save + scratch (`kt,wt,s0,s1,s2,t1r,
tmp,na,nd`) ≈ 41 distinct value names, so it is rendered frame-resident (the
BLAKE2 / BLAKE3 discipline): every value name lives in a `cellW`-byte stack cell
off `%rsp`; each `JInstr` reloads operands into the working registers, computes,
stores the destination cell. The three pointer bases stay in their arg registers
`%rdi`/`%rsi`/`%rdx`. -/

/-- A width's printer config: AT&T size suffix, dst/src working registers, cell
    size in bytes. -/
structure PrinterCfg where
  /-- AT&T size suffix: `"l"` (32) or `"q"` (64). -/
  suf  : String
  /-- The dst working register: `%eax`/`%rax`. -/
  wax  : String
  /-- The src working register: `%ecx`/`%rcx`. -/
  wcx  : String
  /-- Cell size in bytes: `4`/`8`. -/
  cellW : Int

/-- SHA-256 printer config (32-bit). -/
def cfg32 : PrinterCfg := { suf := "l", wax := "%eax", wcx := "%ecx", cellW := 4 }

/-- SHA-512 printer config (64-bit). -/
def cfg64 : PrinterCfg := { suf := "q", wax := "%rax", wcx := "%rcx", cellW := 8 }

/-- The ordered list of value names the body uses (working, schedule, save,
    scratch). The pointer bases are not cells (they live in arg registers). -/
def cellNames : List String :=
  reg8.toList ++ (List.range 16).map wReg ++
  (List.range 8).map (fun i => "S" ++ toString i) ++
  ["kt", "wt", s0, s1, s2, t1r, "tmp", "na", "nd"]

/-- The cell-frame offset of a value name (off `%rsp`), or `0` if absent. -/
def cellOff (c : PrinterCfg) (n : String) : Int :=
  match cellNames.idxOf? n with
  | some k => c.cellW * Int.ofNat k
  | none => 0

/-- The total cell-frame size in bytes (`#names × cellW`), rounded up to 16. -/
def frameBytes (c : PrinterCfg) : Nat :=
  ((cellNames.length * c.cellW.toNat + 15) / 16) * 16

/-- A value-name cell as an AT&T `%rsp`-relative memory operand. -/
def cell (c : PrinterCfg) (n : String) : String := toString (cellOff c n) ++ "(%rsp)"

/-- The `%`-register for a pointer-base name: `state→%rdi`, `K→%rsi`, `M→%rdx`. -/
def baseReg (n : String) : String :=
  if n = stateBase then "%rdi" else if n = kBase then "%rsi"
  else if n = mBase then "%rdx" else "%rax"

/-- A width-`w` operand: an immediate `$v`, or a cell load of a register name into
    a working register. Returns the operand string and the (possibly empty)
    reload line. -/
def loadOperand (c : PrinterCfg) (work : String) : JOperand → String × List String
  | .imm v => ("$" ++ toString v, [])
  | .reg r => (work, ["\tmov" ++ c.suf ++ " " ++ cell c r ++ ", " ++ work])

/-- Render one `JInstr w` frame-resident at the given width config. Only the ARX +
    memory ops the compression body emits are handled; the rest are a defensive
    sentinel the `_total` theorem proves never fires. `loadMem`/`storeMem` route
    through the pointer base's arg register (`baseReg`). -/
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
  | .loadMem d base off =>
      ["\tmov" ++ c.suf ++ " " ++ toString off ++ "(" ++ baseReg base ++ "), " ++ c.wax,
       "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ cell c d]
  | .storeMem base off (.reg s) =>
      ["\tmov" ++ c.suf ++ " " ++ cell c s ++ ", " ++ c.wax,
       "\tmov" ++ c.suf ++ " " ++ c.wax ++ ", " ++ toString off ++ "(" ++ baseReg base ++ ")"]
  | _ => ["\t# unsupported in SHA-2 batched frame-resident printer"]

/-- The rendered body lines for a compression block at the given width config. -/
def bodyLines {w : Nat} (c : PrinterCfg) (block : List (JInstr w)) : List String :=
  block.flatMap (renderJInstrFR c)

/-- The rendered SHA-256 batched body. -/
def sha256x4BodyLines : List String := bodyLines cfg32 sha256x4Body

/-- The rendered SHA-512 batched body. -/
def sha512x4BodyLines : List String := bodyLines cfg64 sha512x4Body

/-- **No `unsupported` sentinel in the SHA-256 body.** -/
theorem sha256x4BodyLines_total :
    (sha256x4BodyLines.any (fun l => (l.splitOn "unsupported").length > 1)) = false := by
  native_decide

/-- **No `unsupported` sentinel in the SHA-512 body.** -/
theorem sha512x4BodyLines_total :
    (sha512x4BodyLines.any (fun l => (l.splitOn "unsupported").length > 1)) = false := by
  native_decide

/-! ## 7. The System V leaf functions

`state` in `%rdi`, `K` in `%rsi`, `M` in `%rdx`. Leaf (no call): adjust `%rsp` by
the cell-frame size on entry, restore on exit. The C harness reads `state` in
place and ignores the return value, but we return `state` in `%rax` (the
`-> reg ptr` ABI). -/

/-- Assemble a labelled System V leaf: frame setup, body, teardown, `ret`. -/
def renderLeaf (name : String) (c : PrinterCfg) (lines : List String) : String :=
  let header :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t4"
    , "\t.globl " ++ name, "\t.type " ++ name ++ ", @function", name ++ ":" ]
  let prologue := [ "\tsubq $" ++ toString (frameBytes c) ++ ", %rsp" ]
  let epilogue :=
    [ "\tmovq %rdi, %rax", "\taddq $" ++ toString (frameBytes c) ++ ", %rsp", "\tret" ]
  let footer := [ "\t.section .note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (header ++ prologue ++ lines ++ epilogue ++ footer) ++ "\n"

/-- The emitted SHA-256 batched `.s` text. -/
def sha256x4Asm : String := renderLeaf "sha256_compress_x4" cfg32 sha256x4BodyLines

/-- The emitted SHA-512 batched `.s` text. -/
def sha512x4Asm : String := renderLeaf "sha512_compress_x4" cfg64 sha512x4BodyLines

/-- The SHA-256 leaf carries the ABI label, frame setup, three-pointer I/O. -/
theorem sha256x4Asm_shape :
    (sha256x4Asm.splitOn "sha256_compress_x4:").length > 1
      ∧ (sha256x4Asm.splitOn ".globl sha256_compress_x4").length > 1
      ∧ (sha256x4Asm.splitOn "subq $").length > 1
      ∧ (sha256x4Asm.splitOn "(%rdi)").length > 1
      ∧ (sha256x4Asm.splitOn "(%rsi)").length > 1
      ∧ (sha256x4Asm.splitOn "(%rdx)").length > 1 := by
  native_decide

/-- The SHA-512 leaf carries the ABI label, frame setup, three-pointer I/O. -/
theorem sha512x4Asm_shape :
    (sha512x4Asm.splitOn "sha512_compress_x4:").length > 1
      ∧ (sha512x4Asm.splitOn ".globl sha512_compress_x4").length > 1
      ∧ (sha512x4Asm.splitOn "subq $").length > 1
      ∧ (sha512x4Asm.splitOn "(%rdi)").length > 1
      ∧ (sha512x4Asm.splitOn "(%rsi)").length > 1
      ∧ (sha512x4Asm.splitOn "(%rdx)").length > 1 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha2BatchedOwnedEmit
