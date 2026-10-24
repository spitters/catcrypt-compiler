/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2MultiBufAvx2Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2MultiBufAvx2Emit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-!
# Whole-function 8-way SHA-512 block compression over AVX-512 ZMM lanes

**TEST/BENCH-ONLY — STRING-TEMPLATED, not verified-compiler output.** The
emitted `bench/sha2_compare/gen_com/sha512_compress_x8_zmm.s` is a body rendered
from `WInst` blocks by the module-local printer `renderZInst` wrapped in
hand-written header / prologue / epilogue / `.rodata` frame lines (string lists
joined with `String.intercalate`), with no single verified-printer descent for
the whole file. The `#guard` checks are structural assertions; the per-lane
realization theorems `roundBlk_realizes_zmm`/`schedBlk_realizes_zmm` scope the
`runZBlock` round/schedule blocks, not the emitted frame. It is a bench/interop
reference. The verified emit path is the FRONT-SOURCED descent.

`sha512_compress_x8` runs eight independent SHA-512 streams packed across the
eight `u64` lanes of a 512-bit ZMM register: one FIPS-180-4 §6.4 single-block
compression per lane, all eight lanes advancing together through the 80 rounds
and the message schedule.

SoA ABI, two pointers (the round constants live in the emitted `.rodata`):

```
void sha512_compress_x8(uint64_t *state, const uint64_t *msg);
  state[8*i + l] = chaining word i of lane l    (8 words × 8 lanes)
  msg[8*w + l]   = message word w of lane l     (16 words × 8 lanes)
```

`state` arrives in `%rdi` and `msg` in `%rsi`; word `i` therefore sits at byte
offset `64*i` from its pointer, one ZMM load. The function computes
`state[i] += round-output[i]`, the FIPS feed-forward, in place.

## Structure

The 4-lane owned emit `VIR.Sha2MultiBufAvx2Emit.Sha512X4w` carries the
lane-count-independent part of this kernel:

* the FIPS-180-4 §4.1.3/§6.4 word functions on `BitVec 64`
  (`rotrSynth`, `chL`, `majL`, `bigSigma0L`, `bigSigma1L`, `smallSigma0L`,
  `smallSigma1L`, `shaRound`, `schedNext`) and the round-constant / initial-hash
  tables (`k512`, `h0`);
* the instruction type `WInst` (packed qword add / xor / and / or plus
  immediate-count qword shifts) and the round and schedule instruction blocks
  built from it (`rotBlk`, `bigSigma0Blk`, `bigSigma1Blk`, `roundBlk`,
  `schedBlk`) — plain `List WInst` over register names, with no lane count in
  their statement.

This module supplies the pieces that carry the lane count:

1. the 8-lane register machine (`Zmm`, `ZState`, `evalZInst`, `runZBlock`);
2. the per-lane realisation theorems at `Fin 8`
   (`roundBlk_realizes_zmm`, `schedBlk_realizes_zmm`);
3. the 8-lane corollary of `LaneMap.laneMap_eq_scalarMap`
   (`sha512_8way_lane_map`);
4. the EVEX AT&T renderer and the 64-byte slot layout, and the whole-function
   text `sha512x8ExportAsm`.

## EVEX forms

`vpaddq`, `vpsllq $imm` and `vpsrlq $imm` have ZMM encodings under the same
mnemonic. `vpxor`, `vpand` and `vpor` are VEX-only, so the ZMM renderer emits
the `q`-suffixed AVX-512 forms `vpxorq` / `vpandq` / `vporq`. Aligned ZMM moves
are `vmovdqa64` and unaligned ones `vmovdqu64`.

## Register and slot layout

The 4-lane ring allocator carries over unchanged: `%zmm0..7` hold the eight
working words `a..h` as a rotating ring (logical word `j` at round `t` lives in
ring position `(j + 8 - t % 8) % 8`, so a round writes `a'` where `h` was and
`e'` where `d` was, and after 80 rounds the ring is back at the identity);
`%zmm8`/`%zmm9` hold `K[t]`/`W[t]`; `%zmm10..15` are scratch. The 16-word
schedule window and the eight saved chaining words live in the 1536-byte stack
frame — `%rsp + 64*i` for window slot `i`, `%rsp + 1024 + 64*i` for saved word
`i` — with `%rsp` 64-byte aligned so every stack access is an aligned ZMM move.

## Value correctness

Per-lane correctness of the round and schedule blocks against FIPS-180-4 is
`roundBlk_realizes_zmm` / `schedBlk_realizes_zmm`. The all-lanes value check on
the assembled function is the external harness
`bench/sha2_compare/sha512_x8_kat.c`, which feeds eight distinct one-block
messages through the emitted symbol and compares each lane against a reference
SHA-512 single-block compression, with lane 0 against the canonical
`SHA-512("abc")` digest.

Emit: `lake env lean --run
  CatCrypt/Crypto/SecureCompilation/X86Backend/Sha512X8ZmmWideEmit.lean`
writes `bench/sha2_compare/gen_com/sha512_compress_x8_zmm.s`.

## Main definitions

* `Zmm`, `ZState`, `evalZInst`, `runZBlock`: the 8x u64 machine, over the reused
  `Sha512X4w.WInst` instruction type
* `sha512x8ExportAsm`, `emit`: the rendered function and its writer

## Main results

* `roundBlk_realizes_zmm`, `schedBlk_realizes_zmm`: each lane of the reused
  `roundBlk` and `schedBlk` computes the FIPS 180-4 §6.4.2 round and message
  schedule
* `sha512_8way_lane_map`: the eight-lane instance of
  `LaneMap.laneMap_eq_scalarMap`, the lane tie `bench/sha2_compare/Makefile` names
* `runZBlock_append`: running a concatenation runs the parts in order
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8ZmmWideEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2MultiBufAvx2Emit.Sha512X4w
  (WInst laneAdd laneXor laneAnd laneOr laneShl laneShr rotrSynth chL majL
   bigSigma0L bigSigma1L smallSigma0L smallSigma1L Work shaRound schedNext
   k512 rotBlk bigSigma0Blk bigSigma1Blk roundBlk schedBlk)

/-! ## 1. The 8-lane ZMM register machine

A 512-bit ZMM register viewed as eight independent `u64` lanes. The instruction
type is the 4-lane emit's `WInst` verbatim (packed qword add / xor / and / or and
immediate-count qword shifts); only the register-file width changes. -/

/-- A 512-bit ZMM register as 8 × `u64` lanes. -/
abbrev Zmm : Type := Fin 8 → BitVec 64

/-- The ZMM register file: a name → `Zmm`. -/
structure ZState where
  /-- The `zmm` register file, named by string. -/
  regs : String → Zmm

namespace ZState

/-- Read a register. Not `@[simp]`; the register-file laws are the rewrite path. -/
def get (s : ZState) (r : String) : Zmm := s.regs r

/-- Write a register, leaving the others unchanged. -/
def setV (s : ZState) (r : String) (v : Zmm) : ZState :=
  { regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem get_setV_same (s : ZState) (r : String) (v : Zmm) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_apply (s : ZState) (r r' : String) (v : Zmm) (i : Fin 8) :
    (s.setV r v).get r' i = if r' = r then v i else s.get r' i := by
  by_cases h : r' = r
  · subst h; simp [get_setV_same]
  · simp [setV, get, h]

end ZState

/-- The semantics of one packed instruction on the 8-lane register file: the
    lane operation applied independently in each of the eight `u64` lanes. -/
def evalZInst (s : ZState) : WInst → ZState
  | .vpaddq d a b  => s.setV d (fun i => laneAdd (s.get a i) (s.get b i))
  | .vpxor d a b   => s.setV d (fun i => laneXor (s.get a i) (s.get b i))
  | .vpand d a b   => s.setV d (fun i => laneAnd (s.get a i) (s.get b i))
  | .vpor d a b    => s.setV d (fun i => laneOr (s.get a i) (s.get b i))
  | .vpsllq d a m  => s.setV d (fun i => laneShl (s.get a i) m)
  | .vpsrlq d a m  => s.setV d (fun i => laneShr (s.get a i) m)

/-- Straight-line fold of `evalZInst`. -/
def runZBlock (s : ZState) : List WInst → ZState
  | [] => s
  | i :: is => runZBlock (evalZInst s i) is

@[simp] theorem runZBlock_nil (s : ZState) : runZBlock s [] = s := rfl

@[simp] theorem runZBlock_cons (s : ZState) (i : WInst) (is : List WInst) :
    runZBlock s (i :: is) = runZBlock (evalZInst s i) is := rfl

@[simp] theorem runZBlock_append (s : ZState) (b1 b2 : List WInst) :
    runZBlock s (b1 ++ b2) = runZBlock (runZBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runZBlock_cons, ih]

/-! ## 2. Per-lane realisation of the round and schedule blocks at eight lanes

The round and schedule instruction blocks are the 4-lane emit's `roundBlk` /
`schedBlk` unchanged. Run on the 8-lane register file, each lane independently
computes the FIPS-180-4 §6.4.2 round and the §6.4.2 schedule recurrence: the
statements quantify over `ℓ : Fin 8` and the proofs never case on `ℓ`, so lane
independence is what makes them lane-count-generic. -/

/-- **`a'`/`e'` SHA-512 round realisation at each of the eight ZMM lanes.** -/
theorem roundBlk_realizes_zmm (s : ZState) (ℓ : Fin 8) :
    let out := runZBlock s (roundBlk "ra" "re"
      "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt")
    out.get "ra" ℓ
      = (shaRound (s.get "kt" ℓ) (s.get "wt" ℓ)
          { a := s.get "va" ℓ, b := s.get "vb" ℓ, c := s.get "vc" ℓ, d := s.get "vd" ℓ
          , e := s.get "ve" ℓ, f := s.get "vf" ℓ, g := s.get "vg" ℓ, h := s.get "vh" ℓ }).a
    ∧ out.get "re" ℓ
      = (shaRound (s.get "kt" ℓ) (s.get "wt" ℓ)
          { a := s.get "va" ℓ, b := s.get "vb" ℓ, c := s.get "vc" ℓ, d := s.get "vd" ℓ
          , e := s.get "ve" ℓ, f := s.get "vf" ℓ, g := s.get "vg" ℓ, h := s.get "vh" ℓ }).e := by
  constructor <;>
    · simp only [roundBlk, rotBlk, bigSigma1Blk, bigSigma0Blk, runZBlock_cons,
        runZBlock_append, runZBlock_nil, evalZInst, ZState.get_setV_apply,
        String.reduceEq, ite_true, ite_false,
        shaRound, bigSigma1L, bigSigma0L, chL, majL, rotrSynth, laneAdd, laneXor,
        laneAnd, laneOr, laneShl, laneShr]
      ring

/-- **SHA-512 schedule realisation at each of the eight ZMM lanes.** -/
theorem schedBlk_realizes_zmm (s : ZState) (ℓ : Fin 8) :
    (runZBlock s (schedBlk "wd" "w2" "w7" "w15" "w16")).get "wd" ℓ
      = schedNext (s.get "w2" ℓ) (s.get "w7" ℓ) (s.get "w15" ℓ) (s.get "w16" ℓ) := by
  simp only [schedBlk, rotBlk, runZBlock_cons, runZBlock_append, runZBlock_nil,
    evalZInst, ZState.get_setV_apply, String.reduceEq, ite_true, ite_false,
    schedNext, smallSigma1L, smallSigma0L, rotrSynth, laneAdd,
    laneXor, laneOr, laneShl, laneShr]

/-! ## 3. The 8-lane vectorisation corollary

Packing eight streams into the eight ZMM lanes denotes eight independent scalar
SHA-512 compressions. This is `LaneMap.laneMap_eq_scalarMap` at
`α = β = (Fin 8 → BitVec 64)` (the eight chaining words) and `L = 8`; the term
is that theorem applied, since `LaneMap.scalarMap f v` is `fun i => f (v i)`.
The `L = 4` and 8×`u32` siblings are `Sha2MultiBuf.sha512_4way_lane_map` and
`Sha2MultiBuf.sha256_8way_lane_map`. -/

/-- **SHA-512 8-way lane map** (corollary of `LaneMap.laneMap_eq_scalarMap`): for
    any single-block compression on the eight chaining words, applying it packed
    across the eight ZMM lanes equals running it independently on each of the
    eight streams. -/
theorem sha512_8way_lane_map
    (compress : (Fin 8 → BitVec 64) → (Fin 8 → BitVec 64))
    (streams : Fin 8 → (Fin 8 → BitVec 64)) :
    LaneMap.laneMap compress streams = (fun i => compress (streams i)) :=
  LaneMap.laneMap_eq_scalarMap compress streams

/-! ## 4. EVEX AT&T renderer

One `WInst` prints to one AT&T line over `%zmm` operands. `vpxor`/`vpand`/`vpor`
are VEX-only mnemonics, so the ZMM forms are `vpxorq`/`vpandq`/`vporq`;
`vpaddq` and the immediate-count `vpsllq`/`vpsrlq` keep their mnemonic.
Three-operand AT&T order is `op src2, src1, dst`. A name may resolve to a
memory operand rather than a register, which is how the schedule reads its
`W[t-7]` / `W[t-16]` window slots directly. -/

/-- A register assignment: abstract name → `%zmmN` or a memory operand. -/
abbrev ZAlloc := List (String × String)

/-- The operand an abstract name maps to; an unmapped name yields an explicit
    `<UNALLOCATED:n>` sentinel so an over-budget block is rejected by gas rather
    than silently aliasing. -/
def zmmOf (alloc : ZAlloc) (n : String) : String :=
  (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- Print one `WInst` to its AT&T `%zmm` line (EVEX `q`-suffixed logical forms,
    immediate-first shifts). -/
def renderZInst (alloc : ZAlloc) : WInst → String
  | .vpaddq d a b  =>
      "\tvpaddq " ++ zmmOf alloc b ++ ", " ++ zmmOf alloc a ++ ", " ++ zmmOf alloc d
  | .vpxor d a b   =>
      "\tvpxorq " ++ zmmOf alloc b ++ ", " ++ zmmOf alloc a ++ ", " ++ zmmOf alloc d
  | .vpand d a b   =>
      "\tvpandq " ++ zmmOf alloc b ++ ", " ++ zmmOf alloc a ++ ", " ++ zmmOf alloc d
  | .vpor d a b    =>
      "\tvporq " ++ zmmOf alloc b ++ ", " ++ zmmOf alloc a ++ ", " ++ zmmOf alloc d
  | .vpsllq d a m  =>
      "\tvpsllq $" ++ toString m ++ ", " ++ zmmOf alloc a ++ ", " ++ zmmOf alloc d
  | .vpsrlq d a m  =>
      "\tvpsrlq $" ++ toString m ++ ", " ++ zmmOf alloc a ++ ", " ++ zmmOf alloc d

/-- Print a whole block. -/
def renderBlock (alloc : ZAlloc) (block : List WInst) : List String :=
  block.map (renderZInst alloc)

/-! ## 5. Register file and stack-slot layout -/

/-- Ring register holding a working word. -/
def zmmA := "%zmm0"
/-- Ring register holding a working word. -/
def zmmB := "%zmm1"
/-- Ring register holding a working word. -/
def zmmC := "%zmm2"
/-- Ring register holding a working word. -/
def zmmD := "%zmm3"
/-- Ring register holding a working word. -/
def zmmE := "%zmm4"
/-- Ring register holding a working word. -/
def zmmF := "%zmm5"
/-- Ring register holding a working word. -/
def zmmG := "%zmm6"
/-- Ring register holding a working word. -/
def zmmH := "%zmm7"
/-- The round constant `K[t]`, broadcast across the eight lanes. -/
def zmmKt := "%zmm8"
/-- The schedule word `W[t]`. -/
def zmmWt := "%zmm9"
/-- Scratch. -/
def zmmT0 := "%zmm10"
/-- Scratch. -/
def zmmT1 := "%zmm11"
/-- Scratch. -/
def zmmT2 := "%zmm12"
/-- Scratch. -/
def zmmT3 := "%zmm13"
/-- Scratch. -/
def zmmT4 := "%zmm14"
/-- Scratch. -/
def zmmT5 := "%zmm15"

/-- A memory operand `off(%reg)` for `u512` slot `i` (64 bytes per slot). -/
def memSlot (reg : String) (i : Nat) : String := toString (64*i) ++ "(" ++ reg ++ ")"

/-- A `%rsp`-relative schedule-window slot (16 slots, bytes `0..1023`). -/
def wSlot (i : Nat) : String := toString (64*i) ++ "(%rsp)"

/-- The chaining-save slot `S[i]` (8 slots, bytes `1024..1535`). -/
def sSlot (i : Nat) : String := toString (1024 + 64*i) ++ "(%rsp)"

/-- The eight working-word ring registers `%zmm0..7`. -/
def zmmRing : List String := [zmmA, zmmB, zmmC, zmmD, zmmE, zmmF, zmmG, zmmH]

/-- The ring register holding logical word `j` at round `t`. -/
def ringSlot (t j : Nat) : String := zmmRing.getD ((j + 8 - t % 8) % 8) zmmA

/-- The shared scratch / constant allocation. -/
def scratchAlloc : ZAlloc :=
  [ ("t0", zmmT0), ("t1", zmmT1), ("t2", zmmT2), ("t3", zmmT3), ("t4", zmmT4)
  , ("t5", zmmT5), ("kt", zmmKt), ("wt", zmmWt) ]

/-- The per-round allocation: the eight working words at their ring positions for
    round `t`, with `a'` written where `h` sat and `e'` where `d` sat. -/
def roundAlloc (t : Nat) : ZAlloc :=
  [ ("va", ringSlot t 0), ("vb", ringSlot t 1), ("vc", ringSlot t 2)
  , ("vd", ringSlot t 3), ("ve", ringSlot t 4), ("vf", ringSlot t 5)
  , ("vg", ringSlot t 6), ("vh", ringSlot t 7)
  , ("ra", ringSlot t 7), ("re", ringSlot t 3) ] ++ scratchAlloc

/-- The schedule allocation: `w2`, `w15` in the free `%zmm8`/`%zmm9` slots; `w7`,
    `w16` read straight out of their window memory operands; scratch and the
    result `sd` on `%zmm10..14`, all distinct. -/
def schedAllocOf (w7mem w16mem : String) : ZAlloc :=
  [ ("w2", zmmKt), ("w15", zmmWt), ("w7", w7mem), ("w16", w16mem)
  , ("t3", zmmT0), ("t4", zmmT1), ("t0", zmmT2), ("t1", zmmT3), ("t5", zmmT4)
  , ("sd", zmmT0) ]

/-! ## 6. The broadcast round-constant table and the round emitter -/

/-- The `.rodata` label of the broadcast round-constant table. -/
def kLabel : String := "sha512_x8_kbr"

/-- The memory operand of the broadcast round constant for round `t`. -/
def kSlot (t : Nat) : String := kLabel ++ "+" ++ toString (64*t) ++ "(%rip)"

/-- The `.rodata` broadcast round-constant table: each `K[t]` as a `.quad`×8, one
    per lane, 64-byte aligned so a single aligned ZMM move loads it. -/
def kRodata : List String :=
  [ "\t.section\t.rodata", "\t.align\t64", kLabel ++ ":" ]
  ++ (List.range 80).map (fun t =>
      let v := toString (k512[t]!).toNat
      "\t.quad\t" ++ String.intercalate ", " (List.replicate 8 v))

/-- One emitted SHA-512 round `t` (0..79): for `t ≥ 16` the schedule recompute
    that overwrites window slot `t % 16`, then the `K[t]`/`W[t]` loads, then the
    round body at round `t`'s ring positions. -/
def emitRound (t : Nat) : List String :=
  let sched : List String :=
    if t ≥ 16 then
      [ "\tvmovdqa64\t" ++ wSlot ((t-2)%16)  ++ ", " ++ zmmKt
      , "\tvmovdqa64\t" ++ wSlot ((t-15)%16) ++ ", " ++ zmmWt ]
      ++ renderBlock (schedAllocOf (wSlot ((t-7)%16)) (wSlot ((t-16)%16)))
           (schedBlk "sd" "w2" "w7" "w15" "w16")
      ++ [ "\tvmovdqa64\t" ++ zmmT0 ++ ", " ++ wSlot (t%16) ]
    else []
  let loadKW :=
    [ "\tvmovdqa64\t" ++ kSlot t ++ ", " ++ zmmKt
    , "\tvmovdqa64\t" ++ wSlot (t%16) ++ ", " ++ zmmWt ]
  let roundBody := renderBlock (roundAlloc t)
    (roundBlk "ra" "re" "va" "vb" "vc" "vd" "ve" "vf" "vg" "vh" "kt" "wt")
  sched ++ loadKW ++ roundBody

/-- The emitted prologue: align the stack to 64 bytes and reserve the 1536-byte
    frame, load the eight chaining words into the ring and save them for the
    feed-forward, then load the sixteen message words into the schedule window. -/
def prologue : List String :=
  [ "\tpush\t%rbp", "\tmovq\t%rsp, %rbp", "\tandq\t$-64, %rsp", "\tsubq\t$1536, %rsp" ]
  ++ (List.range 8).flatMap (fun i =>
      [ "\tvmovdqu64\t" ++ memSlot "%rdi" i ++ ", " ++ zmmRing.getD i zmmA
      , "\tvmovdqa64\t" ++ zmmRing.getD i zmmA ++ ", " ++ sSlot i ])
  ++ (List.range 16).flatMap (fun w =>
      [ "\tvmovdqu64\t" ++ memSlot "%rsi" w ++ ", " ++ zmmT0
      , "\tvmovdqa64\t" ++ zmmT0 ++ ", " ++ wSlot w ])

/-- The emitted epilogue: the FIPS feed-forward add of the saved chaining words
    into the ring registers (after 80 rounds `80 % 8 = 0`, so the ring is back at
    the identity), stored through `%rdi`, then the frame teardown. -/
def epilogue : List String :=
  (List.range 8).flatMap (fun i =>
    [ "\tvpaddq\t" ++ sSlot i ++ ", " ++ zmmRing.getD i zmmA ++ ", " ++ zmmT0
    , "\tvmovdqu64\t" ++ zmmT0 ++ ", " ++ memSlot "%rdi" i ])
  ++ [ "\tmovq\t%rbp, %rsp", "\tpopq\t%rbp", "\tvzeroupper", "\tret" ]

/-! ## 7. The whole function -/

/-- The full emitted `sha512_compress_x8` function text: header, prologue, the 80
    rounds, epilogue, and the broadcast round-constant `.rodata` table. -/
def sha512x8ExportAsm : String :=
  let header :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t6"
    , "\t.global\tsha512_compress_x8", "\t.type\tsha512_compress_x8, @function"
    , "sha512_compress_x8:" ]
  let body := (List.range 80).flatMap emitRound
  let footer := [ "\t.section\t.note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n"
    (header ++ prologue ++ body ++ epilogue ++ kRodata ++ footer) ++ "\n"

/-! ## 8. Structural pins on the renderer and the round shape -/

/- The logical ops render to the `q`-suffixed EVEX mnemonics (`vpxor`/`vpand`/
   `vpor` have no ZMM encoding), in AT&T `op src2, src1, dst` order. -/
#guard renderZInst [("d", "%zmm0"), ("a", "%zmm1"), ("b", "%zmm2")]
         (.vpxor "d" "a" "b") == "\tvpxorq %zmm2, %zmm1, %zmm0"
#guard renderZInst [("d", "%zmm0"), ("a", "%zmm1"), ("b", "%zmm2")]
         (.vpand "d" "a" "b") == "\tvpandq %zmm2, %zmm1, %zmm0"
#guard renderZInst [("d", "%zmm0"), ("a", "%zmm1"), ("b", "%zmm2")]
         (.vpor "d" "a" "b") == "\tvporq %zmm2, %zmm1, %zmm0"
#guard renderZInst [("d", "%zmm0"), ("a", "%zmm1"), ("b", "%zmm2")]
         (.vpaddq "d" "a" "b") == "\tvpaddq %zmm2, %zmm1, %zmm0"

/- The immediate-count shifts keep their mnemonic and take the count first. -/
#guard renderZInst [("d", "%zmm0"), ("a", "%zmm1")]
         (.vpsllq "d" "a" 36) == "\tvpsllq $36, %zmm1, %zmm0"
#guard renderZInst [("d", "%zmm0"), ("a", "%zmm1")]
         (.vpsrlq "d" "a" 28) == "\tvpsrlq $28, %zmm1, %zmm0"

/- A schedule window slot and a saved chaining slot are 64-byte-strided and
   disjoint: the sixteen window slots occupy bytes `0..1023`, the eight saved
   words `1024..1535`. -/
#guard wSlot 15 == "960(%rsp)"
#guard sSlot 0 == "1024(%rsp)"
#guard sSlot 7 == "1472(%rsp)"

/- The SoA ABI puts word `i` at byte offset `64*i` from its pointer. -/
#guard memSlot "%rdi" 7 == "448(%rdi)"
#guard memSlot "%rsi" 15 == "960(%rsi)"

/- The ring returns to the identity after eight rounds, so the epilogue reads the
   working words out of `%zmm0..7` in order. -/
#guard ringSlot 0 0 == "%zmm0"
#guard ringSlot 8 0 == "%zmm0"
#guard ringSlot 0 7 == "%zmm7"
#guard ringSlot 1 0 == "%zmm7"

/- A round below 16 emits the two constant/schedule loads plus the 36-instruction
   round body; a round at or above 16 prepends the two window loads, the
   21-instruction schedule recompute and the window store. -/
#guard (emitRound 0).length == 38
#guard (emitRound 16).length == 62

/- The broadcast round-constant table carries the section directives plus one
   `.quad`×8 line per round. -/
#guard kRodata.length == 83
#guard kSlot 0 == "sha512_x8_kbr+0(%rip)"
#guard kSlot 79 == "sha512_x8_kbr+5056(%rip)"

/-! ## 9. Emit driver -/

/-- Write the emitted whole-function 8-way SHA-512 compression `.s` to
    `bench/sha2_compare/gen_com/`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/sha2_compare/gen_com"
  IO.FS.writeFile "bench/sha2_compare/gen_com/sha512_compress_x8_zmm.s"
    sha512x8ExportAsm
  IO.println
    "wrote bench/sha2_compare/gen_com/sha512_compress_x8_zmm.s (owned AVX-512 ZMM, 8x u64)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8ZmmWideEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8ZmmWideEmit in
/-- `lake env lean --run` entry point. -/
def main : IO Unit := emit
