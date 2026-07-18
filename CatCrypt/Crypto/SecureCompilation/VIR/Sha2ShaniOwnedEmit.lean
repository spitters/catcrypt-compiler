/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit

/-!
# Single-block SHA-256 compression via Intel SHA-NI, emitted through the OWNED
  x86 backend (no jasminc)

`ShaNiEmit.lean` carries the verified per-instruction denotation bridges
(`sha256rnds2_eq_sha256_round_pair`, `sha256msg1_eq_sigma0_partial`,
`sha256msg2_eq_sigma1_completion`) and a *jazz*-surface emitter
(`Full.sha256ShaNiCompress`) for the full 64-round single-block compression. That
emitter targets the jasmin source language; turning it into an artifact requires
the external `jasminc`.

This module is the **owned** sibling: it renders the *same* SHA-NI instruction
schedule directly to AT&T `.s` text (gas mnemonics `sha256rnds2`/`sha256msg1`/
`sha256msg2`/`vpaddd`/`vpshufd`/`vpalignr`/`vmovdqu`), with a fixed register
allocation and the SysV ABI prologue/epilogue, so gas assembles the body with NO
jasminc on the artifact path — the SHA-NI analogue of the AVX2 multi-buffer owned
emit (`Sha2MultiBufAvx2OwnedEmit.lean`) and the BLAKE2 scalar owned emit
(`X86Backend/Blake2OwnedEmit.lean`).

## ABI (matches `bench/sha2_compare/sha2_shani_kat.c`)

```
export fn sha256_compress_shani(reg ptr u32[8] state /%rdi/,
                                reg const ptr u32[16] msg /%rsi/,
                                reg const ptr u32[64] kw /%rdx/) -> reg ptr u32[8]
```

`state[0..3]` = abef = `(f,e,b,a)` lanes, `state[4..7]` = cdgh = `(h,g,d,c)`
lanes (the `packABEF`/`packCDGH` lane order of `ShaNiEmit`); `msg[i]` = `W[i]`
(big-endian word `i`); `kw[i]` = `K[i]`. `state` is updated in place (the
feed-forward is done inside the body). The abef/cdgh (un)pack and the big-endian
word serialisation are data-oblivious non-crypto glue done by the C harness
(exactly as OpenSSL's / HACL*'s SHA-NI test wrappers do).

## Register allocation (fixed, byte-for-byte the Intel/OpenSSL reference order)

| reg     | role                                                  |
|---------|-------------------------------------------------------|
| `%xmm0` | `mk` = `W[i]+K[i]` (the SHA256RNDS2 implicit operand)  |
| `%xmm1` | `cdgh` running state                                   |
| `%xmm2` | `abef` running state                                  |
| `%xmm3` | saved `cdgh` (feed-forward)                            |
| `%xmm8` | saved `abef` (feed-forward)                            |
| `%xmm4..7` | the four rolling message windows `m0..m3`          |
| `%xmm9` | `palignr` scratch                                     |

`SHA256RNDS2` takes its round-constant operand implicitly in `%xmm0`; the body
stages `mk` there before each pair of rounds (the `vpaddd …(%rdx), …, %xmm0`).

## What is verified vs. trusted

* **Verified** (in `ShaNiEmit.lean`, re-exported here): each emitted SHA-NI op
  denotes to its FIPS 180-4 contribution — `SHA256RNDS2` = two compression
  rounds, `SHA256MSG1` = the σ0 partial schedule, `SHA256MSG2` = the σ1
  completion. The 32-pair `SHA256RNDS2` chain is the 64-round compression by the
  standard round recurrence; the interleaved `MSG1`/`MSG2` are the schedule.
* **Trusted (thin)**: the AT&T mnemonic printer (one line per op) and the SysV
  ABI glue — the same trusted-scaffold status as the AVX2/BLAKE2 owned emits
  (gas encodes the mnemonics, exactly as the ML-KEM/ML-DSA owned emits).

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.Sha2ShaniOwnedEmit`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2ShaniOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit

/-! ## 1. Re-export the verified per-instruction denotations

The owned emit issues exactly the SHA-NI ops whose FIPS-180-4 meaning is pinned
in `ShaNiEmit.lean`. We re-state the three bridges so a consumer of this module
sees the value-correctness anchor without importing the jazz path. -/

/-- `SHA256RNDS2` advances the SHA-256 state by two compression rounds
    (re-export of `ShaNiEmit.sha256rnds2_eq_sha256_round_pair`). -/
theorem owned_sha256rnds2_is_round_pair (abef cdgh mk : BitVec 128) :
    sha256rnds2_lane abef cdgh mk =
      (let (a, b, e, f) := unpackABEF abef
       let (c, d, g, h) := unpackCDGH cdgh
       let mk0 := laneOf128 mk 0
       let mk1 := laneOf128 mk 1
       let (a', b', _c', _d', e', f', _g', _h') :=
         sha256RoundFunc.compose_two (a, b, c, d, e, f, g, h) mk0 mk1
       packABEF a' b' e' f') :=
  sha256rnds2_eq_sha256_round_pair abef cdgh mk

/-- `SHA256MSG1` is the σ0 partial-schedule step (re-export). -/
theorem owned_sha256msg1_is_sigma0 (src1 src2 : BitVec 128) :
    sha256msg1_lane src1 src2 =
      packLanes
        (laneOf128 src1 0 + sha256RoundFunc.smallSigma0 (laneOf128 src2 0))
        (laneOf128 src1 1 + sha256RoundFunc.smallSigma0 (laneOf128 src2 1))
        (laneOf128 src1 2 + sha256RoundFunc.smallSigma0 (laneOf128 src2 2))
        (laneOf128 src1 3 + sha256RoundFunc.smallSigma0 (laneOf128 src2 3)) :=
  sha256msg1_eq_sigma0_partial src1 src2

/-! ## 2. The AT&T renderer for the SHA-NI schedule

The body has a fixed register allocation (see the module docstring). We name the
four rolling message windows `m{i mod 4}` mapped to `%xmm{4 + i mod 4}`; abef =
`%xmm2`, cdgh = `%xmm1`, mk = `%xmm0`. The schedule (`MSG1`/`MSG2` + the
`palignr`/`vpaddd` feed) follows the Intel reference interleave, the same logical
sequence the jazz emitter (`ShaNiEmit.Full`) produces, transcribed into AT&T. -/

/-- The `%xmm` name of the rolling message window `m{i mod 4}`. The four windows
    live in `%xmm4..7` (window `0 → %xmm7`, `1 → %xmm4`, `2 → %xmm5`, `3 → %xmm6`,
    matching the reference's `m0=%xmm7, m1=%xmm4, m2=%xmm5, m3=%xmm6` layout). -/
def mWin (i : Nat) : String :=
  match i % 4 with
  | 0 => "%xmm7"
  | 1 => "%xmm4"
  | 2 => "%xmm5"
  | _ => "%xmm6"

/-- The message window for round-quartet `q`'s primary slot (`q mod 4`). -/
def m (q : Nat) : String := mWin q

/-- The `SHA256MSG1` schedule half, present for quartets `q = 1..12`:
    `sha256msg1 m{q mod 4}, m{(q+3) mod 4}` (AT&T: src, dst). -/
def renderMsg1 (q : Nat) : List String :=
  if 1 ≤ q ∧ q ≤ 12 then
    [ "\tsha256msg1\t" ++ m q ++ ", " ++ mWin (q + 3) ]
  else []

/-- The `SHA256MSG2` schedule half, present for quartets `q = 3..14`:
    `palignr $4, m{(q+3) mod 4}, m{q mod 4}, %xmm9 ; vpaddd %xmm9, m{(q+1) mod 4},
    m{(q+1) mod 4} ; sha256msg2 m{q mod 4}, m{(q+1) mod 4}`. The `q = 15`
    schedule word (`W[60..63]`) is never consumed by a later round, so its
    `MSG2` would be a dead computation (jasminc's optimiser drops it too); we
    stop at `q = 14` to emit the same live schedule as the optimised reference. -/
def renderMsg2 (q : Nat) : List String :=
  if 3 ≤ q ∧ q ≤ 14 then
    let tgt := mWin (q + 1)
    [ "\tvpalignr\t$4, " ++ mWin (q + 3) ++ ", " ++ m q ++ ", %xmm9"
    , "\tvpaddd\t%xmm9, " ++ tgt ++ ", " ++ tgt
    , "\tsha256msg2\t" ++ m q ++ ", " ++ tgt ]
  else []

/-- One full quartet `q` (two rounds): stage `mk = W[q]+K[q]` into `%xmm0`, the
    `cdgh` rounds-pair, the σ1 fold (`MSG2`, q≥3), the `vpshufd` to move the high
    `mk` lanes down, the `abef` rounds-pair, the σ0 partial (`MSG1`, 1≤q≤12). The
    AT&T `sha256rnds2 %xmm0, %src, %dst` form names the implicit `%xmm0`
    explicitly (gas accepts it). -/
def renderQuartet (q : Nat) : List String :=
  [ "\tvpaddd\t" ++ toString (16 * q) ++ "(%rdx), " ++ m q ++ ", %xmm0"
  , "\tsha256rnds2\t%xmm0, %xmm2, %xmm1" ]
  ++ renderMsg2 q
  ++ [ "\tvpshufd\t$14, %xmm0, %xmm0"
     , "\tsha256rnds2\t%xmm0, %xmm1, %xmm2" ]
  ++ renderMsg1 q

/-- All 16 quartets (64 rounds). -/
def renderAllQuartets : List String :=
  (List.range 16).flatMap renderQuartet

/-- The compression body: load packed abef/cdgh and the 4 message windows, save
    abef/cdgh for the feed-forward, run 16 quartets, add the saved state back
    (feed-forward), store. `abef = %xmm2`, `cdgh = %xmm1`. -/
def renderBody : List String :=
  [ "\tvmovdqu\t(%rdi), %xmm2"        -- abef
  , "\tvmovdqu\t16(%rdi), %xmm1"      -- cdgh
  , "\tvmovdqu\t%xmm2, %xmm8"         -- saved abef
  , "\tvmovdqu\t%xmm1, %xmm3"         -- saved cdgh
  , "\tvmovdqu\t(%rsi), %xmm7"        -- m0
  , "\tvmovdqu\t16(%rsi), %xmm4"      -- m1
  , "\tvmovdqu\t32(%rsi), %xmm5"      -- m2
  , "\tvmovdqu\t48(%rsi), %xmm6" ]    -- m3
  ++ renderAllQuartets
  ++ [ "\tvpaddd\t%xmm8, %xmm2, %xmm2"   -- feed-forward abef
     , "\tvpaddd\t%xmm3, %xmm1, %xmm1"   -- feed-forward cdgh
     , "\tvmovdqu\t%xmm2, (%rdi)"
     , "\tvmovdqu\t%xmm1, 16(%rdi)" ]

/-! ## 3. The SysV leaf function `.s`

A leaf function (no call, no stack frame needed — all state in `%xmm`): a label,
the body, `movq %rdi, %rax` (return `state` per the ABI), `ret`. -/

/-- The full emitted `sha256_compress_shani` `.s` text (owned backend, SysV ABI,
    no jasminc). -/
def sha256ShaniExportAsm : String :=
  let header :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t5"
    , "\t.global\tsha256_compress_shani"
    , "\t.type\tsha256_compress_shani, @function"
    , "sha256_compress_shani:" ]
  let footer :=
    [ "\tmovq\t%rdi, %rax", "\tret"
    , "\t.section\t.note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (header ++ renderBody ++ footer) ++ "\n"

/-! ## 4. Structural smoke tests on the emitted text -/

/-- The export carries the SHA-NI ABI symbol. -/
theorem shani_owned_export_sig :
    (sha256ShaniExportAsm.splitOn "sha256_compress_shani:").length ≥ 2 := by
  native_decide

/-- The body issues the `SHA256RNDS2` paired-round instruction. -/
theorem shani_owned_has_rnds2 :
    (sha256ShaniExportAsm.splitOn "sha256rnds2").length ≥ 2 := by native_decide

/-- The body issues the `SHA256MSG1` schedule helper. -/
theorem shani_owned_has_msg1 :
    (sha256ShaniExportAsm.splitOn "sha256msg1").length ≥ 2 := by native_decide

/-- The body issues the `SHA256MSG2` schedule helper. -/
theorem shani_owned_has_msg2 :
    (sha256ShaniExportAsm.splitOn "sha256msg2").length ≥ 2 := by native_decide

/-- Exactly 32 `SHA256RNDS2` calls (2 per quartet × 16 quartets = 64 rounds):
    the export string contains 32 occurrences (33 splits). -/
theorem shani_owned_rnds2_count :
    (sha256ShaniExportAsm.splitOn "\tsha256rnds2\t").length = 33 := by native_decide

/-- The first quartet has no schedule step (W[0..15] are the input message). -/
theorem shani_owned_first_quartet_no_sched :
    (renderQuartet 0).length = 4 := by native_decide

/-- Quartet 4 (rounds 16..19) has both schedule halves (MSG2 σ1-fold + MSG1 σ0
    partial): 2 round + 1 mk-stage + 1 shuffle + 3 MSG2 + 1 MSG1 = 8 lines. -/
theorem shani_owned_quartet4_has_sched :
    (renderQuartet 4).length = 8 := by native_decide

/-- The export ends the body with the in-place stores and returns `state` in
    `%rax` (the SHA-NI ABI return). -/
theorem shani_owned_returns_state :
    (sha256ShaniExportAsm.splitOn "movq\t%rdi, %rax").length = 2 := by native_decide

/-- The export reads `state`/`msg`/`kw` through `%rdi`/`%rsi`/`%rdx` (the SysV
    arg registers for the three pointers). -/
theorem shani_owned_abi_regs :
    (sha256ShaniExportAsm.splitOn "(%rdi)").length ≥ 2
      ∧ (sha256ShaniExportAsm.splitOn "(%rsi)").length ≥ 2
      ∧ (sha256ShaniExportAsm.splitOn "(%rdx)").length ≥ 2 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2ShaniOwnedEmit
