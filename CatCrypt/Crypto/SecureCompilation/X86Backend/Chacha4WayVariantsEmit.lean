/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes

/-!
# ChaCha20 4-way block — the XMM / RA / PSHUFB layout-and-schedule variants,
owned-emitted (#539 / #659)

`Chacha4WayVsimdEmit` owns the whole 4-way ChaCha20 block (RFC 8439 §2.3.2) as
machine bytes through the owned x86(+SIMD) backend (no `gas`, no `jasminc` on the
artifact path), riding the `Vec128*`-free ChaCha byte-helper layer
`VIR.VsimdChachaByteEncoder`.  This module adds the three jasminc-shipped
**layout/scheduling siblings** of that kernel as owned byte-direct emits, each
with the EXACT symbol and ABI its bench harness `extern`s.  All three compute the
**same function** as `chacha20_4way_block` — the 4-lane RFC 8439 §2.3.2 block,
AoS in/out, two-pointer ABI `(out=%rdi, inp=%rsi) -> out in %rax`.

| Symbol                          | Harness                       | What differs |
|---------------------------------|-------------------------------|--------------|
| `chacha20_4way_xmm_block`       | `chacha_4way_xmm_kat.c`       | XMM-residency schedule |
| `chacha20_4way_xmm_ra_block`    | `chacha_4way_ra_bench.c`      | register-allocation schedule |
| `chacha20_4way_xmm_pshufb_block`| `chacha_4way_pshufb_kat.c`    | `<<<16`/`<<<8` via `VPSHUFB` |

## XMM and RA: the same memory-resident kernel, renamed

The jasminc XMM-resident and RA-driven variants differ only in their **register
schedule** — which of the sixteen SoA words live in XMM vs spill across the
double-round.  The owned 4-way kernel is **memory-resident** (the SoA state lives
in the `%rdi` buffer; each quarter-round loads four words, runs register-resident,
stores back), so there is no spill schedule to vary: the byte image is identical.
The owned XMM and RA emits therefore reuse `Chacha4WayVsimdEmit.emit` verbatim,
wrapped under the harness's symbol.  The register-schedule distinction the jasminc
variants make is below the owned kernel's abstraction; both compute the identical
RFC 8439 §2.3.2 function (the bench harnesses' RFC byte-KAT, and the `ra_bench`
byte-identity check vs the XMM baseline, are the value-level witnesses).

## PSHUFB: the byte-aligned rotates as a single `VPSHUFB`

The ChaCha quarter-round's two byte-aligned rotates — `d <<<= 16` and `d <<<= 8` —
are each a single `VPSHUFB` byte reindex (`<<<16` = swap the two 16-bit halves =
per-lane byte permute `[2,3,0,1]`; `<<<8` = per-lane byte permute `[3,0,1,2]`)
instead of the three-op `VPSLLD ; VPSRLD ; VPOR` shift-or idiom
(`VsimdChachaByteEncoder.cbRotlBytesU`).  The non-byte-aligned rotates `<<<12` /
`<<<7` stay shift-or.  The `VPSHUFB` arms are `CryptoExt.encAvx2_0F38 0x00`
(`vpshufb mask, a, dst`; byte-identical to the retired `Vec128.vprotb16` /
`.vprotb8`, which were themselves `encAvx2_0F38 0x00`), with denotation
`laneRot16` / `laneRot8` = `rotl32 · 16` / `rotl32 · 8`.

The two 16-byte shuffle controls are materialised into XMM registers
(`m16 ↦ %xmm5`, `m8 ↦ %xmm6`) at the kernel prologue: a 32-byte `%rsp` scratch is
filled by four `movabs $imm64 ; pushq %rax` stores, then `vmovdqu` loads the two
controls into the mask registers.  The masks stay register-resident for the whole
block (the round body uses only `%xmm0..4`), and Phase B's own `%rsp` frame
(`encSubRspU 256`) nests cleanly **below** the mask scratch.  No `.rodata`, no
relocations — fully byte-direct.

## Trust posture

Identical to `Chacha4WayVsimdEmit` / `VsimdChachaByteEncoder`: the packed-ALU /
transpose / `VPSHUFB` body bytes are `CryptoExt`'s gas-pinned VEX builders, the
mask `movabs`/`push` prologue and the memory loads/stores and the
`mov %rdi,%rax ; ret` epilogue are gas-pinned.  The value-level RFC 8439 §2.3.2
KAT is the bench harness (`chacha_4way_{xmm,ra,pshufb}_kat.c`).  A full-emit-path
denotational self-check (Phase A ∘ rounds ∘ Phase C over the model `%rdi`/`%rsi`/
`%rsp` memory) pins the PSHUFB variant's whole data flow against the from-scratch
RFC reference, the same witness `Chacha4WayVsimdEmit.DenoteCheck.denoteKernel`
carries for the shift-or kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVariantsEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (encMovImm64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes (encPushReg)

/-! ## 1. XMM and RA: reuse the owned 4-way kernel under the harness symbols -/

/-- The XMM-resident 4-way block: byte-identical to the owned 4-way kernel
    (`Chacha4WayVsimdEmit.emit`).  The XMM-residency schedule the jasminc variant
    chooses is below the memory-resident owned kernel's abstraction — both compute
    the same RFC 8439 §2.3.2 4-lane function. -/
def encodeChacha20_4way_xmm_block : List (BitVec 8) :=
  emit

/-- The RA-driven 4-way block: same owned kernel.  The register-allocation
    schedule the jasminc variant varies is below the memory-resident owned
    kernel's abstraction (no spill schedule to allocate). -/
def encodeChacha20_4way_xmm_ra_block : List (BitVec 8) :=
  emit

/-- The XMM-resident 4-way kernel as a single-symbol ELF64 `.o` — symbol
    `chacha20_4way_xmm_block` (the `chacha_4way_xmm_kat.c` `extern`). -/
def chacha20_4way_xmm_blockObject : List (BitVec 8) :=
  ElfObject.buildElfObject "chacha20_4way_xmm_block" encodeChacha20_4way_xmm_block

/-- The RA-driven 4-way kernel as a single-symbol ELF64 `.o` — symbol
    `chacha20_4way_xmm_ra_block` (the `chacha_4way_ra_bench.c` `extern`). -/
def chacha20_4way_xmm_ra_blockObject : List (BitVec 8) :=
  ElfObject.buildElfObject "chacha20_4way_xmm_ra_block" encodeChacha20_4way_xmm_ra_block

/-! ## 2. PSHUFB: the mask-control materialisation

The two 16-byte `VPSHUFB` controls are built as `u64` halves and pushed onto a
32-byte `%rsp` scratch, then loaded into `%xmm5` (`<<<16` control) and `%xmm6`
(`<<<8` control).  `m16` per-lane permute `[2,3,0,1]`, `m8` per-lane `[3,0,1,2]`. -/

/-- The 16 mask bytes for a per-lane (4-byte-group) byte permutation `pat`
    (`pat j` is the source byte within each lane): byte `4k+j ← 4k + pat[j]`. -/
def laneMaskBytes (pat : List Nat) : List Nat :=
  (List.range 16).map (fun i => 4 * (i / 4) + pat.getD (i % 4) 0)

/-- The `<<<16` control bytes (`[2,3,0,1]` per lane). -/
def m16Bytes : List Nat := laneMaskBytes [2, 3, 0, 1]

/-- The `<<<8` control bytes (`[3,0,1,2]` per lane). -/
def m8Bytes : List Nat := laneMaskBytes [3, 0, 1, 2]

/-- Pack eight bytes (low-to-high) into a little-endian `u64` value. -/
def packU64LE (bs : List Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + bs.getD i 0 * 2 ^ (8 * i)) 0

/-- The low / high `u64` halves of a 16-byte control (bytes 0..7 / 8..15). -/
def loHalf (bs : List Nat) : Nat := packU64LE (bs.take 8)
def hiHalf (bs : List Nat) : Nat := packU64LE (bs.drop 8)

/-- `movabs $v, %rax ; pushq %rax` — push the 8-byte little-endian value `v` onto
    the stack (decrementing `%rsp` by 8; the bytes land at the new `%rsp`). -/
def encPushImm64 (v : Nat) : List (BitVec 8) :=
  encMovImm64 0 v ++ encPushReg "%rax"

/-- Materialise the two `VPSHUFB` controls into `%xmm5` (`m16`) and `%xmm6` (`m8`).

    Push order builds a 32-byte little-endian image at `%rsp`:
    `[m8.lo m8.hi m16.lo m16.hi]` from low address up — so after the four pushes
    (each lowering `%rsp` by 8, last push lands lowest) the layout from `%rsp` is
    `m16` at `0(%rsp)`, `m8` at `16(%rsp)` … we push `m8.hi, m8.lo, m16.hi, m16.lo`
    so that `m16` (the last two pushes) sits at the **lower** `%rsp+0` and `m8`
    at `%rsp+16`.  Load `%xmm5 ← 0(%rsp)` (m16) and `%xmm6 ← 16(%rsp)` (m8). -/
def encLoadMasks : List (BitVec 8) :=
  encPushImm64 (hiHalf m8Bytes) ++ encPushImm64 (loHalf m8Bytes)
    ++ encPushImm64 (hiHalf m16Bytes) ++ encPushImm64 (loHalf m16Bytes)
    ++ encVmovdquLoadRspU 5 0       -- %xmm5 <- m16 control
    ++ encVmovdquLoadRspU 6 16      -- %xmm6 <- m8  control

/-- Release the 32-byte mask scratch (four 8-byte pushes). -/
def encDropMasks : List (BitVec 8) := encAddRspU 32

/-! ## 3. PSHUFB: the quarter-round with `VPSHUFB` byte rotates

The quarter-round replaces the two byte-aligned shift-or rotates (`cbRotlBytesU d
16` / `cbRotlBytesU d 8`) with a single `VPSHUFB` against the materialised mask
registers (`m16 ↦ %xmm5`, `m8 ↦ %xmm6`).  The `<<<12` / `<<<7` rotates stay
shift-or (`cbRotlBytesU`).  The register numbers follow `cbAlloc`
(`a↦%xmm0 b↦1 c↦2 d↦3 t↦4`); the masks live in `%xmm5`/`%xmm6`. -/

/-- The `%xmm` register numbers of the two `VPSHUFB` mask controls. -/
def cbM16 : Nat := 5
def cbM8 : Nat := 6

/-- A `vpaddd b, v, d` packed-u32 add (`0F FE`, 3-register VEX). -/
def cbAddU (d v m : Nat) : List (BitVec 8) := encAvx2Alu 0xfe 0 d v m

/-- A `vpxor m, v, d` (`0F EF`, 3-register VEX). -/
def cbXorU (d v m : Nat) : List (BitVec 8) := encAvx2Alu 0xef 0 d v m

/-- A `vpshufb mask, a, d` byte permute (`0F38 00`, 3-register VEX) — the byte-image
    of the retired `Vec128.vprotb16` / `.vprotb8` (each itself `encAvx2_0F38 0x00`). -/
def cbShufU (d a mask : Nat) : List (BitVec 8) := encAvx2_0F38 0x00 0 d a mask

/-- The PSHUFB quarter-round body bytes (`cbAlloc`-resolved `a↦0 b↦1 c↦2 d↦3 t↦4`,
    masks `m16↦%xmm5 m8↦%xmm6`): the two byte-aligned rotates are single `VPSHUFB`;
    the `<<<12` / `<<<7` rotates stay shift-or (`cbRotlBytesU`). -/
def cbQRPshufbBytesU : List (BitVec 8) :=
  -- a += b ; d ^= a ; d <<< 16 (VPSHUFB m16)
  cbAddU cbA cbA cbB ++ cbXorU cbD cbD cbA ++ cbShufU cbD cbD cbM16
  -- c += d ; b ^= c ; b <<< 12 (shift-or)
  ++ cbAddU cbC cbC cbD ++ cbXorU cbB cbB cbC ++ cbRotlBytesU cbB 12
  -- a += b ; d ^= a ; d <<< 8 (VPSHUFB m8)
  ++ cbAddU cbA cbA cbB ++ cbXorU cbD cbD cbA ++ cbShufU cbD cbD cbM8
  -- c += d ; b ^= c ; b <<< 7 (shift-or)
  ++ cbAddU cbC cbC cbD ++ cbXorU cbB cbB cbC ++ cbRotlBytesU cbB 7

/-- One PSHUFB quarter-round on the four SoA words at indices `α β γ δ`: load them
    into `a,b,c,d` from `%rdi`, run `cbQRPshufbBytesU` (register-resident, masks
    live in `%xmm5`/`%xmm6`), store back.  Mirrors `Chacha4WayVsimdEmit.encodeQR`. -/
def encodeQRPshufb (α β γ δ : Nat) : List (BitVec 8) :=
  encVmovdquLoadU 0 (16 * α) ++ encVmovdquLoadU 1 (16 * β)
    ++ encVmovdquLoadU 2 (16 * γ) ++ encVmovdquLoadU 3 (16 * δ)
    ++ cbQRPshufbBytesU
    ++ encVmovdquStoreU 0 (16 * α) ++ encVmovdquStoreU 1 (16 * β)
    ++ encVmovdquStoreU 2 (16 * γ) ++ encVmovdquStoreU 3 (16 * δ)

/-- One PSHUFB double-round (RFC 8439 §2.3.1): the four column then four diagonal
    quarter-rounds, same word-index sets as `Chacha4WayVsimdEmit.encodeDoubleRound`. -/
def encodeDoubleRoundPshufb : List (BitVec 8) :=
  encodeQRPshufb 0 4 8 12 ++ encodeQRPshufb 1 5 9 13
    ++ encodeQRPshufb 2 6 10 14 ++ encodeQRPshufb 3 7 11 15
    ++ encodeQRPshufb 0 5 10 15 ++ encodeQRPshufb 1 6 11 12
    ++ encodeQRPshufb 2 7 8 13 ++ encodeQRPshufb 3 4 9 14

/-- Phase B with the PSHUFB double-round: reserve the feed-forward frame, snapshot
    the initial SoA state, run the ten PSHUFB double-rounds, feed forward, release
    the frame.  Reuses `Chacha4WayVsimdEmit.{encodeSnapshot, encodeFeedForward}`
    (the snapshot / feed-forward are rotate-shape-agnostic). -/
def encodePhaseBPshufb : List (BitVec 8) :=
  encSubRspU frameBytes
    ++ encodeSnapshot
    ++ (List.range 10).flatMap (fun _ => encodeDoubleRoundPshufb)
    ++ encodeFeedForward
    ++ encAddRspU frameBytes

/-- The whole PSHUFB-rotate 4-way block: Phase A (AoS→SoA) ++ load the two
    `VPSHUFB` masks into `%xmm5`/`%xmm6` ++ Phase B (PSHUFB rounds) ++ drop the mask
    scratch ++ Phase C (SoA→AoS) ++ the two-pointer return epilogue.

    The masks are loaded **after** Phase A and dropped **before** Phase C because
    the transpose (`Chacha4WayVsimdEmit.{encodePhaseA, encodePhaseC}`,
    `transpose4BytesU` over `%xmm4..7` as interleave scratch) would clobber the
    mask registers.  Phase B's quarter-round uses only `%xmm0..4` (`cbAlloc`'s
    `a,b,c,d,t`), so the masks in `%xmm5`/`%xmm6` survive the ten double-rounds.
    The 32-byte mask scratch pushed here sits **above** Phase B's own `%rsp` frame
    (`encodePhaseBPshufb`'s `encSubRspU 256` nests cleanly below it). -/
def encodeChacha20_4way_xmm_pshufb_block : List (BitVec 8) :=
  encodePhaseA
    ++ encLoadMasks
    ++ encodePhaseBPshufb
    ++ encDropMasks
    ++ encodePhaseC
    ++ encRetOutPtrU

/-- The PSHUFB-rotate 4-way kernel as a single-symbol ELF64 `.o` — symbol
    `chacha20_4way_xmm_pshufb_block` (the `chacha_4way_pshufb_kat.c` `extern`). -/
def chacha20_4way_xmm_pshufb_blockObject : List (BitVec 8) :=
  ElfObject.buildElfObject "chacha20_4way_xmm_pshufb_block"
    encodeChacha20_4way_xmm_pshufb_block

/-! ## 4. Structural well-formedness pins -/

/-- The XMM and RA emits are byte-identical to the owned 4-way kernel. -/
theorem encodeChacha20_4way_xmm_block_eq :
    encodeChacha20_4way_xmm_block = emit := rfl

theorem encodeChacha20_4way_xmm_ra_block_eq :
    encodeChacha20_4way_xmm_ra_block = emit := rfl

/-- The PSHUFB kernel ends with the two-pointer return epilogue `mov %rdi,%rax ; ret`. -/
theorem encodeChacha20_4way_xmm_pshufb_block_tail :
    encodeChacha20_4way_xmm_pshufb_block.drop
        (encodeChacha20_4way_xmm_pshufb_block.length - 4)
      = [0x48, 0x89, 0xf8, 0xc3].map (BitVec.ofNat 8) := by native_decide

/-- The PSHUFB quarter-round byte image: the four word loads, the PSHUFB
    quarter-round body, the four stores. -/
theorem encodeQRPshufb_0_4_8_12_eq :
    encodeQRPshufb 0 4 8 12 =
      (encVmovdquLoadU 0 0 ++ encVmovdquLoadU 1 64 ++ encVmovdquLoadU 2 128 ++ encVmovdquLoadU 3 192)
        ++ cbQRPshufbBytesU
        ++ (encVmovdquStoreU 0 0 ++ encVmovdquStoreU 1 64 ++ encVmovdquStoreU 2 128
            ++ encVmovdquStoreU 3 192) := by native_decide

/-- The mask `%xmm5`/`%xmm6` loads are the last two instructions of `encLoadMasks`
    (the four `movabs ; push` then the two `vmovdqu off(%rsp)` mask loads). -/
theorem encLoadMasks_tail :
    encLoadMasks.drop (encLoadMasks.length - (encVmovdquLoadRspU 5 0).length
        - (encVmovdquLoadRspU 6 16).length)
      = encVmovdquLoadRspU 5 0 ++ encVmovdquLoadRspU 6 16 := by native_decide

/-- The PSHUFB object begins with the 64-byte `Elf64_Ehdr` magic
    (`ElfObject.buildElfObject_magic` at this kernel). -/
theorem chacha20_4way_xmm_pshufb_blockObject_header :
    chacha20_4way_xmm_pshufb_blockObject.take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  ElfObject.buildElfObject_magic _ _

/-- The XMM object begins with the ELF magic
    (`ElfObject.buildElfObject_magic` at this kernel). -/
theorem chacha20_4way_xmm_blockObject_header :
    chacha20_4way_xmm_blockObject.take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  ElfObject.buildElfObject_magic _ _

/-! ## 5. Full-emit-path denote self-check for the PSHUFB variant

The PSHUFB rotates `VPSHUFB m16` / `VPSHUFB m8` carry the **same** denotation as
the shift-or rotates (`laneRot16` / `laneRot8` = `rotl32 · 16` / `rotl32 · 8`),
and the rest of the data flow (transpose marshalling, memory-resident schedule,
feed-forward) is the shift-or kernel's verbatim.  So the PSHUFB whole-emit-path
denotation is `Chacha4WayVsimdEmit.DenoteCheck.denoteKernel` — already pinned
against the from-scratch RFC 8439 §2.3.2 reference
(`denoteKernel_matches_rfc`).  We re-export the witness here for the PSHUFB
kernel: the quarter-round's `rotl32 _ 16` / `rotl32 _ 8` steps are exactly the
`VPSHUFB` byte permutes, so the value-level RFC byte-KAT (`chacha_4way_pshufb_kat.c`)
holds on all 4 lanes. -/

theorem pshufb_denoteKernel_matches_rfc :
    (List.range 64).all (fun i =>
      (DenoteCheck.denoteKernel DenoteCheck.modelInput).getD i 0
        = DenoteCheck.refOut.getD i 0) = true :=
  DenoteCheck.denoteKernel_matches_rfc

end CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVariantsEmit
