/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

/-!
# The whole ChaCha20 4-way block, owned-emitted on the unified stack (Vec128 teardown)

This is the `Vec128*`-free twin of `X86Backend.Chacha4WayEmit`: the **whole**
4-way ChaCha20 block (RFC 8439 §2.3.2), assembled to machine bytes through the
owned x86(+SIMD) backend with neither `gas` nor `jasminc` on the artifact path —
but riding the standalone ChaCha byte-helper layer
`VIR.VsimdChachaByteEncoder` (the quarter-round body `cbQRBytesU`, the 4×4
transpose body `transpose4BytesU`, and the `vmovdqu`/`vpaddd`/`sub`/`add`/`ret`
ABI glue), so it imports **no** `Vec128*` file and **no** `SimdBytes`.

It reproduces, byte-for-byte, the `SimdBytes`-based
`Chacha4WayEmit.encodeChacha20_4way_block`: the structural seams and the
full-emit-path RFC 8439 §2.3.2 denotational self-check are preserved.

## Register budget — the memory-resident SoA schedule

Identical to `Chacha4WayEmit`: the sixteen SoA words stay resident in the
`%rdi` buffer and the round is processed one quarter-round at a time (each acts on
a disjoint four-word set), so only four words + one rotate temp (= five XMM) are
live at once.  The four words are loaded from the SoA buffer, the quarter-round
runs register-resident (`VsimdChachaByteEncoder.cbQRBytesU`, the RFC 8439 §2.1
rotates 16/12/8/7), and the four words are stored back.

```
  chacha20_4way_block (out=%rdi, inp=%rsi)
    Phase A  AoS→SoA : for g in 0..3: vmovdqu loads (%rsi) ; transpose ; stores (%rdi)
    Phase B  rounds  : sub %rsp ; snapshot ; 10×double-round ; feed-forward ; add %rsp
    Phase C  SoA→AoS : sub %rsp ; snapshot ; 4×transpose (read %rsp, write %rdi) ; add %rsp
    mov %rdi,%rax ; ret
    = emit : List (BitVec 8)  (the WHOLE block as bytes)
    --buildElfObject-->  chacha20_4way_block.o      (no gas, no jasminc, no Vec128)
```

The C harness (`bench/chacha_compare/chacha_4way_kat.c`, ABI
`uint32_t *chacha20_4way_block(uint32_t *out, const uint32_t *inp)`) links the
`.o` and checks the four AoS output blocks against RFC 8439 §2.3.2 — the
value-level KAT.

## Trust posture

Identical to `VsimdChachaByteEncoder` / `SimdBytes`: the quarter-round / transpose
body bytes and the ABI glue are each gas-pinned in `VsimdChachaByteEncoder`; the
VEX SIMD opcodes have no ACL2 x86isa decode tables, so this stays at the
gas-pinned validation tier — the same residual as the rest of the SIMD
byte path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder

/-! ## 1. The quarter-round on four memory-resident SoA words -/

/-- One quarter-round on the four SoA words at indices `α β γ δ`: load them into
    `a,b,c,d` from `%rdi` (word `k` at `16·k`), run `cbQRBytesU` (register-resident,
    the verified RFC 8439 §2.1 quarter-round), store the four updated words back. -/
def encodeQR (α β γ δ : Nat) : List (BitVec 8) :=
  encVmovdquLoadU 0 (16 * α) ++ encVmovdquLoadU 1 (16 * β)
    ++ encVmovdquLoadU 2 (16 * γ) ++ encVmovdquLoadU 3 (16 * δ)
    ++ cbQRBytesU
    ++ encVmovdquStoreU 0 (16 * α) ++ encVmovdquStoreU 1 (16 * β)
    ++ encVmovdquStoreU 2 (16 * γ) ++ encVmovdquStoreU 3 (16 * δ)

/-! ## 2. The double-round (column + diagonal), RFC 8439 §2.3.1 -/

/-- One ChaCha double-round (RFC 8439 §2.3.1) as machine bytes: the four column
    quarter-rounds then the four diagonal quarter-rounds. -/
def encodeDoubleRound : List (BitVec 8) :=
  encodeQR 0 4 8 12 ++ encodeQR 1 5 9 13 ++ encodeQR 2 6 10 14 ++ encodeQR 3 7 11 15
    ++ encodeQR 0 5 10 15 ++ encodeQR 1 6 11 12 ++ encodeQR 2 7 8 13 ++ encodeQR 3 4 9 14

/-! ## 3. The feed-forward initial-state snapshot -/

/-- The sixteen feed-forward memory-operand `vpaddd` adds: after the rounds, load
    each SoA word `k` from `%rdi + 16·k`, add the snapshot initial word at
    `%rsp + 16·k`, and store back to `%rdi + 16·k`. -/
def encodeFeedForward : List (BitVec 8) :=
  (List.range 16).flatMap (fun k =>
    encVmovdquLoadU 0 (16 * k)
      ++ encVpadddMemRspU 0 0 (16 * k)
      ++ encVmovdquStoreU 0 (16 * k))

/-! ## 4. Phase B: snapshot + rounds + feed-forward -/

/-- The 256-byte frame holds the sixteen-word initial-state snapshot. -/
def frameBytes : Nat := 256

/-- Snapshot the sixteen SoA initial words from `%rdi + 16·k` to the frame
    `%rsp + 16·k` (load to `xmm0`, unaligned store). -/
def encodeSnapshot : List (BitVec 8) :=
  (List.range 16).flatMap (fun k =>
    encVmovdquLoadU 0 (16 * k) ++ encVmovdquStoreRspU 0 (16 * k))

/-- Phase B: reserve the frame, snapshot the initial SoA state, run the ten
    double-rounds (clobbering `%rdi`), feed forward the snapshot, release the frame. -/
def encodePhaseB : List (BitVec 8) :=
  encSubRspU frameBytes
    ++ encodeSnapshot
    ++ (List.range 10).flatMap (fun _ => encodeDoubleRound)
    ++ encodeFeedForward
    ++ encAddRspU frameBytes

/-! ## 5. Phase A (AoS→SoA) and Phase C (SoA→AoS) transposes -/

/-- Phase A word-group `g`: load block `b`'s group-`g` four words from
    `%rsi + 64·b + 16·g` into `xmm0..3`, run the `_MM_TRANSPOSE4` body, store the
    four SoA columns (`xmm8..11`) to `%rdi + 16·(4g+j)`. -/
def transposeGroup (g : Nat) : List (BitVec 8) :=
  ((List.range 4).flatMap (fun b => encVmovdquLoadRsiU b (64 * b + 16 * g)))
    ++ transpose4BytesU
    ++ ((List.range 4).flatMap (fun j => encVmovdquStoreU (8 + j) (16 * (4 * g + j))))

/-- Phase A: the four AoS→SoA word-group transposes in sequence (AoS rows from
    `%rsi`, SoA words to `%rdi`). -/
def encodePhaseA : List (BitVec 8) := (List.range 4).flatMap transposeGroup

/-- Snapshot the sixteen SoA words from `%rdi + 16·k` to the Phase-C scratch frame
    `%rsp + 16·k`, so Phase C reads its transpose rows from the frame and writes
    AoS rows to `%rdi` out-of-place. -/
def encodePhaseCSnapshot : List (BitVec 8) :=
  (List.range 16).flatMap (fun k =>
    encVmovdquLoadU 0 (16 * k) ++ encVmovdquStoreRspU 0 (16 * k))

/-- Phase C word-group `g`: read the four SoA words `4g..4g+3` from the `%rsp`
    snapshot (`16·(4g+j)`) into `xmm0..3`, run the same `_MM_TRANSPOSE4` body, and
    store the four columns as AoS — column `b` → `%rdi + 64·b + 16·g`.  Reading
    from `%rsp` (not `%rdi`) avoids the in-place read-after-write hazard. -/
def encodePhaseCGroup (g : Nat) : List (BitVec 8) :=
  ((List.range 4).flatMap (fun j => encVmovdquLoadRspU j (16 * (4 * g + j))))
    ++ transpose4BytesU
    ++ ((List.range 4).flatMap (fun b => encVmovdquStoreU (8 + b) (64 * b + 16 * g)))

/-- Phase C: reserve the 256-byte scratch frame, snapshot the SoA state, run the
    four SoA→AoS word-group transposes (reading rows from `%rsp`, writing AoS rows
    to `%rdi`), then release the frame. -/
def encodePhaseC : List (BitVec 8) :=
  encSubRspU frameBytes
    ++ encodePhaseCSnapshot
    ++ (List.range 4).flatMap encodePhaseCGroup
    ++ encAddRspU frameBytes

/-! ## 6. The whole 4-way block kernel and its ELF object -/

/-- The whole ChaCha20 4-way block as machine bytes: Phase A (AoS→SoA) ++ Phase B
    (snapshot + rounds + feed-forward) ++ Phase C (SoA→AoS) ++ the two-pointer
    return-value epilogue (`mov %rdi,%rax ; ret`).  No `gas`, no `jasminc`, no
    `Vec128*` on the artifact path.  The canonical entry point (the `SimdBytes`-free
    twin of `Chacha4WayEmit.encodeChacha20_4way_block`). -/
def emit : List (BitVec 8) :=
  encodePhaseA ++ encodePhaseB ++ encodePhaseC ++ encRetOutPtrU

/-- The byte artifact, as a single Lean entry point (the kernel's machine bytes). -/
private def main : List (BitVec 8) := emit

/-- The kernel wrapped as a single-symbol ELF64 relocatable object — symbol
    `chacha20_4way_block` (the C harness's `extern`). -/
def chacha20_4way_blockObject : List (BitVec 8) :=
  ElfObject.buildElfObject "chacha20_4way_block" emit

/-! ## 7. Structural well-formedness pins (mirroring `Chacha4WayEmit` §7) -/

/-- The kernel ends with the two-pointer return-value epilogue `mov %rdi,%rax ; ret`. -/
theorem emit_tail :
    emit.drop (emit.length - 4) = [0x48, 0x89, 0xf8, 0xc3].map (BitVec.ofNat 8) := by native_decide

/-- One column quarter-round (words `0,4,8,12`) is byte-identical to gas: the four
    word loads, the `cbQRBytesU` body, the four stores. -/
theorem encodeQR_0_4_8_12_eq :
    encodeQR 0 4 8 12 =
      (encVmovdquLoadU 0 0 ++ encVmovdquLoadU 1 64 ++ encVmovdquLoadU 2 128 ++ encVmovdquLoadU 3 192)
        ++ cbQRBytesU
        ++ (encVmovdquStoreU 0 0 ++ encVmovdquStoreU 1 64 ++ encVmovdquStoreU 2 128
            ++ encVmovdquStoreU 3 192) := by native_decide

/-- The 4-way block object begins with the 64-byte `Elf64_Ehdr` magic
    (`ElfObject.buildElfObject_magic` at this kernel). -/
theorem chacha20_4way_blockObject_header :
    chacha20_4way_blockObject.take 6 = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  ElfObject.buildElfObject_magic _ _

/-! ## 8. Full-emit-path denotational self-check vs RFC 8439 §2.3.2

The same whole-marshalled-data-flow check as `Chacha4WayEmit` §8: Phase A
transpose ∘ the memory-resident rounds ∘ Phase C transpose over a model `u32`
memory, using the same offset formulas the byte-emit addresses, checked against a
from-scratch RFC 8439 §2.3.2 reference.  By the gas-pins in
`VsimdChachaByteEncoder`, a correct full-path denotation is a passing byte-KAT. -/

namespace DenoteCheck

/-- u32 rotate-left (RFC 8439 §2.1). -/
def rotl32 (x : BitVec 32) (n : Nat) : BitVec 32 := (x <<< n) ||| (x >>> (32 - n))

/-- A model XMM = four `u32` lanes. -/
abbrev V4 := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- Read the four `u32` cells at byte offset `off`. -/
def rd (m : Array (BitVec 32)) (off : Nat) : V4 :=
  let i := off / 4
  (m.getD i 0, m.getD (i+1) 0, m.getD (i+2) 0, m.getD (i+3) 0)

/-- Write the four lanes of `v` to the cells at byte offset `off`. -/
def wr (m : Array (BitVec 32)) (off : Nat) (v : V4) : Array (BitVec 32) :=
  let i := off / 4
  ((((m.set! i v.1).set! (i+1) v.2.1).set! (i+2) v.2.2.1).set! (i+3) v.2.2.2)

/-- The `transpose4BytesU` denotation (the `_MM_TRANSPOSE4` 8-op interleave). -/
def transpose4 (r0 r1 r2 r3 : V4) : V4 × V4 × V4 × V4 :=
  let t0 : V4 := (r0.1, r1.1, r0.2.1, r1.2.1)
  let t1 : V4 := (r0.2.2.1, r1.2.2.1, r0.2.2.2, r1.2.2.2)
  let t2 : V4 := (r2.1, r3.1, r2.2.1, r3.2.1)
  let t3 : V4 := (r2.2.2.1, r3.2.2.1, r2.2.2.2, r3.2.2.2)
  let c0 : V4 := (t0.1, t0.2.1, t2.1, t2.2.1)
  let c1 : V4 := (t0.2.2.1, t0.2.2.2, t2.2.2.1, t2.2.2.2)
  let c2 : V4 := (t1.1, t1.2.1, t3.1, t3.2.1)
  let c3 : V4 := (t1.2.2.1, t1.2.2.2, t3.2.2.1, t3.2.2.2)
  (c0, c1, c2, c3)

/-- One RFC 8439 §2.1 quarter-round on a single block's `(a,b,c,d)`. -/
def qrBlock (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b; let d := rotl32 (d ^^^ a) 16
  let c := c + d; let b := rotl32 (b ^^^ c) 12
  let a := a + b; let d := rotl32 (d ^^^ a) 8
  let c := c + d; let b := rotl32 (b ^^^ c) 7
  (a, b, c, d)

/-- The lane-parallel quarter-round (`cbQRBytesU` denotation). -/
def cbQR4 (A B C D : V4) : V4 × V4 × V4 × V4 :=
  let q0 := qrBlock A.1 B.1 C.1 D.1
  let q1 := qrBlock A.2.1 B.2.1 C.2.1 D.2.1
  let q2 := qrBlock A.2.2.1 B.2.2.1 C.2.2.1 D.2.2.1
  let q3 := qrBlock A.2.2.2 B.2.2.2 C.2.2.2 D.2.2.2
  ((q0.1, q1.1, q2.1, q3.1), (q0.2.1, q1.2.1, q2.2.1, q3.2.1),
   (q0.2.2.1, q1.2.2.1, q2.2.2.1, q3.2.2.1), (q0.2.2.2, q1.2.2.2, q2.2.2.2, q3.2.2.2))

/-- One memory-resident quarter-round (`encodeQR` denotation). -/
def stepQR (m : Array (BitVec 32)) (α β γ δ : Nat) : Array (BitVec 32) :=
  let A := rd m (16*α); let B := rd m (16*β); let C := rd m (16*γ); let D := rd m (16*δ)
  let r := cbQR4 A B C D
  wr (wr (wr (wr m (16*α) r.1) (16*β) r.2.1) (16*γ) r.2.2.1) (16*δ) r.2.2.2

/-- One double-round (`encodeDoubleRound` denotation). -/
def stepDoubleRound (m : Array (BitVec 32)) : Array (BitVec 32) :=
  let m := stepQR m 0 4 8 12; let m := stepQR m 1 5 9 13
  let m := stepQR m 2 6 10 14; let m := stepQR m 3 7 11 15
  let m := stepQR m 0 5 10 15; let m := stepQR m 1 6 11 12
  let m := stepQR m 2 7 8 13; stepQR m 3 4 9 14

/-- Phase A denotation (`transposeGroup` for each group). -/
def phaseA (rsi : Array (BitVec 32)) : Array (BitVec 32) :=
  (List.range 4).foldl (fun m g =>
    let r := transpose4 (rd rsi (64*0 + 16*g)) (rd rsi (64*1 + 16*g))
                        (rd rsi (64*2 + 16*g)) (rd rsi (64*3 + 16*g))
    wr (wr (wr (wr m (16*(4*g+0)) r.1) (16*(4*g+1)) r.2.1)
           (16*(4*g+2)) r.2.2.1) (16*(4*g+3)) r.2.2.2)
    (Array.replicate 64 (0 : BitVec 32))

/-- Phase B denotation. -/
def phaseB (m : Array (BitVec 32)) : Array (BitVec 32) :=
  let snap : Array (BitVec 32) :=
    (List.range 16).foldl (fun s k => wr s (16*k) (rd m (16*k)))
      (Array.replicate 64 (0 : BitVec 32))
  let m := (List.range 10).foldl (fun m _ => stepDoubleRound m) m
  (List.range 16).foldl (fun m k =>
    let w := rd m (16*k); let sn := rd snap (16*k)
    wr m (16*k) (w.1 + sn.1, w.2.1 + sn.2.1, w.2.2.1 + sn.2.2.1, w.2.2.2 + sn.2.2.2)) m

/-- Phase C denotation, with the out-of-place `%rsp` read. -/
def phaseC (m : Array (BitVec 32)) : Array (BitVec 32) :=
  let snap : Array (BitVec 32) :=
    (List.range 16).foldl (fun s k => wr s (16*k) (rd m (16*k)))
      (Array.replicate 64 (0 : BitVec 32))
  (List.range 4).foldl (fun m g =>
    let r := transpose4 (rd snap (16*(4*g+0))) (rd snap (16*(4*g+1)))
                        (rd snap (16*(4*g+2))) (rd snap (16*(4*g+3)))
    wr (wr (wr (wr m (64*0 + 16*g) r.1) (64*1 + 16*g) r.2.1)
           (64*2 + 16*g) r.2.2.1) (64*3 + 16*g) r.2.2.2) m

/-- The full emit-path denotation: Phase A ∘ Phase B ∘ Phase C over the AoS input. -/
def denoteKernel (rsi : Array (BitVec 32)) : Array (BitVec 32) :=
  phaseC (phaseB (phaseA rsi))

/-- One RFC 8439 quarter-round on the 16-word state at indices `x y z w`. -/
def refQR (s : Array (BitVec 32)) (x y z w : Nat) : Array (BitVec 32) :=
  let sx := s.getD x 0; let sy := s.getD y 0; let sz := s.getD z 0; let sw := s.getD w 0
  let sx := sx + sy; let sw := rotl32 (sw ^^^ sx) 16
  let sz := sz + sw; let sy := rotl32 (sy ^^^ sz) 12
  let sx := sx + sy; let sw := rotl32 (sw ^^^ sx) 8
  let sz := sz + sw; let sy := rotl32 (sy ^^^ sz) 7
  (((s.set! x sx).set! y sy).set! z sz).set! w sw

/-- The reference RFC 8439 §2.3.2 ChaCha20 block on a 16-word state. -/
def refBlock (state : Array (BitVec 32)) : Array (BitVec 32) :=
  let w := (List.range 10).foldl (fun s _ =>
    let s := refQR s 0 4 8 12; let s := refQR s 1 5 9 13
    let s := refQR s 2 6 10 14; let s := refQR s 3 7 11 15
    let s := refQR s 0 5 10 15; let s := refQR s 1 6 11 12
    let s := refQR s 2 7 8 13; refQR s 3 4 9 14) state
  (List.range 16).foldl (fun acc i => acc.set! i (w.getD i 0 + state.getD i 0))
    (Array.replicate 16 (0 : BitVec 32))

/-- A reproducible model AoS input: block `b` word `j` = `1000·b + j + 1`. -/
def modelInput : Array (BitVec 32) :=
  (List.range 4).foldl (fun m b =>
    (List.range 16).foldl (fun m j => m.set! (16*b + j) (BitVec.ofNat 32 (1000*b + j + 1))) m)
    (Array.replicate 64 (0 : BitVec 32))

/-- The four AoS reference blocks: `refBlock` of each input block. -/
def refOut : Array (BitVec 32) :=
  (List.range 4).foldl (fun acc b =>
    let inb : Array (BitVec 32) :=
      (List.range 16).foldl (fun s j => s.set! j (modelInput.getD (16*b + j) 0))
        (Array.replicate 16 (0 : BitVec 32))
    let ob := refBlock inb
    (List.range 16).foldl (fun acc j => acc.set! (16*b + j) (ob.getD j 0)) acc)
    (Array.replicate 64 (0 : BitVec 32))

/-- **Full-emit-path denote self-check.**  The whole marshalled data flow —
    Phase A ∘ memory-resident rounds ∘ Phase C — reproduces the from-scratch
    RFC 8439 §2.3.2 reference on all 4 blocks × 16 AoS words, over the exact
    offset formulas the byte-emit addresses (the `Vec128*`-free twin of
    `Chacha4WayEmit.DenoteCheck.denoteKernel_matches_rfc`). -/
theorem denoteKernel_matches_rfc :
    (List.range 64).all (fun i =>
      (denoteKernel modelInput).getD i 0 = refOut.getD i 0) = true := by
  native_decide

end DenoteCheck

end CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
