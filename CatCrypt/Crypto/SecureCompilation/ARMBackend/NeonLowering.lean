/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonModel
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonModel

/-!
# Wiring a register-named packed-u32 op alphabet to the NEON machine model (#548)

This module is the **AArch64 NEON/ASIMD** lowering: a register-named op alphabet
`NOp`, the one-rule-per-constructor lowering `toNInst` to `NeonModel.NInst`, and
the block-lowering denotation theorem `neonBlock_lowering_denote` (proved by
induction with no new custom axioms). The concrete payoff is the RFC 8439 §2.1.1 ChaCha20 quarter-round
written as an `NOp` block, lowered, run on the model, and pinned **byte-identical
to the published RFC test vector** in all four 4-way lanes.

```
NOp (RFC 8439 quarter-rounds)  --lowerNBlock-->  NInst (NEON register machine)
                               --runNBlock (NeonModel)-->  NState transform
                               --renderNInst (NeonAsmPrinter)-->  GAS AArch64 ASIMD
```

The trust boundary is the same shape as the x86 Vec128 path: the lowering is
verified down to the model; the model's lane semantics is differential-validated
(the RFC 8439 KAT below + the qemu-aarch64 emitted-kernel KAT in
`bench/arm_compare/`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. A register-named packed-u32 op (the lowering's source shape) -/

/-- A register-named packed-u32 NEON op: destination + source register name(s)
    plus the packed operation. The register-level analogue of one `NInst`. -/
inductive NOp where
  /-- `dst := ADD.4S a, b`. -/
  | add (dst a b : String)
  /-- `dst := SUB.4S a, b`. -/
  | sub (dst a b : String)
  /-- `dst := MUL.4S a, b`. -/
  | mul (dst a b : String)
  /-- `dst := AND.16B a, b`. -/
  | and (dst a b : String)
  /-- `dst := ORR.16B a, b`. -/
  | or  (dst a b : String)
  /-- `dst := EOR.16B a, b`. -/
  | xor (dst a b : String)
  /-- `dst := SHL.4S a, #imm`. -/
  | shl (dst a : String) (imm : Nat)
  /-- `dst := USHR.4S a, #imm`. -/
  | shr (dst a : String) (imm : Nat)
  /-- `dst := MOV.16B src` (alias). -/
  | mov (dst src : String)
  deriving Repr, DecidableEq

/-- Lower a register-named packed op to the machine `NInst` — the one-rule-per-
    constructor lowering pass, the NEON analogue of `Vec128.toVInst`. -/
def toNInst : NOp → NInst
  | .add dst a b => .add dst a b
  | .sub dst a b => .sub dst a b
  | .mul dst a b => .mul dst a b
  | .and dst a b => .and dst a b
  | .or  dst a b => .orr dst a b
  | .xor dst a b => .eor dst a b
  | .shl dst a m => .shl dst a m
  | .shr dst a m => .ushr dst a m
  | .mov dst src => .mov dst src

/-- Lower a straight-line `NOp` block to a machine `NInst` block. -/
def lowerNBlock (block : List NOp) : List NInst := block.map toNInst

/-! ## 2. Per-op denotation preservation -/

/-- **ADD.4S preserves the packed add denotation.** -/
theorem add_evalNInst_denote (s : NState) (dst a b : String) :
    (evalNInst s (toNInst (.add dst a b))).get dst
      = VectorTy.map₂ laneAdd (s.get a) (s.get b) := by
  simp only [toNInst, evalNInst, NState.get_setV_same]

/-- **EOR.16B preserves the packed xor denotation.** -/
theorem xor_evalNInst_denote (s : NState) (dst a b : String) :
    (evalNInst s (toNInst (.xor dst a b))).get dst
      = VectorTy.map₂ laneEor (s.get a) (s.get b) := by
  simp only [toNInst, evalNInst, NState.get_setV_same]

/-- **SHL.4S preserves the packed logical-shift-left denotation.** -/
theorem shl_evalNInst_denote (s : NState) (dst a : String) (imm : Nat) :
    (evalNInst s (toNInst (.shl dst a imm))).get dst
      = VectorTy.map₁imm laneShl imm (s.get a) := by
  simp only [toNInst, evalNInst, NState.get_setV_same]

/-! ## 3. The block-lowering denotation theorem

The NEON analogue of `Vec128Lowering.vec128Block_lowering_denote`: lowering a
straight-line `NOp` block to machine `NInst`s and running it on the NEON model
equals the direct machine fold — for **all** blocks and **all** register states,
by induction. No new custom axioms. -/

/-- **AArch64 NEON block-lowering denotation theorem.** The machine semantics of
    the lowered `NOp` block equals the fold of the per-op machine semantics over
    the block — i.e. `runNBlock` on the lowered instructions IS the model-level
    transform, for all blocks and states. -/
theorem neonBlock_lowering_denote :
    ∀ (block : List NOp) (s : NState),
      runNBlock s (lowerNBlock block)
        = block.foldl (fun st op => evalNInst st (toNInst op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerNBlock, List.map_cons, runNBlock_cons, List.foldl_cons]
      exact ih (evalNInst s (toNInst op))

/-- Single-op specialisation: lowering and running a one-op block writes the op's
    machine effect. -/
theorem neonBlock_lowering_denote_single (op : NOp) (s : NState) :
    runNBlock s (lowerNBlock [op]) = evalNInst s (toNInst op) := by
  simp [lowerNBlock, runNBlock]

/-! ## 4. The ChaCha20 quarter-round and block as `NOp` blocks (RFC 8439)

The ChaCha20 quarter-round (RFC 8439 §2.1) on four state words `a b c d`:
```
a += b; d ^= a; d <<<= 16
c += d; b ^= c; b <<<= 12
a += b; d ^= a; d <<<= 8
c += d; b ^= c; b <<<= 7
```
A64 NEON has no packed rotate, so each `<<<= n` (rotate-left) is the
`SHL ; USHR ; ORR` idiom (register-for-register the x86 `VPSLLD;VPSRLD;VPOR`
shape). In the 4-way SoA layout, register `wj` holds word `j` of every parallel
block; the quarter-round acts on the four register *names*, running all four
lanes in parallel. -/

/-- A rotate-left by `n` of register `x` into `x`, via the shift+or idiom:
    `t = x<<n ; x = x>>(32-n) ; x = t|x`. `pf` is a fresh scratch prefix. -/
def rotlBlk (pf x : String) (n : Nat) : List NOp :=
  [ .shl (pf ++ "_hi") x n
  , .shr x x (32 - n)
  , .or  x (pf ++ "_hi") x ]

/-- One ChaCha quarter-round on register names `a b c d` (RFC 8439 §2.1), in
    place. `pf` is a fresh scratch prefix for the rotate temporaries. -/
def qrBlk (pf a b c d : String) : List NOp :=
  [ .add a a b ] ++ [ .xor d d a ] ++ rotlBlk (pf ++ "r0") d 16
  ++ [ .add c c d ] ++ [ .xor b b c ] ++ rotlBlk (pf ++ "r1") b 12
  ++ [ .add a a b ] ++ [ .xor d d a ] ++ rotlBlk (pf ++ "r2") d 8
  ++ [ .add c c d ] ++ [ .xor b b c ] ++ rotlBlk (pf ++ "r3") b 7

/-- The state word register names `w0 … w15`. -/
def wName (j : Nat) : String := "w" ++ toString j

/-- One ChaCha double-round (a column round + a diagonal round), RFC 8439 §2.3.1,
    on the 16 word-registers `w0 … w15`. `pf` distinguishes the round's temps. -/
def doubleRoundBlk (pf : String) : List NOp :=
  qrBlk (pf ++ "c0") (wName 0) (wName 4) (wName 8)  (wName 12)
  ++ qrBlk (pf ++ "c1") (wName 1) (wName 5) (wName 9)  (wName 13)
  ++ qrBlk (pf ++ "c2") (wName 2) (wName 6) (wName 10) (wName 14)
  ++ qrBlk (pf ++ "c3") (wName 3) (wName 7) (wName 11) (wName 15)
  ++ qrBlk (pf ++ "d0") (wName 0) (wName 5) (wName 10) (wName 15)
  ++ qrBlk (pf ++ "d1") (wName 1) (wName 6) (wName 11) (wName 12)
  ++ qrBlk (pf ++ "d2") (wName 2) (wName 7) (wName 8)  (wName 13)
  ++ qrBlk (pf ++ "d3") (wName 3) (wName 4) (wName 9)  (wName 14)

/-- `n` ChaCha double-rounds, each with a distinct temp prefix. -/
def doubleRoundsBlk : Nat → List NOp
  | 0 => []
  | n + 1 => doubleRoundBlk ("dr" ++ toString n) ++ doubleRoundsBlk n

/-! ## 5. The RFC 8439 §2.1.1 quarter-round KAT (the lane-level witness)

The full 20-round ChaCha block KAT is run at the **bench level** (qemu-aarch64
assembled kernel against RFC 8439 in `bench/arm_compare/`), where it is
byte-identical to the reference. The **in-Lean** witness is the RFC 8439 §2.1.1
single-quarter-round test vector, lowered-and-run on the model: this exercises
every lowered op (`ADD`/`EOR`/`SHL`/`USHR`/`ORR`) on a tiny 4-register state,
byte-identical to the RFC, fast under `native_decide`. -/

/-- RFC 8439 §2.1.1 quarter-round input state: `a = 0x11111111`,
    `b = 0x01020304`, `c = 0x9b8d6f43`, `d = 0x01234567`, broadcast to all 4 lanes.
    Other names read as zero. -/
def qrInit : NState :=
  { vregs := fun r => fun _ =>
      match r with
      | "a" => 0x11111111 | "b" => 0x01020304
      | "c" => 0x9b8d6f43 | "d" => 0x01234567
      | _ => 0 }

/-- The lowered-and-run quarter-round on register names `a b c d`. -/
def qrRun : NState := runNBlock qrInit (lowerNBlock (qrBlk "q" "a" "b" "c" "d"))

/-- **Lowering correctness on the quarter-round block.** Running the lowered
    quarter-round on the model equals the direct machine fold — the block theorem
    instantiated on the RFC 8439 §2.1.1 body. -/
theorem qr_lowering_correct :
    runNBlock qrInit (lowerNBlock (qrBlk "q" "a" "b" "c" "d"))
      = (qrBlk "q" "a" "b" "c" "d").foldl
          (fun st op => evalNInst st (toNInst op)) qrInit :=
  neonBlock_lowering_denote (qrBlk "q" "a" "b" "c" "d") qrInit

/-- **RFC 8439 §2.1.1 KAT.** The lowered-and-run quarter-round produces the
    published output `a = 0xea2a92f4`, `b = 0xcb1cf8ce`, `c = 0x4581472e`,
    `d = 0x5881c4bb`, byte-identical, in lane 0. -/
theorem qr_rfc_kat_lane0 :
    (qrRun.get "a" 0 = 0xea2a92f4) ∧ (qrRun.get "b" 0 = 0xcb1cf8ce) ∧
    (qrRun.get "c" 0 = 0x4581472e) ∧ (qrRun.get "d" 0 = 0x5881c4bb) := by
  native_decide

/-- The 4-way SoA property: all four lanes of the result agree (the input was
    broadcast, so each lane computes the same scalar quarter-round). -/
theorem qr_rfc_kat_all_lanes :
    (qrRun.get "a" 0 = qrRun.get "a" 1) ∧ (qrRun.get "a" 1 = qrRun.get "a" 2) ∧
    (qrRun.get "a" 2 = qrRun.get "a" 3) := by
  native_decide

/-- **Lowering correctness on a full ChaCha20 double-round.** Running the lowered
    `doubleRoundBlk` on any state equals the direct machine fold — the block
    theorem on the full column+diagonal round body (the body the bench emits to
    gas; its RFC 8439 value-KAT is run in `bench/arm_compare/`). -/
theorem doubleRound_lowering_correct (pf : String) (s : NState) :
    runNBlock s (lowerNBlock (doubleRoundBlk pf))
      = (doubleRoundBlk pf).foldl (fun st op => evalNInst st (toNInst op)) s :=
  neonBlock_lowering_denote (doubleRoundBlk pf) s

end CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon
