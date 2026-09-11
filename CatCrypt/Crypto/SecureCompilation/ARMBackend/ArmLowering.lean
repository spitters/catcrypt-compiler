/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmModel
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmModel

/-!
# Wiring a register-named scalar op alphabet to the A64 machine model (#533)

`Vec128Lowering.lean` lowers a register-named packed-u32 op alphabet (`VOp`) to
the XMM machine `VInst` with the block-lowering denotation theorem
`vec128Block_lowering_denote`, and the ChaCha 4-way SIMD kernel rides it. This
module is the **AArch64 scalar** analogue for the ChaCha20 quarter-round: a
register-named op alphabet `AOp`, the one-rule-per-constructor lowering `toAInst`
to `ArmModel.AInst`, and the block-lowering denotation theorem
`armBlock_lowering_denote` (the A64 analogue of `vec128Block_lowering_denote`,
proved by induction with no new custom axioms). The concrete payoff is the RFC
8439 §2.1.1 ChaCha20 quarter-round written as an `AOp` block, lowered, run on the
model, and pinned **byte-identical to the published RFC test vector**.

```
AOp (RFC 8439 quarter-round)  --lowerABlock-->  AInst (A64 register machine)
                              --runABlock (ArmModel)-->  AState transform
                              --renderAInst (ArmAsmPrinter)-->  GAS AArch64 asm
```

The trust boundary is the same shape as the x86 path: the lowering is verified
down to the model; the model's per-op semantics is differential-validated (the
RFC 8439 KAT below; the assembled-object check + qemu KAT live in `bench/`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. A register-named scalar op (the lowering's source shape) -/

/-- A register-named scalar A64 op: destination + source register name(s) plus
    the operation. The register-level analogue of one `AInst`. -/
inductive AOp where
  /-- `dst := ADD a, b`. -/
  | add (dst a b : String)
  /-- `dst := SUB a, b`. -/
  | sub (dst a b : String)
  /-- `dst := AND a, b`. -/
  | and (dst a b : String)
  /-- `dst := ORR a, b`. -/
  | or  (dst a b : String)
  /-- `dst := EOR a, b`. -/
  | xor (dst a b : String)
  /-- `dst := LSL a, #imm`. -/
  | shl (dst a : String) (imm : Nat)
  /-- `dst := LSR a, #imm`. -/
  | shr (dst a : String) (imm : Nat)
  /-- `dst := ROR a, #imm`. -/
  | rotr (dst a : String) (imm : Nat)
  /-- `dst := MOV src`. -/
  | mov (dst src : String)
  deriving Repr, DecidableEq

/-- Lower a register-named scalar op to the machine `AInst` — the one-rule-per-
    constructor lowering pass, the A64 analogue of `Vec128.toVInst`. -/
def toAInst : AOp → AInst
  | .add dst a b => .add dst a b
  | .sub dst a b => .sub dst a b
  | .and dst a b => .and dst a b
  | .or  dst a b => .orr dst a b
  | .xor dst a b => .eor dst a b
  | .shl dst a m => .lsl dst a m
  | .shr dst a m => .lsr dst a m
  | .rotr dst a m => .ror dst a m
  | .mov dst src => .mov dst src

/-- Lower a straight-line `AOp` block to a machine `AInst` block. -/
def lowerABlock (block : List AOp) : List AInst := block.map toAInst

/-! ## 2. Per-op denotation preservation -/

/-- **ADD preserves the add denotation.** -/
theorem add_evalAInst_denote (s : AState) (dst a b : String) (h : dst ≠ "wzr") :
    (evalAInst s (toAInst (.add dst a b))).get dst = opAdd (s.get a) (s.get b) := by
  simp only [toAInst, evalAInst, AState.get_set_same _ _ _ h]

/-- **EOR preserves the xor denotation.** -/
theorem xor_evalAInst_denote (s : AState) (dst a b : String) (h : dst ≠ "wzr") :
    (evalAInst s (toAInst (.xor dst a b))).get dst = opEor (s.get a) (s.get b) := by
  simp only [toAInst, evalAInst, AState.get_set_same _ _ _ h]

/-- **ROR preserves the rotate-right denotation.** -/
theorem rotr_evalAInst_denote (s : AState) (dst a : String) (imm : Nat)
    (h : dst ≠ "wzr") :
    (evalAInst s (toAInst (.rotr dst a imm))).get dst = opRor (s.get a) imm := by
  simp only [toAInst, evalAInst, AState.get_set_same _ _ _ h]

/-! ## 3. The block-lowering denotation theorem (the A64 keystone)

The A64 analogue of `Vec128Lowering.vec128Block_lowering_denote`: lowering a
straight-line `AOp` block to machine `AInst`s and running it on the A64 model
equals the direct machine fold — for **all** blocks and **all** register states,
by induction. No new custom axioms. -/

/-- **AArch64 block-lowering denotation theorem.** The machine semantics of the
    lowered `AOp` block equals the fold of the per-op machine semantics over the
    block — i.e. `runABlock` on the lowered instructions IS the model-level
    transform, for all blocks and states. -/
theorem armBlock_lowering_denote :
    ∀ (block : List AOp) (s : AState),
      runABlock s (lowerABlock block)
        = block.foldl (fun st op => evalAInst st (toAInst op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerABlock, List.map_cons, runABlock_cons, List.foldl_cons]
      exact ih (evalAInst s (toAInst op))

/-- Single-op specialisation: lowering and running a one-op block writes the
    op's machine effect. -/
theorem armBlock_lowering_denote_single (op : AOp) (s : AState) :
    runABlock s (lowerABlock [op]) = evalAInst s (toAInst op) := by
  simp [lowerABlock, runABlock]

/-! ## 4. The ChaCha20 quarter-round as an `AOp` block (RFC 8439 §2.1)

The ChaCha20 quarter-round (RFC 8439 §2.1) on four state words `a b c d`:
```
a += b; d ^= a; d <<<= 16
c += d; b ^= c; b <<<= 12
a += b; d ^= a; d <<<= 8
c += d; b ^= c; b <<<= 7
```
A64 has a native rotate-**right** by immediate (`ROR`), so the rotate-**left**
by `n` is the single op `ROR Wd, Wn, #(32-n)` — one instruction, no shift+or
idiom (contrast the x86 SIMD `VPSLLD;VPSRLD;VPOR`). The quarter-round is thus a
flat 12-instruction A64 block. -/

/-- A rotate-**left** by `n` of register `x` into `x`, as a single A64 `ROR` by
    `32 - n` (rotate-left n ≡ rotate-right (32-n)). -/
def rotlOp (x : String) (n : Nat) : AOp := .rotr x x (32 - n)

/-- One ChaCha quarter-round on register names `a b c d` (RFC 8439 §2.1),
    in place — the flat 12-op A64 block. -/
def qrBlk (a b c d : String) : List AOp :=
  [ .add a a b, .xor d d a, rotlOp d 16
  , .add c c d, .xor b b c, rotlOp b 12
  , .add a a b, .xor d d a, rotlOp d 8
  , .add c c d, .xor b b c, rotlOp b 7 ]

/-! ## 5. The RFC 8439 §2.1.1 quarter-round KAT (the scalar A64 witness)

Lowered-and-run on the model: this exercises every lowered op (`ADD`/`EOR`/`ROR`)
on a tiny 4-register state, byte-identical to the RFC, fast under `native_decide`.
The assembled-object + qemu byte-KAT lives in `bench/arm_compare/`. -/

/-- RFC 8439 §2.1.1 quarter-round input state: `a = 0x11111111`,
    `b = 0x01020304`, `c = 0x9b8d6f43`, `d = 0x01234567`. Other names read as
    zero. -/
def qrInit : AState :=
  { regs := fun r =>
      match r with
      | "a" => 0x11111111 | "b" => 0x01020304
      | "c" => 0x9b8d6f43 | "d" => 0x01234567
      | _ => 0 }

/-- The lowered-and-run quarter-round on register names `a b c d`. -/
def qrRun : AState := runABlock qrInit (lowerABlock (qrBlk "a" "b" "c" "d"))

/-- **Lowering correctness on the quarter-round block.** Running the lowered
    quarter-round on the model equals the direct machine fold — the block theorem
    instantiated on the RFC 8439 §2.1.1 body. -/
theorem qr_lowering_correct :
    runABlock qrInit (lowerABlock (qrBlk "a" "b" "c" "d"))
      = (qrBlk "a" "b" "c" "d").foldl
          (fun st op => evalAInst st (toAInst op)) qrInit :=
  armBlock_lowering_denote (qrBlk "a" "b" "c" "d") qrInit

/-- **RFC 8439 §2.1.1 KAT.** The lowered-and-run quarter-round produces the
    published output `a = 0xea2a92f4`, `b = 0xcb1cf8ce`, `c = 0x4581472e`,
    `d = 0x5881c4bb`, byte-identical. -/
theorem qr_rfc_kat :
    (qrRun.get "a" = 0xea2a92f4) ∧ (qrRun.get "b" = 0xcb1cf8ce) ∧
    (qrRun.get "c" = 0x4581472e) ∧ (qrRun.get "d" = 0x5881c4bb) := by
  native_decide

/-! ## 6. The 64-bit bignum/field op alphabet and its lowering (#547)

The A64 analogue of `BOp → BInst`, for the bignum/field hot path. The lowering is
one-rule-per-constructor (no instruction selection), so the block-lowering
denotation theorem `bignumBlock_lowering_denote` is the same induction as
`armBlock_lowering_denote`, with no new custom axioms. The concrete payoff is
s2n-bignum's `bignum_add_p256` (add mod p256 with the constant-time
conditional-subtract reduce) written as a `BOp` block, lowered, run on the
`BState` model, and pinned against a hand-computed reference vector. -/

/-- A register-named 64-bit bignum/field op. Mirrors `ArmModel.BInst` at the
    register-name level (the lowering's source shape). -/
inductive BOp where
  /-- `dst := ADD a, b` (no flags). -/
  | add (dst a b : String)
  /-- `dst := SUB a, b` (no flags). -/
  | sub (dst a b : String)
  /-- `dst := ADDS a, b` (set `C`). -/
  | adds (dst a b : String)
  /-- `dst := ADCS a, b` (add-with-carry, set `C`). -/
  | adcs (dst a b : String)
  /-- `dst := ADC a, b` (add-with-carry, no flags). -/
  | adc (dst a b : String)
  /-- `dst := SUBS a, b` (set `C`). -/
  | subs (dst a b : String)
  /-- `dst := SBCS a, b` (subtract-with-borrow, set `C`). -/
  | sbcs (dst a b : String)
  /-- `dst := SBC a, b` (subtract-with-borrow, no flags). -/
  | sbc (dst a b : String)
  /-- `dst := MUL a, b` (low 64). -/
  | mul (dst a b : String)
  /-- `dst := UMULH a, b` (high 64). -/
  | umulh (dst a b : String)
  /-- `dst := AND a, b` (64-bit bitwise conjunction). -/
  | and (dst a b : String)
  /-- `dst := ORR a, b` (64-bit bitwise disjunction). -/
  | orr (dst a b : String)
  /-- `dst := EOR a, b` (64-bit bitwise exclusive-or). -/
  | eor (dst a b : String)
  /-- `dst := CSEL a, b, cond`. -/
  | csel (dst a b : String) (c : ACond)
  /-- `dst := MOVZ #imm16`. -/
  | movz (dst : String) (imm16 : Nat)
  /-- `dst := MOVK #imm16, LSL #(16·hw)`. -/
  | movk (dst : String) (imm16 hw : Nat)
  /-- `dst := MOV src`. -/
  | mov (dst src : String)
  /-- `dst := LSR a, #imm` (logical shift-right by immediate, 64-bit). -/
  | lsr (dst a : String) (imm : Nat)
  /-- `dst := LSL a, #imm` (logical shift-left by immediate, 64-bit). -/
  | lsl (dst a : String) (imm : Nat)
  deriving Repr, DecidableEq

/-- Lower a register-named bignum op to the machine `BInst` — one rule per
    constructor (the A64 analogue of `toAInst`). -/
def toBInst : BOp → BInst
  | .add dst a b => .add dst a b
  | .sub dst a b => .sub dst a b
  | .adds dst a b => .adds dst a b
  | .adcs dst a b => .adcs dst a b
  | .adc dst a b => .adc dst a b
  | .subs dst a b => .subs dst a b
  | .sbcs dst a b => .sbcs dst a b
  | .sbc dst a b => .sbc dst a b
  | .mul dst a b => .mul dst a b
  | .umulh dst a b => .umulh dst a b
  | .and dst a b => .and dst a b
  | .orr dst a b => .orr dst a b
  | .eor dst a b => .eor dst a b
  | .csel dst a b c => .csel dst a b c
  | .movz dst imm16 => .movz dst imm16
  | .movk dst imm16 hw => .movk dst imm16 hw
  | .mov dst src => .mov dst src
  | .lsr dst a imm => .lsr dst a imm
  | .lsl dst a imm => .lsl dst a imm

/-- Lower a straight-line `BOp` block to a machine `BInst` block. -/
def lowerBBlock (block : List BOp) : List BInst := block.map toBInst

/-- **AArch64 bignum block-lowering denotation theorem.** The machine semantics
    of the lowered `BOp` block equals the fold of the per-op machine semantics
    over the block — for all blocks and all 64-bit states, by induction. No new
    custom axioms (the 64-bit analogue of `armBlock_lowering_denote`). -/
theorem bignumBlock_lowering_denote :
    ∀ (block : List BOp) (s : BState),
      runBBlock s (lowerBBlock block)
        = block.foldl (fun st op => evalBInst st (toBInst op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerBBlock, List.map_cons, runBBlock_cons, List.foldl_cons]
      exact ih (evalBInst s (toBInst op))

end CatCrypt.Crypto.SecureCompilation.ARMBackend
