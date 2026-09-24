/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel

/-!
# Wiring a register-named scalar op alphabet to the RV64 machine model

`ARMBackend.ArmLowering` lowers a register-named scalar op alphabet (`AOp`) to
the A64 machine `AInst` with the block-lowering denotation theorem
`armBlock_lowering_denote`, and the ChaCha quarter-round rides it. This module
is the **RISC-V RV64** analogue: a register-named op alphabet `ROp`, the lowering
`toRInst` to a *list* of `RiscvModel.RInst`, and the block-lowering denotation
theorem `riscvBlock_lowering_denote` (the RV64 analogue of
`armBlock_lowering_denote`, proved by induction with no new custom axioms). The
concrete payoff is the RFC 8439 §2.1.1 ChaCha20 quarter-round written as an `ROp`
block, lowered, run on the model, and pinned **byte-identical to the published
RFC test vector** (and run for real under `qemu-riscv64` in `bench/`).

```
ROp (RFC 8439 quarter-round)  --lowerRBlock-->  RInst (RV64 register machine)
                              --runRBlock (RiscvModel)-->  RState transform
                              --renderRInst (RiscvAsmPrinter)-->  GAS RV64 asm
```

## The rotate is a *macro* lowering (one `ROp` → three `RInst`)

RV64I has no rotate, so `ROp.rotl dst x n` (the ChaCha rotate-left) lowers to the
three-instruction idiom `slliw tmp x n ; srliw dst x (32-n) ; or dst tmp dst`
(using a fresh temp). Hence `toRInst` returns a `List RInst` and `lowerRBlock`
is a `flatMap`, not a `map` — the one structural difference from the AArch64
backend (where `ROR` is one instruction). The lowering is still verified down to
the model: `riscvBlock_lowering_denote` is by induction over the source block,
and the rotate macro's denotation is proved to equal `opRol`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. A register-named scalar op (the lowering's source shape) -/

/-- A register-named scalar RV64 op: destination + source register name(s) plus
    the operation. The register-level analogue of `ARMBackend.AOp`. The rotate-
    left `rotl` additionally names the temporary register the macro uses. -/
inductive ROp where
  /-- `dst := ADDW a, b`. -/
  | add (dst a b : String)
  /-- `dst := SUBW a, b`. -/
  | sub (dst a b : String)
  /-- `dst := AND a, b`. -/
  | and (dst a b : String)
  /-- `dst := OR a, b`. -/
  | or  (dst a b : String)
  /-- `dst := XOR a, b`. -/
  | xor (dst a b : String)
  /-- `dst := SLLIW a, #imm`. -/
  | shl (dst a : String) (imm : Nat)
  /-- `dst := SRLIW a, #imm`. -/
  | shr (dst a : String) (imm : Nat)
  /-- `dst := rotate-left(a, #imm)`, synthesized via `slliw`+`srliw`+`or` using
      the named temporary `tmp` (distinct from `dst`/`a`). -/
  | rotl (dst a : String) (imm : Nat) (tmp : String)
  /-- `dst := rotate-right(a, #imm)`, synthesized via `srliw`+`slliw`+`or` using
      the named temporary `tmp` (distinct from `dst`/`a`). The SHA-256 `Σ`/`σ`
      mixers (FIPS 180-4 §4.1.2) use right-rotate. -/
  | rotr (dst a : String) (imm : Nat) (tmp : String)
  /-- `dst := MV src`. -/
  | mov (dst src : String)
  deriving Repr, DecidableEq

/-- Lower a register-named scalar op to a *list* of machine `RInst`s. All ops are
    one-to-one except `rotl`, which expands to the three-instruction RV64I rotate
    idiom `slliw tmp a imm ; srliw dst a (32-imm) ; or dst tmp dst`. -/
def toRInst : ROp → List RInst
  | .add dst a b => [.addw dst a b]
  | .sub dst a b => [.subw dst a b]
  | .and dst a b => [.and  dst a b]
  | .or  dst a b => [.or   dst a b]
  | .xor dst a b => [.xor  dst a b]
  | .shl dst a m => [.slliw dst a m]
  | .shr dst a m => [.srliw dst a m]
  | .rotl dst a m tmp => [.slliw tmp a m, .srliw dst a (32 - m), .or dst tmp dst]
  | .rotr dst a m tmp => [.srliw tmp a m, .slliw dst a (32 - m), .or dst tmp dst]
  | .mov dst src => [.mv dst src]

/-- Lower a straight-line `ROp` block to a machine `RInst` block. Since the
    rotate macro expands one `ROp` to three `RInst`, this is a `flatMap`. -/
def lowerRBlock (block : List ROp) : List RInst := block.flatMap toRInst

/-! ### The `Zbb` (single-instruction rotate) lowering

The base lowering above expands each `ROp.rotr` to **three** RV64I instructions
(`srliw tmp a m ; slliw dst a (32-m) ; or dst tmp dst`) — the no-rotate tax. The
`Zbb` extension's `RORIW` does the same rotate in **one** instruction. The Zbb
lowering `toRInstZbb` is identical to `toRInst` except `rotr` (and `rotl`, via the
identity `rotl x n = rotr x (32-n)`) lowers to a single `RInst.roriw`. Every other
op is unchanged, so `toRInstZbb` is `1:1` on the whole block and `lowerRBlockZbb`
is a `map` whose length equals the source `ROp` count — the rotate tax is gone.
The base path (`toRInst`/`lowerRBlock`) is kept for the instruction-count
comparison. -/

/-- The `Zbb` lowering of a register-named scalar op. Identical to `toRInst`
    except the rotate ops become a single `RInst.roriw` (no scratch temp, no
    macro): `rotr dst a m` → `[roriw dst a m]`, and `rotl dst a m` →
    `[roriw dst a (32 - m)]` (a left-rotate by `m` is a right-rotate by `32-m`).
    For the SHA-256 rotates `m ∈ {2,6,7,11,13,17,18,19,22,25}`, all `< 32`, the
    `5`-bit `RORIW` `shamt` represents them exactly. -/
def toRInstZbb : ROp → List RInst
  | .add dst a b => [.addw dst a b]
  | .sub dst a b => [.subw dst a b]
  | .and dst a b => [.and  dst a b]
  | .or  dst a b => [.or   dst a b]
  | .xor dst a b => [.xor  dst a b]
  | .shl dst a m => [.slliw dst a m]
  | .shr dst a m => [.srliw dst a m]
  | .rotl dst a m _tmp => [.roriw dst a (32 - m)]
  | .rotr dst a m _tmp => [.roriw dst a m]
  | .mov dst src => [.mv dst src]

/-- The `Zbb` lowering of a block: a `flatMap` of `toRInstZbb`. Because every op
    (including the rotate) lowers to exactly one `RInst`, the result length equals
    the source `ROp` count — the no-rotate `2×`-per-rotate tax of `lowerRBlock`
    is eliminated. -/
def lowerRBlockZbb (block : List ROp) : List RInst := block.flatMap toRInstZbb

/-- Each `Zbb`-lowered op is exactly **one** `RInst` (the rotate is a single
    `Zbb` instruction, not a 3-instruction macro). Hence the whole `Zbb`-lowered
    block has length equal to
    the source `ROp` count. -/
theorem toRInstZbb_length (op : ROp) : (toRInstZbb op).length = 1 := by
  cases op <;> rfl

/-- `lowerRBlockZbb` has length equal to the `ROp` count: the rotate tax is gone
    (`lowerRBlock` is longer by `2 ×` the number of rotate ops). -/
theorem lowerRBlockZbb_length (block : List ROp) :
    (lowerRBlockZbb block).length = block.length := by
  induction block with
  | nil => rfl
  | cons op rest ih =>
      simp only [lowerRBlockZbb, List.flatMap_cons, List.length_append,
        toRInstZbb_length, List.length_cons] at *
      omega

/-! ## 2. Per-op denotation preservation

The interesting case is the rotate macro: running its three lowered instructions
produces `opRol` in `dst`, provided the temporary is distinct from `dst` and the
source. -/

/-- **ADDW preserves the add denotation.** -/
theorem add_run_denote (s : RState) (dst a b : String)
    (h : ¬ (dst = "zero" ∨ dst = "x0")) :
    (runRBlock s (toRInst (.add dst a b))).get dst = opAddw (s.get a) (s.get b) := by
  simp only [toRInst, runRBlock, evalRInst, RState.get_set_same _ _ _ h]

/-- **XOR preserves the xor denotation.** -/
theorem xor_run_denote (s : RState) (dst a b : String)
    (h : ¬ (dst = "zero" ∨ dst = "x0")) :
    (runRBlock s (toRInst (.xor dst a b))).get dst = opXor (s.get a) (s.get b) := by
  simp only [toRInst, runRBlock, evalRInst, RState.get_set_same _ _ _ h]

/-- **The rotate macro preserves the rotate-left denotation.** Running
    `slliw tmp a m ; srliw dst a (32-m) ; or dst tmp dst` writes `opRol (a) m`
    into `dst`, when `tmp ≠ dst`, `tmp ≠ a` (the temp is fresh) and neither is
    the zero register. -/
theorem rotl_run_denote (s : RState) (dst a tmp : String) (m : Nat)
    (hdst : ¬ (dst = "zero" ∨ dst = "x0"))
    (htmp : ¬ (tmp = "zero" ∨ tmp = "x0"))
    (htd : tmp ≠ dst) (hta : tmp ≠ a) :
    (runRBlock s (toRInst (.rotl dst a m tmp))).get dst = opRol (s.get a) m := by
  simp only [toRInst, runRBlock, evalRInst, opSlliw, opSrliw, opOr, opRol]
  -- the final `or dst tmp dst` reads tmp and the just-written dst (the srliw result)
  rw [RState.get_set_same _ _ _ hdst, RState.get_set_same _ _ _ hdst]
  -- the tmp read: set tmp, then set dst (tmp ≠ dst), then read tmp
  rw [RState.get_set_other _ _ _ _ htd, RState.get_set_same _ _ _ htmp]
  -- the `a` source read through the tmp write (a ≠ tmp)
  rw [RState.get_set_other _ _ _ _ (Ne.symm hta)]

/-- **The right-rotate macro preserves the rotate-right denotation.** Running
    `srliw tmp a m ; slliw dst a (32-m) ; or dst tmp dst` writes `opRor (a) m`
    into `dst`, when `tmp ≠ dst`, `tmp ≠ a` (the temp is fresh) and neither is
    the zero register. -/
theorem rotr_run_denote (s : RState) (dst a tmp : String) (m : Nat)
    (hdst : ¬ (dst = "zero" ∨ dst = "x0"))
    (htmp : ¬ (tmp = "zero" ∨ tmp = "x0"))
    (htd : tmp ≠ dst) (hta : tmp ≠ a) :
    (runRBlock s (toRInst (.rotr dst a m tmp))).get dst = opRor (s.get a) m := by
  simp only [toRInst, runRBlock, evalRInst, opSrliw, opSlliw, opOr, opRor]
  rw [RState.get_set_same _ _ _ hdst, RState.get_set_same _ _ _ hdst]
  rw [RState.get_set_other _ _ _ _ htd, RState.get_set_same _ _ _ htmp]
  rw [RState.get_set_other _ _ _ _ (Ne.symm hta)]

/-- **The `Zbb` rotate preserves the rotate-right denotation in one instruction.**
    Running the single `roriw dst a m` writes `opRor (a) m` into `dst` (the same
    word the three-instruction base macro writes via `rotr_run_denote`, by
    `opRoriw_eq_opRor`), with no scratch temporary. The only side-condition is that
    `dst` is not the zero register. -/
theorem roriw_run_denote (s : RState) (dst a tmp : String) (m : Nat)
    (hdst : ¬ (dst = "zero" ∨ dst = "x0")) :
    (runRBlock s (toRInstZbb (.rotr dst a m tmp))).get dst = opRor (s.get a) m := by
  simp only [toRInstZbb, runRBlock, evalRInst, opRoriw_eq_opRor]
  rw [RState.get_set_same _ _ _ hdst]

/-! ## 3. The block-lowering denotation theorem (RV64)

The RV64 analogue of `ARMBackend.armBlock_lowering_denote`: lowering a
straight-line `ROp` block to machine `RInst`s and running it on the RV64 model
equals the direct machine fold of the per-op lowering — for **all** blocks and
**all** register states, by induction. No new custom axioms.

Because each `ROp` lowers to a *list* of `RInst`, the per-op machine effect is
`fun st op => runRBlock st (toRInst op)` (run the op's expansion), and the
theorem says running the flattened block equals folding that. -/

/-- A helper: running a concatenation of `RInst` lists is the left-fold of
    running each piece. -/
theorem runRBlock_append (xs ys : List RInst) (s : RState) :
    runRBlock s (xs ++ ys) = runRBlock (runRBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runRBlock_cons]; exact ih _

/-- **RISC-V RV64 block-lowering denotation theorem.** The machine semantics of
    the lowered `ROp` block (the `flatMap` of `toRInst` over the block, run on the
    model) equals the fold of each op's expansion run on the model — i.e.
    `runRBlock` on the lowered instructions IS the model-level transform, for all
    blocks and states. -/
theorem riscvBlock_lowering_denote :
    ∀ (block : List ROp) (s : RState),
      runRBlock s (lowerRBlock block)
        = block.foldl (fun st op => runRBlock st (toRInst op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerRBlock, List.flatMap_cons, List.foldl_cons]
      rw [runRBlock_append]
      exact ih (runRBlock s (toRInst op))

/-- Single-op specialisation: lowering and running a one-op block runs that op's
    expansion. -/
theorem riscvBlock_lowering_denote_single (op : ROp) (s : RState) :
    runRBlock s (lowerRBlock [op]) = runRBlock s (toRInst op) := by
  simp [lowerRBlock]

/-- **The `Zbb` block-lowering denotation theorem.** The RV64 main theorem for the
    `Zbb` (single-instruction-rotate) lowering: running the `Zbb`-lowered `ROp`
    block on the model equals the fold of each op's `Zbb` expansion run on the
    model, for all blocks and states, by induction. No new custom axioms. -/
theorem riscvBlockZbb_lowering_denote :
    ∀ (block : List ROp) (s : RState),
      runRBlock s (lowerRBlockZbb block)
        = block.foldl (fun st op => runRBlock st (toRInstZbb op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerRBlockZbb, List.flatMap_cons, List.foldl_cons]
      rw [runRBlock_append]
      exact ih (runRBlock s (toRInstZbb op))

/-! ## 4. The ChaCha20 quarter-round as an `ROp` block (RFC 8439 §2.1)

The ChaCha20 quarter-round (RFC 8439 §2.1) on four state words `a b c d`:
```
a += b; d ^= a; d <<<= 16
c += d; b ^= c; b <<<= 12
a += b; d ^= a; d <<<= 8
c += d; b ^= c; b <<<= 7
```
RV64I has no rotate, so each rotate-**left** by `n` is the three-instruction
macro (`slliw`+`srliw`+`or`) using a scratch register `t`. The quarter-round is
thus 8 ALU ops + 4 rotate macros = 8 + 12 = 20 RV64 instructions. -/

/-- A rotate-**left** by `n` of register `x` into `x`, via the RV64I macro using
    scratch register `t`. -/
def rotlOp (x : String) (n : Nat) (t : String) : ROp := .rotl x x n t

/-- One ChaCha quarter-round on register names `a b c d` (RFC 8439 §2.1), in
    place, using scratch register `t` for the rotate macros — the `ROp` block. -/
def qrBlk (a b c d t : String) : List ROp :=
  [ .add a a b, .xor d d a, rotlOp d 16 t
  , .add c c d, .xor b b c, rotlOp b 12 t
  , .add a a b, .xor d d a, rotlOp d 8 t
  , .add c c d, .xor b b c, rotlOp b 7 t ]

/-! ## 5. The RFC 8439 §2.1.1 quarter-round KAT (the scalar RV64 witness)

Lowered-and-run on the model: this exercises every lowered op
(`ADDW`/`XOR`/`SLLIW`/`SRLIW`/`OR`) on a tiny register state, byte-identical to
the RFC, fast under `native_decide`. The assembled + `qemu-riscv64`-run byte-KAT
lives in `bench/riscv_compare/`. -/

/-- RFC 8439 §2.1.1 quarter-round input state: `a = 0x11111111`,
    `b = 0x01020304`, `c = 0x9b8d6f43`, `d = 0x01234567`. Other names read as
    zero. -/
def qrInit : RState :=
  { regs := fun r =>
      match r with
      | "a" => 0x11111111 | "b" => 0x01020304
      | "c" => 0x9b8d6f43 | "d" => 0x01234567
      | _ => 0 }

/-- The lowered-and-run quarter-round on register names `a b c d` with scratch
    `t`. -/
def qrRun : RState := runRBlock qrInit (lowerRBlock (qrBlk "a" "b" "c" "d" "t"))

/-- **Lowering correctness on the quarter-round block.** Running the lowered
    quarter-round on the model equals the direct per-op machine fold — the block
    theorem instantiated on the RFC 8439 §2.1.1 body. -/
theorem qr_lowering_correct :
    runRBlock qrInit (lowerRBlock (qrBlk "a" "b" "c" "d" "t"))
      = (qrBlk "a" "b" "c" "d" "t").foldl
          (fun st op => runRBlock st (toRInst op)) qrInit :=
  riscvBlock_lowering_denote (qrBlk "a" "b" "c" "d" "t") qrInit

/-- **RFC 8439 §2.1.1 KAT.** The lowered-and-run quarter-round produces the
    published output `a = 0xea2a92f4`, `b = 0xcb1cf8ce`, `c = 0x4581472e`,
    `d = 0x5881c4bb`, byte-identical. -/
theorem qr_rfc_kat :
    (qrRun.get "a" = 0xea2a92f4) ∧ (qrRun.get "b" = 0xcb1cf8ce) ∧
    (qrRun.get "c" = 0x4581472e) ∧ (qrRun.get "d" = 0x5881c4bb) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend
