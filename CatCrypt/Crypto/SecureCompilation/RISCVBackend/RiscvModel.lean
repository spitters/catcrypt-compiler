/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# A Lean RV64 (RISC-V 64-bit) machine model for the scalar GP-ALU subset (#535)

`X86Backend/Model.lean` (scalar x86) and `ARMBackend/ArmModel.lean` (AArch64
scalar) are the owned machine layers for those two ISAs; this module is their
**RISC-V RV64** analogue at the scalar 32-bit-word GP-ALU shape a ChaCha20
quarter-round needs (`addw`/`xor`/`slliw`/`srliw`/`or`, plus `subw`/`and`/`mv`).
It adds a named general-purpose register file (`RState`) over the RV64 integer
registers (`x0=zero … x31`) and the per-instruction semantics
(`evalRInst` / `runRBlock`) of that subset.

`RiscvLowering.lean` lifts a register-named op alphabet (`ROp`) onto this model
with the block-lowering denotation theorem `riscvBlock_lowering_denote` (the
RV64 analogue of `ARMBackend.armBlock_lowering_denote`, proved by induction with
no new custom axioms); `RiscvAsmPrinter.lean` renders the lowered `RInst` block
to GAS RV64 assembly text with a linear-scan GP allocator.

## The honest anchor (same posture as the x86/ARM owned models)

This sub-1 stands up the *framework*: a Lean RV64 GP-ALU machine + verified
lowering + GAS printer, with one scalar primitive (the RFC 8439 §2.1.1 ChaCha
quarter-round) emitted, the in-Lean KAT pinned, and a **real `qemu-riscv64` run**
of the emitted code against the RFC vector (`bench/riscv_compare/`). As with the
x86/ARM models, the **lowering** `ROp → RInst → RState transform` is verified
down to this model (`RiscvLowering.riscvBlock_lowering_denote`, no new custom
axioms); the **model's per-instruction semantics** is written to be obviously
the integer op the RV64 mnemonic computes (the RISC-V ISA `ADDW`/`XOR`/`SLLIW`/
`SRLIW`/… on the 32-bit-word view, auditable by eye), and is
differentially validated against the RFC 8439 KAT.

**Deferred to sub-2/sub-3** (per the task plan): the machine-code byte `Encoder`
+ `decode(encode i) = i` against the hand-transcribed `riscv/sail-riscv` `encdec`
clauses (upstream is not vendored in this repo; the RV64 analogue of
`SailX86Decoder`/`SailX86Validation`), and the RVV vector / Zvk
crypto extensions. This module deliberately covers only the scalar 32-bit-word
GP-ALU subset (RV64I, no `B`-extension rotate).

## RV64 has no base-ISA rotate — synthesize it

Unlike AArch64 (native `ROR`) or x86 (`shl;shr;or`), RV64 *base* (RV64I) has no
rotate instruction at all. So we model the ChaCha rotate-**left** by `n` over a
32-bit word as the base-ISA idiom
`slliw t, x, n ; srliw u, x, 32-n ; or x, t, u` — three RV64I instructions — and
the model's `opRol` semantics is exactly that decomposition (so the model and
the emitted code agree, and qemu runs on plain `rv64gc` with no extension).

The `Zbb` bit-manipulation extension adds the single-instruction rotate `RORIW`
(`roriw rd, rs1, imm`, opcode OP-IMM-32 `0x1b`, funct3 `0x5`, funct7 `0x30`). `Zbb`
is **mandated by the RVA22 / RVA23 application-profiles** (so every real RV64
application core — and `qemu-riscv64`'s default `rv64` CPU — ships it). We model
it as `RInst.roriw` with `opRoriw` (value-equal to the base-ISA `opRor` macro by
`opRoriw_eq_opRor`), so the SHA-256 `Σ`/`σ` mixers can each lower their six rotates
to **one** instruction instead of the three-instruction base macro — killing the
no-rotate instruction-count tax. The base path is preserved for comparison.

## The RV64 scalar ops we model (the 32-bit-word GP-ALU subset ChaCha emits)

| mnemonic | shape           | op (32-bit word view)                   |
|----------|-----------------|-----------------------------------------|
| `MV`     | `rd, rs`        | `rd := rs`                              |
| `ADDW`   | `rd, rs1, rs2`  | `rd := rs1 + rs2`  (wrapping 32-bit)    |
| `SUBW`   | `rd, rs1, rs2`  | `rd := rs1 - rs2`  (wrapping 32-bit)    |
| `AND`    | `rd, rs1, rs2`  | `rd := rs1 &&& rs2`                     |
| `OR`     | `rd, rs1, rs2`  | `rd := rs1 ||| rs2`                     |
| `XOR`    | `rd, rs1, rs2`  | `rd := rs1 ^^^ rs2`                     |
| `SLLIW`  | `rd, rs1, imm`  | `rd := rs1 <<< imm`  (logical shl)      |
| `SRLIW`  | `rd, rs1, imm`  | `rd := rs1 >>> imm`  (logical shr)      |

`x0` (`zero`) is hard-wired to `0` (reads as 0, writes ignored), exactly like
the AArch64 `wzr`. We model the 32-bit-word view (`BitVec 32`): RV64 `*W`
instructions operate on the low 32 bits and sign-extend into the 64-bit
register, but ChaCha only ever consumes the 32-bit value, so the 32-bit view is
the faithful and auditable abstraction. Loads/stores (`ld`/`sd`) used by the
prologue/epilogue to read args / write results are trusted scaffolding rendered
by the printer; the verified straight-line body is register-to-register, exactly
the x86/ARM `renderLeafFn` posture.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. The RV64 word type and register state

We model the 32-bit-word view of the integer registers, which is the lane width
ChaCha20 operates on. A register is a `BitVec 32`; the file is a
`String → BitVec 32` function keyed by register name. An absent name (and the
zero register `zero`/`x0`) reads as `0`. -/

/-- A 32-bit RV64 word-register value (the `*W`-instruction view). -/
abbrev R32 : Type := BitVec 32

/-- The RV64 GP register file: a name → `R32` function. An absent name (e.g. an
    uninitialised temporary, or the zero register `zero`) reads as `0`. -/
structure RState where
  /-- The integer register file (`x0 … x31` / ABI names, by string). -/
  regs : String → R32

namespace RState

/-- Read a register. The zero register `zero`/`x0` and any absent name read as
    `0`. -/
@[simp] def get (s : RState) (r : String) : R32 :=
  if r = "zero" ∨ r = "x0" then 0 else s.regs r

/-- Write a register, leaving the others unchanged. Writes to `zero`/`x0` are
    discarded (the RISC-V zero register is hard-wired to 0). -/
def set (s : RState) (r : String) (v : R32) : RState :=
  if r = "zero" ∨ r = "x0" then s
  else { regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem get_set_same (s : RState) (r : String) (v : R32)
    (h : ¬ (r = "zero" ∨ r = "x0")) : (s.set r v).get r = v := by
  simp [set, get, h]

@[simp] theorem get_set_other (s : RState) (r r' : String) (v : R32)
    (h : r' ≠ r) : (s.set r v).get r' = s.get r' := by
  by_cases hz : r' = "zero" ∨ r' = "x0"
  · simp [get, hz]
  · simp only [get, hz, if_false, set]
    by_cases hr : r = "zero" ∨ r = "x0"
    · simp [hr]
    · simp [hr, h]

end RState

/-! ## 2. Per-op 32-bit-word RV64 ALU semantics

Each op is the obvious 32-bit integer op over `BitVec 32` — auditable against
the RISC-V ISA manual by eye. -/

/-- `ADDW` op: wrapping 32-bit add. -/
@[simp] def opAddw (a b : R32) : R32 := a + b

/-- `SUBW` op: wrapping 32-bit subtract. -/
@[simp] def opSubw (a b : R32) : R32 := a - b

/-- `AND` op: bitwise and. -/
@[simp] def opAnd (a b : R32) : R32 := a &&& b

/-- `OR` op: bitwise or. -/
@[simp] def opOr (a b : R32) : R32 := a ||| b

/-- `XOR` op: bitwise xor. -/
@[simp] def opXor (a b : R32) : R32 := a ^^^ b

/-- `SLLIW` op: logical left shift by an immediate count. -/
@[simp] def opSlliw (a : R32) (m : Nat) : R32 := a <<< m

/-- `SRLIW` op: logical right shift by an immediate count. -/
@[simp] def opSrliw (a : R32) (m : Nat) : R32 := a >>> m

/-- The ChaCha rotate-**left** by `n` over a 32-bit word, as the RV64I base-ISA
    idiom `(a <<< n) ||| (a >>> (32 - n))` (no rotate instruction; synthesized
    from `slliw`+`srliw`+`or`). This is exactly what the emitted three-instruction
    sequence computes. -/
@[simp] def opRol (a : R32) (n : Nat) : R32 := (a <<< n) ||| (a >>> (32 - n))

/-- The SHA-256 rotate-**right** by `n` over a 32-bit word, as the RV64I base-ISA
    idiom `(a >>> n) ||| (a <<< (32 - n))` (no rotate instruction; synthesized
    from `srliw`+`slliw`+`or`). This is exactly what the emitted three-instruction
    sequence computes. The `Σ`/`σ` mixers of SHA-256 (FIPS 180-4 §4.1.2) use this. -/
@[simp] def opRor (a : R32) (n : Nat) : R32 := (a >>> n) ||| (a <<< (32 - n))

/-- The `Zbb` `RORIW` op: a 32-bit rotate-**right** by the immediate count `n`,
    computed as **one** RISC-V Zbb instruction (`roriw rd, rs1, n`). The result
    value is exactly the base-ISA `opRor` decomposition `(a >>> n) ||| (a <<< (32 - n))`
    — the Zbb instruction computes the same word in a single op, with no scratch
    temporary. RVA22/RVA23-profile cores (every real RV64 application core) ship
    `Zbb`, so this is the production rotate; `opRor` (the `srliw`+`slliw`+`or`
    macro) is kept as the base-RV64I comparison path. -/
@[simp] def opRoriw (a : R32) (n : Nat) : R32 := (a >>> n) ||| (a <<< (32 - n))

/-- The `Zbb` rotate-right instruction computes the same 32-bit word as the
    base-RV64I `srliw`+`slliw`+`or` macro: `opRoriw a n = opRor a n`, definitionally
    (both are `(a >>> n) ||| (a <<< (32 - n))`). This is the value-equality that
    lets the Zbb-lowered SHA-256 produce the same digest as the base-RV64I one. -/
@[simp] theorem opRoriw_eq_opRor (a : R32) (n : Nat) : opRoriw a n = opRor a n := rfl

/-! ## 3. The RV64 scalar instruction set

The 32-bit-word GP-ALU subset the ChaCha quarter-round emits (RV64I; rotate is
synthesized from `slliw`+`srliw`+`or`, so it is *not* a constructor here). The
machine-level analogue of `ARMBackend.AInst`. -/

/-- A single scalar RV64 instruction over named registers. -/
inductive RInst where
  /-- `ADDW rd, rs1, rs2` — 32-bit add. -/
  | addw (d a b : String)
  /-- `SUBW rd, rs1, rs2` — 32-bit subtract. -/
  | subw (d a b : String)
  /-- `AND rd, rs1, rs2` — bitwise and. -/
  | and  (d a b : String)
  /-- `OR rd, rs1, rs2` — bitwise or. -/
  | or   (d a b : String)
  /-- `XOR rd, rs1, rs2` — bitwise xor. -/
  | xor  (d a b : String)
  /-- `SLLIW rd, rs1, imm` — logical shift-left by immediate. -/
  | slliw (d a : String) (imm : Nat)
  /-- `SRLIW rd, rs1, imm` — logical shift-right by immediate. -/
  | srliw (d a : String) (imm : Nat)
  /-- `RORIW rd, rs1, imm` — `Zbb` 32-bit rotate-right by immediate (one
      instruction; opcode OP-IMM-32 `0x1b`, funct3 `0x5`, funct7 `0x30`). The
      single-instruction production rotate (RVA22/RVA23 mandate `Zbb`). -/
  | roriw (d a : String) (imm : Nat)
  /-- `MV rd, rs` — register move (pseudo-op for `ADDI rd, rs, 0`). -/
  | mv   (d s : String)
  deriving Repr, DecidableEq

/-- The semantics of one RV64 instruction: read source register(s), apply the
    op, write the destination. The analogue of `ARMBackend.evalAInst`. -/
def evalRInst (s : RState) : RInst → RState
  | .addw d a b => s.set d (opAddw (s.get a) (s.get b))
  | .subw d a b => s.set d (opSubw (s.get a) (s.get b))
  | .and  d a b => s.set d (opAnd (s.get a) (s.get b))
  | .or   d a b => s.set d (opOr  (s.get a) (s.get b))
  | .xor  d a b => s.set d (opXor (s.get a) (s.get b))
  | .slliw d a m => s.set d (opSlliw (s.get a) m)
  | .srliw d a m => s.set d (opSrliw (s.get a) m)
  | .roriw d a m => s.set d (opRoriw (s.get a) m)
  | .mv   d a   => s.set d (s.get a)

/-- `runRBlock`: a straight-line fold of `evalRInst`, the RV64 analogue of
    `ARMBackend.runABlock`. -/
def runRBlock (s : RState) : List RInst → RState
  | [] => s
  | i :: is => runRBlock (evalRInst s i) is

@[simp] theorem runRBlock_nil (s : RState) : runRBlock s [] = s := rfl

@[simp] theorem runRBlock_cons (s : RState) (i : RInst) (is : List RInst) :
    runRBlock s (i :: is) = runRBlock (evalRInst s i) is := rfl

theorem runRBlock_append_model (s : RState) (xs ys : List RInst) :
    runRBlock s (xs ++ ys) = runRBlock (runRBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runRBlock_cons, ih]

/-! ## 3b. RV64 B-type branches + the bounded counter-loop semantics (#552)

`RiscvControlFlow.lean` is the RV64 analogue of `ARMBackend.ArmControlFlow` (#551)
and `X86Backend/LprogControlFlow` (#538): it lowers a **bounded counter loop**
`for k in 0..n { body }` to a single body copy wrapped in an RV64 back-edge

```
   .Ltop:
       <body>                  -- the per-iteration RInst body (incl. its ctr -= 1)
       bne   <ctr>, x0, .Ltop  -- B-type back-edge: loop while ctr ≠ 0
```

instead of unrolling the body `n` times. Every RISC-V kernel so far was
straight-line/unrolled; this adds the looped emission.

RV64 has no `CBNZ`: the counter back-edge is the **B-type** conditional branch
`BNE ctr, x0, .Ltop` (branch if `ctr ≠ x0`, i.e. `ctr ≠ 0`). B-type branches
(`BEQ`/`BNE`/`BLT`/`BGE`/`BLTU`/`BGEU`) carry a 12-bit signed PC-relative offset
in the **scrambled** field layout `imm[12|10:5] rs2 rs1 funct3 imm[4:1|11]
opcode`, the RV64 immediate quirk handled in `RiscvEncoder`. The branch alphabet
is a *separate* inductive from `RInst` (the straight-line model carries no PC);
`runBoundedLoopR` runs the body `n` times, and `RiscvControlFlow.loopRBlock_denote`
shows that executing the looped form (`RiscvControlFlow.runRLoop`) from a counter
holding `n` reaches that state when the body decrements the counter. -/

/-- A function-local branch label (a string symbol). -/
abbrev RLabel : Type := String

/-- The RV64 B-type branch comparison the `funct3` selects (RISC-V `base_insts.sail`
    `encdec` `funct3`: `BEQ=000`, `BNE=001`, `BLT=100`, `BGE=101`, `BLTU=110`,
    `BGEU=111`). `bne` is the counter-loop back-edge (`ctr ≠ x0`). -/
inductive BCmp where
  /-- `BEQ` — branch if equal (`funct3 = 0b000`). -/
  | beq
  /-- `BNE` — branch if not equal (`funct3 = 0b001`); the loop back-edge. -/
  | bne
  /-- `BLT` — branch if signed `<` (`funct3 = 0b100`). -/
  | blt
  /-- `BGE` — branch if signed `≥` (`funct3 = 0b101`). -/
  | bge
  /-- `BLTU` — branch if unsigned `<` (`funct3 = 0b110`). -/
  | bltu
  /-- `BGEU` — branch if unsigned `≥` (`funct3 = 0b111`). -/
  | bgeu
  deriving Repr, DecidableEq

/-- The 3-bit `funct3` of a B-type branch comparison (sail `encdec`). -/
def BCmp.funct3 : BCmp → Nat
  | .beq => 0b000
  | .bne => 0b001
  | .blt => 0b100
  | .bge => 0b101
  | .bltu => 0b110
  | .bgeu => 0b111

/-- A single RV64 branch / control-flow instruction (or a label definition). The
    looped-emission control-flow alphabet, distinct from the straight-line
    `RInst`. -/
inductive RBranch where
  /-- `label:` — a function-local label definition (no machine word; the assembler
      resolves the PC-relative offsets of branches that target it). -/
  | label (l : RLabel)
  /-- `B<cmp> rs1, rs2, label` — B-type conditional branch (e.g. `BNE ctr, x0,
      .Ltop`, the counter back-edge). -/
  | bcc (c : BCmp) (rs1 rs2 : String) (l : RLabel)
  /-- `JAL x0, label` — unconditional jump (the J-type `j label` pseudo-op). -/
  | j (l : RLabel)
  deriving Repr, DecidableEq

/-- `runBoundedLoopR s n body`: the straight-line `body` run exactly `n` times over
    the `RState` model. The RV64 analogue of `ARMBackend.runBoundedLoopA`. -/
def runBoundedLoopR (s : RState) (n : Nat) (body : List RInst) : RState :=
  match n with
  | 0 => s
  | k + 1 => runBoundedLoopR (runRBlock s body) k body

@[simp] theorem runBoundedLoopR_zero (s : RState) (body : List RInst) :
    runBoundedLoopR s 0 body = s := rfl

@[simp] theorem runBoundedLoopR_succ (s : RState) (k : Nat) (body : List RInst) :
    runBoundedLoopR s (k + 1) body = runBoundedLoopR (runRBlock s body) k body := rfl

/-- The straight-line **unrolled** block of the same loop: `body` replicated `n`
    times. The RV64 analogue of `ARMBackend.unrollABounded`. -/
def unrollRBounded (n : Nat) (body : List RInst) : List RInst :=
  match n with
  | 0 => []
  | k + 1 => body ++ unrollRBounded k body

/-- **The bounded loop equals running the unrolled block.** `runBoundedLoopR s n
    body = runRBlock s (unrollRBounded n body)` — the looped semantics is exactly
    what running the `n`-copy unrolled straight-line block computes, by induction
    (the RV64 analogue of `runBoundedLoopA_eq_runABlock_unroll`). -/
theorem runBoundedLoopR_eq_runRBlock_unroll (s : RState) (n : Nat) (body : List RInst) :
    runBoundedLoopR s n body = runRBlock s (unrollRBounded n body) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp only [runBoundedLoopR_succ, unrollRBounded, runRBlock_append_model, ih]

/-! ## 4. Differential-validation pins (the scalar RV64 anchor)

Unit-level witnesses for the ops; the integration witness is the ChaCha
quarter-round KAT (`RiscvLowering.qr_rfc_kat`, RFC 8439 §2.1.1) and the real
qemu-riscv64 run-KAT in `bench/riscv_compare/`. -/

/-- `ADDW` pin: wrapping 32-bit add, `(2³²-1) + 3 = 2`. -/
example : opAddw (BitVec.allOnes 32) (3 : BitVec 32) = 2 := by native_decide

/-- `XOR` pin: `0xff00ff00 ^ 0x00ff00ff = 0xffffffff`. -/
example : opXor (BitVec.ofNat 32 0xff00ff00) (BitVec.ofNat 32 0x00ff00ff)
    = BitVec.allOnes 32 := by native_decide

/-- The synthesized rotate-left-16 (`slliw`+`srliw`+`or`) on `x = 0x12345678`
    yields `0x56781234`, matching the AArch64 native `ROR #16`. -/
example : opRol (BitVec.ofNat 32 0x12345678) 16 = BitVec.ofNat 32 0x56781234 := by
  native_decide

/-- The synthesized rotate-right-2 (`srliw`+`slliw`+`or`) on `x = 0x80000001`
    yields `0x60000000`, the SHA-256 `Σ0` first term. -/
example : opRor (BitVec.ofNat 32 0x80000001) 2 = BitVec.ofNat 32 0x60000000 := by
  native_decide

/-- The `Zbb` `RORIW` op computes the same `Σ0`-first-term word as the base macro,
    in one instruction: `roriw x, 2` on `0x80000001` yields `0x60000000`. -/
example : opRoriw (BitVec.ofNat 32 0x80000001) 2 = BitVec.ofNat 32 0x60000000 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend
