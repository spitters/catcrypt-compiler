/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter

/-!
# Looped (non-unrolled) control-flow lowering for the owned RV64 backend (#552)

`RiscvLowering.lean` (#535) lowers a straight-line `ROp` block to the RV64 machine
`RInst`s with `riscvBlock_lowering_denote`; `RiscvSha256Kernel.lean` rode that for
the SHA-256 compression. A straight-line lowering emits an `n`-iteration loop as
an `n`-copy `RInst` block, so the `.s` grows linearly in the trip count.

This module is the **RV64 analogue of the ARM owned-backend loop emission**
(`ARMBackend/ArmControlFlow.lean`, #551) and the original x86 #538
(`X86Backend/LprogControlFlow.lean`): a bounded counter loop is emitted as a
single body copy wrapped in an RV64 back-edge

```
   .L<top>:
       <body>                  -- the per-iteration RInst body (incl. its ctr -= 1)
       bne   <ctr>, x0, .L<top>   -- B-type back-edge: loop while ctr ≠ 0
```

The emitted control-flow block is **constant-size** in the trip count (1 body copy
+ 1 label + 1 back-edge `BNE`), so the `.s` is `O(1)` body copies instead of
`O(n)` — cutting both the emitted code size and the compiler's peak `RInst` memory.

## RV64 has no `CBNZ` — the back-edge is a B-type `BNE`

AArch64 has `CBNZ Wt, .L` (one compare-and-branch op); RV64 base has no such
instruction. The counter back-edge is the **B-type** conditional branch
`BNE ctr, x0, .L<top>` — branch if `ctr ≠ x0`, i.e. while the counter is non-zero —
using the hard-wired zero register `x0` as the comparand. B-type branches carry a
12-bit signed PC-relative offset in the *scrambled* field layout
`imm[12|10:5] rs2 rs1 funct3 imm[4:1|11] opcode`; `RiscvEncoder.encB` packs that
scramble and `SailRiscvDecoder.roundtrip_bcc` round-trips it (the high-risk spot
the gas byte-diff also catches).

## What is proved about the loop

`loopRBlock` returns rendered GAS lines (`List String`), and the `RInst` model
has no semantics for labels or branches, so no theorem here states what the
looped emission computes. The proved facts are:

* `loopRBlock_length` / `unrollRGasLines_length` / `looped_shorter_than_unrolled`:
  line counts of the two renderings;
* `loopRBlock_denote`: the unrolled straight-line block
  `unrollRBounded n body`, run on the `RState` model, equals
  `RiscvModel.runBoundedLoopR s n body`, the body run `n` times
  (`RiscvModel.runBoundedLoopR_eq_runRBlock_unroll`, restated).

`runBoundedLoopR` takes the trip count `n` as an argument and does not read the
counter register, so the correspondence between `n` iterations and the
`BNE <ctr>` back-edge is an assumption about the emitted loop, not a theorem.

## What is lowered

* **Bounded for-loop (counter-decrement)** — `for k in 0..n { body }`, where the
  body decrements its own counter (`ADDIW ctr,ctr,-1` / `SUBW`) and the back-edge
  `BNE ctr, x0, .L<top>` loops while non-zero. This is the public-trip-count loop
  every multi-block hash / fixed-iteration ladder step uses. Its semantics is
  `runBoundedLoopR`.
* The **forward branch / guard** (`BEQ`/`BLT`/…) and the unconditional `J` render
  through the same `renderRBranch` arms (`RiscvAsmPrinter`).

A **general data-dependent loop** (a runtime, non-counter guard) is *not* lowered
here, as on the x86/ARM side: the loop semantics used is the bounded counter loop
whose trip count is the compile-time / loaded limb count; an unbounded loop needs
a fixpoint denotation the framework's pure model does not carry.

## Constant-time note

The loop counter and the back-edge condition are intended to be **public** (a
block count / limb count / fixed ladder length), so `bne <ctr>, x0, .L<top>`
branches on public data only. A *secret*-dependent loop bound or branch is outside
the constant-time subset. No theorem in this module states a constant-time
property.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvControlFlow

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. The looped control-flow block builder

A bounded counter loop `for k in 0..n { body }` (where `body` ends with its own
counter decrement) is emitted as the owned-backend control-flow shape
`.L<top>: <body> ; BNE ctr, x0, .L<top>`. The emitted artifact is the rendered GAS
lines (label line + body lines + back-edge line), constant-size in the trip
count. -/

/-- The looped control-flow shape for a bounded counter loop: a label at the top,
    the body, and a `BNE <ctr>, x0, .L<top>` back-edge. Returned as the rendered
    GAS lines, wrapping the body **once**, independent of the trip count. -/
def loopRBlock (alloc : GpAlloc) (top : RLabel) (ctr : String) (body : List RInst) :
    List String :=
  renderRBranch alloc (.label top)
    :: renderRBlockBody alloc body
    ++ [renderRBranch alloc (.bcc .bne ctr "zero" top)]

/-- The straight-line **unrolled** GAS lines of the same loop: the body's lines
    replicated `n` times (no label, no branch). This is the existing emission
    shape — `O(n)` body copies. -/
def unrollRGasLines (alloc : GpAlloc) (n : Nat) (body : List RInst) : List String :=
  match n with
  | 0 => []
  | k + 1 => renderRBlockBody alloc body ++ unrollRGasLines alloc k body

/-! ## 2. Size: looped is constant, unrolled is linear in the trip count -/

/-- The looped emission has a constant line count: the body line count plus two
    control lines (label + back-edge), **independent of the trip count** `n`. -/
@[simp] theorem loopRBlock_length (alloc : GpAlloc) (top : RLabel) (ctr : String)
    (body : List RInst) :
    (loopRBlock alloc top ctr body).length = body.length + 2 := by
  simp [loopRBlock, renderRBlockBody, List.length_append]

/-- The unrolled emission has a line count linear in the trip count: `n · |body|`.
    Together with `loopRBlock_length` this is the size payoff. -/
@[simp] theorem unrollRGasLines_length (alloc : GpAlloc) (n : Nat) (body : List RInst) :
    (unrollRGasLines alloc n body).length = n * body.length := by
  induction n with
  | zero => simp [unrollRGasLines]
  | succ k ih =>
      simp only [unrollRGasLines, List.length_append, renderRBlockBody, List.length_map, ih]
      rw [Nat.succ_mul]; omega

/-- For any trip count `n ≥ 4` and a body of `≥ 2` instrs, the looped emission is
    strictly shorter than the unrolled one — the concrete size win. -/
theorem looped_shorter_than_unrolled (alloc : GpAlloc) (top : RLabel) (ctr : String)
    (body : List RInst) (n : Nat) (hn : 4 ≤ n) (hb : 2 ≤ body.length) :
    (loopRBlock alloc top ctr body).length < (unrollRGasLines alloc n body).length := by
  rw [loopRBlock_length, unrollRGasLines_length]
  have h4 : 4 * body.length ≤ n * body.length := Nat.mul_le_mul_right body.length hn
  omega

/-! ## 3. The bounded-loop semantics and the unrolled block

`RiscvModel.runBoundedLoopR s n body` runs `body` `n` times on the `RState` model.
`runBoundedLoopR_eq_runRBlock_unroll` proves that running the unrolled
straight-line block `unrollRBounded n body` computes the same state. The looped
rendering `loopRBlock` has no semantics in the model, so the statement below is
about the unrolled block only. -/

/-- The unrolled straight-line block `unrollRBounded n body`, run on the `RState`
    model, equals `runBoundedLoopR s n body` (the body run `n` times); the symmetric
    form of `runBoundedLoopR_eq_runRBlock_unroll`. The looped emission
    `loopRBlock` does not occur in the statement: it is a list of rendered lines,
    and no theorem relates its execution to `runBoundedLoopR`. -/
theorem loopRBlock_denote (n : Nat) (body : List RInst) (s : RState) :
    runRBlock s (unrollRBounded n body) = runBoundedLoopR s n body :=
  (runBoundedLoopR_eq_runRBlock_unroll s n body).symm

/-- The same statement as `loopRBlock_denote`: the unrolled block run on the
    model equals `runBoundedLoopR s n body`. -/
theorem looped_eq_unrolled_denote (n : Nat) (body : List RInst) (s : RState) :
    runRBlock s (unrollRBounded n body) = runBoundedLoopR s n body :=
  loopRBlock_denote n body s

/-! ## 4. A small counted-loop kernel through the owned branch path

A small iterative kernel for the looped emission: a
counted accumulate — `acc := 0 ; for k in 0..n { acc += step ; ctr -= 1 }`, i.e.
`acc := n · step` computed by an `n`-iteration loop rather than `n` copies of the
add. The body is the two-instruction `{ ADDW acc,acc,step ; SUBW ctr,ctr,one }`
(with `one` holding the constant `1`, so the counter decrement is a real `SUBW`
the `BNE` back-edge tests), wrapped once by `loopRBlock`. This is the same
counted-accumulate kernel the ARM twin used (`ArmControlFlow.accBody`), for
cross-ISA comparison.

We pin:

* the looped block's line count is constant (body + 2), the unrolled one's is
  linear (`#looped < #unrolled` for the real trip counts);
* the rendered looped `.s` contains the loop label `.Lacc:`, the body's
  `addw`/`subw`, and the back-edge `bne … zero`;
* on the model: `runBoundedLoopR` of the body, from `acc = 0`, `step = 7`,
  `ctr = 5`, leaves `acc = 35` and `ctr = 0` after 5 iterations.

The rendering checks are substring tests on the emitted lines; the value check
is on `runBoundedLoopR`, not on the rendered loop. Execution of the emitted `.s`
is not checked in this package.

For the loop we model the counter decrement as `SUBW ctr,ctr,one` (`one` holds
the constant `1`); the `RInst` model carries no flags, so the back-edge condition
is the model-level "counter reached 0 after `n` decrements", which
`runBoundedLoopR … n` captures directly. -/

/-- The accumulate-loop **body**: `acc += step ; ctr -= 1`. Two `RInst`s; the
    `subw` is the counter decrement the `BNE` back-edge tests. -/
def accBody : List RInst := [ .addw "acc" "acc" "step", .subw "ctr" "ctr" "one" ]

/-- The looped accumulate kernel: `accBody` wrapped once by `loopRBlock`, counter
    register `ctr`, top label `acc`. The allocation pins `acc/step/ctr/one`. -/
def accLoopGas (alloc : GpAlloc) : List String := loopRBlock alloc "acc" "ctr" accBody

/-- A representative allocation for the accumulate kernel. -/
def accAlloc : GpAlloc := [("acc","a0"),("step","a1"),("ctr","a2"),("one","a3")]

/-- The looped emission is 4 lines (2 body + label + back-edge), independent of
    the trip count. -/
example : (accLoopGas accAlloc).length = 4 := by decide

/-- For the real trip counts (`n ≥ 4`) the looped emission is strictly shorter
    than the unrolled one. -/
example (n : Nat) (hn : 4 ≤ n) :
    (accLoopGas accAlloc).length < (unrollRGasLines accAlloc n accBody).length :=
  looped_shorter_than_unrolled accAlloc "acc" "ctr" accBody n hn (by decide)

/-- **KAT (rendering): the counted-loop kernel renders with the owned control-flow
    shape.** The looped accumulate body, rendered through `renderRBranch` /
    `renderRBlockBody`, contains the loop label `.Lacc:`, the body's `addw a0, a0,
    a1` and `subw a2, a2, a3`, and the conditional back-edge `bne a2, zero, .Lacc`
    — the owned-backend label / B-type-branch emission for a real looping kernel. -/
example :
    let ls := accLoopGas accAlloc
    ls.contains ".Lacc:" = true ∧ ls.contains "\taddw a0, a0, a1" = true
      ∧ ls.contains "\tsubw a2, a2, a3" = true
      ∧ ls.contains "\tbne a2, zero, .Lacc" = true := by
  native_decide

/-! ### Loop semantics KAT: `n` iterations accumulate `n · step`

We instantiate the bounded-loop denotation on `accBody` over a concrete state.
Running `accBody` `n` times from `acc = 0` leaves `acc = n · step` (32-bit
wrapping); the check below is at `n = 5`. It concerns `runBoundedLoopR`, not the
rendered `BNE` loop, whose execution has no model here. -/

/-- Initial state for the accumulate KAT: `acc = 0`, `step = 7`, `ctr = 5`,
    `one = 1`. -/
def accInit : RState :=
  { regs := fun r => match r with
      | "acc" => 0 | "step" => 7 | "ctr" => 5 | "one" => 1 | _ => 0 }

/-- **Counted-loop value KAT.** Running the accumulate body 5 times from `acc = 0`,
    `step = 7` leaves `acc = 35` (= 5·7) under `runBoundedLoopR`. The counter
    `ctr` ends at 0 (5 decrements from 5). -/
theorem acc_loop_kat :
    (runBoundedLoopR accInit 5 accBody).get "acc" = 35
      ∧ (runBoundedLoopR accInit 5 accBody).get "ctr" = 0 := by
  native_decide

/-- On the accumulate kernel, running the unrolled 5-copy block equals
    `runBoundedLoopR accInit 5 accBody` (`loopRBlock_denote` at `n = 5`). -/
theorem acc_loop_looped_eq_unrolled :
    runRBlock accInit (unrollRBounded 5 accBody) = runBoundedLoopR accInit 5 accBody :=
  loopRBlock_denote 5 accBody accInit

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvControlFlow
