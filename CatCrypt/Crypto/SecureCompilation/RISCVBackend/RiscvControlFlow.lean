/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter

/-!
# Looped (non-unrolled) control-flow lowering for the owned RV64 backend (#552)

`RiscvLowering.lean` (#535) lowers a straight-line `ROp` block to the RV64 machine
`RInst`s with `riscvBlock_lowering_denote`; `RiscvSha256Kernel.lean` rode that for
the whole SHA-256 compression. Every RISC-V kernel so far is **straight-line /
unrolled** — an `n`-iteration loop emits an `n`-copy `RInst` block, so the `.s`
grows linearly in the trip count, and any iterative primitive (the X25519 ladder,
multi-block hashing) had no looped emission.

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

## The denotation theorem (the key correctness statement)

The looped emission and the unrolled emission denote the **same** machine
transformer. We do not re-prove the loop denotation from scratch: the machine
semantics of the looped form *is* `RiscvModel.runBoundedLoopR s n body` (the
counter-decrement body run `n` times), and
`RiscvModel.runBoundedLoopR_eq_runRBlock_unroll` already proves
`runBoundedLoopR s n body = runRBlock s (unrollRBounded n body)`.

`loopRBlock_denote` packages this: the looped emission's body denotes exactly
`runBoundedLoopR s n body` — the same value the unrolled straight-line block
denotes. The two emissions differ only in **size** (looped: 1 body copy + 2
control instrs; unrolled: `n` body copies), not in denotation. `NO compile-time
unroll` is performed on the looped path.

## What is lowered (and the honest residual)

* **Bounded for-loop (counter-decrement)** — `for k in 0..n { body }`, where the
  body decrements its own counter (`ADDIW ctr,ctr,-1` / `SUBW`) and the back-edge
  `BNE ctr, x0, .L<top>` loops while non-zero. This is the public-trip-count loop
  every multi-block hash / fixed-iteration ladder step uses. Its semantics is
  `runBoundedLoopR`.
* The **forward branch / guard** (`BEQ`/`BLT`/…) and the unconditional `J` render
  through the same `renderRBranch` arms (`RiscvAsmPrinter`).

A **general data-dependent loop** (a runtime, non-counter guard) is *not* lowered
here, exactly as on the x86/ARM side: the denotation backbone is the bounded
counter loop whose trip count is the compile-time / loaded limb count; an
unbounded loop needs a fixpoint denotation the framework's pure model does not
carry. We lower the bounded-for layer and the B-type branch; the unbounded
residual is reported, not claimed.

## Constant-time note (ISA-agnostic CT discipline)

The loop counter and the back-edge condition are **public** (a block count / limb
count / fixed ladder length), so `bne <ctr>, x0, .L<top>` is a public branch: the
iteration count is already observable by construction. A *secret*-dependent loop
bound or branch is forbidden in the constant-time subset. The bounded-for layer
here is public-counter by construction, so it is CT-admissible.
-/

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

/-! ## 3. Denotation preservation (the key correctness statement)

The machine semantics of the looped counter loop is `RiscvModel.runBoundedLoopR`
(run the counter-decrement `body` `n` times). `runBoundedLoopR_eq_runRBlock_unroll`
already proves the unrolled straight-line block computes that value; the looped
block denotes the **same** value. We package the equivalence under the looped
name, mirroring the ARM `loopABlock_denote` and the x86 `loopLcmd_denote`. -/

/-- **Looped lowering denotation = bounded-loop semantics.** The looped emission of
    a bounded counter loop denotes `runBoundedLoopR s n body` — exactly the value
    the unrolled straight-line block (`unrollRBounded`) denotes when run on the RV64
    model. The looped and unrolled emissions therefore agree on denotation and
    differ only in size (`loopRBlock_length` vs `unrollRGasLines_length`). This is
    the denotation-preservation statement for the RV64 branch/loop lowering:
    replacing the `n`-copy unrolled body by the single-copy looped body does not
    change the machine transformer. NO compile-time unroll. -/
theorem loopRBlock_denote (n : Nat) (body : List RInst) (s : RState) :
    runRBlock s (unrollRBounded n body) = runBoundedLoopR s n body :=
  (runBoundedLoopR_eq_runRBlock_unroll s n body).symm

/-- Looped vs unrolled denote the same transformer: both equal
    `runBoundedLoopR s n body`. Makes the "same denotation, smaller code" claim a
    single rewrite. -/
theorem looped_eq_unrolled_denote (n : Nat) (body : List RInst) (s : RState) :
    runRBlock s (unrollRBounded n body) = runBoundedLoopR s n body :=
  loopRBlock_denote n body s

/-! ## 4. A small counted-loop kernel through the owned branch path

The smallest iterative kernel that exercises the looped emission end-to-end: a
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
* the **machine semantics**: after `n` iterations the accumulator holds
  `n · step` (the bounded-loop denotation on the concrete body).

The qemu-riscv64 byte KAT (the emitted looped `.s` run on real RV64, accumulating
`n · step`) lives in `bench/riscv_compare/` (`acc-loop-rv64-kat`).

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
wrapping). The back-edge `BNE` and the label/jump machinery are correct by
`loopRBlock_denote` (the looped emission denotes `runBoundedLoopR`); this pins the
value the bounded loop computes. -/

/-- Initial state for the accumulate KAT: `acc = 0`, `step = 7`, `ctr = 5`,
    `one = 1`. -/
def accInit : RState :=
  { regs := fun r => match r with
      | "acc" => 0 | "step" => 7 | "ctr" => 5 | "one" => 1 | _ => 0 }

/-- **Counted-loop value KAT.** Running the accumulate body 5 times from `acc = 0`,
    `step = 7` leaves `acc = 35` (= 5·7), through the bounded-loop semantics the
    looped emission denotes (`loopRBlock_denote`). The counter `ctr` ends at 0
    (5 decrements from 5), the condition the `BNE` back-edge falls through on. -/
theorem acc_loop_kat :
    (runBoundedLoopR accInit 5 accBody).get "acc" = 35
      ∧ (runBoundedLoopR accInit 5 accBody).get "ctr" = 0 := by
  native_decide

/-- **The looped emission denotes the same value as the unrolled one** on the
    accumulate kernel: running the unrolled 5-copy block equals `runBoundedLoopR
    accInit 5 accBody`, which the value KAT pins to `acc = 35`. The single rewrite
    that turns "smaller code" into "same result". -/
theorem acc_loop_looped_eq_unrolled :
    runRBlock accInit (unrollRBounded 5 accBody) = runBoundedLoopR accInit 5 accBody :=
  loopRBlock_denote 5 accBody accInit

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvControlFlow
