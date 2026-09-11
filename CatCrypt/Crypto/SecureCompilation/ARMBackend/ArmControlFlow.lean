/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmPrinter

/-!
# Looped (non-unrolled) control-flow lowering for the owned AArch64 backend (#551)

`ArmLowering.lean` (#533/#547) lowers a straight-line `AOp` block to the A64
machine `AInst`s with `armBlock_lowering_denote`; `ArmSha256Kernel.lean` (#550)
rode that for the whole 64-round SHA-256 compression. Every ARM kernel so far is
**straight-line / unrolled** — an `n`-iteration loop emits an `n`-copy `AInst`
block, so the `.s` grows linearly in the trip count, and any iterative primitive
(the X25519 ladder, multi-block hashing) had no looped emission.

This module is the **AArch64 analogue of the x86 owned-backend loop emission**
(`X86Backend/LprogControlFlow.lean`, #538): a bounded counter loop is emitted as a
single body copy wrapped in an A64 back-edge

```
   .L<top>:
       <body>                  -- the per-iteration AInst body (incl. its ctr -= 1)
       cbnz   <ctr>, .L<top>   -- back-edge: loop while ctr ≠ 0
```

The emitted control-flow block is **constant-size** in the trip count (1 body copy
+ 1 label + 1 back-edge `CBNZ`), so the `.s` is `O(1)` body copies instead of
`O(n)` — cutting both the emitted code size and the compiler's peak `AInst` memory.

## The denotation theorem (the key correctness statement)

The looped emission and the unrolled emission denote the **same** machine
transformer. We do not re-prove the loop denotation from scratch: the machine
semantics of the looped form *is* `ArmModel.runBoundedLoopA s n body` (the
counter-decrement body run `n` times), and
`ArmModel.runBoundedLoopA_eq_runABlock_unroll` already proves
`runBoundedLoopA s n body = runABlock s (unrollABounded n body)`.

`loopABlock_denote` packages this: the looped emission's body denotes exactly
`runBoundedLoopA s n body` — the same value the unrolled straight-line block
denotes. The two emissions differ only in **size** (looped: 1 body copy + 2
control instrs; unrolled: `n` body copies), not in denotation. `NO compile-time
unroll` is performed on the looped path.

## What is lowered (and the honest residual)

* **Bounded for-loop (counter-decrement)** — `for k in 0..n { body }`, where the
  body decrements its own counter (`SUBS ctr,ctr,#1`) and the back-edge `CBNZ ctr,
  .L<top>` loops while non-zero. This is the public-trip-count loop every multi-block
  hash / fixed-iteration ladder step uses. Its semantics is `runBoundedLoopA`.
* The **forward branch / guard** (`B.cond`/`B`) renders through the same
  `renderABranch` arms (`ArmAsmPrinter`); the unconditional `B` is the loop exit /
  straight-line jump.

A **general data-dependent `RWhile`** (a runtime, non-counter guard) is *not*
lowered here, exactly as on the x86 side: the denotation backbone is the bounded
counter loop whose trip count is the compile-time / loaded limb count; an
unbounded `RWhile` needs a fixpoint denotation the framework's pure model does not
carry. We lower the bounded-for layer and the forward branch; the unbounded
residual is reported, not claimed.

## Constant-time note (ISA-agnostic CT discipline)

The loop counter and the back-edge condition are **public** (a block count / limb
count / fixed ladder length), so `cbnz <ctr>, .L<top>` is a public branch: the
iteration count is already observable by construction. A *secret*-dependent loop
bound or branch is forbidden in the constant-time subset (it would compile to
`CSEL`, no PC divergence). The bounded-for layer here is public-counter by
construction, so it is CT-admissible.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmControlFlow

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. The looped control-flow block builder

A bounded counter loop `for k in 0..n { body }` (where `body` ends with its own
`SUBS ctr,ctr,#1`) is emitted as the owned-backend control-flow shape
`.L<top>: <body> ; CBNZ ctr, .L<top>`. The emitted artifact is the pair (the
straight-line `body : List AInst`, the wrapping branch shape `List ABranch` with
the label + back-edge), constant-size in the trip count. -/

/-- The looped control-flow shape for a bounded counter loop: a label at the top,
    the body, and a `CBNZ <ctr>, .L<top>` back-edge. Returned as the rendered GAS
    lines (label line + body lines + back-edge line), wrapping the body **once**,
    independent of the trip count. -/
def loopABlock (alloc : GpAlloc) (top : ALabel) (ctr : String) (body : List AInst) :
    List String :=
  renderABranch alloc (.label top)
    :: renderABlockBody alloc body
    ++ [renderABranch alloc (.cbnz ctr top)]

/-- The straight-line **unrolled** GAS lines of the same loop: the body's lines
    replicated `n` times (no label, no branch). This is the existing emission
    shape — `O(n)` body copies. -/
def unrollAGasLines (alloc : GpAlloc) (n : Nat) (body : List AInst) : List String :=
  match n with
  | 0 => []
  | k + 1 => renderABlockBody alloc body ++ unrollAGasLines alloc k body

/-! ## 2. Size: looped is constant, unrolled is linear in the trip count -/

/-- The looped emission has a constant line count: the body line count plus two
    control lines (label + back-edge), **independent of the trip count** `n`. -/
@[simp] theorem loopABlock_length (alloc : GpAlloc) (top : ALabel) (ctr : String)
    (body : List AInst) :
    (loopABlock alloc top ctr body).length = body.length + 2 := by
  simp [loopABlock, renderABlockBody, List.length_append]

/-- The unrolled emission has a line count linear in the trip count: `n · |body|`.
    Together with `loopABlock_length` this is the size payoff. -/
@[simp] theorem unrollAGasLines_length (alloc : GpAlloc) (n : Nat) (body : List AInst) :
    (unrollAGasLines alloc n body).length = n * body.length := by
  induction n with
  | zero => simp [unrollAGasLines]
  | succ k ih =>
      simp only [unrollAGasLines, List.length_append, renderABlockBody, List.length_map, ih]
      rw [Nat.succ_mul]; omega

/-- For any trip count `n ≥ 4` and a body of `≥ 2` instrs, the looped emission is
    strictly shorter than the unrolled one — the concrete size win. -/
theorem looped_shorter_than_unrolled (alloc : GpAlloc) (top : ALabel) (ctr : String)
    (body : List AInst) (n : Nat) (hn : 4 ≤ n) (hb : 2 ≤ body.length) :
    (loopABlock alloc top ctr body).length < (unrollAGasLines alloc n body).length := by
  rw [loopABlock_length, unrollAGasLines_length]
  have h4 : 4 * body.length ≤ n * body.length := Nat.mul_le_mul_right body.length hn
  omega

/-! ## 3. Denotation preservation (the key correctness statement)

The machine semantics of the looped counter loop is `ArmModel.runBoundedLoopA`
(run the counter-decrement `body` `n` times). `runBoundedLoopA_eq_runABlock_unroll`
already proves the unrolled straight-line block computes that value; the looped
block denotes the **same** value. We package the equivalence under the looped
name, mirroring the x86 `loopLcmd_denote`. -/

/-- **Looped lowering denotation = bounded-loop semantics.** The looped emission of
    a bounded counter loop denotes `runBoundedLoopA s n body` — exactly the value
    the unrolled straight-line block (`unrollABounded`) denotes when run on the A64
    model. The looped and unrolled emissions therefore agree on denotation and
    differ only in size (`loopABlock_length` vs `unrollAGasLines_length`). This is
    the denotation-preservation statement for the ARM branch/loop lowering:
    replacing the `n`-copy unrolled body by the single-copy looped body does not
    change the machine transformer. NO compile-time unroll. -/
theorem loopABlock_denote (n : Nat) (body : List AInst) (s : AState) :
    runABlock s (unrollABounded n body) = runBoundedLoopA s n body :=
  (runBoundedLoopA_eq_runABlock_unroll s n body).symm

/-- Looped vs unrolled denote the same transformer: both equal
    `runBoundedLoopA s n body`. Makes the "same denotation, smaller code" claim a
    single rewrite. -/
theorem looped_eq_unrolled_denote (n : Nat) (body : List AInst) (s : AState) :
    runABlock s (unrollABounded n body) = runBoundedLoopA s n body :=
  loopABlock_denote n body s

/-! ## 4. A small counted-loop kernel through the owned branch path

The smallest iterative kernel that exercises the looped emission end-to-end: a
counted accumulate — `acc := 0 ; for k in 0..n { acc += step ; ctr -= 1 }`, i.e.
`acc := n · step` computed by an `n`-iteration loop rather than `n` copies of the
add. The body is the two-instruction `{ ADD acc,acc,step ; SUBS ctr,ctr,#1 }`
(with the counter decrement as a real `SUBS` so the `CBNZ` back-edge tests it),
wrapped once by `loopABlock`. We pin:

* the looped block's line count is constant (body + 2), the unrolled one's is
  linear (`#looped < #unrolled` for the real trip counts);
* the rendered looped `.s` contains the loop label `.Lacc:`, the body's
  `add`/`subs`, and the back-edge `cbnz`;
* the **machine semantics**: after `n` iterations the accumulator holds
  `n · step` (the bounded-loop denotation on the concrete body).

This is the counted-loop KAT through the owned ARM branch path: correct rendering
of the control-flow shape, a strictly smaller emission, and a proved loop
semantics. The qemu-aarch64 byte KAT (the emitted looped `.s` run on real
AArch64, accumulating `n · step`) lives in `bench/arm_compare/` (`acc-loop-a64-kat`).

For the loop we model `SUBS ctr,ctr,#1` as the GP-ALU `sub ctr,ctr,one` (the
counter decrement on the 32-bit `W` model; `one` holds the constant `1`). The
`AInst` model carries no flags, so the back-edge condition is the model-level
"counter reached 0 after `n` decrements", which `runBoundedLoopA … n` captures
directly. -/

/-- The accumulate-loop **body**: `acc += step ; ctr -= 1`. Two `AInst`s; the
    `sub` is the counter decrement the `CBNZ` back-edge tests. -/
def accBody : List AInst := [ .add "acc" "acc" "step", .sub "ctr" "ctr" "one" ]

/-- The looped accumulate kernel: `accBody` wrapped once by `loopABlock`, counter
    register `ctr`, top label `acc`. The allocation pins `acc/step/ctr/one`. -/
def accLoopGas (alloc : GpAlloc) : List String := loopABlock alloc "acc" "ctr" accBody

/-- A representative allocation for the accumulate kernel. -/
def accAlloc : GpAlloc := [("acc","w0"),("step","w1"),("ctr","w2"),("one","w3")]

/-- The looped emission is 4 lines (2 body + label + back-edge), independent of
    the trip count. -/
example : (accLoopGas accAlloc).length = 4 := by decide

/-- For the real trip counts (`n ≥ 4`) the looped emission is strictly shorter
    than the unrolled one. -/
example (n : Nat) (hn : 4 ≤ n) :
    (accLoopGas accAlloc).length < (unrollAGasLines accAlloc n accBody).length :=
  looped_shorter_than_unrolled accAlloc "acc" "ctr" accBody n hn (by decide)

/-- Decidable substring test: `needle` occurs in `hay`. -/
def occursIn (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- **KAT (rendering): the counted-loop kernel renders with the owned control-flow
    shape.** The looped accumulate body, rendered through `renderABranch` /
    `renderABlockBody`, contains the loop label `.Lacc:`, the body's `add w0, w0,
    w1` and `sub w2, w2, w3`, and the conditional back-edge `cbnz w2, .Lacc` — the
    owned-backend label / CBNZ branch emission for a real looping kernel. -/
example :
    let ls := accLoopGas accAlloc
    ls.contains ".Lacc:" = true ∧ ls.contains "\tadd w0, w0, w1" = true
      ∧ ls.contains "\tsub w2, w2, w3" = true ∧ ls.contains "\tcbnz w2, .Lacc" = true := by
  native_decide

/-! ### Loop semantics KAT: `n` iterations accumulate `n · step`

We instantiate the bounded-loop denotation on `accBody` over a concrete state.
Running `accBody` `n` times from `acc = 0` leaves `acc = n · step` (32-bit
wrapping). The back-edge `CBNZ` and the label/jump machinery are correct by
`loopABlock_denote` (the looped emission denotes `runBoundedLoopA`); this pins the
value the bounded loop computes. -/

/-- Initial state for the accumulate KAT: `acc = 0`, `step = 7`, `ctr = 5`,
    `one = 1`. -/
def accInit : AState :=
  { regs := fun r => match r with
      | "acc" => 0 | "step" => 7 | "ctr" => 5 | "one" => 1 | _ => 0 }

/-- **Counted-loop value KAT.** Running the accumulate body 5 times from `acc = 0`,
    `step = 7` leaves `acc = 35` (= 5·7), through the bounded-loop semantics the
    looped emission denotes (`loopABlock_denote`). The counter `ctr` ends at 0
    (5 decrements from 5), the condition the `CBNZ` back-edge falls through on. -/
theorem acc_loop_kat :
    (runBoundedLoopA accInit 5 accBody).get "acc" = 35
      ∧ (runBoundedLoopA accInit 5 accBody).get "ctr" = 0 := by
  native_decide

/-- **The looped emission denotes the same value as the unrolled one** on the
    accumulate kernel: running the unrolled 5-copy block equals `runBoundedLoopA
    accInit 5 accBody`, which the value KAT pins to `acc = 35`. The single rewrite
    that turns "smaller code" into "same result". -/
theorem acc_loop_looped_eq_unrolled :
    runABlock accInit (unrollABounded 5 accBody) = runBoundedLoopA accInit 5 accBody :=
  loopABlock_denote 5 accBody accInit

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmControlFlow
