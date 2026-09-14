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

A loop is the model instruction `RLoop` (top label, counter register, body), whose
rendering `RLoop.render` is `loopRBlock`: the label line, the body lines and the
`BNE <ctr>, zero, .L<top>` line. Its semantics `runRLoop fuel s l` executes the
rendered control flow with at most `fuel` passes: run the body, stop when the
counter register reads `0`, otherwise branch back to the label. The proved facts
are:

* `loopRBlock_length` / `unrollRGasLines_length` / `looped_shorter_than_unrolled`:
  line counts of the two renderings;
* `looped_eq_unrolled_denote`: if every run of the body decrements the counter
  register by one (under an invariant `P` the body preserves), and the counter
  holds `n` with `1 ≤ n < 2^32`, then with fuel at least `n` the loop terminates
  in the state of the unrolled block `unrollRBounded n body`;
* `loopRBlock_denote`: the same final state is `runBoundedLoopR s n body`;
* `acc_loop_looped_eq_unrolled`: the accumulate kernel with counter `5` runs to the
  state of its unrolled 5-copy block.

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

/-! ## 3. The loop as a model instruction and its execution

`RLoop` is the counted loop the renderer prints as `loopRBlock`. `runRLoop` runs
that control flow: the body falls through to the `BNE`, which branches back to
the label while the counter register is non-zero. The fuel bounds the number of
passes; `none` means the fuel ran out. -/

/-- A counted loop: the label `top`, the counter register `ctr` tested by the
    back-edge, and the body. -/
structure RLoop where
  /-- The loop label. -/
  top : RLabel
  /-- The register the `BNE` back-edge compares with `zero`. -/
  ctr : String
  /-- The loop body. -/
  body : List RInst

/-- The GAS lines of a loop: label, body, `BNE ctr, zero, .L<top>`. -/
def RLoop.render (alloc : GpAlloc) (l : RLoop) : List String :=
  loopRBlock alloc l.top l.ctr l.body

/-- Execution of a loop with at most `fuel` passes: run the body; if the counter
    register then reads `0`, fall through with that state, otherwise take the
    back-edge. -/
def runRLoop (fuel : Nat) (s : RState) (l : RLoop) : Option RState :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if (runRBlock s l.body).get l.ctr = 0 then some (runRBlock s l.body)
    else runRLoop f (runRBlock s l.body) l

/-- **The looped emission computes the unrolled block.** Let the body decrement the
    counter register by one on every state satisfying an invariant `P` that it
    preserves. From a state satisfying `P` whose counter holds `n`, with
    `1 ≤ n < 2^32` and fuel at least `n`, the loop terminates in the state reached
    by the unrolled block `unrollRBounded n l.body`. -/
theorem looped_eq_unrolled_denote (P : RState → Prop) (l : RLoop)
    (hdec : ∀ s, P s → P (runRBlock s l.body) ∧
      (runRBlock s l.body).get l.ctr = s.get l.ctr - 1) :
    ∀ (n fuel : Nat) (s : RState), P s → 1 ≤ n → n < 2 ^ 32 →
      s.get l.ctr = BitVec.ofNat 32 n → n ≤ fuel →
      runRLoop fuel s l = some (runRBlock s (unrollRBounded n l.body)) := by
  intro n
  induction n with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
    intro fuel s hP _ hlt hctr hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hP', hc⟩ := hdec s hP
    rw [hctr] at hc
    have hc' : (runRBlock s l.body).get l.ctr = BitVec.ofNat 32 k := by
      rw [hc]; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub]; omega
    simp only [runRLoop, unrollRBounded, runRBlock_append_model]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos (by rw [hc']; rfl)]
      rfl
    · rw [if_neg (by rw [hc']; intro h; have := congrArg BitVec.toNat h; simp at this; omega)]
      exact ih f _ hP' (by omega) (by omega) hc' (by omega)

/-- Under the hypotheses of `looped_eq_unrolled_denote`, the loop terminates in
    `runBoundedLoopR s n l.body`, the body run `n` times. -/
theorem loopRBlock_denote (P : RState → Prop) (l : RLoop)
    (hdec : ∀ s, P s → P (runRBlock s l.body) ∧
      (runRBlock s l.body).get l.ctr = s.get l.ctr - 1)
    (n fuel : Nat) (s : RState) (hP : P s) (hn : 1 ≤ n) (hlt : n < 2 ^ 32)
    (hctr : s.get l.ctr = BitVec.ofNat 32 n) (hfuel : n ≤ fuel) :
    runRLoop fuel s l = some (runBoundedLoopR s n l.body) := by
  rw [looped_eq_unrolled_denote P l hdec n fuel s hP hn hlt hctr hfuel,
    runBoundedLoopR_eq_runRBlock_unroll]

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

The rendering checks are substring tests on the emitted lines. The value check is
on `runBoundedLoopR`; `acc_loop_looped_eq_unrolled` transfers it to the loop
`accLoop` executed by `runRLoop`. Execution of the emitted `.s` on hardware is not
checked in this package.

The counter decrement is `SUBW ctr,ctr,one` with `one` holding `1`
(`accBody_dec`); `BNE` compares the register value with `zero`. -/

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

/-- The accumulate kernel as a loop: label `acc`, counter `ctr`, body `accBody`. -/
def accLoop : RLoop := { top := "acc", ctr := "ctr", body := accBody }

/-- The rendering of `accLoop` is `accLoopGas`. -/
theorem accLoop_render (alloc : GpAlloc) : accLoop.render alloc = accLoopGas alloc := rfl

/-- On states with `one = 1`, `accBody` keeps `one = 1` and decrements `ctr`. -/
theorem accBody_dec (s : RState) (h : s.get "one" = 1) :
    (runRBlock s accBody).get "one" = 1 ∧
      (runRBlock s accBody).get "ctr" = s.get "ctr" - 1 := by
  have hnil : ∀ t : RState, runRBlock t [] = t := fun _ => rfl
  simp only [accBody, runRBlock_cons, evalRInst, hnil]
  refine ⟨?_, ?_⟩
  · rw [RState.get_set_other _ _ _ _ (by decide), RState.get_set_other _ _ _ _ (by decide), h]
  · rw [RState.get_set_same _ _ _ (by decide), RState.get_set_other _ _ _ _ (by decide),
      RState.get_set_other _ _ _ _ (by decide), h]
    rfl

/-- **The accumulate loop runs to its unrolled block.** Executing `accLoop` from
    `accInit` (counter `5`) with fuel `5` terminates in the state of the unrolled
    5-copy block. -/
theorem acc_loop_looped_eq_unrolled :
    runRLoop 5 accInit accLoop = some (runRBlock accInit (unrollRBounded 5 accBody)) :=
  looped_eq_unrolled_denote (fun s => s.get "one" = 1) accLoop (fun s h => accBody_dec s h)
    5 5 accInit rfl (by decide) (by decide) rfl (Nat.le_refl 5)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvControlFlow
