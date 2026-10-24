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
# Looped (non-unrolled) control-flow lowering for the owned AArch64 backend

`ArmLowering.lean` lowers a straight-line `AOp` block to the A64
machine `AInst`s with `armBlock_lowering_denote`; `ArmSha256Kernel.lean`
uses that for the 64-round SHA-256 compression. A straight-line lowering emits an
`n`-iteration loop as an `n`-copy `AInst` block, so the `.s` grows linearly in the
trip count.

This module is the **AArch64 analogue of the x86 owned-backend loop emission**
(`X86Backend/LprogControlFlow.lean`): a bounded counter loop is emitted as a
single body copy wrapped in an A64 back-edge

```
   .L<top>:
       <body>                  -- the per-iteration AInst body (incl. its ctr -= 1)
       cbnz   <ctr>, .L<top>   -- back-edge: loop while ctr ≠ 0
```

The emitted control-flow block is **constant-size** in the trip count (1 body copy
+ 1 label + 1 back-edge `CBNZ`), so the `.s` is `O(1)` body copies instead of
`O(n)` — cutting both the emitted code size and the compiler's peak `AInst` memory.

## What is proved about the loop

A loop is the model instruction `ALoop` (top label, counter register, body), whose
rendering `ALoop.render` is `loopABlock`: the label line, the body lines and the
`CBNZ <ctr>, .L<top>` line. Its semantics `runALoop fuel s l` executes the rendered
control flow with at most `fuel` passes: run the body, stop when the counter
register reads `0`, otherwise branch back to the label. The proved facts are:

* `loopABlock_length` / `unrollAGasLines_length` / `looped_shorter_than_unrolled`:
  line counts of the two renderings;
* `looped_eq_unrolled_denote`: if every run of the body decrements the counter
  register by one (under an invariant `P` the body preserves), and the counter
  holds `n` with `1 ≤ n < 2^32`, then with fuel at least `n` the loop terminates
  in the state of the unrolled block `unrollABounded n body`;
* `loopABlock_denote`: the same final state is `runBoundedLoopA s n body`;
* `acc_loop_looped_eq_unrolled`: the accumulate kernel with counter `5` runs to the
  state of its unrolled 5-copy block.

## What is lowered

* **Bounded for-loop (counter-decrement)** — `for k in 0..n { body }`, where the
  body decrements its own counter (`SUBS ctr,ctr,#1`) and the back-edge `CBNZ ctr,
  .L<top>` loops while non-zero. This is the public-trip-count loop every multi-block
  hash / fixed-iteration ladder step uses. Its semantics is `runBoundedLoopA`.
* The **forward branch / guard** (`B.cond`/`B`) renders through the same
  `renderABranch` arms (`ArmAsmPrinter`); the unconditional `B` is the loop exit /
  straight-line jump.

A **general data-dependent `RWhile`** (a runtime, non-counter guard) is *not*
lowered here, as on the x86 side: the loop semantics used is the bounded counter
loop whose trip count is the compile-time / loaded limb count; an unbounded
`RWhile` needs a fixpoint denotation the framework's pure model does not carry.

## Constant-time note

The loop counter and the back-edge condition are intended to be **public** (a
block count / limb count / fixed ladder length), so `cbnz <ctr>, .L<top>` branches
on public data only. A *secret*-dependent loop bound or branch is outside the
constant-time subset. No theorem in this module states a constant-time property.
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

/-! ## 3. The loop as a model instruction and its execution

`ALoop` is the counted loop the renderer prints as `loopABlock`. `runALoop` runs
that control flow: the body falls through to the `CBNZ`, which branches back to
the label while the counter register is non-zero. The fuel bounds the number of
passes; `none` means the fuel ran out. -/

/-- A counted loop: the label `top`, the counter register `ctr` tested by the
    back-edge, and the body. -/
structure ALoop where
  /-- The loop label. -/
  top : ALabel
  /-- The register the `CBNZ` back-edge tests. -/
  ctr : String
  /-- The loop body. -/
  body : List AInst

/-- The GAS lines of a loop: label, body, `CBNZ ctr, .L<top>`. -/
def ALoop.render (alloc : GpAlloc) (l : ALoop) : List String :=
  loopABlock alloc l.top l.ctr l.body

/-- Execution of a loop with at most `fuel` passes: run the body; if the counter
    register then reads `0`, fall through with that state, otherwise take the
    back-edge. -/
def runALoop (fuel : Nat) (s : AState) (l : ALoop) : Option AState :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if (runABlock s l.body).get l.ctr = 0 then some (runABlock s l.body)
    else runALoop f (runABlock s l.body) l

/-- **The looped emission computes the unrolled block.** Let the body decrement the
    counter register by one on every state satisfying an invariant `P` that it
    preserves. From a state satisfying `P` whose counter holds `n`, with
    `1 ≤ n < 2^32` and fuel at least `n`, the loop terminates in the state reached
    by the unrolled block `unrollABounded n l.body`. -/
theorem looped_eq_unrolled_denote (P : AState → Prop) (l : ALoop)
    (hdec : ∀ s, P s → P (runABlock s l.body) ∧
      (runABlock s l.body).get l.ctr = s.get l.ctr - 1) :
    ∀ (n fuel : Nat) (s : AState), P s → 1 ≤ n → n < 2 ^ 32 →
      s.get l.ctr = BitVec.ofNat 32 n → n ≤ fuel →
      runALoop fuel s l = some (runABlock s (unrollABounded n l.body)) := by
  intro n
  induction n with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
    intro fuel s hP _ hlt hctr hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hP', hc⟩ := hdec s hP
    rw [hctr] at hc
    have hc' : (runABlock s l.body).get l.ctr = BitVec.ofNat 32 k := by
      rw [hc]; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub]; omega
    simp only [runALoop, unrollABounded, runABlock_append]
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left (by rw [hc']; rfl)]
      rfl
    · rw [ite_eq_right (by rw [hc']; intro h; have := congrArg BitVec.toNat h; simp at this; omega)]
      exact ih f _ hP' (by omega) (by omega) hc' (by omega)

/-- Under the hypotheses of `looped_eq_unrolled_denote`, the loop terminates in
    `runBoundedLoopA s n l.body`, the body run `n` times. -/
theorem loopABlock_denote (P : AState → Prop) (l : ALoop)
    (hdec : ∀ s, P s → P (runABlock s l.body) ∧
      (runABlock s l.body).get l.ctr = s.get l.ctr - 1)
    (n fuel : Nat) (s : AState) (hP : P s) (hn : 1 ≤ n) (hlt : n < 2 ^ 32)
    (hctr : s.get l.ctr = BitVec.ofNat 32 n) (hfuel : n ≤ fuel) :
    runALoop fuel s l = some (runBoundedLoopA s n l.body) := by
  rw [looped_eq_unrolled_denote P l hdec n fuel s hP hn hlt hctr hfuel,
    runBoundedLoopA_eq_runABlock_unroll]

/-! ## 4. A small counted-loop kernel through the owned branch path

A small iterative kernel for the looped emission: a
counted accumulate — `acc := 0 ; for k in 0..n { acc += step ; ctr -= 1 }`, i.e.
`acc := n · step` computed by an `n`-iteration loop rather than `n` copies of the
add. The body is the two-instruction `{ ADD acc,acc,step ; SUBS ctr,ctr,#1 }`
(with the counter decrement as a real `SUBS` so the `CBNZ` back-edge tests it),
wrapped once by `loopABlock`. We pin:

* the looped block's line count is constant (body + 2), the unrolled one's is
  linear (`#looped < #unrolled` for the real trip counts);
* the rendered looped `.s` contains the loop label `.Lacc:`, the body's
  `add`/`subs`, and the back-edge `cbnz`;
* on the model: `runBoundedLoopA` of the body, from `acc = 0`, `step = 7`,
  `ctr = 5`, leaves `acc = 35` and `ctr = 0` after 5 iterations.

The rendering checks are substring tests on the emitted lines. The value check is
on `runBoundedLoopA`; `acc_loop_looped_eq_unrolled` transfers it to the loop
`accLoop` executed by `runALoop`. Execution of the emitted `.s` on hardware is not
checked in this package.

The counter decrement `SUBS ctr,ctr,#1` is modelled as `sub ctr,ctr,one` with `one`
holding `1` (`accBody_dec`). The `AInst` model carries no flags; `CBNZ` tests the
register value. -/

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
wrapping); the check below is at `n = 5`. It concerns `runBoundedLoopA`, not the
rendered `CBNZ` loop, whose execution has no model here. -/

/-- Initial state for the accumulate KAT: `acc = 0`, `step = 7`, `ctr = 5`,
    `one = 1`. -/
def accInit : AState :=
  { regs := fun r => match r with
      | "acc" => 0 | "step" => 7 | "ctr" => 5 | "one" => 1 | _ => 0 }

/-- **Counted-loop value KAT.** Running the accumulate body 5 times from `acc = 0`,
    `step = 7` leaves `acc = 35` (= 5·7) under `runBoundedLoopA`. The counter
    `ctr` ends at 0 (5 decrements from 5). -/
theorem acc_loop_kat :
    (runBoundedLoopA accInit 5 accBody).get "acc" = 35
      ∧ (runBoundedLoopA accInit 5 accBody).get "ctr" = 0 := by
  native_decide

/-- The accumulate kernel as a loop: label `acc`, counter `ctr`, body `accBody`. -/
def accLoop : ALoop := { top := "acc", ctr := "ctr", body := accBody }

/-- The rendering of `accLoop` is `accLoopGas`. -/
theorem accLoop_render (alloc : GpAlloc) : accLoop.render alloc = accLoopGas alloc := rfl

/-- On states with `one = 1`, `accBody` keeps `one = 1` and decrements `ctr`. -/
theorem accBody_dec (s : AState) (h : s.get "one" = 1) :
    (runABlock s accBody).get "one" = 1 ∧
      (runABlock s accBody).get "ctr" = s.get "ctr" - 1 := by
  simp only [accBody, runABlock_cons, runABlock_nil, evalAInst]
  refine ⟨?_, ?_⟩
  · rw [AState.get_set_other _ _ _ _ (by decide), AState.get_set_other _ _ _ _ (by decide), h]
  · rw [AState.get_set_same _ _ _ (by decide), AState.get_set_other _ _ _ _ (by decide),
      AState.get_set_other _ _ _ _ (by decide), h]
    rfl

/-- **The accumulate loop runs to its unrolled block.** Executing `accLoop` from
    `accInit` (counter `5`) with fuel `5` terminates in the state of the unrolled
    5-copy block. -/
theorem acc_loop_looped_eq_unrolled :
    runALoop 5 accInit accLoop = some (runABlock accInit (unrollABounded 5 accBody)) :=
  looped_eq_unrolled_denote (fun s => s.get "one" = 1) accLoop (fun s h => accBody_dec s h)
    5 5 accInit rfl (by decide) (by decide) rfl (Nat.le_refl 5)

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmControlFlow
