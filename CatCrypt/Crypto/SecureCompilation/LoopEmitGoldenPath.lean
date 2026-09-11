/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLoop

/-!
# Golden path for an ITERATED kernel: a bounded accumulate loop, emitted by the compiler

The straight-line golden path (`FieldEmitGoldenPath.lean`) writes a field op ONCE as a
`Com jasminDialect` source, proves `Com.denote = <value spec>` once, and the verified
compiler emits the machine block with no per-kernel backend proof. This file is the
**loop** analogue: an *iterated* kernel — the same compiled body run `n` times by the
verified bounded-counter loop — with the whole loop proven to compute a recognizable
*mathematical* spec (not a restatement of its own `denote`).

The loop machinery already exists and is proved generically:

* `ComToArm.regToBOp` / `ComToArm.armTarget` — the AArch64 `ScalarTarget` instance: a
  source `RegProg` compiles to a `BOp` block whose lowered machine run computes the
  source denotation `armTarget.denote p` (`ComToArm.regToBOp_denote`, the straight-line
  waist keystone, proved once);
* `ComToArmLoop.loop_waist_denote` — the **loop ∘ waist** keystone: an `n`-trip bounded
  counter loop whose body is the compiled+lowered block `lowerBBlock (regToBOp p)`
  denotes the `n`-fold iteration `iterTimes (armTarget.denote p) n` of the source
  semantics, for **every** trip count `n`. No new per-loop backend proof.

## What this file adds (the genuine, non-vacuous content)

We instantiate the generic loop keystone on a concrete, recognizable iterated kernel:
the single-statement accumulate body `acc := acc + step` (`accStepProg`, one
`RegStmt.add` — the iterated step of a sum/scalar-multiply). Two facts are then proved:

1. `accLoop_denote` (a direct corollary of `loop_waist_denote`): the compiled+lowered
   accumulate body, run as an `n`-trip bounded loop, denotes `iterTimes (armTarget.denote
   accStepProg) n s` — emitted by the verified compiler, no per-loop backend proof.

2. `accLoop_spec` — the **recognizable mathematical spec**: provided the accumulator and
   step registers are distinct (and the accumulator is a real register, not `xzr`),
   running the emitted bounded loop `n` times from a state `s` yields, in the `acc`
   register, exactly `s.get acc + n • s.get step` — i.e. `acc + n · step`, the closed
   form of an `n`-fold accumulate. This is the actual iterated function (a scalar
   multiply by the iteration count), NOT a restatement of the loop's own `denote`.

So the golden path emits a genuinely iterated kernel: one compiled body, the verified
loop wraps it, and the whole loop is pinned to `acc + n·step` for every `n`.

## Honest scope

* **Covered**: the *control-flow + waist composition* end to end — the compiled,
  lowered accumulate body, run by the verified bounded-counter loop semantics
  (`runBoundedLoopB`), computes the closed-form scalar-multiply value `acc + n·step`
  for every `n`, with no per-loop backend proof (it rides `loop_waist_denote`, the
  AArch64 `ScalarTarget` keystone, and the loop-unroll equality).
* **Not claimed here**: the byte-level encoder round-trip (`encodeBBlock`) and the
  *constant-emitted-size* looped back-edge (`loopABlock`/`CBNZ`) are the encoder /
  control-flow-emission layers proved elsewhere (`ArmEncoder`, `ArmControlFlow`,
  `ArmX25519FieldKernel.runBoundedLoopB_eq_runBBlock_unroll`); this file proves the
  *denotational value* the loop computes, which is the part the spec pins.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.LoopEmit

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLoop
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.ScalarLin

/-! ## 1. The iterated kernel source: the accumulate step `acc := acc + step` -/

/-- **The loop body source.** The one-statement accumulate `acc := acc + step` as a
    `RegProg` (the `regArith` straight-line waist the field leaves use). Iterating it
    `n` times is the `n`-fold accumulate — `acc += step` repeated, i.e. the running sum
    / scalar multiply step. The compiler emits this body; the bounded-counter loop runs
    it `n` times. -/
def accStepProg (acc step : String) : RegProg := [RegStmt.add acc acc step]

/-- The source effect of one accumulate step on the AArch64 register state:
    `acc := acc + step`. A direct unfold of `armTarget.denote` on the one-statement
    program. -/
theorem accStep_denote (acc step : String) (s : BState) :
    armTarget.denote (accStepProg acc step) s
      = s.set acc (s.get acc + s.get step) := rfl

/-! ## 2. A register-disjointness helper (local, self-contained) -/

/-- A write to a *different* register leaves the read unchanged. (Proved locally so the
    file depends only on the loop keystone import.) -/
theorem get_set_ne (s : BState) (r r' : String) (v : X64) (h : r ≠ r') :
    (s.set r' v).get r = s.get r := by
  by_cases hr' : r' = "xzr"
  · simp [BState.set, hr']
  · simp [BState.set, BState.get, hr', h]

/-! ## 3. The closed form of the `n`-fold accumulate

Iterating `acc := acc + step` `n` times, when `acc ≠ step` and `acc ≠ "xzr"`, sets `acc`
to `acc₀ + n · step` (a `BitVec` multiply by the trip count) and leaves `step` untouched.
This is the recognizable mathematical spec — a scalar multiply by the iteration count —
proved by induction on `n`. -/

/-- **The iterated-accumulate closed form.** With distinct accumulator/step registers
    (`acc ≠ step`) and a real accumulator (`acc ≠ "xzr"`), the `n`-fold iteration of the
    source accumulate step reads back `acc₀ + (n · step₀)` in `acc` (and leaves `step`
    unchanged), where `n · step₀ = BitVec.ofNat 64 n * step₀` is the 64-bit multiply of
    the trip count by the step — the closed form of `acc` incremented by `step` exactly
    `n` times. -/
theorem iter_accStep_spec (acc step : String) (hne : acc ≠ step) (hacc : acc ≠ "xzr")
    (n : Nat) (s : BState) :
    ((iterTimes (fun st => armTarget.denote (accStepProg acc step) st) n s).get acc
        = s.get acc + BitVec.ofNat 64 n * s.get step)
      ∧ ((iterTimes (fun st => armTarget.denote (accStepProg acc step) st) n s).get step
        = s.get step) := by
  induction n generalizing s with
  | zero => simp [iterTimes]
  | succ k ih =>
      simp only [iterTimes]
      have hstep : (armTarget.denote (accStepProg acc step) s).get step = s.get step := by
        rw [accStep_denote]; exact get_set_ne s step acc _ (Ne.symm hne)
      have hacc' : (armTarget.denote (accStepProg acc step) s).get acc
          = s.get acc + s.get step := by
        rw [accStep_denote]; exact BState.get_set_same s acc _ hacc
      refine ⟨?_, ?_⟩
      · rw [(ih (armTarget.denote (accStepProg acc step) s)).1, hacc', hstep]
        have hk1 : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
          simp [BitVec.ofNat_add]
        rw [hk1, BitVec.add_mul]
        rw [show (1 : BitVec 64) * s.get step = s.get step from by simp]
        rw [BitVec.add_assoc, BitVec.add_comm (s.get step)]
      · rw [(ih (armTarget.denote (accStepProg acc step) s)).2, hstep]

/-! ## 4. The emitted iterated kernel: the verified bounded loop over the compiled body -/

/-- **The iterated kernel is emitted by the verified compiler.** The accumulate body is
    compiled (`regToBOp`) and lowered (`lowerBBlock`); the verified bounded-counter loop
    runs it `n` times. By the loop ∘ waist keystone the whole loop denotes the `n`-fold
    iteration of the source semantics — no per-loop backend proof. -/
theorem accLoop_denote (acc step : String) (n : Nat) (s : BState) :
    runBoundedLoopB s n (lowerBBlock (regToBOp (accStepProg acc step)))
      = iterTimes (fun st => armTarget.denote (accStepProg acc step) st) n s :=
  loop_waist_denote (accStepProg acc step) n s

/-- **The iterated-kernel value spec (the headline).** Running the *compiler-emitted,
    lowered* accumulate loop body for `n` trips of the verified bounded-counter loop
    reads back, in the accumulator, exactly `acc₀ + n • step₀` — the closed form of an
    `n`-fold accumulate (a scalar multiply by the trip count). This is the loop analogue
    of `FieldEmitGoldenPath.fieldAddCom_arm_e2e`: the whole *iterated* emitted kernel
    pinned to a recognizable mathematical spec, for every `n`, with no per-loop backend
    proof (it composes `accLoop_denote` — the loop ∘ waist keystone — with the
    closed-form `iter_accStep_spec`). -/
theorem accLoop_spec (acc step : String) (hne : acc ≠ step) (hacc : acc ≠ "xzr")
    (n : Nat) (s : BState) :
    (runBoundedLoopB s n (lowerBBlock (regToBOp (accStepProg acc step)))).get acc
      = s.get acc + BitVec.ofNat 64 n * s.get step := by
  rw [accLoop_denote]
  exact (iter_accStep_spec acc step hne hacc n s).1

/-- A worked instantiation: `acc := "x0"`, `step := "x1"`. The emitted `n`-trip loop
    leaves `x0 = x0₀ + (n · x1₀)`. (`decide` discharges the register-distinctness side
    conditions.) -/
theorem accLoop_spec_x0_x1 (n : Nat) (s : BState) :
    (runBoundedLoopB s n (lowerBBlock (regToBOp (accStepProg "x0" "x1")))).get "x0"
      = s.get "x0" + BitVec.ofNat 64 n * s.get "x1" :=
  accLoop_spec "x0" "x1" (by decide) (by decide) n s

end CatCrypt.Crypto.SecureCompilation.LoopEmit
