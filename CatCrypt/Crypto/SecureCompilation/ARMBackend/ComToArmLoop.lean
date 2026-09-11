/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmX25519FieldKernel

/-!
# Composing the bounded loop with the scalar waist (`Com → AArch64`)

The straight-line scalar waist gives, for any backend, that the compiled-and-lowered
`RegProg` block computes the source denotation:

* `ScalarLin.ScalarTarget.compile_denote` — generic keystone, proved once;
* `ComToArm.regToBOp_denote` — its AArch64 instance,
  `runBBlock s (lowerBBlock (regToBOp p)) = armTarget.denote p s`.

The control-flow layer gives the bounded counter loop, proved equal to the unrolled
block, *generically in the loop `body`*:

* `ArmX25519FieldKernel.runBoundedLoopB_eq_runBBlock_unroll`.

These two layers live over the **same** `BState`/`runBBlock`, but the loop lemma's
`body` was an opaque `List BInst` — so they were never combined into one statement.
This file closes that gap. Instantiating the loop body with the waist-compiled block
`lowerBBlock (regToBOp p)`, an `n`-trip bounded loop denotes exactly the `n`-fold
iteration of the **source** program's denotation `armTarget.denote p`. That is the
whole-kernel (loop ∘ waist) correctness statement: machine-level looping over the
compiled+lowered block agrees with iterating the source block semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLoop

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.ScalarLin

/-- `n`-fold iteration of a `BState` transformer: the source-level meaning of an
    `n`-trip loop whose body denotes `f`. (Self-contained; the minimal-Mathlib ARM
    closure does not carry the `Function.iterate`/`^[·]` API.) -/
def iterTimes (f : BState → BState) : Nat → BState → BState
  | 0, s => s
  | k + 1, s => iterTimes f k (f s)

/-- **Loop ∘ waist composition.** An `n`-trip bounded counter loop whose body is the
    waist-compiled, lowered scalar block `lowerBBlock (regToBOp p)` denotes the
    `n`-fold iteration of the source program's denotation `armTarget.denote p`.

    This is the previously-missing glue: `ScalarTarget.compile_denote` (the
    straight-line waist) composed with `runBoundedLoopB_eq_runBBlock_unroll`
    (loop = unrolled block), over the shared `BState`/`runBBlock`. Each trip the
    machine runs the lowered block and the source semantics applies `armTarget.denote p`
    once; `n` trips iterate it `n` times. -/
theorem loop_waist_denote (p : RegProg) (n : Nat) (s : BState) :
    runBoundedLoopB s n (lowerBBlock (regToBOp p))
      = iterTimes (fun st => armTarget.denote p st) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [runBoundedLoopB_succ, regToBOp_denote, ih]; rfl

/-- The same fact phrased through the *bytes-faithful* unrolled block: running the
    `n`-copy unrolled compiled block is the `n`-fold source iteration. Bridges the
    constant-size looped emission (`runBoundedLoopB`) and the `O(n)` unrolled block
    (`unrollBBounded`, the form the encoder emits) to one source-level value. -/
theorem unrolled_waist_denote (p : RegProg) (n : Nat) (s : BState) :
    runBBlock s (unrollBBounded n (lowerBBlock (regToBOp p)))
      = iterTimes (fun st => armTarget.denote p st) n s := by
  rw [← runBoundedLoopB_eq_runBBlock_unroll, loop_waist_denote]

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArmLoop
