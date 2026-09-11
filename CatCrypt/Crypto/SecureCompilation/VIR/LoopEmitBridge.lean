/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# The loop-emit correctness bridge — emitted back-edge loop = verified `scfRepeat`

This module connects the **abstract verified loop combinator** `scfRepeat`
(from `StructuredControlFlow`, which proves `scfRepeat n step = step^[n]`) to the
**emitted machine back-edge loop** `runBoundedLoop` (the actual
`loopLcmd`/`bne`-back-edge the owned x86 backend emits, whose lowering
`LprogControlFlow.loopLcmd_denote` denotes `runBoundedLoop`).

The owned backend lowers a bounded counter loop `while (n != 0) { body ; n -= 1 }`
to a single body copy wrapped in a `Llabel … ; body ; CMP n,#0 ; jne .L`
back-edge (`LprogControlFlow.loopLcmd`); the *machine semantics* of that emitted
loop is `LoopUnroll.runBoundedLoop s n body` — the body run `n` times, threading
the `JState`. The verified control-flow layer, on the other hand, models a
bounded counted loop as `StructuredControlFlow.scfRepeat n step` over an abstract
state and proves it is the `n`-fold iterate `step^[n]` of its body.

This file proves they are the **same** under the obvious identification of the
emitted body's single-iteration step:

```
bodyStep body : JState w → JState w := fun s => runBlock s body
```

i.e. one machine iteration is running the straight-line body block once. Both
`runBoundedLoop` and `scfRepeat` then fold `bodyStep body` exactly `n` times.

## Results

* `runBoundedLoop_eq_scfRepeat` — `runBoundedLoop s n body = scfRepeat n (bodyStep body) s`:
  the emitted machine loop *is* the verified `scfRepeat` combinator applied to the
  body's single-iteration step.
* `runBoundedLoop_eq_iterate` — `runBoundedLoop s n body = (bodyStep body)^[n] s`:
  the clean "machine loop = `n`-fold application of the body" corollary, via
  `scfRepeat_eq_iterate`.
* `loopEmit_denote_iterate` — the **headline**: the *emitted* looped back-edge
  lowering denotes the `n`-fold iterate of its body,
  `(lowerBoundedLoop n body).denote (.cons s .nil) = (bodyStep body)^[n] s`,
  chaining `LprogControlFlow.loopLcmd_denote` with the above. This ties the
  emitted machine loop directly to the verified control-flow combinator.

The body step `bodyStep body` is a *front* fold in `runBoundedLoop`
(`runBoundedLoop (k+1) = runBoundedLoop ∘ runBlock`), matching `Function.iterate`'s
front recursion `f^[k+1] x = f^[k] (f x)`; `scfRepeat` end-unrolls but is proved
equal to the iterate, so all three agree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LoopEmitBridge

open CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-- The single machine iteration of the emitted back-edge loop: run the
    straight-line body block `body` once over the `JState`. This is the
    body-step the emitted `runBoundedLoop` folds `n` times, and the function the
    verified `scfRepeat`/`Function.iterate` combinators iterate. -/
def bodyStep {w : Nat} (body : List (JInstr w)) : JState w → JState w :=
  fun s => runBlock s body

/-- **The emitted machine loop is the verified `scfRepeat` combinator.**
    `runBoundedLoop s n body = scfRepeat n (bodyStep body) s`: the owned
    backend's bounded back-edge loop (machine semantics `runBoundedLoop`) is
    exactly the abstract counted-loop combinator `scfRepeat` applied to the
    body's single-iteration step `bodyStep body`. Proved by aligning both with
    `Function.iterate` (each folds the body step `n` times). -/
theorem runBoundedLoop_eq_scfRepeat {w : Nat} (s : JState w) (n : Nat)
    (body : List (JInstr w)) :
    runBoundedLoop s n body = scfRepeat n (bodyStep body) s := by
  rw [scfRepeat_eq_iterate]
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [runBoundedLoop_succ, Function.iterate_succ, Function.comp_apply, ih]
    rfl

/-- **Machine loop = `n`-fold application of the body.**
    `runBoundedLoop s n body = (bodyStep body)^[n] s`. The clean corollary via
    `scfRepeat_eq_iterate`: the emitted bounded loop is the `n`-th iterate of the
    single-iteration body step. -/
theorem runBoundedLoop_eq_iterate {w : Nat} (s : JState w) (n : Nat)
    (body : List (JInstr w)) :
    runBoundedLoop s n body = (bodyStep body)^[n] s := by
  rw [runBoundedLoop_eq_scfRepeat, scfRepeat_eq_iterate]

/-- **Headline: the emitted looped back-edge denotes the `n`-fold iterate of its
    body.** Chaining `LprogControlFlow.loopLcmd_denote` (the emitted looped
    lowering denotes `runBoundedLoop`) with `runBoundedLoop_eq_iterate`:

    `(lowerBoundedLoop n body).denote (.cons s .nil) = (bodyStep body)^[n] s`.

    This ties the EMITTED machine back-edge loop (the actual `Llabel … ; body ;
    CMP ; jne .L` shape the owned backend renders) to the verified control-flow
    combinator — the emitted prover loop is provably the `n`-fold iterate of its
    straight-line body. -/
theorem loopEmit_denote_iterate {w : Nat} (n : Nat) (body : List (JInstr w))
    (s : JState w) :
    (lowerBoundedLoop (Γ := []) n body).denote (.cons s .nil)
      = (bodyStep body)^[n] s := by
  rw [loopLcmd_denote, runBoundedLoop_eq_iterate]

end CatCrypt.Crypto.SecureCompilation.VIR.LoopEmitBridge
