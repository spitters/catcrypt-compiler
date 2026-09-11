/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Do.Triple
public import Std.Tactic.Do


@[expose] public section
set_option autoImplicit false

/-!
# mvcgen smoke test (Phase 0 of the integration plan)

Confirms that Lean's `mvcgen` tactic recognizes our intended program
shape — a `forM`-style loop over a list of operations in a `StateT`
monad — before committing to the Phase 1 BignumExec refactor.

## What we're testing

A miniature analog of `bignumExec`: a body of "instructions" interpreted
as state-monad steps. Each instruction increments / decrements / sets
a counter. We try to prove a Hoare triple about the running interpreter
via `mvcgen`.

If `mvcgen` walks this naturally, the integration plan is viable.
If it doesn't, we pivot to Aeneas's `step` tactic.
-/

namespace CatCrypt.Crypto.Jasmin.MVCGenSmoke

open Std.Do

/-! ## §1. Toy "InstrR" — three instruction kinds -/

inductive ToyInstr
  | inc       : ToyInstr           -- counter += 1
  | dec       : ToyInstr           -- counter -= 1
  | set (n : Nat) : ToyInstr       -- counter := n
  deriving Repr

abbrev ToyM := StateM Nat

def stepToy : ToyInstr → ToyM Unit
  | .inc => modify (· + 1)
  | .dec => modify (fun n => n - 1)
  | .set n => set n

def runToy (body : List ToyInstr) : ToyM Unit :=
  body.forM stepToy

/-! ## §2. Execution sanity (computational, no Hoare) -/

#eval runToy [.set 5, .inc, .inc] 0  -- ((), 7)
#eval runToy [.inc, .dec] 10         -- ((), 10)

/-! ## §3. mvcgen smoke — the actual test

Question: does `mvcgen` walk `runToy`'s `forM` into per-instruction
VCs, and does it close them via the `@[spec]`-tagged stdlib lemmas
(or stay open for our discharge)?

Three increasingly complex tests, each checking a property of `runToy`. -/

/-- Test 1: trivial `True` postcondition on an empty body. Should be
    immediate. -/
example : ⦃⌜True⌝⦄ runToy [] ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen [runToy]

/-- Test 2: trivial `True` on a one-instruction body. -/
example : ⦃⌜True⌝⦄ runToy [.inc] ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen [runToy, stepToy]

/-- Variant runToy as an explicit `do`-block (mvcgen-native shape). -/
def runToyDo (b0 b1 b2 : ToyInstr) : ToyM Unit := do
  stepToy b0
  stepToy b1
  stepToy b2

/-- Test 3: substantive — using the explicit `do` form, mvcgen walks
    cleanly. This is the shape Phase 1's BignumExec refactor would
    produce (modulo length quantification). -/
example : ⦃fun s => ⌜s = 0⌝⦄
    runToyDo (.set 5) .inc .inc
    ⦃⇓ _ => fun s => ⌜s = 7⌝⦄ := by
  mvcgen [runToyDo, stepToy]
  all_goals (try omega)

end CatCrypt.Crypto.Jasmin.MVCGenSmoke
