/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.WP
public import Std.Tactic.Do


@[expose] public section
set_option autoImplicit false
set_option experimental.vcgen true

/-!
# `vcgen` smoke test for a list interpreter in a state monad

A miniature analog of `bignumExec`: a body of instructions interpreted as steps of
`StateM Nat`. Each instruction increments, decrements or sets a counter. The examples
prove `Std.WP` Hoare triples about the interpreter by `vcgen`: after the interpreter and the
literal body are unfolded by `simp only`, `vcgen` walks the resulting `do`-chain through the
`@[spec]` triples of `modify` and `set`.
-/

namespace CatCrypt.Crypto.Jasmin.MVCGenSmoke

open Std.WP

/-! ## Toy instructions -/

/-- Three instruction kinds acting on a counter. -/
inductive ToyInstr
  | inc       : ToyInstr           -- counter += 1
  | dec       : ToyInstr           -- counter -= 1
  | set (n : Nat) : ToyInstr       -- counter := n
  deriving Repr

/-- The toy interpreter monad. -/
abbrev ToyM := StateM Nat

/-- One step of the toy interpreter. -/
def stepToy : ToyInstr → ToyM Unit
  | .inc => modify (· + 1)
  | .dec => modify (fun n => n - 1)
  | .set n => set n

/-- The toy interpreter: `forM` of `stepToy` over a body. -/
def runToy (body : List ToyInstr) : ToyM Unit :=
  body.forM stepToy

/-! ## Triples by `vcgen` -/

/-- The empty body satisfies the trivial triple. -/
example : ⦃fun _ => True⦄ runToy [] ⦃fun _ _ => True⦄ := by
  simp only [runToy, List.forM]
  vcgen

/-- A one-instruction body satisfies the trivial triple. -/
example : ⦃fun _ => True⦄ runToy [.inc] ⦃fun _ _ => True⦄ := by
  simp only [runToy, List.forM, stepToy]
  vcgen

/-- Three steps as an explicit `do`-block. -/
def runToyDo (b0 b1 b2 : ToyInstr) : ToyM Unit := do
  stepToy b0
  stepToy b1
  stepToy b2

/-- The block `set 5; inc; inc` ends with the counter at `7`. -/
example : ⦃fun s => s = 0⦄
    runToyDo (.set 5) .inc .inc
    ⦃fun _ s => s = 7⦄ := by
  simp only [runToyDo, stepToy]
  vcgen
  grind

end CatCrypt.Crypto.Jasmin.MVCGenSmoke
