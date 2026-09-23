/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec

/-!
# Chaining part results across a concatenated block

A part result says that a block carries an entry map to an exit map under the slot
values `ρ`. Two such results chain across the concatenation of their blocks, and a
capstone applies the chain once, with its concrete blocks as arguments, so that the block
terms appear once in the proof rather than once per rewrite.

## Main results

* `mapHolds_cat`: two part results chain across `b1 ++ b2`.
* `holds_lits_get`: a run of literal statements holds the literal at each slot.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-- Two part results chain across the concatenation of their blocks. -/
theorem mapHolds_cat (ρ : Nat → BitVec 64) {m0 m1 m2 : List (Loc × WE)}
    {b1 b2 : List (JInstr 64)}
    (h1 : ∀ s, MapHolds ρ m0 s → MapHolds ρ m1 (runBlock s b1))
    (h2 : ∀ s, MapHolds ρ m1 s → MapHolds ρ m2 (runBlock s b2)) :
    ∀ s, MapHolds ρ m0 s → MapHolds ρ m2 (runBlock s (b1 ++ b2)) := by
  intro s h
  rw [runBlock_cat]
  exact h2 _ (h1 _ h)

/-- The value of a cell location is the cell's contents. Stated as an equation so that a
    rewrite with it leaves an `Eq.mpr` term: a definitional unfolding at this site makes
    the kernel reduce the state — the run of a whole block — to a constructor. -/
theorem Loc.val_cell (s : JState 64) (b : String) (o : Int) :
    Loc.val s (.cell b o) = s.mem b o := rfl

/-- The value of a slot expression is the slot's value; an equation for the same reason as
    `Loc.val_cell`. -/
theorem WE.eval_v (ρ : Nat → BitVec 64) (j : Nat) : WE.eval ρ (.v j) = ρ j := rfl

/-- A run of literal statements from slot `n` holds the `i`-th literal at slot `n + i`. -/
theorem holds_lits_get (ρ : Nat → BitVec 64) :
    ∀ (l : List Nat) (n i c : Nat), Holds ρ n (l.map WE.lit) → l[i]? = some c →
      ρ (n + i) = BitVec.ofNat 64 c
  | [], _, _, _, _, h => by simp at h
  | m :: l, n, 0, c, h, hc => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      simpa [Holds, WE.eval] using h.1
  | m :: l, n, i + 1, c, h, hc => by
      simp only [List.getElem?_cons_succ] at hc
      rw [show n + (i + 1) = (n + 1) + i by omega]
      exact holds_lits_get ρ l (n + 1) i c h.2 hc

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
