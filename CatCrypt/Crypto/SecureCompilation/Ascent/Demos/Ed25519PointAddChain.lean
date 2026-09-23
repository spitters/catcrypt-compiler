/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts

/-!
# Chaining flag-aware part results across a concatenated block

A flag-aware part result carries an entry map and entry flags to an exit map and exit
flags. Two such results chain across the concatenation of their blocks; a capstone
applies the chain once with its concrete blocks as arguments, so the block terms appear
once in the proof.

## Main results

* `holds3_cat`: two flag-aware part results chain across `b1 ++ b2`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-- Two flag-aware part results chain across the concatenation of their blocks. -/
theorem holds3_cat (ρ : Nat → BitVec 64) {m0 m1 m2 : List (Loc × WE)} {c0 c1 c2 z0 z1 z2 : Option WE}
    {b1 b2 : List (JInstr 64)}
    (h1 : ∀ s, MapHolds ρ m0 s → CfHolds ρ c0 s → ZfHolds ρ z0 s →
      MapHolds ρ m1 (runBlock s b1) ∧ CfHolds ρ c1 (runBlock s b1) ∧ ZfHolds ρ z1 (runBlock s b1))
    (h2 : ∀ s, MapHolds ρ m1 s → CfHolds ρ c1 s → ZfHolds ρ z1 s →
      MapHolds ρ m2 (runBlock s b2) ∧ CfHolds ρ c2 (runBlock s b2) ∧ ZfHolds ρ z2 (runBlock s b2)) :
    ∀ s, MapHolds ρ m0 s → CfHolds ρ c0 s → ZfHolds ρ z0 s →
      MapHolds ρ m2 (runBlock s (b1 ++ b2)) ∧ CfHolds ρ c2 (runBlock s (b1 ++ b2)) ∧
        ZfHolds ρ z2 (runBlock s (b1 ++ b2)) := by
  intro s hm hc hz
  rw [runBlock_cat]
  obtain ⟨m, c, z⟩ := h1 s hm hc hz
  exact h2 _ m c z

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
