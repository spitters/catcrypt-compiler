/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity

/-!
# Verified quantum compiler passes

A quantum compiler pass is a circuit transformation together with a proof that it preserves
the unitary-channel semantics `unitaryDenote`.

## Main definitions

* `QPass` — a circuit transformation with its proof of `UnitaryCorrectQ`
* `QPass.id` — the identity pass
* `QPass.compose` — sequential composition; correct by `unitaryCorrectQ_comp`
-/

@[expose] public section

namespace CatCrypt.Quantum

open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity

variable {n : ℕ}

/-- A quantum compiler pass: a circuit transformation together with a proof
    that it preserves the unitary-channel semantics (`UnitaryCorrectQ`). -/
structure QPass (n : ℕ) where
  /-- The circuit transformation. -/
  transform : Circuit n → Circuit n
  /-- The pass preserves the unitary-channel semantics. -/
  correct : UnitaryCorrectQ transform

/-- The identity pass (no transformation). -/
def QPass.id (n : ℕ) : QPass n where
  transform := _root_.id
  correct := fun _ => rfl

/-- Compose two quantum compiler passes. The result is correct by
    transitivity of semantic equivalence. -/
def QPass.compose (p₁ p₂ : QPass n) : QPass n where
  transform := p₂.transform ∘ p₁.transform
  correct := unitaryCorrectQ_comp p₁.correct p₂.correct

end CatCrypt.Quantum
