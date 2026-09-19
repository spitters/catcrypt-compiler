/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardSatisfiable

/-!
# Guard satisfiability for the Curve25519 field operation correspondences

`CorresJ SR P fa c` holds of every block when `SR` and `P` share no witness, so each
closed correspondence carries the obligation `∃ st a, SR st a ∧ P a`. The
correspondences of the field operations run over their respective state relations
and guards, and the theorems below supply explicit witnesses.

`corresJ_guardSat` reads the state relation and the guard off the correspondence's own
type, so each statement below is checked against the theorem it names.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519)

/-- The add block's layout and guard have a common witness. -/
theorem feAddBlock_corresJ_guardSat :
    ∃ st a, SRfe st a ∧ a.x + a.y < 2 * p25519 :=
  corresJ_guardSat feAddBlock_corresJ
    ⟨{ regs := fun _ => 0 }, { x := 0, y := 0, z := 0 }, ⟨rfl, rfl, rfl⟩, by decide⟩

/-- The sub block's layout and guard have a common witness. -/
theorem feSubBlock_corresJ_guardSat :
    ∃ st a, SRfe st a ∧ a.x < a.y + p25519 ∧ a.y ≤ a.x + p25519 :=
  corresJ_guardSat feSubBlock_corresJ
    ⟨{ regs := fun _ => 0 }, { x := 0, y := 0, z := 0 }, ⟨rfl, rfl, rfl⟩, by decide, by decide⟩

/-- The multiply block's layout and guard have a common witness. -/
theorem feMulBlock_corresJ_guardSat :
    ∃ st a, SRf "y" st a ∧ a.stage = 0 :=
  corresJ_guardSat feMulBlock_corresJ
    ⟨{ regs := fun _ => 0 }, { stage := 0, x := 0, y := 0, acc := 0, q := 0 }, ⟨rfl, rfl, trivial⟩, rfl⟩

/-- The square block's layout and guard have a common witness. -/
theorem feSqrBlock_corresJ_guardSat :
    ∃ st a, SRf "x" st a ∧ a.stage = 0 :=
  corresJ_guardSat feSqrBlock_corresJ
    ⟨{ regs := fun _ => 0 }, { stage := 0, x := 0, y := 0, acc := 0, q := 0 }, ⟨rfl, rfl, trivial⟩, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
