/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSym
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.LeanSourceX86
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.X86StraightLine
public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardSatisfiable

/-!
# Guard satisfiability for the solver correspondences

`CorresJ SR P fa c` holds of every block when `SR` and `P` share no witness, so each
closed correspondence carries the obligation `∃ st a, SR st a ∧ P a`. The
correspondences of the solver modules run over their respective state relations
and guards, and the theorems below supply explicit witnesses.

`corresJ_guardSat` reads the state relation and the guard off the correspondence's own
type, so each statement below is checked against the theorem it names.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos

/-- Instructions 1–33 of `solinas_square` refine their abstract run over the Solinas
    layout with a common witness. -/
theorem solinasSeg1_corres_sym_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg1_corres_sym
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 34–65 of `solinas_square` refine their abstract run over the Solinas
    layout with a common witness. -/
theorem solinasSeg2_corres_sym_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg2_corres_sym
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 66–93 of `solinas_square` refine their abstract run over the Solinas
    layout with a common witness. -/
theorem solinasSeg3_corres_sym_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg3_corres_sym
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 94–99 of `solinas_square` refine their abstract run over the Solinas
    layout with a common witness. -/
theorem solinasSeg4_corres_sym_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg4_corres_sym
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- The 99-instruction `solinas_square` body refines its abstract run over
    the Solinas layout with a common witness. -/
theorem solinasSquareBlock_corres_sym_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSquareBlock_corres_sym
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- The compiled x86 block of `fun a b : BitVec 64 => a + b`, translated to `JInstr`,
    refines the two-address fold over the register-only relation with a common witness. -/
theorem add_descent_solver_guardSat :
    ∃ st a, SRx st a ∧ True :=
  corresJ_guardSat add_descent_solver
    ⟨{ regs := fun _ => 0 }, fun _ => 0, fun _ => rfl, trivial⟩

/-- The compiled x86 block of `fun a b : BitVec 64 => a - b`, translated to `JInstr`,
    refines the two-address fold over the register-only relation with a common witness. -/
theorem sub_descent_solver_guardSat :
    ∃ st a, SRx st a ∧ True :=
  corresJ_guardSat sub_descent_solver
    ⟨{ regs := fun _ => 0 }, fun _ => 0, fun _ => rfl, trivial⟩

/-- A value block of move, add, subtract, and shift refines the composed fold over
    the register-only relation with a common witness. -/
theorem alu_refines_guardSat :
    ∃ st a, SRx st a ∧ True :=
  corresJ_guardSat alu_refines
    ⟨{ regs := fun _ => 0 }, fun _ => 0, fun _ => rfl, trivial⟩

/-- The compiled x86 block of a two-statement program, translated to `JInstr`,
    refines the fold of four value steps over the register-only relation with a common witness. -/
theorem compiled_refines_guardSat :
    ∃ st a, SRx st a ∧ True :=
  corresJ_guardSat compiled_refines
    ⟨{ regs := fun _ => 0 }, fun _ => 0, fun _ => rfl, trivial⟩

/-- A widening multiply followed by an add-with-carry refines the composed fold
    over the carry-tracking relation with a common witness. -/
theorem mulx_adcx_refines_guardSat :
    ∃ st a, SRcarry st a ∧ True :=
  corresJ_guardSat mulx_adcx_refines
    ⟨{ regs := fun _ => 0 }, { regs := fun _ => 0, cf := false }, ⟨fun _ => rfl, rfl⟩, trivial⟩

/-- A three-limb subtract-with-borrow chain refines the composed fold
    over the carry-tracking relation with a common witness. -/
theorem sbb3_refines_guardSat :
    ∃ st a, SRcarry st a ∧ True :=
  corresJ_guardSat sbb3_refines
    ⟨{ regs := fun _ => 0 }, { regs := fun _ => 0, cf := false }, ⟨fun _ => rfl, rfl⟩, trivial⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
