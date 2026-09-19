/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Mem
public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardSatisfiable

/-!
# Guard satisfiability for the memory-operand x86 correspondences

`CorresJ SR P fa c` holds of every block when `SR` and `P` share no witness, so
each closed correspondence carries the obligation `∃ st a, SR st a ∧ P a`. The
correspondences of `CorresX86Mem` named below run over `SRmem carryMulBodyCells`
or `SRmem solinasCells` under the guard `fun _ => True`, and
`srmem_carryMulBody_satisfiable` and `srmem_solinas_satisfiable` supply the states.

`corresJ_guardSat` reads the state relation and the guard off the correspondence's
own type, so each statement below is checked against the theorem it names.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.Ascent

/-- Instructions 8–16 of `carry_mul`'s body refine their abstract run over the
    body segment's layout with a common witness. -/
theorem carryMul_lines8to16_corres_guardSat :
    ∃ st a, SRmem carryMulBodyCells st a ∧ True :=
  corresJ_guardSat carryMul_lines8to16_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulBody_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- The `imul` step of `carry_mul`'s body refines its abstract run over the body
    segment's layout with a common witness. -/
theorem carryMul_imul_corres_guardSat :
    ∃ st a, SRmem carryMulBodyCells st a ∧ True :=
  corresJ_guardSat carryMul_imul_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulBody_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- The `add`/`adcx` chain of `carry_mul`'s body refines its abstract run over the
    body segment's layout with a common witness. -/
theorem carryMul_addAdcx_corres_guardSat :
    ∃ st a, SRmem carryMulBodyCells st a ∧ True :=
  corresJ_guardSat carryMul_addAdcx_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulBody_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 1–33 of `solinas_square` refine their abstract run over the
    `solinas_square` layout with a common witness. -/
theorem solinasSeg1_corres_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg1_corres
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 34–65 of `solinas_square` refine their abstract run over the
    `solinas_square` layout with a common witness. -/
theorem solinasSeg2_corres_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg2_corres
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 66–93 of `solinas_square` refine their abstract run over the
    `solinas_square` layout with a common witness. -/
theorem solinasSeg3_corres_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg3_corres
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 94–99 of `solinas_square` refine their abstract run over the
    `solinas_square` layout with a common witness. -/
theorem solinasSeg4_corres_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSeg4_corres
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- The whole body of `solinas_square` refines its abstract run over the
    `solinas_square` layout with a common witness. -/
theorem solinasBody_corres_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasBody_corres
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- The parsed `solinas_square` kernel refines its abstract run over the
    `solinas_square` layout with a common witness. -/
theorem solinasSquareBlock_corres_guardSat :
    ∃ st a, SRmem solinasCells st a ∧ True :=
  corresJ_guardSat solinasSquareBlock_corres
    (by obtain ⟨st, a, h⟩ := srmem_solinas_satisfiable; exact ⟨st, a, h, trivial⟩)

end CatCrypt.Crypto.SecureCompilation.Ascent
