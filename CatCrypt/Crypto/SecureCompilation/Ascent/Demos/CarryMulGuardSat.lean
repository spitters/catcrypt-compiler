/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.Ascent.CarryMulCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardSatisfiable

/-!
# Guard satisfiability for the carry-multiply correspondences

`CorresJ SR P fa c` holds of every block when `SR` and `P` share no witness, so each
closed correspondence carries the obligation `∃ st a, SR st a ∧ P a`. The
correspondences of `CarryMulCorres` run over `SRmem carryMulMidCells` and
`SRmem carryMulTailCells` under the guard `fun _ => True`, and
`srmem_carryMulMid_satisfiable` and `srmem_carryMulTail_satisfiable` supply the states.

`corresJ_guardSat` reads the state relation and the guard off the correspondence's own
type, so each statement below is checked against the theorem it names.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.Ascent

/-- The middle segment's layout and guard have a common witness. -/
theorem carryMulMid1_corres_guardSat :
    ∃ st a, SRmem carryMulMidCells st a ∧ True :=
  corresJ_guardSat carryMulMid1_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulMid_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 34–63 refine their abstract run over the middle segment's layout with a common witness. -/
theorem carryMulMid2_corres_guardSat :
    ∃ st a, SRmem carryMulMidCells st a ∧ True :=
  corresJ_guardSat carryMulMid2_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulMid_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 64–92 refine their abstract run over the middle segment's layout with a common witness. -/
theorem carryMulMid3_corres_guardSat :
    ∃ st a, SRmem carryMulMidCells st a ∧ True :=
  corresJ_guardSat carryMulMid3_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulMid_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 93–120 refine their abstract run over the middle segment's layout with a common witness. -/
theorem carryMulMid4_corres_guardSat :
    ∃ st a, SRmem carryMulMidCells st a ∧ True :=
  corresJ_guardSat carryMulMid4_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulMid_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 121–146 refine their abstract run over the middle segment's layout with a common witness. -/
theorem carryMulMid5_corres_guardSat :
    ∃ st a, SRmem carryMulMidCells st a ∧ True :=
  corresJ_guardSat carryMulMid5_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulMid_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 5–146 refine their abstract run over the middle segment's layout with a common witness. -/
theorem carryMulMid_corres_guardSat :
    ∃ st a, SRmem carryMulMidCells st a ∧ True :=
  corresJ_guardSat carryMulMid_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulMid_satisfiable; exact ⟨st, a, h, trivial⟩)

/-- Instructions 148–166 refine their abstract run over the tail segment's layout with a common witness. -/
theorem carryMulTail_corres_guardSat :
    ∃ st a, SRmem carryMulTailCells st a ∧ True :=
  corresJ_guardSat carryMulTail_corres
    (by obtain ⟨st, a, h⟩ := srmem_carryMulTail_satisfiable; exact ⟨st, a, h, trivial⟩)

end CatCrypt.Crypto.SecureCompilation.Ascent
