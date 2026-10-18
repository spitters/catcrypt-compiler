/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignment
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

/-!
# Alignment of every op of the stack-memory fragment

`opMemB` (`X86Backend.ExportCertFragment`) is the set of `jasminDialect` ops the region
back half of `compileA` admits. Each of them has an alignment row in
`JasmincSemAlignment`: its denotation equals the Jasmin text the lowering prints for it,
evaluated with the transcriptions of `x86_instr_decl.v`. This module collects the rows;
it is separate so that `JasmincSemAlignment` does not import the export chain.

## Main results

* `opcode_alignment_opMemB` — every op that `opMemB` admits satisfies `OpAligned`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignmentOpMem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignment
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)

/-- **Every op of the stack-memory fragment `opMemB` has its alignment row.** The
    side conditions of `opMemB` (a count below `2 ^ w` for an immediate shift) are
    the hypotheses of the shift rows; the `sarImm` row keeps its hypothesis `n < w`. -/
theorem opcode_alignment_opMemB : ∀ op, opMemB op = true → OpAligned op := by
  intro op h
  cases op <;> simp only [opMemB, decide_eq_true_eq, Bool.false_eq_true] at h <;>
    simp only [OpAligned]
  case regArith => exact fun a b => binop_agrees_jasmin _ a b
  case stackLoad => exact stackLoad_agrees_jasmin
  case stackStore => exact stackStore_agrees_jasmin
  case castW => exact castW_agrees_jasmin
  case regConst w n => exact regConst_agrees_jasmin w n
  case mulhi => exact mulhi_agrees_jasmin
  case addCarryLo => exact addCarryLo_agrees_jasmin
  case addCarryHi => exact addCarryHi_agrees_jasmin
  case shrImm => exact shrImm_agrees_jasmin h
  case sarImm => exact fun hn => sarImm_agrees_jasmin hn
  case shlImm => exact shlImm_agrees_jasmin h
  case select => exact select_agrees_jasmin
  case cmp => exact cmp_agrees_jasmin _
  case cmpImm c w n => exact cmpImm_agrees_jasmin c n
  case stackZero => exact stackZero_agrees_jasmin
  case stackStoreImm => exact fun arr v => stackStoreImm_agrees_jasmin arr _ v

end CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignmentOpMem
