/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Mem

/-!
# `corres_sym` on the `solinas_square` body

`corres_sym` (`CorresSolver`) is the x86 instance of the `SymM` worklist engine of
`CorresSymEngine`. This module applies it to the 99-instruction `solinas_square` body
of `X86Backend/SolinasSquareBlock.lean` as one block, given as the definition
`solinasSquareBlock`, which the engine puts in weak head normal form step by step.

## Main results

* `corres_sym_adx`: a dual-carry block over `SRcarry2`.
* `solinasSeg1_corres_sym` … `solinasSeg4_corres_sym`: the four `solinas_square`
  segments over `SRmem solinasCells`, one `corres_sym` call each.
* `solinasSquareBlock_corres_sym`: the 99-instruction `solinas_square` body over
  `SRmem solinasCells`, one `corres_sym` call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock

/-- A dual-carry block over `SRcarry2`, closed by `corres_sym`. -/
theorem corres_sym_adx (dh dl ra rb d1 s1 d2 s2 : String) :
    CorresJ SRcarry2 (fun _ => True)
      (fun a => adoxStep2 d2 s2 (adcxStep2 d1 s1 (mulxStep2 dh dl ra rb a)))
      [.mulx dh dl (.reg ra) (.reg rb), .adcx d1 (.reg s1), .adox d2 (.reg s2)] := by
  corres_sym

/-- Instructions 1–33 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg1_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg1) solinasSeg1 := by
  corres_sym

/-- Instructions 34–65 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg2_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg2) solinasSeg2 := by
  corres_sym

/-- Instructions 66–93 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg3_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg3) solinasSeg3 := by
  corres_sym

/-- Instructions 94–99 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg4_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg4) solinasSeg4 := by
  corres_sym

/-- The 99-instruction `solinas_square` body refines its abstract run over
    `SRmem solinasCells`, by one `corres_sym` call at the default `maxRecDepth`. -/
theorem solinasSquareBlock_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSquareBlock)
      solinasSquareBlock := by
  corres_sym

end CatCrypt.Crypto.SecureCompilation.Ascent
