/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
import CatCrypt.Crypto.MAYO.KernelEmitDenote

/-!
# `corres_solve_scalar` re-derives the MAYO GF(16) multiply `Corres`

`MAYO.KernelEmitDenote.gfMul16_corres` proves that the front-authored bit-serial
`GF(16)` multiply `gfMul dst aE bE` refines the value-model fold `gfMulSem16`, by
`corres_seqAll` over the eleven per-leaf `corres_setExprWord` obligations spelled
out in `gfMul16List_leaf` (`fin_cases` + a per-leaf `srcClean` discharge).

`corres_solve_scalar` (`Ascent.CorresScalar`) collapses that assembly: it walks the
`RSeq` tree the multiply unfolds to and discharges each leaf automatically. The
statement `gfMul16_corres_via_tactic` is the same correspondence — the abstract
step is the synthesized fold, reconciled with `MAYO`'s `gfMulSem16` by definitional
equality — proved without the `gfMul16List_leaf` scaffold.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.MAYO.KernelFromRustcmdFrontEmit (gfMul gfAccStep gfXtime negMask bitOf)

namespace CatCrypt.Crypto.MAYO.KernelEmitDenote

/-- The MAYO GF(16) multiply refines its value-model fold `gfMulSem16`, proved by
    `corres_solve_scalar`. Unfolding `gfMulSem16` (a `List.foldl` of `wordStep`s)
    and the multiply's `seqAll` chain leaves a `Corres SRwordBV` over the plain
    `RSeq` / `RScalarSetExpr` tree, which the tactic walks — no `gfMul16List_leaf`
    `fin_cases` enumeration and no explicit `corres_seqAll`/`forall2_map_self`
    assembly. -/
theorem gfMul16_corres_via_tactic (dst : String) (aE bE : SExpr)
    (haE : srcClean aE) (hbE : srcClean bE) :
    Corres SRwordBV (fun _ => True) (gfMulSem16 dst aE bE) (gfMul dst aE bE) := by
  rw [gfMul16_eq]
  simp only [gfMul16List, gfAccStep, gfXtime, negMask, bitOf,
    KernelFromRustcmdFrontEmit.seqAll]
  corres_solve_scalar

end CatCrypt.Crypto.MAYO.KernelEmitDenote
