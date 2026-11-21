/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSABase
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeFlat

/-!
# Related call trees with skips at an answer predicate

The relation `RuttSA Sk` relates two call trees up to source events that the target does not
perform, each skipped source event `e` continued at every answer `a` with `Sk e a`. Its
declarations, in the namespace `NFProgCallTreeRuttSA`, are in the modules this module imports.

## Main results

* `NFProgCallTreeRuttSABase`: `RuttSA`, `RetsA`, `ruttSA_iff_ruttS`, `retsA_eq_iff`, the laws
  `RuttSA.imp`, `RuttSA.mono`, `RuttSA.of_rutt`, `RuttSA.bind`, `RuttSA.skip_bind`,
  `RuttSA.of_ret_fail`, `RuttSA.refl`, and `interp_ruttSA`.
* `NFProgCallTree`: `RefinesTA`, `refinesTA_iff_refinesT`, `RefinesTA.refl`, `RefinesTA.obind`.
* `NFProgCallTreeExt`: `ruttSA_obind`.
* `NFProgCallTreeFlat`: `ruttSA_eqTrans`.
-/
