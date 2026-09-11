/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.StoreRefinement

/-!
# Multi-limb value abstraction (re-export shim)

The multi-limb value-abstraction layer — the base-`2^64` limb-array→field split
surjection `(Fin n → BitVec 64) ↠ ZMod p` — now lives in the ParamTransfer release
library as `Transfer.Examples.MachineLimbField`. This module re-exports the
multi-limb names into `CatCrypt.Crypto.SecureCompilation.Ascent` so existing
consumers resolve them unqualified exactly as before. It imports the single-limb
shim (`StoreRefinement`) to preserve the original import chain.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Ascent

export Transfer.Param
  (limbVal toLimbs limbVal_zero limbVal_succ toLimbs_tail limbVal_toLimbs
   multiLimbFieldParam limbVal_congr limbVal_hcongr limbVal_hcongr_field
   MultiLimbStoreRefines multiLimbLeaf_hcongr)

end CatCrypt.Crypto.SecureCompilation.Ascent
