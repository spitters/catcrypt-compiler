/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Transfer.Examples.MachineLimbField

/-!
# Single-limb value abstraction (re-export shim)

The single-limb value-abstraction layer of the LowCT ascent calculus — the
limb→field split surjection `BitVec 64 ↠ ZMod p` — now lives in the ParamTransfer
release library as `Transfer.Examples.MachineLimbField`. This module re-exports the
single-limb names into `CatCrypt.Crypto.SecureCompilation.Ascent` so existing
consumers resolve them unqualified exactly as before.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

export Transfer.Param
  (limbFieldParam instTransferDomLimbField dec_add dec_mul LimbStoreRefines
   limbLeaf_hcongr)

end CatCrypt.Crypto.SecureCompilation.Ascent
