/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge

/-!
# CryptoSSA → VIR (CatCrypt dialect): variable-translation re-export

Re-exports the dialect variable / argument translators `toVIRVar` / `toVIRArgs`
(defined in `VIR/DialectVarBridge.lean`) into the `CryptoToVIR` namespace, where
downstream code resolves them. The `CryptoTy` is the same type on both the
CryptoSSA and `catCryptDialect` sides; contexts are compatible, so a de-Bruijn
variable maps across unchanged.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.CryptoToVIR

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## Variable / argument translation

The variable translators `toVIRVar` / `toVIRArgs` live in the support module
`VIR/DialectVarBridge.lean`. They are re-exported into this namespace so
`CryptoToVIR.toVIRVar` / `CryptoToVIR.toVIRArgs` references elsewhere keep
resolving. -/

export CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar toVIRArgs)

end CatCrypt.Crypto.SecureCompilation.VIR.CryptoToVIR
