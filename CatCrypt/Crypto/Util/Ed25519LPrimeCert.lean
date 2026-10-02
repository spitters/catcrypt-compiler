/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KeyAgreement.Ed25519LPrimeCert
public import CatCrypt.Crypto.Util.PrattCertificate

/-! Re-export of `CatCryptCore.Crypto.KeyAgreement.Ed25519LPrimeCert` from the
CatCrypt-core package, so existing `import CatCrypt.Crypto.Util.Ed25519LPrimeCert` lines
resolve to the upstream library. Declarations and the namespace
`CatCrypt.Crypto.Util.Ed25519LPrimeCert` are provided by the upstream module. -/

@[expose] public section
