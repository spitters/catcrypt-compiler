/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PrattCertificate
public import Transfer.Examples.ZModPowMod

/-! Re-export of `CatCryptCore.ForMathlib.PrattCertificate` from the CatCrypt-core
package, so existing `import CatCrypt.Crypto.Util.PrattCertificate` lines resolve to the
upstream library. Declarations and the namespace `CatCrypt.PrattCertificate` are
provided by the upstream module; `Transfer.Examples.ZModPowMod` stays in the import
closure of this module's consumers. -/

@[expose] public section
