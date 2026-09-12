/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.OracleGamePackage

/-! Re-export of `CatCryptCore.Deep.OracleGamePackage` from the CatCrypt-core package, so
`import CatCrypt.Deep.OracleGamePackage` resolves to the upstream library. The constructor
`DeepPackage.ofOracle`, turning a shallow oracle implementation `dom → RawCode codom` into
a package that exports that oracle, lives in the `CatCrypt.Deep` namespace provided by the
upstream module. -/

@[expose] public section
