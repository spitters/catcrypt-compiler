/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.GamePackage

/-! Re-export of `CatCryptCore.Deep.GamePackage` from the CatCrypt-core package, so
`import CatCrypt.Deep.GamePackage` resolves to the upstream library. The constructors
packaging a closed `RawCode Bool` as a `DeepPackage` / `NomPackage` whose sole export is
the main procedure live in the `CatCrypt.Deep` namespace provided by the upstream
module. -/

@[expose] public section
