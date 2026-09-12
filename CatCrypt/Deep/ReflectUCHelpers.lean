/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.ReflectUCHelpers

/-! Re-export of `CatCryptCore.Deep.ReflectUCHelpers` from the CatCrypt-core package, so
`import CatCrypt.Deep.ReflectUCHelpers` resolves to the upstream library. The perfect
security stack combinators lifting two reflected oracle bodies along
`rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC` live in the
`CatCrypt.Deep` namespace provided by the upstream module. -/

@[expose] public section
