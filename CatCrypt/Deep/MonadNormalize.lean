/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.MonadNormalize

/-! Re-export of `CatCryptCore.Deep.MonadNormalize` from the CatCrypt-core package, so
`import CatCrypt.Deep.MonadNormalize` resolves to the upstream library. The reflective
normalizer for the `RawCode` free monad — a canonical normal form on the syntax tree with
its once-and-for-all soundness proof — lives in the `CatCrypt.Deep` and
`CatCrypt.Deep.RawCode` namespaces provided by the upstream module. -/

@[expose] public section
