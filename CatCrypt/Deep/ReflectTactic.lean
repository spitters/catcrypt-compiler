/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.ReflectTactic

/-! Re-export of `CatCryptCore.Deep.ReflectTactic` from the CatCrypt-core package, so
`import CatCrypt.Deep.ReflectTactic` resolves to the upstream library. The end-to-end
reflective SSP tactic, driving two shallow games through reflection to package and UC
security, lives in the `CatCrypt.Deep` namespace provided by the upstream module. -/

@[expose] public section
