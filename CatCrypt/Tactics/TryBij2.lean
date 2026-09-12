/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.TryBij2

/-! Re-export of `CatCryptCore.Tactics.TryBij2` from the CatCrypt-core package, so
`import CatCrypt.Tactics.TryBij2` resolves to the upstream library. The
`ssprove_try_bij₂` tactic, which synchronises an outer sample and bijection-couples the
inner one with an outer-sample-indexed family, lives in the `CatCrypt.Tactics` namespace
provided by the upstream module. -/

@[expose] public section
