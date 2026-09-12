/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.FieldClear

/-! Re-export of `CatCryptCore.Tactics.FieldClear` from the CatCrypt-core package, so
`import CatCrypt.Tactics.FieldClear` resolves to the upstream library. The `field_clear`
tactic, which extends `field_simp` to denominators that are ring-equivalent to the given
hypotheses rather than syntactically equal, lives in the `CatCrypt.Tactic.FieldClear`
namespace provided by the upstream module. `CatCrypt.Tactic.FieldClear` re-exports the same
module. -/

@[expose] public section
