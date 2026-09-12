/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindAlign

/-! Re-export of `CatCryptCore.Tactics.BindAlign` from the CatCrypt-core package, so
`import CatCrypt.Tactics.BindAlign` resolves to the upstream library. The `bind_align` /
`bind_step` tactics, which peel matching `SPComp.bind` layers from a goal equality, live in
the `CatCrypt.Tactic` namespace provided by the upstream module. `CatCrypt.Tactic.BindAlign`
re-exports the same module. -/

@[expose] public section
