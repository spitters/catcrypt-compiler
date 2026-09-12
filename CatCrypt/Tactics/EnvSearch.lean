/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.EnvSearch

/-! Re-export of `CatCryptCore.Tactics.EnvSearch` from the CatCrypt-core package, so
`import CatCrypt.Tactics.EnvSearch` resolves to the upstream library. The `#nameFind`,
`#typeFind` and `#docFind` commands, which query the elaborated environment by declaration
name, by pretty-printed type, and by docstring, live in the `CatCrypt.Tactic.EnvSearch`
namespace provided by the upstream module. `CatCrypt.Tactic.EnvSearch` re-exports the same module. -/

@[expose] public section
