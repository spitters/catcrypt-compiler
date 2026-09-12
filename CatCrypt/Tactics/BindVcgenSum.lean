/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindVcgenSum

/-! Re-export of `CatCryptCore.Tactics.BindVcgenSum` from the CatCrypt-core package, so
`import CatCrypt.Tactics.BindVcgenSum` resolves to the upstream library. The
`mapSum`-extended drivers `spcomp_normalize_sum` / `bind_vcgen_sum`, which flatten
bind-chains dispatching on a `Sum`-typed interface, live in the `CatCrypt.Tactic` namespace
provided by the upstream module. `CatCrypt.Tactic.BindVcgen` re-exports the same module. -/

@[expose] public section
