/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindVcgen
public import CatCryptCore.Tactics.BindVcgenSum

/-! Re-export of `CatCryptCore.Tactics.BindVcgen` and `CatCryptCore.Tactics.BindVcgenSum`
from the CatCrypt-core package, so existing `import CatCrypt.Tactic.BindVcgen` lines resolve
to the upstream library. Both the base run-to-completion drivers `spcomp_normalize` /
`bind_vcgen` for `SPComp`-equality goals and the `mapSum`-extended pair
`spcomp_normalize_sum` / `bind_vcgen_sum`, which additionally resolve `mapSum` on `.inl` /
`.inr` so a bind-chain over a `Sum`-typed interface flattens, live in the
`CatCrypt.Tactic` namespace provided by the upstream modules. -/

@[expose] public section
