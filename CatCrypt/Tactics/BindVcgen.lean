/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindVcgen

/-! Re-export of `CatCryptCore.Tactics.BindVcgen` from the CatCrypt-core package, so
`import CatCrypt.Tactics.BindVcgen` resolves to the upstream library. The
`spcomp_normalize` / `bind_vcgen` run-to-completion drivers for `SPComp`-equality goals live
in the `CatCrypt.Tactic` namespace provided by the upstream module. -/

@[expose] public section
