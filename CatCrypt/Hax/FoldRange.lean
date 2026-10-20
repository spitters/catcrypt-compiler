/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Runtime
public import CatCryptCore.Hax.FoldRange

/-! Re-export of `CatCryptCore.Hax.FoldRange` from the CatCrypt-core package, so existing
`import CatCrypt.Hax.FoldRange` lines resolve to the upstream library. The lemmas about
`Hax.foldRange` live in the namespaces provided by the upstream module. -/

@[expose] public section
