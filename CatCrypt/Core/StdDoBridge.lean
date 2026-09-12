/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.StdDoBridge

/-! Re-export of `CatCryptCore.Core.StdDoBridge` from the CatCrypt-core package, so
existing `import CatCrypt.Core.StdDoBridge` lines resolve to the upstream library. The
`Std.Do` weakest-precondition / `Triple` bridge for `SPComp` lives in the
`CatCrypt.Core.SPComp` namespace provided by the upstream module. -/

@[expose] public section
