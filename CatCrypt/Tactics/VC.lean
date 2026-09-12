/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.VC

/-! Re-export of `CatCryptCore.Tactics.VC` from the CatCrypt-core package, so existing
`import CatCrypt.Tactics.VC` lines resolve to the upstream library. The verification-
condition tactics (`ssprove_ispure`, `ssprove_nofail`, `ssprove_vc`) live in the
`CatCrypt.Tactics.VC` namespace provided by the upstream module. -/

@[expose] public section
