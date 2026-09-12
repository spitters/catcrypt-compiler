/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.PureCode

/-!
# `CatCrypt.Deep.PureCode` (shim)

The state-free purity reflection backend (`RawCode.StateFree`,
`eval_isPure_of_stateFree`, `ssprove_ispure_reflect`, `ssprove_statefree`) now
lives in `CatCryptCore.Deep.PureCode`; this module re-exports it and preserves
the `CatCrypt.Deep.PureCode` import path.
-/

@[expose] public section
