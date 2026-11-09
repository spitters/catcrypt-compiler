/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Range.Domain
public import Mathlib.Tactic.Linarith

/-!
# The interval domain of a lane-wise range analysis

The domain lives in hax-lean (`HaxLean/Range/Domain.lean`), which imports no Mathlib, so that
the range checker of the typed extraction and the compiler share one domain. Its declarations
keep the namespace `CatCrypt.Crypto.SecureCompilation.RangeDomain`. The import of
`Mathlib.Tactic.Linarith` is the one the module had before the move, which its importers
receive through it.
-/
