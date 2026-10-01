/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CompPoly.Univariate.NTT.FastMul

/-!
# CompPoly import check

Imports the upstream CompPoly NTT theory (`fastMulImpl_eq_mul`, `Domain R`,
`forwardSpec`, `inverseSpec`, …) into the CatCrypt source tree; the example below
checks that its `Domain` structure resolves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.CompPolyTest

/-- The CompPoly NTT `Domain` structure over `ℚ` is a type in this tree. -/
example : Type := CompPoly.CPolynomial.NTT.Domain Rat

end CatCrypt.Crypto.Optimizer.Lattice.CompPolyTest
