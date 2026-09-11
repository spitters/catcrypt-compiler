/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CompPoly.Univariate.NTT.FastMul

/-!
# CompPoly smoke import

Verifies that the upstream CompPoly NTT theory (`fastMulImpl_eq_mul`,
`Domain R`, `forwardSpec`, `inverseSpec`, …) is importable from the
CatCrypt source tree.  Once this builds clean, the lake dep is wired
correctly and downstream `Optimizer/Lattice/*` files can rely on it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.CompPolyTest

/-- Smoke test that CompPoly is importable. -/
theorem compPoly_imports : True := trivial

/-- Sanity check: the `Domain` structure from CompPoly is available
    in this namespace.  We don't construct a value here (that's Stage B),
    just confirm the name resolves. -/
example : Type := CompPoly.CPolynomial.NTT.Domain Rat

end CatCrypt.Crypto.Optimizer.Lattice.CompPolyTest
