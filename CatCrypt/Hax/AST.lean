/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.ImpType
public import HaxLean.AST

/-!
# `CatCrypt.Hax` aliases for the hax-lean AST

The imperative AST of the hax pipeline is `Hax.ImpExpr` from `HaxLean.AST`.
This module aliases its names into the `CatCrypt.Hax` namespace so that a
module written against `open CatCrypt.Hax (ImpExpr …)` or the qualified
`CatCrypt.Hax.ImpExpr` resolves to the hax-lean declarations.
-/

public section

namespace CatCrypt.Hax

export _root_.Hax (ImpLit ImpPat ImpExpr IntWidth ImpType)

namespace ImpExpr
export _root_.Hax.ImpExpr (ind beq)
end ImpExpr

namespace IntWidth
export _root_.Hax.IntWidth (bits modulus)
end IntWidth

end CatCrypt.Hax
