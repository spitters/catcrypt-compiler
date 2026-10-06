/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.AST
public import HaxLean.AST

/-!
# The variable predicate on `ImpExpr`

`isVar e` holds when the hax expression `e` is a plain variable. It is the side condition
on call arguments and on the components of an aggregate tuple tail in the translation
`ImpExpr → Option LowCT`, and the test the A-normaliser uses to decide whether a
subexpression is bound to a fresh name.

## Main definitions

* `isVar` — the Boolean test for the constructor `ImpExpr.var`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr)

/-- An `ImpExpr` argument is "named" if it is a plain `var`.  This is
    the side-condition every `app`-argument must satisfy for the H2
    translation to succeed (since `haxArgToLocated` only lifts `var`s
    into `Located` slots), and the condition on every component of an
    aggregate tuple tail. -/
def isVar : ImpExpr → Bool
  | .var _ => true
  | _      => false

end CatCrypt.Crypto.Hax
