/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.TExpr

/-!
# `Repr` for `Hax.TExpr` (CatCrypt-side, no hax-lean edit)

Piece A of the path-(b) literal-generation pipeline: `Hax.TExpr`/`Hax.TExprKind`
carry only `Repr`-deriving components (`ImpLit`, `ImpPat`, `ImpType` already
`deriving Repr`), so a `Repr` instance is derivable downstream here, in CatCrypt,
without touching hax-lean. The codegen tool (piece B) uses this to print a real
parsed `TExpr` as a reducible `def foo_texpr : Hax.TExpr := <literal>`, which the
typed front `texprToThir` can then consume + prove by `rfl` (a runtime
`parseHaxTExpr` result is `partial` and not kernel-reducible).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TExprRepr

deriving instance Repr for Hax.ImpType
deriving instance Repr for Hax.TExpr, Hax.TExprKind

open Hax in
/-- Smoke: a small typed TExpr reprs to re-parseable Lean syntax. -/
example : True := by trivial

end CatCrypt.Crypto.SecureCompilation.TExprRepr
