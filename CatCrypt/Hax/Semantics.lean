/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.AST
public import CatCrypt.Hax.Value
public import HaxLean.Semantics

/-!
# `CatCrypt.Hax` aliases for the hax-lean reference semantics

The big-step semantics of `Hax.ImpExpr` is `Hax.denote` from
`HaxLean.Semantics`, with its outcome type, builtin tables and evaluation
helpers. This module aliases those names into the `CatCrypt.Hax` namespace.
-/

public section

namespace CatCrypt.Hax

export _root_.Hax (Outcome Builtins defaultBuiltins denote denoteArgs denoteMatchArms
  denoteForLoop denoteForLoopRev denoteWhile denoteDefault denoteValue denoteWidthAware
  wrapUint wrapSint widthArithOps widthBitwiseOps widthCmpOps widthCastOps widthArrayOps
  signedArithOps signedCmpOps panicOps widthOps fullBuiltins widthAwareBuiltins
  denoteArgs_map_congr denoteMatchArms_map_congr denoteForLoop_congr
  denoteForLoopRev_congr denoteWhile_congr)

namespace Outcome
export _root_.Hax.Outcome (isVal toVal)
end Outcome

end CatCrypt.Hax
