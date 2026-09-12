/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Semantics
public import HaxLean.SemanticsCF

/-!
# `CatCrypt.Hax` aliases for the hax-lean control-flow semantics

The control-flow-aware semantics of `Hax.ImpExpr` is `Hax.denote'` from
`HaxLean.SemanticsCF`, with the outcome encoders, the loop-scoping predicate and
the control-flow-freedom predicates on values, environments and builtin tables.
This module aliases those names into the `CatCrypt.Hax` namespace.
-/

public section

namespace CatCrypt.Hax

export _root_.Hax (denote' denoteApp' denoteArgs' denoteMatchArms' denoteForLoop'
  denoteWhile' denoteForLoopOrig' denoteWhileOrig' denoteForLoop'Return
  denoteWhile'Return denoteForLoopRevOrig' denoteForLoopRev' denoteForLoopRev'Return
  cfBuiltins LoopScoped)

namespace Outcome
export _root_.Hax.Outcome (encodeCF4 encodeCF3 encodeCF encodeCF3nested encodeCF3gen
  encodeCFnested)
end Outcome

namespace Builtins
export _root_.Hax.Builtins (NoControlFlow HasErr DeepNoControlFlow
  defaultBuiltins_noControlFlow defaultBuiltins_hasErr defaultBuiltins_deepNoControlFlow)
end Builtins

namespace Value
export _root_.Hax.Value (isControlFlow deepNoControlFlow ofLit_not_isControlFlow
  ofLit_deepNoControlFlow deepNoControlFlow_implies_isControlFlow_false
  deepNoControlFlow_tuple_mem deepNoControlFlow_array_mem deepNoControlFlow_projIdx)
end Value

namespace Env
export _root_.Hax.Env (NoControlFlow)
end Env

end CatCrypt.Hax
