/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.AST
public import HaxLean.Value

/-!
# `CatCrypt.Hax` aliases for the hax-lean runtime values

The runtime value type of the hax reference interpreter is `Hax.Value` from
`HaxLean.Value`, with the environments `Hax.Env` and the pattern matcher
`Hax.matchPat`. This module aliases those names into the `CatCrypt.Hax`
namespace.
-/

public section

namespace CatCrypt.Hax

export _root_.Hax (Value Env matchPat)

namespace Value
export _root_.Hax.Value (ofLit toBool toInt toUint toTuple toArray projIdx arrayLen)
end Value

namespace Env
export _root_.Hax.Env (empty extend restrict remove extend_same extend_other)
end Env

namespace matchPat
export _root_.Hax.matchPat (matchPatList)
end matchPat

end CatCrypt.Hax
