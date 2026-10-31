/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.Hax64Table
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import HaxLean.Phase.InlineLocalClosures
public import HaxLean.TExpr

/-!
# Source runs that return words

The source conditions of an extraction under an ABI layout `σ`: every run of
`denoteSpine hax64WExit` from an environment `σ` reads off an entry state returns an array
of integers, or an integer.

## Main definitions

* `WordArrResult` — every source run from an ABI environment returns an array of integers.
* `WordScalResult` — every source run from an ABI environment returns an integer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

/-- **Every source run from an ABI environment returns an array of integers**: from every
    entry state satisfying `σ.Regions` and every environment `σ` reads off it, every run of
    `denoteSpine hax64WExit` on `te.erase` to a value returns an array of `Value.int` words. -/
def WordArrResult (σ : AbiLayout) (te : _root_.Hax.TExpr) : Prop :=
  ∀ sa env fuel v env', σ.Regions sa → σ.EnvOf sa env →
    (_root_.Hax.InlineLocalClosures.denoteSpine CatCrypt.Crypto.Hax.hax64WExit fuel
      te.erase).run env = (.val v, env') →
    ∃ zs : List Int, v = .array (zs.map .int)

/-- **Every source run from an ABI environment returns an integer**: from every entry state
    satisfying `σ.Regions` and every environment `σ` reads off it, every run of
    `denoteSpine hax64WExit` on `te.erase` to a value returns a `Value.int`. -/
def WordScalResult (σ : AbiLayout) (te : _root_.Hax.TExpr) : Prop :=
  ∀ sa env fuel v env', σ.Regions sa → σ.EnvOf sa env →
    (_root_.Hax.InlineLocalClosures.denoteSpine CatCrypt.Crypto.Hax.hax64WExit fuel
      te.erase).run env = (.val v, env') →
    ∃ z : Int, v = .int z

end CatCrypt.Crypto.SecureCompilation.Haxc
