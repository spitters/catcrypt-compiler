/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit
public import HaxLean.Phase.WhileTrueFlag

/-!
# Lowering a function body whose `while true` loops are rewritten onto a flag

hax-lean emits a Rust loop that threads a tuple state through `continue (s)` and
`break (s)` as `whileFold (lit (bool true)) body`, and `haxToLowCTK` lowers a
`whileFold` only on a variable guard. `haxToLowCTFnW g` rewrites each such loop, at
every nesting depth, into a loop on the flag `g` bound to `true`
(`Hax.WhileTrueFlag.wtFn`), and lowers the result by `haxToLowCTFn`: a loop whose
body breaks becomes the exit-flag loop `exitLoop` on the slot `g`, followed by
`breakLoop`.

## Main results

* `haxToLowCTFnW`: the lowering
* `haxToLowCTFnW_simulates_exit`: for a function body of `Hax.WhileTrueFlag.wtOk g`
  whose rewriting lies in the fragment `exitSimOk`, the result slot of the lowered
  function holds the decoding of the returned or final value of the body
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Env Outcome Builtins denote')
open _root_.Hax.WhileTrueFlag (wtFn wtOk wtFn_run_same)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)

/-- The lowering of a function body whose `whileFold (lit (bool true))` loops are
    rewritten onto the flag `g` (`Hax.WhileTrueFlag.wtFn`); the result is lowered by
    `haxToLowCTFn`. -/
def haxToLowCTFnW (g : String) (e : ImpExpr) : Option LowCT :=
  haxToLowCTFn (wtFn g e)

/-- **Function-level simulation with `while true` loops.** For a function body of
    `wtOk g` whose rewriting `wtFn g e` lies in the fragment, the result slot of
    `haxToLowCTFnW g e` holds the decoding of the returned or final value of `e`. -/
theorem haxToLowCTFnW_simulates_exit (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hs : ScalarOpsSound bi) (g : String) (e : ImpExpr) (C : LowCT)
    (hfn : wtOk g e = true) (hok : exitSimOk true true (wtFn g e) = true)
    (hK : haxToLowCTFnW g e = some C)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec C rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) := by
  have hsame := wtFn_run_same (bi := bi) hfn fuel env
  have hrun' : (denote' bi fuel (wtFn g e)).run env =
      (o, ((denote' bi fuel (wtFn g e)).run env).2) :=
    Prod.ext (by rw [hsame, hrun]) rfl
  exact haxToLowCTFn_simulates_exit bi N leafSpec hs _ C hok hK fuel env _ o rs hrun' hval hag

end CatCrypt.Crypto.Hax
