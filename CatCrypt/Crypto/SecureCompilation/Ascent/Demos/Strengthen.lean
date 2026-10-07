/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Strengthen
public import CatCrypt.Crypto.SecureCompilation.Ascent.FeAddEndToEnd
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Decide
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Scalar
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.EarlyExit
public import CatCrypt.Crypto.Jasmin.LowCTNotation

/-!
# Demo: the result monad the type-strengthening pass picks, per kernel

Each `*_ts` theorem states the level `Kernel.tsLevel` computes for a kernel of the
ascent demos and capstones, closed by `rfl`; no kernel carries an annotation.

| kernel | source | level | reason |
|---|---|---|---|
| `arithK` | `Demos/Decide` | pure | arithmetic terminals, no guard |
| `bitK` | `Demos/Decide` | pure | xor, and, shift by `7`: range guards statically true |
| `qrFrag` | `Demos/Scalar` | option | `d <<< 16` carries a range guard |
| `feSubC` | `FeSubEndToEnd` | pure | arithmetic terminal, no guard |
| `feAddC` | `FeAddEndToEnd` | pure | arithmetic terminal, no guard |
| `avgK` | `Guards` | option | `(a + b) >>> 1` carries a range guard |
| `sumK` | `Guards` | pure | counted loop over an arithmetic body |
| `countdownK` | this module | option | a `while` loop carries its halting guard |
| `mergeK` | this module | none | a φ-merge on two names has no rule |
| `searchU` | `Demos/EarlyExit` | exception | `return` inside the loop |
| `countU` | this module | option | a hax loop without `return` |

## Main results

* `feSubC_ts_refines`, `qrFrag_ts_refines`, `searchU_ts_refines`: the abstract
  program at the computed level refines the kernel
* `countU_ts_toExcept`: the `Option` program of `countU` is its exception program
* `searchU_abs_found`: the exception program of `searchU` at `x = 1` throws the
  index `searchAbs` returns
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## `LowCT` kernels -/

/-- The count-down loop `while n != 0 { n := n - 1 }`. -/
def countdownK : LowCT := lowct% while n { n := n - 1 }

/-- A conditional writing two different names, outside the φ-merge rule. -/
def mergeK : LowCT := lowct% if c { x := lit 1 } else { y := lit 2 }

theorem arithK_ts : (Kernel.lowct 0 arithK).tsLevel = some .pure := rfl
theorem bitK_ts : (Kernel.lowct 0 bitK).tsLevel = some .pure := rfl
theorem qrFrag_ts : (Kernel.lowct 0 qrFrag).tsLevel = some .option := rfl
theorem feSubC_ts : (Kernel.lowct 0 feSubC).tsLevel = some .pure := rfl
theorem feAddC_ts : (Kernel.lowct 0 feAddC).tsLevel = some .pure := rfl
theorem avgK_ts : (Kernel.lowct 0 avgK).tsLevel = some .option := rfl
theorem sumK_ts : (Kernel.lowct 0 sumK).tsLevel = some .pure := rfl
theorem countdownK_ts : (Kernel.lowct 8 countdownK).tsLevel = some .option := rfl
theorem mergeK_ts : (Kernel.lowct 0 mergeK).tsLevel = none := rfl

/-- The pass returns the pure transformer of `ascendG` for `feSubC`. -/
theorem feSubC_ts_prog :
    tsLowCT (ε := Empty) 0 feSubC = some (.pure (ascendG 0 feSubC).2) := rfl

/-- `feSubC` refines its pure abstract program at `semScalar`. -/
theorem feSubC_ts_refines :
    (AbsProg.pure (ε := Empty) (ascendG 0 feSubC).2).Refines (fun env => semScalar feSubC env)
      SRwordNT (liftOk SRwordNT) :=
  tsLowCT_sound_scalar 0 feSubC rfl feSubC_ts_prog

/-- The pass returns the `Option` program of `ascendG` for `qrFrag`. -/
theorem qrFrag_ts_prog :
    tsLowCT (ε := Empty) 0 qrFrag =
      some (.option (optGuard (guardsHold (ascendG 0 qrFrag).1) (ascendG 0 qrFrag).2)) := rfl

/-- `qrFrag` refines its `Option` abstract program at `semScalar`. -/
theorem qrFrag_ts_refines :
    (AbsProg.option (ε := Empty) (optGuard (guardsHold (ascendG 0 qrFrag).1)
        (ascendG 0 qrFrag).2)).Refines (fun env => semScalar qrFrag env)
      SRwordNT (liftOk SRwordNT) :=
  tsLowCT_sound_scalar 0 qrFrag rfl qrFrag_ts_prog

/-! ## hax source kernels -/

/-- The counting loop `let i = 0; while i < 3 { i = i + 1 }; i`, without `return`. -/
def countU : _root_.Hax.ImpExpr :=
  .letBind "i" (.lit (.uintLit .w64 0))
   (.letBind "one" (.lit (.uintLit .w64 1))
    (.letBind "three" (.lit (.uintLit .w64 3))
     (.letBind "c" (.app "lt" [.var "i", .var "three"])
      (.seq
        (.whileLoop (.var "c")
          (.seq
            (.assign "i" (.app "add" [.var "i", .var "one"]))
            (.assign "c" (.app "lt" [.var "i", .var "three"]))))
        (.var "i")))))

theorem searchU_ts (x : Nat) : (Kernel.hax searchBuiltins 8 (searchU x)).tsLevel = some .except :=
  rfl

theorem countU_ts : (Kernel.hax searchBuiltins 8 countU).tsLevel = some .option := rfl

/-- `searchU x` refines its exception abstract program. -/
theorem searchU_ts_refines (x : Nat) :
    (tsHax searchBuiltins 8 (searchU x)).Refines (haxPipelineSem searchBuiltins 8 (searchU x))
      haxEntry (fun d r => d = r) :=
  tsHax_sound searchBuiltins searchBuiltins_deepNoControlFlow (searchU x) (searchU_loopScoped x)
    (searchU_noQuestionMark x) (searchU_noCFConstructors x) 8

/-- At `x = 1` the exception program of `searchU` from the empty environment is the run
    of `searchAbs 1`: the thrown index `1`. -/
theorem searchU_abs_found :
    (tsHax searchBuiltins 8 (searchU 1)).toExcept _root_.Hax.Env.empty = some (searchAbs 1 8).run := by
  show outcomeExceptRaw (_root_.Hax.denote searchBuiltins 8 (searchU 1) _root_.Hax.Env.empty).1 = _
  rw [searchU_denote_found, searchAbs_found]
  rfl

/-- The `Option` program of `countU` is its exception program. -/
theorem countU_ts_toExcept :
    (tsHax searchBuiltins 8 countU).toExcept = haxExceptAbs searchBuiltins 8 countU :=
  tsHax_toExcept searchBuiltins 8 countU rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
