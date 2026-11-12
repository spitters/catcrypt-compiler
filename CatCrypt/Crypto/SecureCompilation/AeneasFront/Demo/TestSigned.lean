/-
Definitions of the Aeneas test outputs `tests/lean/Constants.lean` and `tests/lean/Paper.lean`
of the Aeneas repository (https://github.com/AeneasVerif/aeneas) at commit
b08bf81f2524ee295a8c37444893acfc9c5f4dde, Apache License 2.0, copied unchanged: the definitions
at the source lines 129-134 of `Constants.lean` (`constants.add`) and 22-26 of `Paper.lean`
(`paper.ref_incr`), enclosed in the namespace `CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo`,
with `import Aeneas` replaced by `import HaxLean.AeneasBackendPrelude`. The function
`signed.abs_diff` is not output of Aeneas: it is written in the form the backend prints.
-/
module
public import HaxLean.AeneasBackendPrelude

/-!
# Test inputs: signed scalars

Three functions on the Aeneas signed integer `I32`, as source material for `reifyAeneas%` in
`AeneasFront.Demo.CompiledSigned`:

* `constants.add`: `a + b`, copied from the Aeneas test output `Constants.lean`;
* `paper.ref_incr`: `x + 1`, copied from the Aeneas test output `Paper.lean`;
* `signed.abs_diff`: `if x < y { y - x } else { x - y }`, written in the printed form of the
  backend.

The module states no theorem.
-/

@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

namespace constants

/-- [constants::add]:
    Source: 'tests/src/constants.rs', lines 67:0-69:1
    Visibility: public -/
def add (a : Std.I32) (b : Std.I32) : Result Std.I32 := do
  a + b

end constants

namespace paper

/-- [paper::ref_incr]:
    Source: 'tests/src/paper.rs', lines 7:0-9:1
    Visibility: public -/
def ref_incr (x : Std.I32) : Result Std.I32 := do
  x + 1#i32

end paper

namespace signed

/-- `fn abs_diff(x: i32, y: i32) -> i32 { if x < y { y - x } else { x - y } }`. -/
def abs_diff (x : Std.I32) (y : Std.I32) : Result Std.I32 := do
  if x < y
  then y - x
  else x - y

end signed

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
