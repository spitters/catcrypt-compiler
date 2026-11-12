/-
Definitions of the Aeneas test output `tests/lean/Constants.lean` of the Aeneas repository
(https://github.com/AeneasVerif/aeneas) at commit b08bf81f2524ee295a8c37444893acfc9c5f4dde,
Apache License 2.0, copied unchanged: the definitions at the source lines 54-65 of
`Constants.lean` (`constants.Pair`, `constants.mk_pair1`), enclosed in the namespace
`CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo`, with `import Aeneas` replaced by
`import HaxLean.AeneasBackendPrelude`. The functions `structs.incr_x` and `structs.sum` are not
output of Aeneas: they are written in the form the backend prints.
-/
module
public import HaxLean.AeneasBackendPrelude

/-!
# Test inputs: structures of scalars

Three functions on the Aeneas structure `constants.Pair U32 U32`, as source material for
`reifyAeneas%` in `AeneasFront.Demo.CompiledStructs`:

* `constants.mk_pair1`: `Pair { x, y }`, copied from the Aeneas test output `Constants.lean`;
* `structs.incr_x`: `Pair { x: p.x + 1, ..p }`, written in the printed form of the backend;
* `structs.sum`: `p.x + p.y`, written in the printed form of the backend.

The module states no theorem.
-/

@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

namespace constants

/-- [constants::Pair]
    Source: 'tests/src/constants.rs', lines 37:0-40:1
    Visibility: public -/
structure Pair (T1 : Type) (T2 : Type) where
  x : T1
  y : T2

/-- [constants::mk_pair1]:
    Source: 'tests/src/constants.rs', lines 28:0-30:1
    Visibility: public -/
def mk_pair1 (x : Std.U32) (y : Std.U32) : Result (Pair Std.U32 Std.U32) := do
  ok { x, y }

end constants

namespace structs

/-- `fn incr_x(p: Pair<u32, u32>) -> Pair<u32, u32> { Pair { x: p.x + 1, ..p } }`. -/
def incr_x (p : constants.Pair Std.U32 Std.U32) : Result (constants.Pair Std.U32 Std.U32) := do
  let i ← p.x + 1#u32
  ok { p with x := i }

/-- `fn sum(p: Pair<u32, u32>) -> u32 { p.x + p.y }`. -/
def sum (p : constants.Pair Std.U32 Std.U32) : Result Std.U32 := do
  p.x + p.y

end structs

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
