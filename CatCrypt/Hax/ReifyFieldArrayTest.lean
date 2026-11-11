/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyField

/-!
# Tests of `reifyField%` on arrays of field elements

Three functions over `Array (ZMod 2013265921)` (BabyBear) read by `reifyField%`: a read at a
fixed index, a read at the loop index inside `Hax.foldRange`, and a loop carrying an array that
it updates at the loop index from two input arrays (the shape of a FRI fold). Each literal is
stated in full, lifted by `ImpExpr.toTExpr` with the arrays typed `.array (.uint .w64) n`, and
validated by `ascend_reified` under the runtime table `runtimeBuiltins hax64Builtins`, whose
`index` and `array_update` are the runtime leaves of `Hax.index` and `Hax.array_update`.

## Main results

* `readFixed_fnCorres`, `sum_fnCorres`, `foldUpd_fnCorres` — the literals denote the functions
* `readFixedImp_toTExpr_isSome`, `sumImp_toTExpr_isSome`, `foldUpdImp_toTExpr_isSome` — the
  lifts to typed expressions exist
* `readFixedImp_ty` — the read of an array of `u64` words is typed as one `u64` word
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ReifyFieldArrayTest

open _root_.Hax _root_.Hax.Ascent CatCrypt.Hax.ReifyField

/-- The runtime table answers the BabyBear head of `mul` by the encoding of the product. -/
theorem runtimeBuiltins_mul_babyBear (x y : ZMod 2013265921) :
    runtimeBuiltins hax64Builtins "mul#p2013265921" [enc x, enc y] = some (enc (x * y)) :=
  runtimeBuiltins_zmod_mul _ (by decide) (by norm_num) x y

/-- The runtime table answers the BabyBear head of `add` by the encoding of the sum. -/
theorem runtimeBuiltins_add_babyBear (x y : ZMod 2013265921) :
    runtimeBuiltins hax64Builtins "add#p2013265921" [enc x, enc y] = some (enc (x + y)) :=
  runtimeBuiltins_zmod_add _ (by decide) (by norm_num) x y

/-- The runtime table answers `index` on an array of BabyBear elements by the encoding of
    `Hax.index`. -/
theorem runtimeBuiltins_index_babyBear (a : Array (ZMod 2013265921)) (i : Int) :
    runtimeBuiltins hax64Builtins "index" [enc a, .int i] = some (enc (Hax.index a i)) :=
  runtimeBuiltins_index_zmod _ (by norm_num) a i

/-! ## A read at a fixed index -/

/-- The element at `3` of `a`, multiplied by `x`. -/
def readFixedLean (a : Array (ZMod 2013265921)) (x : ZMod 2013265921) : ZMod 2013265921 :=
  Hax.index a 3 * x

/-- The literal of `readFixedLean`. -/
def readFixedImp : ImpExpr := reifyField% readFixedLean

/-- The literal of `readFixedLean`: the index `3` bound to `t`, the call `index`, the product
    (a test, checked by `rfl`). -/
theorem readFixedImp_eq : readFixedImp =
    .letBind "t" (.lit (.int 3))
    (.letBind "t_1" (.app "index" [.var "a", .var "t"])
    (.letBind "t_2" (.app "mul#p2013265921" [.var "t_1", .var "x"]) (.var "t_2"))) :=
  rfl

/-- The lift of `readFixedImp` with `a` typed as `8` words exists (a test, checked by
    `rfl`). -/
theorem readFixedImp_toTExpr_isSome :
    (readFixedImp.toTExpr [("a", .array (.uint .w64) 8), ("x", .uint .w64)]).isSome = true := by
  rfl

/-- The lift of `readFixedImp` is typed as one `u64` word (a test, checked by `rfl`). -/
theorem readFixedImp_ty :
    (readFixedImp.toTExpr [("a", .array (.uint .w64) 8), ("x", .uint .w64)]).map TExpr.ty =
      some (.uint .w64) := by
  rfl

/-- The literal `readFixedImp` returns the encoding of `readFixedLean` under the runtime
    table. -/
theorem readFixed_fnCorres :
    FnCorres (runtimeBuiltins hax64Builtins) readFixedImp
      (A := Array (ZMod 2013265921) × ZMod 2013265921 × Unit)
      (fun a => bindParams [("a", enc a.1), ("x", enc a.2.1)]) (fun _ => True)
      (fun a => readFixedLean a.1 a.2.1) := by
  ascend_reified readFixedLean using [runtimeBuiltins_mul_babyBear,
    runtimeBuiltins_index_babyBear]

/-! ## A read at the loop index -/

/-- `x` plus the first eight elements of `a`, as a counted fold. -/
def sumLean (a : Array (ZMod 2013265921)) (x : ZMod 2013265921) : ZMod 2013265921 :=
  Hax.foldRange 0 8 x fun i s => s + Hax.index a i

/-- The literal of `sumLean`. -/
def sumImp : ImpExpr := reifyField% sumLean

/-- The literal of `sumLean`: a `forFold` over `[0, 8)` whose body reads `a` at the loop index
    (a test, checked by `rfl`). -/
theorem sumImp_eq : sumImp =
    .letBind "s" (.var "x")
    (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 8))
      (.letBind "t" (.app "index" [.var "a", .var "i"])
      (.letBind "s" (.app "add#p2013265921" [.var "s", .var "t"]) (.var "s"))))
      (.var "s")) :=
  rfl

/-- The lift of `sumImp` exists (a test, checked by `rfl`). -/
theorem sumImp_toTExpr_isSome :
    (sumImp.toTExpr [("a", .array (.uint .w64) 8), ("x", .uint .w64)]).isSome = true := by
  rfl

/-- The literal `sumImp` returns the encoding of `sumLean` under the runtime table. -/
theorem sum_fnCorres :
    FnCorres (runtimeBuiltins hax64Builtins) sumImp
      (A := Array (ZMod 2013265921) × ZMod 2013265921 × Unit)
      (fun a => bindParams [("a", enc a.1), ("x", enc a.2.1)]) (fun _ => True)
      (fun a => sumLean a.1 a.2.1) := by
  ascend_reified sumLean using [runtimeBuiltins_add_babyBear, runtimeBuiltins_index_babyBear]

/-! ## An array carried and updated by a loop -/

/-- The array `a` with its element at `i` replaced by `a[i] + c * b[i]` for `i < 4`, as a
    counted fold carrying the array. -/
def foldUpdLean (a b : Array (ZMod 2013265921)) (c : ZMod 2013265921) :
    Array (ZMod 2013265921) :=
  Hax.foldRange 0 4 a fun i o => Hax.array_update o i (Hax.index a i + c * Hax.index b i)

/-- The literal of `foldUpdLean`. -/
def foldUpdImp : ImpExpr := reifyField% foldUpdLean

/-- The literal of `foldUpdLean`: the accumulator `o` bound to `a`, and a `forFold` whose body
    reads `a` and `b` at the loop index and rebinds `o` to the update (a test, checked by
    `rfl`). -/
theorem foldUpdImp_eq : foldUpdImp =
    .letBind "o" (.var "a")
    (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 4))
      (.letBind "t" (.app "index" [.var "a", .var "i"])
      (.letBind "t_1" (.app "index" [.var "b", .var "i"])
      (.letBind "t_2" (.app "mul#p2013265921" [.var "c", .var "t_1"])
      (.letBind "t_3" (.app "add#p2013265921" [.var "t", .var "t_2"])
      (.letBind "o" (.app "array_update" [.var "o", .var "i", .var "t_3"]) (.var "o")))))))
      (.var "o")) :=
  rfl

/-- The lift of `foldUpdImp` with `a`, `b` typed as `4` words exists (a test, checked by
    `rfl`). -/
theorem foldUpdImp_toTExpr_isSome :
    (foldUpdImp.toTExpr [("a", .array (.uint .w64) 4), ("b", .array (.uint .w64) 4),
      ("c", .uint .w64)]).isSome = true := by
  rfl

/-- The literal `foldUpdImp` returns the encoding of `foldUpdLean` under the runtime table. -/
theorem foldUpd_fnCorres :
    FnCorres (runtimeBuiltins hax64Builtins) foldUpdImp
      (A := Array (ZMod 2013265921) × Array (ZMod 2013265921) × ZMod 2013265921 × Unit)
      (fun a => bindParams [("a", enc a.1), ("b", enc a.2.1), ("c", enc a.2.2.1)])
      (fun _ => True)
      (fun a => foldUpdLean a.1 a.2.1 a.2.2.1) := by
  ascend_reified foldUpdLean using [runtimeBuiltins_add_babyBear, runtimeBuiltins_mul_babyBear,
    runtimeBuiltins_index_babyBear, RuntimeOps.array_update_enc]

end CatCrypt.Hax.ReifyFieldArrayTest
