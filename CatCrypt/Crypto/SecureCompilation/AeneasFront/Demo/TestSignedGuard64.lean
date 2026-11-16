/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.SignedGuard64

/-!
# Tests of the overflow guard of the signed checked operations at `i64`

The function `incr` binds the checked sum `x + 1` at `i64`; `incrT` returns it in tail
position; `dec` binds the checked difference `x - y`; `mul` binds the checked product `x * y`
and `mulT` returns it. The reader `reifyAeneas%` reads each through its guarded form
(`reifyRw_iadd64`, `reifyRw_isub64`, `reifyRw_imul64`), `completeAeneas%` proves each reading
complete, and at `x = 2 ^ 63 - 1` (for the sum), `x = -2 ^ 63`, `y = 1` (for the difference)
and `x = 2 ^ 62`, `y = 2` (for the product), where the operation overflows, no reading has a
value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.signedGuard64Test

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Valuation)

/-- `x + 1` at `i64`, its result bound. -/
def incr (x : I64) : RustM I64 := do
  let z ← x + 1#i64
  .ok z

/-- The reading of `incr`. -/
def incrR := reifyAeneas% incr

/-- The reading of `incr` is complete. -/
theorem incr_complete (x : I64) :
    ReifyComplete.CompleteG single (incr x) (vCons x vNil) incrR.prog :=
  (completeAeneas% incrR) x

/-- Test: `incr (2 ^ 63 - 1)` overflows. -/
theorem incr_max : incr 9223372036854775807#i64 = .fail .panic := rfl

/-- **The reading of `incr (2 ^ 63 - 1)` has no value**: the guard aborts. -/
example (W : Valuation (d := nfDialect) [.word 64]) :
    nfToRustM incrR.prog (vCons 9223372036854775807#i64 vNil) ≠ .ok W := fun h => by
  obtain ⟨y, hy, -⟩ := incr_complete 9223372036854775807#i64 W h
  rw [incr_max] at hy
  cases hy

/-- `x + 1` at `i64` in tail position. -/
def incrT (x : I64) : RustM I64 :=
  x + 1#i64

/-- The reading of `incrT`. -/
def incrTR := reifyAeneas% incrT

/-- The reading of `incrT` is complete. -/
theorem incrT_complete (x : I64) :
    ReifyComplete.CompleteG single (incrT x) (vCons x vNil) incrTR.prog :=
  (completeAeneas% incrTR) x

/-- Test: `incrT (2 ^ 63 - 1)` overflows. -/
theorem incrT_max : incrT 9223372036854775807#i64 = .fail .panic := rfl

/-- **The reading of `incrT (2 ^ 63 - 1)` has no value**: the guard aborts. -/
example (W : Valuation (d := nfDialect) [.word 64]) :
    nfToRustM incrTR.prog (vCons 9223372036854775807#i64 vNil) ≠ .ok W := fun h => by
  obtain ⟨y, hy, -⟩ := incrT_complete 9223372036854775807#i64 W h
  rw [incrT_max] at hy
  cases hy

/-- `x - y` at `i64`, its result bound. -/
def dec (x y : I64) : RustM I64 := do
  let z ← x - y
  .ok z

/-- The reading of `dec`. -/
def decR := reifyAeneas% dec

/-- The reading of `dec` is complete. -/
theorem dec_complete (x y : I64) :
    ReifyComplete.CompleteG single (dec x y) (vCons x (vCons y vNil)) decR.prog :=
  (completeAeneas% decR) x y

/-- The least `i64` value `-2 ^ 63`. -/
def minI64 : I64 := ⟨BitVec.ofNat 64 (2 ^ 63)⟩

/-- Test: `dec (-2 ^ 63) 1` overflows. -/
theorem dec_min : dec minI64 1#i64 = .fail .panic := rfl

/-- **The reading of `dec (-2 ^ 63) 1` has no value**: the guard aborts. -/
example (W : Valuation (d := nfDialect) [.word 64]) :
    nfToRustM decR.prog (vCons minI64 (vCons 1#i64 vNil)) ≠ .ok W :=
  fun h => by
    obtain ⟨y, hy, -⟩ := dec_complete minI64 1#i64 W h
    rw [dec_min] at hy
    cases hy

/-- `x * y` at `i64`, its result bound. -/
def mul (x y : I64) : RustM I64 := do
  let z ← x * y
  .ok z

/-- The reading of `mul`. -/
def mulR := reifyAeneas% mul

/-- The reading of `mul` is complete. -/
theorem mul_complete (x y : I64) :
    ReifyComplete.CompleteG single (mul x y) (vCons x (vCons y vNil)) mulR.prog :=
  (completeAeneas% mulR) x y

/-- Test: `mul (2 ^ 62) 2` overflows. -/
theorem mul_ovf : mul 4611686018427387904#i64 2#i64 = .fail .panic := rfl

/-- **The reading of `mul (2 ^ 62) 2` has no value**: the guard aborts. -/
example (W : Valuation (d := nfDialect) [.word 64]) :
    nfToRustM mulR.prog (vCons 4611686018427387904#i64 (vCons 2#i64 vNil)) ≠ .ok W :=
  fun h => by
    obtain ⟨y, hy, -⟩ := mul_complete 4611686018427387904#i64 2#i64 W h
    rw [mul_ovf] at hy
    cases hy

/-- `x * y` at `i64` in tail position. -/
def mulT (x y : I64) : RustM I64 :=
  x * y

/-- The reading of `mulT`. -/
def mulTR := reifyAeneas% mulT

/-- The reading of `mulT` is complete. -/
theorem mulT_complete (x y : I64) :
    ReifyComplete.CompleteG single (mulT x y) (vCons x (vCons y vNil)) mulTR.prog :=
  (completeAeneas% mulTR) x y

/-- Test: `mulT (-2 ^ 62) 2` is `-2 ^ 63`, in bounds. -/
theorem mulT_min :
    mulT ⟨BitVec.ofNat 64 (3 * 2 ^ 62)⟩ 2#i64 = .ok ⟨BitVec.ofNat 64 (2 ^ 63)⟩ :=
  rfl

/-- An assertion of one comparison whose first operand `toU x ^^^ toU y` is computed from the
    arguments and whose second operand `2 ^ 63` is closed. -/
def xorChk (x y : I64) : RustM I64 := do
  massert (toU x ^^^ toU y < sbit64 .I64)
  .ok x

/-- The reading of `xorChk`: the computed operand is read by the call `BitXor#64`
    (`readWordBxor`), the closed operand as a literal. -/
def xorChkR := reifyAeneas% xorChk

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.signedGuard64Test
