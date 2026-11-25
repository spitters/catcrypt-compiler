/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.SignedGuard

/-!
# Tests of the overflow guard of the signed checked operations

The function `incr` binds the checked sum `x + 1` at `i8`; the function `incrT` returns it in
tail position. The reader `reifyAeneas%` reads the sum through its guarded form
(`reifyRw_iadd`), `completeAeneas%` proves each reading complete, and at `x = 127`, where the
sum overflows, neither reading has a value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.signedGuardTest

open HaxLean.Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Valuation)

/-- `x + 1` at `i8`, its result bound. -/
def incr (x : I8) : RustM I8 := do
  let z ← x + 1#i8
  .ok z

/-- The reading of `incr`. -/
def incrR := reifyAeneas% incr

/-- The reading of `incr` is complete. -/
theorem incr_complete (x : I8) :
    ReifyComplete.CompleteG single (incr x) (vCons x vNil) incrR.prog :=
  (completeAeneas% incrR) x

/-- Test: `incr 127` overflows. -/
theorem incr_127 : incr 127#i8 = .fail .panic := rfl

/-- **The reading of `incr 127` has no value**: the guard aborts. -/
example (W : Valuation (d := nfDialect) [.word 64]) :
    nfToRustM incrR.prog (vCons 127#i8 vNil) ≠ .ok W := fun h => by
  obtain ⟨y, hy, -⟩ := incr_complete 127#i8 W h
  rw [incr_127] at hy
  cases hy

/-- `x + 1` at `i8` in tail position, as Aeneas prints it. -/
def incrT (x : I8) : RustM I8 :=
  x + 1#i8

/-- The reading of `incrT`. -/
def incrTR := reifyAeneas% incrT

/-- The reading of `incrT` is complete. -/
theorem incrT_complete (x : I8) :
    ReifyComplete.CompleteG single (incrT x) (vCons x vNil) incrTR.prog :=
  (completeAeneas% incrTR) x

/-- Test: `incrT 127` overflows. -/
theorem incrT_127 : incrT 127#i8 = .fail .panic := rfl

/-- **The reading of `incrT 127` has no value**: the guard aborts. -/
example (W : Valuation (d := nfDialect) [.word 64]) :
    nfToRustM incrTR.prog (vCons 127#i8 vNil) ≠ .ok W := fun h => by
  obtain ⟨y, hy, -⟩ := incrT_complete 127#i8 W h
  rw [incrT_127] at hy
  cases hy

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.signedGuardTest
