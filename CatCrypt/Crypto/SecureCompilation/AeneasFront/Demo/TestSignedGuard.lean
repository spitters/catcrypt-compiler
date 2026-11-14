/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.SignedGuard

/-!
# Tests of the overflow guard of the signed checked operations

The function `incr` binds the checked sum `x + 1` at `i8`. The reader `reifyAeneas%` reads the
sum through its guarded form (`reifyRw_iadd`), `completeAeneas%` proves the reading complete,
and at `x = 127`, where the sum overflows, the reading has no value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.signedGuardTest

open Aeneas.Std
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

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.signedGuardTest
