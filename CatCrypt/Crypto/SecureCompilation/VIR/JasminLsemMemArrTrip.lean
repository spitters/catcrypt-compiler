/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1LsemTie

/-!
# Per-trip array simulation for the emitted `mpn_mul_1` loop body

The consumer `MpnMul1LsemTie.mul1_emitted_machine_val` takes the array-accumulator
faithfulness conclusion as a hypothesis `hfaithful`. That hypothesis is what
`JasminLsemMemSourceTieUncond.loopMemArr_export_faithful_denote` produces from a
per-trip simulation `hsim`. This module supplies the `mpn_mul_1` per-trip
identity that bridges the front-compiled update `mul1Update` to the word-model
step `mul1FoldStep`.

## Main results

* `mul1_stepC` — one `JLoopBodyN.stepC` of the front-compiled `mul1Update` at
  trip `t` on any accumulator array equals the word-model step
  `mul1FoldStep up v arr t`. The `hsim`-shaped right-hand side, discharged from
  `MpnMul1FrontDenote.limbBody_run` through `frontLoopBodyJ_stepC`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC (frontLoopBodyJ_stepC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-- **One trip of the front-compiled `mpn_mul_1` body computes the word step.**
    For any accumulator array `arrt` and trip `t` within the counter range, one
    `JLoopBodyN.stepC` of `mul1Update` at the loop invariants equals the
    word-model `mul1FoldStep`. Discharged from `limbBody_run` (the per-trip
    source run) through `frontLoopBodyJ_stepC`. -/
theorem mul1_stepC (V : Ctxt.Valuation Gouter) (t : Nat)
    (arrt : Fin NR → BitVec 64) (ht : t + 1 < 2 ^ 64) :
    JLoopBodyN.stepC mul1Update (Expr.lookupArgs mul1Invs V) t arrt
      = mul1FoldStep (upVar.lookup V) (vVar.lookup V) arrt t := by
  obtain ⟨env', hrun, hrp⟩ :=
    limbBody_run (upVar.lookup V) (vVar.lookup V) arrt t ht
  exact frontLoopBodyJ_stepC (accCTy := .memref NR) (invCTys := [.sword 64, .memref NU])
    vmBody "rp" limbBodyLowCT limbBody_covered
    (.cons (vVar.lookup V) (.cons (upVar.lookup V) .nil))
    t arrt (mul1Env (upVar.lookup V) (vVar.lookup V) arrt (BitVec.ofNat 64 t)) env'
    (mul1FoldStep (upVar.lookup V) (vVar.lookup V) arrt t)
    (consistentS_mul1Env (upVar.lookup V) (vVar.lookup V) arrt (BitVec.ofNat 64 t))
    hrun hrp mul1Update_eq

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
