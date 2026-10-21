/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates

/-! # Runtime-bound `forFold` simulation (Stage 1a)

The Stage-1a front lowers a hax `forFold 0 hi body` whose upper bound `hi`
is a non-literal `SExpr` (a scalar variable, `2*K`, `min(eta,128)`, …) to the
runtime-bound loop node `RForRuntime v boundE bodyC`
(`impBoundToSExpr hi = some boundE`, `haxToLowCT body = some bodyC`).

Semantically the runtime loop **delegates** to the bounded loop `RFor` at the
trip count obtained by evaluating `boundE` in the entry state (that is exactly
the `RustExec.forRuntime` rule).  This file makes that delegation an explicit
equivalence, so the runtime-loop simulation reduces to the `RFor`-fold
simulation already established in `HaxToLowCTSimulates`. -/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Runtime-loop ↔ bounded-loop delegation

`RForRuntime x bound body` runs exactly `RFor x (bound.evalState rs) body` from
the same entry state `rs`.  Both directions are immediate from the operational
rule `RustExec.forRuntime`. -/

theorem rustExec_forRuntime_iff
    {N : Nat} {leafSpec : LeafSpec} {x : String} {bound : SExpr} {body : LowCT}
    {rs rs' : RustState} :
    RustExec N leafSpec (.RForRuntime x bound body) rs rs'
      ↔ RustExec N leafSpec (.RFor x (bound.evalState rs) body) rs rs' := by
  constructor
  · intro h
    cases h with
    | forRuntime _ _ _ _ _ hInner => exact hInner
  · intro h
    exact RustExec.forRuntime x bound body rs rs' h

/-- Forward delegation: any `RForRuntime` execution is an `RFor` execution at
the entry-state trip count. -/
theorem rustExec_forRuntime_to_rFor
    {N : Nat} {leafSpec : LeafSpec} {x : String} {bound : SExpr} {body : LowCT}
    {rs rs' : RustState}
    (h : RustExec N leafSpec (.RForRuntime x bound body) rs rs') :
    RustExec N leafSpec (.RFor x (bound.evalState rs) body) rs rs' :=
  rustExec_forRuntime_iff.mp h

/-! ## §2  Syntactic unpacker for the runtime `forFold` arm

When the source `forFold 0 hi body` has already been recognised as the runtime
arm (`impBoundToSExpr hi = some boundE`, `haxToLowCT body = some bodyC`, and `hi`
is not one of the two literal-bound shapes handled earlier), the lowering is the
runtime-loop node. -/

theorem haxToLowCT_forFold_runtime_some
    (v : String) (hi body : Hax.ImpExpr)
    (boundE : SExpr) (bodyC : LowCT)
    (hb : impBoundToSExpr hi = some boundE)
    (hbody : haxToLowCT body = some bodyC)
    -- `hi` is not a literal-bound shape (those lower to `RFor`, handled earlier):
    (hnl_int : ∀ n : Int, hi ≠ .lit (.int n))
    (hnl_uint : ∀ (w : Hax.IntWidth) (n : Nat), hi ≠ .lit (.uintLit w n)) :
    haxToLowCT (.forFold v (.lit (.int 0)) hi body)
      = some (.RForRuntime v boundE bodyC) := by
  cases hi with
  | lit l =>
    cases l with
    | int n => exact absurd rfl (hnl_int n)
    | uintLit w n => exact absurd rfl (hnl_uint w n)
    | bool b => simp [haxToLowCT, hb, hbody]
    | unit => simp [haxToLowCT, hb, hbody]
    | sintLit w n => simp [haxToLowCT, hb, hbody]
  | _ => simp [haxToLowCT, hb, hbody]

end CatCrypt.Crypto.Hax
