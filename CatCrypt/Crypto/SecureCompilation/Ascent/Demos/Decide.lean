/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AscendDecide
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar

/-!
# Demo: the deciding ascent tactics

Route: a straight-line `LowCT` kernel lifts to its word spec (`asemWExpr` over
`ZMod 2^64`, `asemWBV` over `BitVec 64`) once fragment membership is decided.
`ascend_expr!`, `ascend_bitwise!` and `ascend_unified!` decide membership by one
`decide` on the `Bool` fragment tests and close the goal through the fragment's
soundness theorem (`Ascent/AscendDecide.lean`). `corres_solve_scalar`
(`Ascent/CorresScalar.lean`) reaches the `BitVec 64` spec of the same kernel by
composing leaves instead of deciding a fragment.

## Main results

* `arithK_expr`, `arithK_unified`: an arithmetic kernel lifts to `asemWExpr` by
  `ascend_expr!` and by `ascend_unified!`.
* `bitK_bitwise`, `bitK_solve`: a bitwise kernel lifts to `asemWBV` by
  `ascend_bitwise!` and by `corres_solve_scalar`.
* `seeded_unified`: a kernel with a seeding `RScalarSet` lifts by `ascend_unified!`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Jasmin.LowCT

/-- The arithmetic kernel `t := a + b; r := t * c`. -/
def arithK : LowCT :=
  .RSeq (.RScalarSetExpr "t" (.SAdd (.SVar "a") (.SVar "b")))
    (.RScalarSetExpr "r" (.SMul (.SVar "t") (.SVar "c")))

/-- The bitwise kernel `d := d ^^^ a; b := (b &&& c) >>> 7`. -/
def bitK : LowCT :=
  .RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
    (.RScalarSetExpr "b" (.SShr (.SAnd (.SVar "b") (.SVar "c")) (.SLit 7)))

/-- The arithmetic kernel over `SRwordNT`, at its `ZMod 2^64` spec. -/
theorem arithK_expr : Corres SRwordNT (fun _ => True) (asemWExpr arithK) arithK := by
  ascend_expr!

/-- The bitwise kernel over `SRwordBV`, at its `BitVec 64` spec. -/
theorem bitK_bitwise : Corres SRwordBV (fun _ => True) (asemWBV bitK) bitK := by
  ascend_bitwise!

/-- The arithmetic kernel behind a literal seed, through the unified entry point. -/
theorem seeded_unified :
    Corres SRwordNT (fun _ => True)
      (asemWExpr (.RSeq (.RScalarSet "c" 3) arithK)) (.RSeq (.RScalarSet "c" 3) arithK) := by
  ascend_unified!

/-- The same goal as `arithK_expr`, by the unified entry point. -/
theorem arithK_unified : Corres SRwordNT (fun _ => True) (asemWExpr arithK) arithK := by
  ascend_unified!

/-- The same goal as `bitK_bitwise`, by leaf composition. -/
theorem bitK_solve : Corres SRwordBV (fun _ => True) (asemWBV bitK) bitK := by
  unfold bitK
  corres_solve_scalar

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.arithK_expr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms arithK_expr
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.bitK_bitwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bitK_bitwise
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.seeded_unified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seeded_unified
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.arithK_unified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms arithK_unified
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.bitK_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bitK_solve
end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
