/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# The leaf-call hypothesis `LeafImplOk` at every fuel is unsatisfiable

`LowCTToJasmin.LeafImplOk leafSpec env fuel` asks that the translated leaf call,
run by `translateCmd env _ sid fuel`, evaluates to a point distribution. At fuel
`0`, `translateCmd` returns the code `.fail`, whose evaluation is
`SDistr.fail = PMF.pure none`, which is not a point distribution on a result.
The premises of `LeafImplOk` are satisfiable (a state binding one tower variable
to the value its heap cell holds), so `∀ fuel', LeafImplOk leafSpec env fuel'` is
false for every `leafSpec` and `env`.

`rustExecSimulates`, `rustCallSimulates`, `rustCloneCallSimulates`,
`rustExecSimulates_emptyInlineRegistry`, `rustExecSimulates_with_inlines` and
`rustExecSimulates_withCalls` take this hypothesis.

## Contents

* `not_forall_leafImplOk` — the refutation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin
open CatCrypt.Core CatCrypt.Deep CatCrypt.Prob

/-- `LeafImplOk` holds at no family of fuels containing `0`: the translated call
    at fuel `0` evaluates to the failure distribution. -/
theorem not_forall_leafImplOk (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', LeafImplOk leafSpec env fuel' := by
  intro h
  let heap0 : Heap := default
  let dest : Located := mkFpLoc "x"
  let v0 : RustVal dest.locDst := heap0.get (towerLoc 1 "x" dest.locDst)
  let rs0 : RustState :=
    { rsTower := fun y => if y = "x" then some ⟨dest.locDst, v0⟩ else none,
      rsScalar := fun _ => 0 }
  have hInv : HeapInv rs0 heap0 1 := by
    intro y t v hy
    by_cases hyx : y = "x"
    · subst hyx
      simp only [rs0, if_true, Option.some.injEq, Sigma.mk.inj_iff] at hy
      obtain ⟨rfl, hv⟩ := hy
      cases hv
      rfl
    · simp [rs0, hyx] at hy
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 "f" dest [] rs0 1 heap0 v0 [] hInv (by simp [rs0, dest, mkFpLoc]) rfl
  have hfail := congrArg (fun p : SDistr _ => p none) hEval
  simp [translateCmd, SPComp.fail, SDistr.fail, SDistr.pure] at hfail

end CatCrypt.Crypto.Jasmin.LowCT
