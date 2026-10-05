/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.CorresMCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres

/-!
# `CorresJ` as the x86 instance of `CorresM`

The total block runner `runBlock` is the never-failing step `runBlockStep`, and the
machine correspondence `CorresJ` is `CorresM` at that step. The closure of this module
is `RunBlockCorres` and Lean core.

## Main definitions

* `runBlockStep` — `runBlock` as an `Option`-valued step
* `corresJ_eq_corresM` — `CorresJ` is `CorresM runBlockStep`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The total `runBlock` as a never-failing step. -/
def runBlockStep (c : List (JInstr 64)) (st : JState 64) : Option (JState 64) :=
  some (runBlock st c)

/-- `CorresJ` is `CorresM` at the total `runBlock` step. -/
theorem corresJ_eq_corresM {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔ CorresM runBlockStep SR P fa c := by
  constructor
  · intro h m a hSR hP
    exact ⟨runBlock m c, rfl, h m a hSR hP⟩
  · intro h st a hSR hP
    obtain ⟨m', hstep, hSR'⟩ := h st a hSR hP
    rw [runBlockStep, Option.some.injEq] at hstep
    exact hstep ▸ hSR'

end CatCrypt.Crypto.SecureCompilation.Ascent
