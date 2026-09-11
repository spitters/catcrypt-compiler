/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGeneric
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel64

/-!
# The ascent correspondence at the RV64 machine

`CorresJ` (`RunBlockCorres`) states the correspondence at the x86 `runBlock`.
`CorresR` is the same statement at `runRBlock64`, the RV64 straight-line block
runner, and `corresR_eq_corresM` exhibits it as `CorresM` at that machine's step
— the second instance of the dialect-generic simulation alongside `semScalar`
and `runBlock`.

RV64 has no carry flag and no conditional select, so a borrow is a materialised
word rather than a flag. The structural rules below are therefore the whole of
what transfers from the x86 side; the arithmetic leaves (`corresJ_sbb` and its
chain) have no RV64 analogue and are not restated here.

## Main definitions

* `CorresR` — the correspondence over `runRBlock64`
* `runRBlock64Step` — the total runner as a never-failing step
* `corresR_eq_corresM` — `CorresR` is `CorresM` at that step
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-- Running a concatenation is running each part in turn. -/
theorem runRBlock64_append (s : RState64) (xs ys : List RInst64) :
    runRBlock64 s (xs ++ ys) = runRBlock64 (runRBlock64 s xs) ys := by
  induction xs generalizing s with
  | nil => simp
  | cons i is ih => simp [ih]

/-- From a machine state related by `SR` to an abstract state satisfying `P`,
    running the block lands in a state related to the abstract result. -/
def CorresR {AState : Type} (SR : RState64 → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : List RInst64) : Prop :=
  ∀ s a, SR s a → P a → SR (runRBlock64 s c) (fa a)

variable {AState : Type} (SR : RState64 → AState → Prop)

/-- The empty block transports any `SR` at the identity. -/
theorem corresR_nil : CorresR SR (fun _ => True) id [] := by
  intro s a hSR _
  simpa using hSR

/-- Blocks compose: the abstract steps compose in the same order, provided the
    first step lands in the second's precondition. -/
theorem corresR_append {P Q : AState → Prop} {fa ga : AState → AState}
    {xs ys : List RInst64} (hx : CorresR SR P fa xs) (hy : CorresR SR Q ga ys)
    (hPQ : ∀ a, P a → Q (fa a)) :
    CorresR SR P (ga ∘ fa) (xs ++ ys) := by
  intro s a hSR hP
  rw [runRBlock64_append]
  exact hy _ (fa a) (hx s a hSR hP) (hPQ a hP)

/-- Strengthening the precondition. -/
theorem corresR_weaken {P P' : AState → Prop} {fa : AState → AState}
    {c : List RInst64} (h : CorresR SR P fa c) (hP : ∀ a, P' a → P a) :
    CorresR SR P' fa c := by
  intro s a hSR hP'
  exact h s a hSR (hP a hP')

/-- The total block runner as a never-failing step, the `runBlockStep` twin. -/
def runRBlock64Step (c : List RInst64) (s : RState64) : Option RState64 :=
  some (runRBlock64 s c)

/-- `CorresR` is `CorresM` at the RV64 step. -/
theorem corresR_eq_corresM {AState : Type} (SR : RState64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List RInst64) :
    CorresR SR P fa c ↔ CorresM runRBlock64Step SR P fa c := by
  constructor
  · intro h s a hSR hP
    exact ⟨runRBlock64 s c, rfl, h s a hSR hP⟩
  · intro h s a hSR hP
    obtain ⟨s', hstep, hSR'⟩ := h s a hSR hP
    rw [runRBlock64Step, Option.some.injEq] at hstep
    exact hstep ▸ hSR'

end CatCrypt.Crypto.SecureCompilation.Ascent
