/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGenericSpec
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscv

/-!
# The machine correspondences for an arbitrary postcondition

The three machine instances of `corresM_iff_post` (`CorresGenericSpec`), through the
identifications of `CorresGeneric` and `CorresRiscv`: `corres_post` for `Corres`
over `semScalar`, `corresJ_post_generic` for `CorresJ` over `runBlock`, and
`corresR_post` for `CorresR` over `runRBlock64`. The two total machines state the
conclusion at the state the runner returns.

## Main definitions

* `corres_iff_post`, `corres_post` — `Corres` over `semScalar`
* `corresJ_iff_post_generic`, `corresJ_post_generic` — `CorresJ` over `runBlock`
* `corresR_iff_post`, `corresR_post` — `CorresR` over `runRBlock64`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## The three machine instances -/

section Instances

variable {AState : Type} {P : AState → Prop} {fa : AState → AState}

/-- `Corres` over `semScalar` as the family of step triples over all postconditions. -/
theorem corres_iff_post {SR : SEnvScalar → AState → Prop} {c : LowCT} :
    Corres SR P fa c ↔ ∀ Q : SEnvScalar → Prop,
      StepTriple semScalar
        (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q := by
  rw [corres_eq_corresM]
  exact corresM_iff_post

/-- A `Corres` correspondence gives a `semScalar` step triple for every
    postcondition. -/
theorem corres_post {SR : SEnvScalar → AState → Prop} {c : LowCT}
    (h : Corres SR P fa c) (Q : SEnvScalar → Prop) :
    StepTriple semScalar
      (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q :=
  corres_iff_post.mp h Q

/-- A step triple over the never-failing `runBlockStep` is its postcondition at the
    state `runBlock` returns. -/
theorem stepTriple_runBlockStep_iff {pre post : JState 64 → Prop}
    {c : List (JInstr 64)} :
    StepTriple runBlockStep pre c post ↔ ∀ st, pre st → post (runBlock st c) := by
  constructor
  · intro h st hst
    obtain ⟨m', hstep, hm'⟩ := h st hst
    rw [runBlockStep, Option.some.injEq] at hstep
    exact hstep ▸ hm'
  · intro h st hst
    exact ⟨runBlock st c, rfl, h st hst⟩

/-- `CorresJ` over `runBlock` as the family over all postconditions, derived from the
    generic `corresM_iff_post` through `corresJ_eq_corresM`. -/
theorem corresJ_iff_post_generic {SR : JState 64 → AState → Prop}
    {c : List (JInstr 64)} :
    CorresJ SR P fa c ↔ ∀ Q : JState 64 → Prop, ∀ st,
      (∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → Q st') → Q (runBlock st c) := by
  rw [corresJ_eq_corresM, corresM_iff_post]
  exact forall_congr' fun _ => stepTriple_runBlockStep_iff

/-- A `CorresJ` correspondence gives, for every postcondition `Q`, `Q` at the state
    `runBlock` returns. -/
theorem corresJ_post_generic {SR : JState 64 → AState → Prop} {c : List (JInstr 64)}
    (h : CorresJ SR P fa c) (Q : JState 64 → Prop) (st : JState 64)
    (hpre : ∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → Q st') :
    Q (runBlock st c) :=
  corresJ_iff_post_generic.mp h Q st hpre

/-- A step triple over the never-failing `runRBlock64Step` is its postcondition at
    the state `runRBlock64` returns. -/
theorem stepTriple_runRBlock64Step_iff {pre post : RState64 → Prop}
    {c : List RInst64} :
    StepTriple runRBlock64Step pre c post ↔ ∀ s, pre s → post (runRBlock64 s c) := by
  constructor
  · intro h s hs
    obtain ⟨s', hstep, hs'⟩ := h s hs
    rw [runRBlock64Step, Option.some.injEq] at hstep
    exact hstep ▸ hs'
  · intro h s hs
    exact ⟨runRBlock64 s c, rfl, h s hs⟩

/-- `CorresR` over `runRBlock64` as the family over all postconditions. -/
theorem corresR_iff_post {SR : RState64 → AState → Prop} {c : List RInst64} :
    CorresR SR P fa c ↔ ∀ Q : RState64 → Prop, ∀ s,
      (∃ a, SR s a ∧ P a ∧ ∀ s', SR s' (fa a) → Q s') → Q (runRBlock64 s c) := by
  rw [corresR_eq_corresM, corresM_iff_post]
  exact forall_congr' fun _ => stepTriple_runRBlock64Step_iff

/-- A `CorresR` correspondence gives, for every postcondition `Q`, `Q` at the state
    `runRBlock64` returns. -/
theorem corresR_post {SR : RState64 → AState → Prop} {c : List RInst64}
    (h : CorresR SR P fa c) (Q : RState64 → Prop) (s : RState64)
    (hpre : ∃ a, SR s a ∧ P a ∧ ∀ s', SR s' (fa a) → Q s') :
    Q (runRBlock64 s c) :=
  corresR_iff_post.mp h Q s hpre

end Instances

end CatCrypt.Crypto.SecureCompilation.Ascent
