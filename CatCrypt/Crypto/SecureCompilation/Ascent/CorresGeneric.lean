/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import HaxAscent.Calculus.CorresMCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGenericX86

/-!
# The dialect-generic correspondence `CorresM`

`Corres` (over `semScalar`) and `CorresJ` (over `runBlock`) are two instances of
one forward simulation parameterised by the machine's step function
`step : C → M → Option M`, the relation `CorresM` of `CorresMCore`. This module
shows both are instances and proves the structural core (`weaken`, `seq`)
generically, so the two relations share one proof.

The step abstracts the machine: `semScalar : LowCT → SEnvScalar → Option SEnvScalar`
is already `Option`-valued, and `runBlock : JState 64 → List (JInstr 64) → JState 64`
is total, wrapped as the never-failing `runBlockStep`. The sequencing law each
machine satisfies (`semScalar` over `RSeq`, `runBlock` over `++`) is the single
hypothesis `corresM_seq` needs; both `corres_seq` and `corresJ_append` are its
instances.

This is the "machine-generic `Corres`" the `Com`/dialect framing points at: the
step is the dialect denotation, and one relation covers every machine layer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The two machines as instances

`CorresM` is defined in `CorresMCore`; `runBlockStep` and `corresJ_eq_corresM` (the
`runBlock` instance) are in `CorresGenericX86`. -/

/-- `Corres` is `CorresM` at the scalar machine `semScalar` — definitionally. -/
theorem corres_eq_corresM {AState : Type} (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) :
    Corres SR P fa c = CorresM semScalar SR P fa c := rfl

/-! ## The structural core, proved once -/

/-- Strengthen the precondition (contravariant in `P`) — generic in the machine. -/
theorem corresM_weaken {M C AState : Type} (step : C → M → Option M)
    (SR : M → AState → Prop) {P P' : AState → Prop} {fa : AState → AState} {c : C}
    (h : CorresM step SR P fa c) (himp : ∀ a, P' a → P a) :
    CorresM step SR P' fa c :=
  (corresM_iff_rrelPT step SR P' fa c).mpr (((corresM_iff_rrelPT step SR P fa c).mp h).weaken himp)

/-- Sequencing, generic in the machine: any step whose sequencing is Kleisli-bind
    (`step (seq c₁ c₂) = step c₁ >=> step c₂`) composes two correspondences,
    provided the first re-establishes the second's precondition. Both `semScalar`
    (over `RSeq`) and `runBlock` (over `++`) satisfy the bind law, so `corres_seq`
    and `corresJ_append` are instances. -/
theorem corresM_seq {M C AState : Type} (step : C → M → Option M) (seq : C → C → C)
    (SR : M → AState → Prop)
    (hbind : ∀ c₁ c₂ m, step (seq c₁ c₂) m = (step c₁ m).bind (step c₂))
    {P Q : AState → Prop} {fa ga : AState → AState} {c₁ c₂ : C}
    (h₁ : CorresM step SR P fa c₁) (h₂ : CorresM step SR Q ga c₂)
    (hpre : ∀ a, P a → Q (fa a)) :
    CorresM step SR P (fun a => ga (fa a)) (seq c₁ c₂) := by
  have e : (fun m (_ : Unit) m' => step (seq c₁ c₂) m = some m') =
      CatCrypt.Refinement.stepComp (fun m (_ : Unit) m' => step c₁ m = some m')
        (fun m (_ : Unit) m' => step c₂ m = some m') := by
    funext m _ m'
    simp only [hbind, Option.bind_eq_some_iff, CatCrypt.Refinement.stepComp]
  rw [corresM_iff_rrelPT, e]
  exact ((corresM_iff_rrelPT _ _ _ _ _).mp h₁).seq ((corresM_iff_rrelPT _ _ _ _ _).mp h₂) hpre

/-! ## The bind laws the two machines satisfy -/

/-- `semScalar` sequences by Kleisli-bind over `RSeq` (definitional). -/
theorem semScalar_seq_bind (c₁ c₂ : LowCT) (env : SEnvScalar) :
    semScalar (.RSeq c₁ c₂) env = (semScalar c₁ env).bind (semScalar c₂) := rfl

/-- `runBlockStep` sequences by Kleisli-bind over list append. -/
theorem runBlockStep_append (c₁ c₂ : List (JInstr 64)) (st : JState 64) :
    runBlockStep (c₁ ++ c₂) st = (runBlockStep c₁ st).bind (runBlockStep c₂) := by
  simp only [runBlockStep, Option.bind_some]
  rw [runBlock_append]

/-! ## The instances: the hand-proved cores are `corresM_seq` specialised -/

/-- `corres_seq` (the scalar sequencing lemma) is `corresM_seq` at `semScalar`/`RSeq`. -/
theorem corres_seq_via_generic {AState : Type} (SR : SEnvScalar → AState → Prop)
    {P Q : AState → Prop} {fa ga : AState → AState} {c₁ c₂ : LowCT}
    (h₁ : Corres SR P fa c₁) (h₂ : Corres SR Q ga c₂) (hpre : ∀ a, P a → Q (fa a)) :
    Corres SR P (fun a => ga (fa a)) (.RSeq c₁ c₂) :=
  corresM_seq semScalar .RSeq SR (fun c₁ c₂ m => semScalar_seq_bind c₁ c₂ m) h₁ h₂ hpre

/-- `corresJ_append` (the machine block-concatenation lemma) is `corresM_seq` at
    `runBlockStep`/`++`. -/
theorem corresJ_append_via_generic {AState : Type} (SR : JState 64 → AState → Prop)
    {P Q : AState → Prop} {fa ga : AState → AState} {c₁ c₂ : List (JInstr 64)}
    (h₁ : CorresJ SR P fa c₁) (h₂ : CorresJ SR Q ga c₂) (hpre : ∀ a, P a → Q (fa a)) :
    CorresJ SR P (fun a => ga (fa a)) (c₁ ++ c₂) := by
  rw [corresJ_eq_corresM] at h₁ h₂ ⊢
  exact corresM_seq runBlockStep (· ++ ·) SR runBlockStep_append h₁ h₂ hpre

end CatCrypt.Crypto.SecureCompilation.Ascent
