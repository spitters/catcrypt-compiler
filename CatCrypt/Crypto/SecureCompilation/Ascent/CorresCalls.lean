/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockWP
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaWP
public import RefinementWP.Step

/-!
# Correspondences as registered refinements of `wrp_step`

A correspondence `CorresJ` of a block of instructions and a correspondence `CorresIsa` of a
fuel run are refinements of guarded updates (`corresJ_iff_refines`, `corresIsa_iff_refines`).
They are registered here as instances of `RefinementWP.RefinesCall`, with the correspondence
as the condition on the arguments, so that `wrp_step` and `wrp_steps` sequence proved blocks
and leave each correspondence as a goal or close it by a hypothesis.

## Main results

* `corresJ_call`, `corresIsa_call`: the two registrations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.WP Lean.Order RefinementWP
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

variable {A : Type}

open scoped Classical in
/-- `CorresJ SR P fa c` registers the block run `runBlockM c` as a refinement of the guarded
    update by `fa`. -/
instance corresJ_call (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    RefinesCall (runBlockM c) (optD fun a => if P a then some ((), fa a) else none)
      (Concretization.ofStateRel SR) (fun _ : Unit => bot) (CorresJ SR P fa c)
      (fun _ _ _ => True) :=
  ⟨(corresJ_iff_refines SR P fa c).1⟩

open scoped Classical in
/-- `CorresIsa isa p SR Pre fa fuel` registers the fuel run of `p` under `isa` as a refinement of
    the guarded update by `fa`. -/
instance corresIsa_call (isa : VIR.LprogIsa.Isa) (p : VIR.JasminLsemMemLoop.LprogM)
    (SR : VIR.JasminLsemMemFlagGuard.LstateMF → A → Prop) (Pre : A → Prop) (fa : A → A)
    (fuel : Nat) :
    RefinesCall (isa.runM p fuel) (optD fun a => if Pre a then some ((), fa a) else none)
      (Concretization.ofStateRel SR) (fun _ : Unit => bot) (CorresIsa isa p SR Pre fa fuel)
      (fun _ _ _ => True) :=
  ⟨(corresIsa_iff_refines isa p SR Pre fa fuel).1⟩

open scoped Classical in
/-- Two proved blocks compose by `wrp_steps`. -/
example (SR : JState 64 → A → Prop) (P₁ P₂ : A → Prop) (f₁ f₂ : A → A)
    (c₁ c₂ : List (JInstr 64)) (h₁ : CorresJ SR P₁ f₁ c₁) (h₂ : CorresJ SR P₂ f₂ c₂) :
    Refines top (Concretization.ofStateRel SR) (fun _ : Unit => bot)
      (runBlockM c₁ >>= fun _ => runBlockM c₂)
      ((optD fun a => if P₁ a then some ((), f₁ a) else none) >>= fun _ =>
        optD fun a => if P₂ a then some ((), f₂ a) else none)
      (fun _ _ _ => True) := by
  wrp_steps

end CatCrypt.Crypto.SecureCompilation.Ascent

end
