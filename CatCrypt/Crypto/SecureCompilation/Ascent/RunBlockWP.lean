/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCryptCore.Refinement.RRelWRP

/-!
# The block run `runBlockM` over `Std.WP`, and `CorresJ` as a `RefinementWP` refinement

The weakest precondition of the block run `runBlockM c` (`Ascent/RunBlockMvcgen.lean`)
in the `Std.WP` instance of `StateM (JState 64)` at a state `s` is the postcondition at
`runBlock s c`. `CorresJ SR P fa c` (`Ascent/RunBlockCorres.lean`) is then the refinement
of the guarded abstract update `optD` by `runBlockM c` at the concretization
`Concretization.ofStateRel SR`, by `CatCrypt.Refinement.WRP.corresRel_iff_refines`.

## Main results

* `wp_runBlockM_std`: `Std.WP.wp (runBlockM c) Q E s ↔ Q () (runBlock s c)`.
* `corresJ_iff_refines`: `CorresJ SR P fa c` is `RefinementWP.Refines` of the guarded
  update by `runBlockM c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.WP Lean.Order
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

variable {A : Type}

/-- The `Std.WP` weakest precondition of the block run `runBlockM c` at `s` is the
    postcondition at `runBlock s c`. -/
theorem wp_runBlockM_std (c : List (JInstr 64)) (Q : Unit → JState 64 → Prop)
    (E) (s : JState 64) :
    Std.WP.wp (runBlockM c) Q E s ↔ Q () (runBlock s c) := by
  have h := runBlockM_run c s
  simp only [runBlockM, List.forM_eq_forM] at h
  simp only [runBlockM, List.forM_eq_forM, StateT.wp_apply_eq, h]
  exact Iff.rfl

open scoped Classical in
/-- `CorresJ SR P fa c` is the `RefinementWP` refinement of the guarded abstract update
    by the block run `runBlockM c`. -/
theorem corresJ_iff_refines (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔
      RefinementWP.Refines top (RefinementWP.Concretization.ofStateRel SR) (fun _ => bot)
        (runBlockM c) (RefinementWP.optD fun a => if P a then some ((), fa a) else none)
        (fun _ _ _ => True) :=
  Iff.trans ⟨fun h s a hs hp => ⟨_, rfl, h s a hs hp⟩,
      fun h s a hs hp => by obtain ⟨_, e, h'⟩ := h s a hs hp; exact e ▸ h'⟩
    (CatCrypt.Refinement.WRP.corresRel_iff_refines (T := fun s s' => runBlock s c = s')
      (runBlockM c) fun Q s =>
        (wp_runBlockM_std c Q _ s).trans ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, hs, h⟩ => hs ▸ h⟩)

end CatCrypt.Crypto.SecureCompilation.Ascent

end
