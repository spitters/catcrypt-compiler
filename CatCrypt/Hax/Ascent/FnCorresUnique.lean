/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Corres

/-!
# The value of a function correspondence is unique

A function correspondence `FnCorres bi e entry G f` fixes the value of every run of `e` from
`entry a` with `G a`: a run that returns a value from some fuel on returns `enc (f a)`, the
eventual value `haxEval bi e (entry a)` is `enc (f a)`, and two correspondences of the same
program, entry and guard have equal encoded results.

## Main results

* `fnCorres_val_unique`: an eventual value of the run is `enc (f a)`.
* `fnCorres_haxEval`: the eventual value `haxEval` of the run is `enc (f a)`.
* `fnCorres_enc_unique`: two correspondences of one program agree on the encoded result.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {bi : Builtins} {A β : Type} [HaxEnc β] {e : ImpExpr} {entry : A → Env}
  {G : A → Prop}

/-- **An eventual value of the run is the encoded result.** Under `FnCorres bi e entry G f`
    and `G a`, a value `v` that the run of `e` from `entry a` returns at every fuel from
    `fuel₀` on is `enc (f a)`. -/
theorem fnCorres_val_unique {f : A → β} (h : FnCorres bi e entry G f) {a : A} (hG : G a)
    {v : Value} {fuel₀ : Nat}
    (hv : ∀ fuel, fuel₀ ≤ fuel → (denote' bi fuel e (entry a)).1 = .val v) :
    v = enc (f a) :=
  fnPartial_of_fnCorres h a hG fuel₀ v (hv fuel₀ (Nat.le_refl _))

/-- The eventual value `haxEval` of the run of `e` from `entry a` is `enc (f a)`. -/
theorem fnCorres_haxEval {f : A → β} (h : FnCorres bi e entry G f) {a : A} (hG : G a) :
    haxEval bi e (entry a) = some (enc (f a)) := by
  obtain ⟨_, hrun⟩ := h a hG
  exact haxEval_eq hrun

/-- Two function correspondences of the same program, entry and guard have equal encoded
    results at every argument satisfying the guard. -/
theorem fnCorres_enc_unique {f g : A → β} (hf : FnCorres bi e entry G f)
    (hg : FnCorres bi e entry G g) {a : A} (hG : G a) : enc (f a) = enc (g a) := by
  obtain ⟨_, hrun⟩ := hg a hG
  exact (fnCorres_val_unique hf hG hrun).symm

end Hax.Ascent
