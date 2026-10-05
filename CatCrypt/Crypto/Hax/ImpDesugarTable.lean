/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.ImpDesugarRem

/-!
# The builtin tables of the desugaring passes

The passes `desugarIte` and `desugarRem` are stated against hypotheses on the builtins:
`SelectSpec`, `Refines` and `WordSpec`. This module proves them for the `u64` table
`Hax.hax64Builtins`, for every table whose values are values of a table that satisfies them,
and for a table with `select` (`ImpToNF.withSelect`).

## Main results

* `selectSpec_withSelect` — a table with `select` satisfies `SelectSpec`.
* `refines_hax64Builtins` — on `Hax.hax64Builtins`, the checked `Sub` and `Add`, where
  defined, agree with the wrapping operations at `64` bits (`Refines` at `hax64Spec`).
* `refines_mono`, `refines_withSelect` — `Refines` passes to a table whose values are
  values of the table, and to the table with `select` when the renaming does not mention
  `select`.
* `wordSpec_hax64Builtins`, `wordSpec_mono`, `wordSpec_withSelect` — the same for
  `WordSpec`.
* `desugar_hax64Builtins` — the three hypotheses at `withSelect Hax.hax64Builtins`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpDesugarTable

open _root_.Hax (Value Builtins)
open CatCrypt.Crypto.Hax.ImpDesugarIte
open CatCrypt.Crypto.Hax.ImpDesugarRem (WordSpec wordSpec_hax64WordOps)
open CatCrypt.Crypto.Hax.ImpToNF (withSelect withSelect_select_bool withSelect_of_ne)

/-! ## 1. `select` -/

/-- A table with `select` satisfies `SelectSpec`. -/
theorem selectSpec_withSelect (bi : Builtins) : SelectSpec (withSelect bi) :=
  fun k x y => withSelect_select_bool bi k x y

/-! ## 2. The renaming of the checked operations -/

/-- A value of `Hax.hax64Builtins`, at a call `Hax.widthArrayOps` does not define, is a value
    of `Hax.hax64WordOps`. -/
theorem word_of_builtins {f : String} {vals : List Value} {v : Value}
    (hn : _root_.Hax.widthArrayOps f vals = none)
    (h : _root_.Hax.hax64Builtins f vals = some v) :
    _root_.Hax.hax64WordOps f vals = some v := by
  have h' : (_root_.Hax.hax64WordOps f vals <|> _root_.Hax.widthArrayOps f vals) = some v := h
  rwa [hn, ImpToNF.orElse_none_eq] at h'

/-- A value of `wrapping_add#64` of `Hax.hax64WordOps` is the sum modulo `2^64` of two words
    below `2^64`. -/
theorem wrapping_add_inv {vals : List Value} {v : Value}
    (h : _root_.Hax.hax64WordOps "wrapping_add#64" vals = some v) :
    ∃ a b : Nat, a < 2 ^ 64 ∧ b < 2 ^ 64 ∧ vals = [.int (a : Int), .int (b : Int)] ∧
      v = .int (((a + b) % 2 ^ 64 : Nat) : Int) := by
  rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;>
    first
      | cases (h.symm.trans (rfl : _ = none))
      | (cases x <;> first
          | cases (h.symm.trans (rfl : _ = none))
          | (cases y <;> first | cases (h.symm.trans (rfl : _ = none)) | skip))
  rw [_root_.Hax.hax64WordOps_wrapping_add] at h
  obtain ⟨x, y, r, hx, hy, rfl, rfl, hg, rfl⟩ := ImpDesugarRem.u64BinOp_some h
  cases hg
  exact ⟨x, y, hx, hy, rfl, rfl⟩

/-- **The renaming `hax64Spec` on `Hax.hax64Builtins`.** Where the checked `Sub` or `Add`
    and the wrapping operation at `64` bits are both defined, their values are equal; every
    other name `hax64Spec` admits is kept. -/
theorem refines_hax64Builtins : Refines _root_.Hax.hax64Builtins hax64Spec := by
  intro f g hfg vals v w hv hw
  unfold hax64Spec at hfg
  split at hfg
  · rename_i hf
    subst hf
    cases hfg
    obtain ⟨a, b, ha, hb, rfl, rfl⟩ := wordSpec_hax64WordOps.wsub vals w (word_of_builtins rfl hw)
    simp only [_root_.Hax.hax64Builtins] at hv
    rw [_root_.Hax.hax64WordOps_Sub, _root_.Hax.u64BinOp_natCast ha hb] at hv
    split at hv
    · rename_i hle
      obtain rfl : _ = v := Option.some.inj hv
      have he : (a + 2 ^ 64 - b) % 2 ^ 64 = a - b := by omega
      rw [he]
    · simp [_root_.Hax.widthArrayOps] at hv
  · split at hfg
    · rename_i hf
      subst hf
      cases hfg
      obtain ⟨a, b, ha, hb, rfl, rfl⟩ := wrapping_add_inv (word_of_builtins rfl hw)
      simp only [_root_.Hax.hax64Builtins] at hv
      rw [_root_.Hax.hax64WordOps_add, _root_.Hax.u64BinOp_natCast ha hb] at hv
      split at hv
      · rename_i hlt
        obtain rfl : _ = v := Option.some.inj hv
        rw [Nat.mod_eq_of_lt hlt]
      · simp [_root_.Hax.widthArrayOps] at hv
    · split at hfg
      · cases hfg
        exact Option.some.inj (hv.symm.trans hw)
      · cases hfg

/-- `Refines` passes to a table whose values are values of the table. -/
theorem refines_mono {bi bi' : Builtins} {ρ : String → Option String} (h : Refines bi ρ)
    (hsub : ∀ f vals v, bi' f vals = some v → bi f vals = some v) : Refines bi' ρ :=
  fun f g hfg vals v w hv hw => h f g hfg vals v w (hsub _ _ _ hv) (hsub _ _ _ hw)

/-- `Refines` passes to the table with `select`, for a renaming that does not mention
    `select`. -/
theorem refines_withSelect {bi : Builtins} {ρ : String → Option String} (h : Refines bi ρ)
    (hρ : ∀ f g, ρ f = some g → f ≠ "select" ∧ g ≠ "select") : Refines (withSelect bi) ρ := by
  intro f g hfg vals v w hv hw
  obtain ⟨hf, hg⟩ := hρ f g hfg
  rw [withSelect_of_ne bi hf] at hv
  rw [withSelect_of_ne bi hg] at hw
  exact h f g hfg vals v w hv hw

/-- The renaming `hax64Spec` does not mention `select`. -/
theorem hax64Spec_ne_select (f g : String) (h : hax64Spec f = some g) :
    f ≠ "select" ∧ g ≠ "select" := by
  unfold hax64Spec at h
  split at h
  · rename_i hf
    subst hf
    cases h
    decide
  · split at h
    · rename_i hf
      subst hf
      cases h
      decide
    · split at h
      · rename_i hmem
        cases h
        have hne : f ≠ "select" := by
          rintro rfl
          exact absurd hmem (by decide)
        exact ⟨hne, hne⟩
      · cases h

/-! ## 3. The word operations of the Barrett sequence -/

/-- **`Hax.hax64Builtins` satisfies `WordSpec`.** -/
theorem wordSpec_hax64Builtins : WordSpec _root_.Hax.hax64Builtins where
  mulhi := fun vals v h => wordSpec_hax64WordOps.mulhi vals v (word_of_builtins rfl h)
  wmul := fun vals v h => wordSpec_hax64WordOps.wmul vals v (word_of_builtins rfl h)
  wsub := fun vals v h => wordSpec_hax64WordOps.wsub vals v (word_of_builtins rfl h)
  lt := fun a b v h => wordSpec_hax64WordOps.lt a b v (word_of_builtins rfl h)
  rem := fun a p v ha hp0 hp h =>
    wordSpec_hax64WordOps.rem a p v ha hp0 hp (word_of_builtins rfl h)

/-- `WordSpec` passes to a table whose values are values of the table. -/
theorem wordSpec_mono {bi bi' : Builtins} (h : WordSpec bi)
    (hsub : ∀ f vals v, bi' f vals = some v → bi f vals = some v) : WordSpec bi' where
  mulhi := fun vals v hv => h.mulhi vals v (hsub _ _ _ hv)
  wmul := fun vals v hv => h.wmul vals v (hsub _ _ _ hv)
  wsub := fun vals v hv => h.wsub vals v (hsub _ _ _ hv)
  lt := fun a b v hv => h.lt a b v (hsub _ _ _ hv)
  rem := fun a p v ha hp0 hp hv => h.rem a p v ha hp0 hp (hsub _ _ _ hv)

/-- `WordSpec` passes to the table with `select`. -/
theorem wordSpec_withSelect {bi : Builtins} (h : WordSpec bi) : WordSpec (withSelect bi) where
  mulhi := fun vals v hv => h.mulhi vals v (by rwa [withSelect_of_ne bi (by decide)] at hv)
  wmul := fun vals v hv => h.wmul vals v (by rwa [withSelect_of_ne bi (by decide)] at hv)
  wsub := fun vals v hv => h.wsub vals v (by rwa [withSelect_of_ne bi (by decide)] at hv)
  lt := fun a b v hv => h.lt a b v (by rwa [withSelect_of_ne bi (by decide)] at hv)
  rem := fun a p v ha hp0 hp hv =>
    h.rem a p v ha hp0 hp (by rwa [withSelect_of_ne bi (by decide)] at hv)

/-! ## 4. The `u64` table with `select` -/

/-- **The hypotheses of the desugaring passes at the `u64` table with `select`**:
    `SelectSpec`, `Refines` at `hax64Spec`, and `WordSpec`. -/
theorem desugar_hax64Builtins :
    SelectSpec (withSelect _root_.Hax.hax64Builtins) ∧
    Refines (withSelect _root_.Hax.hax64Builtins) hax64Spec ∧
    WordSpec (withSelect _root_.Hax.hax64Builtins) :=
  ⟨selectSpec_withSelect _, refines_withSelect refines_hax64Builtins hax64Spec_ne_select,
    wordSpec_withSelect wordSpec_hax64Builtins⟩

end CatCrypt.Crypto.Hax.ImpDesugarTable
