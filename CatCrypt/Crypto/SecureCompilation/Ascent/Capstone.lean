/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Ascend
public import CatCrypt.Crypto.SecureCompilation.Ascent.StoreRefinement

/-!
# The word ascent, pushed forward along the limb decoder

`ascend_sound` (Phase 1, word) gives, for an `IsAscendable` kernel, a `Corres` to
the pure word spec `asemW c` over `ZMod 2^64`. `capstone_word_to_field` states
that result with its conclusion carried along the `ZMod p` cast of
`limbFieldParam` (Phase 2, the `BitVec 64 ↠ ZMod p` split surjection).

The field conjunct is the image of the word conjunct under that cast: both sides
are `w.toNat` cast into `ZMod p`, so it holds for every `p`, and only the `R`
field of the `Param` is used. `IsAscendable` admits `RSkip`, `RBlock`, `RSeq` and
`RScalarSet`, so the kernels it covers assign constants and exercise no
arithmetic.

`Ascent/CapstoneField.lean` states the composing shape over an `r := a - b`
kernel: the output word against a field operation computed in `ZMod p` on the
field projections of the inputs, with the no-borrow side condition it needs. The
arithmetic leaf is `corres_setExpr` / `ascend_expr_sound` in `Ascend.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open Transfer Transfer.Param

/-- For any `IsAscendable` straight-line kernel `c` and output name `out`, running
    the real `semScalar` from an `SRword`-related state makes progress to `some env'`
    and leaves `out` holding a word `w` related by `limbFieldParam.R` to the `ZMod p`
    cast of the abstract word spec `asemW c a out`.

    `ascend_sound` carries the word content; the third conjunct is that result cast
    into `ZMod p`. See the module header. -/
theorem capstone_word_to_field (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64)
    {c : LowCT} (hc : IsAscendable c) (out : String)
    (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) (hSR : SRword env a) :
    ∃ env' w, semScalar c env = some env' ∧ env' out = some ⟨.sword 64, w⟩ ∧
      (limbFieldParam p hp).R w (((asemW c a out).val : ℕ) : ZMod p) := by
  obtain ⟨env', hstep, hSR'⟩ := ascend_sound hc env a hSR trivial
  obtain ⟨w, hw, hwe⟩ := hSR' out
  refine ⟨env', w, hstep, hw, ?_⟩
  -- `limbFieldParam.R w x` is `(w.toNat : ZMod p) = x`; and `(asemW c a out).val = w.toNat`
  show ((w.toNat : ℕ) : ZMod p) = (((asemW c a out).val : ℕ) : ZMod p)
  rw [← hwe]
  simp only [wEnc, ZMod.val_natCast, Nat.mod_eq_of_lt w.isLt]

/-- The single-assignment instance made concrete: `out := 5` ascends to the field value
    `(5 : ZMod p)` on its output word — Phases 0, 1, 2 end-to-end, one theorem. -/
example (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64)
    (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) (hSR : SRword env a) :
    ∃ env' w, semScalar (.RScalarSet "out" 5) env = some env' ∧
      env' "out" = some ⟨.sword 64, w⟩ ∧ (limbFieldParam p hp).R w (5 : ZMod p) := by
  have h := capstone_word_to_field p hp (IsAscendable.rScalarSet "out" 5) "out" env a hSR
  simpa [asemW] using! h

end CatCrypt.Crypto.SecureCompilation.Ascent
