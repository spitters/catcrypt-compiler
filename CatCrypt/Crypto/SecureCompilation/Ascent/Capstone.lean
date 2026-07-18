/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Ascend
import CatCrypt.Crypto.SecureCompilation.Ascent.StoreRefinement

/-!
# Capstone: the word ascent composed with the field split-surjection

Ties the two value phases end-to-end. `ascend_sound` (Phase 1, word) gives, for an
`IsAscendable` kernel, a `Corres` to the pure word spec `asemW c` over `ZMod 2^64`;
`limbFieldParam` (Phase 2, the `BitVec 64 ↠ ZMod p` split surjection) projects a word to
its field value. Composing them: the kernel's output word carries the field value of its
abstract spec, projected through `limbFieldParam.R`.

Frontier (= the descent's): a *field-arithmetic* capstone (e.g. `feSub`) additionally
needs the `RScalarSetExpr` leaf (`semLowerSExpr` guard) so the kernel can carry `SExpr`
arithmetic; the value-tree transfer through `wEnc` (`composeBinOp`, in `Corres`) is the
mechanism, the loop is the counted `corres_for`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open Transfer Transfer.Param

/-- **Capstone.** For any `IsAscendable` straight-line kernel `c` and output name `out`,
    running the real `semScalar` from an `SRword`-related state (Phase 0: it makes
    progress to `some env'`) leaves `out` holding a word `w` whose **field** projection
    (Phase 2, `limbFieldParam.R`) is the `ZMod p` value of the abstract word spec
    (Phase 1, `asemW c a out`). The word ascent and the field split-surjection compose. -/
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
  simpa [asemW] using h

end CatCrypt.Crypto.SecureCompilation.Ascent
