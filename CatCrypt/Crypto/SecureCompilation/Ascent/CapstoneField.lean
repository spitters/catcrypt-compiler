/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.StoreRefinement

/-!
# Field capstone: a real `feSub`-shape kernel ascends to its field spec

The arithmetic value leaf (`corres_setExpr`, Phase 1 over the `ZMod 2^64` word ring)
composed with the field split surjection (`limbFieldParam`, Phase 2). A subtraction
kernel `r := a - b` over word variables ascends — through the ParamTransfer word-tree
transfer at the leaf — to the pure word spec `φa - φb`, and its output word projects to
the `ZMod p` field value.

Honesty on the field connection: the ascent target is the `ZMod 2^64` *word* subtraction,
projected to `ZMod p`. Matching *true field* subtraction `(a : ZMod p) - (b : ZMod p)`
needs the no-borrow / canonical-range condition (`a ≥ b`, or a conditional add-p) — the
`Corres` precondition of "Way 1". The word ascent itself is unconditional.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open Transfer Transfer.Param

/-- A real `feSub`-shape kernel `r := a - b` (subtraction over word source variables)
    ascends, unconditionally, to its `ZMod 2^64` word spec `φa - φb` — via the arithmetic
    value leaf `corres_setExpr` (whose `SSub` node transfers through the `RelatedBinOp
    wEnc` square). -/
theorem feSub_ascends (aName bName rName : String)
    (hna : ¬ isTmpName aName) (hnb : ¬ isTmpName bName) :
    Corres SRwordNT (fun _ => True)
      (fun φ s => if s = rName then φ aName - φ bName else φ s)
      (.RScalarSetExpr rName (.SSub (.SVar aName) (.SVar bName))) := by
  have h := corres_setExpr rName (.SSub (.SVar aName) (.SVar bName)) ⟨hna, hnb⟩
  simpa only [evalZMod] using h

/-- **Field capstone.** The `feSub`-shape kernel makes progress under the real
    `semScalar`, and its output word `w` at `r` carries the `ZMod p` field projection
    (Phase 2, `limbFieldParam.R`) of the abstract word spec `φa - φb`. Phase-1 arithmetic
    ascent ∘ Phase-2 field split-surjection, on a real subtraction kernel. -/
theorem feSub_word_to_field (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64)
    (aName bName rName : String)
    (hna : ¬ isTmpName aName) (hnb : ¬ isTmpName bName) (hnr : ¬ isTmpName rName)
    (env : SEnvScalar) (φ : String → ZMod (2 ^ 64)) (hSR : SRwordNT env φ) :
    ∃ env' w,
      semScalar (.RScalarSetExpr rName (.SSub (.SVar aName) (.SVar bName))) env = some env' ∧
      env' rName = some ⟨.sword 64, w⟩ ∧
      (limbFieldParam p hp).R w (((φ aName - φ bName).val : ℕ) : ZMod p) := by
  obtain ⟨env', hstep, hSR'⟩ := feSub_ascends aName bName rName hna hnb env φ hSR trivial
  obtain ⟨w, hw, hwe⟩ := hSR' rName hnr
  refine ⟨env', w, hstep, ?_, ?_⟩
  · simpa using hw
  · show ((w.toNat : ℕ) : ZMod p) = (((φ aName - φ bName).val : ℕ) : ZMod p)
    have : φ aName - φ bName = wEnc w := by
      have := hwe; simpa using this.symm
    rw [this]
    simp only [wEnc, ZMod.val_natCast, Nat.mod_eq_of_lt w.isLt]

end CatCrypt.Crypto.SecureCompilation.Ascent
