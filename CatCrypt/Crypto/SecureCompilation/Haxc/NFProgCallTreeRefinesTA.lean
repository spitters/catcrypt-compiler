/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree

/-!
# Refinement of trees at an answer predicate: transitivity and the iteration combinators

`RefinesTA Sk` is a transitive relation and a congruence of the tree combinators `ofoldl` and
`owhileIter`, as `RefinesT h₁` is at the answers of a handler.

## Main results

* `RefinesTA.trans`: refinement at a skip predicate composes.
* `RefinesTA.ofoldl`: refined steps give a refined fold.
* `RefinesTA.owhileIter`: refined bodies give a refined exit-flag iteration.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open Ctxt (Valuation)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (obind ofoldl owhileIter)

section Refines

variable {E : EventSig} {Sk : (e : E.Event) → E.Resp e → Prop}

/-- **Transitivity**: refinement up to events skipped at `Sk` composes. -/
theorem RefinesTA.trans {α : Type} {t₁ t₂ t₃ : CallTree E (Option α)}
    (h12 : RefinesTA Sk t₁ t₂) (h23 : RefinesTA Sk t₂ t₃) : RefinesTA Sk t₁ t₃ := by
  induction h12 generalizing t₃ with
  | ret h => subst h; exact h23
  | fail h => exact .fail h
  | vis he _ ih =>
    subst he
    cases h23 with
    | vis he' hk' => exact .vis he' fun a₁ a₂ ha => ih a₁ a₁ HEq.rfl (hk' a₁ a₂ ha)
    | skip hk' => exact .skip fun a ha => ih a a HEq.rfl (hk' a ha)
  | skip _ ih => exact .skip fun a ha => ih a ha h23

/-- Refined steps give a refined fold. -/
theorem RefinesTA.ofoldl {α β : Type} {f₁ f₂ : β → α → CallTree E (Option β)}
    (hf : ∀ b a, RefinesTA Sk (f₁ b a) (f₂ b a)) (l : List α) (b : β) :
    RefinesTA Sk (ofoldl f₁ l b) (ofoldl f₂ l b) := by
  induction l generalizing b with
  | nil => exact RefinesTA.refl _
  | cons a l ih => exact RefinesTA.obind (hf b a) fun b' => ih b'

end Refines

section Iter

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

omit [DialectSignature d] [HasWord64 d] in
/-- Refined bodies give a refined exit-flag iteration. -/
theorem RefinesTA.owhileIter {Sk : (e : E.Event) → E.Resp e → Prop} {cs : List d.Ty}
    {s₁ s₂ : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))}
    (hs : ∀ a, RefinesTA Sk (s₁ a) (s₂ a)) :
    ∀ (n : Nat) (a : Valuation cs), RefinesTA Sk (owhileIter s₁ n a) (owhileIter s₂ n a) := by
  intro n
  induction n with
  | zero => intro a; exact RefinesTA.refl _
  | succ n ih =>
    intro a
    refine RefinesTA.obind (hs a) fun r => ?_
    split
    · exact ih _
    · exact RefinesTA.refl _

end Iter

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA
