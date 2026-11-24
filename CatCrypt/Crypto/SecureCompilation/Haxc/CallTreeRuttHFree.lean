/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.CodeRel
public import CatCryptCore.Crypto.Party.ViewRelCode
public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeRutt
public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP

/-!
# Related call trees as the heterogeneous lift of free monads

A call tree `CallTree E R` is the free monad `PFunctor.FreeM (sigPF E) R`, so the coercion
between the two is the identity. An event relation `RE` and an answer relation `RA` form the
signature relation `toSigRel RE RA` between `sigPF E₁` and `sigPF E₂`, and `Rutt` at the empty
failure predicate is the heterogeneous lift `HFreeRel (toSigRel RE RA)` of the leaf relation.

The interpretations `interp` and `interpSP` are `FreeM.liftM` in the monads `Id` and `SPComp`.
Through the equivalence, the interpretation theorems `interp_rutt` and `interpSP_rutt` at the
empty failure predicate are instances of `HFreeRel.liftM_rel`: at the relational lifting of `Id`
by the relation itself, and at the lifting `rHoareRelLift I` of `SPComp` by `rHoare`.

## Main definitions

* `toSigRel`: the signature relation given by an event and an answer relation.
* `idRelLift`: the relational lifting of `Id` by the relation itself.

## Main results

* `rutt_false_iff_hFreeRel`: `Rutt` at the empty failure predicate is `HFreeRel`.
* `interp_eq_liftM`, `interpSP_eq_liftM`: the interpretations are `FreeM.liftM`.
* `interp_rutt_false`, `interpSP_rutt_false`: `interp_rutt` and `interpSP_rutt` at the empty
  failure predicate, derived from `HFreeRel.liftM_rel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeRuttHFree

open CatCrypt.Container CatCrypt.Core CatCrypt.Relational
open CatCrypt.Crypto.Party (rHoareRelLift)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP (HandlerCoupled interpSP_rutt)

/-- The signature relation between `sigPF E₁` and `sigPF E₂` given by a relation on events and
    a relation on answers. -/
def toSigRel {E₁ E₂ : EventSig} (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop) :
    SigRel (sigPF E₁) (sigPF E₂) where
  pos := RE
  dir := RA

section Relation

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type} {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → R₂ → Prop}

/-- **`Rutt` at the empty failure predicate is the heterogeneous lift** of the leaf relation
    along `toSigRel RE RA`. -/
theorem rutt_false_iff_hFreeRel {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} :
    Rutt RE RA RR (fun _ => False) t₁ t₂ ↔ HFreeRel (toSigRel RE RA) RR t₁ t₂ := by
  constructor
  · intro h
    induction h with
    | ret h => exact HFreeRel.pure h
    | fail h => exact h.elim
    | vis he _ ih => exact HFreeRel.liftBind he ih
  · intro h
    induction h with
    | pure h => exact Rutt.ret h
    | liftBind he _ ih => exact Rutt.vis he ih

end Relation

/-! ## Interpretations as `FreeM.liftM` -/

/-- **Interpretation under a pure handler is `FreeM.liftM` in `Id`.** -/
theorem interp_eq_liftM {E : EventSig} {R : Type} (h : ∀ e : E.Event, E.Resp e)
    (t : CallTree E R) : interp h t = PFunctor.FreeM.liftM (m := Id) h t := by
  induction t with
  | ret r => rfl
  | vis e k ih => exact ih (h e)

/-- **Interpretation in `SPComp` is `FreeM.liftM` in `SPComp`.** -/
theorem interpSP_eq_liftM {E : EventSig} {R : Type} (h : ∀ e : E.Event, SPComp (E.Resp e))
    (t : CallTree E R) : interpSP h t = PFunctor.FreeM.liftM (m := SPComp) h t := by
  induction t with
  | ret r => rfl
  | vis e k ih =>
    rw [interpSP_vis]
    change _ = (h e >>= fun u => PFunctor.FreeM.liftM (m := SPComp) h (k u))
    simp only [← ih]
    rfl

/-- The relational lifting of `Id` by the relation itself. -/
def idRelLift : RelLift Id Id where
  rel R a b := R a b
  rel_pure h := h
  rel_bind hc hf := hf _ _ hc

/-! ## The interpretation theorems as instances of `HFreeRel.liftM_rel` -/

section Interp

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type} {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → R₂ → Prop}

/-- **Interpretation of related trees** (`interp_rutt` at the empty failure predicate), as the
    instance of `HFreeRel.liftM_rel` at the lifting `idRelLift`. -/
theorem interp_rutt_false (h₁ : ∀ e : E₁.Event, E₁.Resp e) (h₂ : ∀ e : E₂.Event, E₂.Resp e)
    (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : Rutt RE RA RR (fun _ => False) t₁ t₂) :
    False ∨ RR (interp h₁ t₁) (interp h₂ t₂) := by
  refine .inr ?_
  rw [interp_eq_liftM, interp_eq_liftM]
  exact HFreeRel.liftM_rel idRelLift (S := toSigRel RE RA) hh (rutt_false_iff_hFreeRel.1 h)

/-- **Probabilistic interpretation of related trees** (`interpSP_rutt` at the empty failure
    predicate), as the instance of `HFreeRel.liftM_rel` at the lifting `rHoareRelLift I`. -/
theorem interpSP_rutt_false {I : RPre}
    {h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e)} {h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)}
    (hc : HandlerCoupled I RE RA h₁ h₂)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : Rutt RE RA RR (fun _ => False) t₁ t₂) :
    rHoare I (interpSP h₁ t₁) (interpSP h₂ t₂)
      (fun r₁ s₁ r₂ s₂ => False ∨ (RR r₁ r₂ ∧ I s₁ s₂)) := by
  have key := HFreeRel.liftM_rel (rHoareRelLift I) (S := toSigRel RE RA) hc
    (rutt_false_iff_hFreeRel.1 h)
  rw [← interpSP_eq_liftM, ← interpSP_eq_liftM] at key
  exact rHoare_conseq (fun _ _ hI => hI) (fun _ _ _ _ hp => Or.inr hp) key

end Interp

end CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeRuttHFree
