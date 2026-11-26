/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakOfCom

/-!
# A counted loop over a straight-line body

For a straight-line body `body : Com d (s :: word :: Γ) s` embedded as `NFProg.ofCom body`,
a counted loop carrying one value of type `s` has a pure denotation and a constant-time
criterion, for every dialect `d`.

## Main results

* `denote_forLoop_ofCom`: the loop denotes its continuation at the `List.range` fold of the
  body denotation.
* `foldl_range_conj`: a fold of a step `g` over `List.range n` that conjugates a step `f`
  through an encoding `enc` is the encoding of the fold of `f`.
* `nfct_forLoop_ofCom`: a loop with a public count whose body has equal events at equal trip
  index, whatever the carried value, whenever the public positions agree, is constant time if
  its continuation is constant time with the carried value secret.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open Ctxt (Valuation)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- **The denotation of a counted loop over a straight-line body** is its continuation at the
    `List.range` fold of the body. -/
theorem denote_forLoop_ofCom [CallDenote d]
    {Γ : Ctxt d} {s : d.Ty} {ts : List d.Ty}
    (count : Ctxt.Var Γ (HasWord64.word (d := d))) (init : Ctxt.Var Γ s)
    (body : Com d (s :: HasWord64.word (d := d) :: Γ) s) (k : NFProg d (s :: Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (NFProg.forLoop (cs := [s]) count (.cons init .nil) (NFProg.ofCom body) k).denote fuel V =
      k.denote fuel (.cons
        ((List.range (HasWord64.toNat (d := d) (count.lookup V))).foldl
          (fun a i => body.denote (.cons a (.cons (HasWord64.ofNat (d := d) i) V)))
          (init.lookup V)) V) := by
  rw [NFProg.denote_forLoop]
  have h := NFProg.foldlM_single
    (fun (acc : Valuation [s]) i => NFProg.denote fuel (NFProg.ofCom body)
      (MultiBlockLowering.hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
    (fun a i => body.denote (.cons a (.cons (HasWord64.ofNat (d := d) i) V)))
    (fun a i => NFProg.denote_ofCom body fuel _)
    (List.range (HasWord64.toNat (d := d) (count.lookup V))) (init.lookup V)
  change (List.foldlM _ (HVector.cons (init.lookup V) HVector.nil) _ >>= _) = _
  rw [h]
  rfl

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenote d] in
/-- **A fold that conjugates a step through an encoding** is the encoding of the fold. -/
theorem foldl_range_conj {α : Type} {s : d.Ty} (enc : α → ⟦s⟧) (f : Nat → α → α)
    (g : ⟦s⟧ → Nat → ⟦s⟧) (n : Nat) (hg : ∀ i < n, ∀ x, g (enc x) i = enc (f i x)) (x : α) :
    (List.range n).foldl g (enc x) = enc ((List.range n).foldl (fun x i => f i x) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))]
      simp only [List.foldl_cons, List.foldl_nil]
      exact hg n (Nat.lt_succ_self n) _

/-- **A counted loop over a straight-line body is constant time** when its count is public and
    the events of the body at each trip index agree for equal public positions, whatever the
    carried value. -/
theorem nfct_forLoop_ofCom (M : LeakModel d) {Γ : Ctxt d} {s : d.Ty} {ts : List d.Ty}
    (L : Labels Γ) (count : Ctxt.Var Γ (HasWord64.word (d := d))) (init : Ctxt.Var Γ s)
    (body : Com d (s :: HasWord64.word (d := d) :: Γ) s) (k : NFProg d (s :: Γ) ts)
    (fuel : Nat) (hc : lvlOf count L = .Public)
    (hb : ∀ (i : Nat) (a₁ a₂ : ⟦s⟧) (V₁ V₂ : Valuation Γ), PubEqV L V₁ V₂ →
      Com.ctLeak M body (.cons a₁ (.cons (HasWord64.ofNat (d := d) i) V₁)) =
        Com.ctLeak M body (.cons a₂ (.cons (HasWord64.ofNat (d := d) i) V₂)))
    (hk : NFCT M (.cons .Secret L) fuel k) :
    NFCT M L fuel
      (NFProg.forLoop (cs := [s]) count (.cons init .nil) (NFProg.ofCom body) k) := by
  intro V₁ V₂ hV
  have hcount : count.lookup V₁ = count.lookup V₂ := hV _ count hc
  have hs : ∀ (i : Nat) (X₁ X₂ : Valuation [s]), PubEqV (allSecret [s]) X₁ X₂ →
      ∃ r₁ r₂, NFProg.leakRun M fuel (NFProg.ofCom body)
          (MultiBlockLowering.hvAppend X₁ (.cons (HasWord64.ofNat (d := d) i) V₁)) = some r₁ ∧
        NFProg.leakRun M fuel (NFProg.ofCom body)
          (MultiBlockLowering.hvAppend X₂ (.cons (HasWord64.ofNat (d := d) i) V₂)) = some r₂ ∧
        r₁.2 = r₂.2 ∧ PubEqV (allSecret [s]) r₁.1 r₂.1 := by
    intro i X₁ X₂ _
    cases X₁ with
    | cons a₁ X₁ =>
      cases X₁
      cases X₂ with
      | cons a₂ X₂ =>
        cases X₂
        exact ⟨_, _, NFProg.leakRun_ofCom M fuel body _, NFProg.leakRun_ofCom M fuel body _,
          hb i a₁ a₂ V₁ V₂ hV, pubEqV_allSecret _ _⟩
  obtain ⟨r₁, r₂, h₁, h₂, he, hr⟩ :=
    forIterLeak_rel (allSecret [s]) _ _ hs (List.range (HasWord64.toNat (d := d)
      (count.lookup V₁))) (Expr.lookupArgs (.cons init .nil) V₁)
      (Expr.lookupArgs (.cons init .nil) V₂) (pubEqV_allSecret _ _)
  have hk' : ∀ X₁ X₂ : Valuation [s], PubEqV (.cons .Secret L)
      (MultiBlockLowering.hvAppend X₁ V₁) (MultiBlockLowering.hvAppend X₂ V₂) := by
    intro X₁ X₂
    cases X₁ with
    | cons x₁ X₁ =>
      cases X₁
      cases X₂ with
      | cons x₂ X₂ =>
        cases X₂
        exact pubEqV_cons hV Jasmin.LowCT.SecretLevel.Secret x₁ x₂ (fun h => nomatch h)
  have hk2 := hk _ _ (hk' r₁.1 r₂.1)
  simp only [NFProg.leakRun]
  rw [← hcount, h₁, h₂]
  simp only [Option.bind_some]
  rcases e₁ : NFProg.leakRun M fuel k (MultiBlockLowering.hvAppend r₁.1 V₁) with _ | q₁ <;>
    rcases e₂ : NFProg.leakRun M fuel k (MultiBlockLowering.hvAppend r₂.1 V₂) with _ | q₂ <;>
    rw [e₁, e₂] at hk2 <;> simp_all

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
