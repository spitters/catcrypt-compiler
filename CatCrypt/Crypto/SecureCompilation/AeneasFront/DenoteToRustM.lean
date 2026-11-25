/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.NFToRustM

/-!
# From the denotation at the reading's table to the Aeneas reading

The denotation of an NF program with the leaf table `aeTable` of the Aeneas reading determines
the reading `nfToRustM`: for a program without `whileLoop`, a value of
`NFProg.denote` under `nfDenote aeTable` at any fuel is the value of `nfToRustM`. This is the
converse direction of `nfToRustM_sim_whileFree`, at the reading's own table: an analysis that
proves a value of the denotation (the range checker of `VIR/NFRange*.lean`) proves a value of
the reading, hence, through a reification, of the Aeneas function.

## Main results

* `aeExpr_of_denote`: a denotation of an expression at `aeTable` is the value of its reading
* `foldlM_of_option`: a fold whose steps transport transports
* `nfToRustM_of_denote`: the transport for every program without `whileLoop`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open HaxLean.Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-- A denotation of an expression with the leaf table `aeTable` is the value of its Aeneas
    reading. -/
theorem aeExpr_of_denote {Γ : Ctxt nfDialect} {t : NfTy} (e : Expr nfDialect Γ t)
    (V : Valuation Γ) {x : t.denote}
    (h : @Expr.denoteM nfDialect Option _ _ (nfDenote aeTable) Γ t e V = some x) :
    aeExpr e V = .ok x := by
  obtain ⟨op, rfl, args⟩ := e
  change nfDenoteOp aeTable op (Expr.lookupArgs args V) = some x at h
  change aeOp op (Expr.lookupArgs args V) = .ok x
  unfold aeOp
  rw [h]

/-- A fold in `Option` whose steps have the values of the steps of a fold in `RustM` has the
    value of that fold. -/
theorem foldlM_of_option {σ : Type} (f : σ → Nat → Option σ) (g : σ → Nat → RustM σ)
    (hfg : ∀ acc i W, f acc i = some W → g acc i = .ok W) :
    ∀ (l : List Nat) (acc W : σ), l.foldlM f acc = some W → l.foldlM g acc = .ok W
  | [], acc, W, h => by
    cases h
    rfl
  | i :: l, acc, W, h => by
    rw [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc', h1, h2⟩ := h
    rw [List.foldlM_cons, hfg acc i acc' h1, bind_tc_ok]
    exact foldlM_of_option f g hfg l acc' W h2

/-- **Transport (a).** For a program without `whileLoop`, a value of its denotation with the
    leaf table `aeTable` of the Aeneas reading, at any fuel, is the value of the reading
    `nfToRustM`. -/
theorem nfToRustM_of_denote : ∀ {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts), p.whileFree = true → ∀ {fuel : Nat} {V : Valuation Γ}
    {W : Valuation (d := nfDialect) ts},
    @NFProg.denote nfDialect _ _ _ _ (nfDenote aeTable) _ fuel Γ ts p V = some W →
      nfToRustM p V = .ok W
  | _, _, .ret vs, _, fuel, V, W, h => by
    cases h
    rw [nfToRustM]
  | _, _, .var e k, hp, fuel, V, W, h => by
    rw [@NFProg.denote_var nfDialect _ _ _ _ (nfDenote aeTable), Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    rw [nfToRustM, aeExpr_of_denote e V hx, bind_tc_ok]
    exact nfToRustM_of_denote k hp h
  | _, _, .forLoop count inits body k, hp, fuel, V, W, h => by
    simp only [NFProg.whileFree, Bool.and_eq_true] at hp
    rw [@NFProg.denote_forLoop nfDialect _ _ _ _ (nfDenote aeTable), Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨acc, hacc, h⟩ := h
    rw [nfToRustM, foldlM_of_option _ _ (fun _ _ _ hW => nfToRustM_of_denote body hp.1 hW)
      _ _ _ hacc, bind_tc_ok]
    exact nfToRustM_of_denote k hp.2 h
  | _, _, .ifThenElse cond thn els k, hp, fuel, V, W, h => by
    simp only [NFProg.whileFree, Bool.and_eq_true] at hp
    rw [@NFProg.denote_ifThenElse nfDialect _ _ _ _ (nfDenote aeTable), Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    have hb : (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) then nfToRustM thn V
        else nfToRustM els V) = .ok r := by
      split
      · rename_i hc
        simp only [hc, ite_true] at hr
        exact nfToRustM_of_denote thn hp.1.1 hr
      · rename_i hc
        simp only [hc] at hr
        exact nfToRustM_of_denote els hp.1.2 hr
    rw [nfToRustM, hb, bind_tc_ok]
    exact nfToRustM_of_denote k hp.2 h
  | _, _, .whileLoop _ _ _, hp, _, _, _, _ => by simp [NFProg.whileFree] at hp
  | _, _, .call _ _ _, _, _, _, _, h => by
    rw [@NFProg.denote_call nfDialect _ _ _ _ (nfDenote aeTable)] at h
    cases h

end CatCrypt.Crypto.SecureCompilation.AeneasFront
