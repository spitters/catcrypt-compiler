/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom

/-!
# Global value numbering of multi-return programs

The value numbering `gvnGo` of `Optimizer/Rewrite/AegraphGeneric.lean` on the multi-return
programs `MultiReturnCom d Γ ts` of `VIR/MultiReturnCom.lean`. The traversal is that of
`gvnGo`: it walks the let-chain once, carrying a renaming `ρ : Ctxt.Hom Γ Δ` from the
context of the input program to the context of the output program and the node table
`Tbl d`; a binding of an operation satisfying `pure` whose renamed key (operation,
argument levels) is recorded is dropped and its variable mapped to the recorded node. The
returned variables are renamed by `ρ`.

One table spans the whole program, so the bindings of two outputs that compute the same
node from the same arguments are merged across the outputs.

## Main results

* `gvnMRGo_denote`: under a table sound for `V`, the output of the traversal denotes the
  input at the valuation pulled back along the renaming.
* `gvnMR`, `gvnMR_denote`: the pass from the identity renaming and the empty table; it
  denotes the same function as its input, for every predicate `pure`.
* `mrLen`, `gvnMRGo_mrLen_le`: the number of bindings, which the pass does not increase.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

open CatCrypt.Crypto.SecureCompilation.VIR

section Rename

variable {d : Dialect.{0, 0}} [TyDenote d.Ty]

/-- The returned variables `vs` renamed by `ρ`. -/
def renameVars {Γ Δ : Ctxt d} (ρ : Ctxt.Hom Γ Δ) :
    {ts : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) ts → HVector (fun ty => Ctxt.Var Δ ty) ts
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (ρ v) (renameVars ρ rest)

/-- The renamed returned variables read at `V` are the returned variables read at the
    valuation pulled back along `ρ`. -/
theorem lookupVars_renameVars {Γ Δ : Ctxt d} (ρ : Ctxt.Hom Γ Δ) (V : Ctxt.Valuation Δ) :
    ∀ {ts : List d.Ty} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts),
      MultiReturnCom.lookupVars (renameVars ρ vs) V = MultiReturnCom.lookupVars vs (V.comap ρ)
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      simp only [renameVars, MultiReturnCom.lookupVars, lookupVars_renameVars ρ V rest,
        Ctxt.Valuation.lookup_comap]

end Rename

section GvnMulti

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op]

/-- Global value numbering of a multi-return program under the renaming `ρ` and the node
    table `M`: a binding of an operation satisfying `pure` whose renamed key is recorded is
    dropped and its variable mapped to the recorded node; every other binding is renamed by
    `ρ`, kept and recorded; the returned variables are renamed by `ρ`. -/
def gvnMRGo (pure : d.Op → Bool) : {Γ Δ : Ctxt d} → {ts : List d.Ty} → Ctxt.Hom Γ Δ → Tbl d →
    MultiReturnCom d Γ ts → MultiReturnCom d Δ ts
  | _, _, _, ρ, _, .ret vs => .ret (renameVars ρ vs)
  | _, Δ, _, ρ, M, .var (t := s) e body =>
      match findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with
      | some w => gvnMRGo pure (consHom w ρ) M body
      | none =>
          .var (e.rename ρ)
            (gvnMRGo pure ρ.lift
              (insertT pure M (e.rename ρ).op (argLvls (e.rename ρ).args) Δ.length) body)

/-- **Denotation of the traversal.** Under a table sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem gvnMRGo_denote (pure : d.Op → Bool) : ∀ {Γ Δ : Ctxt d} {ts : List d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (M : Tbl d) (m : MultiReturnCom d Γ ts) (V : Ctxt.Valuation Δ),
    Sound V M → (gvnMRGo pure ρ M m).denote V = m.denote (V.comap ρ)
  | _, _, _, ρ, _, .ret vs, V, _ => lookupVars_renameVars ρ V vs
  | _, Δ, _, ρ, M, .var (t := s) e body, V, hM => by
      simp only [gvnMRGo]
      rcases hc : findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [MultiReturnCom.denote]
        rw [gvnMRGo_denote pure ρ.lift _ body _ (sound_insertT hM (e.rename ρ)),
          Expr.denote_rename ρ e V, Ctxt.Valuation.extend_comap_lift]
      · simp only [MultiReturnCom.denote]
        rw [gvnMRGo_denote pure (consHom w ρ) M body V hM, comap_consHom, findVar_expr hM hc,
          Expr.denote_rename ρ e V]

/-- **Global value numbering of a multi-return program**: the traversal from the identity
    renaming and the empty table. -/
def gvnMR (pure : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} (m : MultiReturnCom d Γ ts) :
    MultiReturnCom d Γ ts :=
  gvnMRGo pure (Ctxt.Hom.id Γ) ∅ m

/-- **Denotation of the pass.** `gvnMR pure m` denotes the same function as `m`. -/
theorem gvnMR_denote (pure : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty}
    (m : MultiReturnCom d Γ ts) (V : Ctxt.Valuation Γ) :
    (gvnMR pure m).denote V = m.denote V := by
  rw [gvnMR, gvnMRGo_denote pure _ _ m V (sound_empty V), Ctxt.Valuation.comap_id]

end GvnMulti

section Length

variable {d : Dialect.{0, 0}} [DecidableEq d.Ty] [DialectSignature d] [DecidableEq d.Op]

/-- The number of bindings of a multi-return program. -/
def mrLen : {Γ : Ctxt d} → {ts : List d.Ty} → MultiReturnCom d Γ ts → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => mrLen body + 1

/-- The traversal does not increase the number of bindings. -/
theorem gvnMRGo_mrLen_le [TyDenote d.Ty] [DialectDenote d] (pure : d.Op → Bool) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (M : Tbl d)
      (m : MultiReturnCom d Γ ts), mrLen (gvnMRGo pure ρ M m) ≤ mrLen m
  | _, _, _, ρ, _, .ret vs => by simp [gvnMRGo, mrLen]
  | _, Δ, _, ρ, M, .var (t := s) e body => by
      simp only [gvnMRGo]
      rcases findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [mrLen]
        exact Nat.succ_le_succ (gvnMRGo_mrLen_le pure ρ.lift _ body)
      · simp only [mrLen]
        exact Nat.le_succ_of_le (gvnMRGo_mrLen_le pure (consHom w ρ) M body)

end Length

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
