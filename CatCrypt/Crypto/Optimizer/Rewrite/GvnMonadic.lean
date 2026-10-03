/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.OpInfo

/-!
# Global value numbering under a monadic denotation

The value numbering `gvnGo` of `Optimizer/Rewrite/AegraphGeneric.lean` drops a binding
whose renamed key is recorded in the node table, and records only the operations its
predicate `pure` admits. Against the pure denotation `Com.denote` it is sound for every
predicate (`gvnGo_denote`). Against a monadic denotation `Com.denoteM` in a lawful
monad `M`, the effect of a dropped binding does not run in the output, so soundness needs the
purity law `PureLaw T M` of the operation traits `T` whose field `pure` is the
predicate: the monadic denotation of a pure operation is the return of its pure
denotation. The law is used at the two places where the pass reads the predicate: a
dropped binding runs no effect, and the value a recorded binding binds is its pure
denotation, which the node table stores.

## Main results

* `gvnGo_denoteM`: under a node table sound for `V`, the output of the traversal
  denotes in `M` the input at the valuation pulled back along the renaming.
* `gvnCom_denoteM`: `gvnCom T.pure c` denotes in `M` the same function as `c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

open CatCrypt.Crypto.SecureCompilation.VIR

section Expr

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] {M : Type → Type}

/-- A renamed expression denotes in `M`, at `V`, the source at the pulled-back
    valuation. -/
theorem Expr.denoteM_rename [DialectDenoteM d M] {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (e : Expr d Γ t) (V : Ctxt.Valuation Δ) :
    (e.rename ρ).denoteM (M := M) V = e.denoteM (V.comap ρ) := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenoteM.denoteM op (Expr.lookupArgs (HVector.renameVars ρ args) V) = _
  rw [Expr.lookupArgs_renameVars]
  rfl

/-- Under the purity law, an expression whose operation is pure denotes in `M` the
    return of its pure denotation. -/
theorem Expr.denoteM_of_pure [Monad M] [DialectDenote d] [DialectDenoteM d M]
    (T : OpTraits d) (hP : PureLaw T M) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (h : T.pure e.op = true) (V : Ctxt.Valuation Γ) :
    e.denoteM (M := M) V = pure (e.denote V) := by
  obtain ⟨op, rfl, args⟩ := e
  exact hP op h _

end Expr

section GvnMonadic

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op]

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
/-- A recorded node is found only for an operation the predicate admits. -/
theorem findVar_pure {pure : d.Op → Bool} {Δ : Ctxt d} {s : d.Ty} {Mt : Tbl d} {op : d.Op}
    {lv : List Nat} {w : Ctxt.Var Δ s} (h : findVar pure Δ s Mt op lv = some w) :
    pure op = true := by
  unfold findVar at h
  split at h
  · assumption
  · cases h

omit [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectDenote d]
  [DecidableEq d.Op] in
/-- A node whose operation the predicate rejects is not entered. -/
theorem insertT_of_pure_false {pure : d.Op → Bool} (Mt : Tbl d) {op : d.Op} (lv : List Nat)
    (n : Nat) (h : pure op = false) : insertT pure Mt op lv n = Mt := by
  simp [insertT, h]

variable {M : Type → Type} [Monad M] [LawfulMonad M] [DialectDenoteM d M]

/-- **Monadic denotation of the traversal.** For operation traits `T` satisfying the
    purity law in `M`, under a node table sound for `V`, the output of the value
    numbering at `T.pure` denotes in `M` the input at the valuation pulled back along
    `ρ`. -/
theorem gvnGo_denoteM (T : OpTraits d) (hP : PureLaw T M) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (Mt : Tbl d) (c : Com d Γ t) (V : Ctxt.Valuation Δ),
    Sound V Mt → (gvnGo T.pure ρ Mt c).denoteM (M := M) V = c.denoteM (V.comap ρ)
  | _, _, _, ρ, _, .ret v, V, _ => by
      simp only [gvnGo, Com.denoteM, Ctxt.Valuation.lookup_comap]
  | _, Δ, _, ρ, Mt, .var (t := s) e body, V, hM => by
      simp only [gvnGo]
      rcases hc : findVar T.pure Δ s Mt (e.rename ρ).op (argLvls (e.rename ρ).args) with
        _ | w
      · simp only [Com.denoteM, Expr.denoteM_rename ρ e V]
        cases hp : T.pure e.op
        · rw [insertT_of_pure_false (op := (e.rename ρ).op) Mt _ _ hp]
          congr 1
          funext x
          rw [gvnGo_denoteM T hP ρ.lift Mt body _ (sound_extend x hM),
            Ctxt.Valuation.extend_comap_lift]
        · rw [Expr.denoteM_of_pure T hP e hp, pure_bind, pure_bind, ← Expr.denote_rename,
            gvnGo_denoteM T hP ρ.lift _ body _ (sound_insertT hM (e.rename ρ)),
            Ctxt.Valuation.extend_comap_lift]
      · simp only [Com.denoteM]
        rw [gvnGo_denoteM T hP (consHom w ρ) Mt body V hM, comap_consHom, findVar_expr hM hc,
          Expr.denote_rename ρ e V, Expr.denoteM_of_pure T hP e (findVar_pure hc), pure_bind]

/-- **Monadic denotation of the pass.** For operation traits `T` satisfying the purity
    law in `M`, `gvnCom T.pure c` denotes in `M` the same function as `c`. -/
theorem gvnCom_denoteM (T : OpTraits d) (hP : PureLaw T M) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) : (gvnCom T.pure c).denoteM (M := M) = c.denoteM :=
  funext fun V => by
    rw [gvnCom, gvnGo_denoteM T hP _ _ c V (sound_empty V), Ctxt.Valuation.comap_id]

end GvnMonadic

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
