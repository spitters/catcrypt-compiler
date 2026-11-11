/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
public import CatCrypt.Crypto.SecureCompilation.VIR.NFAbortElim

/-!
# Elimination of aborting branches at the level of call trees

The chain `extChain` of the front starts with the elimination of aborting branches
`NFProg.abortElim NfOp.isAbort`, which replaces a branch without result whose first arm binds an
aborting operation first and whose second arm returns at once by its continuation. At the level
of call trees the tree of the branch is the tree of its continuation when the branch takes the
second arm, and the failed leaf `none` when it takes the first arm, at every reader that reads an
aborting operation as the leaf `none`. The tree of the eliminated program therefore refines the
tree of the program (`RefinesT`): equal events and answers, equal leaves, and the failed source
leaf `none`.

## Main results

* `refinesT_treeAt_iteElim`: the tree of a branch is refined by the tree of `iteElim` of it.
* `refinesT_treeAt_abortElim`: the stage lemma of the elimination at every reader that reads an
  aborting operation as the leaf `none`.
* `linkReader_isAbort`, `refinesT_treeAt_abortElim_link`: the reader `linkReader` of
  `nfDialect` reads an aborting operation as the leaf `none`, and the stage lemma at it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAbort

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig linkReader opTree)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

section Abort

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] (ab : d.Op → Bool)

/-- **The branch step of the elimination at the tree level.** At a reader that reads every
    operation `ab` marks as the leaf `none`, the tree of a branch is refined by the tree of
    `iteElim` of it: a replaced branch that takes its first arm fails at the aborting
    operation, and one that takes its second arm continues at the valuation of the branch. -/
theorem refinesT_treeAt_iteElim (h₁ : ∀ e : E.Event, E.Resp e) {ex : ExprReader E d}
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → ex e V = .ret none)
    (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d} {ts rs : List d.Ty}
    (c : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs) (k : NFProg d (rs ++ Γ) ts)
    (V : Valuation Γ) :
    RefinesT h₁ (treeAt ex tE fuel (NFProg.ifThenElse c thn els k) V)
      (treeAt ex tE fuel (NFProg.iteElim ab c thn els k) V) := by
  cases rs with
  | cons _ _ => exact RefinesT.refl _
  | nil =>
    rw [NFProg.iteElim]
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      show RefinesT h₁ (obind (if HasBoolBit.toBool (d := d) (c.lookup V) then
          treeAt ex tE fuel thn V else treeAt ex tE fuel els V)
        fun r => treeAt ex tE fuel k (hvAppend r V)) _
      split
      · cases thn with
        | var e k' =>
          simp only [treeAt, hab e V hc.1]
          exact .fail rfl
        | _ => simp [NFProg.abortsFirst] at hc
      · cases els with
        | ret vs =>
          cases vs
          exact RefinesT.refl _
        | _ => simp [NFProg.isRetNil] at hc
    · exact RefinesT.refl _

/-- **The stage lemma of the elimination of aborting branches at the tree level.** At a reader
    that reads every operation `ab` marks as the leaf `none`, the tree of `NFProg.abortElim ab p`
    refines the tree of `p`, at every source handler, tree call environment and fuel. -/
theorem refinesT_treeAt_abortElim (h₁ : ∀ e : E.Event, E.Resp e) {ex : ExprReader E d}
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → ex e V = .ret none)
    (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ V : Valuation Γ,
      RefinesT h₁ (treeAt ex tE fuel p V) (treeAt ex tE fuel (NFProg.abortElim ab p) V) := by
  induction p with
  | ret vs => intro V; exact RefinesT.refl _
  | var e k ih =>
    intro V
    exact RefinesT.obind (RefinesT.refl _) fun x => ih _
  | forLoop count inits body k ihb ihk =>
    intro V
    exact RefinesT.obind (RefinesT.ofoldl (fun _ _ => ihb _) _ _) fun _ => ihk _
  | ifThenElse cond thn els k iht ihe ihk =>
    intro V
    refine RefinesT.trans ?_ (refinesT_treeAt_iteElim ab h₁ hab tE fuel cond _ _ _ V)
    refine RefinesT.obind ?_ fun _ => ihk _
    split
    · exact iht V
    · exact ihe V
  | whileLoop inits body k ihb ihk =>
    intro V
    exact RefinesT.obind (RefinesT.owhileIter (fun _ => ihb _) _ _) fun _ => ihk _
  | call fn args k ih =>
    intro V
    exact RefinesT.obind (RefinesT.refl _) fun _ => ih _

end Abort

/-- **The reader of `nfDialect` reads an aborting operation as the leaf `none`.** -/
theorem linkReader_isAbort {Γ : Ctxt nfDialect} {t : NfTy} (e : Expr nfDialect Γ t)
    (V : Valuation Γ) (h : NfOp.isAbort e.op = true) : linkReader e V = .ret none := by
  obtain ⟨op, rfl, args⟩ := e
  change opTree op (Expr.lookupArgs args V) = .ret none
  cases op <;> first | rfl | simp [NfOp.isAbort] at h

/-- **The stage lemma of the elimination of aborting branches at `linkReader`.** -/
theorem refinesT_treeAt_abortElim_link (h₁ : ∀ e : leafSig.Event, leafSig.Resp e)
    (tE : TreeCallEnv leafSig nfDialect) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    RefinesT h₁ (treeAt linkReader tE fuel p V)
      (treeAt linkReader tE fuel (NFProg.abortElim NfOp.isAbort p) V) :=
  refinesT_treeAt_abortElim NfOp.isAbort h₁ (fun e V h => linkReader_isAbort e V h) tE fuel p V

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAbort
