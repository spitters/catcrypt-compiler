/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontBody
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNFLoops
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable

/-!
# The source program of the front at the level of call trees

The source program `nfSrcProgC fs σ te` of the front is the translation `impToNF` of the body
`nfBody te`. At the tree table `evTable`, in which every call is an event, the call tree of the
extraction `te` and the call tree of the program are related by `RuttS` at the relations
`ImpRE`, `ImpRA` of the translation: the body stage (`NFCallTreeFrontBody.nfBody_relT`) composed
with the translation (`NFCallTreeImpToNF.impToNF_relT`) and the read-back of the result variable
of the output. A value leaf of the source that is not a control-flow value is the encoding of the
result of the program; the other source leaves failed.

Every tree table is a substitution of its trees for the events of `evTable`
(`nfTree_eq_substT`), so the relation at `evTable` passes to the tables of a module by
`NFCallTreeSubst.RuttS.substT`.

## Main results

* `substTable_evTable`, `nfTree_eq_substT`: the call tree at a table is the substitution of the
  table into the call tree at `evTable`.
* `srcProg_relT`: the call tree of the extraction and the call tree of the source program of the
  front, at `evTable`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontProg

open _root_.Hax (ImpExpr Value Env Outcome TExpr)
open _root_.Hax.EarlyReturnElim (RetRel)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig linkReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF (evTable ImpRE ImpRA LeafRel SrcFail
  preTreeAt treeAt_plug impToNF_relT)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst (substT)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable (substTable substT_nfTree)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_ret)
open Ctxt (Var Valuation)

/-! ## Every table is a substitution into `evTable` -/

/-- The substitution of `σ` into the table `evTable` is the table of the trees of `σ`. -/
theorem substTable_evTable (σ : ∀ e : linkSig.Event, CallTree linkSig (linkSig.Resp e)) :
    substTable σ evTable = fun g vals => σ ⟨g, vals⟩ := by
  funext g vals
  exact bind_ret _

/-- **The call tree at a table is the substitution of the table into the call tree at
    `evTable`.** -/
theorem nfTree_eq_substT (bt : TreeTable linkSig) (fuel : Nat) (e : ImpExpr) (env : Env) :
    nfTree bt fuel e env =
      substT (fun c : linkSig.Event => bt (LinkCall.name c) (LinkCall.args c))
        (nfTree evTable fuel e env) := by
  have h := substT_nfTree (fun c : linkSig.Event => bt (LinkCall.name c) (LinkCall.args c))
    evTable fuel e env
  rw [h]
  congr 1
  funext g vals
  exact (bind_ret _).symm

/-! ## The source program -/

/-- The leaf relation of a program of one result: a source value that is not a control-flow
    value is the encoding of the result. -/
def ProgOut (t : NfTy) (r : Outcome × Env) (o : Option (HVector NfTy.denote [t])) : Prop :=
  ∀ v, r.1 = .val v → v.isControlFlow = false → ∃ y, o = some (HVector.cons y .nil) ∧ v = enc t y

/-- **The extraction and the source program of the front at `evTable`.** Let `nfSrcProgC fs σ te`
    return `q`, the extraction have call-free arguments at the calls of its inlined closures
    (`spineArgsOk`), and the source handler `h₁` answer `repeat` as the table of `repeat` calls.
    From a source environment and a valuation of the entry related by `EntryVals`, at a target
    fuel at least the source fuel, the call tree of `te` at `evTable` and the call tree of the
    program are related by `RuttS` at `ImpRE`, `ImpRA` and `ProgOut`, the source leaves that are
    not values failed. -/
theorem srcProg_relT (fs : List CrateFn) (σ : AbiLayout) (te : TExpr)
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hq : nfSrcProgC fs σ te = some q)
    (hs : NFCallTreeInlineSpine.spineArgsOk te.erase = true)
    (h₁ : ∀ e : linkSig.Event, linkSig.Resp e)
    (hR : RepeatCalls fun f vals => h₁ ⟨f, vals⟩) (tE : TreeCallEnv leafSig nfDialect)
    (fuel tf : Nat) (hft : fuel ≤ tf) (env : Env)
    (V : Valuation (entryCtx (NFToRoute.abiEntry σ)))
    (hV : EntryVals env (NFToRoute.abiEntry σ) V) :
    RuttS h₁ ImpRE ImpRA (ProgOut q.1) (fun r => ¬ ∃ v, r.1 = .val v)
      (nfTree evTable fuel te.erase env) (treeAt linkReader tE tf q.2 V) := by
  unfold nfSrcProgC at hq
  split at hq
  · rename_i hok
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hq
    have hB := NFCallTreeFrontBody.nfBody_relT h₁ evTable fuel te hok hs env
    have hI := impToNF_relT _ h₁ hR tE (nfBody te) none _ ho fuel tf hft env V (entryEnv_rel hV)
    have hI' : RuttS h₁ ImpRE ImpRA (ProgOut o.t) SrcFail
        (denoteT evTable fuel (nfBody te) env) (treeAt linkReader tE tf o.prog V) := by
      rw [Out.prog, treeAt_plug, ← bind_ret (denoteT evTable fuel (nfBody te) env)]
      refine NFCallTreeImpToNF.ruttS_obindK hI (fun r W hr => .ret ?_) ?_
        (fun r hf _ => .fail hf)
      · obtain ⟨v, W', hv, hW, -, henc⟩ := hr
        cases hW
        intro v' hv' _
        rw [hv] at hv'
        cases hv'
        exact ⟨_, rfl, henc⟩
      · rintro r w ⟨v, W, -, hW, -⟩
        exact ⟨W, hW⟩
    refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans ?_ hB hI')
    · rintro r₀ o' ⟨r₁, h01, h12⟩ v hv hcf
      rcases h01 with h | ⟨w, -, h, -⟩
      · exact h12 v (h.trans hv) hcf
      · rw [hv] at h
        cases h
        simp at hcf
    · intro r₀ r₁ h01 hf ⟨v, hv⟩
      rcases h01 with h | ⟨w, -, -, h'⟩
      · exact hf v (h.trans hv)
      · exact hf w h'
  · cases hq

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontProg
