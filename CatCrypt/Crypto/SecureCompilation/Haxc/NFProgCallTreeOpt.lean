/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF

/-!
# Composition of tree relations and the e-graph pass at the tree level

The stage lemmas of the chain of `compileA` at the tree level relate the call tree of the input
of a stage to the call tree of its output. A stage that changes the dialect gives a relation
`RuttS` at relations of events and answers; a stage within a dialect gives the refinement
`RefinesT`. `RuttS.trans_refinesT` composes the two, under a target handler whose answers at
related events are related to the source handler's, which is the condition under which a
skipped event of the intermediate tree may be skipped in the source tree as well.

The e-graph pass `aegraphOptNF` keeps every node `call` with its symbol, in its position, on
the renamed arguments (`AegraphNF.nfGo`), and rewrites only let-bindings, which are no events
in a dialect with a pure denotation. Its output has the call tree of its input
(`treeAt_aegraphOptNF`), so the pass refines the tree (`refinesT_aegraphOptNF`).

## Main results

* `RuttS.trans_refinesT`: a relation `RuttS` followed by a refinement `RefinesT` is a relation
  `RuttS`.
* `treeAt_var_pure`: a let-binding of a dialect with a pure denotation has the tree of its
  continuation at the extended valuation.
* `treeAt_nfGo`: under a state sound for `V`, the traversal of the e-graph pass has the tree of
  its input at the valuation pulled back along the renaming.
* `treeAt_aegraphOptNF`, `refinesT_aegraphOptNF`: the stage lemma of `aegraphStep`.
* `spliceNF?_elimQ`, `ruttS_castRetHead`: a spliced block and a carried result type keep a
  property of the call tree.
* `map?_ruttS`: the stage lemma of the lowering `map?` along a partial block lowering (the step
  `mapStep catToJasmin`): each call is the event with the mapped signature and the
  transported arguments (`MapRE`), answered by the transported source answer (`MapRA`).

The lowering `map?` keeps every node `call` with its symbol and lowers each let-binding to a
block of let-bindings, so its stage lemma relates the trees event by event without skips.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
open Ctxt (Var Valuation)

/-! ## Composition -/

/-- **A relation followed by a refinement is a relation.** Let the target handler `h₂` answer
    related events with answers related to those of the source handler `h₁`, and let a leaf
    related to `none` be a failed source leaf. Then `RuttS h₁ RE RA RR Fail t₁ t₂` and
    `RefinesT h₂ t₂ t₃` give `RuttS h₁ RE RA RR Fail t₁ t₃`: an event of `t₂` that `t₃` skips is
    skipped in `t₁` at the answer of `h₁`. -/
theorem RuttS.trans_refinesT {E₁ E₂ : EventSig} {R₁ β : Type}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {h₂ : ∀ e : E₂.Event, E₂.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → Option β → Prop} {Fail : R₁ → Prop}
    (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    (hRR : ∀ r₁, RR r₁ none → Fail r₁)
    {t₁ : CallTree E₁ R₁} {t₂ t₃ : CallTree E₂ (Option β)}
    (h12 : RuttS h₁ RE RA RR Fail t₁ t₂) (h23 : RefinesT h₂ t₂ t₃) :
    RuttS h₁ RE RA RR Fail t₁ t₃ := by
  induction h12 generalizing t₃ with
  | ret h =>
    cases h23 with
    | ret h' => subst h'; exact .ret h
    | fail h' => subst h'; exact .fail (hRR _ h)
  | fail h => exact .fail h
  | vis he _ ih =>
    cases h23 with
    | vis he' hk' =>
      subst he'
      exact .vis he fun a₁ a₂ ha => ih a₁ a₂ ha (hk' a₂ a₂ HEq.rfl)
    | skip hk' => exact .skip (ih _ _ (hh _ _ he) hk')
  | skip _ ih => exact .skip (ih h23)

/-! ## The e-graph pass -/

section Aegraph

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

omit [DecidableEq d.Ty] [DecidableEq d.Op] in
/-- A let-binding of a dialect with a pure denotation has the call tree of its continuation at
    the extended valuation. -/
theorem treeAt_var_pure (fuel : Nat) {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts) (V : Valuation Γ) :
    treeAt (E := nfCallSig d) pureReader eventEnv fuel (.var e k) V =
      treeAt pureReader eventEnv fuel k (V.extend (e.denote V)) := by
  simp only [treeAt, pureReader, Expr.denoteM_option_eq_some]
  rfl

/-- **The call tree of the traversal of the e-graph pass**: under a state sound for `V`, the
    output of `nfGo R ρ S` has at `V` the call tree of its input at the valuation pulled back
    along `ρ`, at every fuel. -/
theorem treeAt_nfGo (R : RuleSet d) (fuel : Nat) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts) (V : Valuation Δ), StSound V S →
      treeAt (E := nfCallSig d) pureReader eventEnv fuel (nfGo R ρ S p) V =
        treeAt pureReader eventEnv fuel p (V.comap ρ)
  | _, _, _, ρ, _, .ret vs, V, _ => by
      simp only [nfGo, treeAt, Expr.lookupArgs_renameVars]
  | _, Δ, _, ρ, S, .var (t := s) e k, V, hS => by
      simp only [nfGo]
      split
      · rename_i w hc
        obtain ⟨hS', hw⟩ := stVar_sound R hS _ hc
        rw [treeAt_nfGo R fuel _ _ k V hS', comap_consHom, hw, Expr.denote_rename,
          treeAt_var_pure]
      · rename_i e2 hc
        obtain ⟨hS', hw⟩ := stOne_sound R hS _ hc
        rw [treeAt_var_pure, treeAt_nfGo R fuel _ _ k _ hS', Ctxt.Valuation.extend_comap_lift,
          hw, Expr.denote_rename, treeAt_var_pure]
      · rename_i s1 e1 e2 hc
        obtain ⟨hS', hw⟩ := stTwo_sound R hS _ hc
        rw [treeAt_var_pure, treeAt_var_pure, treeAt_nfGo R fuel _ _ k _ hS', comap_consHom,
          comap_wk2, treeAt_var_pure]
        rw [Expr.denote_rename] at hw
        rw [← hw]
        rfl
  | _, _, _, ρ, S, .forLoop (cs := cs) count inits body k, V, hS => by
      have hb : ∀ (acc : Valuation cs) (i : Nat),
          treeAt (E := nfCallSig d) pureReader eventEnv fuel
              (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) =
            treeAt pureReader eventEnv fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) (V.comap ρ))) := by
        intro acc i
        refine (treeAt_nfGo R fuel _ S body _
            (stSound_append acc (stSound_extend (HasWord64.ofNat (d := d) i) hS))).trans ?_
        rw [comap_homLiftApp]
        exact congrArg (fun W => treeAt pureReader eventEnv fuel body (hvAppend acc W))
          (Ctxt.Valuation.extend_comap_lift ρ V _)
      have hk : ∀ acc : Valuation cs,
          treeAt (E := nfCallSig d) pureReader eventEnv fuel (nfGo R (homLiftApp cs ρ) S k)
              (hvAppend acc V) =
            treeAt pureReader eventEnv fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [treeAt_nfGo R fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hb, hk, Ctxt.Valuation.lookup_comap,
        Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V, hS => by
      have hk : ∀ r : Valuation rs,
          treeAt (E := nfCallSig d) pureReader eventEnv fuel (nfGo R (homLiftApp rs ρ) S k)
              (hvAppend r V) =
            treeAt pureReader eventEnv fuel k (hvAppend r (V.comap ρ)) := by
        intro r
        rw [treeAt_nfGo R fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hk, Ctxt.Valuation.lookup_comap,
        treeAt_nfGo R fuel ρ S thn V hS, treeAt_nfGo R fuel ρ S els V hS]
  | _, _, _, ρ, S, .whileLoop (cs := cs) inits body k, V, hS => by
      have hb : ∀ acc : Valuation cs,
          treeAt (E := nfCallSig d) pureReader eventEnv fuel (nfGo R (homLiftApp cs ρ) S body)
              (hvAppend acc V) =
            treeAt pureReader eventEnv fuel body (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [treeAt_nfGo R fuel _ S body _ (stSound_append acc hS), comap_homLiftApp]
      have hk : ∀ acc : Valuation cs,
          treeAt (E := nfCallSig d) pureReader eventEnv fuel (nfGo R (homLiftApp cs ρ) S k)
              (hvAppend acc V) =
            treeAt pureReader eventEnv fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [treeAt_nfGo R fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hb, hk, Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .call (rs := rs) f args k, V, hS => by
      have hk : ∀ r : Valuation rs,
          treeAt (E := nfCallSig d) pureReader eventEnv fuel (nfGo R (homLiftApp rs ρ) S k)
              (hvAppend r V) =
            treeAt pureReader eventEnv fuel k (hvAppend r (V.comap ρ)) := by
        intro r
        rw [treeAt_nfGo R fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hk, Expr.lookupArgs_renameVars]

/-- **The e-graph pass keeps the call tree**: `aegraphOptNF R p` has the call tree of `p`, at
    every fuel and valuation, for every rule set. -/
theorem treeAt_aegraphOptNF (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (fuel : Nat) (V : Valuation Γ) :
    nfProgTree fuel (aegraphOptNF R p) V = nfProgTree fuel p V := by
  rw [nfProgTree, nfProgTree, aegraphOptNF, treeAt_nfGo R fuel _ _ p V (stSound_empty V),
    Ctxt.Valuation.comap_id]

/-- **The stage lemma of `aegraphStep` at the tree level**: the call tree of the output of the
    e-graph pass refines the call tree of its input, at every source handler. -/
theorem refinesT_aegraphOptNF (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (fuel : Nat) (V : Valuation Γ)
    (h₁ : ∀ e : (nfCallSig d).Event, (nfCallSig d).Resp e) :
    RefinesT h₁ (nfProgTree fuel p V) (nfProgTree fuel (aegraphOptNF R p) V) := by
  rw [treeAt_aegraphOptNF]
  exact RefinesT.refl _

end Aegraph

/-! ## The lowering along a partial block lowering -/

section MapStage

open FieldDialectBlockDescent
open BlockLoweringCPS (lookup_pullV)
open BlockLoweringExtend (transArgs)
open NFProg (map? spliceNF? castRetHead tyCast lookupArgs_mapArgs pullV_appHom pullV_liftTo
  pullV_bodyHom lookup_varTyCast)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- **The call tree of a spliced block**: a property closed under the let-bindings of a dialect
    with a pure denotation holds of every program `spliceNF? blk k` returns, when it holds of
    every program the continuation returns at a renaming that keeps the lookups and a result
    variable that holds the value of the block. -/
theorem spliceNF?_elimQ {ts : List d.Ty}
    (Q : ∀ {Δ : Ctxt d}, NFProg d Δ ts → Valuation Δ → Prop)
    (hQ : ∀ {Δ : Ctxt d} {c : d.Ty} (e : Expr d Δ c) (k : NFProg d (c :: Δ) ts)
      (W : Valuation Δ), Q k (W.extend (e.denote W)) → Q (.var e k) W) :
    ∀ {Δ : Ctxt d} {a : d.Ty} (blk : Com d Δ a)
      (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts))
      (W : Valuation Δ),
      (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (W' : Valuation Δ'),
        (∀ {s : d.Ty} (v : Var Δ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W → ∀ q, k ren res = some q → Q q W') →
      ∀ q, spliceNF? blk k = some q → Q q W
  | _, _, .ret v, k, W, hk => hk (fun x => x) v W (fun _ => rfl) rfl
  | _, _, .var e blk, k, W, hk => by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hQ e q' W (spliceNF?_elimQ Q hQ blk _ (W.extend (e.denote W))
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2) q' hq')

variable {d' : Dialect.{0, 0}} [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d'] [DialectDenote d']
variable (P : PartialBlockLowering d d') (transTy : P.TransTy) (mapVal : P.MapVal)

/-- **The event relation of a lowering**: the target call is the source call with its
    signature mapped by `P.mapTy` and its arguments transported. -/
def MapRE (e₁ : (nfCallSig d).Event) (e₂ : (nfCallSig d').Event) : Prop :=
  e₂ = ⟨e₁.name, e₁.argTys.map P.mapTy, e₁.resTys.map P.mapTy,
    transArgs P.mapTy transTy e₁.args⟩

/-- **The answer relation of a lowering**: a source result is answered by its transport. -/
def MapRA (e₁ : (nfCallSig d).Event) (e₂ : (nfCallSig d').Event)
    (a₁ : (nfCallSig d).Resp e₁) (a₂ : (nfCallSig d').Resp e₂) : Prop :=
  ∀ y : Valuation e₁.resTys, a₁ = some y →
    a₂ ≍ (some (transArgs P.mapTy transTy y) : Option (Valuation (e₁.resTys.map P.mapTy)))

/-- A program carried along an equality of its first result type keeps a relation of trees,
    the first result read back along the equality. -/
theorem ruttS_castRetHead {E₁ : EventSig} {R₁ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → (nfCallSig d').Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : (nfCallSig d').Event) → E₁.Resp e₁ →
      (nfCallSig d').Resp e₂ → Prop}
    {Δ : Ctxt d'} {a b : d'.Ty} {ts : List d'.Ty} (h : a = b) (p : NFProg d' Δ (a :: ts))
    (fuel : Nat) (W : Valuation Δ) {R : R₁ → Valuation (a :: ts) → Prop}
    {t : CallTree E₁ (Option R₁)}
    (hp : RuttS h₁ RE RA (OutRel R) (fun o => o = none) t (nfProgTree fuel p W)) :
    RuttS h₁ RE RA (OutRel fun x (y : Valuation (b :: ts)) =>
        R x (.cons (tyCast h.symm y.head) y.tail)) (fun o => o = none) t
      (nfProgTree fuel (castRetHead h p) W) := by
  subst h
  refine RuttS.mono (fun o o' ho x hx => ?_) hp
  obtain ⟨y, hy, hR⟩ := ho x hx
  refine ⟨y, hy, ?_⟩
  rcases y with _ | ⟨y, ys⟩
  exact hR

omit [DialectSignature d'] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d'] in
/-- A value carried back along an equality of types is the carried value. -/
theorem tyCast_eq_of_symm {a b : d'.Ty} (h : a = b) {y : ⟦b⟧} {z : ⟦a⟧}
    (hz : tyCast h.symm y = z) : y = tyCast h z := by
  subst h
  exact hz

/-- **The stage lemma of a lowering along a partial block lowering at the tree level.**
    Under the leaves of `map?_denoteAt`, the call tree of a `Good`-covered program is related
    to the call tree of the program `map?` returns at a renaming relating `W` to the transported
    `V`: each call is the event with the mapped signature and the transported arguments
    (`MapRE`), answered by the transport of the source answer (`MapRA`), and a result of the
    source is matched by its transport. -/
theorem map?_ruttS (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denote (mapVal V) = transTy (e.denote V))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (h₁ : ∀ e : (nfCallSig d).Event, (nfCallSig d).Resp e) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      pullV ren W = mapVal V → ∀ q, map? P hT p ren = some q →
      RuttS h₁ (MapRE P transTy) (MapRA P transTy)
        (OutRel fun x y => y = transArgs P.mapTy transTy x) (fun o => o = none)
        (nfProgTree fuel p V) (nfProgTree fuel q W) := by
  induction p with
  | ret vs =>
    intro Δ ren V W hren q hq
    cases hq
    refine .ret fun x hx => ⟨_, rfl, ?_⟩
    cases hx
    exact lookupArgs_mapArgs P transTy mapVal hVar ren V W hren vs
  | var e k ih =>
    intro Δ ren V W hren q hq
    obtain ⟨hg, hk⟩ := hp
    obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
    rw [nfProgTree, treeAt_var_pure]
    refine spliceNF?_elimQ (fun q W => RuttS h₁ (MapRE P transTy) (MapRA P transTy)
        (OutRel fun x y => y = transArgs P.mapTy transTy x) (fun o => o = none)
        (treeAt pureReader eventEnv fuel k (V.extend (e.denote V))) (nfProgTree fuel q W))
      (fun e k W hk => by rwa [nfProgTree, treeAt_var_pure]) _ _ W
      (fun ren' res W' h1 h2 q' hq' => ?_) q hq
    refine ih hk _ (V.extend (e.denote V)) W' ?_ q' hq'
    refine pullV_bodyHom P transTy mapVal hExt ren ren' res V _ W W' hren h1 ?_
    rw [h2, FieldDialectBlockDescent.Com.denote_rename, hren, hBlk e hg blk hblk V]
  | forLoop count inits body k ihb ihk =>
    intro Δ ren V W hren q hq
    obtain ⟨hb, hk⟩ := hp
    obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [nfProgTree, treeAt]
    rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toNat_trans,
      lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
    refine ruttS_obind (R := fun acc acc' => acc' = transArgs P.mapTy transTy acc)
      (ruttS_ofoldl (fun acc acc' i hacc => ?_) _ _ _ rfl) fun acc acc' hacc => ?_
    · subst hacc
      rw [← hR.ofNat_trans i]
      exact ihb hb _ _ _ (pullV_appHom P transTy mapVal hExt _ _ _
        (pullV_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ acc) b hbq
    · subst hacc
      exact ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ acc) k' hkq
  | ifThenElse cond thn els k iht ihe ihk =>
    intro Δ ren V W hren q hq
    obtain ⟨ht, he, hk⟩ := hp
    obtain ⟨a, haq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [nfProgTree, treeAt]
    rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toBool_trans]
    refine ruttS_obind (R := fun r r' => r' = transArgs P.mapTy transTy r) ?_
      fun r r' hr => ?_
    · cases HasBoolBit.toBool (d := d) (cond.lookup V)
      · exact ihe he ren V W hren b hbq
      · exact iht ht ren V W hren a haq
    · subst hr
      exact ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ r) k' hkq
  | whileLoop inits body k ihb ihk =>
    intro Δ ren V W hren q hq
    obtain ⟨hb, hk⟩ := hp
    obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [nfProgTree, treeAt]
    rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
    refine ruttS_obind (R := fun acc acc' => acc' = transArgs P.mapTy transTy acc)
      (ruttS_owhileIter (fun a a' ha => ?_) fuel fuel le_rfl _ _ rfl) fun acc acc' hacc => ?_
    · subst ha
      refine RuttS.mono (fun o o' ho x hx => ?_) (ruttS_castRetHead hT.bit_eq b fuel _
        (ihb hb _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ a) b hbq))
      obtain ⟨y, hy, hxy⟩ := ho x hx
      refine ⟨y, hy, ?_⟩
      rcases x with _ | ⟨x, xs⟩
      rcases y with _ | ⟨y, ys⟩
      obtain ⟨h1, h2⟩ := HVector.cons.inj hxy
      refine ⟨h2, ?_⟩
      rw [tyCast_eq_of_symm hT.bit_eq h1, hR.toBool_trans]
      rfl
    · subst hacc
      exact ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ acc) k' hkq
  | call f args k ih =>
    intro Δ ren V W hren q hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [nfProgTree, treeAt]
    refine .vis ?_ fun a₁ a₂ ha => ?_
    · simp only [MapRE]
      rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
    · cases a₁ with
      | none => exact .fail rfl
      | some y =>
        cases eq_of_heq (ha y rfl)
        exact ih hp _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ y) k' hkq

end MapStage

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt
