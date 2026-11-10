/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgNarrowPrep

/-!
# The narrow-word stages at the level of call trees

The chain `extChainCore` ends, at the tree level, at the tree `mfTree` of its output, which
answers the field and reduce-multiply heads (`innerHead`) inside the tree. The narrow-word
stages `narrowPrep` (the widening `widenJ`, the mask elimination `maskElim`, the dead-binding
elimination `NFProg.dce` and the carry pairs `carryPair`) run on that output. This module
relates the tree `mfTree` of the input of `narrowPrep` to the tree `mfTree` of its output, and
composes the relation after `ruttS_extChainCore`.

The lowering `map?` relates trees at every pair of tree call environments whose trees of a call
and of its transport are related (`map?_ruttS_env`); at `mfEnv` on both sides this holds at
every call whose signature the widening fixes (`mfEnv_callsRelated_widen`), which is the case at
every call of a program that passes `regionExportableB`. The three later stages keep the tree
`treeAt pureReader` of a program of `jasminDialect` at every tree call environment: every
operation denotes a value, a removed mask is read through a relation of the values that the
analysis `okP` keeps exact at every call and every result, and an inserted carry pair binds a
value nothing reads.

## Main definitions

* `CallsRelated`: two tree call environments whose trees of a call admitted by a predicate and
  of its transport along a partial block lowering are related.

## Main results

* `treeAt_var_pure_env`, `ruttS_castRetHead_env`: a let-binding and a carried result type at
  every tree call environment.
* `map?_ruttS_env`: the stage lemma of `map?` at related tree call environments.
* `mfEnv_callsRelated_widen`, `ruttS_widenJ_mf`: the widening between trees `mfTree`.
* `treeAt_maskElimGo`, `treeAt_maskElim`: mask elimination keeps the tree.
* `treeAt_dce_jasmin`: dead-binding elimination keeps the tree of a program of
  `jasminDialect`.
* `treeAt_carryInsert`, `treeAt_carryPairGo`, `treeAt_carryPair`: the carry pairs keep the
  tree.
* `ruttS_narrowPrep_mf`: the stage lemma of `narrowPrep` between trees `mfTree`.
* `ruttS_extChainCore_narrowPrep`: the steps of `extChainCore` followed by `narrowPrep`, from the
  call tree of the source program to the tree `mfTree` of the narrowed program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeNarrow

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSel
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc (fieldEnv)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf)
open Ctxt (Var Valuation)

/-! ## The lowering `map?` at related tree call environments -/

section MapEnv

open FieldDialectBlockDescent
open BlockLoweringCPS (lookup_pullV)
open NFProg (map? spliceNF? castRetHead tyCast lookupArgs_mapArgs pullV_appHom pullV_liftTo
  pullV_bodyHom lookup_varTyCast)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- A let-binding of a dialect with a pure denotation has, at every tree call environment, the
    call tree of its continuation at the extended valuation. -/
theorem treeAt_var_pure_env {E : EventSig} (tE : TreeCallEnv E d) (fuel : Nat) {Γ : Ctxt d}
    {t : d.Ty} {ts : List d.Ty} (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts)
    (V : Valuation Γ) :
    treeAt pureReader tE fuel (.var e k) V =
      treeAt pureReader tE fuel k (V.extend (e.denote V)) := by
  simp only [treeAt, pureReader, Expr.denoteM_option_eq_some]
  rfl

/-- A program carried along an equality of its first result type keeps a relation of trees at
    every tree call environment, the first result read back along the equality. -/
theorem ruttS_castRetHead_env {E₁ E₂ : EventSig} {R₁ : Type}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    (tE : TreeCallEnv E₂ d) {Δ : Ctxt d} {a b : d.Ty} {ts : List d.Ty} (h : a = b)
    (p : NFProg d Δ (a :: ts)) (fuel : Nat) (W : Valuation Δ)
    {R : R₁ → Valuation (a :: ts) → Prop} {t : CallTree E₁ (Option R₁)}
    (hp : RuttS h₁ RE RA (OutRel R) (fun o => o = none) t (treeAt pureReader tE fuel p W)) :
    RuttS h₁ RE RA (OutRel fun x (y : Valuation (b :: ts)) =>
        R x (.cons (tyCast h.symm y.head) y.tail)) (fun o => o = none) t
      (treeAt pureReader tE fuel (castRetHead h p) W) := by
  subst h
  refine RuttS.mono (fun o o' ho x hx => ?_) hp
  obtain ⟨y, hy, hR⟩ := ho x hx
  refine ⟨y, hy, ?_⟩
  rcases y with _ | ⟨y, ys⟩
  exact hR

variable {d' : Dialect.{0, 0}} [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d'] [DialectDenote d']
variable (P : PartialBlockLowering d d') (transTy : P.TransTy) (mapVal : P.MapVal)

/-- **Related tree call environments along a lowering**: at every call that `C` admits, the
    tree of the source environment at the call and the tree of the target environment at the
    call with the mapped signature and the transported arguments are related, events by
    `MapRE`, answers by `MapRA`, a source result by its transport. -/
def CallsRelated (h₁ : ∀ e : (nfCallSig d).Event, (nfCallSig d).Resp e)
    (tE₁ : TreeCallEnv (nfCallSig d) d) (tE₂ : TreeCallEnv (nfCallSig d') d')
    (C : String → List d.Ty → List d.Ty → Prop) : Prop :=
  ∀ (f : String) (as rs : List d.Ty) (x : Valuation as), C f as rs →
    RuttS h₁ (MapRE P transTy) (MapRA P transTy)
      (OutRel fun y y' => y' = transArgs P.mapTy transTy y) (fun o => o = none)
      (tE₁.call f as rs x)
      (tE₂.call f (as.map P.mapTy) (rs.map P.mapTy) (transArgs P.mapTy transTy x))

/-- **The stage lemma of `map?` at related tree call environments.** Under the leaves of
    `map?_ruttS` and tree call environments related at every call of the program
    (`CallsRelated`), the tree of a `Good`-covered program at the source environment is related
    to the tree of the program `map?` returns at the target environment, at a renaming relating
    `W` to the transported `V`. -/
theorem map?_ruttS_env (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denote (mapVal V) = transTy (e.denote V))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (h₁ : ∀ e : (nfCallSig d).Event, (nfCallSig d).Resp e)
    (tE₁ : TreeCallEnv (nfCallSig d) d) (tE₂ : TreeCallEnv (nfCallSig d') d')
    {C : String → List d.Ty → List d.Ty → Prop} (hC : CallsRelated P transTy h₁ tE₁ tE₂ C)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good)
    (hcalls : ∀ f as rs, p.Calls f as rs → C f as rs) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      pullV ren W = mapVal V → ∀ q, map? P hT p ren = some q →
      RuttS h₁ (MapRE P transTy) (MapRA P transTy)
        (OutRel fun x y => y = transArgs P.mapTy transTy x) (fun o => o = none)
        (treeAt pureReader tE₁ fuel p V) (treeAt pureReader tE₂ fuel q W) := by
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
    rw [treeAt_var_pure_env]
    refine spliceNF?_elimQ (fun q W => RuttS h₁ (MapRE P transTy) (MapRA P transTy)
        (OutRel fun x y => y = transArgs P.mapTy transTy x) (fun o => o = none)
        (treeAt pureReader tE₁ fuel k (V.extend (e.denote V))) (treeAt pureReader tE₂ fuel q W))
      (fun e k W hk => by rwa [treeAt_var_pure_env]) _ _ W
      (fun ren' res W' h1 h2 q' hq' => ?_) q hq
    refine ih hk hcalls _ (V.extend (e.denote V)) W' ?_ q' hq'
    refine pullV_bodyHom P transTy mapVal hExt ren ren' res V _ W W' hren h1 ?_
    rw [h2, FieldDialectBlockDescent.Com.denote_rename, hren, hBlk e hg blk hblk V]
  | forLoop count inits body k ihb ihk =>
    intro Δ ren V W hren q hq
    obtain ⟨hb, hk⟩ := hp
    obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [treeAt]
    rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toNat_trans,
      lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
    refine ruttS_obind (R := fun acc acc' => acc' = transArgs P.mapTy transTy acc)
      (ruttS_ofoldl (fun acc acc' i hacc => ?_) _ _ _ rfl) fun acc acc' hacc => ?_
    · subst hacc
      rw [← hR.ofNat_trans i]
      exact ihb hb (fun f as rs h => hcalls f as rs (.inl h)) _ _ _
        (pullV_appHom P transTy mapVal hExt _ _ _
          (pullV_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ acc) b hbq
    · subst hacc
      exact ihk hk (fun f as rs h => hcalls f as rs (.inr h)) _ _ _
        (pullV_appHom P transTy mapVal hExt ren V W hren _ acc) k' hkq
  | ifThenElse cond thn els k iht ihe ihk =>
    intro Δ ren V W hren q hq
    obtain ⟨ht, he, hk⟩ := hp
    obtain ⟨a, haq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [treeAt]
    rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toBool_trans]
    refine ruttS_obind (R := fun r r' => r' = transArgs P.mapTy transTy r) ?_
      fun r r' hr => ?_
    · cases HasBoolBit.toBool (d := d) (cond.lookup V)
      · exact ihe he (fun f as rs h => hcalls f as rs (.inr (.inl h))) ren V W hren b hbq
      · exact iht ht (fun f as rs h => hcalls f as rs (.inl h)) ren V W hren a haq
    · subst hr
      exact ihk hk (fun f as rs h => hcalls f as rs (.inr (.inr h))) _ _ _
        (pullV_appHom P transTy mapVal hExt ren V W hren _ r) k' hkq
  | whileLoop inits body k ihb ihk =>
    intro Δ ren V W hren q hq
    obtain ⟨hb, hk⟩ := hp
    obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [treeAt]
    rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
    refine ruttS_obind (R := fun acc acc' => acc' = transArgs P.mapTy transTy acc)
      (ruttS_owhileIter (fun a a' ha => ?_) fuel fuel le_rfl _ _ rfl) fun acc acc' hacc => ?_
    · subst ha
      refine RuttS.mono (fun o o' ho x hx => ?_) (ruttS_castRetHead_env tE₂ hT.bit_eq b fuel _
        (ihb hb (fun f as rs h => hcalls f as rs (.inl h)) _ _ _
          (pullV_appHom P transTy mapVal hExt ren V W hren _ a) b hbq))
      obtain ⟨y, hy, hxy⟩ := ho x hx
      refine ⟨y, hy, ?_⟩
      rcases x with _ | ⟨x, xs⟩
      rcases y with _ | ⟨y, ys⟩
      obtain ⟨h1, h2⟩ := HVector.cons.inj hxy
      refine ⟨h2, ?_⟩
      rw [tyCast_eq_of_symm hT.bit_eq h1, hR.toBool_trans]
      rfl
    · subst hacc
      exact ihk hk (fun f as rs h => hcalls f as rs (.inr h)) _ _ _
        (pullV_appHom P transTy mapVal hExt ren V W hren _ acc) k' hkq
  | call f args k ih =>
    intro Δ ren V W hren q hq
    obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [treeAt]
    rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
    refine ruttS_obind (R := fun y y' => y' = transArgs P.mapTy transTy y)
      (hC f _ _ _ (hcalls f _ _ (.inl ⟨rfl, rfl, rfl⟩))) fun y y' hy => ?_
    subst hy
    exact ih hp (fun f as rs h => hcalls f as rs (.inr h)) _ _ _
      (pullV_appHom P transTy mapVal hExt ren V W hren _ y) k' hkq

end MapEnv

/-! ## The widening between trees `mfTree` -/

section Widen

open NarrowWords (widenJ widenP widenP_regionTypes widenP_varTransports widenP_mapValExtends
  widenP_regionTransports exprBlock?_denote wideTy transports_of_wide)

/-- **`mfEnv` is related to itself along the widening** at every call whose signature the
    widening fixes: an inner head answers by `montEnv (fieldEnv CallEnv.empty)` on both sides,
    which agree along the widening at such a call (`transports_of_wide`), and every other call
    is one event on both sides, the target event the widened source event. -/
theorem mfEnv_callsRelated_widen
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    {C : String → List JasminTy → List JasminTy → Prop}
    (hC : ∀ f as rs, C f as rs → as.map wideTy = as ∧ rs.map wideTy = rs) :
    CallsRelated widenP (fun x => NarrowWords.transTy x) h₁ mfEnv mfEnv C := by
  intro f as rs x hc
  by_cases hf : innerHead f = true
  · simp only [mfEnv, hf, ite_true]
    refine .ret fun y hy => ⟨_, ?_, rfl⟩
    have ht := transports_of_wide (montEnv (fieldEnv CallEnv.empty)) hC f as rs x hc
    change (montEnv (fieldEnv CallEnv.empty)).call f (as.map wideTy) (rs.map wideTy)
      (transArgs wideTy (fun x => NarrowWords.transTy x) x) = _
    rw [ht, hy]
    rfl
  · simp only [mfEnv, hf]
    refine .vis rfl fun a₁ a₂ ha => .ret fun y hy => ⟨_, ?_, rfl⟩
    cases hy
    exact eq_of_heq (ha y rfl)

/-- **The stage lemma of the widening between trees `mfTree`**: for a program whose calls are at
    signatures the widening fixes, at every source handler and fuel, the tree `mfTree` of `p` is
    related to the tree `mfTree` of the widened program at the widened valuation, each call the
    event with the widened signature and arguments, answered by the widening of the source
    answer, the leaves related by the widening, and the failed source leaf `none`. -/
theorem ruttS_widenJ_mf
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : widenJ p = some q)
    (hw : ∀ f as rs, p.Calls f as rs → as.map wideTy = as ∧ rs.map wideTy = rs)
    (V : Valuation Γ) :
    RuttS h₁ (MapRE widenP fun x => NarrowWords.transTy x)
      (MapRA widenP fun x => NarrowWords.transTy x)
      (OutRel fun x y => y = transArgs widenP.mapTy (fun x => NarrowWords.transTy x) x)
      (fun o => o = none) (mfTree fuel p V) (mfTree fuel q (NarrowWords.mapVal V)) :=
  map?_ruttS_env widenP (fun x => NarrowWords.transTy x) (fun V => NarrowWords.mapVal V)
    widenP_regionTypes (fun _ => True) widenP_varTransports
    (fun e _ blk hblk V => exprBlock?_denote e blk hblk V) widenP_mapValExtends
    widenP_regionTransports h₁ mfEnv mfEnv (mfEnv_callsRelated_widen h₁ hw) fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) (fun _ _ _ h => h) (fun v => v) V
    (NarrowWords.mapVal V) (FieldDialectBlockDescent.pullV_id _) q hq

end Widen

/-! ## Mask elimination, dead-binding elimination and the carry pairs -/

section Later

open NarrowWords (maskElimGo maskElim okP okE okE_sound maskOf?_rel MRel MRel.push MRel.bind
  MRel.appExact Facts rel_exact constOK_exact okP_of_noRelax carryInsert carryPairGo carryPair
  agrees_wk1)

variable {E : EventSig} (tE : TreeCallEnv E jasminDialect) (fuel : Nat)

/-- **Mask elimination keeps the tree along a renaming**: when the facts `A` relate `V` to `W`
    along `ren` and the source passes `okP`, the output of `maskElimGo` has at `W`, at every
    tree call environment and fuel, the tree of the source at `V`. -/
theorem treeAt_maskElimGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ)
      (W : Valuation Δ), MRel A ren V W → okP p A = true →
      treeAt pureReader tE fuel (maskElimGo p A ren) W = treeAt pureReader tE fuel p V := by
  induction p with
  | ret vs =>
      intro Δ A ren V W hR hok
      simp only [maskElimGo, treeAt, hR.lookupArgs_eq vs hok]
  | var e k ih =>
      intro Δ A ren V W hR hok
      simp only [okP] at hok
      split at hok
      · rename_i i hi
        have hkeep : treeAt pureReader tE fuel (NFProg.var (e.rename ren)
            (maskElimGo k (A.push ((okE A e).getD .exact)) (Ctxt.Hom.lift ren))) W =
            treeAt pureReader tE fuel (NFProg.var e k) V := by
          rw [treeAt_var_pure_env, treeAt_var_pure_env]
          simp only [hi, Option.getD_some]
          have hs := okE_sound hR e hi
          exact ih _ _ _ _ (MRel.push hR hs.1 hs.2) hok
        simp only [maskElimGo]
        split
        · rename_i x m h he
          split
          · rename_i hk
            subst h
            have hrel := maskOf?_rel hR e he hi
            rw [ih _ _ _ _ (MRel.bind hR (NFProg.varTyCast rfl (ren x)) hrel trivial) hk,
              treeAt_var_pure_env]
          · exact hkeep
        · exact hkeep
      · cases hok
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨⟨hc, hi⟩, hb⟩, hk⟩ := hok
      have hbd : ∀ acc i, treeAt pureReader tE fuel (maskElimGo body
            (Facts.appExact _ (A.push .exact)) (NFProg.appLift _ (Ctxt.Hom.lift ren)))
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) =
          treeAt pureReader tE fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i => ihb _ _ _ _
          (MRel.appExact (MRel.push hR (rel_exact _) (constOK_exact _)) _ acc) hb
      have hkd : ∀ acc, treeAt pureReader tE fuel
            (maskElimGo k (Facts.appExact _ A) (NFProg.appLift _ ren)) (hvAppend acc W) =
          treeAt pureReader tE fuel k (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (MRel.appExact hR _ acc) hk
      simp only [maskElimGo, treeAt, hR.lookupArgs_eq inits hi, hR.lookup_ren_eq count hc, hbd,
        hkd]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨⟨hc, htn⟩, hel⟩, hk⟩ := hok
      have hkd : ∀ r, treeAt pureReader tE fuel
            (maskElimGo k (Facts.appExact _ A) (NFProg.appLift _ ren)) (hvAppend r W) =
          treeAt pureReader tE fuel k (hvAppend r V) :=
        fun r => ihk _ _ _ _ (MRel.appExact hR _ r) hk
      simp only [maskElimGo, treeAt, hR.lookup_ren_eq cond hc, iht A ren V W hR htn,
        ihe A ren V W hR hel, hkd]
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨⟨hi, hb⟩, hk⟩ := hok
      have hbd : ∀ acc, treeAt pureReader tE fuel
            (maskElimGo body (Facts.appExact _ A) (NFProg.appLift _ ren)) (hvAppend acc W) =
          treeAt pureReader tE fuel body (hvAppend acc V) :=
        fun acc => ihb _ _ _ _ (MRel.appExact hR _ acc) hb
      have hkd : ∀ acc, treeAt pureReader tE fuel
            (maskElimGo k (Facts.appExact _ A) (NFProg.appLift _ ren)) (hvAppend acc W) =
          treeAt pureReader tE fuel k (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (MRel.appExact hR _ acc) hk
      simp only [maskElimGo, treeAt, hR.lookupArgs_eq inits hi, hbd, hkd]
  | call f args k ih =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨ha, hk⟩ := hok
      have hkd : ∀ r, treeAt pureReader tE fuel
            (maskElimGo k (Facts.appExact _ A) (NFProg.appLift _ ren)) (hvAppend r W) =
          treeAt pureReader tE fuel k (hvAppend r V) :=
        fun r => ih _ _ _ _ (MRel.appExact hR _ r) hk
      simp only [maskElimGo, treeAt, hR.lookupArgs_eq args ha, hkd]

/-- **Mask elimination keeps the tree** of a program of `jasminDialect`, at every tree call
    environment, fuel and valuation. -/
theorem treeAt_maskElim {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    treeAt pureReader tE fuel (maskElim p) V = treeAt pureReader tE fuel p V :=
  treeAt_maskElimGo tE fuel p _ _ V V (fun _ => ⟨rel_exact _, constOK_exact _⟩)
    (okP_of_noRelax p _ (fun _ => rfl))

/-- **Dead-binding elimination keeps the tree** of a program of `jasminDialect` at the pure
    reader: every operation denotes a value, so a removed binding has no event and cannot
    fail. -/
theorem treeAt_dce_jasmin {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ V : Valuation Γ,
      treeAt pureReader tE fuel (NFProg.dce p) V = treeAt pureReader tE fuel p V := by
  induction p with
  | ret vs => intro V; rfl
  | var e k ih =>
    intro V
    simp only [NFProg.dce]
    split
    · rename_i k' hr
      rw [treeAt_var_pure_env, treeAt_rename? pureReader_renameInv tE fuel (NFProg.dce k) hr
        (PRen.agrees_drop V _)]
      exact ih _
    · rw [treeAt_var_pure_env, treeAt_var_pure_env]
      exact ih _
  | forLoop count inits body k ihb ihk =>
    intro V
    simp only [NFProg.dce, treeAt, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
    intro V
    simp only [NFProg.dce, treeAt, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
    intro V
    simp only [NFProg.dce, treeAt, ihb, ihk]
  | call f args k ih =>
    intro V
    simp only [NFProg.dce, treeAt, ih]

/-- **An inserted carry pair keeps the tree**: the data binding denotes a value, which nothing
    reads. -/
theorem treeAt_carryInsert {Γ : Ctxt jasminDialect} {ts : List JasminTy} {t : JasminTy}
    (w : Nat) (h : DialectSignature.ret (d := jasminDialect) (.addCarryHi w) = t)
    (args : HVector (fun t => Var Γ t)
      (DialectSignature.sig (d := jasminDialect) (.addCarryHi w)))
    (k : NFProg jasminDialect (t :: Γ) ts) (V : Valuation Γ) :
    treeAt pureReader tE fuel (carryInsert w h args k) V =
      treeAt pureReader tE fuel (NFProg.var ⟨JasminOp.addCarryHi w, h, args⟩ k) V := by
  unfold carryInsert
  split
  · rename_i e' k' he hk
    rw [treeAt_var_pure_env, treeAt_var_pure_env, treeAt_var_pure_env]
    have hx : PRen.Agrees (NarrowWords.wk1 (s := .reg w)) V (V.extend
        (Expr.denote (⟨.addCarryLo w, rfl, args⟩ : Expr jasminDialect Γ (.reg w)) V)) :=
      agrees_wk1 V _
    have he' := Expr.denoteM_rename? (M := Option) hx _ he
    simp only [Expr.denoteM_option_eq_some, Option.some.injEq] at he'
    rw [he']
    exact treeAt_rename? pureReader_renameInv tE fuel k hk (PRen.agrees_lift hx _)
  · rfl

/-- **The carry pairs keep the tree** of a program of `jasminDialect`, at every key of the
    binding before it. -/
theorem treeAt_carryPairGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ (prev : Option (Nat × List Nat)) (V : Valuation Γ),
      treeAt pureReader tE fuel (carryPairGo prev p) V = treeAt pureReader tE fuel p V := by
  induction p with
  | ret vs => intro prev V; rfl
  | var e k ih =>
      intro prev V
      unfold carryPairGo
      split
      · split
        · rw [treeAt_var_pure_env, treeAt_var_pure_env, ih]
        · rw [treeAt_carryInsert, treeAt_var_pure_env, treeAt_var_pure_env, ih]
      · rw [treeAt_var_pure_env, treeAt_var_pure_env, ih]
  | forLoop count inits body k ihb ihk =>
      intro prev V
      simp only [carryPairGo, treeAt, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro prev V
      simp only [carryPairGo, treeAt, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
      intro prev V
      simp only [carryPairGo, treeAt, ihb, ihk]
  | call f args k ih =>
      intro prev V
      simp only [carryPairGo, treeAt, ih]

/-- **The carry pairs keep the tree**. -/
theorem treeAt_carryPair {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    treeAt pureReader tE fuel (carryPair p) V = treeAt pureReader tE fuel p V :=
  treeAt_carryPairGo tE fuel p none V

end Later

/-! ## The narrow-word stages -/

section Narrow

open NarrowWords (narrowPrep narrowPrep_eq_some wideTy wordSig_of_calls wordSig_wide)
open JasminLprogExport.ExportRegions (regionExportableB)

/-- **The stage lemma of `narrowPrep` between trees `mfTree`**: for a program whose calls are
    at signatures the widening fixes, the tree `mfTree` of `p` is related to the tree `mfTree`
    of the narrowed program at the widened valuation, at the relations of `ruttS_widenJ_mf`:
    mask elimination, dead-binding elimination and the carry pairs keep the tree. -/
theorem ruttS_narrowPrep_mf
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (hw : ∀ f as rs, p.Calls f as rs → as.map wideTy = as ∧ rs.map wideTy = rs)
    (V : Valuation Γ) :
    RuttS h₁ (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x)
      (MapRA NarrowWords.widenP fun x => NarrowWords.transTy x)
      (OutRel fun x y => y = transArgs NarrowWords.widenP.mapTy
        (fun x => NarrowWords.transTy x) x)
      (fun o => o = none) (mfTree fuel p V) (mfTree fuel q (NarrowWords.mapVal V)) := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  have he : mfTree fuel (NarrowWords.carryPair (NFProg.dce (NarrowWords.maskElim q₀)))
      (NarrowWords.mapVal V) = mfTree fuel q₀ (NarrowWords.mapVal V) := by
    rw [mfTree, mfTree, treeAt_carryPair, treeAt_dce_jasmin, treeAt_maskElim]
  exact he ▸ ruttS_widenJ_mf h₁ fuel h₀ hw V

/-- **The narrow-word stages on a program that passes `regionExportableB`**: its calls are at
    word signatures, which the widening fixes. -/
theorem ruttS_narrowPrep_mf_of_exportable
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hB : regionExportableB p = true)
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (V : Valuation Γ) :
    RuttS h₁ (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x)
      (MapRA NarrowWords.widenP fun x => NarrowWords.transTy x)
      (OutRel fun x y => y = transArgs NarrowWords.widenP.mapTy
        (fun x => NarrowWords.transTy x) x)
      (fun o => o = none) (mfTree fuel p V) (mfTree fuel q (NarrowWords.mapVal V)) :=
  ruttS_narrowPrep_mf h₁ fuel hq (fun f as rs hc => wordSig_wide (wordSig_of_calls hB f as rs hc))
    V

/-- **The steps of `extChainCore` followed by `narrowPrep` at the tree level.** Under the
    hypotheses of `ruttS_extChainCore`, for a program `p` that the chain `extChainCore D Γ t`
    turns into `q`, which passes `regionExportableB` and which `narrowPrep` turns into `q'`, and
    a valuation `V` in range: the tree of `p` at `linkReader`, the source fuel `tf` and the
    handler of the leaf table of `bi` is related to the tree `mfTree` of `q'` at the transported
    and widened valuation, at every fuel at least `tf`: events related by `ExtRE`, `MapRE` of
    `catToJasmin` and `MapRE` of the widening, answers by the corresponding answer relations,
    leaves by `VRelL`, the transport and the widening, and the failed source leaf `none`. -/
theorem ruttS_extChainCore_narrowPrep {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    (D : List ExtDecl) (tE : TreeCallEnv leafSig nfDialect)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂ (leafHandler (tableOf bi) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    {Γ : Ctxt nfDialect} {t : NfTy} {p : NFProg nfDialect Γ [t]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChainCore D Γ t).run p = some q) (hB : regionExportableB q = true)
    {q' : NFProg jasminDialect ((mapCtx (Γ.map catTy)).map wideTy)
      ([mapTy (catTy t)].map wideTy)} (hq' : narrowPrep q = some q')
    (V : Valuation Γ) (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    (tf fuel : Nat) (hle : tf ≤ fuel) :
    RuttS (leafHandler (tableOf bi))
      (CompRE (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
        (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x))
      (CompRA (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
        (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x)
        (CompRA ExtRE (MapRE catToJasmin fun x => ctTransTy x) ExtRA
          (MapRA catToJasmin fun x => ctTransTy x))
        (MapRA NarrowWords.widenP fun x => NarrowWords.transTy x))
      (Relation.Comp
        (Relation.Comp (OutRel (VRelL [t]))
          (OutRel fun x y => y = transArgs catToJasmin.mapTy (fun x => ctTransTy x) x))
        (OutRel fun x y => y = transArgs NarrowWords.widenP.mapTy
          (fun x => NarrowWords.transTy x) x))
      (fun o => o = none)
      (treeAt linkReader tE tf p V)
      (mfTree fuel q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) := by
  refine RuttS.trans (h₁ := h₃) ?_ ?_
    (ruttS_extChainCore hbi D tE h₂ h₃ hh₂ hh₃ hinner h V hin tf fuel hle)
    (ruttS_narrowPrep_mf_of_exportable h₃ fuel hB hq' _)
  · rintro e₀ e ⟨e₁, he₁, he₂⟩ e₁' he₁' he₂'
    exact ⟨h₂ e₁', hh₂ _ _ he₁', hh₃ _ _ he₂'⟩
  · rintro r₀ r₁ ⟨r, h₁, h₂⟩ rfl
    have : r = none := by
      cases r with
      | none => rfl
      | some a => obtain ⟨b, hb, -⟩ := h₂ a rfl; cases hb
    subst this
    cases r₀ with
    | none => rfl
    | some a => obtain ⟨b, hb, -⟩ := h₁ a rfl; cases hb

end Narrow

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeNarrow
