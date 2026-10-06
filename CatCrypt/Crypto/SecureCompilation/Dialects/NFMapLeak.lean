/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect

/-!
# The leakage of the lifting of a partial block lowering to `NFProg`

`NFProg.map? P hT p ren` lowers each let-binding of `p` to the block `P` gives it and keeps
the region constructors. When each block emits, on the transported valuation, the events of
the expression it lowers, the lowered program runs at a valuation related to the transported
source valuation to the transported results and to the events of the source run
(`NFProg.map?_leakRun`): the leakage transformer is the identity. The trip count, the trip
index and the branch decisions are transported by `RegionTransports`.

At the lowering `catToJasmin` of `catCryptDialect` to `jasminDialect`, the block leaf is
`toJBlockD_ctLeak`, under `LeakCompat P Pj` (`catToJasmin_map?_leakRun`).

`map?` creates no branch, so it maps a branch-free program to a branch-free program
(`NFProg.ifFree_map?`).

## Main results

* `NFProg.Com.ctLeak_rename_pullV` — a renamed block emits the events of the block at the
  pulled-back valuation.
* `NFProg.spliceNF?_leakRun` — the leakage run of a splice.
* `NFProg.forIterLeak_transport`, `NFProg.whileIterLeak_transport` — the iterations of loops
  whose steps commute with a transport.
* `NFProg.map?_leakRun` — the leakage transformer of `map?` is the identity.
* `NFProg.ifFree_map?` — `map?` keeps a program branch-free.
* `NFProgCatToJasmin.catToJasmin_map?_leakRun`, `NFProgCatToJasmin.catToJasmin_map?_ctLeak`
  — the instance at `catToJasmin`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open FieldDialectBlockDescent
  (BlockLoweringData TransTy MapVal VarTransports MapValExtends pullV)
open BlockLoweringCPS (consHom castHom valuation_ext lookup_pullV)
open BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Expr.ctLeak Com.ctLeak)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

namespace NFProg

/-! ## 1. Renaming and splicing -/

section Splice

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

omit [HasWord64 d] [HasBoolBit d] in
/-- A renamed expression emits the events of the expression at the pulled-back
    valuation. -/
theorem Expr.ctLeak_rename_pullV (M : LeakModel d) {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ')
    {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ') :
    Expr.ctLeak M (e.rename h) V = Expr.ctLeak M e (pullV h V) := by
  obtain ⟨op, rfl, args⟩ := e
  show ComLevelCheck.opLeak M op (Expr.lookupArgs (HVector.renameVars h args) V) = _
  rw [FieldDialectBlockDescent.lookupArgs_renameVars h args V]
  rfl

omit [HasWord64 d] [HasBoolBit d] in
/-- A renamed block emits the events of the block at the pulled-back valuation. -/
theorem Com.ctLeak_rename_pullV (M : LeakModel d) {Γ Γ' : Ctxt d} {t : d.Ty}
    (h : Ctxt.Hom Γ Γ') (c : Com d Γ t) (V : Valuation Γ') :
    Com.ctLeak M (Com.rename h c) V = Com.ctLeak M c (pullV h V) := by
  induction c generalizing Γ' with
  | ret v => rfl
  | var e body ih =>
      show Expr.ctLeak M (e.rename h) V ++
          Com.ctLeak M (Com.rename h.lift body) (V.extend ((e.rename h).denote V)) =
        Expr.ctLeak M e (pullV h V) ++
          Com.ctLeak M body ((pullV h V).extend (e.denote (pullV h V)))
      rw [Expr.ctLeak_rename_pullV, ih, FieldDialectBlockDescent.Expr.denote_rename h e V]
      congr 2
      show HVector.cons (e.denote (pullV h V))
          (pullV (fun v => (h v).there) (HVector.cons (e.denote (pullV h V)) V))
        = HVector.cons (e.denote (pullV h V)) (pullV h V)
      rw [FieldDialectBlockDescent.pullV_there h (e.denote (pullV h V)) V]

/-- **The leakage run of a splice.** If every program `k ren res` returns runs to `G`
    whenever `ren` preserves lookups back to `W` and `res` holds the value of the block,
    every program the splice returns runs to `G` with the events of the block in front. -/
theorem spliceNF?_leakRun (M : LeakModel d) (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {a : d.Ty} → (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts)) →
    (W : Valuation Δ) → (G : Option (Valuation ts × List CTLeak)) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (W' : Valuation Δ'),
        (∀ {s : d.Ty} (v : Var Δ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W →
        ∀ q, k ren res = some q → NFProg.leakRun M fuel q W' = G) →
    ∀ q, spliceNF? blk k = some q →
      NFProg.leakRun M fuel q W = G.map fun r => (r.1, Com.ctLeak M blk W ++ r.2)
  | _, _, .ret v, k, W, G, hk => by
      intro q hq
      rw [hk (fun x => x) v W (fun _ => rfl) rfl q hq]
      cases G <;> rfl
  | _, _, .var e blk, k, W, G, hk => by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.leakRun]
      rw [spliceNF?_leakRun M fuel blk _ (W.extend (e.denote W)) G
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2) q' hq', Option.map_map]
      cases G with
      | none => rfl
      | some r =>
          show some _ = some _
          simp only [Function.comp, Com.ctLeak, List.append_assoc]

/-- A program with its first result type carried runs to its results with the first one
    carried, and to the same events. -/
theorem leakRun_castRetHead (M : LeakModel d) (fuel : Nat) {Δ : Ctxt d} {a b : d.Ty}
    {ts : List d.Ty} (h : a = b) (p : NFProg d Δ (a :: ts)) (W : Valuation Δ) :
    NFProg.leakRun M fuel (castRetHead h p) W =
      (NFProg.leakRun M fuel p W).map
        (fun r => (.cons (tyCast h r.1.head) r.1.tail, r.2)) := by
  subst h
  show NFProg.leakRun M fuel p W = _
  cases NFProg.leakRun M fuel p W with
  | none => rfl
  | some r =>
      obtain ⟨r1, ev⟩ := r
      cases r1
      rfl

end Splice

/-! ## 2. Loops under a transport -/

section Loops

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectSignature d'] [HasWord64 d']
  [HasBoolBit d'] in
/-- The iterations of a counted loop whose step commutes with the transport `T` of
    carried tuples, keeping the events, commute with `T` and keep the events. -/
theorem forIterLeak_transport {cs : List d.Ty} {cs' : List d'.Ty}
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (step' : Nat → Valuation cs' → Option (Valuation cs' × List CTLeak))
    (T : Valuation cs → Valuation cs')
    (hs : ∀ i a, step' i (T a) = (step i a).map fun r => (T r.1, r.2)) :
    ∀ (l : List Nat) (a : Valuation cs),
      forIterLeak step' l (T a) = (forIterLeak step l a).map fun r => (T r.1, r.2) :=
  fun l a => (rel_graph_prod_iff.1 (forIterLeak_rel_bisim (R := fun a a' => T a = a') l
    (fun i _ a _ e => by
      subst e; rw [hs]; exact rel_map_of (fun _ => ⟨rfl, rfl⟩) _) a _ rfl)).symm

omit [DialectSignature d] [HasWord64 d] [DialectSignature d'] [HasWord64 d'] in
/-- The iterations of an exit-flag loop whose body commutes with the transport `T` of
    carried tuples and `Tb` of flags, keeping the events, and whose transported flags read
    as the source flags, commute with `T` and keep the events. -/
theorem whileIterLeak_transport {cs : List d.Ty} {cs' : List d'.Ty}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (step' : Valuation cs' →
      Option (Valuation (HasBitType.bit (d := d') :: cs') × List CTLeak))
    (T : Valuation cs → Valuation cs')
    (Tb : ⟦HasBitType.bit (d := d)⟧ → ⟦HasBitType.bit (d := d')⟧)
    (hb : ∀ b, HasBoolBit.toBool (d := d') (Tb b) = HasBoolBit.toBool (d := d) b)
    (hs : ∀ a, step' (T a) =
      (step a).map fun r => (.cons (Tb r.1.head) (T r.1.tail), r.2)) :
    ∀ (n : Nat) (a : Valuation cs),
      whileIterLeak step' n (T a) = (whileIterLeak step n a).map fun r => (T r.1, r.2) :=
  fun n a => (rel_graph_prod_iff.1 (whileIterLeak_rel_bisim (R := fun a a' => T a = a')
    (fun a _ e => by
      subst e; rw [hs]; exact rel_map_of (fun _ => ⟨rfl, (hb _).symm, rfl⟩) _) n a _ rfl)).symm

end Loops

/-! ## 3. The leakage transformer of `map?` -/

section Map

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  [DialectDenote d] [DialectDenote d']

variable (P : PartialBlockLowering d d') (transTy : P.TransTy) (mapVal : P.MapVal)

/-- **The leakage transformer of `map?` is the identity.** Under the leaves of
    `map?_denote` and the block leak leaf (each block `P` gives a `Good` expression emits,
    on the transported valuation, the events of the expression), a program that `map?`
    returns for a `Good`-covered program at a renaming relating `W` to the transported `V`
    runs at `W`, at every fuel, to the transported results and to the events of the
    source run at `V`. -/
theorem map?_leakRun (M : LeakModel d) (M' : LeakModel d') (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denote (mapVal V) = transTy (e.denote V))
    (hBlkLeak : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, Com.ctLeak M' blk (mapVal V) = Expr.ctLeak M e V)
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      pullV ren W = mapVal V → ∀ q, map? P hT p ren = some q →
      NFProg.leakRun M' fuel q W =
        (NFProg.leakRun M fuel p V).map fun r => (transArgs P.mapTy transTy r.1, r.2) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren q hq
      cases hq
      show some _ = some _
      rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren q hq
      obtain ⟨hg, hk⟩ := hp
      obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
      rw [spliceNF?_leakRun M' fuel _ _ W
        ((NFProg.leakRun M fuel k (V.extend (e.denote V))).map
          fun r => (transArgs P.mapTy transTy r.1, r.2))
        (fun ren' res W' h1 h2 q' hq' => ih hk _ (V.extend (e.denote V)) W'
          (pullV_bodyHom P transTy mapVal hExt ren ren' res V _ W W' hren h1 (by
            rw [h2, FieldDialectBlockDescent.Com.denote_rename, hren, hBlk e hg blk hblk V]))
          q' hq') q hq,
        Com.ctLeak_rename_pullV, hren, hBlkLeak e hg blk hblk V]
      simp only [NFProg.leakRun, Option.map_map]
      rfl
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨hb, hk⟩ := hp
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.leakRun]
      rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toNat_trans,
        lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
      rw [forIterLeak_transport _ _ (transArgs P.mapTy transTy) (fun i acc => by
        rw [← hR.ofNat_trans i]
        exact ihb hb _ _ _ (pullV_appHom P transTy mapVal hExt _ _ _
          (pullV_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ acc) b hbq)]
      refine bind_map_comm _ _ _ _ _ (fun r => ?_)
      dsimp only
      rw [ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ r.1) k' hkq,
        Option.map_map, Option.map_map]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨ht, he, hk⟩ := hp
      obtain ⟨a, haq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.leakRun]
      rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toBool_trans]
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then NFProg.leakRun M' fuel a W else NFProg.leakRun M' fuel b W) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRun M fuel thn V
            else NFProg.leakRun M fuel els V).map
              fun r => (transArgs P.mapTy transTy r.1, r.2) := by
        split
        · exact iht ht ren V W hren a haq
        · exact ihe he ren V W hren b hbq
      rw [harm]
      refine bind_map_comm _ _ _ _ _ (fun r => ?_)
      dsimp only
      rw [ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ r.1) k' hkq,
        Option.map_map, Option.map_map]
      rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨hb, hk⟩ := hp
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.leakRun]
      rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren,
        whileIterLeak_transport (fun acc => NFProg.leakRun M fuel body (hvAppend acc V))
          (fun acc => NFProg.leakRun M' fuel (castRetHead hT.bit_eq b) (hvAppend acc W))
          (transArgs P.mapTy transTy) (fun x => tyCast hT.bit_eq (transTy x))
          hR.toBool_trans (fun a => by
            rw [leakRun_castRetHead,
              ihb hb _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ a) b hbq,
              Option.map_map]
            congr 1
            funext r
            obtain ⟨r1, ev⟩ := r
            cases r1
            rfl)]
      refine bind_map_comm _ _ _ _ _ (fun r => ?_)
      dsimp only
      rw [ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ r.1) k' hkq,
        Option.map_map, Option.map_map]
      rfl
  | call =>
      intro Δ ren V W hren q hq
      obtain ⟨k', _, rfl⟩ := Option.map_eq_some_iff.mp hq
      rfl

end Map

/-! ## 4. `map?` keeps a program branch-free -/

section IfFree

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- A splice of a block and a continuation all of whose programs are branch-free is
    branch-free. -/
theorem ifFree_spliceNF? {ts : List d'.Ty} : {Δ : Ctxt d'} → {a : d'.Ty} →
    (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) q, k ren res = some q →
      ifFree q = true) →
    ∀ q, spliceNF? blk k = some q → ifFree q = true
  | _, _, .ret v, _, hk, q, hq => hk _ v q hq
  | _, _, .var _ blk, _, hk, q, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simpa only [ifFree, ctSafeNF, nodesOk, Bool.true_and] using
        ifFree_spliceNF? blk _ (fun ren res => hk _ res) q' hq'

omit [HasWord64 d] [HasBoolBit d] [DialectSignature d] [TyDenote d.Ty] in
/-- Carrying the first result type keeps a program branch-free. -/
theorem ifFree_castRetHead {Δ : Ctxt d'} {a b : d'.Ty} {ts : List d'.Ty} (h : a = b)
    (p : NFProg d' Δ (a :: ts)) : ifFree (castRetHead h p) = ifFree p := by
  subst h
  rfl

/-- **`map?` keeps a program branch-free.** A program that `map?` returns for a
    branch-free program has no `ifThenElse`. -/
theorem ifFree_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : ifFree p = true) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) q, map? P hT p ren = some q →
      ifFree q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q hq
      cases hq
      rfl
  | var e k ih =>
      have hk : ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk, Bool.true_and] using hp
      intro Δ ren q hq
      obtain ⟨blk, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      exact ifFree_spliceNF? _ _ (fun ren' res q' hq' => ih hk _ q' hq') q hq
  | forLoop count inits body k ihb ihk =>
      have hbk : ifFree body = true ∧ ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk, Bool.and_eq_true] using hp
      intro Δ ren q hq
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [ifFree, ctSafeNF, nodesOk, Bool.and_eq_true]
      exact ⟨ihb hbk.1 _ b hbq, ihk hbk.2 _ k' hkq⟩
  | ifThenElse =>
      simp [ifFree, ctSafeNF, nodesOk] at hp
  | whileLoop inits body k ihb ihk =>
      have hbk : ifFree body = true ∧ ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk, Bool.and_eq_true] using hp
      intro Δ ren q hq
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      have hb' : ifFree (castRetHead hT.bit_eq b) = true := by
        rw [ifFree_castRetHead]
        exact ihb hbk.1 _ b hbq
      simp only [ifFree, ctSafeNF, nodesOk, Bool.and_eq_true]
      exact ⟨hb', ihk hbk.2 _ k' hkq⟩
  | call f args k ih =>
      have hk : ifFree k = true := by
        simpa only [ifFree, ctSafeNF, nodesOk] using hp
      intro Δ ren q hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simpa only [ifFree, ctSafeNF, nodesOk] using ih hk _ k' hkq

end IfFree

end NFProg

/-! ## 5. The instance at `catToJasmin` -/

namespace NFProgCatToJasmin

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak

/-- The block leak leaf of `catToJasmin` is `toJBlockD_ctLeak`: the block the lowering gives
    an expression emits, on the transported valuation, the events of the expression. -/
theorem catToJasmin_blockLeak {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (blk : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hblk : catToJasmin.lowerExprBlock? e = some blk)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    Com.ctLeak (jLeakModel Pj) blk (ctMapValD V) = Expr.ctLeak (catLeakModel P) e V :=
  toJBlockD_ctLeak hc e blk hblk V

/-- **The leakage transformer of `map?` along `catToJasmin`.** Under `LeakCompat P Pj`, a
    program that `map?` returns for an `NFProg catCryptDialect` program, at a renaming
    relating `W` to `ctMapValD V`, runs at `W`, at every fuel, to the `ctTransTy` transport
    of the results and to the events of the source run at `V`. -/
theorem catToJasmin_map?_leakRun {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) (fuel : Nat) {Γ : Ctx} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom (mapCtx Γ) Δ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (W : Ctxt.Valuation Δ) (hren : pullV ren W = ctMapValD V)
    (q : NFProg jasminDialect Δ (ts.map mapTy))
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes p ren = some q) :
    NFProg.leakRun (jLeakModel Pj) fuel q W =
      (NFProg.leakRun (catLeakModel P) fuel p V).map
        fun r => (transArgs mapTy (fun x => ctTransTy x) r.1, r.2) :=
  NFProg.map?_leakRun catToJasmin (fun x => ctTransTy x) ctMapValD (catLeakModel P)
    (jLeakModel Pj) catToJasmin_regionTypes (fun _ => True) catToJasmin_varTransports
    (fun e _ blk hblk V => catToJasmin_block e blk hblk V)
    (fun e _ blk hblk V => catToJasmin_blockLeak hc e blk hblk V)
    catToJasmin_mapValExtends catToJasmin_regionTransports fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) ren V W hren q hq

/-- **The events of `map?` along `catToJasmin` at the identity renaming.** Under
    `LeakCompat P Pj`, the lowered program runs at `ctMapValD V` to the events of the
    source run at `V`, at every fuel. -/
theorem catToJasmin_map?_ctLeak {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) (fuel : Nat) {Γ : Ctx} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) (q : NFProg jasminDialect (mapCtx Γ) (ts.map mapTy))
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes p (fun v => v) = some q)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    (NFProg.leakRun (jLeakModel Pj) fuel q (ctMapValD V)).map Prod.snd =
      (NFProg.leakRun (catLeakModel P) fuel p V).map Prod.snd := by
  rw [catToJasmin_map?_leakRun hc fuel p _ V (ctMapValD V)
    (FieldDialectBlockDescent.pullV_id _) q hq, Option.map_map]
  rfl

end NFProgCatToJasmin

end CatCrypt.Crypto.SecureCompilation.VIR
