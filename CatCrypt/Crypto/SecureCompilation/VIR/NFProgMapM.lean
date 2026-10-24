/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-!
# Lowering `NFProg` along a partial block lowering into a dialect with partial operations

`NFProg.map? P hT p ren` (`VIR/NFProgMap.lean`) lowers a structured program along a partial
block lowering `P`. Its preservation theorem `NFProg.map?_denoteAt` reads the blocks of `P`
by the total denotation `Com.denote`, so both dialects carry a `DialectDenote` instance.
This module states preservation for dialects whose operations denote in `Option` only
(`DialectDenoteM d Option`), as the cast `fromWords` of the field dialect does: the block of
an expression is read by `Com.denoteM` in `Option`, and the leaf hypothesis is an equation
of `Option` values (bisimulation form) or a forward implication (forward form).

The renaming that relates the target valuation to the transported source valuation is
stated pointwise, `∀ v, (ren v).lookup W = v.lookup (mapVal V)`, which is the equation
`pullV ren W = mapVal V` of `map?_denoteAt` read at each variable.

## Main definitions

* `NFProg.RenRel` — a renaming reads at each variable what a valuation reads.

## Main results

* `NFProg.Com.denoteM_rename_of` — a renamed block denotes in `Option` what the block
  denotes at a valuation the renaming reads back.
* `NFProg.spliceNF?_denoteM` — the `Option` denotation of `spliceNF?`.
* `NFProg.map?_denoteAtM` — bisimulation form: under the block leaf
  `blk.denoteM (mapVal V) = (e.denoteM V).map transTy`, a program `map?` returns denotes
  the transport of the source denotation, at explicit call environments;
  `NFProg.map?_denoteM_call` is the same at the instance call environments.
* `NFProg.map?_refinesAtM` — forward form: under the block leaf "a successful source
  expression has a successful block with the transported value", a successful source run
  has a successful target run with the transported result; `NFProg.map?_refinesM_call` is
  the same at the instance call environments.
* `PassChain.StepCert.ofMapAtM?` — the chain certificate of `NFProgPasses.mapStep` from the
  forward form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open FieldDialectBlockDescent
open BlockLoweringCPS (consHom castHom)
open BlockLoweringExtend (transArgs)

namespace NFProg

/-! ## 1. Renamings read pointwise -/

section Rename

variable {d : Dialect} [TyDenote d.Ty]

/-- The renaming `ren` reads in `W` at each variable what `W₀` reads there. -/
def RenRel {Γ Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (W : Valuation Δ) (W₀ : Valuation Γ) :
    Prop :=
  ∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W = v.lookup W₀

/-- The identity renaming reads every valuation back. -/
theorem renRel_id {Γ : Ctxt d} (W : Valuation Γ) : RenRel (fun v => v) W W :=
  fun _ => rfl

/-- A lifted renaming reads the extended valuations. -/
theorem RenRel.lift {Γ Δ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {W : Valuation Δ}
    {W₀ : Valuation Γ} (h : RenRel ren W W₀) {s : d.Ty} (x : ⟦s⟧) :
    RenRel (Ctxt.Hom.lift ren) (W.extend x) (W₀.extend x) := by
  intro t v
  cases v with
  | here => rfl
  | there v => exact h v

/-- Renamed argument variables read what the arguments read at a valuation the renaming
    reads back. -/
theorem lookupArgs_renameVars_of {Γ Δ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {W : Valuation Δ}
    {W₀ : Valuation Γ} (h : RenRel ren W W₀) :
    {ts : List d.Ty} → (args : HVector (fun t => Var Γ t) ts) →
    Expr.lookupArgs (HVector.renameVars ren args) W = Expr.lookupArgs args W₀
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [h v, lookupArgs_renameVars_of h rest]

variable [DialectSignature d] [DialectDenoteM d Option]

/-- A renamed expression denotes in `Option` what the expression denotes at a valuation
    the renaming reads back. -/
theorem Expr.denoteM_rename_of {Γ Δ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {W : Valuation Δ}
    {W₀ : Valuation Γ} (h : RenRel ren W W₀) {t : d.Ty} (e : Expr d Γ t) :
    (e.rename ren).denoteM (M := Option) W = e.denoteM W₀ := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenoteM.denoteM op (Expr.lookupArgs (HVector.renameVars ren args) W) =
    DialectDenoteM.denoteM op (Expr.lookupArgs args W₀)
  rw [lookupArgs_renameVars_of h args]

/-- A renamed block denotes in `Option` what the block denotes at a valuation the renaming
    reads back. -/
theorem Com.denoteM_rename_of : {Γ Δ : Ctxt d} → {t : d.Ty} → (ren : Ctxt.Hom Γ Δ) →
    (c : Com d Γ t) → (W : Valuation Δ) → (W₀ : Valuation Γ) → RenRel ren W W₀ →
    (Com.rename ren c).denoteM (M := Option) W = c.denoteM W₀
  | _, _, _, ren, .ret v, W, W₀, h => by
      show some ((ren v).lookup W) = some (v.lookup W₀)
      rw [h v]
  | _, _, _, ren, .var e body, W, W₀, h => by
      show (e.rename ren).denoteM W >>= _ = e.denoteM W₀ >>= _
      rw [Expr.denoteM_rename_of h e]
      cases e.denoteM (M := Option) W₀ with
      | none => rfl
      | some x => exact Com.denoteM_rename_of _ body _ _ (h.lift x)

end Rename

/-! ## 2. Splicing a block that may fail -/

section Splice

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option] [CallDenote d]

/-- **The `Option` denotation of `spliceNF?`.** Let `G` be `none` where the block fails,
    and let every program `k ren res` denote `G` whenever the block succeeds with `y`,
    `ren` preserves lookups back to `W`, and `res` holds `y`. Then every program the splice
    returns denotes `G`. -/
theorem spliceNF?_denoteM (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {a : d.Ty} → (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts)) →
    (W : Valuation Δ) → (G : Option (Valuation ts)) →
    (blk.denoteM (M := Option) W = none → G = none) →
    (∀ y, blk.denoteM (M := Option) W = some y →
      ∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (W' : Valuation Δ'),
        RenRel ren W' W → res.lookup W' = y →
        ∀ q, k ren res = some q → q.denote fuel W' = G) →
    ∀ q, spliceNF? blk k = some q → q.denote fuel W = G
  | _, _, .ret v, _, W, _, _, hk => fun q hq =>
      hk (v.lookup W) rfl (fun x => x) v W (renRel_id W) rfl q hq
  | _, _, .var e blk, k, W, G, hnone, hk => by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      show e.denoteM W >>= _ = G
      have hd : (Com.var e blk).denoteM (M := Option) W =
          e.denoteM W >>= fun x => blk.denoteM (W.extend x) := rfl
      cases he : e.denoteM (M := Option) W with
      | none =>
          rw [he] at hd
          exact (hnone hd).symm
      | some x =>
          rw [he] at hd
          exact spliceNF?_denoteM fuel blk _ (W.extend x) G
            (fun h => hnone (hd.trans h))
            (fun y hy {_} ren res W' h1 h2 => hk y (hd.trans hy) (fun v => ren (.there v)) res W'
              (fun v => h1 (.there v)) h2) q' hq'

end Splice

/-! ## 3. Renamings of the lowering, read pointwise -/

section Lifts

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
variable (P : PartialBlockLowering d d') (transTy : P.TransTy) (mapVal : P.MapVal)

omit [DialectSignature d'] [HasWord64 d'] [HasBoolBit d'] in
/-- A variable of a context carried along an equality of contexts reads in the carried
    valuation what the carried variable reads. -/
theorem lookup_cast_val {Γ₁ Γ₂ : Ctxt d'} (h : Γ₁ = Γ₂) (V₂ : Valuation Γ₂) {s : d'.Ty}
    (v : Var Γ₁ s) : v.lookup (h ▸ V₂ : Valuation Γ₁) = (castHom h v).lookup V₂ := by
  subst h
  rfl

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] in
/-- The renaming `P.bodyHom ren ren' res` reads back the transported extended valuation. -/
theorem renRel_bodyHom (hExt : P.MapValExtends transTy mapVal) {Γ : Ctxt d} {u : d.Ty}
    {Δ Δ' : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (ren' : Ctxt.Hom Δ Δ')
    (res : Var Δ' (P.mapTy u)) (V : Valuation Γ) (x : ⟦u⟧) (W : Valuation Δ)
    (W' : Valuation Δ') (hren : RenRel ren W (mapVal V)) (h1 : RenRel ren' W' W)
    (h2 : res.lookup W' = transTy x) :
    RenRel (P.bodyHom ren ren' res) W' (mapVal (V.extend x)) := by
  intro s v
  rw [show mapVal (V.extend x) = _ from hExt V x, lookup_cast_val (P.mapCtx_cons u Γ)]
  show (consHom (fun w => ren' (ren w)) res (castHom (P.mapCtx_cons u Γ) v)).lookup W' =
    (castHom (P.mapCtx_cons u Γ) v).lookup ((mapVal V).extend (transTy x))
  generalize castHom (P.mapCtx_cons u Γ) v = w
  cases w with
  | here => exact h2
  | there w =>
      show (ren' (ren w)).lookup W' = w.lookup (mapVal V)
      rw [h1, hren]

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] in
/-- `liftTo` reads back the transported extended valuation. -/
theorem renRel_liftTo (hExt : P.MapValExtends transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} {t : d.Ty} {t' : d'.Ty} (h : P.mapTy t = t')
    (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ) (x : ⟦t⟧)
    (y : ⟦t'⟧) (hren : RenRel ren W (mapVal V)) (hy : tyCast h (transTy x) = y) :
    RenRel (liftTo P h ren) (.cons y W) (mapVal (V.extend x)) := by
  subst h hy
  intro s v
  exact renRel_bodyHom P transTy mapVal hExt ren (fun x => .there x) (varTyCast rfl .here) V x
    W (.cons (tyCast rfl (transTy x)) W) hren (fun _ => rfl) (lookup_varTyCast _ _ _) v

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] in
/-- `appHom` reads back the transported valuation prefixed by a transported tuple. -/
theorem renRel_appHom (hExt : P.MapValExtends transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : RenRel ren W (mapVal V)) :
    (cs : List d.Ty) → (acc : Valuation cs) →
    RenRel (appHom P cs ren) (hvAppend (transArgs P.mapTy transTy acc) W)
      (mapVal (hvAppend acc V))
  | [], .nil => hren
  | _ :: cs, .cons a acc =>
      renRel_liftTo P transTy mapVal hExt rfl (appHom P cs ren) (hvAppend acc V)
        (hvAppend (transArgs P.mapTy transTy acc) W) a _
        (renRel_appHom hExt ren V W hren cs acc) rfl

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] in
/-- The mapped and renamed argument variables read the transported argument values. -/
theorem lookupArgs_mapArgs_of (hVar : P.VarTransports transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : RenRel ren W (mapVal V)) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    Expr.lookupArgs (mapArgs P ren vs) W = transArgs P.mapTy transTy (Expr.lookupArgs vs V)
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupArgs_mapArgs_of hVar ren V W hren vs, hren, hVar]

end Lifts

/-! ## 4. Preservation -/

section Preservation

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  [DialectDenoteM d Option] [DialectDenoteM d' Option]
variable (P : PartialBlockLowering d d') (transTy : P.TransTy) (mapVal : P.MapVal)

/-- **Preservation, bisimulation form.** Under the variable leaf, the block leaf
    `blk.denoteM (mapVal V) = (e.denoteM V).map transTy` on the `Good` expressions `P`
    accepts, the binding-threading leaf, `RegionTransports`, and the agreement `hCall` of
    the call environments of `d` and `d'` at every call of the program, a program that
    `map?` returns for a `Good`-covered program at a renaming `ren` reading back the
    transported `V` denotes, at every fuel, the transport of the source denotation. -/
theorem map?_denoteM_call [CallDenote d] [CallDenote d'] (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denoteM (M := Option) (mapVal V) =
        (e.denoteM (M := Option) V).map transTy)
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good)
    (hCall : (CallDenote.env (d := d)).Transports (CallDenote.env (d := d'))
      (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x) p.Calls) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      RenRel ren W (mapVal V) → ∀ q, map? P hT p ren = some q →
      q.denote fuel W = (p.denote fuel V).map (transArgs P.mapTy transTy) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren q hq
      cases hq
      show some _ = some _
      rw [lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren q hq
      obtain ⟨hg, hk⟩ := hp
      obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
      have hB : (Com.rename ren blk).denoteM (M := Option) W =
          (e.denoteM (M := Option) V).map transTy := by
        rw [Com.denoteM_rename_of ren blk W (mapVal V) hren, hBlk e hg blk hblk V]
      refine spliceNF?_denoteM fuel _ _ W _ (fun h => ?_)
        (fun y hy {_} ren' res W' h1 h2 q' hq' => ?_) q hq
      · rw [hB, Option.map_eq_none_iff] at h
        rw [denote_var, h]
        rfl
      · rw [hB] at hy
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
        rw [denote_var, hx]
        exact ih hk hCall _ (V.extend x) W'
          (renRel_bodyHom P transTy mapVal hExt ren ren' res V x W W' hren h1 h2) q' hq'
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨hb, hk⟩ := hp
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookup_varTyCast, hren, hVar, hR.toNat_trans,
        lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
      rw [foldlM_option_map _ _ (transArgs P.mapTy transTy) (fun acc i => by
        rw [← hR.ofNat_trans i]
        exact ihb hb hCb _ _ _ (renRel_appHom P transTy mapVal hExt _ _ _
          (renRel_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ acc) b hbq)]
      exact bind_map_comm _ _ _ _ _
        (fun acc => ihk hk hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ acc)
          k' hkq)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨ht, he, hk⟩ := hp
      have hCt := hCall.mono fun _ _ _ h => Or.inl h
      have hCe := hCall.mono fun _ _ _ h => Or.inr (Or.inl h)
      have hCk := hCall.mono fun _ _ _ h => Or.inr (Or.inr h)
      obtain ⟨a, haq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookup_varTyCast, hren, hVar, hR.toBool_trans]
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then a.denote fuel W else b.denote fuel W) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
            else els.denote fuel V).map (transArgs P.mapTy transTy) := by
        split
        · exact iht ht hCt ren V W hren a haq
        · exact ihe he hCe ren V W hren b hbq
      rw [harm]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hk hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ r)
          k' hkq)
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨hb, hk⟩ := hp
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren,
        whileIter_map (fun acc => body.denote fuel (hvAppend acc V)) _
          (transArgs P.mapTy transTy) (fun b => tyCast hT.bit_eq (transTy b))
          hR.toBool_trans (fun a => by
            rw [denote_castRetHead,
              ihb hb hCb _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ a) b hbq,
              Option.map_map]
            congr 1
            funext r
            cases r
            rfl)]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hk hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ r)
          k' hkq)
  | call f args k ih =>
      intro Δ ren V W hren q hq
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren,
        hCall f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩)]
      exact bind_map_comm _ _ _ _ _
        (fun r => ih hp hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ r)
          k' hkq)

/-- **Preservation at explicit call environments, bisimulation form.** `map?_denoteM_call`
    with the source program denoted at the call environment `E` and the lowered program at
    `E'`, under the agreement of `E` and `E'` along the transport at every call of the
    program. This is `map?_denoteAt` for dialects whose operations denote in `Option`. -/
theorem map?_denoteAtM (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denoteM (M := Option) (mapVal V) =
        (e.denoteM (M := Option) V).map transTy)
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (E : CallEnv d) (E' : CallEnv d') (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : p.Covered Good)
    (hCall : E.Transports E' (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x)
      p.Calls) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      RenRel ren W (mapVal V) → ∀ q, map? P hT p ren = some q →
      q.denoteAt E' fuel W = (p.denoteAt E fuel V).map (transArgs P.mapTy transTy) :=
  letI : CallDenote d := ⟨E⟩
  letI : CallDenote d' := ⟨E'⟩
  map?_denoteM_call P transTy mapVal hT Good hVar hBlk hExt hR fuel p hp hCall

/-- **Preservation, forward form.** Under the variable leaf, the block leaf "a successful
    `Good` expression has a successful block with the transported value", the
    binding-threading leaf, `RegionTransports`, and the agreement `hCall` of the call
    environments at every call of the program, a successful run of a `Good`-covered
    program has a successful run of every program `map?` returns for it, at a renaming
    reading back the transported valuation, with the transported result. -/
theorem map?_refinesM_call [CallDenote d] [CallDenote d'] (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk → ∀ (V : Valuation Γ) (x : ⟦t⟧),
      e.denoteM (M := Option) V = some x →
      blk.denoteM (M := Option) (mapVal V) = some (transTy x))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good)
    (hCall : (CallDenote.env (d := d)).Transports (CallDenote.env (d := d'))
      (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x) p.Calls) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      RenRel ren W (mapVal V) → ∀ q, map? P hT p ren = some q →
      ∀ out, p.denote fuel V = some out →
      q.denote fuel W = some (transArgs P.mapTy transTy out) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren q hq out ho
      cases hq
      cases ho
      show some _ = some _
      rw [lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren q hq out ho
      obtain ⟨hg, hk⟩ := hp
      obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
      rw [denote_var] at ho
      obtain ⟨x, hx, ho⟩ := Option.bind_eq_some_iff.mp ho
      have hB : (Com.rename ren blk).denoteM (M := Option) W = some (transTy x) := by
        rw [Com.denoteM_rename_of ren blk W (mapVal V) hren, hBlk e hg blk hblk V x hx]
      refine spliceNF?_denoteM fuel _ _ W _ (fun h => by rw [hB] at h; cases h)
        (fun y hy {_} ren' res W' h1 h2 q' hq' => ?_) q hq
      rw [hB] at hy
      cases hy
      exact ih hk hCall _ (V.extend x) W'
        (renRel_bodyHom P transTy mapVal hExt ren ren' res V x W W' hren h1 h2) q' hq' out ho
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren q hq out ho
      obtain ⟨hb, hk⟩ := hp
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [denote_forLoop] at ho
      obtain ⟨acc, hacc, ho⟩ := Option.bind_eq_some_iff.mp ho
      rw [denote_forLoop, lookup_varTyCast, hren, hVar, hR.toNat_trans,
        lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
      obtain ⟨acc', hacc', rfl⟩ := foldlM_rel_fwd (R := fun a a' => a' = transArgs P.mapTy transTy a)
        (f := fun acc i => body.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
        (g := fun acc i => b.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d') i) W)))
        _ (fun i _ a a' c hr hc => by
          subst hr
          refine ⟨_, ?_, rfl⟩
          rw [← hR.ofNat_trans i]
          exact ihb hb hCb _ _ _ (renRel_appHom P transTy mapVal hExt _ _ _
            (renRel_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ a) b hbq c hc)
        _ _ acc rfl hacc
      rw [hacc']
      exact ihk hk hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ acc) k' hkq
        out ho
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren q hq out ho
      obtain ⟨ht, he, hk⟩ := hp
      have hCt := hCall.mono fun _ _ _ h => Or.inl h
      have hCe := hCall.mono fun _ _ _ h => Or.inr (Or.inl h)
      have hCk := hCall.mono fun _ _ _ h => Or.inr (Or.inr h)
      obtain ⟨a, haq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [denote_ifThenElse] at ho
      obtain ⟨r, hr, ho⟩ := Option.bind_eq_some_iff.mp ho
      rw [denote_ifThenElse, lookup_varTyCast, hren, hVar, hR.toBool_trans]
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then a.denote fuel W else b.denote fuel W) =
          some (transArgs P.mapTy transTy r) := by
        split
        · rename_i hc
          rw [ite_eq_left hc] at hr
          exact iht ht hCt ren V W hren a haq r hr
        · rename_i hc
          rw [ite_eq_right hc] at hr
          exact ihe he hCe ren V W hren b hbq r hr
      rw [harm]
      exact ihk hk hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ r) k' hkq
        out ho
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren q hq out ho
      obtain ⟨hb, hk⟩ := hp
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [denote_whileLoop] at ho
      obtain ⟨acc, hacc, ho⟩ := Option.bind_eq_some_iff.mp ho
      rw [denote_whileLoop, lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
      obtain ⟨acc', hacc', rfl⟩ := whileIter_rel_fwd
        (R := fun a a' => a' = transArgs P.mapTy transTy a)
        (step := fun acc => body.denote fuel (hvAppend acc V))
        (step' := fun acc => (castRetHead hT.bit_eq b).denote fuel (hvAppend acc W))
        (fun a a' c hr hc => by
          subst hr
          refine ⟨.cons (tyCast hT.bit_eq (transTy c.head)) (transArgs P.mapTy transTy c.tail),
            ?_, rfl, (hR.toBool_trans c.head).symm⟩
          rw [denote_castRetHead,
            ihb hb hCb _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ a) b hbq c hc]
          cases c
          rfl)
        fuel _ _ acc rfl hacc
      rw [hacc']
      exact ihk hk hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ acc) k' hkq
        out ho
  | call f args k ih =>
      intro Δ ren V W hren q hq out ho
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [denote_call] at ho
      obtain ⟨r, hr, ho⟩ := Option.bind_eq_some_iff.mp ho
      rw [denote_call, lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren,
        hCall f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), hr]
      exact ih hp hCk _ _ _ (renRel_appHom P transTy mapVal hExt ren V W hren _ r) k' hkq
        out ho

/-- **Preservation at explicit call environments, forward form.** `map?_refinesM_call` with
    the source program denoted at the call environment `E` and the lowered program at
    `E'`. -/
theorem map?_refinesAtM (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk → ∀ (V : Valuation Γ) (x : ⟦t⟧),
      e.denoteM (M := Option) V = some x →
      blk.denoteM (M := Option) (mapVal V) = some (transTy x))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (E : CallEnv d) (E' : CallEnv d') (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : p.Covered Good)
    (hCall : E.Transports E' (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x)
      p.Calls) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      RenRel ren W (mapVal V) → ∀ q, map? P hT p ren = some q →
      ∀ out, p.denoteAt E fuel V = some out →
      q.denoteAt E' fuel W = some (transArgs P.mapTy transTy out) :=
  letI : CallDenote d := ⟨E⟩
  letI : CallDenote d' := ⟨E'⟩
  map?_refinesM_call P transTy mapVal hT Good hVar hBlk hExt hR fuel p hp hCall

end Preservation

end NFProg

section MapCert

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  [DialectDenoteM d Option] [DialectDenoteM d' Option]

open NFProgPasses in
/-- **The certificate of the lowering along a partial block lowering into a dialect with
    partial operations, at call environments.** Under the variable leaf, the forward block
    leaf on every expression `P` accepts, the binding-threading leaf, `RegionTransports`,
    and the agreement `hCall` of the call environments `E` and `E'` along the transport at
    every call, the step `mapStep P hT Γ ts` is certified from the semantics at `E` to the
    semantics at `E'`, at every fuel, with the graph of `mapVal` as input relation and the
    graph of the transport of result tuples as output relation, from
    `NFProg.map?_refinesAtM`. -/
def PassChain.StepCert.ofMapAtM? (P : PartialBlockLowering d d') (hT : P.RegionTypes)
    (transTy : P.TransTy) (mapVal : P.MapVal) (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) blk, P.lowerExprBlock? e = some blk →
      ∀ (V : Valuation Γ) (x : ⟦t⟧), e.denoteM (M := Option) V = some x →
      blk.denoteM (M := Option) (mapVal V) = some (transTy x))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (E : CallEnv d) (E' : CallEnv d')
    (hCall : E.Transports E' (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x)
      (fun _ _ _ => True))
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.StepCert (mapStep P hT Γ ts).run (nfSemE E fuel Γ ts)
      (nfSemE E' fuel (P.mapCtx Γ) (ts.map P.mapTy)) where
  relIn V W := W = mapVal V
  relOut o o' := o' = transArgs P.mapTy transTy o
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    exact ⟨_, NFProg.map?_refinesAtM P transTy mapVal hT (fun _ => True) hVar
      (fun e _ blk hb V x hx => hBlk e blk hb V x hx) hExt hR E E' fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) (hCall.mono fun _ _ _ _ => trivial)
      _ V (mapVal V) (NFProg.renRel_id _) q hf o hd, rfl⟩

end MapCert

end CatCrypt.Crypto.SecureCompilation.VIR
