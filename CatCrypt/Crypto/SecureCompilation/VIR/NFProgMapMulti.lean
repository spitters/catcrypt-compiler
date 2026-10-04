/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering

/-!
# Lifting a multi-value block lowering through the regions of `NFProg`

A multi-value lowering `L : MultiBlockLoweringData d d'` represents a source type `t` by
the list of target types `L.mapTys t` and a source op by a closed multi-result block over
the flattened argument registers. `NFProg.mapM L hT p ren` lowers the structured program
`p : NFProg d Γ ts` to `NFProg d' Δ (ctxFlat L.mapTys ts)`: a let-binding becomes the
op's block, renamed along the registers of its arguments and spliced in front of the
lowered continuation (`spliceM`); a counted loop, a branch and an exit-flag loop become the
same constructor of `NFProg d'`, with the carried tuple, the branch results and the final
tuple flattened by `L.mapTys`. The lowering is renaming-accumulating: `ren` renames the
flattened source context into the target context.

The region constructors read the trip counter at `HasWord64.word` and the bit at
`HasBitType.bit`. `RegionTypesM L` states that `L.mapTys` sends each of them to the
singleton list of the corresponding target type; `RegionTransportsM` states that the
encoding is compatible with the trip count, the trip index and the decision bit.

The single-valued lowering `NFProg.map` embeds: `BlockLoweringData.toMulti L hNil` is the
multi-value lowering with singleton type lists, whose op block is the block of the closed
expression of the op, for a block lowering whose context map sends `[]` to `[]`.

## Main definitions

* `NFProg.castVal`, `NFProg.castRet`: a valuation and a program carried along an equality
  of type lists.
* `NFProg.spliceM`: a multi-result block followed by a once-applied continuation.
* `NFProg.RegionTypesM`, `NFProg.RegionTransportsM`: the conditions on a multi-value
  lowering at the trip counter and the bit.
* `NFProg.mapM`: the lowering of a structured program along a multi-value lowering.
* `FieldDialectBlockDescent.BlockLoweringData.toMulti`: a block lowering as a multi-value
  lowering with singleton type lists.

## Main results

* `NFProg.spliceM_denote`: the denotation of `spliceM`.
* `NFProg.mapM_denote`: under the `Good`-gated block square and `RegionTransportsM`, the
  lowered program denotes, on the flattened encoding of a valuation and at every fuel, the
  flattened encoding of the source denotation.
* `BlockLoweringData.toMulti_blockSquare`, `toMulti_fundamental`,
  `toMulti_lowerMulti_denote`: the block square of `toMulti L` from the block square of
  `L`, and the agreement of `(toMulti L).lowerMulti` with `L.blockLowerCom` through
  `blockFundamental`.
* `NFProg.mapM_toMulti_denote`: `mapM` at `toMulti L` and `map` at `L` denote the same
  results, up to the identification of `ts.map L.mapTy` with the singleton flattening.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering
open FieldDialectBlockDescent
  (BlockLoweringData TransTy MapVal VarTransports MapValExtends BlockOpTransports pullV)
open BlockLoweringCPS (castHom valuation_ext lookup_pullV CoveredCom)
open BlockLoweringExtend (transArgs)

namespace NFProg

/-! ## 1. Casts along an equality of type lists -/

section Casts

variable {d : Dialect} [TyDenote d.Ty]

/-- A valuation carried along an equality of contexts. -/
def castVal {A B : Ctxt d} (h : A = B) (X : Valuation A) : Valuation B := h ▸ X

/-- Carrying a valuation along two equalities is carrying it along their composite. -/
theorem castVal_castVal {A B C : Ctxt d} (h₁ : A = B) (h₂ : B = C) (X : Valuation A) :
    castVal h₂ (castVal h₁ X) = castVal (h₁.trans h₂) X := by
  subst h₁ h₂
  rfl

/-- Carrying a valuation along an equality and back is the identity. -/
theorem castVal_symm {A B : Ctxt d} (h : A = B) (X : Valuation A) :
    castVal h.symm (castVal h X) = X := by
  subst h
  rfl

/-- A cons cell carried along an equality of tails. -/
theorem castVal_cons {A B : Ctxt d} {a : d.Ty} (h : a :: A = a :: B) (h' : A = B) (x : ⟦a⟧)
    (X : Valuation A) : castVal h (.cons x X) = .cons x (castVal h' X) := by
  subst h'
  rfl

/-- A one-entry valuation carried along an equality of its type. -/
theorem castVal_single {a b : d.Ty} (h : a = b) (x : ⟦a⟧) :
    castVal (congrArg (fun t => [t]) h) (.cons x .nil) = .cons (NFProg.tyCast h x) .nil := by
  subst h
  rfl

/-- A one-entry valuation carried along an equality of its type and back. -/
theorem castVal_single_symm {a b : d.Ty} (h : a = b) (x : ⟦a⟧) :
    castVal (congrArg (fun t => [t]) h).symm (.cons (NFProg.tyCast h x) .nil) =
      .cons x .nil := by
  subst h
  rfl

/-- An appended valuation whose left part has the types `ms = [w]`, carried along
    `ms ++ cs = [w] ++ cs`. -/
theorem castVal_append {ms : Ctxt d} {w : d.Ty} (h : ms = [w]) (X : Valuation ms)
    {cs : Ctxt d} (Y : Valuation cs) :
    castVal (congrArg (· ++ cs) h) (hvAppend X Y) = .cons (castVal h X).head Y := by
  subst h
  cases X with
  | cons x X => cases X; rfl

/-- Two valuations of the empty context are equal. -/
theorem valuation_nil_eq (X Y : Valuation ([] : Ctxt d)) : X = Y := by
  cases X; cases Y; rfl

/-- The variable of a one-element context `ms = [w]`. -/
def singleVar {ms : Ctxt d} {w : d.Ty} (h : ms = [w]) : Var ms w := castHom h.symm .here

/-- The variable of a one-element context reads the entry of the carried valuation. -/
theorem lookup_singleVar {ms : Ctxt d} {w : d.Ty} (h : ms = [w]) (X : Valuation ms) :
    (singleVar h).lookup X = (castVal h X).head := by
  subst h
  cases X with
  | cons x X => rfl

variable [DialectSignature d] [DialectDenote d]

/-- Pulling back along a renaming by an equality of contexts is the carried valuation. -/
theorem pullV_castHom_symm {A B : Ctxt d} (h : A = B) (X : Valuation A) :
    pullV (castHom h.symm) X = castVal h X := by
  subst h
  exact FieldDialectBlockDescent.pullV_id X

/-- Pulling back along a renaming by an equality of contexts undoes the carrying. -/
theorem pullV_castHom_castVal {A B : Ctxt d} (h : A = B) (X : Valuation A) :
    pullV (castHom h) (castVal h X) = X := by
  subst h
  exact FieldDialectBlockDescent.pullV_id X

/-- The renaming of `ms ++ Θ` into `w :: Δ` for `ms = [w]`: the entry of `ms` goes to the
    head and `Θ` goes through `ren`. -/
def liftOne {ms Θ Δ : Ctxt d} {w : d.Ty} (h : ms = [w]) (ren : Ctxt.Hom Θ Δ) :
    Ctxt.Hom (ms ++ Θ) (w :: Δ) :=
  appendHom (fun v => inlHom Δ (castHom h v)) (fun v => (ren v).there)

/-- The pullback along `liftOne` of a valuation with head `y`. -/
theorem pullV_liftOne {ms Θ Δ : Ctxt d} {w : d.Ty} (h : ms = [w]) (ren : Ctxt.Hom Θ Δ)
    (y : ⟦w⟧) (W : Valuation Δ) :
    pullV (liftOne h ren) (.cons y W) =
      hvAppend (castVal h.symm (.cons y .nil)) (pullV ren W) := by
  subst h
  unfold liftOne
  rw [pullV_appendHom, FieldDialectBlockDescent.pullV_there]
  congr 1

end Casts

section CastRet

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A program with its result types carried along an equality of type lists. -/
def castRet {Δ : Ctxt d} {ts ts' : List d.Ty} (h : ts = ts') (p : NFProg d Δ ts) :
    NFProg d Δ ts' :=
  h ▸ p

/-- A program with its result types carried denotes the carried results. -/
theorem denote_castRet [DialectDenote d] [CallDenote d] {Δ : Ctxt d} {ts ts' : List d.Ty} (h : ts = ts')
    (p : NFProg d Δ ts) (fuel : Nat) (W : Valuation Δ) :
    (castRet h p).denote fuel W = (p.denote fuel W).map (castVal h) := by
  subst h
  show p.denote fuel W = _
  cases p.denote fuel W <;> rfl

end CastRet

/-! ## 2. Splicing a multi-result block into a structured program -/

section Splice

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **A multi-result block followed by a continuation.** `spliceM blk k` keeps the bindings
    of `blk` and, at its return vector `res`, continues with `k ren res`, where `ren`
    renames the context of `blk` into the extended context. -/
def spliceM {ts : List d.Ty} : {Δ : Ctxt d} → {as : List d.Ty} → MultiReturnCom d Δ as →
    ({Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) as → NFProg d Δ' ts) →
    NFProg d Δ ts
  | _, _, .ret vs, k => k (fun x => x) vs
  | _, _, .var e blk, k => .var e (spliceM blk (fun ren res => k (fun x => ren (.there x)) res))

/-- **Denotation of `spliceM`.** If `k ren res` denotes `G` whenever `ren` preserves lookups
    back to `W` and `res` holds the values of the block, the splice denotes `G`. -/
theorem spliceM_denote [DialectDenote d] [CallDenote d] (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {as : List d.Ty} → (blk : MultiReturnCom d Δ as) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) as → NFProg d Δ' ts) →
    (W : Valuation Δ) → (G : Option (Valuation ts)) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : HVector (fun u => Var Δ' u) as)
        (W' : Valuation Δ'),
        (∀ {s : d.Ty} (v : Var Δ s), (ren v).lookup W' = v.lookup W) →
        MultiReturnCom.lookupVars res W' = blk.denote W →
        (k ren res).denote fuel W' = G) →
    (spliceM blk k).denote fuel W = G
  | _, _, .ret vs, _, W, _, hk => hk (fun x => x) vs W (fun _ => rfl) rfl
  | _, _, .var e blk, _, W, G, hk => by
      simp only [spliceM, denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      exact spliceM_denote fuel blk _ (W.extend (e.denote W)) G
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2)

end Splice

/-! ## 3. The region conditions and the lowering -/

section Map

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The type map of `L` sends the trip-counter type and the bit type of `d` to the
    singleton lists of those of `d'`. -/
structure RegionTypesM (L : MultiBlockLoweringData d d') : Prop where
  /-- The trip-counter type is represented by one trip-counter register. -/
  word_eq : L.mapTys (HasWord64.word (d := d)) = [HasWord64.word (d := d')]
  /-- The bit type is represented by one bit register. -/
  bit_eq : L.mapTys (HasBitType.bit (d := d)) = [HasBitType.bit (d := d')]

/-- The encoding `enc` of `L` is compatible with the readings of the trip counter and the
    bit: `toNat` (the trip count), `ofNat` (the trip index) and `toBool` (the branch and
    exit decisions). -/
structure RegionTransportsM (L : MultiBlockLoweringData d d') (hT : RegionTypesM L)
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (L.mapTys t)) : Prop where
  /-- An encoded counter value denotes the same trip count. -/
  toNat_enc : ∀ x : ⟦HasWord64.word (d := d)⟧,
    HasWord64.toNat (d := d') (castVal hT.word_eq (enc x)).head = HasWord64.toNat (d := d) x
  /-- The encoded trip index is the trip index. -/
  ofNat_enc : ∀ i : Nat,
    enc (HasWord64.ofNat (d := d) i) =
      castVal hT.word_eq.symm (.cons (HasWord64.ofNat (d := d') i) .nil)
  /-- An encoded bit reads as the same `Bool`. -/
  toBool_enc : ∀ b : ⟦HasBitType.bit (d := d)⟧,
    HasBoolBit.toBool (d := d') (castVal hT.bit_eq (enc b)).head = HasBoolBit.toBool (d := d) b

/-- The renaming of `ctxFlat m (cs ++ Γ)` into `ctxFlat m cs ++ Δ` that sends the prefix to
    the prefix and the rest through `ren`. -/
def appHomM (m : d.Ty → List d'.Ty) {Γ : Ctxt d} {Δ : Ctxt d'} (cs : Ctxt d)
    (ren : Ctxt.Hom (ctxFlat m Γ) Δ) : Ctxt.Hom (ctxFlat m (cs ++ Γ)) (ctxFlat m cs ++ Δ) :=
  fun v => appendHom (inlHom Δ) (fun w => inrHom (ctxFlat m cs) (ren w)) (splitHom m cs Γ v)

/-- **The lowering of a structured program along a multi-value lowering.** A let-binding
    becomes the block of its op, renamed along the registers of its arguments and spliced
    in front of the lowered continuation; a return, a counted loop, a branch and an
    exit-flag loop become the same constructor of `NFProg d'`, with their variables and
    carried tuples flattened by `L.mapTys` and their regions lowered. The counter, the
    condition and the continue bit are read through `RegionTypesM`. A call keeps its
    symbol, with its arguments and its signature flattened by `L.mapTys`. -/
def mapM (L : MultiBlockLoweringData d d') (hT : RegionTypesM L) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → {Δ : Ctxt d'} →
    Ctxt.Hom (L.mapCtx Γ) Δ → NFProg d' Δ (L.mapCtx ts)
  | _, _, .ret vs, _, ren => .ret (homToHV _ (argsHom L.mapTys ren vs))
  | _, _, .var e k, _, ren =>
      spliceM (MultiReturnCom.rename (argsHom L.mapTys ren e.args) (L.exprBlock e))
        (fun ren' res => mapM L hT k (appendHom (hvToHom res) (fun w => ren' (ren w))))
  | _, _, .forLoop (cs := cs) count inits body k, _, ren =>
      .forLoop (ren (varHom L.mapTys count (singleVar hT.word_eq)))
        (homToHV _ (argsHom L.mapTys ren inits))
        (mapM L hT body
          (appHomM L.mapTys (Γ := HasWord64.word (d := d) :: _) cs (liftOne hT.word_eq ren)))
        (mapM L hT k (appHomM L.mapTys cs ren))
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ren =>
      .ifThenElse (ren (varHom L.mapTys cond (singleVar hT.bit_eq)))
        (mapM L hT thn ren) (mapM L hT els ren) (mapM L hT k (appHomM L.mapTys rs ren))
  | _, _, .whileLoop (cs := cs) inits body k, _, ren =>
      .whileLoop (homToHV _ (argsHom L.mapTys ren inits))
        (castRet (congrArg (· ++ L.mapCtx cs) hT.bit_eq)
          (mapM L hT body (appHomM L.mapTys cs ren)))
        (mapM L hT k (appHomM L.mapTys cs ren))
  | _, _, .call (rs := rs) f args k, _, ren =>
      .call f (homToHV _ (argsHom L.mapTys ren args)) (mapM L hT k (appHomM L.mapTys rs ren))

/-! ## 4. Preservation -/

variable [DialectDenote d] [DialectDenote d']

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d']
  [DialectDenote d] in
/-- `appHomM` relates the flattened valuations `ren` relates, prefixed by a flattened
    tuple. -/
theorem pullV_appHomM {m : d.Ty → List d'.Ty} (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t))
    {Γ : Ctxt d} {Δ : Ctxt d'} (ren : Ctxt.Hom (ctxFlat m Γ) Δ) (V : Valuation Γ)
    (W : Valuation Δ) (hren : pullV ren W = flatVal enc V) (cs : Ctxt d)
    (acc : Valuation cs) :
    pullV (appHomM m cs ren) (hvAppend (flatVal enc acc) W) = flatVal enc (hvAppend acc V) := by
  unfold appHomM
  rw [pullV_comp (fun v => splitHom m cs Γ v)
      (fun v => appendHom (inlHom Δ) (fun w => inrHom (ctxFlat m cs) (ren w)) v),
    pullV_appendHom, pullV_inlHom,
    pullV_comp (fun w => ren w) (fun w => inrHom (ctxFlat m cs) w), pullV_inrHom, hren,
    pullV_splitHom_flatVal]

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d']
  [DialectDenote d] in
/-- The variables `homToHV (argsHom ren vs)` read the flattened argument values. -/
theorem lookupArgs_homToHV_argsHom {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (ctxFlat m Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = flatVal enc V) {ts : List d.Ty}
    (vs : HVector (fun t => Var Γ t) ts) :
    Expr.lookupArgs (homToHV _ (argsHom m ren vs)) W = flatVal enc (Expr.lookupArgs vs V) := by
  rw [← lookupVars_eq_lookupArgs, lookupVars_homToHV, pullV_argsHom enc ren W V hren]

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- The trip-counter variable of a lowered counted loop reads the encoded counter. -/
theorem lookup_counter (L : MultiBlockLoweringData d d')
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (L.mapTys t)) {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = flatVal enc V) {a : d.Ty} {a' : d'.Ty} (h : L.mapTys a = [a'])
    (v : Var Γ a) :
    (ren (varHom L.mapTys v (singleVar h))).lookup W = (castVal h (enc (v.lookup V))).head := by
  rw [← lookup_pullV, hren, ← lookup_pullV, pullV_varHom_flatVal, lookup_singleVar]

variable [CallDenote d] [CallDenote d']

/-- **Preservation.** Under the `Good`-gated block square of `L` and `RegionTransportsM`, a
    `Good`-covered program without `call` lowered by `mapM` at a renaming `ren` relating `W`
    to the flattened encoding of `V` denotes, at every fuel, the flattened encoding of the
    source denotation. -/
theorem mapM_denote (L : MultiBlockLoweringData d d') (hT : RegionTypesM L)
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (L.mapTys t))
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    (hR : RegionTransportsM L hT enc) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hc : p.callFree = true) (hp : p.Covered Good) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      pullV ren W = flatVal enc V →
      (mapM L hT p ren).denote fuel W = (p.denote fuel V).map (flatVal enc) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren
      show some _ = some _
      rw [lookupArgs_homToHV_argsHom enc ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren
      obtain ⟨hg, hk⟩ := hp
      rw [denote_var, Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some]
      refine spliceM_denote fuel _ _ W _ (fun ren' res W' h1 h2 => ?_)
      refine ih hc hk _ (V.extend (e.denote V)) W' ?_
      have hW' : pullV ren' W' = W :=
        valuation_ext _ _ fun v => by rw [lookup_pullV]; exact h1 v
      have hRn : pullV (fun w => ren' (ren w)) W' = flatVal enc V := by
        rw [pullV_comp (fun w => ren w) (fun w => ren' w), hW', hren]
      have hL : pullV (hvToHom res) W' = enc (e.denote V) := by
        rw [pullV_hvToHom, h2, multiReturnCom_denote_rename,
          pullV_argsHom enc ren W V hren]
        rcases e with ⟨op, rfl, args⟩
        exact hBlk ⟨op, rfl, args⟩ hg _
      exact (pullV_appendHom (hvToHom res) (fun w => ren' (ren w)) W').trans
        (congrArg₂ hvAppend hL hRn)
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren
      simp only [callFree, Bool.and_eq_true] at hc
      obtain ⟨hb, hk⟩ := hp
      simp only [mapM, denote]
      rw [lookup_counter L enc ren V W hren, hR.toNat_enc,
        lookupArgs_homToHV_argsHom enc ren V W hren]
      rw [foldlM_option_map
        (fun acc i => body.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
        _ (flatVal enc) (fun acc i => by
        refine ihb hc.1 hb _ _ _
          (pullV_appHomM enc _ (HVector.cons (HasWord64.ofNat (d := d) i) V) _ ?_ _ acc)
        rw [pullV_liftOne, hren, ← hR.ofNat_enc]
        rfl)]
      exact bind_map_comm _ _ _ _ _
        (fun acc => ihk hc.2 hk _ _ _ (pullV_appHomM enc ren V W hren _ acc))
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren
      simp only [callFree, Bool.and_eq_true] at hc
      obtain ⟨ht, he, hk⟩ := hp
      simp only [mapM, denote]
      rw [lookup_counter L enc ren V W hren, hR.toBool_enc]
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then (mapM L hT thn ren).denote fuel W else (mapM L hT els ren).denote fuel W) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
            else els.denote fuel V).map (flatVal enc) := by
        split
        · exact iht hc.1.1 ht ren V W hren
        · exact ihe hc.1.2 he ren V W hren
      rw [harm]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hc.2 hk _ _ _ (pullV_appHomM enc ren V W hren _ r))
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren
      simp only [callFree, Bool.and_eq_true] at hc
      obtain ⟨hb, hk⟩ := hp
      simp only [mapM, denote]
      rw [lookupArgs_homToHV_argsHom enc ren V W hren,
        whileIter_map (fun acc => body.denote fuel (hvAppend acc V)) _
          (flatVal enc) (fun b => (castVal hT.bit_eq (enc b)).head)
          hR.toBool_enc (fun a => by
            rw [denote_castRet,
              ihb hc.1 hb _ _ _ (pullV_appHomM enc ren V W hren _ a), Option.map_map]
            congr 1
            funext r
            cases r with
            | cons b r => exact castVal_append hT.bit_eq (enc b) (flatVal enc r))]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hc.2 hk _ _ _ (pullV_appHomM enc ren V W hren _ r))
  | call => simp [callFree] at hc

/-- **Preservation at the identity renaming.** A `Good`-covered program without `call`
    lowered by `mapM` into the flattened context denotes, on the flattened encoding of a
    valuation and at every fuel, the flattened encoding of the source denotation. -/
theorem mapM_denote_id (L : MultiBlockLoweringData d d') (hT : RegionTypesM L)
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (L.mapTys t))
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    (hR : RegionTransportsM L hT enc) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hc : p.callFree = true) (hp : p.Covered Good) (V : Valuation Γ) :
    (mapM L hT p (fun v => v)).denote fuel (flatVal enc V) =
      (p.denote fuel V).map (flatVal enc) :=
  mapM_denote L hT enc Good hBlk hR fuel p hc hp _ V _ (FieldDialectBlockDescent.pullV_id _)

end Map

end NFProg

/-! ## 5. A block lowering as a multi-value lowering -/

namespace FieldDialectBlockDescent.BlockLoweringData

section ToMulti

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [DialectSignature d']

/-- The expression applying `op` to the variables of its signature. -/
def opExpr (op : d.Op) : Expr d (DialectSignature.sig op) (DialectSignature.ret op) :=
  ⟨op, rfl, allVars _⟩

/-- For a block lowering whose context map sends `[]` to `[]`, the context map is the
    flattening by singleton lists. -/
theorem mapCtx_eq_ctxFlat (L : BlockLoweringData d d') (hNil : L.mapCtx [] = []) :
    ∀ Γ : Ctxt d, L.mapCtx Γ = ctxFlat (fun t => [L.mapTy t]) Γ
  | [] => hNil
  | t :: Γ => (L.mapCtx_cons t Γ).trans (congrArg (L.mapTy t :: ·) (mapCtx_eq_ctxFlat L hNil Γ))

omit [DialectSignature d] [DialectSignature d'] in
/-- The result types of the singleton flattening are the mapped result types. -/
theorem map_eq_ctxFlat (m : d.Ty → d'.Ty) :
    ∀ ts : List d.Ty, ts.map m = ctxFlat (fun t => [m t]) ts
  | [] => rfl
  | t :: ts => congrArg (m t :: ·) (map_eq_ctxFlat m ts)

/-- **A block lowering as a multi-value lowering.** Each source type is represented by the
    singleton list of its mapped type, and the block of an op is the block of `opExpr op`,
    renamed along `mapCtx_eq_ctxFlat`. -/
def toMulti (L : BlockLoweringData d d') (hNil : L.mapCtx [] = []) :
    MultiBlockLoweringData d d' where
  mapTys t := [L.mapTy t]
  lowerOp op :=
    (Com.rename (castHom (L.mapCtx_eq_ctxFlat hNil _)) (L.lowerExprBlock (opExpr op))).toMulti

variable [TyDenote d.Ty] [TyDenote d'.Ty]

/-- The encoding of `toMulti L` carried by a value transport: the one-entry valuation of the
    transported value. -/
def encMulti (L : BlockLoweringData d d') (transTy : TransTy L) {t : d.Ty} (x : ⟦t⟧) :
    Valuation [L.mapTy t] :=
  .cons (transTy x) .nil

variable [DialectDenote d] [DialectDenote d']

omit [DialectDenote d] [DialectDenote d'] in
/-- The flattened encoding of a valuation is the transported valuation, carried along
    `mapCtx_eq_ctxFlat`. -/
theorem flatVal_encMulti (L : BlockLoweringData d d') (hNil : L.mapCtx [] = [])
    (transTy : TransTy L) (mapVal : MapVal L) (hExt : MapValExtends L transTy mapVal) :
    ∀ {Γ : Ctxt d} (V : Valuation Γ),
      flatVal (m := fun t => [L.mapTy t]) (fun x => L.encMulti transTy x) V =
        NFProg.castVal (L.mapCtx_eq_ctxFlat hNil Γ) (mapVal V)
  | [], .nil => NFProg.valuation_nil_eq _ _
  | t :: Γ, .cons x V => by
      have hE : mapVal (HVector.cons x V) = NFProg.castVal (L.mapCtx_cons t Γ).symm
          (HVector.cons (transTy x) (mapVal V)) := hExt V x
      rw [hE, NFProg.castVal_castVal]
      exact (congrArg (HVector.cons (transTy x))
        (flatVal_encMulti L hNil transTy mapVal hExt V)).trans (NFProg.castVal_cons _ _ _ _).symm

omit [DialectDenote d] [DialectDenote d'] in
/-- The flattened encoding of a result tuple is its transport, carried along
    `map_eq_ctxFlat`. -/
theorem flatVal_encMulti_results (L : BlockLoweringData d d') (transTy : TransTy L) :
    ∀ {ts : List d.Ty} (R : Valuation ts),
      flatVal (m := fun t => [L.mapTy t]) (fun x => L.encMulti transTy x) R =
        NFProg.castVal (map_eq_ctxFlat L.mapTy ts) (transArgs L.mapTy transTy R)
  | [], .nil => rfl
  | _ :: _, .cons x R =>
      (congrArg (HVector.cons (transTy x)) (flatVal_encMulti_results L transTy R)).trans
        (NFProg.castVal_cons _ _ _ _).symm

/-- **Block square of `toMulti L`** from the per-op block square of `L` (the op leaf of
    `blockFundamental`) and its binding-threading leaf. -/
theorem toMulti_blockSquare (L : BlockLoweringData d d') (hNil : L.mapCtx [] = [])
    (transTy : TransTy L) (mapVal : MapVal L) (hOp : BlockOpTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) :
    (L.toMulti hNil).BlockSquare (fun x => L.encMulti transTy x) Good := by
  intro Γ t e _ vals
  have hX : pullV (castHom (L.mapCtx_eq_ctxFlat hNil (DialectSignature.sig e.op)))
      (flatVal (m := fun t => [L.mapTy t]) (fun x => L.encMulti transTy x) vals) =
        mapVal vals := by
    rw [flatVal_encMulti L hNil transTy mapVal hExt, NFProg.pullV_castHom_castVal]
  refine (Com.denote_toMulti _ _).trans (congrArg (HVector.cons · .nil) ?_)
  refine (FieldDialectBlockDescent.Com.denote_rename _ _ _).trans ?_
  refine (congrArg _ hX).trans ((hOp _ vals).trans ?_)
  show transTy (DialectDenote.denote e.op (Expr.lookupArgs (allVars _) vals)) = _
  rw [lookupArgs_allVars]

/-- **Fundamental theorem of `toMulti L`.** Every program lowered by `toMulti L` maps the
    flattened encoding of the inputs to the one-entry valuation of the transported value. -/
theorem toMulti_fundamental (L : BlockLoweringData d d') (hNil : L.mapCtx [] = [])
    (transTy : TransTy L) (mapVal : MapVal L) (hOp : BlockOpTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (V : Valuation Γ) :
    ((L.toMulti hNil).lowerMulti c).denote (flatVal (fun x => L.encMulti transTy x) V) =
      .cons (transTy (c.denote V)) .nil :=
  (L.toMulti hNil).multiFundamental_on (fun x => L.encMulti transTy x) (fun _ => True)
    (L.toMulti_blockSquare hNil transTy mapVal hOp hExt (fun _ => True)) c
    (BlockLoweringCPS.coveredCom_of_forall _ (fun _ => trivial) c) V

/-- **`toMulti L` agrees with `L.blockLowerCom`.** Under the three leaves of
    `blockFundamental`, the multi-value lowering of `c` by `toMulti L` denotes on the
    flattened encoding what the single-result embedding of `L.blockLowerCom c` denotes on
    the transported valuation. -/
theorem toMulti_lowerMulti_denote (L : BlockLoweringData d d') (hNil : L.mapCtx [] = [])
    (transTy : TransTy L) (mapVal : MapVal L) (hVar : VarTransports L transTy mapVal)
    (hOp : BlockOpTransports L transTy mapVal) (hExt : MapValExtends L transTy mapVal)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Valuation Γ) :
    ((L.toMulti hNil).lowerMulti c).denote (flatVal (fun x => L.encMulti transTy x) V) =
      (L.blockLowerCom c).toMulti.denote (mapVal V) := by
  rw [toMulti_fundamental L hNil transTy mapVal hOp hExt, Com.denote_toMulti,
    FieldDialectBlockDescent.blockFundamental L transTy mapVal hVar hOp hExt]

end ToMulti

end FieldDialectBlockDescent.BlockLoweringData

namespace NFProg

section ToMultiMap

open FieldDialectBlockDescent.BlockLoweringData

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The region types of `L` give the region types of `toMulti L`. -/
theorem regionTypesM_toMulti (L : BlockLoweringData d d') (hNil : L.mapCtx [] = [])
    (hT : RegionTypes L) : RegionTypesM (L.toMulti hNil) where
  word_eq := congrArg (fun t => [t]) hT.word_eq
  bit_eq := congrArg (fun t => [t]) hT.bit_eq

/-- The region transports of `L` give the region transports of `toMulti L`. -/
theorem regionTransportsM_toMulti [DialectDenote d] [DialectDenote d']
    (L : BlockLoweringData d d') (hNil : L.mapCtx [] = []) (hT : RegionTypes L)
    (transTy : TransTy L) (hR : RegionTransports L hT transTy) :
    RegionTransportsM (L.toMulti hNil) (regionTypesM_toMulti L hNil hT)
      (fun x => L.encMulti transTy x) where
  toNat_enc x :=
    (congrArg (fun X => HasWord64.toNat (d := d') (HVector.head X))
      (castVal_single hT.word_eq (transTy x))).trans (hR.toNat_trans x)
  ofNat_enc i :=
    (castVal_single_symm hT.word_eq (transTy (HasWord64.ofNat (d := d) i))).symm.trans
      (congrArg (fun y => castVal (congrArg (fun t => [t]) hT.word_eq).symm
        (HVector.cons y .nil)) (hR.ofNat_trans i))
  toBool_enc b :=
    (congrArg (fun X => HasBoolBit.toBool (d := d') (HVector.head X))
      (castVal_single hT.bit_eq (transTy b))).trans (hR.toBool_trans b)

/-- **`mapM` at `toMulti L` against `map` at `L`.** Under the three leaves of
    `blockFundamental` and `RegionTransports`, for a renaming `ren` relating `W` to the
    transported `V`, the program `mapM` produces at `toMulti L` (with `ren` read through
    `mapCtx_eq_ctxFlat`) denotes, at every fuel, the results of `map L hT p hc ren` carried
    along `map_eq_ctxFlat`, for a program `p` without `call`. -/
theorem mapM_toMulti_denote [DialectDenote d] [DialectDenote d'] [CallDenote d]
    [CallDenote d'] (L : BlockLoweringData d d') (hNil : L.mapCtx [] = [])
    (hT : RegionTypes L) (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : BlockOpTransports L transTy mapVal) (hExt : MapValExtends L transTy mapVal)
    (hR : RegionTransports L hT transTy) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hc : p.callFree = true) {Δ : Ctxt d'}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ)
    (W : Valuation Δ) (hren : pullV ren W = mapVal V) :
    (mapM (L.toMulti hNil) (regionTypesM_toMulti L hNil hT) p
        (fun v => ren (castHom (L.mapCtx_eq_ctxFlat hNil Γ).symm v))).denote fuel W =
      ((map L hT p hc ren).denote fuel W).map (castVal (map_eq_ctxFlat L.mapTy ts)) := by
  have hrenM : pullV (fun v => ren (castHom (L.mapCtx_eq_ctxFlat hNil Γ).symm v)) W =
      flatVal (m := fun t => [L.mapTy t]) (fun x => L.encMulti transTy x) V := by
    rw [pullV_comp (fun v => castHom (L.mapCtx_eq_ctxFlat hNil Γ).symm v) (fun v => ren v),
      hren, pullV_castHom_symm, flatVal_encMulti L hNil transTy mapVal hExt]
  refine (mapM_denote (L.toMulti hNil) _ (fun x => L.encMulti transTy x) (fun _ => True)
      (L.toMulti_blockSquare hNil transTy mapVal hOp hExt (fun _ => True))
      (regionTransportsM_toMulti L hNil hT transTy hR) fuel p hc
      (covered_of_forall _ (fun _ => trivial) p) _ V W hrenM).trans ?_
  rw [map_denote L transTy mapVal hT (fun _ => True) hVar (fun e _ V => hOp e V) hExt hR fuel p
      hc (covered_of_forall _ (fun _ => trivial) p) ren V W hren, Option.map_map]
  congr 1
  funext R
  exact flatVal_encMulti_results L transTy R

end ToMultiMap

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
