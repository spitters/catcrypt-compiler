/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend

/-!
# Lifting a block lowering through the regions of `NFProg`

A block lowering `L : BlockLoweringData d d'` (`VIR/FieldDialectBlockDescent.lean`)
maps each expression of `d` to a straight-line block of `d'`. `NFProg.map L hT p ren`
lowers every let-binding of the structured program `p : NFProg d Γ ts` by `L`, splicing
its block in front of the lowered continuation, and maps the counted loops, branches and
exit-flag loops of `p` to the same constructors of `NFProg d'`, with their region
bodies lowered recursively. The lowering is renaming-accumulating, as
`BlockLoweringData.blockLowerComR`: `ren` renames `L.mapCtx Γ` into the target context.

The region constructors read the trip counter at `HasWord64.word` and the branch bit at
`HasBitType.bit`. `RegionTypes L` states that the type map of `L` sends the source's
word and bit types to the target's; `map` uses these two equations to retype the
counter and condition variables and the continue bit of an exit-flag loop body.

`map_denote` is the preservation theorem. Besides the three leaves of the block
lowering (`VarTransports`, the block leaf on `Good` expressions, `MapValExtends`), it
assumes `RegionTransports`: the value transport commutes with `HasWord64.toNat` (the
trip count is preserved), with `HasWord64.ofNat` (the trip index the body sees is
transported), and with `HasBoolBit.toBool` (a branch and an exit-flag loop take the same
decision).

## Main definitions

* `NFProg.spliceNF` — a straight-line block followed by a once-applied continuation.
* `NFProg.RegionTypes`, `NFProg.RegionTransports` — the conditions on the lowering at the
  trip counter and the branch bit.
* `NFProg.Covered` — every let-bound expression of a program satisfies a predicate.
* `NFProg.map` — the lowering of a structured program.

## Main results

* `NFProg.spliceNF_denote` — the denotation of `spliceNF`.
* `NFProg.map_denote` — under the leaves of the block lowering and `RegionTransports`,
  the lowered program denotes the transport of the source denotation, at every fuel.
* `NFProg.map_denote_id` — the same at the identity renaming and the transported
  valuation.
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

namespace NFProg

/-! ## 1. Casts along an equality of types -/

section Casts

variable {d : Dialect} [TyDenote d.Ty]

/-- A value carried along an equality of types. -/
def tyCast {a b : d.Ty} (h : a = b) (x : ⟦a⟧) : ⟦b⟧ := h ▸ x

/-- A variable carried along an equality of types. -/
def varTyCast {Γ : Ctxt d} {a b : d.Ty} (h : a = b) (v : Var Γ a) : Var Γ b := h ▸ v

/-- A variable carried along an equality of types reads the carried value. -/
theorem lookup_varTyCast {Γ : Ctxt d} {a b : d.Ty} (h : a = b) (v : Var Γ a)
    (V : Valuation Γ) : (varTyCast h v).lookup V = tyCast h (v.lookup V) := by
  subst h
  rfl

/-- A valuation that reads at each variable what a valuation of an equal context reads
    at the carried variable is the carried valuation. -/
theorem eq_cast_of_lookup {Γ₁ Γ₂ : Ctxt d} (h : Γ₁ = Γ₂) (P : Valuation Γ₁)
    (V₂ : Valuation Γ₂)
    (hP : ∀ {s : d.Ty} (v : Var Γ₁ s), v.lookup P = (castHom h v).lookup V₂) :
    P = h ▸ V₂ := by
  subst h
  exact valuation_ext _ _ (fun v => hP v)

end Casts

/-! ## 2. Splicing a block into a structured program -/

section Splice

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **A block followed by a continuation.** `spliceNF blk k` keeps the bindings of the
    straight-line block `blk` and, at its return variable `res`, continues with
    `k ren res`, where `ren` renames the context of `blk` into the extended context. -/
def spliceNF {ts : List d.Ty} : {Δ : Ctxt d} → {a : d.Ty} → Com d Δ a →
    ({Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → NFProg d Δ' ts) → NFProg d Δ ts
  | _, _, .ret v, k => k (fun x => x) v
  | _, _, .var e blk, k => .var e (spliceNF blk (fun ren res => k (fun x => ren (.there x)) res))

/-- **Denotation of `spliceNF`.** If `k ren res` denotes `G` whenever `ren` preserves
    lookups back to `W` and `res` holds the value of the block, the spliced program
    denotes `G`. -/
theorem spliceNF_denote [DialectDenote d] (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {a : d.Ty} → (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → NFProg d Δ' ts) →
    (W : Valuation Δ) → (G : Option (Valuation ts)) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (W' : Valuation Δ'),
        (∀ {s : d.Ty} (v : Var Δ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W →
        (k ren res).denote fuel W' = G) →
    (spliceNF blk k).denote fuel W = G
  | _, _, .ret v, k, W, G, hk => hk (fun x => x) v W (fun _ => rfl) rfl
  | _, _, .var e blk, k, W, G, hk => by
      simp only [spliceNF, denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      exact spliceNF_denote fuel blk _ (W.extend (e.denote W)) G
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2)

/-- A program with its first result type carried along an equality of types. -/
def castRetHead {Δ : Ctxt d} {a b : d.Ty} {ts : List d.Ty} (h : a = b)
    (p : NFProg d Δ (a :: ts)) : NFProg d Δ (b :: ts) := h ▸ p

/-- A program with its first result type carried denotes its results with the first
    one carried. -/
theorem denote_castRetHead [DialectDenoteM d Option] {Δ : Ctxt d} {a b : d.Ty}
    {ts : List d.Ty} (h : a = b) (p : NFProg d Δ (a :: ts)) (fuel : Nat)
    (W : Valuation Δ) :
    (castRetHead h p).denote fuel W =
      (p.denote fuel W).map (fun r => .cons (tyCast h r.head) r.tail) := by
  subst h
  show p.denote fuel W = _
  cases p.denote fuel W with
  | none => rfl
  | some r =>
      cases r
      rfl

/-- The programs whose let-bound expressions all satisfy `Good`, in every region. -/
def Covered (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var e k => Good e ∧ Covered Good k
  | _, _, .forLoop _ _ body k => Covered Good body ∧ Covered Good k
  | _, _, .ifThenElse _ thn els k => Covered Good thn ∧ Covered Good els ∧ Covered Good k
  | _, _, .whileLoop _ body k => Covered Good body ∧ Covered Good k

/-- Under a predicate that holds of every expression, every program is covered. -/
theorem covered_of_forall (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hG : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) : p.Covered Good := by
  induction p with
  | ret => trivial
  | var e k ih => exact ⟨hG e, ih⟩
  | forLoop _ _ _ _ ihb ihk => exact ⟨ihb, ihk⟩
  | ifThenElse _ _ _ _ iht ihe ihk => exact ⟨iht, ihe, ihk⟩
  | whileLoop _ _ _ ihb ihk => exact ⟨ihb, ihk⟩

end Splice

/-! ## 3. The lowering -/

section Map

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The type map of `L` sends the trip-counter type and the bit type of `d` to those of
    `d'`. -/
structure RegionTypes (L : BlockLoweringData d d') : Prop where
  /-- The trip-counter type maps to the trip-counter type. -/
  word_eq : L.mapTy (HasWord64.word (d := d)) = HasWord64.word (d := d')
  /-- The bit type maps to the bit type. -/
  bit_eq : L.mapTy (HasBitType.bit (d := d)) = HasBitType.bit (d := d')

/-- The renaming of `L.mapCtx (t :: Γ)` into `t' :: Δ` that sends the head to the head
    and the tail through `ren`, for `L.mapTy t = t'`. -/
def liftTo (L : BlockLoweringData d d') {Γ : Ctxt d} {Δ : Ctxt d'} {t : d.Ty}
    {t' : d'.Ty} (h : L.mapTy t = t') (ren : Ctxt.Hom (L.mapCtx Γ) Δ) :
    Ctxt.Hom (L.mapCtx (t :: Γ)) (t' :: Δ) :=
  L.bodyHom ren (fun x => .there x) (varTyCast h.symm .here)

/-- The renaming of `L.mapCtx (cs ++ Γ)` into `cs.map L.mapTy ++ Δ` that sends the
    prefix to the prefix and the rest through `ren`. -/
def appHom (L : BlockLoweringData d d') {Γ : Ctxt d} {Δ : Ctxt d'} :
    (cs : List d.Ty) → Ctxt.Hom (L.mapCtx Γ) Δ →
    Ctxt.Hom (L.mapCtx (cs ++ Γ)) (cs.map L.mapTy ++ Δ)
  | [], ren => ren
  | _ :: cs, ren => liftTo L rfl (appHom L cs ren)

/-- An argument vector of variables mapped by `L.mapVar` and renamed by `ren`. -/
def mapArgs (L : BlockLoweringData d d') {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) :
    {ts : List d.Ty} → HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var Δ t) (ts.map L.mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (ren (L.mapVar v)) (mapArgs L ren vs)

/-- **The lowering of a structured program along a block lowering.** A let-binding
    becomes the block `L` gives its expression, renamed by `ren` and spliced in front of
    the lowered continuation; a return, a counted loop, a branch and an exit-flag loop
    become the same constructor of `NFProg d'`, with their variables mapped and renamed
    and their regions lowered. The counter, the condition and the continue bit are
    retyped along `RegionTypes`. -/
def map (L : BlockLoweringData d d') (hT : RegionTypes L) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → {Δ : Ctxt d'} →
    Ctxt.Hom (L.mapCtx Γ) Δ → NFProg d' Δ (ts.map L.mapTy)
  | _, _, .ret vs, _, ren => .ret (mapArgs L ren vs)
  | _, _, .var e k, _, ren =>
      spliceNF (Com.rename ren (L.lowerExprBlock e))
        (fun ren' res => map L hT k (L.bodyHom ren ren' res))
  | _, _, .forLoop (cs := cs) count inits body k, _, ren =>
      .forLoop (varTyCast hT.word_eq (ren (L.mapVar count))) (mapArgs L ren inits)
        (map L hT body (appHom L cs (liftTo L hT.word_eq ren)))
        (map L hT k (appHom L cs ren))
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ren =>
      .ifThenElse (varTyCast hT.bit_eq (ren (L.mapVar cond))) (map L hT thn ren)
        (map L hT els ren) (map L hT k (appHom L rs ren))
  | _, _, .whileLoop (cs := cs) inits body k, _, ren =>
      .whileLoop (mapArgs L ren inits)
        (castRetHead hT.bit_eq (map L hT body (appHom L cs ren)))
        (map L hT k (appHom L cs ren))

/-! ## 4. Preservation -/

variable [DialectDenote d] [DialectDenote d']

/-- The value transport of `L` commutes with the readings of the trip counter and the
    bit: `toNat` (the trip count), `ofNat` (the trip index) and `toBool` (the branch
    and exit decisions). -/
structure RegionTransports (L : BlockLoweringData d d') (hT : RegionTypes L)
    (transTy : TransTy L) : Prop where
  /-- A transported counter value denotes the same trip count. -/
  toNat_trans : ∀ x : ⟦HasWord64.word (d := d)⟧,
    HasWord64.toNat (d := d') (tyCast hT.word_eq (transTy x)) = HasWord64.toNat (d := d) x
  /-- The transported trip index is the trip index. -/
  ofNat_trans : ∀ i : Nat,
    tyCast hT.word_eq (transTy (HasWord64.ofNat (d := d) i)) = HasWord64.ofNat (d := d') i
  /-- A transported bit reads as the same `Bool`. -/
  toBool_trans : ∀ b : ⟦HasBitType.bit (d := d)⟧,
    HasBoolBit.toBool (d := d') (tyCast hT.bit_eq (transTy b)) = HasBoolBit.toBool (d := d) b

variable (L : BlockLoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- The renaming `L.bodyHom ren ren' res` relates the valuations that `ren`, `ren'` and
    `res` relate, extended by a transported value. -/
theorem pullV_bodyHom (hExt : MapValExtends L transTy mapVal) {Γ : Ctxt d} {u : d.Ty}
    {Δ Δ' : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (ren' : Ctxt.Hom Δ Δ')
    (res : Var Δ' (L.mapTy u)) (V : Valuation Γ) (x : ⟦u⟧) (W : Valuation Δ)
    (W' : Valuation Δ') (hren : pullV ren W = mapVal V)
    (h1 : ∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W)
    (h2 : res.lookup W' = transTy x) :
    pullV (L.bodyHom ren ren' res) W' = mapVal (V.extend x) := by
  refine Eq.trans ?_ (hExt V x).symm
  refine eq_cast_of_lookup (L.mapCtx_cons u Γ) _ _ (fun v => ?_)
  rw [lookup_pullV]
  unfold BlockLoweringData.bodyHom
  generalize castHom (L.mapCtx_cons u Γ) v = w
  cases w with
  | here => exact h2
  | there w =>
      show (ren' (ren w)).lookup W' = w.lookup (mapVal V)
      rw [h1, ← hren, lookup_pullV]

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- `liftTo` relates the valuations `ren` relates, extended by a transported value. -/
theorem pullV_liftTo (hExt : MapValExtends L transTy mapVal) {Γ : Ctxt d} {Δ : Ctxt d'}
    {t : d.Ty} {t' : d'.Ty} (h : L.mapTy t = t') (ren : Ctxt.Hom (L.mapCtx Γ) Δ)
    (V : Valuation Γ) (W : Valuation Δ) (x : ⟦t⟧) (y : ⟦t'⟧)
    (hren : pullV ren W = mapVal V) (hy : tyCast h (transTy x) = y) :
    pullV (liftTo L h ren) (.cons y W) = mapVal (V.extend x) := by
  subst h hy
  exact pullV_bodyHom L transTy mapVal hExt ren _ _ V x W _ hren (fun _ => rfl)
    (lookup_varTyCast _ _ _)

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- `appHom` relates the valuations `ren` relates, prefixed by a transported tuple. -/
theorem pullV_appHom (hExt : MapValExtends L transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = mapVal V) :
    (cs : List d.Ty) → (acc : Valuation cs) →
    pullV (appHom L cs ren) (hvAppend (transArgs L.mapTy transTy acc) W) =
      mapVal (hvAppend acc V)
  | [], .nil => hren
  | _ :: cs, .cons a acc =>
      pullV_liftTo L transTy mapVal hExt rfl (appHom L cs ren) (hvAppend acc V)
        (hvAppend (transArgs L.mapTy transTy acc) W) a _
        (pullV_appHom hExt ren V W hren cs acc) rfl

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- The mapped and renamed argument variables read the transported argument values. -/
theorem lookupArgs_mapArgs (hVar : VarTransports L transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = mapVal V) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    Expr.lookupArgs (mapArgs L ren vs) W = transArgs L.mapTy transTy (Expr.lookupArgs vs V)
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupArgs_mapArgs hVar ren V W hren vs, ← lookup_pullV, hren, hVar]

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  [DialectDenote d] [DialectDenote d'] in
/-- A fold in `Option` whose step commutes with `T` commutes with `T`. -/
theorem foldlM_option_map {α α' β : Type} (f : α → β → Option α) (g : α' → β → Option α')
    (T : α → α') (h : ∀ a i, g (T a) i = (f a i).map T) :
    ∀ (l : List β) (a : α), l.foldlM g (T a) = (l.foldlM f a).map T
  | [], _ => rfl
  | i :: l, a => by
      rw [List.foldlM_cons, List.foldlM_cons, h]
      cases f a i with
      | none => rfl
      | some b => exact foldlM_option_map f g T h l b

omit [DialectSignature d] [HasWord64 d] [DialectSignature d'] [HasWord64 d']
  [DialectDenote d] [DialectDenote d'] in
/-- An exit-flag iteration whose step commutes with `T` (and reads transported bits as
    the source bits) commutes with `T`. -/
theorem whileIter_map {cs : List d.Ty} {cs' : List d'.Ty}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs)))
    (step' : Valuation cs' → Option (Valuation (HasBitType.bit (d := d') :: cs')))
    (T : Valuation cs → Valuation cs')
    (Tb : ⟦HasBitType.bit (d := d)⟧ → ⟦HasBitType.bit (d := d')⟧)
    (hb : ∀ b, HasBoolBit.toBool (d := d') (Tb b) = HasBoolBit.toBool (d := d) b)
    (hs : ∀ a, step' (T a) = (step a).map (fun r => .cons (Tb r.head) (T r.tail))) :
    ∀ (n : Nat) (a : Valuation cs), whileIter step' n (T a) = (whileIter step n a).map T
  | 0, _ => rfl
  | n + 1, a => by
      simp only [whileIter, hs]
      cases step a with
      | none => rfl
      | some r =>
          cases r with
          | cons b r => ?_
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, HVector.head,
            HVector.tail, hb]
          cases HasBoolBit.toBool (d := d) b with
          | true => exact whileIter_map step step' T Tb hb hs n _
          | false => rfl

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
  [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']
  [DialectDenote d] [DialectDenote d'] in
/-- A bind after a map by `T`, whose continuation sends `T a` to the map by `T₂` of
    `G a`, is the map by `T₂` of the bind with `G`. -/
theorem bind_map_comm {α α' β β' : Type} (o : Option α) (T : α → α') (T₂ : β → β')
    (F : α' → Option β') (G : α → Option β) (h : ∀ a, F (T a) = (G a).map T₂) :
    (o.map T >>= F) = (o >>= G).map T₂ := by
  cases o with
  | none => rfl
  | some a => exact h a

/-- **Preservation.** Under the variable leaf, the block leaf on `Good` expressions and
    the binding-threading leaf of `L`, and `RegionTransports`, a `Good`-covered program
    lowered by `map` at a renaming `ren` relating `W` to the transported `V` denotes,
    at every fuel, the transport of the source denotation. -/
theorem map_denote (hT : RegionTypes L)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : VarTransports L transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ V : Valuation Γ, (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V))
    (hExt : MapValExtends L transTy mapVal) (hR : RegionTransports L hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      pullV ren W = mapVal V →
      (map L hT p ren).denote fuel W =
        (p.denote fuel V).map (transArgs L.mapTy transTy) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren
      show some _ = some _
      rw [lookupArgs_mapArgs L transTy mapVal hVar ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren
      obtain ⟨hg, hk⟩ := hp
      simp only [map, denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      refine spliceNF_denote fuel _ _ W _ (fun ren' res W' h1 h2 => ?_)
      refine ih hk _ (V.extend (e.denote V)) W' ?_
      refine pullV_bodyHom L transTy mapVal hExt ren ren' res V _ W W' hren h1 ?_
      rw [h2, FieldDialectBlockDescent.Com.denote_rename, hren, hBlk e hg V]
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren
      obtain ⟨hb, hk⟩ := hp
      simp only [map, denote]
      rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toNat_trans,
        lookupArgs_mapArgs L transTy mapVal hVar ren V W hren]
      rw [foldlM_option_map _ _ (transArgs L.mapTy transTy) (fun acc i => by
        rw [← hR.ofNat_trans i]
        exact ihb hb _ _ _ (pullV_appHom L transTy mapVal hExt _ _ _
          (pullV_liftTo L transTy mapVal hExt _ ren V W _ _ hren rfl) _ acc))]
      exact bind_map_comm _ _ _ _ _
        (fun acc => ihk hk _ _ _ (pullV_appHom L transTy mapVal hExt ren V W hren _ acc))
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren
      obtain ⟨ht, he, hk⟩ := hp
      simp only [map, denote]
      rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toBool_trans]
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then (map L hT thn ren).denote fuel W else (map L hT els ren).denote fuel W) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
            else els.denote fuel V).map (transArgs L.mapTy transTy) := by
        split
        · exact iht ht ren V W hren
        · exact ihe he ren V W hren
      rw [harm]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hk _ _ _ (pullV_appHom L transTy mapVal hExt ren V W hren _ r))
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren
      obtain ⟨hb, hk⟩ := hp
      simp only [map, denote]
      rw [lookupArgs_mapArgs L transTy mapVal hVar ren V W hren,
        whileIter_map (fun acc => body.denote fuel (hvAppend acc V)) _
          (transArgs L.mapTy transTy) (fun b => tyCast hT.bit_eq (transTy b))
          hR.toBool_trans (fun a => by
            rw [denote_castRetHead,
              ihb hb _ _ _ (pullV_appHom L transTy mapVal hExt ren V W hren _ a),
              Option.map_map]
            congr 1
            funext r
            cases r
            rfl)]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hk _ _ _ (pullV_appHom L transTy mapVal hExt ren V W hren _ r))

/-- **Preservation at the identity renaming.** A `Good`-covered program lowered by
    `map` into `L.mapCtx Γ` denotes, on the transported valuation and at every fuel, the
    transport of the source denotation. -/
theorem map_denote_id (hT : RegionTypes L)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : VarTransports L transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ V : Valuation Γ, (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V))
    (hExt : MapValExtends L transTy mapVal) (hR : RegionTransports L hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good)
    (V : Valuation Γ) :
    (map L hT p (fun v => v)).denote fuel (mapVal V) =
      (p.denote fuel V).map (transArgs L.mapTy transTy) :=
  map_denote L transTy mapVal hT Good hVar hBlk hExt hR fuel p hp _ V (mapVal V)
    (FieldDialectBlockDescent.pullV_id _)

/-- **Preservation for a lowering whose block leaf holds of every expression.** Every
    program lowered by `map` into `L.mapCtx Γ` denotes, on the transported valuation and
    at every fuel, the transport of the source denotation. -/
theorem map_denote_of_blockOpTransports (hT : RegionTypes L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : FieldDialectBlockDescent.BlockOpTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal) (hR : RegionTransports L hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) :
    (map L hT p (fun v => v)).denote fuel (mapVal V) =
      (p.denote fuel V).map (transArgs L.mapTy transTy) :=
  map_denote_id L transTy mapVal hT (fun _ => True) hVar (fun e _ V => hOp e V) hExt hR
    fuel p (covered_of_forall _ (fun _ => trivial) p) V

end Map

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
