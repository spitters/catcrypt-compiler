/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend

/-!
# Lifting a block lowering through the regions of `NFProg`

A partial block lowering `P : PartialBlockLowering d d'` maps each expression of `d`
either to a straight-line block of `d'` or to `none`. `NFProg.map? P hT p ren` lowers
every let-binding of the structured program `p : NFProg d Γ ts` by `P`, splicing its
block in front of the lowered continuation, and maps the counted loops, branches and
exit-flag loops of `p` to the same constructors of `NFProg d'`, with their region
bodies lowered recursively; it is `none` when `P` refuses a let-bound expression. The
lowering is renaming-accumulating, as `BlockLoweringData.blockLowerComR`: `ren` renames
`P.mapCtx Γ` into the target context.

A total block lowering `L : BlockLoweringData d d'` is the partial lowering
`L.toPartial` that refuses nothing. `NFProg.map L hT p ren` is the value of
`map? L.toPartial hT p ren`, which is always `some` (`isSome_map?_toPartial`).

The region constructors read the trip counter at `HasWord64.word` and the branch bit at
`HasBitType.bit`. `RegionTypes P` states that the type map of `P` sends the source's
word and bit types to the target's; `map?` uses these two equations to retype the
counter and condition variables and the continue bit of an exit-flag loop body.

`map?_denote` is the preservation theorem. Besides the three leaves of the block
lowering (`VarTransports`, the block leaf on the `Good` expressions the lowering
accepts, `MapValExtends`), it assumes `RegionTransports`: the value transport commutes
with `HasWord64.toNat` (the trip count is preserved), with `HasWord64.ofNat` (the trip
index the body sees is transported), and with `HasBoolBit.toBool` (a branch and an
exit-flag loop take the same decision). `map_denote` is its instance at a total
lowering.

## Main definitions

* `PartialBlockLowering` — a block lowering whose per-expression block is `Option`-valued.
* `FieldDialectBlockDescent.BlockLoweringData.toPartial` — a total block lowering as a
  partial one.
* `NFProg.spliceNF?` — a straight-line block followed by a once-applied partial
  continuation.
* `PartialBlockLowering.RegionTypes`, `PartialBlockLowering.RegionTransports` — the
  conditions on the lowering at the trip counter and the branch bit.
* `NFProg.Covered` — every let-bound expression of a program satisfies a predicate.
* `NFProg.map?` — the partial lowering of a structured program.
* `NFProg.map` — the lowering along a total block lowering.

## Main results

* `NFProg.spliceNF?_denote` — the denotation of `spliceNF?`.
* `NFProg.map?_denote` — under the leaves of the block lowering and `RegionTransports`,
  a program `map?` returns denotes the transport of the source denotation, at every
  fuel.
* `NFProg.map_denote`, `NFProg.map_denote_id`, `NFProg.map_denote_of_blockOpTransports`
  — the same for a total lowering.
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

/-- **A block followed by a partial continuation.** `spliceNF? blk k` keeps the bindings
    of the straight-line block `blk` and, at its return variable `res`, continues with
    `k ren res`, where `ren` renames the context of `blk` into the extended context; it
    is `none` when the continuation is. -/
def spliceNF? {ts : List d.Ty} : {Δ : Ctxt d} → {a : d.Ty} → Com d Δ a →
    ({Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts)) →
    Option (NFProg d Δ ts)
  | _, _, .ret v, k => k (fun x => x) v
  | _, _, .var e blk, k =>
      (spliceNF? blk (fun ren res => k (fun x => ren (.there x)) res)).map (.var e)

/-- A continuation that is `some` everywhere, spliced after a block, is `some`. -/
theorem isSome_spliceNF? {ts : List d.Ty} : {Δ : Ctxt d} → {a : d.Ty} →
    (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts)) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a), (k ren res).isSome) →
    (spliceNF? blk k).isSome
  | _, _, .ret v, _, hk => hk _ v
  | _, _, .var _ blk, k, hk => by
      rw [spliceNF?, Option.isSome_map]
      exact isSome_spliceNF? blk _ (fun ren res => hk _ res)

/-- **Denotation of `spliceNF?`.** If every program `k ren res` returns denotes `G`
    whenever `ren` preserves lookups back to `W` and `res` holds the value of the block,
    every program the splice returns denotes `G`. -/
theorem spliceNF?_denote [DialectDenote d] (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {a : d.Ty} → (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts)) →
    (W : Valuation Δ) → (G : Option (Valuation ts)) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (W' : Valuation Δ'),
        (∀ {s : d.Ty} (v : Var Δ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W →
        ∀ q, k ren res = some q → q.denote fuel W' = G) →
    ∀ q, spliceNF? blk k = some q → q.denote fuel W = G
  | _, _, .ret v, k, W, G, hk => hk (fun x => x) v W (fun _ => rfl) rfl
  | _, _, .var e blk, k, W, G, hk => by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      exact spliceNF?_denote fuel blk _ (W.extend (e.denote W)) G
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2) q' hq'

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

end NFProg

/-! ## 3. Partial block lowerings -/

/-- **A partial block lowering** from `d` to `d'`: the type, context and variable maps of
    a block lowering, and for each expression of `d` either a straight-line block of `d'`
    returning the mapped type or `none`. -/
structure PartialBlockLowering (d d' : Dialect) [DialectSignature d]
    [DialectSignature d'] where
  /-- Type map. -/
  mapTy : d.Ty → d'.Ty
  /-- Context map. -/
  mapCtx : Ctxt d → Ctxt d'
  /-- `cons`-compatibility of the context map. -/
  mapCtx_cons : ∀ (t : d.Ty) (Γ : Ctxt d), mapCtx (t :: Γ) = mapTy t :: mapCtx Γ
  /-- Variable transport. -/
  mapVar : ∀ {Γ : Ctxt d} {t : d.Ty}, Var Γ t → Var (mapCtx Γ) (mapTy t)
  /-- The block of an expression, or `none` where the lowering refuses it. -/
  lowerExprBlock? : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t →
    Option (Com d' (mapCtx Γ) (mapTy t))

/-- A total block lowering as the partial block lowering that refuses no expression. -/
def FieldDialectBlockDescent.BlockLoweringData.toPartial {d d' : Dialect}
    [DialectSignature d] [DialectSignature d'] (L : BlockLoweringData d d') :
    PartialBlockLowering d d' where
  mapTy := L.mapTy
  mapCtx := L.mapCtx
  mapCtx_cons := L.mapCtx_cons
  mapVar := L.mapVar
  lowerExprBlock? e := some (L.lowerExprBlock e)

namespace PartialBlockLowering

section Defs

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-- The renaming handed to the lowered body of a let-binding of type `u`: the head of
    `P.mapCtx (u :: Γ)` goes to the block's result `res`, the tail through `ren` and then
    `ren'`. -/
def bodyHom (P : PartialBlockLowering d d') {Γ : Ctxt d} {u : d.Ty} {Δ Δ' : Ctxt d'}
    (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' (P.mapTy u)) :
    Ctxt.Hom (P.mapCtx (u :: Γ)) Δ' :=
  fun v => consHom (fun w => ren' (ren w)) res (castHom (P.mapCtx_cons u Γ) v)

variable [TyDenote d.Ty] [TyDenote d'.Ty]

/-- Value transport carried by a partial block lowering. -/
abbrev TransTy (P : PartialBlockLowering d d') := ∀ {t : d.Ty}, ⟦t⟧ → ⟦P.mapTy t⟧

/-- Valuation transport carried by a partial block lowering. -/
abbrev MapVal (P : PartialBlockLowering d d') :=
  ∀ {Γ : Ctxt d}, Ctxt.Valuation Γ → Ctxt.Valuation (P.mapCtx Γ)

/-- Variable-transport leaf coherence. -/
def VarTransports (P : PartialBlockLowering d d') (transTy : P.TransTy)
    (mapVal : P.MapVal) : Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ),
    (P.mapVar v).lookup (mapVal V) = transTy (v.lookup V)

/-- Binding-threading coherence. -/
def MapValExtends (P : PartialBlockLowering d d') (transTy : P.TransTy)
    (mapVal : P.MapVal) : Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (V : Ctxt.Valuation Γ) (x : ⟦t⟧),
    mapVal (Ctxt.Valuation.extend V x)
      = (P.mapCtx_cons t Γ ▸ Ctxt.Valuation.extend (mapVal V) (transTy x))

end Defs

section Regions

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The type map of `P` sends the trip-counter type and the bit type of `d` to those of
    `d'`. -/
structure RegionTypes (P : PartialBlockLowering d d') : Prop where
  /-- The trip-counter type maps to the trip-counter type. -/
  word_eq : P.mapTy (HasWord64.word (d := d)) = HasWord64.word (d := d')
  /-- The bit type maps to the bit type. -/
  bit_eq : P.mapTy (HasBitType.bit (d := d)) = HasBitType.bit (d := d')

/-- The value transport of `P` commutes with the readings of the trip counter and the
    bit: `toNat` (the trip count), `ofNat` (the trip index) and `toBool` (the branch
    and exit decisions). -/
structure RegionTransports (P : PartialBlockLowering d d') (hT : P.RegionTypes)
    (transTy : P.TransTy) : Prop where
  /-- A transported counter value denotes the same trip count. -/
  toNat_trans : ∀ x : ⟦HasWord64.word (d := d)⟧,
    HasWord64.toNat (d := d') (NFProg.tyCast hT.word_eq (transTy x)) =
      HasWord64.toNat (d := d) x
  /-- The transported trip index is the trip index. -/
  ofNat_trans : ∀ i : Nat,
    NFProg.tyCast hT.word_eq (transTy (HasWord64.ofNat (d := d) i)) =
      HasWord64.ofNat (d := d') i
  /-- A transported bit reads as the same `Bool`. -/
  toBool_trans : ∀ b : ⟦HasBitType.bit (d := d)⟧,
    HasBoolBit.toBool (d := d') (NFProg.tyCast hT.bit_eq (transTy b)) =
      HasBoolBit.toBool (d := d) b

end Regions

end PartialBlockLowering

namespace NFProg

/-! ## 4. The lowering -/

section Map

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- The type map of the total lowering `L` sends the trip-counter type and the bit type
    of `d` to those of `d'`. -/
abbrev RegionTypes (L : BlockLoweringData d d') : Prop :=
  L.toPartial.RegionTypes

/-- The renaming of `P.mapCtx (t :: Γ)` into `t' :: Δ` that sends the head to the head
    and the tail through `ren`, for `P.mapTy t = t'`. -/
def liftTo (P : PartialBlockLowering d d') {Γ : Ctxt d} {Δ : Ctxt d'} {t : d.Ty}
    {t' : d'.Ty} (h : P.mapTy t = t') (ren : Ctxt.Hom (P.mapCtx Γ) Δ) :
    Ctxt.Hom (P.mapCtx (t :: Γ)) (t' :: Δ) :=
  P.bodyHom ren (fun x => .there x) (varTyCast h.symm .here)

/-- The renaming of `P.mapCtx (cs ++ Γ)` into `cs.map P.mapTy ++ Δ` that sends the
    prefix to the prefix and the rest through `ren`. -/
def appHom (P : PartialBlockLowering d d') {Γ : Ctxt d} {Δ : Ctxt d'} :
    (cs : List d.Ty) → Ctxt.Hom (P.mapCtx Γ) Δ →
    Ctxt.Hom (P.mapCtx (cs ++ Γ)) (cs.map P.mapTy ++ Δ)
  | [], ren => ren
  | _ :: cs, ren => liftTo P rfl (appHom P cs ren)

/-- An argument vector of variables mapped by `P.mapVar` and renamed by `ren`. -/
def mapArgs (P : PartialBlockLowering d d') {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (P.mapCtx Γ) Δ) :
    {ts : List d.Ty} → HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var Δ t) (ts.map P.mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (ren (P.mapVar v)) (mapArgs P ren vs)

/-- **The lowering of a structured program along a partial block lowering.** A
    let-binding becomes the block `P` gives its expression, renamed by `ren` and spliced
    in front of the lowered continuation; a return, a counted loop, a branch and an
    exit-flag loop become the same constructor of `NFProg d'`, with their variables
    mapped and renamed and their regions lowered. The counter, the condition and the
    continue bit are retyped along `RegionTypes`. The result is `none` when `P` refuses
    a let-bound expression of the program or of one of its regions. -/
def map? (P : PartialBlockLowering d d') (hT : P.RegionTypes) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → {Δ : Ctxt d'} →
    Ctxt.Hom (P.mapCtx Γ) Δ → Option (NFProg d' Δ (ts.map P.mapTy))
  | _, _, .ret vs, _, ren => some (.ret (mapArgs P ren vs))
  | _, _, .var e k, _, ren =>
      (P.lowerExprBlock? e).bind fun blk =>
        spliceNF? (Com.rename ren blk)
          (fun ren' res => map? P hT k (P.bodyHom ren ren' res))
  | _, _, .forLoop (cs := cs) count inits body k, _, ren =>
      (map? P hT body (appHom P cs (liftTo P hT.word_eq ren))).bind fun body' =>
        (map? P hT k (appHom P cs ren)).map fun k' =>
          .forLoop (varTyCast hT.word_eq (ren (P.mapVar count))) (mapArgs P ren inits)
            body' k'
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ren =>
      (map? P hT thn ren).bind fun thn' =>
        (map? P hT els ren).bind fun els' =>
          (map? P hT k (appHom P rs ren)).map fun k' =>
            .ifThenElse (varTyCast hT.bit_eq (ren (P.mapVar cond))) thn' els' k'
  | _, _, .whileLoop (cs := cs) inits body k, _, ren =>
      (map? P hT body (appHom P cs ren)).bind fun body' =>
        (map? P hT k (appHom P cs ren)).map fun k' =>
          .whileLoop (mapArgs P ren inits) (castRetHead hT.bit_eq body') k'

/-- Along a total block lowering, `map?` is `some` on every program. -/
theorem isSome_map?_toPartial (L : BlockLoweringData d d') (hT : RegionTypes L)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (L.toPartial.mapCtx Γ) Δ),
      (map? L.toPartial hT p ren).isSome := by
  induction p with
  | ret => intro _ _; rfl
  | var e k ih =>
      intro _ ren
      exact isSome_spliceNF? _ _ (fun _ _ => ih _)
  | forLoop _ _ _ _ ihb ihk =>
      intro _ ren
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ihb (appHom _ _ (liftTo _ hT.word_eq ren)))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk (appHom _ _ ren))
      simp only [map?, hb, hk, Option.bind_some, Option.map_some, Option.isSome_some]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro _ ren
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (iht ren)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ihe ren)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk (appHom _ _ ren))
      simp only [map?, ha, hb, hk, Option.bind_some, Option.map_some, Option.isSome_some]
  | whileLoop _ _ _ ihb ihk =>
      intro _ ren
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ihb (appHom _ _ ren))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk (appHom _ _ ren))
      simp only [map?, hb, hk, Option.bind_some, Option.map_some, Option.isSome_some]

/-- **The lowering of a structured program along a total block lowering**: the value of
    `map?` at `L.toPartial`. -/
def map (L : BlockLoweringData d d') (hT : RegionTypes L) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) :
    NFProg d' Δ (ts.map L.mapTy) :=
  (map? L.toPartial hT p ren).get (isSome_map?_toPartial L hT p ren)

/-- `map?` along a total block lowering returns `map`. -/
theorem map?_toPartial (L : BlockLoweringData d d') (hT : RegionTypes L) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) {Δ : Ctxt d'}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) :
    map? L.toPartial hT p ren = some (map L hT p ren) :=
  (Option.some_get _).symm

/-! ## 5. Preservation -/

variable [DialectDenote d] [DialectDenote d']

/-- The value transport of the total lowering `L` commutes with the readings of the trip
    counter and the bit. -/
abbrev RegionTransports (L : BlockLoweringData d d') (hT : RegionTypes L)
    (transTy : TransTy L) : Prop :=
  L.toPartial.RegionTransports hT transTy

variable (P : PartialBlockLowering d d') (transTy : P.TransTy) (mapVal : P.MapVal)

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- The renaming `P.bodyHom ren ren' res` relates the valuations that `ren`, `ren'` and
    `res` relate, extended by a transported value. -/
theorem pullV_bodyHom (hExt : P.MapValExtends transTy mapVal) {Γ : Ctxt d} {u : d.Ty}
    {Δ Δ' : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (ren' : Ctxt.Hom Δ Δ')
    (res : Var Δ' (P.mapTy u)) (V : Valuation Γ) (x : ⟦u⟧) (W : Valuation Δ)
    (W' : Valuation Δ') (hren : pullV ren W = mapVal V)
    (h1 : ∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W)
    (h2 : res.lookup W' = transTy x) :
    pullV (P.bodyHom ren ren' res) W' = mapVal (V.extend x) := by
  refine Eq.trans ?_ (hExt V x).symm
  refine eq_cast_of_lookup (P.mapCtx_cons u Γ) _ _ (fun v => ?_)
  rw [lookup_pullV]
  unfold PartialBlockLowering.bodyHom
  generalize castHom (P.mapCtx_cons u Γ) v = w
  cases w with
  | here => exact h2
  | there w =>
      show (ren' (ren w)).lookup W' = w.lookup (mapVal V)
      rw [h1, ← hren, lookup_pullV]

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- `liftTo` relates the valuations `ren` relates, extended by a transported value. -/
theorem pullV_liftTo (hExt : P.MapValExtends transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} {t : d.Ty} {t' : d'.Ty} (h : P.mapTy t = t')
    (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ) (x : ⟦t⟧)
    (y : ⟦t'⟧) (hren : pullV ren W = mapVal V) (hy : tyCast h (transTy x) = y) :
    pullV (liftTo P h ren) (.cons y W) = mapVal (V.extend x) := by
  subst h hy
  exact pullV_bodyHom P transTy mapVal hExt ren _ _ V x W _ hren (fun _ => rfl)
    (lookup_varTyCast _ _ _)

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- `appHom` relates the valuations `ren` relates, prefixed by a transported tuple. -/
theorem pullV_appHom (hExt : P.MapValExtends transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = mapVal V) :
    (cs : List d.Ty) → (acc : Valuation cs) →
    pullV (appHom P cs ren) (hvAppend (transArgs P.mapTy transTy acc) W) =
      mapVal (hvAppend acc V)
  | [], .nil => hren
  | _ :: cs, .cons a acc =>
      pullV_liftTo P transTy mapVal hExt rfl (appHom P cs ren) (hvAppend acc V)
        (hvAppend (transArgs P.mapTy transTy acc) W) a _
        (pullV_appHom hExt ren V W hren cs acc) rfl

omit [HasWord64 d] [HasBoolBit d] [HasWord64 d'] [HasBoolBit d'] [DialectDenote d] in
/-- The mapped and renamed argument variables read the transported argument values. -/
theorem lookupArgs_mapArgs (hVar : P.VarTransports transTy mapVal) {Γ : Ctxt d}
    {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ)
    (hren : pullV ren W = mapVal V) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    Expr.lookupArgs (mapArgs P ren vs) W = transArgs P.mapTy transTy (Expr.lookupArgs vs V)
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
    ∀ (l : List β) (a : α), l.foldlM g (T a) = (l.foldlM f a).map T :=
  fun l a => (rel_graph_iff.1 (foldlM_rel l (fun i _ a _ e => by
    subst e; rw [h]; exact rel_map_of (fun _ => rfl) _) a _ rfl)).symm

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
    ∀ (n : Nat) (a : Valuation cs), whileIter step' n (T a) = (whileIter step n a).map T :=
  fun n a => (rel_graph_iff.1 (whileIter_rel (fun a _ e => by
    subst e; rw [hs]; exact rel_map_of (fun _ => ⟨rfl, (hb _).symm⟩) _) n a _ rfl)).symm

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

/-- **Preservation.** Under the variable leaf, the block leaf on the `Good` expressions
    `P` accepts, the binding-threading leaf of `P` and `RegionTransports`, a program that
    `map?` returns for a `Good`-covered program at a renaming `ren` relating `W` to the
    transported `V` denotes, at every fuel, the transport of the source denotation. -/
theorem map?_denote (hT : P.RegionTypes)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ blk, P.lowerExprBlock? e = some blk →
      ∀ V : Valuation Γ, blk.denote (mapVal V) = transTy (e.denote V))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.Covered Good) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      pullV ren W = mapVal V → ∀ q, map? P hT p ren = some q →
      q.denote fuel W = (p.denote fuel V).map (transArgs P.mapTy transTy) := by
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
      simp only [denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      refine spliceNF?_denote fuel _ _ W _ (fun ren' res W' h1 h2 q' hq' => ?_) q hq
      refine ih hk _ (V.extend (e.denote V)) W' ?_ q' hq'
      refine pullV_bodyHom P transTy mapVal hExt ren ren' res V _ W W' hren h1 ?_
      rw [h2, FieldDialectBlockDescent.Com.denote_rename, hren, hBlk e hg blk hblk V]
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨hb, hk⟩ := hp
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toNat_trans,
        lookupArgs_mapArgs P transTy mapVal hVar ren V W hren]
      rw [foldlM_option_map _ _ (transArgs P.mapTy transTy) (fun acc i => by
        rw [← hR.ofNat_trans i]
        exact ihb hb _ _ _ (pullV_appHom P transTy mapVal hExt _ _ _
          (pullV_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ acc) b hbq)]
      exact bind_map_comm _ _ _ _ _
        (fun acc => ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ acc)
          k' hkq)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨ht, he, hk⟩ := hp
      obtain ⟨a, haq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookup_varTyCast, ← lookup_pullV, hren, hVar, hR.toBool_trans]
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then a.denote fuel W else b.denote fuel W) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
            else els.denote fuel V).map (transArgs P.mapTy transTy) := by
        split
        · exact iht ht ren V W hren a haq
        · exact ihe he ren V W hren b hbq
      rw [harm]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ r)
          k' hkq)
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren q hq
      obtain ⟨hb, hk⟩ := hp
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote]
      rw [lookupArgs_mapArgs P transTy mapVal hVar ren V W hren,
        whileIter_map (fun acc => body.denote fuel (hvAppend acc V)) _
          (transArgs P.mapTy transTy) (fun b => tyCast hT.bit_eq (transTy b))
          hR.toBool_trans (fun a => by
            rw [denote_castRetHead,
              ihb hb _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ a) b hbq,
              Option.map_map]
            congr 1
            funext r
            cases r
            rfl)]
      exact bind_map_comm _ _ _ _ _
        (fun r => ihk hk _ _ _ (pullV_appHom P transTy mapVal hExt ren V W hren _ r)
          k' hkq)

variable (L : BlockLoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)

/-- **Preservation along a total lowering.** Under the variable leaf, the block leaf on
    `Good` expressions and the binding-threading leaf of `L`, and `RegionTransports`, a
    `Good`-covered program lowered by `map` at a renaming `ren` relating `W` to the
    transported `V` denotes, at every fuel, the transport of the source denotation. -/
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
        (p.denote fuel V).map (transArgs L.mapTy transTy) :=
  fun ren V W hren =>
    map?_denote L.toPartial transTy mapVal hT Good hVar
      (fun e hg blk hblk V => by
        cases hblk
        exact hBlk e hg V)
      hExt hR fuel p hp ren V W hren _ (map?_toPartial L hT p ren)

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
