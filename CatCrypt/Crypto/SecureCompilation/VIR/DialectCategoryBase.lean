/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategoryTemplate
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminValTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategoryTemplateCatToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.TransArgsLaws

/-!
# The category of dialects with certified template lowerings

An object of `Dial` is a dialect together with the instances under which its structured
programs `NFProg` are denoted: a signature, a denotation of types and of operations, the
trip-counter type, the bit type and a call environment.

A morphism `Dial.Hom a b` is a block lowering that is a template lowering, together with
a value transport `transTy`, a valuation transport `mapVal`, and the proofs under which
`NFProg.map` along the lowering preserves denotation (`NFProg.map_denote_call`): the
variable leaf, the block leaf at every expression, the binding-threading leaf, the
agreement of the type map and of the transport with the trip counter and the bit, and the
agreement of the two call environments along the transport. The value transport is
surjective at every type.

The value transport is part of the identity of a morphism. The valuation transport is
determined by it (`Dial.mapVal_unique`), so two morphisms with the same lowering and the
same value transport are equal (`Dial.Hom.ext`).

The identity is `BlockLoweringData.id` with the identity transports, and the composition
is `BlockLoweringData.compBlock` with the composite transports `compBlockTransTy` and
`compBlockMapVal`. The unit and associativity laws are those of template lowerings
(`ofTemplate_id_comp`, `compBlock_id`, `ofTemplate_comp_assoc`); on the value transports
they hold by reduction.

## Main definitions

* `Dial` — a dialect with the instances of its structured programs.
* `Dial.Hom` — a template lowering with its transports, their proofs and surjectivity.
* `Dial.Hom.id`, `Dial.Hom.comp` — identity and composition.
* `Dial.instCategory` — the category of dialects.
* `Dialect.restrict`, `Dial.restrict`, `Dial.incl` — the restriction of a dialect to a
  set of operations, with the instances of the dialect, and its inclusion.
* `DialectRestrict.restrictFrame`, `DialectRestrict.acceptedTemplate`,
  `DialectRestrict.acceptedLowering` — a partial template lowering as a total lowering of
  the dialect restricted to the operations it accepts.
* `DialectRestrict.restrictNF?` — the restriction of a structured program, defined when
  every let-bound operation is in the set.
* `Dial.cryptoAccepted`, `Dial.catToJasmin` — the crypto dialect restricted to the
  operations `NFProgCatToJasmin.catToJasmin` accepts, and its lowering to the Jasmin
  dialect as a morphism.

## Main results

* `Dial.Hom.mapTy_ne_cryptoToJasmin` — no morphism from the unrestricted crypto dialect
  to the Jasmin dialect has the type map `CryptoToJasminCom.mapTy`.
* `DialectRestrict.templateBlock?_ofRestrict` — a partial template at an accepted
  expression gives the block of the accepted lowering.

* `Dial.Hom.ext` — a morphism is determined by its lowering and its value transport.
* `Dial.Hom.mapVal_surjective` — every valuation of a mapped context is a transported
  valuation.
* `Dial.Hom.map_denote` — `NFProg.map` along a morphism preserves denotation, for every
  program.
* `Dial.transArgs_comp_heq` — the transport of an argument vector along a composite (the
  identity case is `BlockLoweringExtend.transArgs_id_heq` of `TransArgsLaws`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open FieldDialectBlockDescent
  (BlockLoweringData TransTy MapVal VarTransports BlockOpTransports MapValExtends)
open BlockLoweringExtend (transArgs transArgs_id_heq)
open BlockLoweringDataComp
open DialectCategory
open CategoryTheory

/-- **A dialect with the instances of its structured programs**: a signature, a
    denotation of types and of operations, the trip-counter type, the bit type and a call
    environment. -/
structure Dial : Type 1 where
  /-- The dialect. -/
  dia : Dialect.{0, 0}
  /-- Its signature. -/
  [sig : DialectSignature dia]
  /-- The denotation of its types. -/
  [tyDenote : TyDenote dia.Ty]
  /-- Its trip-counter type. -/
  [word : HasWord64 dia]
  /-- Its bit type. -/
  [bool : HasBoolBit dia]
  /-- The denotation of its operations. -/
  [denote : DialectDenote dia]
  /-- Its call environment. -/
  [call : CallDenote dia]

namespace Dial

attribute [instance] Dial.sig Dial.tyDenote Dial.word Dial.bool Dial.denote Dial.call

/-! ## 1. Casts and argument transports -/

section Casts

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [TyDenote d'.Ty]

/-- A value transport along a type map `m` followed by a cast is the cast along the
    composite equality: the transport commutes with the cast along an equality of source
    types. -/
theorem tyCast_transTy (m : d.Ty → d'.Ty) (tr : ∀ {t : d.Ty}, ⟦t⟧ → ⟦m t⟧) {a b : d.Ty}
    {c : d'.Ty} (h₁ : a = b) (h₂ : m b = c) (y : ⟦a⟧) :
    NFProg.tyCast ((congrArg m h₁).trans h₂) (tr y) =
      NFProg.tyCast h₂ (tr (NFProg.tyCast h₁ y)) := by
  subst h₁ h₂
  rfl

/-- A valuation of a context equal to the empty context is unique. -/
theorem valuation_eq_of_nil {Δ : Ctxt d} (h : Δ = []) (A B : Valuation Δ) : A = B := by
  subst h
  cases A
  cases B
  rfl

/-- A valuation of a context equal to a cons is the cast of an extended valuation. -/
theorem valuation_eq_extend {Δ Γ : Ctxt d} {t : d.Ty} (h : Δ = t :: Γ) (W : Valuation Δ) :
    ∃ (y : ⟦t⟧) (W' : Valuation Γ), W = h ▸ Valuation.extend W' y := by
  subst h
  cases W with
  | cons y W' => exact ⟨y, W', rfl⟩

end Casts

section TransArgs

variable {T T' T'' : Type} [TyDenote T] [TyDenote T'] [TyDenote T'']

/-- The transport of an argument vector along a composite type map and the composite
    value transport is the transport by the first followed by the transport by the
    second. -/
theorem transArgs_comp_heq (f : T → T') (g : T' → T'') (tf : ∀ {t : T}, ⟦t⟧ → ⟦f t⟧)
    (tg : ∀ {t : T'}, ⟦t⟧ → ⟦g t⟧) : {ts : List T} → (x : HVector (fun t => ⟦t⟧) ts) →
    transArgs (g ∘ f) (fun x => tg (tf x)) x ≍ transArgs g tg (transArgs f tf x)
  | [], .nil => HEq.rfl
  | t :: ts, .cons x xs => by
      have ih := transArgs_comp_heq f g tf tg xs
      show HVector.cons (tg (tf x)) (transArgs (g ∘ f) (fun x => tg (tf x)) xs) ≍
        HVector.cons (tg (tf x)) (transArgs g tg (transArgs f tf xs))
      generalize transArgs (g ∘ f) (fun x => tg (tf x)) xs = ys at ih
      generalize transArgs g tg (transArgs f tf xs) = zs at ih
      have hts : ts.map (g ∘ f) = (ts.map f).map g := (List.map_map).symm
      revert ys
      rw [hts]
      intro ys ih
      rw [eq_of_heq ih]

end TransArgs

/-! ## 2. Morphisms -/

/-- **A certified template lowering** from `a` to `b`: a block lowering that is a
    template lowering, a value transport and a valuation transport, the leaves of
    `NFProg.map_denote_call` for them, and surjectivity of the value transport at every
    type. -/
structure Hom (a b : Dial) : Type where
  /-- The block lowering. -/
  lower : BlockLoweringData a.dia b.dia
  /-- The lowering is the template lowering of an op template over a frame. -/
  isTemplate : ∃ (F : LoweringFrame a.dia b.dia) (T : F.Template),
    lower = BlockLoweringData.ofTemplate F T
  /-- The value transport. -/
  transTy : TransTy lower
  /-- The valuation transport. -/
  mapVal : MapVal lower
  /-- The type map sends the trip-counter type and the bit type of `a` to those of `b`. -/
  regionTypes : NFProg.RegionTypes lower
  /-- The variable leaf. -/
  varTransports : VarTransports lower transTy mapVal
  /-- The block leaf, at every expression. -/
  blockOpTransports : BlockOpTransports lower transTy mapVal
  /-- The binding-threading leaf. -/
  mapValExtends : MapValExtends lower transTy mapVal
  /-- The value transport commutes with the readings of the trip counter and the bit. -/
  regionTransports : NFProg.RegionTransports lower regionTypes transTy
  /-- The call environments of `a` and `b` agree along the transport at every call. -/
  callTransports : (CallDenote.env (d := a.dia)).Transports (CallDenote.env (d := b.dia))
    (fun as => as.map lower.mapTy) (fun x => transArgs lower.mapTy transTy x)
    (fun _ _ _ => True)
  /-- The value transport is surjective at every type. -/
  surjective : ∀ t : a.dia.Ty, Function.Surjective (transTy (t := t))

/-- A valuation transport of a lowering that sends the empty context to the empty context
    is determined by the value transport it threads through bindings. -/
theorem mapVal_unique {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [DialectSignature d'] [TyDenote d'.Ty] [DialectDenote d']
    (L : BlockLoweringData d d') (hnil : L.mapCtx [] = [])
    (tr : TransTy L) (m₁ m₂ : MapVal L) (h₁ : MapValExtends L tr m₁)
    (h₂ : MapValExtends L tr m₂) : {Γ : Ctxt d} → (V : Valuation Γ) → m₁ V = m₂ V
  | [], _ => valuation_eq_of_nil hnil _ _
  | t :: Γ, .cons x V => by
      show m₁ (Valuation.extend V x) = m₂ (Valuation.extend V x)
      have e₁ : m₁ (Valuation.extend V x) =
          (L.mapCtx_cons t Γ ▸ Valuation.extend (m₁ V) (tr x)) := h₁ V x
      have e₂ : m₂ (Valuation.extend V x) =
          (L.mapCtx_cons t Γ ▸ Valuation.extend (m₂ V) (tr x)) := h₂ V x
      rw [e₁, e₂, mapVal_unique L hnil tr m₁ m₂ h₁ h₂ V]

namespace Hom

variable {a b c : Dial}

/-- The lowering of a morphism sends the empty context to the empty context. -/
theorem mapCtx_nil (f : Hom a b) : f.lower.mapCtx [] = [] := by
  obtain ⟨F, T, h⟩ := f.isTemplate
  rw [h]
  exact F.mapCtx_nil

/-- **Extensionality.** Two morphisms with the same lowering and the same value transport
    are equal. -/
theorem ext (f g : Hom a b) (hl : f.lower = g.lower)
    (ht : ∀ {t : a.dia.Ty} (x : ⟦t⟧), f.transTy x ≍ g.transTy x) : f = g := by
  have hnil := f.mapCtx_nil
  obtain ⟨l, it, tr, mv, rt, hv, ho, he, hr, hc, hs⟩ := f
  obtain ⟨l', it', tr', mv', rt', hv', ho', he', hr', hc', hs'⟩ := g
  dsimp only at hl ht hnil
  subst hl
  obtain rfl : @tr = @tr' := funext fun t => funext fun x => eq_of_heq (ht x)
  obtain rfl : @mv = @mv' :=
    funext fun Γ => funext fun V => mapVal_unique l hnil tr mv mv' he he' V
  rfl

/-- **Surjectivity on valuations.** Every valuation of a mapped context is the transport
    of a valuation. -/
theorem mapVal_surjective (f : Hom a b) : (Γ : Ctxt a.dia) →
    (W : Valuation (f.lower.mapCtx Γ)) → ∃ V : Valuation Γ, f.mapVal V = W
  | [], _ => ⟨.nil, valuation_eq_of_nil f.mapCtx_nil _ _⟩
  | t :: Γ, W => by
      obtain ⟨y, W', rfl⟩ := valuation_eq_extend (f.lower.mapCtx_cons t Γ) W
      obtain ⟨x, rfl⟩ := f.surjective t y
      obtain ⟨V, rfl⟩ := mapVal_surjective f Γ W'
      exact ⟨Valuation.extend V x, f.mapValExtends V x⟩

/-- **Preservation along a morphism.** Every program lowered by `NFProg.map` along the
    lowering of a morphism, at a renaming relating `W` to the transported `V`, denotes at
    every fuel the transport of the source denotation. -/
theorem map_denote_ren (f : Hom a b) (fuel : Nat) {Γ : Ctxt a.dia} {ts : List a.dia.Ty}
    (p : NFProg a.dia Γ ts) {Δ : Ctxt b.dia} (ren : Ctxt.Hom (f.lower.mapCtx Γ) Δ)
    (V : Valuation Γ) (W : Valuation Δ)
    (hren : FieldDialectBlockDescent.pullV ren W = f.mapVal V) :
    (NFProg.map f.lower f.regionTypes p ren).denote fuel W =
      (p.denote fuel V).map (transArgs f.lower.mapTy f.transTy) :=
  NFProg.map_denote_call f.lower f.transTy f.mapVal f.regionTypes (fun _ => True)
    f.varTransports (fun e _ V => f.blockOpTransports e V) f.mapValExtends
    f.regionTransports fuel p (NFProg.covered_of_forall _ (fun _ => trivial) p)
    (f.callTransports.mono fun _ _ _ _ => trivial) ren V W hren

/-- **Preservation along a morphism at the identity renaming.** -/
theorem map_denote (f : Hom a b) (fuel : Nat) {Γ : Ctxt a.dia} {ts : List a.dia.Ty}
    (p : NFProg a.dia Γ ts) (V : Valuation Γ) :
    (NFProg.map f.lower f.regionTypes p (fun v => v)).denote fuel (f.mapVal V) =
      (p.denote fuel V).map (transArgs f.lower.mapTy f.transTy) :=
  f.map_denote_ren fuel p _ V _ (FieldDialectBlockDescent.pullV_id _)

/-! ## 3. Identity and composition -/

/-- **The identity morphism**: the identity block lowering with the identity
    transports. -/
protected def id (a : Dial) : Hom a a where
  lower := BlockLoweringData.id a.dia
  isTemplate := ⟨_, _, id_eq_ofTemplate a.dia⟩
  transTy := fun x => x
  mapVal := fun V => V
  regionTypes := regionTypes_id
  varTransports := fun _ _ => rfl
  blockOpTransports := fun _ _ => rfl
  mapValExtends := fun _ _ => rfl
  regionTransports := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  callTransports := fun f as rs x _ =>
    call_eq_map_of_heq _ f (List.map_id' as) (List.map_id' rs) (transArgs_id_heq x) _ _
      (fun r => r) (fun r => transArgs_id_heq r) Option.map_id'.symm
  surjective := fun _ => Function.surjective_id

/-- **The composite of two morphisms**: the composite block lowering with the composite
    transports. -/
protected def comp (f : Hom a b) (g : Hom b c) : Hom a c where
  lower := f.lower.compBlock g.lower
  isTemplate := by
    obtain ⟨F, T, hL⟩ := f.isTemplate
    obtain ⟨G, S, hM⟩ := g.isTemplate
    rw [hL, hM]
    exact ⟨_, _, ofTemplate_comp F T G S⟩
  transTy := compBlockTransTy f.lower g.lower f.transTy g.transTy
  mapVal := compBlockMapVal f.lower g.lower f.mapVal g.mapVal
  regionTypes :=
    ⟨(congrArg g.lower.mapTy f.regionTypes.word_eq).trans g.regionTypes.word_eq,
      (congrArg g.lower.mapTy f.regionTypes.bit_eq).trans g.regionTypes.bit_eq⟩
  varTransports := compBlock_varTransports _ _ _ _ _ _ f.varTransports g.varTransports
  blockOpTransports := compBlock_blockOpTransports _ _ _ _ _ _ f.blockOpTransports
    g.varTransports g.blockOpTransports g.mapValExtends
  mapValExtends := compBlock_mapValExtends _ _ _ _ _ _ f.mapValExtends g.mapValExtends
  regionTransports :=
    { toNat_trans := fun x =>
        (congrArg (HasWord64.toNat (d := c.dia))
          (tyCast_transTy g.lower.mapTy g.transTy f.regionTypes.word_eq
            g.regionTypes.word_eq (f.transTy x))).trans
          ((g.regionTransports.toNat_trans _).trans (f.regionTransports.toNat_trans x))
      ofNat_trans := fun i =>
        (tyCast_transTy g.lower.mapTy g.transTy f.regionTypes.word_eq
          g.regionTypes.word_eq (f.transTy (HasWord64.ofNat (d := a.dia) i))).trans
          ((congrArg (fun y => NFProg.tyCast g.regionTypes.word_eq (g.transTy y))
            (f.regionTransports.ofNat_trans i)).trans (g.regionTransports.ofNat_trans i))
      toBool_trans := fun x =>
        (congrArg (HasBoolBit.toBool (d := c.dia))
          (tyCast_transTy g.lower.mapTy g.transTy f.regionTypes.bit_eq
            g.regionTypes.bit_eq (f.transTy x))).trans
          ((g.regionTransports.toBool_trans _).trans (f.regionTransports.toBool_trans x)) }
  callTransports := fun s as rs x _ =>
    call_eq_map_of_heq (CallDenote.env (d := c.dia)) s
      (as₂ := (as.map f.lower.mapTy).map g.lower.mapTy)
      (rs₂ := (rs.map f.lower.mapTy).map g.lower.mapTy)
      (List.map_map).symm (List.map_map).symm
      (transArgs_comp_heq f.lower.mapTy g.lower.mapTy f.transTy g.transTy x)
      ((CallDenote.env (d := a.dia)).call s as rs x) _
      (fun r => transArgs g.lower.mapTy g.transTy (transArgs f.lower.mapTy f.transTy r))
      (fun r => transArgs_comp_heq f.lower.mapTy g.lower.mapTy f.transTy g.transTy r)
      (by
        rw [g.callTransports s _ _ _ trivial, f.callTransports s as rs x trivial,
          Option.map_map]
        rfl)
  surjective := fun t => (g.surjective _).comp (f.surjective t)

end Hom

/-! ## 4. The category -/

/-- **The category of dialects**: dialects with the instances of their structured
    programs are the objects and certified template lowerings the morphisms, with
    `BlockLoweringData.id` as identity and `compBlock` as composition. -/
instance instCategory : Category Dial where
  Hom a b := Dial.Hom a b
  id a := Dial.Hom.id a
  comp f g := Dial.Hom.comp f g
  id_comp f := Hom.ext _ _ (by
    obtain ⟨G, S, hM⟩ := f.isTemplate
    show (BlockLoweringData.id _).compBlock f.lower = f.lower
    rw [hM]
    exact ofTemplate_id_comp G S) (fun _ => HEq.rfl)
  comp_id f := Hom.ext _ _ (compBlock_id f.lower) (fun _ => HEq.rfl)
  assoc f g h := Hom.ext _ _ (by
    obtain ⟨G, S, hN⟩ := h.isTemplate
    show (f.lower.compBlock g.lower).compBlock h.lower =
      f.lower.compBlock (g.lower.compBlock h.lower)
    rw [hN]
    exact ofTemplate_comp_assoc f.lower g.lower G S) (fun _ => HEq.rfl)

/-- The lowering of an identity morphism is the identity block lowering. -/
theorem id_lower (a : Dial) : (𝟙 a : Hom a a).lower = BlockLoweringData.id a.dia := rfl

/-- The lowering of a composite is the composite of the lowerings. -/
theorem comp_lower {a b c : Dial} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g : Hom a c).lower = (f : Hom a b).lower.compBlock (g : Hom b c).lower := rfl

/-- The value transport of a composite is the composite of the value transports. -/
theorem comp_transTy {a b c : Dial} (f : a ⟶ b) (g : b ⟶ c) {t : a.dia.Ty} (x : ⟦t⟧) :
    (f ≫ g : Hom a c).transTy x = (g : Hom b c).transTy ((f : Hom a b).transTy x) := rfl

/-! ## 5. The crypto dialect and the Jasmin dialect -/

/-- The crypto dialect as an object of `Dial`. -/
@[reducible] def crypto : Dial := ⟨CatCryptDialect.catCryptDialect⟩

/-- The Jasmin dialect as an object of `Dial`. -/
@[reducible] def jasmin : Dial := ⟨JasminDialect.jasminDialect⟩

open CryptoSSA (CryptoTy) in
/-- **The value transport `ctTransTy` is surjective at every type.** It is the identity
    at words and arrays and a bijection at the bit; the unit, pairs and sums map to the
    zero-width register, whose only value is the image of the default value. -/
theorem ctTransTy_surjective : (t : CryptoTy) →
    Function.Surjective (CryptoToJasminComCorrect.ctTransTy (t := t))
  | .sword _ => fun y => ⟨y, rfl⟩
  | .memref _ => fun y => ⟨y, rfl⟩
  | .memrefW _ _ => fun y => ⟨y, rfl⟩
  | .bit => fun (y : BitVec 1) =>
      ⟨y.getLsbD 0, show BitVec.ofBool (y.getLsbD 0) = y by
        revert y
        decide⟩
  | .unit => fun (y : BitVec 0) => ⟨CryptoTy.default .unit, (BitVec.eq_nil y).symm ▸ rfl⟩
  | .pair a b => fun (y : BitVec 0) =>
      ⟨CryptoTy.default (.pair a b), (BitVec.eq_nil y).symm ▸ rfl⟩
  | .sum a b => fun (y : BitVec 0) =>
      ⟨CryptoTy.default (.sum a b), (BitVec.eq_nil y).symm ▸ rfl⟩

open CryptoSSA (CryptoTy) in
open CatCryptDialect JasminDialect in
/-- **No morphism from the crypto dialect to the Jasmin dialect has the type map
    `CryptoToJasminCom.mapTy`.** That type map sends a pair to the zero-width register,
    so the block of the first projection of a pair of a 1-bit word is denoted at one
    valuation only, while the block leaf requires it to return both values of the word. -/
theorem Hom.mapTy_ne_cryptoToJasmin (f : Hom crypto jasmin) :
    f.lower.mapTy ≠ CryptoToJasminCom.mapTy := by
  intro hty
  have hnil := f.mapCtx_nil
  obtain ⟨⟨mT, mC, mCc, mV, lE⟩, it, tr, mv, rt, hv, ho, he, hr, hc, hs⟩ := f
  dsimp only at hty hnil
  subst hty
  have hΓ : mC [CryptoTy.pair (.sword 1) .unit] = [JasminTy.reg 0] :=
    (mCc _ _).trans (congrArg _ hnil)
  have hval : ∀ (Δ : Ctxt jasminDialect) (_ : Δ = [JasminTy.reg 0]) (A B : Valuation Δ),
      A = B := by
    intro Δ h A B
    subst h
    cases A with
    | cons x A =>
      cases B with
      | cons y B =>
        cases A
        cases B
        rw [BitVec.eq_nil x, BitVec.eq_nil y]
  let e : Expr catCryptDialect [CryptoTy.pair (.sword 1) .unit] (.sword 1) :=
    ⟨.fst (.sword 1) .unit, rfl, .cons .here .nil⟩
  have h01 : tr (t := .sword 1) (0#1 : BitVec 1) = tr (t := .sword 1) (1#1 : BitVec 1) := by
    have h0 := ho e (.cons (((0#1 : BitVec 1), ()) : BitVec 1 × Unit) .nil)
    have h1 := ho e (.cons (((1#1 : BitVec 1), ()) : BitVec 1 × Unit) .nil)
    exact h0.symm.trans ((congrArg (lE e).denote (hval _ hΓ _ _)).trans h1)
  have hinj : Function.Injective (fun x : BitVec 1 => (tr (t := .sword 1) x : BitVec 1)) :=
    Finite.injective_iff_surjective.mpr (hs (.sword 1))
  exact absurd (hinj h01) (by decide)

end Dial

/-! ## 6. The restriction of a dialect to a set of operations -/

/-- **The restriction of a dialect** to the operations satisfying `p`: the same types and
    the operations of `d` at which `p` holds. -/
@[reducible] def Dialect.restrict (d : Dialect.{0, 0}) (p : d.Op → Prop) : Dialect.{0, 0} where
  Op := {op : d.Op // p op}
  Ty := d.Ty

namespace DialectRestrict

open DialectOpSum (castVar castArgs lookup_castVar lookupArgs_castArgs)

/-- Equal block lowerings give the same block at every expression. -/
theorem lowerExprBlock_heq {d d' : Dialect} [DialectSignature d] [DialectSignature d']
    {L M : BlockLoweringData d d'} (h : L = M) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    L.lowerExprBlock e ≍ M.lowerExprBlock e := by
  subst h
  rfl

variable {d : Dialect.{0, 0}} (p : d.Op → Prop)


/-- The signature of a restricted dialect is that of the dialect. -/
@[reducible] instance instDialectSignatureRestrict [DialectSignature d] :
    DialectSignature (d.restrict p) where
  sig op := DialectSignature.sig (d := d) op.1
  ret op := DialectSignature.ret (d := d) op.1

/-- The denotation of a restricted dialect is that of the dialect. -/
@[reducible] instance instDialectDenoteRestrict [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] :
    DialectDenote (d.restrict p) where
  denote op := DialectDenote.denote (d := d) op.1

/-- The trip counter of a restricted dialect is that of the dialect. -/
@[reducible] instance instHasWord64Restrict [TyDenote d.Ty] [HasWord64 d] :
    HasWord64 (d.restrict p) where
  word := HasWord64.word (d := d)
  toNat := HasWord64.toNat (d := d)
  ofNat := HasWord64.ofNat (d := d)

/-- The bit of a restricted dialect is that of the dialect. -/
@[reducible] instance instHasBoolBitRestrict [TyDenote d.Ty] [HasBoolBit d] :
    HasBoolBit (d.restrict p) where
  bit := HasBitType.bit (d := d)
  toBool := HasBoolBit.toBool (d := d)

/-- The call environment of a restricted dialect is that of the dialect. -/
@[reducible] instance instCallDenoteRestrict [TyDenote d.Ty] [CallDenote d] :
    CallDenote (d.restrict p) :=
  ⟨⟨(CallDenote.env (d := d)).call⟩⟩

section Literal

/-! The same instances at a dialect given by its operations and types, the form in which
instance resolution meets a dialect that is a reducible definition. -/

variable {O T : Type} (q : O → Prop)

/-- The signature of a restricted dialect, at a dialect given by its operations and
    types. -/
@[reducible] instance instDialectSignatureRestrictMk [DialectSignature (⟨O, T⟩ : Dialect)] :
    DialectSignature (Dialect.restrict ⟨O, T⟩ q) :=
  instDialectSignatureRestrict (d := ⟨O, T⟩) q

/-- The denotation of a restricted dialect, at a dialect given by its operations and
    types. -/
@[reducible] instance instDialectDenoteRestrictMk [TyDenote T]
    [DialectSignature (⟨O, T⟩ : Dialect)] [DialectDenote (⟨O, T⟩ : Dialect)] :
    DialectDenote (Dialect.restrict ⟨O, T⟩ q) :=
  instDialectDenoteRestrict (d := ⟨O, T⟩) q

/-- The trip counter of a restricted dialect, at a dialect given by its operations and
    types. -/
@[reducible] instance instHasWord64RestrictMk [TyDenote T] [HasWord64 (⟨O, T⟩ : Dialect)] :
    HasWord64 (Dialect.restrict ⟨O, T⟩ q) :=
  instHasWord64Restrict (d := ⟨O, T⟩) q

/-- The bit of a restricted dialect, at a dialect given by its operations and types. -/
@[reducible] instance instHasBoolBitRestrictMk [TyDenote T] [HasBoolBit (⟨O, T⟩ : Dialect)] :
    HasBoolBit (Dialect.restrict ⟨O, T⟩ q) :=
  instHasBoolBitRestrict (d := ⟨O, T⟩) q

/-- The call environment of a restricted dialect, at a dialect given by its operations and
    types. -/
@[reducible] instance instCallDenoteRestrictMk [TyDenote T] [CallDenote (⟨O, T⟩ : Dialect)] :
    CallDenote (Dialect.restrict ⟨O, T⟩ q) :=
  instCallDenoteRestrict (d := ⟨O, T⟩) q

end Literal

variable [DialectSignature d]

variable {p} in
/-- An expression of a restricted dialect as an expression of the dialect. -/
def ofRestrict {Γ : List d.Ty} {t : d.Ty} (e : Expr (d.restrict p) Γ t) :
    Expr d Γ t :=
  ⟨e.op.1, e.retTy_eq, castArgs e.args⟩

variable {p} in
/-- An expression of a restricted dialect denotes as it does in the dialect. -/
theorem denote_ofRestrict [TyDenote d.Ty] [DialectDenote d] {Γ : List d.Ty} {t : d.Ty}
    (e : Expr (d.restrict p) Γ t) (V : Valuation (d := d) Γ) :
    (ofRestrict e).denote V = e.denote (d := d.restrict p) V := by
  rcases e with ⟨op, h, args⟩
  subst h
  show DialectDenote.denote (d := d) op.1
      (Expr.lookupArgs (d := d) (castArgs (O' := d.Op) args) V) =
    DialectDenote.denote (d := d) op.1 (Expr.lookupArgs (d := d.restrict p) args V)
  exact congrArg _ (lookupArgs_castArgs args V)

variable {d' : Dialect.{0, 0}} [DialectSignature d']

/-- **The restriction of a lowering frame**: the frame of `F` read on the contexts and
    variables of the restricted dialect. -/
@[reducible] def restrictFrame (F : LoweringFrame d d') :
    LoweringFrame (d.restrict p) d' where
  mapTy := F.mapTy
  mapCtx := F.mapCtx
  mapCtx_nil := F.mapCtx_nil
  mapCtx_cons := F.mapCtx_cons
  mapVar := fun v => F.mapVar (castVar (O' := d.Op) v)
  mapVar_here := fun t Γ => F.mapVar_here t Γ
  mapVar_there := fun s Γ _ v => F.mapVar_there s Γ (castVar (O' := d.Op) v)

/-- The instance renaming of a restricted frame at an argument vector renames a program as
    the instance renaming of the frame at the cast vector. -/
theorem rename_restrictFrame (F : LoweringFrame d d') {Γ : List d.Ty} {ts : List d.Ty}
    (args : HVector (fun t => Var (d := d.restrict p) Γ t) ts) {s : d'.Ty}
    (c : Com d' (F.mapCtx ts) s) :
    Com.rename ((restrictFrame p F).mapHom (argsHom args)) c =
      Com.rename (F.mapHom (argsHom (castArgs (O' := d.Op) args))) c := by
  refine F.rename_ext _ _ (fun v => ?_) c
  obtain ⟨w, rfl⟩ : ∃ w : Var (d := d.restrict p) ts _,
      v = castVar (O' := d.Op) w :=
    ⟨castVar (O := d.Op) (O' := {op : d.Op // p op}) (T := d.Ty) v,
      ((castVar_castVar (O := d.Op) (O' := {op : d.Op // p op}) (O'' := d.Op) (T := d.Ty)
        v).trans (castVar_self (O := d.Op) (T := d.Ty) v)).symm⟩
  refine ((restrictFrame p F).mapHom_mapVar (argsHom args) w).trans ?_
  refine Eq.trans ?_ (F.mapHom_mapVar (argsHom (castArgs (O' := d.Op) args))
    (castVar (O' := d.Op) w)).symm
  exact congrArg F.mapVar (argsHom_castArgs (O' := d.Op) args w).symm

/-- **A total template restricted.** The instance of the restricted template at an
    expression of the restricted dialect is the instance of the template at the
    expression read in the dialect. -/
theorem templateBlock_restrict (F : LoweringFrame d d') (S : F.Template) {Γ : List d.Ty}
    {t : d.Ty} (e : Expr (d.restrict p) Γ t) :
    (restrictFrame p F).templateBlock (fun op => S op.1) e =
      F.templateBlock S (ofRestrict e) := by
  rcases e with ⟨op, h, args⟩
  subst h
  exact rename_restrictFrame p F args (S op.1)

/-- The total template, on the operations a partial template accepts, of the programs the
    partial template gives. -/
def acceptedTemplate (F : LoweringFrame d d') (S : F.Template?) :
    (restrictFrame (fun op => (S op).isSome) F).Template :=
  fun op => (S op.1).get op.2

/-- **A partial template on its accepted operations.** At an expression of the dialect
    restricted to the accepted operations, read in the dialect, the partial template
    gives the instance of `acceptedTemplate`. -/
theorem templateBlock?_ofRestrict (F : LoweringFrame d d') (S : F.Template?)
    {Γ : List d.Ty} {t : d.Ty}
    (e : Expr (d.restrict (fun op => (S op).isSome)) Γ t) :
    F.templateBlock? S (ofRestrict e) =
      some ((restrictFrame _ F).templateBlock (acceptedTemplate F S) e) := by
  rcases e with ⟨⟨op, hop⟩, h, args⟩
  subst h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hop
  show (S op).map (fun c => Com.rename (F.mapHom (argsHom (castArgs (O' := d.Op) args))) c) =
    some (Com.rename ((restrictFrame _ F).mapHom (argsHom args)) ((S op).get hop))
  rw [rename_restrictFrame]
  simp only [hc, Option.map_some, Option.get_some]

section Programs

variable [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [DecidablePred p]

/-- **The restriction of a structured program**: the same program over the restricted
    dialect, defined when every let-bound operation of the program and of its regions
    satisfies `p`. -/
def restrictNF? : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts →
    Option (NFProg (d.restrict p) Γ ts)
  | _, _, .ret vs => some (.ret (castArgs (O' := {op : d.Op // p op}) vs))
  | _, _, .var e k =>
      if h : p e.op then
        (restrictNF? k).map
          (.var ⟨⟨e.op, h⟩, e.retTy_eq, castArgs (O' := {op : d.Op // p op}) e.args⟩)
      else none
  | _, _, .forLoop count inits body k =>
      (restrictNF? body).bind fun body' => (restrictNF? k).map fun k' =>
        .forLoop (castVar (O' := {op : d.Op // p op}) count)
          (castArgs (O' := {op : d.Op // p op}) inits) body' k'
  | _, _, .ifThenElse cond thn els k =>
      (restrictNF? thn).bind fun thn' => (restrictNF? els).bind fun els' =>
        (restrictNF? k).map fun k' =>
          .ifThenElse (castVar (O' := {op : d.Op // p op}) cond) thn' els' k'
  | _, _, .whileLoop inits body k =>
      (restrictNF? body).bind fun body' => (restrictNF? k).map fun k' =>
        .whileLoop (castArgs (O' := {op : d.Op // p op}) inits) body' k'
  | _, _, .call f args k =>
      (restrictNF? k).map (.call f (castArgs (O' := {op : d.Op // p op}) args))

variable [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [DecidablePred p] in
/-- A block followed by the continuation that is `none` everywhere is `none`. -/
theorem spliceNF?_none {ts : List d'.Ty} : {Δ : Ctxt d'} → {a : d'.Ty} → (c : Com d' Δ a) →
    NFProg.spliceNF? (ts := ts) c (fun _ _ => none) = none
  | _, _, .ret _ => rfl
  | _, _, .var e blk => by
      show (NFProg.spliceNF? (ts := ts) blk (fun _ _ => none)).map (NFProg.var e) = none
      rw [spliceNF?_none blk]
      rfl

variable (F : LoweringFrame d d') (S : F.Template?)

/-- The total block lowering, on the operations a partial template accepts, of the
    partial template. -/
@[reducible] def acceptedLowering :
    BlockLoweringData (d.restrict fun op => (S op).isSome) d' :=
  BlockLoweringData.ofTemplate (restrictFrame _ F) (acceptedTemplate F S)

omit [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [DecidablePred p] [TyDenote d'.Ty]
  [HasWord64 d'] [HasBoolBit d'] in
/-- The variable map of a restricted frame at a variable read in the restricted dialect is
    the variable map of the frame. -/
theorem mapVar_restrictFrame {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) :
    (restrictFrame p F).mapVar (castVar (O := d.Op) (O' := {op : d.Op // p op}) (T := d.Ty) v) =
      F.mapVar v :=
  congrArg F.mapVar ((castVar_castVar (O := d.Op) (O' := {op : d.Op // p op}) (O'' := d.Op)
    (T := d.Ty) v).trans (castVar_self (O := d.Op) (T := d.Ty) v))

omit [DecidablePred p] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [TyDenote d'.Ty]
  [HasWord64 d'] [HasBoolBit d'] in
/-- Mapping a vector of variables read in the restricted dialect along the accepted
    lowering is mapping the vector along the partial template lowering. -/
theorem mapArgs_acceptedLowering {Γ : Ctxt d} {Δ : Ctxt d'} (ren : Ctxt.Hom (F.mapCtx Γ) Δ) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    NFProg.mapArgs (acceptedLowering F S).toPartial ren
        (castArgs (O := d.Op) (O' := {op : d.Op // (S op).isSome}) (T := d.Ty) vs) =
      NFProg.mapArgs (PartialBlockLowering.ofTemplate? F S) ren vs
  | [], .nil => rfl
  | _ :: _, .cons v vs =>
      congrArg₂ HVector.cons (congrArg ren (mapVar_restrictFrame _ F v))
        (mapArgs_acceptedLowering ren vs)

end Programs

end DialectRestrict

namespace Dial

open DialectRestrict

/-- The restriction of an object of `Dial` to the operations satisfying `p`, with the
    instances of the dialect. -/
@[reducible] def restrict (a : Dial) (p : a.dia.Op → Prop) : Dial := ⟨a.dia.restrict p⟩

/-- **The inclusion of a restricted dialect**: the identity template read on the
    operations satisfying `p`, with the identity transports. -/
def incl (a : Dial) (p : a.dia.Op → Prop) : Hom (a.restrict p) a where
  lower := BlockLoweringData.ofTemplate (restrictFrame p (LoweringFrame.id a.dia))
    (fun op => idTemplate a.dia op.1)
  isTemplate := ⟨_, _, rfl⟩
  transTy := fun x => x
  mapVal := fun V => V
  regionTypes := ⟨rfl, rfl⟩
  varTransports := fun v V => DialectOpSum.lookup_castVar v V
  blockOpTransports := fun e V => by
    show ((restrictFrame p (LoweringFrame.id a.dia)).templateBlock
      (fun op => idTemplate a.dia op.1) e).denote V = e.denote V
    rw [templateBlock_restrict, ← denote_ofRestrict e V]
    have hb : (BlockLoweringData.ofTemplate (LoweringFrame.id a.dia)
        (idTemplate a.dia)).lowerExprBlock (ofRestrict e) =
        (BlockLoweringData.id a.dia).lowerExprBlock (ofRestrict e) :=
      eq_of_heq (lowerExprBlock_heq (id_eq_ofTemplate a.dia).symm _)
    exact congrArg (fun c : Com a.dia _ _ => c.denote V) hb
  mapValExtends := fun _ _ => rfl
  regionTransports := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  callTransports := fun f as rs x _ =>
    call_eq_map_of_heq (CallDenote.env (d := a.dia)) f (List.map_id' as) (List.map_id' rs)
      (transArgs_id_heq x) _ _ (fun r => r) (fun r => transArgs_id_heq r)
      Option.map_id'.symm
  surjective := fun _ => Function.surjective_id

/-! ## 7. The lowering of the crypto dialect to the Jasmin dialect -/

/-- The operations of the crypto dialect that the template of
    `NFProgCatToJasmin.catToJasmin` accepts. -/
def accepted (op : CatCryptDialect.CatCryptOp) : Prop := (catTemplate op).isSome

/-- The crypto dialect restricted to the operations `catToJasmin` accepts. -/
@[reducible] def cryptoAccepted : Dial := crypto.restrict accepted

open CryptoToJasminComCorrect (ctTransTy) in
open DialectToJasminComCorrect (ctMapValD ctMapValD_lookup ctMapValD_extend) in
/-- **The lowering of the accepted crypto dialect to the Jasmin dialect**: the template of
    `catToJasmin` on the operations it accepts, with the value transport `ctTransTy` and
    the valuation transport `ctMapValD`. -/
def catToJasmin : Hom cryptoAccepted jasmin where
  lower := (BlockLoweringData.ofTemplate (restrictFrame accepted catFrame)
    (acceptedTemplate catFrame catTemplate) :
      BlockLoweringData (CatCryptDialect.catCryptDialect.restrict accepted)
        JasminDialect.jasminDialect)
  isTemplate := ⟨_, _, rfl⟩
  transTy := fun x => ctTransTy x
  mapVal := fun V => ctMapValD V
  regionTypes := ⟨rfl, rfl⟩
  varTransports := fun v V =>
    (ctMapValD_lookup _ V).trans (congrArg ctTransTy (DialectOpSum.lookup_castVar v V))
  blockOpTransports := fun e V =>
    (NFProgCatToJasmin.catToJasmin_block
      (ofRestrict (d := CatCryptDialect.catCryptDialect) (p := accepted) e) _
      ((catToJasmin_lowerExprBlock? _).trans (templateBlock?_ofRestrict catFrame catTemplate e))
      V).trans (congrArg ctTransTy
        (denote_ofRestrict (d := CatCryptDialect.catCryptDialect) (p := accepted) e V))
  mapValExtends := fun V x => ctMapValD_extend V x
  regionTransports :=
    ⟨NFProgCatToJasmin.catToJasmin_regionTransports.toNat_trans,
      NFProgCatToJasmin.catToJasmin_regionTransports.ofNat_trans,
      NFProgCatToJasmin.catToJasmin_regionTransports.toBool_trans⟩
  callTransports := CallEnv.transports_empty _ _ _
  surjective := ctTransTy_surjective

/-- The first projection of a pair is not an accepted operation. -/
theorem not_accepted_fst (a b : CryptoSSA.CryptoTy) : ¬ accepted (.fst a b) := by
  simp [accepted, catTemplate, DialectToJasminCom.toJBlockD, DialectToJasminCom.toJMultiD,
    DialectToJasminCom.toJExprD]

end Dial

end CatCrypt.Crypto.SecureCompilation.VIR
