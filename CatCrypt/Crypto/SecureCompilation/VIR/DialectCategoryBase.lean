/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategoryTemplate
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminValTransport

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

## Main results

* `Dial.Hom.ext` — a morphism is determined by its lowering and its value transport.
* `Dial.Hom.mapVal_surjective` — every valuation of a mapped context is a transported
  valuation.
* `Dial.Hom.map_denote` — `NFProg.map` along a morphism preserves denotation, for every
  program.
* `Dial.transArgs_id_heq`, `Dial.transArgs_comp_heq` — the transport of an argument
  vector along the identity and along a composite.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open FieldDialectBlockDescent
  (BlockLoweringData TransTy MapVal VarTransports BlockOpTransports MapValExtends)
open BlockLoweringExtend (transArgs)
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

/-- The transport of an argument vector along the identity type map and the identity
    value transport is the vector. -/
theorem transArgs_id_heq : {ts : List T} → (x : HVector (fun t => ⟦t⟧) ts) →
    transArgs (fun t => t) (fun x => x) x ≍ x
  | [], .nil => HEq.rfl
  | t :: ts, .cons x xs => by
      have ih := transArgs_id_heq xs
      show HVector.cons x (transArgs (fun t => t) (fun x => x) xs) ≍ HVector.cons x xs
      generalize transArgs (fun t => t) (fun x => x) xs = ys at ih
      have hts : ts.map (fun t => t) = ts := List.map_id' ts
      revert ys
      rw [hts]
      intro ys ih
      rw [eq_of_heq ih]

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

section Calls

variable {d : Dialect.{0, 0}} [TyDenote d.Ty]

/-- A call at a signature and an argument valuation equal to another signature and
    argument valuation returns the same results, read along the equality of the result
    types. -/
theorem call_eq_map_of_heq (E : CallEnv d) (f : String) {as₁ as₂ rs₁ rs₂ : List d.Ty}
    (has : as₁ = as₂) (hrs : rs₁ = rs₂) {x₁ : Valuation as₁} {x₂ : Valuation as₂}
    (hx : x₁ ≍ x₂) {α : Type} (o : Option α) (T₁ : α → Valuation rs₁)
    (T₂ : α → Valuation rs₂) (hT : ∀ r, T₁ r ≍ T₂ r)
    (h : E.call f as₂ rs₂ x₂ = o.map T₂) : E.call f as₁ rs₁ x₁ = o.map T₁ := by
  subst has hrs
  obtain rfl := eq_of_heq hx
  obtain rfl : T₁ = T₂ := funext fun r => eq_of_heq (hT r)
  exact h

end Calls

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
def crypto : Dial := ⟨CatCryptDialect.catCryptDialect⟩

/-- The Jasmin dialect as an object of `Dial`. -/
def jasmin : Dial := ⟨JasminDialect.jasminDialect⟩

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

end CatCrypt.Crypto.SecureCompilation.VIR
