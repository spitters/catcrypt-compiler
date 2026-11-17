/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomLoadsK
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPasses
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCallShape

/-!
# Loads and stores at constant indices through the passes after the splice

The shape `LoadsChainK` (loads and stores at word variables bound by a constant below the
length of the accessed array) is kept by the passes of the field route that keep the shape
`LoadsChain`: the carried form, the splice of a body before a continuation, the select
lowering, the widening, mask elimination, the carry pairs, the region legalisation and the
range stage.

Each pass is stated along a renaming, or between two indices of known constants, that carries
the known constants (`KCtx.Maps`, `KCtx.MapsP`, `KCtx.MapsW`, `KCtx.ModMaps`). A constant
binding stays a constant binding, a memory-free binding stays memory-free or is removed with
its uses sent to a variable of unknown constant, and the index of a load or a store keeps its
known constant.

The range stage rewrites the binding of `regConst 64 c` to the binding of
`regConst 64 (c % 2 ^ 64)` (`rangeExpr_const`): the constant survives exactly when
`c < 2 ^ 64`, and the shape is kept at the known constants reduced mod `2 ^ 64`
(`loadsChainK_loopRange`), which are below the lengths whenever the constants are.

## Main definitions

* `KCtx.MapsW`: a renaming of the widened context carries the known constants.
* `KCtx.ModMaps`: the known constants reduced mod `2 ^ 64`.

## Main results

* `loadsChainK_castNF`, `loadsChainK_seq?`: the carried form and the splice of a body before
  a continuation that continues the chain of its result keep the shape.
* `fieldDialectStep_loadsChainK`: the field dialect step takes one call of a tagged head to a
  program of the shape at every known constants.
* `loadsChainK_lowerSelects`, `loadsChainK_widen`, `loadsChainK_maskElimGo`,
  `loadsChainK_carryPairGo`, `loadsChainK_legalizeRegion`, `loadsChainK_narrowPrep`: the
  select lowering, the widening, mask elimination, the carry pairs, the narrow-word stages and
  the legalisation keep the shape.
* `rangeExpr_const`, `loadsChainK_loopRange`: the range stage reduces a constant mod
  `2 ^ 64` and keeps the shape at the reduced known constants.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open Ctxt (Var)

/-! ## 1. The carried form and the splice of a body -/

/-- **A carried program has the shape `LoadsChainK`** at every known constants when the program
    has it at every known constants. -/
theorem loadsChainK_castNF {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') {q : NFProg jasminDialect Γ ts} (h : ∀ K : KCtx Γ, LoadsChainK K q)
    (K : KCtx Γ') : LoadsChainK K (FieldDialectStep.castNF hΓ hts q) := by
  subst hΓ hts
  exact h K

/-- No known constant is carried by every partial renaming. -/
theorem KCtx.mapsP_none {Γ Δ : Ctxt jasminDialect} (f : PRen Γ Δ) (K' : KCtx Δ) :
    KCtx.MapsP f (fun _ => none) K' := fun _ _ _ _ h => by cases h

/-- A chain tail at constant indices has the shape `LoadsChainK`. -/
theorem loadsChainK_of_chainTailK {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) : LoadsChainK K k := by
  induction h with
  | const K v c k _ ih => exact .const _ _ _ ih
  | free K v e k he _ ih => exact .free _ _ _ he ih
  | store K v i x c k hi hc hk _ => exact .store _ _ _ _ _ _ hi hc hk
  | ret K v => exact .ret _ _

/-- **The splice of a chain tail at constant indices before a continuation that continues the
    chain** is a chain tail at constant indices, under a partial renaming that carries the
    known constants. -/
theorem chainTailK_seq? : ∀ {Δ : Ctxt jasminDialect} {K : KCtx Δ} {w m w' m' : Nat}
    {v : Var Δ (.stackArr w' m')} {b : NFProg jasminDialect Δ [.stackArr w m]},
    ChainTailK K v b →
    ∀ {Γ₀ : Ctxt jasminDialect} {ts : List JasminTy}
      {k : NFProg jasminDialect (.stackArr w m :: Γ₀) ts}, ChainTailK (fun _ => none) .here k →
    ∀ {Γ : Ctxt jasminDialect} {K' : KCtx Γ} {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ}
      {v' : Var Γ (.stackArr w' m')} {q : NFProg jasminDialect Γ ts}, KCtx.MapsP ρ K K' →
      ρ v = some v' → NFProg.seq? k b ρ θ = some q → ChainTailK K' v' q
  | _, _, _, _, _, _, _, _, .const _ v c b hb, _, _, k, hk, _, K', ρ, θ, v', q, hK, hv, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain rfl := rename?_const he'
      exact .const _ _ _ _ (chainTailK_seq? hb hk (KCtx.mapsP_lift hK _)
        (show (ρ v).map Var.there = _ by rw [hv]; rfl) hq')
  | _, _, _, _, _, _, _, _, .free _ v e b he hb, _, _, k, hk, _, K', ρ, θ, v', q, hK, hv, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      exact .free _ _ _ _ ((rename?_op he').symm ▸ he) (chainTailK_seq? hb hk
        (KCtx.mapsP_lift hK _) (show (ρ v).map Var.there = _ by rw [hv]; rfl) hq')
  | _, _, _, _, _, _, _, _, .store _ v i x c b hi hc hb, _, _, k, hk, _, K', ρ, θ, v', q, hK, hv,
      hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨v'', i', x', hv', hi', rfl⟩ := rename?_store' ρ v i x he'
      rw [hv] at hv'
      cases hv'
      exact .store _ _ _ _ c _ (hK i i' c hi' hi) hc
        (chainTailK_seq? hb hk (KCtx.mapsP_lift hK _) rfl hq')
  | _, _, _, _, _, _, _, _, .ret _ v, _, _, k, hk, _, K', ρ, θ, v', q, hK, hv, hq => by
      change ((ρ v).bind fun v' => (some HVector.nil).map (HVector.cons v')).bind
        (fun ws => NFProg.rename? (PRen.appendVars θ ws) k) = some q at hq
      simp only [hv, Option.bind_some, Option.map_some] at hq
      exact chainTailK_rename? hk (KCtx.mapsP_none _ _) rfl hq

/-- **The splice of a body of the shape `LoadsChainK` before a continuation that continues the
    chain of its result** has the shape, under a partial renaming that carries the known
    constants. -/
theorem loadsChainK_seq? : ∀ {Δ : Ctxt jasminDialect} {K : KCtx Δ} {w m : Nat}
    {b : NFProg jasminDialect Δ [.stackArr w m]}, LoadsChainK K b →
    ∀ {Γ₀ : Ctxt jasminDialect} {ts : List JasminTy}
      {k : NFProg jasminDialect (.stackArr w m :: Γ₀) ts}, ChainTailK (fun _ => none) .here k →
    ∀ {Γ : Ctxt jasminDialect} {K' : KCtx Γ} {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ}
      {q : NFProg jasminDialect Γ ts}, KCtx.MapsP ρ K K' → NFProg.seq? k b ρ θ = some q →
      LoadsChainK K' q
  | _, _, _, _, _, .const _ c b hb, _, _, k, hk, _, K', ρ, θ, q, hK, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain rfl := rename?_const he'
      exact .const _ _ _ (loadsChainK_seq? hb hk (KCtx.mapsP_lift hK _) hq')
  | _, _, _, _, _, .free _ e b he hb, _, _, k, hk, _, K', ρ, θ, q, hK, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      exact .free _ _ _ ((rename?_op he').symm ▸ he)
        (loadsChainK_seq? hb hk (KCtx.mapsP_lift hK _) hq')
  | _, _, _, _, _, .load _ a i c b hi hc hb, _, _, k, hk, _, K', ρ, θ, q, hK, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨a', i', hi', rfl⟩ := rename?_load' ρ a i he'
      exact .load _ _ _ c _ (hK i i' c hi' hi) hc
        (loadsChainK_seq? hb hk (KCtx.mapsP_lift hK _) hq')
  | _, _, _, _, _, .store _ v i x c b hi hc hb, _, _, k, hk, _, K', ρ, θ, q, hK, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨v', i', x', -, hi', rfl⟩ := rename?_store' ρ v i x he'
      exact .store _ _ _ _ c _ (hK i i' c hi' hi) hc
        (chainTailK_seq? hb hk (KCtx.mapsP_lift hK _) rfl hq')
  | _, _, _, _, _, .ret _ vs, _, _, k, hk, _, K', ρ, θ, q, hK, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at hq
      obtain ⟨ws, -, hq⟩ := hq
      exact loadsChainK_rename? (loadsChainK_of_chainTailK hk) (KCtx.mapsP_none _ _) hq

/-! ## 2. The field dialect step -/

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open _root_.Hax.FieldTag (FieldMethod fieldLimbs)

/-- **The field dialect step takes one call of a tagged head at a modulus without a narrow
    representation and with a wide template, returned, to a program of the shape
    `LoadsChainK`** at every known constants. -/
theorem fieldDialectStep_loadsChainK {f : String} {m : FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : _root_.Hax.FieldTag.fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p₀ q : NFProg jasminDialect Γ [t]} (hp : CallRet f p₀)
    (hq : (FieldDialectStep.fieldDialectStep Γ [t]).run p₀ = some q) (K : KCtx Γ) :
    LoadsChainK K q := by
  obtain ⟨as, args, rfl⟩ := hp
  have hf := _root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht
  change (if fieldFree (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) then
      some (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) else
    (NFProg.inline? FieldDialectStep.fieldLibD
      (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil)))).bind fun q =>
        if fieldFree q then some q else none) = some q at hq
  simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hq
  obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hq
  simp only [NFProg.inline?, Option.bind_some] at hq0
  split at hq0
  · rename_i b hb
    have ht' := fieldBodyD_rs ht hn hw hb
    obtain rfl : t = .stackArr 64 (fieldLimbs p) := List.head_eq_of_cons_eq ht'
    have hbl := FieldDomComplete.fieldBodyD_loadsChainK ht hn hw hb (fun _ => none)
    split at hif
    · cases hif
      exact loadsChainK_seq? hbl (.ret _ _) (KCtx.mapsP_none _ _) hq0
    · cases hif
  · cases hq0
    simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte] at hif
    cases hif

/-! ## 3. The select lowering -/

/-- **The select lowering keeps a chain tail at constant indices**, along every renaming that
    carries the known constants. -/
theorem chainTailK_lowerSel {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) (K' : KCtx Δ), KCtx.Maps ren K K' →
      ChainTailK K' (ren v) (NFProg.lowerSel k ren) := by
  induction h with
  | const K v c k _ ih =>
      intro Δ ren K' hK
      exact .const _ _ c _ (ih _ _ (KCtx.maps_lift hK _))
  | free K v e k he _ ih =>
      intro Δ ren K' hK
      exact .free _ _ _ _ he (ih _ _ (KCtx.maps_lift hK _))
  | store K v i x c k hi hc _ ih =>
      intro Δ ren K' hK
      exact .store _ _ _ _ c _ (hK i c hi) hc (ih _ _ (KCtx.maps_lift hK _))
  | ret K v => intro Δ ren K' hK; exact .ret _ _

/-- **The select lowering keeps the shape `LoadsChainK`**, along every renaming that carries the
    known constants. -/
theorem loadsChainK_lowerSel {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) (K' : KCtx Δ), KCtx.Maps ren K K' →
      LoadsChainK K' (NFProg.lowerSel p ren) := by
  induction h with
  | const K c k _ ih =>
      intro Δ ren K' hK
      exact .const _ c _ (ih _ _ (KCtx.maps_lift hK _))
  | free K e k he _ ih =>
      intro Δ ren K' hK
      exact .free _ _ _ he (ih _ _ (KCtx.maps_lift hK _))
  | load K a i c k hi hc _ ih =>
      intro Δ ren K' hK
      exact .load _ _ _ c _ (hK i c hi) hc (ih _ _ (KCtx.maps_lift hK _))
  | store K v i x c k hi hc hk =>
      intro Δ ren K' hK
      exact .store _ _ _ _ c _ (hK i c hi) hc
        (chainTailK_lowerSel hk (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | ret K vs => intro Δ ren K' hK; exact .ret _ _

/-- **The select lowering keeps the shape `LoadsChainK`.** -/
theorem loadsChainK_lowerSelects {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    LoadsChainK K (NFProg.lowerSelects p) :=
  loadsChainK_lowerSel h _ K fun _ _ hv => hv

/-! ## 4. Mask elimination, the carry pairs and the legalisation -/

section Narrow

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- **Mask elimination keeps a chain tail at constant indices**, at every facts and every
    renaming that carries the known constants. -/
theorem chainTailK_maskElimGo {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (K' : KCtx Δ)
      (u : Var Δ (.stackArr w m)), KCtx.Maps ren K K' → ren v = u →
      ChainTailK K' u (maskElimGo k A ren) := by
  induction h with
  | const K v c k _ ih =>
      intro Δ A ren K' u hK hu
      exact .const _ _ c _ (ih _ _ _ _ (KCtx.maps_lift hK _) (congrArg Var.there hu))
  | free K v e k he _ ih =>
      intro Δ A ren K' u hK hu
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _ _ _ (KCtx.maps_bind hK _) hu
        · exact .free _ _ _ _ he (ih _ _ _ _ (KCtx.maps_lift hK _) (congrArg Var.there hu))
      · exact .free _ _ _ _ he (ih _ _ _ _ (KCtx.maps_lift hK _) (congrArg Var.there hu))
  | store K v i x c k hi hc _ ih =>
      intro Δ A ren K' u hK hu
      subst hu
      exact .store _ _ _ _ c _ (hK i c hi) hc (ih _ _ _ _ (KCtx.maps_lift hK _) rfl)
  | ret K v => intro Δ A ren K' u hK hu; subst hu; exact .ret _ _

/-- **Mask elimination keeps the shape `LoadsChainK`**, at every facts and every renaming that
    carries the known constants. -/
theorem loadsChainK_maskElimGo {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (K' : KCtx Δ),
      KCtx.Maps ren K K' → LoadsChainK K' (maskElimGo p A ren) := by
  induction h with
  | const K c k _ ih =>
      intro Δ A ren K' hK
      exact .const _ c _ (ih _ _ _ (KCtx.maps_lift hK _))
  | free K e k he _ ih =>
      intro Δ A ren K' hK
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _ _ (KCtx.maps_bind hK _)
        · exact .free _ _ _ he (ih _ _ _ (KCtx.maps_lift hK _))
      · exact .free _ _ _ he (ih _ _ _ (KCtx.maps_lift hK _))
  | load K a i c k hi hc _ ih =>
      intro Δ A ren K' hK
      exact .load _ _ _ c _ (hK i c hi) hc (ih _ _ _ (KCtx.maps_lift hK _))
  | store K v i x c k hi hc hk =>
      intro Δ A ren K' hK
      exact .store _ _ _ _ c _ (hK i c hi) hc
        (chainTailK_maskElimGo hk _ (Ctxt.Hom.lift ren) _ _ (KCtx.maps_lift hK _) rfl)
  | ret K vs => intro Δ A ren K' hK; exact .ret _ _

/-- The weakening past one new binding carries the known constants, the new variable of
    unknown constant. -/
theorem KCtx.mapsP_wk1 {Γ : Ctxt jasminDialect} {s : JasminTy} (K : KCtx Γ) :
    KCtx.MapsP (wk1 (s := s)) K (K.snoc none) := by
  intro v v' c hv hc
  simp only [wk1, Option.some.injEq] at hv
  subst hv
  exact hc

/-- **The insertion of a data binding before a carry-out keeps a chain tail at constant
    indices.** -/
theorem chainTailK_carryInsert {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w' m : Nat}
    {ts : List JasminTy} {t : JasminTy} (w : Nat)
    (h : DialectSignature.ret (d := jasminDialect) (.addCarryHi w) = t)
    (args : HVector (fun t => Var Γ t)
      (DialectSignature.sig (d := jasminDialect) (.addCarryHi w)))
    {v : Var Γ (.stackArr w' m)} {k : NFProg jasminDialect (t :: Γ) ts}
    (hk : ChainTailK (K.snoc none) v.there k) : ChainTailK K v (carryInsert w h args k) := by
  unfold carryInsert
  split
  · rename_i e' k' he hk'
    exact .free _ _ _ _ rfl (.free _ _ _ _ ((rename?_op he).symm ▸ rfl)
      (chainTailK_rename? hk (KCtx.mapsP_lift (KCtx.mapsP_wk1 K) none)
        (by simp [PRen.lift, wk1]) hk'))
  · exact .free _ _ _ _ (by subst h; rfl) hk

/-- **The insertion of a data binding before a carry-out keeps the shape `LoadsChainK`.** -/
theorem loadsChainK_carryInsert {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {t : JasminTy} (w : Nat) (h : DialectSignature.ret (d := jasminDialect) (.addCarryHi w) = t)
    (args : HVector (fun t => Var Γ t)
      (DialectSignature.sig (d := jasminDialect) (.addCarryHi w)))
    {k : NFProg jasminDialect (t :: Γ) ts} (hk : LoadsChainK (K.snoc none) k) :
    LoadsChainK K (carryInsert w h args k) := by
  unfold carryInsert
  split
  · rename_i e' k' he hk'
    exact .free _ _ _ rfl (.free _ _ _ ((rename?_op he).symm ▸ rfl)
      (loadsChainK_rename? hk (KCtx.mapsP_lift (KCtx.mapsP_wk1 K) none) hk'))
  · exact .free _ _ _ (by subst h; rfl) hk

/-- **The carry pairs keep a chain tail at constant indices**, at every key of the binding
    before. -/
theorem chainTailK_carryPairGo {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ prev : Option (Nat × List Nat), ChainTailK K v (carryPairGo prev k) := by
  induction h with
  | const K v c k _ ih => intro prev; exact .const _ _ c _ (ih _)
  | free K v e k he _ ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · exact .free _ _ _ _ he (ih _)
        · exact chainTailK_carryInsert _ _ _ (ih _)
      · exact .free _ _ _ _ he (ih _)
  | store K v i x c k hi hc _ ih => intro prev; exact .store _ _ _ _ c _ hi hc (ih _)
  | ret K v => intro prev; exact .ret _ _

/-- **The carry pairs keep the shape `LoadsChainK`**, at every key of the binding before. -/
theorem loadsChainK_carryPairGo {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ prev : Option (Nat × List Nat), LoadsChainK K (carryPairGo prev p) := by
  induction h with
  | const K c k _ ih => intro prev; exact .const _ c _ (ih _)
  | free K e k he _ ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · exact .free _ _ _ he (ih _)
        · exact loadsChainK_carryInsert _ _ _ (ih _)
      · exact .free _ _ _ he (ih _)
  | load K a i c k hi hc _ ih => intro prev; exact .load _ _ _ c _ hi hc (ih _)
  | store K v i x c k hi hc hk =>
      intro prev
      exact .store _ _ _ _ c _ hi hc (chainTailK_carryPairGo hk _)
  | ret K vs => intro prev; exact .ret _ _

end Narrow

/-- **The region legalisation keeps the shape `LoadsChainK`.** -/
theorem loadsChainK_legalizeRegion {Γ : Ctxt jasminDialect} {K : KCtx Γ} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : LoadsChainK K p) :
    LoadsChainK K (legalizeRegion p) := h

/-! ## 5. The widening of narrow words -/

section Widen

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- **A renaming of the widened context carries the known constants**: the image of the
    widened variable of every variable of known constant `c` has the known constant `c`. -/
def KCtx.MapsW {Γ Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ) (K : KCtx Γ)
    (K' : KCtx Δ) : Prop :=
  ∀ v c, K v = some c → K' (ren (mapVar v)) = some c

/-- The renaming of the continuation of a widened binding of unknown value carries the known
    constants, along a renaming of the target that carries them. -/
theorem KCtx.mapsW_bodyHom_none {Γ Δ Δ' : Ctxt jasminDialect} {u : JasminTy}
    {ren : Ctxt.Hom (widenP.mapCtx Γ) Δ} {K : KCtx Γ} {K' : KCtx Δ} (h : KCtx.MapsW ren K K')
    (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' (widenP.mapTy u)) (K'' : KCtx Δ')
    (hM : KCtx.Maps ren' K' K'') :
    KCtx.MapsW (widenP.bodyHom ren ren' res) (K.snoc (t := u) none) K'' := by
  intro v c hv
  cases v with
  | here => cases hv
  | there v => exact hM _ _ (h v c hv)

/-- The renaming of the continuation of a widened constant binding carries the known
    constants extended by the constant. -/
theorem KCtx.mapsW_bodyHom_const {Γ Δ : Ctxt jasminDialect}
    {ren : Ctxt.Hom (widenP.mapCtx Γ) Δ} {K : KCtx Γ} {K' : KCtx Δ} (h : KCtx.MapsW ren K K')
    (c : Nat) :
    KCtx.MapsW (Δ := .reg 64 :: Δ) (widenP.bodyHom (u := .reg 64) ren (fun x => x.there) .here)
      (K.snoc (some c)) (K'.snoc (some c)) := by
  intro v c' hv
  cases v with
  | here => exact hv
  | there v => exact h v c' hv

/-- **The splice of a block of memory-free operations before continuations that continue a
    chain at constant indices** is a chain tail at constant indices, the continuations taken
    along every renaming that carries the known constants. -/
theorem chainTailK_spliceNF?_maps {w m : Nat} {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)) (u : Var Δ (.stackArr w m)) (K : KCtx Δ),
      ComFree blk →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a) (K'' : KCtx Δ')
        (q' : NFProg jasminDialect Δ' ts), KCtx.Maps ren' K K'' → kont ren' res = some q' →
        ChainTailK K'' (ren' u) q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk kont = some q → ChainTailK K u q
  | _, _, .ret v, kont, u, K, _, hK, _, h => hK _ v K _ (fun _ _ hv => hv) h
  | _, _, .var e blk, kont, u, K, .var _ _ he hb, hK, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .free _ _ _ _ he (chainTailK_spliceNF?_maps blk _ u.there _ hb
        (fun ren' res K'' q'' hM hq => hK _ res K'' q'' (fun v c hv => hM v.there c hv) hq) hq')

/-- **The splice of a block of memory-free operations before continuations of the shape
    `LoadsChainK`** has the shape, the continuations taken along every renaming that carries
    the known constants. -/
theorem loadsChainK_spliceNF?_maps {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)) (K : KCtx Δ),
      ComFree blk →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a) (K'' : KCtx Δ')
        (q' : NFProg jasminDialect Δ' ts), KCtx.Maps ren' K K'' → kont ren' res = some q' →
        LoadsChainK K'' q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk kont = some q → LoadsChainK K q
  | _, _, .ret v, kont, K, _, hK, _, h => hK _ v K _ (fun _ _ hv => hv) h
  | _, _, .var e blk, kont, K, .var _ _ he hb, hK, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .free _ _ _ he (loadsChainK_spliceNF?_maps blk _ _ hb
        (fun ren' res K'' q'' hM hq => hK _ res K'' q'' (fun v c hv => hM v.there c hv) hq) hq')

/-- **The widening keeps a chain tail at constant indices**, along every renaming that carries
    the known constants, at the image of the widened current version. -/
theorem chainTailK_widen {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ) (K' : KCtx Δ)
      (u : Var Δ (.stackArr (wideW w) m)) {q : NFProg jasminDialect Δ (ts.map widenP.mapTy)},
      KCtx.MapsW ren K K' → ren (mapVar v) = u →
      NFProg.map? widenP widenP_regionTypes k ren = some q → ChainTailK K' u q := by
  induction h with
  | const K v c k _ ih =>
      intro Δ ren K' u q hK hu hq
      subst hu
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.regConst (wideW 64) (wideConst 64 c), rfl, .nil⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .const _ _ c _ (ih _ _ _ (KCtx.mapsW_bodyHom_const hK c) rfl hq')
  | free K v e k he _ ih =>
      intro Δ ren K' u q hK hu hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      rcases e with ⟨op, rfl, args⟩
      exact chainTailK_spliceNF?_maps _ _ u K'
        (comFree_rename (comFree_wideOpBlock? op args he hblk) ren)
        (fun ren' res K'' q' hM hq' => ih _ K'' _ (KCtx.mapsW_bodyHom_none hK ren' res K'' hM)
          (by subst hu; rfl) hq') hq
  | store K v i x c k hi hc _ ih =>
      intro Δ ren K' u q hK hu hq
      subst hu
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackStore (wideW _) _, rfl,
          .cons (mapVar v) (.cons (mapVar i) (.cons (mapVar x) .nil))⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .store _ _ _ _ c _ (hK i c hi) hc (ih _ (K'.snoc none) .here
        (KCtx.mapsW_bodyHom_none hK (fun x => x.there) .here _ fun _ _ h => h) rfl hq')
  | ret K v =>
      intro Δ ren K' u q hK hu hq
      subst hu
      rw [NFProg.map?] at hq
      cases hq
      exact .ret _ _

/-- **The widening keeps the shape `LoadsChainK`**, along every renaming that carries the known
    constants. -/
theorem loadsChainK_widen {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ) (K' : KCtx Δ)
      {q : NFProg jasminDialect Δ (ts.map widenP.mapTy)}, KCtx.MapsW ren K K' →
      NFProg.map? widenP widenP_regionTypes p ren = some q → LoadsChainK K' q := by
  induction h with
  | const K c k _ ih =>
      intro Δ ren K' q hK hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.regConst (wideW 64) (wideConst 64 c), rfl, .nil⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .const _ c _ (ih _ _ (KCtx.mapsW_bodyHom_const hK c) hq')
  | free K e k he _ ih =>
      intro Δ ren K' q hK hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      rcases e with ⟨op, rfl, args⟩
      exact loadsChainK_spliceNF?_maps _ _ K'
        (comFree_rename (comFree_wideOpBlock? op args he hblk) ren)
        (fun ren' res K'' q' hM hq' => ih _ K'' (KCtx.mapsW_bodyHom_none hK ren' res K'' hM)
          hq') hq
  | load K a i c k hi hc _ ih =>
      intro Δ ren K' q hK hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackLoad (wideW _) _, rfl,
          .cons (mapVar a) (.cons (mapVar i) .nil)⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .load _ _ _ c _ (hK i c hi) hc
        (ih _ (K'.snoc none)
          (KCtx.mapsW_bodyHom_none hK (fun x => x.there) .here _ fun _ _ h => h) hq')
  | store K v i x c k hi hc hk =>
      intro Δ ren K' q hK hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackStore (wideW _) _, rfl,
          .cons (mapVar v) (.cons (mapVar i) (.cons (mapVar x) .nil))⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .store _ _ _ _ c _ (hK i c hi) hc (chainTailK_widen hk _ (K'.snoc none) .here
        (KCtx.mapsW_bodyHom_none hK (fun x => x.there) .here _ fun _ _ h => h) rfl hq')
  | ret K vs =>
      intro Δ ren K' q hK hq
      rw [NFProg.map?] at hq
      cases hq
      exact .ret _ _

/-- **The narrow-word stages keep the shape `LoadsChainK`** at no known constants of the
    context. -/
theorem loadsChainK_narrowPrep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (h : LoadsChainK (fun _ => none) p) (hq : narrowPrep p = some q) :
    LoadsChainK (fun _ => none) q := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  exact loadsChainK_carryPairGo (loadsChainK_dce (loadsChainK_maskElimGo
    (loadsChainK_widen h _ (fun _ => none) (fun _ _ h => by cases h) h₀) _ _ _
    (KCtx.maps_none _ _))) _

end Widen

/-! ## 6. The range stage -/

section Range

open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (rangeExpr)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop (carriedGo loopRange)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (AEnv)

/-- **The range stage reduces a constant mod `2 ^ 64`**: the binding of `regConst 64 c` is
    rewritten to the binding of `regConst 64 (c % 2 ^ 64)`, so it is kept exactly when
    `c < 2 ^ 64`. -/
theorem rangeExpr_const {Γ : Ctxt jasminDialect} (A : AEnv Γ) (len c : Nat) :
    rangeExpr A len (eConst64 (Γ := Γ) c) = eConst64 (c % 2 ^ 64) := by
  have hlt : c % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have h1 : ((c % 2 ^ 64 : Nat) : Int) / 2 ^ 64 = 0 :=
    Int.ediv_eq_zero_of_lt (by omega) (by omega)
  unfold rangeExpr
  simp only [CatCrypt.Crypto.Optimizer.Rewrite.ComGVN.pairLowOp, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.stageAbs,
    CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.stageOpAbs, ComRange.opAbs,
    RangeDomain.ivConst, RangeDomain.ivLane, RangeDomain.ivSingle?,
    CatCrypt.Crypto.Optimizer.ComRangeFold.pointExpr, h1, zero_mul, sub_zero,
    and_self, Int.natCast_nonneg, Int.toNat_natCast, Option.map_some]
  rfl

/-- **The known constants reduced mod `2 ^ 64`**: every variable of known constant `c` under
    `K` has the known constant `c % 2 ^ 64` under `K'`. -/
def KCtx.ModMaps {Γ : Ctxt jasminDialect} (K K' : KCtx Γ) : Prop :=
  ∀ v c, K v = some c → K' v = some (c % 2 ^ 64)

/-- The known constants reduced mod `2 ^ 64`, extended by a binding. -/
theorem KCtx.modMaps_snoc {Γ : Ctxt jasminDialect} {t : JasminTy} {K K' : KCtx Γ}
    (h : KCtx.ModMaps K K') (o : Option Nat) :
    KCtx.ModMaps (K.snoc (t := t) o) (K'.snoc (o.map (· % 2 ^ 64))) := by
  intro v c hv
  cases v with
  | here =>
      simp only [KCtx.snoc_here] at hv ⊢
      subst hv
      rfl
  | there v => exact h v c hv

/-- **The traversal of the range stage keeps a chain tail at constant indices**, at every
    annotation, at the known constants reduced mod `2 ^ 64`. -/
theorem chainTailK_carriedGo {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ (A : AEnv Γ) (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn)
      (K' : KCtx Γ), KCtx.ModMaps K K' → ChainTailK K' v (carriedGo A len a k) := by
  induction h with
  | const K v c k _ ih =>
      intro A len a K' hK
      simp only [carriedGo]
      rw [rangeExpr_const]
      exact .const _ _ _ _ (ih _ _ _ _ (KCtx.modMaps_snoc hK (some c)))
  | free K v e k he _ ih =>
      intro A len a K' hK
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len e with h | h
      · rw [h]
        exact .free _ _ _ _ he (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
      · exact .free _ _ _ _ h (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
  | store K v i x c k hi hc _ ih =>
      intro A len a K' hK
      simp only [carriedGo]
      exact .store _ _ _ _ (c % 2 ^ 64) _ (hK i c hi) (lt_of_le_of_lt (Nat.mod_le _ _) hc)
        (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
  | ret K v => intro A len a K' hK; exact .ret _ _

/-- **The traversal of the range stage keeps the shape `LoadsChainK`**, at every annotation, at
    the known constants reduced mod `2 ^ 64`. -/
theorem loadsChainK_carriedGo {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ (A : AEnv Γ) (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn)
      (K' : KCtx Γ), KCtx.ModMaps K K' → LoadsChainK K' (carriedGo A len a p) := by
  induction h with
  | const K c k _ ih =>
      intro A len a K' hK
      simp only [carriedGo]
      rw [rangeExpr_const]
      exact .const _ _ _ (ih _ _ _ _ (KCtx.modMaps_snoc hK (some c)))
  | free K e k he _ ih =>
      intro A len a K' hK
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len e with h | h
      · rw [h]
        exact .free _ _ _ he (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
      · exact .free _ _ _ h (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
  | @load Γ K w m ts a i c k hi hc _ ih =>
      intro A len an K' hK
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len
        (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) with h | h
      · rw [h]
        exact .load _ _ _ (c % 2 ^ 64) _ (hK i c hi) (lt_of_le_of_lt (Nat.mod_le _ _) hc)
          (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
      · exact .free _ _ _ h (ih _ _ _ _ (KCtx.modMaps_snoc hK none))
  | store K v i x c k hi hc hk =>
      intro A len a K' hK
      simp only [carriedGo]
      exact .store _ _ _ _ (c % 2 ^ 64) _ (hK i c hi) (lt_of_le_of_lt (Nat.mod_le _ _) hc)
        (chainTailK_carriedGo hk _ _ _ _ (KCtx.modMaps_snoc hK none))
  | ret K vs => intro A len a K' hK; exact .ret _ _

/-- **The range stage keeps the shape `LoadsChainK`**, at every annotation, at the known
    constants reduced mod `2 ^ 64`. -/
theorem loadsChainK_loopRange {Γ : Ctxt jasminDialect} {K K' : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) (hK : KCtx.ModMaps K K')
    (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn) :
    LoadsChainK K' (loopRange a p) :=
  loadsChainK_carriedGo h _ _ _ _ hK

end Range

/-! ## 7. The steps -/

section Steps

open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)

/-- **The select lowering step keeps the shape `LoadsChainK`.** -/
theorem loadsChainK_lowerSelectsStep {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (h : LoadsChainK K p)
    (hq : (lowerSelectsStep Γ ts).run p = some q) : LoadsChainK K q := by
  cases hq
  exact loadsChainK_lowerSelects h

/-- **The range step keeps the shape `LoadsChainK`**, at the known constants reduced mod
    `2 ^ 64`. -/
theorem loadsChainK_synRangeStep {Γ : Ctxt jasminDialect} {K K' : KCtx Γ} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) (hK : KCtx.ModMaps K K')
    (hq : (synRangeStep Γ ts).run p = some q) : LoadsChainK K' q := by
  cases hq
  exact loadsChainK_loopRange h hK _

end Steps

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
