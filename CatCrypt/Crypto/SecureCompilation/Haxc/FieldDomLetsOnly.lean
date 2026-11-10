/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCoalesceShape
import CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps

/-!
# The narrowed output of the chain on the field domain is built of bindings

A program is region-free (`regionFreeB`) when it has no counted loop, no conditional and no
exit-flag loop; it may have bindings and calls. Every pass of the chain and of the narrow-word
stages keeps region-freeness: the passes map a binding to bindings (a block of a conversion is
a straight-line `Com`) and a call to a call or to the inlined body of its head, and the field
dialect step inlines bodies that are themselves region-free (the raised body binds one field
operation, and its lowerings are conversions). The translation of a member of the field domain
is one binding of the call of its head, so it is region-free; the chain output on the field
domain is region-free and has no call (`fieldDom_callFree`), hence is built of bindings only
(`letsOnlyB`), and so is its narrowed form (`fieldLetsOnly`).

## Main definitions

* `regionFreeB`: a structured program without counted loop, conditional or exit-flag loop.

## Main results

* `regionFreeB_rename?`, `regionFreeB_seq?`, `regionFreeB_inline?`, `regionFreeB_dce`,
  `regionFreeB_lowerSel`, `regionFreeB_nfGo`, `regionFreeB_carriedGo`, `regionFreeB_map?`:
  the generic passes keep region-freeness.
* `fieldDialectStep_regionFreeB`: the field dialect step keeps it, since the lowered bodies
  are region-free (`raiseBody_regionFreeB`, `lowerBody_regionFreeB`, `fieldBodyD_regionFreeB`).
* `regionFreeB_narrowPrep`: so do the narrow-word stages (`regionFreeB_maskElimGo`,
  `regionFreeB_carryPairGo`).
* `regionFreeB_flatSame`, `nfToCatExt_regionFreeB`: so do tuple flattening and the
  translation to `catCryptDialect`.
* `extChain_regionFreeB_of_wide`: the chain keeps region-freeness on a source whose field calls
  are tagged at wide moduli.
* `fieldDom_haxToNF_regionFreeB`, `fieldDom_chain_regionFreeB`: the translation and the chain
  output on the field domain are region-free.
* `letsOnlyB_of_regionFreeB`: a region-free program without call is built of bindings only.
* `fieldLetsOnly`: `FieldLetsOnly e σ` on every member of the field domain.
* `fieldDom_coalesce_of_writeKills`: stages `G2` and `G3` on the field domain from
  `WriteKills` alone.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open Ctxt (Var)

/-! ## 1. Region-free programs -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **A region-free program**: bindings and calls ending in `ret`, without a counted loop, a
    conditional or an exit-flag loop. -/
def regionFreeB : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => regionFreeB k
  | _, _, .call _ _ k => regionFreeB k
  | _, _, _ => false

/-- An embedded straight-line program is region-free. -/
theorem regionFreeB_ofCom : {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
    regionFreeB (NFProg.ofCom c) = true
  | _, _, .ret _ => rfl
  | _, _, .var _ c => regionFreeB_ofCom c

/-- A renamed program is region-free exactly when the source is. -/
theorem regionFreeB_rename? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {q : NFProg d Δ ts}, NFProg.rename? f p = some q →
      regionFreeB q = regionFreeB p := by
  induction p with
  | ret vs =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, -, rfl⟩ := h
      rfl
  | var e k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [regionFreeB, ih hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      rfl
  | call g args k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [regionFreeB, ih hk]

/-- The splice of a region-free body and a region-free continuation is region-free. -/
theorem regionFreeB_seq? {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts}, NFProg.seq? k b ρ θ = some q →
      regionFreeB b = true → regionFreeB k = true → regionFreeB q = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [regionFreeB_rename? k h, hk]
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      exact (ih k hb' hb hk : regionFreeB b' = true)
  | forLoop => intro Γ₀ ts k Γ ρ θ q _ hb _; simp [regionFreeB] at hb
  | ifThenElse => intro Γ₀ ts k Γ ρ θ q _ hb _; simp [regionFreeB] at hb
  | whileLoop => intro Γ₀ ts k Γ ρ θ q _ hb _; simp [regionFreeB] at hb
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      exact (ih k hb' hb hk : regionFreeB b' = true)

/-- **Inlining keeps region-freeness** at a library without operation bodies whose call bodies
    are region-free. -/
theorem regionFreeB_inline? (L : InlineLib d) (hL : ∀ o, L.op o = none)
    (hb : ∀ f as rs b, L.call f as rs = some b → regionFreeB b = true)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hp : regionFreeB p = true) :
    ∀ {q : NFProg d Γ ts}, NFProg.inline? L p = some q → regionFreeB q = true := by
  induction p with
  | ret vs =>
      intro q h
      cases h
      rfl
  | var e k ih =>
      intro q h
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨o, rfl, args⟩ := e
      simp only [NFProg.inlineVar, hL] at h
      cases h
      exact (ih hp hk : regionFreeB k' = true)
  | forLoop => intro q _; simp [regionFreeB] at hp
  | ifThenElse => intro q _; simp [regionFreeB] at hp
  | whileLoop => intro q _; simp [regionFreeB] at hp
  | call f args k ih =>
      intro q h
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i b hbb
        exact regionFreeB_seq? b k' h (hb _ _ _ _ hbb) (ih hp hk)
      · cases h
        exact (ih hp hk : regionFreeB k' = true)

/-- **Dead-binding elimination keeps region-freeness.** -/
theorem regionFreeB_dce {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : regionFreeB p = true) : regionFreeB (NFProg.dce p) = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        rw [regionFreeB_rename? _ hk']
        exact ih hp
      · exact (ih hp : regionFreeB (NFProg.dce k) = true)
  | forLoop => simp [regionFreeB] at hp
  | ifThenElse => simp [regionFreeB] at hp
  | whileLoop => simp [regionFreeB] at hp
  | call _ _ _ ih => exact (ih hp : regionFreeB _ = true)

variable [DialectDenoteM d Option] [HasSelect d] in
/-- **The select lowering keeps region-freeness**, along every renaming. -/
theorem regionFreeB_lowerSel {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ), regionFreeB p = true →
      regionFreeB (NFProg.lowerSel p ren) = true := by
  induction p with
  | ret => intro Δ ren _; rfl
  | var e k ih => intro Δ ren hp; exact ih _ hp
  | forLoop => intro Δ ren hp; simp [regionFreeB] at hp
  | ifThenElse => intro Δ ren hp; simp [regionFreeB] at hp
  | whileLoop => intro Δ ren hp; simp [regionFreeB] at hp
  | call f args k ih => intro Δ ren hp; exact ih _ hp

end Generic

/-- **The traversal of the e-graph pass keeps region-freeness.** -/
theorem regionFreeB_nfGo {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]
    (R : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.RuleSet d) {Γ Δ : Ctxt d}
    {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S) (p : NFProg d Γ ts) :
    regionFreeB (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo R ρ S p) = regionFreeB p := by
  induction p generalizing Δ S with
  | ret => rfl
  | var e k ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo]
      split <;> simp only [regionFreeB, ih]
  | forLoop => rfl
  | ifThenElse => rfl
  | whileLoop => rfl
  | call _ _ _ ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, regionFreeB, ih]

/-- **The traversal of the range stage keeps region-freeness**, at every annotation. -/
theorem regionFreeB_carriedGo : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn)
    (p : NFProg jasminDialect Γ ts),
    regionFreeB (CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.carriedGo A len a p) =
      regionFreeB p
  | _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, .var _ k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.carriedGo, regionFreeB,
        regionFreeB_carriedGo _ _ _ k]
  | _, _, _, _, _, .forLoop .. => rfl
  | _, _, _, _, _, .ifThenElse .. => rfl
  | _, _, _, _, _, .whileLoop .. => rfl
  | _, _, _, _, _, .call _ _ k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.carriedGo, regionFreeB,
        regionFreeB_carriedGo _ _ _ k]

section MapRegions

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- A block spliced before continuations that return region-free programs gives a
    region-free program. -/
theorem regionFreeB_spliceNF? {ts : List d'.Ty} :
    {Δ : Ctxt d'} → {a : d'.Ty} → (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (q : NFProg d' Δ' ts),
      k ren res = some q → regionFreeB q = true) →
    ∀ {q : NFProg d' Δ ts}, NFProg.spliceNF? blk k = some q → regionFreeB q = true
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact regionFreeB_spliceNF? blk _ (fun ren res q hq => hk _ res q hq) hq'

/-- **The conversion `map?` keeps region-freeness**: it lowers a binding to a straight-line
    block and keeps a call. -/
theorem regionFreeB_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : regionFreeB p = true) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) {q : NFProg d' Δ (ts.map P.mapTy)},
      NFProg.map? P hT p ren = some q → regionFreeB q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact regionFreeB_spliceNF? _ _ (fun ren' res q' hq' => ih hp _ hq') h
  | forLoop => intro Δ ren q _; simp [regionFreeB] at hp
  | ifThenElse => intro Δ ren q _; simp [regionFreeB] at hp
  | whileLoop => intro Δ ren q _; simp [regionFreeB] at hp
  | call f args k ih =>
      intro Δ ren q h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (ih hp _ hk : regionFreeB k' = true)

end MapRegions

/-! ## 2. The field dialect step -/

section FieldDialect

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect

/-- **A raised body is region-free**: it binds one field operation. -/
theorem raiseBody_regionFreeB {f : String} {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (h : FieldRaise.raiseBody f as rs = some b) :
    regionFreeB b = true := by
  have hw : ∀ m p r b', FieldRaise.raiseWord m p as rs r = some b' → regionFreeB b' = true := by
    intro m p r b' hb
    unfold FieldRaise.raiseWord at hb
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      cases m <;> rfl
    · cases hb
  unfold FieldRaise.raiseBody at h
  split at h
  · rename_i m p _
    have ha : ∀ b', FieldRaise.raiseArr m p as rs = some b' → regionFreeB b' = true := by
      intro b' hb
      unfold FieldRaise.raiseArr at hb
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        cases m <;> rfl
      · cases hb
    split at h
    · exact hw _ _ _ b h
    · exact ha b h
    · exact hw _ _ _ b h
    · cases h
  · split at h
    · split at h
      · exact hw _ _ _ b h
      · cases h
    · cases h

/-- The inclusion into `jasField` keeps region-freeness. -/
theorem regionFreeB_embed {Γ : Ctxt jasPf} {ts : List jasPf.Ty} (q : NFProg jasPf Γ ts) :
    regionFreeB (FieldRaise.embed q) = regionFreeB q := by
  induction q with
  | ret => rfl
  | var e k ih => exact ih
  | forLoop => rfl
  | ifThenElse => rfl
  | whileLoop => rfl
  | call _ _ _ ih => exact ih

/-- The forwarding of loads keeps region-freeness. -/
theorem regionFreeB_fwdLoad1Go {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      regionFreeB (NFFwdLoad1.fwdLoad1Go p K ren) = regionFreeB p := by
  induction p with
  | ret => intro Δ K ren; rfl
  | var e k ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact ih _ _
      · exact ih _ _
  | forLoop => intro Δ K ren; rfl
  | ifThenElse => intro Δ K ren; rfl
  | whileLoop => intro Δ K ren; rfl
  | call _ _ _ ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, regionFreeB, ih]

/-- A carried program is region-free exactly when the program is. -/
theorem regionFreeB_castNF {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') (q : NFProg jasminDialect Γ ts) :
    regionFreeB (castNF hΓ hts q) = regionFreeB q := by
  subst hΓ hts
  rfl

/-- A lowered body of a region-free body is region-free. -/
theorem lowerBody_regionFreeB {as rs : List JasminTy}
    {r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)} (hr : regionFreeB r₁ = true)
    {b : NFProg jasminDialect as rs} (hb : lowerBody as rs r₁ = some b) :
    regionFreeB b = true := by
  obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
  refine regionFreeB_dce (d := jasminDialect) _ ?_
  unfold NFFwdLoad1.fwdLoad1
  rw [regionFreeB_fwdLoad1Go, regionFreeB_castNF]
  refine regionFreeB_map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes
    _ ?_ _ hs₃
  exact regionFreeB_map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
    r₁ hr _ hs₂

/-- **A lowered body is region-free.** -/
theorem fieldBodyD_regionFreeB {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : fieldBodyD f as rs = some b) :
    regionFreeB b = true := by
  obtain ⟨-, r₁, hr₁, hb⟩ := fieldBodyD_some hb
  exact lowerBody_regionFreeB (raiseBody_regionFreeB hr₁) hb

/-- **The field dialect step keeps region-freeness.** Inlining keeps it, since the lowered
    bodies are region-free (`fieldBodyD_regionFreeB`). -/
theorem fieldDialectStep_regionFreeB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hp : regionFreeB p = true)
    (hf : (fieldDialectStep Γ ts).run p = some q) : regionFreeB q = true := by
  change (if fieldFree p then some p else _) = some q at hf
  split at hf
  · cases hf
    exact hp
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · cases hif
      exact regionFreeB_inline? fieldLibD (fun _ => rfl)
        (fun _ _ _ b hb => fieldBodyD_regionFreeB hb) p hp hq0
    · cases hif

end FieldDialect

/-! ## 3. The narrow-word stages -/

section Narrow

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- Mask elimination keeps region-freeness. -/
theorem regionFreeB_maskElimGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ),
      regionFreeB (maskElimGo p A ren) = regionFreeB p := by
  induction p with
  | ret vs => intro Δ A ren; rfl
  | var e k ih =>
      intro Δ A ren
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _
        · exact ih _ _
      · exact ih _ _
  | forLoop => intro Δ A ren; rfl
  | ifThenElse => intro Δ A ren; rfl
  | whileLoop => intro Δ A ren; rfl
  | call f args k ih => intro Δ A ren; exact ih _ _

/-- The carry pairs keep region-freeness: an inserted binding is a binding, and the weakening
    keeps the rest. -/
theorem regionFreeB_carryPairGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ prev : Option (Nat × List Nat), regionFreeB (carryPairGo prev p) = regionFreeB p := by
  induction p with
  | ret vs => intro prev; rfl
  | var e k ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · simp only [regionFreeB, ih]
        · unfold carryInsert
          split
          · rename_i e' k' he hk
            simp only [regionFreeB, regionFreeB_rename? _ hk, ih]
          · simp only [regionFreeB, ih]
      · simp only [regionFreeB, ih]
  | forLoop => intro prev; rfl
  | ifThenElse => intro prev; rfl
  | whileLoop => intro prev; rfl
  | call fn args k ih =>
      intro prev
      simp only [carryPairGo, regionFreeB, ih]

/-- **The narrow-word stages keep region-freeness.** -/
theorem regionFreeB_narrowPrep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (hp : regionFreeB p = true) (hq : narrowPrep p = some q) : regionFreeB q = true := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  rw [carryPair, regionFreeB_carryPairGo]
  refine regionFreeB_dce _ ?_
  rw [maskElim, regionFreeB_maskElimGo]
  exact regionFreeB_map? widenP widenP_regionTypes p hp _ h₀

end Narrow

/-! ## 4. The front half of the chain -/

section Front

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-- Tuple flattening keeps region-freeness. -/
theorem regionFreeB_flatProg {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ) (q : NFProg nfDialect Δ (flatCtx ts)),
      flatProg p ren = some q → regionFreeB p = true → regionFreeB q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q hq _
      rw [flatProg] at hq
      cases hq
      rfl
  | var e k ih =>
      obtain ⟨op, rfl, args⟩ := e
      intro Δ ren q hq hp
      rw [flatProg] at hq
      cases hT : tupleHom? ren op args with
      | some R =>
          simp only [hT] at hq
          exact ih _ q hq hp
      | none =>
          simp only [hT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
          obtain ⟨args', _, R, _, k', hk, rfl⟩ := hq
          exact (ih _ k' hk hp : regionFreeB k' = true)
  | forLoop => intro _ _ _ _ hp; simp [regionFreeB] at hp
  | ifThenElse => intro _ _ _ _ hp; simp [regionFreeB] at hp
  | whileLoop => intro _ _ _ _ hp; simp [regionFreeB] at hp
  | call f args k ih =>
      intro Δ ren q hq hp
      rw [flatProg] at hq
      simp only [Option.map_eq_some_iff] at hq
      obtain ⟨k', hk, rfl⟩ := hq
      exact (ih _ k' hk hp : regionFreeB k' = true)

/-- A program cast along equal contexts and result types is region-free exactly when the
    program is. -/
theorem regionFreeB_cast {Γ Γ' : Ctxt nfDialect} {ts ts' : List NfTy} (hΓ : Γ' = Γ)
    (hts : ts' = ts) (e : NFProg nfDialect Γ' ts' = NFProg nfDialect Γ ts)
    (q : NFProg nfDialect Γ' ts') : regionFreeB (cast e q) = regionFreeB q := by
  subst hΓ hts
  rfl

/-- **Tuple flattening at a context without tuples keeps region-freeness.** -/
theorem regionFreeB_flatSame {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p q : NFProg nfDialect Γ ts} (hq : flatSame p = some q) (hp : regionFreeB p = true) :
    regionFreeB q = true := by
  unfold flatSame at hq
  split at hq
  · rename_i h
    obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [regionFreeB_cast (flatCtx_of_noTuple h.1) (flatCtx_of_noTuple h.2)]
    exact regionFreeB_flatProg p _ q0 hq0 hp
  · cases hq

/-- The bindings of a translated operation keep the region-freeness of the continuation. -/
theorem emitRes_regionFreeB {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), cont σ' = some q → regionFreeB q = true) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ)
      (q : NFProg catCryptDialect Δ (ts.map catTy)), emitRes cont h res σ = some q →
      regionFreeB q = true
  | _, _, _, .rd _, _, q, hq => hcont _ q hq
  | _, _, _, .expr _, _, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hcont _ k' hk'
  | _, _, _, .expr1 _ _, _, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hcont _ k' hk'
  | _, _, h, .bind _ _ rest, σ, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact emitRes_regionFreeB hcont h rest σ.wk k' hk'

/-- The bindings of `pinAll` keep the region-freeness of the program `k` gives. -/
theorem pinAll_regionFreeB {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)) (q : NFProg catCryptDialect Δ' us),
      k σ' ws = some q → regionFreeB q = true)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (q : NFProg catCryptDialect Δ us) (h : pinAll k σ rs = some q) : regionFreeB q = true :=
  pinAll_elim (M := fun {_} _ _ q => regionFreeB q = true)
    (fun σ _ ws q _ hq => hk σ ws q hq) (fun _ _ _ _ _ ih => ih) σ rs q h

/-- **The translation keeps region-freeness**: a binding translates to bindings and calls. -/
theorem nfToCatExt_regionFreeB (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hp : regionFreeB p = true) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt D p σ = some q → regionFreeB q = true := by
  induction p with
  | ret vs =>
      intro Δ σ q h
      refine pinAll_regionFreeB ?_ σ _ q h
      intro _ _ _ q' hq'
      cases hq'
      rfl
  | var e k ih =>
      intro Δ σ q h
      have hk : regionFreeB k = true := hp
      obtain ⟨op, rfl, args⟩ := e
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some q at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        exact emitRes_regionFreeB (fun σ' q' hq' => ih hk σ' q' hq') rfl res σ q h
      · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨g, bs, rds⟩ := c
        dsimp only at h
        unfold emitCall at h
        refine pinAll_regionFreeB ?_ σ rds q h
        intro _ _ _ q' hq'
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq'
        exact (ih hk _ k' hk' : regionFreeB k' = true)
  | forLoop => intro _ _ _ _; simp [regionFreeB] at hp
  | ifThenElse => intro _ _ _ _; simp [regionFreeB] at hp
  | whileLoop => intro _ _ _ _; simp [regionFreeB] at hp
  | call f args k _ =>
      intro Δ σ q h
      cases h

end Front

/-- **A region-free program without call is built of bindings only.** -/
theorem letsOnlyB_of_regionFreeB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hr : regionFreeB p = true) (hc : p.callFree = true) :
    letsOnlyB p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hr hc
  | forLoop => simp [regionFreeB] at hr
  | ifThenElse => simp [regionFreeB] at hr
  | whileLoop => simp [regionFreeB] at hr
  | call => simp [NFProg.callFree] at hc

/-! ## 5. The field domain -/

section Domain

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (callsLoopsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.Hax.ImpToNF (entryEnv NfEnv)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs)

/-- **The chain keeps region-freeness on a source whose field calls are tagged at moduli of
    at least `2^31`**: the montify pass returns its input on such a source
    (`montifyPass_of_wideTag`), and every other step keeps region-freeness. -/
theorem extChain_regionFreeB_of_wide {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]} (h : (extChain [] Γ t).run p = some q)
    (hp : opsNB wideOpB p = true) (hr : regionFreeB p = true) : regionFreeB q = true := by
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr', r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 at hp1
  change (if outTyB t then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor [] p3) p3 TRd.id = some r at hr'
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1; cases hj3; cases hj4; cases hj5
  have hab : NFProg.abortFree NfOp.isAbort p = true :=
    FrontComplete.abortFree_of_opsNB (fun o ho => by
      simp only [wideOpB, Bool.and_eq_true, Bool.not_eq_true'] at ho
      exact ho.1) p hp
  rw [NFProg.abortElim_of_abortFree _ p hab] at hp1
  -- the montify pass is the identity, as in `extChain_callFree_of_wide`
  have hf : opsNB (fun o => !NFFlattenTuples.opIsTuple o && wideOpB o) p1 = true :=
    FrontComplete.opsNB_flatSame (W := fun _ => false) (fun _ h => h) hp1
      (FrontComplete.opsNB_mono_loop (fun o h => by simp [h]) (fun _ h => h) _ hp)
  have hd : opsNB wideOpB p1.dce = true :=
    FrontComplete.opsNB_dce _ (FrontComplete.opsNB_mono_loop
      (fun o h => by simp only [Bool.and_eq_true] at h; exact h.2) (fun _ h => h) _ hf)
  have hD : ∀ d ∈ fieldDeclsFor [] p1.dce, wideTagB d.name = true := by
    intro d hd'
    simp only [fieldDeclsFor, List.filter_nil, List.nil_append] at hd'
    exact fieldDeclsOf_wide _ hd d hd'
  have h0 : callsLoopsAll (fun f _ _ => wideTagB f) (fun _ => true) r = true :=
    ExportChainOps.callsLoopsAll_of_loops _ _ r (ExportChainOps.callsLoopsAll_true r)
      fun f as rs hc => by
        obtain ⟨d, hd', rfl, -⟩ := nfToCatExt_calls _ _ TRd.id r hr' f as rs hc
        exact hD d hd'
  have h1 := (ExportChainOps.callsLoopsAll_nfGo (d := CatCryptDialect.catCryptDialect) _ _
    catRules (Ctxt.Hom.id _) (∅, ∅) r).trans h0
  have h2 := ExportChainOps.callsLoopsAll_map? catToJasmin catToJasmin_regionTypes
    (fun f _ _ => wideTagB f) (fun _ => true) _ h1 _ hj
  have hm := montifyPass_of_wideTag (Γ := mapCtx (List.map catTy Γ))
    (ts := [mapTy (catTy t)]) j h2
  rw [hm] at hj2
  -- region-freeness through the steps
  have g1 : regionFreeB p1 = true := regionFreeB_flatSame hp1 hr
  have g2 : regionFreeB r = true := nfToCatExt_regionFreeB _ _ (regionFreeB_dce _ g1) _ _ hr'
  have g3 : regionFreeB (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF catRules r)
      = true := by
    unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    rw [regionFreeB_nfGo (d := CatCryptDialect.catCryptDialect)]
    exact g2
  have g4 : regionFreeB j = true := regionFreeB_map? catToJasmin catToJasmin_regionTypes _ g3 _ hj
  have g5 : regionFreeB j2 = true := fieldDialectStep_regionFreeB g4 hj2
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.loopRange
  rw [regionFreeB_nfGo (d := jasminDialect), regionFreeB_carriedGo]
  exact regionFreeB_lowerSel _ _ g5

/-- The translation of the literal `let t := f(x, a); t` is region-free. -/
theorem impToNF_letCall_regionFreeB {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (f a : String)
    (T : NfTy) (vx va : Var Γ T) (hx : σ.lookup "x" = some ⟨T, vx⟩)
    (ha : σ.lookup a = some ⟨T, va⟩) (hf : f ≠ "repeat")
    (hs : CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf f [T, T] = some T) :
    ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf none σ
      (.letBind "t" (.app f [.var "x", .var a]) (.var "t")) = some o ∧ o.t = T ∧
      regionFreeB o.prog = true := by
  simp [CatCrypt.Crypto.Hax.ImpToNF.impToNF, CatCrypt.Crypto.Hax.ImpToNF.impArgsNF,
    CatCrypt.Crypto.Hax.ImpToNF.atomOut, hx, ha, hf, hs, NfEnv.lookup_cons,
    CatCrypt.Crypto.Hax.ImpToNF.Out.comp, CatCrypt.Crypto.Hax.ImpToNF.Out.prog,
    regionFreeB, CatCrypt.Crypto.Hax.ImpToNF.mkEN, NFPre.plug, NFPre.append]

/-- **The translation of a member of the field domain is region-free**: it binds the call of
    the head of the member. -/
theorem fieldDom_haxToNF_regionFreeB {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB e σ = true) {T : NfTy}
    {p0 : NFProg nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (abiEntry σ)) [T]}
    (hp : haxToNF σ (HaxModule.single e) = some ⟨T, p0⟩) : regionFreeB p0 = true := by
  unfold fieldDomB at h
  split at h
  · rename_i k n hkn
    obtain ⟨m, p, hm, h64, hok, ht, rfl, he⟩ := fieldDomE_tag hkn
    simp only [fieldAbiB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨hargs, hc⟩, -⟩, -⟩, -⟩, -⟩ := h
    have hfr := fieldLit_front m p k
    have hsh : CatCrypt.Crypto.Hax.haxFrontShapeOk e = true := by
      rw [CatCrypt.Crypto.Hax.haxFrontShapeOk, he]
      exact hfr.1
    have hbody : nfBody e = fieldLit m p k := by
      rw [nfBody, he]
      exact hfr.2
    have hbin : m.binary = true := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | h <;> first | rfl | cases h
    have hsig := hax64SigOf_fieldHead hbin h64 hok ht
    have hk : k = 2 ∨ k = 1 := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      grind
    have hI : ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf
        none (entryEnv (abiEntry σ)) (fieldLit m p k) = some o ∧
          o.t = NfTy.arr (fieldLimbs p) (.word 64) ∧ regionFreeB o.prog = true := by
      rcases hk with rfl | rfl
      · rw [abiEntry_fieldAbi_two hargs]
        exact impToNF_letCall_regionFreeB (entryEnv _) (fieldHead m p) "y" _ Var.here
          Var.here.there (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
      · rw [abiEntry_fieldAbi_one hargs]
        exact impToNF_letCall_regionFreeB (entryEnv _) (fieldHead m p) "x" _ Var.here Var.here
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
    obtain ⟨o, ho, hot, hro⟩ := hI
    have hp' : haxToNF σ (HaxModule.single e) = some ⟨o.t, o.prog⟩ := by
      rw [haxToNF_single, hc, bindConsts_nil]
      simp [nfSrcProg, hsh, hbody, ho, hot, entryResOk, outTyB]
    rw [hp] at hp'
    simp only [Option.some.injEq, Sigma.mk.injEq] at hp'
    obtain ⟨rfl, hq⟩ := hp'
    cases hq
    exact hro
  · cases h

/-- **The output of the chain on the field domain is region-free.** -/
theorem fieldDom_chain_regionFreeB {e : _root_.Hax.TExpr} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (h : fieldDomB e σ = true)
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t, q⟩) : regionFreeB q = true := by
  obtain ⟨T, p0, hp, hops⟩ := fieldDom_haxToNF h
  have hr := fieldDom_haxToNF_regionFreeB h hp
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, Option.map_eq_some_iff] at hq
  obtain ⟨q', hq', heq⟩ := hq
  cases heq
  rw [linkedDecls_single] at hq'
  exact extChain_regionFreeB_of_wide hq' hops hr

/-- **The narrowed output of the chain on the field domain is built of bindings only**: it is
    region-free (`fieldDom_chain_regionFreeB`, `regionFreeB_narrowPrep`) and has no call
    (`fieldDom_callFree`, `NarrowWords.callFree_narrowPrep`). -/
theorem fieldLetsOnly {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true) :
    FieldLetsOnly e σ := by
  intro t0 q q' hq hq'
  exact letsOnlyB_of_regionFreeB q' (regionFreeB_narrowPrep (fieldDom_chain_regionFreeB h hq) hq')
    ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))

/-- **Stages `G2` and `G3` from `WriteKills` alone**: `fieldDom_coalesce_of_letsOnly` with
    `FieldLetsOnly` discharged by `fieldLetsOnly`. -/
theorem fieldDom_coalesce_of_writeKills {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String}
    {b : Lcmd} {t : JasminTy} {r : Exported}
    {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hW : X86Backend.CoalesceComplete.WriteKills
      (canonMemrefName (regionAliasTab σ exportReg t none r.res
        (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))))
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
      (calleeAAT none) (calleeAOT none)
      (regionCoObs t (regionOut (regionCopy σ exportReg t none r.code r.res) r.res))) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" ∧
      regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" :=
  fieldDom_coalesce_of_letsOnly h hB (fieldLetsOnly h) hW

end Domain

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
