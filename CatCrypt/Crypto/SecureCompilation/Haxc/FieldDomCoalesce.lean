/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomExport

/-!
# The coalescing stages on the exported field domain

The coalescing check `coCfgB` of the gate `regionCoStage` accepts an alias map `ρ` on a body
when `ρ` has no real aliasing (`CoalesceComplete.NoRealAlias`). On the code with the result
copies of an export, the entry conjunct of `NoRealAlias` holds
(`RegionCoStorage.storageDisjoint_entry`), and the remaining conjunct is the absence of
interference `CoalesceComplete.Interf`: at every write of an array name `d`, no other name
of the storage class of `d` under `ρ` is live after the write.

On a straight-line body, a name is live at a position exactly when it is read at a later
position, or after the body, with no write of it in between (`pLive_straight`). Hence
`Interf` holds when every write kills its storage class: every other name of the class of a
written name that is read after the write is written again before that read (`WriteKills`,
`interf_of_writeKills`). The exported code of the field domain has this shape: its array
writes are one chain of stores into the second input array, issued after the last load of
that array, followed by the copy into the result buffer.

## Main definitions

* `CoalesceComplete.Straight`: every successor of a position is the next position.
* `CoalesceComplete.ReadAt`, `CoalesceComplete.NoWriteBetween`: a read of a name at a
  position, and the absence of a write of it in a range of positions.
* `CoalesceComplete.WriteKills`: every write kills the other names of its storage class.
* `FieldCoalesceShape`: the code with the result copies of the webs of a member of the field
  domain is straight-line, and its writes kill their classes under the coalescing alias map.

## Main results

* `CoalesceComplete.pLive_straight`: liveness on a straight-line body.
* `CoalesceComplete.interf_of_writeKills`: no interference on a straight-line body whose
  writes kill their classes.
* `fieldDom_coalesce_of_shape`: on the field domain, from `FieldCoalesceShape`, the gate does
  not refuse at `coCfgB` (stage `G2`) nor at `coEntryFix` (stage `G3`).
* `fieldDom_coCfgB`, `fieldDom_coEntryFix`: the stages `G2` and `G3` with the types of the
  fields of `FieldDomStages`, from `FieldCoalesceShape` on every member.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)

/-- **A straight-line body**: every control-flow successor of a position is the next
    position. -/
def Straight (body : List LinstrRM) : Prop :=
  ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ k', Succ body k i k' → k' = k + 1

/-- The array name `r` is read at the position `j` of `body`: by the instruction at `j`, or
    after the body (`j = body.length`) as a name of `obs`. -/
def ReadAt (body : List LinstrRM) (aa : String → Nat → Option Nat) (obs : List String)
    (j : Nat) (r : String) : Prop :=
  (∃ i, body[j]? = some i ∧ r ∈ rdArr aa i) ∨ (j = body.length ∧ r ∈ obs)

/-- No instruction of `body` at a position in `[k, j)` writes the array name `r`. -/
def NoWriteBetween (body : List LinstrRM) (ao : String → Option Nat) (k j : Nat)
    (r : String) : Prop :=
  ∀ (m : Nat) (i : LinstrRM), k ≤ m → m < j → body[m]? = some i → wrArr ao i ≠ some r

/-- **Every write kills its storage class under `σ`**: at the write of an array name `d` at
    position `k`, every name `r ≠ d` with `σ r = σ d` that is read at a later position `j`
    (or after the body) is written at some position in `[k + 1, j)`. -/
def WriteKills (σ : String → String) (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (obs : List String) : Prop :=
  ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i → wrArr ao i = some d →
    ∀ r, r ≠ d → σ r = σ d → ∀ j, k < j → ReadAt body aa obs j r →
      ¬ NoWriteBetween body ao (k + 1) j r

/-- **Liveness on a straight-line body**: a name live at `k` is read at a position `j ≥ k`,
    or after the body, and not written in `[k, j)`. -/
theorem pLive_straight {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {obs : List String} (hs : Straight body) {k : Nat} {r : String}
    (h : PLive body aa ao obs k r) :
    ∃ j, k ≤ j ∧ ReadAt body aa obs j r ∧ NoWriteBetween body ao k j r := by
  induction h with
  | obs hr => exact ⟨_, le_rfl, .inr ⟨rfl, hr⟩, fun m _ h1 h2 _ => absurd h2 (by omega)⟩
  | read hi hr => exact ⟨_, le_rfl, .inl ⟨_, hi, hr⟩, fun m _ h1 h2 _ => absurd h2 (by omega)⟩
  | step hi hsc hw _ ih =>
    obtain rfl := hs _ _ hi _ hsc
    obtain ⟨j, hj, hR, hN⟩ := ih
    refine ⟨j, by omega, hR, fun m i' h1 h2 hm => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rw [hi] at hm
      cases hm
      exact fun he => hw he.symm
    · exact hN m i' h1 h2 hm

/-- **No interference on a straight-line body whose writes kill their storage classes.** -/
theorem interf_of_writeKills {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs : List String}
    (hs : Straight body) (hw : WriteKills σ body aa ao obs) :
    Interf σ body ao (PLive body aa ao obs) := by
  intro k i hi d hd r hr hne heq
  obtain ⟨j, hj, hR, hN⟩ := pLive_straight hs hr
  exact hw k i d hi hd r hne heq j (by omega) hR hN

end CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (Straight WriteKills
  interf_of_writeKills)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The coalescing shape of an exported code** `r` at the layout `σ` and the result type
    `t`: the code with the result copies is straight-line, and every write kills its storage
    class under the coalescing alias map `regionAliasTab`, with the names read after the code
    the returned arrays. -/
def FieldCoalesceShape (σ : AbiLayout) (t : JasminTy) (r : Exported) : Prop :=
  Straight (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
    ∧ WriteKills (canonMemrefName (regionAliasTab σ exportReg t none r.res
        (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))))
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
      (calleeAAT none) (calleeAOT none)
      (regionCoObs t (regionOut (regionCopy σ exportReg t none r.code r.res) r.res))

/-- **Stages `G2` and `G3` from the coalescing shape**: on a member of the field domain whose
    webs have the shape `FieldCoalesceShape`, the gate `regionCoStage` refuses neither at
    `coCfgB` nor at `coEntryFix`. -/
theorem fieldDom_coalesce_of_shape (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hS : FieldCoalesceShape σ t r) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" ∧
      regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, rfl⟩ := hB
  have hE := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE'⟩ := NarrowWords.narrowPrep_of_exportable q hE
  rw [hq'] at hq''
  cases hq''
  have hc : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hlen : ((nfCtx σ).map NarrowWords.wideTy).length ≤ σ.args.length := by
    rw [List.length_map]
    exact (RegionAllocMapDom.nfCtx_length σ).le
  have hgp : ∀ RA, σ.result = .reg RA →
      X86Backend.DecodePrinted.gpOk (exportReg RA) = true := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    intro RA hRA
    rw [hR] at hRA
    cases hRA
  exact RegionCoStorage.regionCoStage_coalesce_webs_of_interf fname (legalizeRegion q')
    (fieldDom_legalize hE') hc hr0 σ exportReg hlen hgp _ (interf_of_writeKills hS.1 hS.2) b
    cert fname

/-- **Stage `G2`**: when the webs of every member of the field domain have the coalescing
    shape, the gate does not refuse at `coCfgB`. -/
theorem fieldDom_coCfgB
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldCoalesceShape σ t r)
    {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" :=
  (fieldDom_coalesce_of_shape h hB (hS h hB)).1

/-- **Stage `G3`**: when the webs of every member of the field domain have the coalescing
    shape, the gate does not refuse at `coEntryFix`. -/
theorem fieldDom_coEntryFix
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldCoalesceShape σ t r)
    {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" :=
  (fieldDom_coalesce_of_shape h hB (hS h hB)).2

example (S : FieldDomStages)
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldCoalesceShape σ t r) :
    type_of% @S.coCfgB :=
  fun h hB => fieldDom_coCfgB hS (fieldDomB_of_fieldDomB' h) hB

example (S : FieldDomStages)
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldCoalesceShape σ t r) :
    type_of% @S.coEntryFix :=
  fun h hB => fieldDom_coEntryFix hS (fieldDomB_of_fieldDomB' h) hB

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
