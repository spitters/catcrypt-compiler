/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCoalesce

/-!
# The straight-line shape of the exported field domain

A structured program built of bindings only, without a loop, a conditional or a call
(`letsOnlyB`), is exported to code whose every instruction is an `Lopn`
(`exportR_isLopn_of_letsOnlyB`). The webs and the result copies keep this
(`isLopn_regionCoCode_webs`), and a body of `Lopn` instructions is straight-line
(`straight_of_isLopn`). On the field domain this reduces the first conjunct of
`FieldCoalesceShape` to the statement that the narrowed output of the chain is built of bindings
only (`FieldLetsOnly`).

## Main definitions

* `letsOnlyB`: a structured program built of bindings only.
* `FieldLetsOnly`: the narrowed output of the chain on a typed expression is built of bindings
  only.

## Main results

* `succ_of_isLopn`, `straight_of_isLopn`: an `Lopn` instruction falls through to the next
  position, and a body of `Lopn` instructions is straight-line.
* `exportR_isLopn_of_letsOnlyB`: the export of a program built of bindings only is a list of
  `Lopn` instructions.
* `isLopn_regionCoCode_webs`: so is the code with the result copies of its webs.
* `fieldDom_straight`: on the field domain, the code with the result copies of the webs is
  straight-line when the narrowed output of the chain is built of bindings only.
* `fieldDom_coalesce_of_letsOnly`: stages `G2` and `G3` from `FieldLetsOnly` and `WriteKills`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (Straight WriteKills Succ
  SuccA armOf)

/-! ## 1. Straight-line code of `Lopn` instructions -/

/-- **An `Lopn` instruction falls through**: its only successor is the next position. -/
theorem succ_of_isLopn {body : List LinstrRM} {k k' : Nat} {i : LinstrRM} (h : IsLopn i)
    (hs : Succ body k i k') : k' = k + 1 := by
  obtain ⟨ds, o, ss, hi⟩ := h
  unfold Succ armOf at hs
  grind [SuccA, JasminLsemMemFlagGuard.flagCondCC?]

/-- **A body of `Lopn` instructions is straight-line.** -/
theorem straight_of_isLopn {body : List LinstrRM} (h : ∀ i ∈ body, IsLopn i) :
    Straight body := by
  intro k i hk k' hs
  exact succ_of_isLopn (h i (List.mem_of_getElem? hk)) hs

/-! ## 2. The export of a program built of bindings only -/

/-- **A structured program built of bindings only**: a list of bindings ending in `ret`, without
    a loop, a conditional or a call. -/
def letsOnlyB : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => letsOnlyB k
  | _, _, _ => false

/-- **The export of a program built of bindings only is a list of `Lopn` instructions.** -/
theorem exportR_isLopn_of_letsOnlyB {nArgs : Nat} {fn : String} {I : LprogIsa.IsaData}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hp : letsOnlyB p = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r → ∀ i ∈ r.code, IsLopn i := by
  induction p with
  | ret vs =>
      intro d n r hr
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      intro i hi
      exact nomatch hi
  | var e k ih =>
      intro d n r hr
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk, rfl⟩ := hr
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact isLopn_bindOps nArgs e d i hi
      · exact ih hp _ _ _ hk i hi
  | forLoop => simp [letsOnlyB] at hp
  | ifThenElse => simp [letsOnlyB] at hp
  | whileLoop => simp [letsOnlyB] at hp
  | call => simp [letsOnlyB] at hp

/-- **The code with the result copies of the webs of an export of `Lopn` instructions is a list
    of `Lopn` instructions.** -/
theorem isLopn_regionCoCode_webs {r0 : Exported} (h : ∀ i ∈ r0.code, IsLopn i)
    (σ : AbiLayout) (nm : String → String) (t : JasminTy) (ex : List String)
    (cp : Option (String × String × Nat)) :
    ∀ i ∈ regionCoCode σ nm t (regionWebsAt ex none r0).code (regionWebsAt ex none r0).res cp,
      IsLopn i := by
  have hw : ∀ i ∈ (regionWebsAt ex none r0).code, IsLopn i :=
    forall_mem_regionWebs (fun σ _ hi => RegionExportDefInitSort.isLopn_renArr σ hi) ex r0 _ _ h
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact hw i hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact hw i hi
      · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact RegionExportDefInit.isLopn_resCopyCode _ _ _ i hi

/-! ## 3. The field domain -/

/-- **The narrowed output of the chain on `e` under `σ` is built of bindings only.** -/
def FieldLetsOnly (e : _root_.Hax.TExpr) (σ : AbiLayout) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ → NarrowWords.narrowPrep q = some q' →
      letsOnlyB q' = true

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The code with the result copies of the webs of the field domain is straight-line** when
    the narrowed output of the chain is built of bindings only. -/
theorem fieldDom_straight (hF : FieldLetsOnly e σ) (hB : FieldBody e σ fname b t r cert) :
    Straight (regionCoCode σ exportReg t r.code r.res
      (regionCopy σ exportReg t none r.code r.res)) := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, rfl⟩ := hB
  exact straight_of_isLopn (isLopn_regionCoCode_webs
    (exportR_isLopn_of_letsOnlyB (legalizeRegion q') (hF t0 q q' hq hq') _ _ _ hr0) σ exportReg _
      _ _)

/-- **Stages `G2` and `G3` from `FieldLetsOnly` and `WriteKills`.** -/
theorem fieldDom_coalesce_of_letsOnly (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hF : FieldLetsOnly e σ)
    (hW : WriteKills (canonMemrefName (regionAliasTab σ exportReg t none r.res
        (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))))
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
      (calleeAAT none) (calleeAOT none)
      (regionCoObs t (regionOut (regionCopy σ exportReg t none r.code r.res) r.res))) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" ∧
      regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" :=
  fieldDom_coalesce_of_shape h hB ⟨fieldDom_straight hF hB, hW⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
