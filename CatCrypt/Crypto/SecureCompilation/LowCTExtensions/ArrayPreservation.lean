/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Stage EE2 — `RArrLoad` / `RArrStore` constructor extension lemmas

This file extends the **robust-compilation** (#95) and **CT-preservation**
(#146) meta-theorems to cover the array-element load/store constructors
`RArrLoad` and `RArrStore` introduced by Agent DD (Phase Ext, 2026-05-12).
It is a *sibling* file: no edits to foundation files.

## Honest status (read this section first)

The array constructors split the two obligations differently from the
loop / scalar constructors:

* **Translation preservation (#95 side).** The `CProg`-free dialect front
  `translateDialectControl` (delegating to `translateDialectFull` for these leaf
  arms) emits an opaque `extCall "arrLoadDyn"` / `"arrStoreDyn"` for `RArrLoad` /
  `RArrStore` when the source slot resolves and the runtime index var is bound.
  We expose this as the positive `.isSome` emit witnesses
  `RArrLoadD_translation_emits` / `RArrStoreD_translation_emits`; denotation
  preservation is the `arrLoad` / `arrStore` case of `rustExecSimulatesDialect`.

* **CT preservation (#146 side).** The big-step semantics of `RArrLoad` /
  `RArrStore` is fully defined (see `RustExec.arrLoad` / `.arrStore` in
  `LowCT.lean`), and the CT predicate `cmdCT` rejects these constructors
  unless the **index variable is Public**. The global soundness theorem
  `cmdCT_sound` therefore covers `RArrLoad` / `RArrStore` under the
  public-index condition. We name those discharges as explicit extension
  lemmas here. The corresponding **secret-index** case is *not* covered —
  and **must not be claimed CT-safe**: a secret-dependent memory index is
  a canonical cache-line / address-bus side channel. We state this
  explicitly as `RArr_secret_index_not_CT` (a *positive* documentation
  lemma about `cmdCT` itself, not a closure obligation).

## Why no general CT preservation lemma

A general theorem of the form "RArrLoad always preserves CT" would be
**unsound**: it would not hold when the index is secret-derived. We
intentionally avoid such a lemma. The closest we can state is the
**conditional** version (`RArrLoad_ct_preserves_if_idx_public`,
`RArrStore_ct_preserves_if_idx_public`).

## References

* `LowCT.lean` — definition of `RArrLoad` / `RArrStore` constructors
  (lines 494-505), big-step semantics (lines 885-904), `ArrLoadSpec` /
  `ArrStoreSpec` oracles (lines 561-575).
* `Dialects/TranslateDialectDirectArms.lean` — `translateDialectFull` emits
  `arrLoadDyn` / `arrStoreDyn` for these arms.
* `LowCTCTAnalysis.lean` — `cmdCT` rejects secret-index uses
  (lines 221-231); `cmdCT_sound` discharges the public-index case
  (lines 1323-1350).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.LowCTExtensions.ArrayPreservation

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-! ## 1. Translation for `RArrLoad` / `RArrStore` (dialect front)

The `CProg`-free dialect front `translateDialectControl` lowers the array
constructors to opaque `extCall "arrLoadDyn"` / `"arrStoreDyn"` expressions when
the source slot resolves and the runtime index var is bound. We expose the
positive `.isSome` emit witnesses below.
-/

/-- **`RArrLoad` translates over the `CProg`-free dialect front (positive).**
    When the source slot resolves and the runtime index var is bound, the
    `catCryptDialect` front `translateDialectControl` (delegating to
    `translateDialectFull` for this leaf arm) emits an opaque `extCall "arrLoadDyn"`
    (carrying the index as an argument). The denotation-preservation is discharged
    by the `arrLoad` case of `rustExecSimulatesDialect` (opaque-value,
    `interp_cons_setTower_any`); the public-index constant-time discipline is in
    `LowCTCTAnalysis.cmdCT`. Dialect twin of the former `translate`-side witness;
    neither statement nor proof names `CProg` / `CExpr` / `translate`. -/
theorem RArrLoadD_translation_emits {Γ : Ctx} (vm : VarMap Γ)
    (dst src : Located) (idxVar : String)
    {ra : List ((t : CryptoTy) × CVar Γ t)} {iv : (t : CryptoTy) × CVar Γ t}
    (hra : resolveLocatedArgs vm [src] = some ra)
    (hiv : vm.lookup idxVar = some iv) :
    (translateDialectControl vm (.RArrLoad dst src idxVar)).isSome := by
  simp only [translateDialectControl, translateDialectFull, hra, hiv]
  rcases listSigmaToCHVector (ra ++ [iv]) with ⟨_, _⟩
  rfl

/-- **`RArrStore` translates over the `CProg`-free dialect front (positive).**
    Dual of `RArrLoadD_translation_emits`. -/
theorem RArrStoreD_translation_emits {Γ : Ctx} (vm : VarMap Γ)
    (arr : Located) (idxVar : String) (src : Located)
    {ra : List ((t : CryptoTy) × CVar Γ t)} {iv : (t : CryptoTy) × CVar Γ t}
    (hra : resolveLocatedArgs vm [arr, src] = some ra)
    (hiv : vm.lookup idxVar = some iv) :
    (translateDialectControl vm (.RArrStore arr idxVar src)).isSome := by
  simp only [translateDialectControl, translateDialectFull, hra, hiv]
  rcases listSigmaToCHVector (ra ++ [iv]) with ⟨_, _⟩
  rfl

/-! ## 2. CT preservation for `RArrLoad` / `RArrStore`: the public-index case

`cmdCT (.RArrLoad dst src idxVar) lt leafCT = true` iff *all three* of
`idxVar`, `dst.locVar`, `src.locVar` are classified `Public` by `lt`. The
**index** Public-classification is the load-bearing one: a secret index
introduces an address-bus / cache-line side channel that is **not**
prevented by any compiler pass downstream.

Under those preconditions, `cmdCT_sound` already discharges the
preservation goal. We name the per-constructor extension lemmas here.
-/

/-- **CT-check decomposition for `RArrLoad`** (computed directly from
    `cmdCT`). The check is "index Public ∧ dst Public ∧ src Public". -/
@[simp]
theorem cmdCT_RArrLoad
    (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrLoad dst src idxVar) lt leafCT
      = ((lt idxVar == .Public) && (lt dst.locVar == .Public)
            && (lt src.locVar == .Public)) := rfl

/-- **CT-check decomposition for `RArrStore`.** Same three-public form. -/
@[simp]
theorem cmdCT_RArrStore
    (arr : Located) (idxVar : String) (src : Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrStore arr idxVar src) lt leafCT
      = ((lt idxVar == .Public) && (lt arr.locVar == .Public)
            && (lt src.locVar == .Public)) := rfl

/-- **`RArrLoad` preserves CT when the index is Public.**

    A **conditional** CT-preservation lemma — the index variable must be
    classified `Public` in the level table. A secret-derived index is
    *not* covered by this lemma (and must not be: secret indices break
    CT, see §3 below).

    Specialization of `cmdCT_sound` to the array-load constructor; the
    soundness proof already handles this case (`cmdCT_sound`, line 1337). -/
theorem RArrLoad_ct_preserves_if_idx_public
    (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (leafSpec : LeafSpec) (N : Nat)
    (hIdxPub : lt idxVar = .Public)
    (hDstPub : lt dst.locVar = .Public)
    (hSrcPub : lt src.locVar = .Public)
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCMOV : CMOVInvariant (.RArrLoad dst src idxVar))
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RArrLoad dst src idxVar) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RArrLoad dst src idxVar) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  have hCT : cmdCT (.RArrLoad dst src idxVar) lt leafCT = true := by
    rw [cmdCT_RArrLoad, hIdxPub, hDstPub, hSrcPub]; decide
  exact cmdCT_sound (.RArrLoad dst src idxVar) lt leafCT leafSpec N
    hCT hLeaf hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-- **`RArrStore` preserves CT when the index is Public.** Same
    conditional shape as `RArrLoad_ct_preserves_if_idx_public`. -/
theorem RArrStore_ct_preserves_if_idx_public
    (arr : Located) (idxVar : String) (src : Located)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (leafSpec : LeafSpec) (N : Nat)
    (hIdxPub : lt idxVar = .Public)
    (hArrPub : lt arr.locVar = .Public)
    (hSrcPub : lt src.locVar = .Public)
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCMOV : CMOVInvariant (.RArrStore arr idxVar src))
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RArrStore arr idxVar src) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RArrStore arr idxVar src) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  have hCT : cmdCT (.RArrStore arr idxVar src) lt leafCT = true := by
    rw [cmdCT_RArrStore, hIdxPub, hArrPub, hSrcPub]; decide
  exact cmdCT_sound (.RArrStore arr idxVar src) lt leafCT leafSpec N
    hCT hLeaf hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-! ## 3. The secret-index restriction, stated formally

**A general CT preservation lemma for `RArrLoad` / `RArrStore` is NOT
claimed and would be false.** A secret-dependent memory index leaks the
secret through the address-bus / cache-line side channel.

The CT analyser `cmdCT` enforces this: if any of `idxVar`, `dst.locVar`,
`src.locVar` is `Secret`-classified, `cmdCT` returns `false`. We expose
this *rejection* as a positive lemma so downstream protocols can cite it
to certify "we did not certify CT for secret-index usages".
-/

/-- **A secret-classified index breaks `cmdCT` for `RArrLoad`.**

    The CT analyser refuses to certify a load with a secret-derived
    index. This is the formal statement of "secret index is not CT". -/
theorem RArrLoad_secret_index_rejected
    (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hIdxSecret : lt idxVar = .Secret) :
    cmdCT (.RArrLoad dst src idxVar) lt leafCT = false := by
  rw [cmdCT_RArrLoad, hIdxSecret]
  -- The leading conjunct `(.Secret == .Public)` is `false`, so the && short-circuits.
  cases h₁ : lt dst.locVar == SecretLevel.Public <;>
    cases h₂ : lt src.locVar == SecretLevel.Public <;> decide

/-- **A secret-classified index breaks `cmdCT` for `RArrStore`.** -/
theorem RArrStore_secret_index_rejected
    (arr : Located) (idxVar : String) (src : Located)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hIdxSecret : lt idxVar = .Secret) :
    cmdCT (.RArrStore arr idxVar src) lt leafCT = false := by
  rw [cmdCT_RArrStore, hIdxSecret]
  cases h₁ : lt arr.locVar == SecretLevel.Public <;>
    cases h₂ : lt src.locVar == SecretLevel.Public <;> decide

/-- **There is no CT-safety claim for a secret-index `RArrLoad`.**

    Combined statement: when the index is secret, the CT analyser
    refuses; therefore no CT-preservation conclusion is in scope. This
    is the documentation lemma that pins the boundary of `#146`'s
    extended coverage. -/
theorem RArrLoad_no_CT_claim_for_secret_index
    (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hIdxSecret : lt idxVar = .Secret) :
    ¬ (cmdCT (.RArrLoad dst src idxVar) lt leafCT = true) := by
  rw [RArrLoad_secret_index_rejected dst src idxVar lt leafCT hIdxSecret]
  decide

/-- **There is no CT-safety claim for a secret-index `RArrStore`.** -/
theorem RArrStore_no_CT_claim_for_secret_index
    (arr : Located) (idxVar : String) (src : Located)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hIdxSecret : lt idxVar = .Secret) :
    ¬ (cmdCT (.RArrStore arr idxVar src) lt leafCT = true) := by
  rw [RArrStore_secret_index_rejected arr idxVar src lt leafCT hIdxSecret]
  decide

end CatCrypt.Crypto.SecureCompilation.LowCTExtensions.ArrayPreservation
