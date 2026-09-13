/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.LowCTExtensions.RForPreservation
public import CatCrypt.Crypto.SecureCompilation.LowCTExtensions.ArrayPreservation

/-!
# Stage EE3 — Combined meta-theorem extensions

This file composes the per-constructor extension lemmas from
`RForPreservation.lean` (Stage EE1) and `ArrayPreservation.lean`
(Stage EE2) into combined statements that name the extended coverage of
the **robust-compilation** (#95) and **CT-preservation** (#146)
meta-theorems for the constructor set on master at extension time:
`RFor`, `RArrLoad`, `RArrStore`.

## Naming conventions

* `*_extended` — the meta-theorem statement, with all per-constructor
  obligations bundled into a single named theorem. The proof composes
  the EE1 / EE2 building blocks.

## Foundational deferral note

The original `#95` and `#146` proofs at the Com-level (lattice → jasmin)
are **not edited** by this extension. The foundation theorems
`rustExecSimulatesDialect` (LowCT → `catCryptDialect` simulation over the
`CProg`-free front, the upstream feeder of #95) and `cmdCT_sound`
(RustExec-level CT soundness, the upstream feeder of #146) **already** cover
`RFor`, `RArrLoad`, and `RArrStore` in their inductive case-splits (see
`LowCTCTAnalysis.lean` cases `forZero`, `forSucc`, `arrLoad`, `arrStore`, and
`Dialects/CryptoDialectRustSim.lean`'s `RFor` / `arrLoad` / `arrStore` arms).

The role of this file is to **expose** that coverage as named, citable
extension theorems on master, so downstream protocols and audits can
reference per-constructor coverage without re-reading the inductive
proofs.

For `RArrLoad` / `RArrStore`, the translation side emits opaque
`extCall "arrLoadDyn"` / `"arrStoreDyn"` via the dialect front; the `.isSome`
emit witnesses are `RArrLoad{,Store}D_translation_emits`.

## What is *not* extended here

This file does **not** modify the statements of the
`robustCompilation_source_to_x86` capstone or `trust_boundary_is_jasmin_ir_to_x86`
in `RobustCompilationPipeline.lean`. Those theorems are stated at the
Com / jasmin level (downstream of the LowCT → `catCryptDialect` front-end);
they range over `Com latticeDialect` programs, regardless of which
front-end constructors emitted them. The capstone is automatically
covered for any LowCT AST that the dialect front translates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.LowCTExtensions.CombinedExtended

open CatCrypt.Crypto.SecureCompilation.LowCTExtensions.RForPreservation
open CatCrypt.Crypto.SecureCompilation.LowCTExtensions.ArrayPreservation
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-! ## 1. Robust compilation, extended (#95-extended)

The robust-compilation theorem chain at the LowCT layer is fed by the
`CProg`-free dialect-front simulation `rustExecSimulatesDialect`. The
per-constructor extensions are:

* **`RFor`**: covered by `RForPreservation.loopRForD_denotation_preserved`.
* **`RArrLoad` / `RArrStore`**: covered by the dialect emit witnesses
  `ArrayPreservation.RArrLoadD_translation_emits` / `RArrStoreD_translation_emits`.
-/

/-- **Robust compilation extended — `RFor` coverage (dialect front).**

    For any control-covered `RFor x N_loop body` AST that the `CProg`-free
    dialect front translates successfully, the simulation theorem
    `rustExecSimulatesDialect` produces a witness `V'` for the post-state
    `RustStateInterp`. This is the constructor-specialized robust-compilation
    statement at the LowCT layer.

    Composing this with the existing #95 chain at the Com→x86 layer
    (`RobustCompilationPipeline.robustCompilation_source_to_x86`) lifts
    the guarantee through the verified emit pipeline to x86. -/
theorem RobustCompilation_RFor_extended
    {Γ : Ctx} (vm : VarMap Γ) (x : String) (N_loop : Nat) (body : LowCT)
    (o : DTransOut Γ) (N : Nat) (leafSpec : LeafSpec)
    (rs rs' : RustState)
    (hCov : IsCoveredCtl body)
    (hTrans : translateDialectControl vm (.RFor x N_loop body) = some o)
    (hExec : RustExec N leafSpec (.RFor x N_loop body) rs rs')
    (V : HVec Γ) (hInv : RustStateInterp vm rs V) :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V' :=
  loopRForD_denotation_preserved vm x N_loop body o N leafSpec rs rs'
    hCov hTrans hExec V hInv

/-- **Robust compilation extended — `RArrLoad` coverage (dialect front).**

    The `CProg`-free dialect front emits an opaque `extCall "arrLoadDyn"` (with
    the runtime index as an argument) for `RArrLoad` when the source slot
    resolves and the index var is bound. Denotation preservation is the `arrLoad`
    case of `rustExecSimulatesDialect`; the public-index constant-time discipline
    is `LowCTCTAnalysis.cmdCT`. -/
theorem RobustCompilation_RArrLoad_extended
    {Γ : Ctx} (vm : VarMap Γ)
    (dst src : Located) (idxVar : String)
    {ra : List ((t : CryptoTy) × CVar Γ t)} {iv : (t : CryptoTy) × CVar Γ t}
    (hra : resolveLocatedArgs vm [src] = some ra)
    (hiv : vm.lookup idxVar = some iv) :
    (translateDialectControl vm (.RArrLoad dst src idxVar)).isSome :=
  RArrLoadD_translation_emits vm dst src idxVar hra hiv

/-- **Robust compilation extended — `RArrStore` coverage (dialect front).** -/
theorem RobustCompilation_RArrStore_extended
    {Γ : Ctx} (vm : VarMap Γ)
    (arr : Located) (idxVar : String) (src : Located)
    {ra : List ((t : CryptoTy) × CVar Γ t)} {iv : (t : CryptoTy) × CVar Γ t}
    (hra : resolveLocatedArgs vm [arr, src] = some ra)
    (hiv : vm.lookup idxVar = some iv) :
    (translateDialectControl vm (.RArrStore arr idxVar src)).isSome :=
  RArrStoreD_translation_emits vm arr idxVar src hra hiv

/-! ## 2. CT preservation, extended (#146-extended)

The CT-preservation chain at the LowCT layer is fed by `cmdCT_sound`.
Per-constructor extensions:

* **`RFor`**: covered unconditionally (closed `N : Nat` bound; counter
  structurally Public). See `RForPreservation.loopRFor_ct_preserves`.
* **`RArrLoad` / `RArrStore`**: covered **conditionally** on Public
  index. See `ArrayPreservation.R{ArrLoad,ArrStore}_ct_preserves_if_idx_public`.

The conditional clause is necessary: a secret-derived index breaks
CT (`R{ArrLoad,ArrStore}_secret_index_rejected`).
-/

/-- **CT preservation extended — `RFor` coverage.**

    `RFor` is CT-by-construction when the body is CT: the closed
    `N : Nat` bound and the structurally-public counter prevent any
    secret-dependent control flow at the loop level. -/
theorem CTPreservation_RFor_extended
    (x : String) (N_loop : Nat) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (leafSpec : LeafSpec) (N : Nat)
    (hCT_body : cmdCT body lt leafCT = true)
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCMOV : CMOVInvariant (.RFor x N_loop body))
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RFor x N_loop body) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RFor x N_loop body) rs2 rs2') :
    PublicEquiv lt rs1' rs2' :=
  loopRFor_ct_preserves x N_loop body lt leafCT leafSpec N
    hCT_body hLeaf hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-- **CT preservation extended — `RArrLoad` coverage (CONDITIONAL on
    Public index).**

    The conditional clause is essential: a secret-derived index leaks
    via the address-bus / cache-line side channel and is **not** CT.
    See `RArrLoad_no_CT_claim_for_secret_index` for the formal
    no-claim statement. -/
theorem CTPreservation_RArrLoad_extended_if_idx_public
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
    PublicEquiv lt rs1' rs2' :=
  RArrLoad_ct_preserves_if_idx_public dst src idxVar lt leafCT leafSpec N
    hIdxPub hDstPub hSrcPub hLeaf hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-- **CT preservation extended — `RArrStore` coverage (CONDITIONAL on
    Public index).** -/
theorem CTPreservation_RArrStore_extended_if_idx_public
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
    PublicEquiv lt rs1' rs2' :=
  RArrStore_ct_preserves_if_idx_public arr idxVar src lt leafCT leafSpec N
    hIdxPub hArrPub hSrcPub hLeaf hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-! ## 3. The CT-public-index restriction, formally stated

The conditional CT clause for array operations is **not** a workaround:
it reflects the fundamental fact that a secret-derived address is a
canonical side-channel leak. We state the formal restriction here as
the single combined no-claim theorem.
-/

/-- **The CT-public-index restriction.**

    For any `RArr*` constructor (load or store), there is **no**
    CT-preservation claim when the index variable is `Secret`-classified.
    Stated as: `cmdCT` refuses to certify the AST. This is the precise
    formal sense of "secret-index breaks CT".

    *Read this lemma as the formal boundary of #146-extended's coverage*:
    array constructors are covered ONLY for public indices, and the
    no-claim case is itself a positive theorem. -/
theorem CTPreservation_array_public_index_restriction
    (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hIdxSecret : lt idxVar = .Secret) :
    ¬ (cmdCT (.RArrLoad dst src idxVar) lt leafCT = true)
      ∧ ¬ (cmdCT (.RArrStore dst idxVar src) lt leafCT = true) :=
  ⟨RArrLoad_no_CT_claim_for_secret_index dst src idxVar lt leafCT hIdxSecret,
   RArrStore_no_CT_claim_for_secret_index dst idxVar src lt leafCT hIdxSecret⟩

/-! ## 4. Audit summary (informal)

The constructor-coverage table closed by this extension batch:

```
Constructor   | Translation preservation       | CT preservation
--------------+--------------------------------+----------------------------
RFor          | RobustCompilation_RFor_ext     | CTPreservation_RFor_ext
              | (positive, via loopRForD)      | (unconditional, body-relative)
RArrLoad      | RobustCompilation_RArrLoad_ext | CTPreservation_RArrLoad_ext
              | (positive, via arrLoadDyn)     | (CONDITIONAL on Public idx)
RArrStore     | RobustCompilation_RArrStore_ext| CTPreservation_RArrStore_ext
              | (positive, via arrStoreDyn)    | (CONDITIONAL on Public idx)
```

The foundation theorems are not modified by the extensions.
-/

end CatCrypt.Crypto.SecureCompilation.LowCTExtensions.CombinedExtended
