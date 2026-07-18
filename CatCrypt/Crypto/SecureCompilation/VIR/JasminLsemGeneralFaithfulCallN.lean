/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledCallN
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf

set_option autoImplicit false

/-!
# General-`Com` `lsem` export faithfulness for the multi-result-call fragment

`JasminLsemGeneralFaithfulLeaf` lifts the opaque-leaf straight-line faithfulness
(`comToLprog_faithful_leaf`, body-fold `lsemStraightLeaf` over the typed `LinstrRT`) into the
program-indexed `lsem` via the typed bridge `lsemFuelLeaf_straightline`. The wider
multi-result-call fragment (`ScalarCallN`: the opaque-leaf heads plus the single-arg
head-result external call `callN`) carries its faithfulness over the same typed `LinstrRT`
body-fold `lsemStraightCallN` (`comToLprog_faithful_callN`, under the carried leaf agreements
`LeafAgreesN leaf` for the single-result `extCall` and `LeafAgreesCN leaf` for the `callN`
head). `JasminLsemLabeledCallN` supplies the typed program-indexed bridge
`lsemFuelCallN_straightline`; this file uses it to lift that fragment into the program-indexed
`lsem` over `LstateN`, the multi-result-call analogue of `comLsemExportFaithfulLeaf_of_leaf`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulCallN

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledCallN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

/-- **An emitted multi-result-call-fragment body is jump-free on the wire.** The
    `.fst`-projection (the emitted bytes) of each typed `straightOpsCallN` instruction is
    `straightOpsMC`'s instruction (`straightOpsCallN_wire`) — a `shiftLinstr` (`Lopn`) for the
    immediate shifts, an `opToLinstrR` image (`Lopn`) for every other op, including the bare
    `"CALLN:name"` `callN` wire — hence `IsStraightLine`. So the program-indexed `callN`
    semantics never fetches a control-transfer instruction. -/
theorem straightOpsCallN_isStraightLine (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ straightOpsCallN nArgs com curDepth, IsStraightLine i.fst := by
  intro i hi
  have hwire : i.fst ∈ straightOpsMC nArgs com curDepth := by
    rw [← straightOpsCallN_wire nArgs com curDepth]
    exact List.mem_map_of_mem hi
  exact straightOpsMC_isStraightLine nArgs com curDepth i.fst hwire

/-- **General-`Com` `lsem` export faithfulness, multi-result-call fragment.** Over the
    labeled, typed program-indexed `lsem` on `LstateN` (under the carried leaf agreements
    `LeafAgreesN leaf` and `LeafAgreesCN leaf`): the emitted singleton typed program drives
    the encoded inputs to a state whose result register decodes to `Com.denote`. -/
def ComLsemExportFaithfulCallN (leaf : LeafEnvCN) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fn : String) {w : Nat} (hw : t = .reg w) : Prop :=
  ∀ V : Ctxt.Valuation Γ, ∃ st' : LstateN,
    lsemFuelCallN leaf (singletonProgT fn (straightOpsCallN Γ.length com Γ.length))
        (straightOpsCallN Γ.length com Γ.length).length { base := encodeN V, lfn := fn }
      = some { base := st', lfn := fn }
    ∧ decodeN st' (comRetReg Γ.length argName com Γ.length) w
        = some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧)

/-- **The export gate is genuinely discharged for the multi-result-call fragment.** Any `Com`
    over `{regArith, select, immediate shifts, mulhi, addCarryLo/Hi, castW, extCall, callN}`
    satisfies `ComLsemExportFaithfulCallN` for any leaf environment whose external primitives
    agree with the dialect (`LeafAgreesN leaf` for `extCall`, `LeafAgreesCN leaf` for the
    `callN` head) — assembled from `comToLprog_faithful_callN` + the `lsemFuelCallN_straightline`
    bridge. The `callN` arm is the genuinely external multi-result leaf; `LeafAgreesCN` is its
    own KAT, carried alongside `LeafAgreesN`. -/
theorem comLsemExportFaithfulCallN_of_callN {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulCallN leaf com fn hw := by
  intro V
  have hf := comToLprog_faithful_callN hleafN hleafCN hcom hw V
  rcases hrun : lsemStraightCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V)
    with _ | st'
  · rw [hrun] at hf; simp at hf
  · refine ⟨st', ?_, ?_⟩
    · rw [lsemFuelCallN_straightline leaf fn (straightOpsCallN Γ.length com Γ.length)
        { base := encodeN V, lfn := fn } rfl (encodeN_lpc V), hrun]
      simp
    · rw [hrun] at hf; simp only [Option.bind_some] at hf; exact hf

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulCallN
