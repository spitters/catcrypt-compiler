/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

@[expose] public section

set_option autoImplicit false

/-!
# General-`Com` `lsem` export faithfulness for the opaque-leaf fragment

`JasminLsemGeneralFaithfulMC` lifts the mul/carry straight-line faithfulness
(`comToLprog_faithful_mulcarry`, body-fold `lsemStraightMC` over `LstateN`) into the
program-indexed `lsem` via the N-state bridge `lsemFuelMC_straightline`. The wider
opaque-leaf fragment (`ScalarLeafN`: `regArith`/`select`/immediate shifts/the `mulhi`/
`addCarry` trio/`castW`/the opaque `extCall` leaf) carries its faithfulness over the
**typed** `LinstrRT` body-fold `lsemStraightLeaf leaf` (`comToLprog_faithful_leaf`, under
the carried leaf agreement `LeafAgreesN leaf`). `JasminLsemLabeledLeaf` supplies the typed
program-indexed bridge `lsemFuelLeaf_straightline`; this file uses it to lift that fragment
into the program-indexed `lsem` over `LstateN`, the opaque-leaf analogue of
`comLsemExportFaithfulMC_of_mulcarry`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

/-- **An emitted opaque-leaf-fragment body is jump-free on the wire.** The `.fst`-projection
    (the emitted bytes) of each typed `straightOpsLeaf` instruction is `straightOpsMC`'s
    instruction (`straightOpsLeaf_wire`) — a `shiftLinstr` (`Lopn`) for the immediate
    shifts, an `opToLinstrR` image (`Lopn`) for every other op, including the bare
    `"CALL:name"` `extCall` wire — hence `IsStraightLine`. So the program-indexed leaf
    semantics never fetches a control-transfer instruction. -/
theorem straightOpsLeaf_isStraightLine (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ straightOpsLeaf nArgs com curDepth, IsStraightLine i.fst := by
  intro i hi
  have hwire : i.fst ∈ straightOpsMC nArgs com curDepth := by
    rw [← straightOpsLeaf_wire nArgs com curDepth]
    exact List.mem_map_of_mem hi
  exact straightOpsMC_isStraightLine nArgs com curDepth i.fst hwire

/-- **General-`Com` `lsem` export faithfulness, opaque-leaf fragment.** Over the labeled,
    typed program-indexed `lsem` on `LstateN` (under the carried leaf agreement
    `LeafAgreesN leaf`): the emitted singleton typed program drives the encoded inputs to a
    state whose result register decodes to `Com.denote`. -/
def ComLsemExportFaithfulLeaf (leaf : LeafEnvN) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fn : String) {w : Nat} (hw : t = .reg w) : Prop :=
  ∀ V : Ctxt.Valuation Γ, ∃ st' : LstateN,
    lsemFuelLeaf leaf (singletonProgT fn (straightOpsLeaf Γ.length com Γ.length))
        (straightOpsLeaf Γ.length com Γ.length).length { base := encodeN V, lfn := fn }
      = some { base := st', lfn := fn }
    ∧ decodeN st' (comRetReg Γ.length argName com Γ.length) w
        = some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧)

/-- **The export gate is genuinely discharged for the opaque-leaf fragment.** Any `Com` over
    `{regArith, select, immediate shifts, mulhi, addCarryLo/Hi, castW, extCall}` satisfies
    `ComLsemExportFaithfulLeaf` for any leaf environment whose external primitives agree
    with the dialect (`LeafAgreesN leaf`) — assembled from `comToLprog_faithful_leaf` + the
    `lsemFuelLeaf_straightline` bridge. The `extCall` arm is the genuinely external leaf;
    `LeafAgreesN` is its own KAT, the only carried hypothesis. -/
theorem comLsemExportFaithfulLeaf_of_leaf {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulLeaf leaf com fn hw := by
  intro V
  have hf := comToLprog_faithful_leaf hleaf hcom hw V
  rcases hrun : lsemStraightLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V)
    with _ | st'
  · rw [hrun] at hf; simp at hf
  · refine ⟨st', ?_, ?_⟩
    · rw [lsemFuelLeaf_straightline leaf fn (straightOpsLeaf Γ.length com Γ.length)
        { base := encodeN V, lfn := fn } rfl (encodeN_lpc V), hrun]
      simp
    · rw [hrun] at hf; simp only [Option.bind_some] at hf; exact hf

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf
