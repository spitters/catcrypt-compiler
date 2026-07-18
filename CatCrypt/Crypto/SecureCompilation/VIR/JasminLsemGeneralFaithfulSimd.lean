/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledSimd
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf

set_option autoImplicit false

/-!
# General-`Com` `lsem` export faithfulness for the packed-lane SIMD fragment

`JasminLsemGeneralFaithfulLeaf` lifts the opaque-leaf straight-line faithfulness
(`comToLprog_faithful_leaf`, body-fold `lsemStraightLeaf` over the typed `LinstrRT`) into the
program-indexed `lsem` via the typed bridge `lsemFuelLeaf_straightline`. The wider AVX-512
packed-lane SIMD fragment (`ScalarSimdN`: the opaque-leaf heads plus the packed-lane
`vpackZMM`) carries its faithfulness over the typed `LinstrRS` body-fold `lsemStraightSimd`
(`comToLprog_faithful_simd`, under the carried leaf agreement `LeafAgreesN leaf`).
`JasminLsemLabeledSimd` supplies the typed program-indexed bridge `lsemFuelSimd_straightline`;
this file uses it to lift that fragment into the program-indexed `lsem` over `LstateN`, the
SIMD analogue of `comLsemExportFaithfulLeaf_of_leaf`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulSimd

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledSimd
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

/-- **An emitted SIMD-fragment body is jump-free on the wire.** The `.fst`-projection (the
    emitted bytes) of each typed `straightOpsSimd` instruction is `straightOpsMC`'s
    instruction (`straightOpsSimd_wire`) — a `shiftLinstr` (`Lopn`) for the immediate shifts,
    an `opToLinstrR` image (`Lopn`) for every other op, including the bare `"VPACK8u64:bop"`
    `vpackZMM` wire — hence `IsStraightLine`. So the program-indexed SIMD semantics never
    fetches a control-transfer instruction. -/
theorem straightOpsSimd_isStraightLine (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ straightOpsSimd nArgs com curDepth, IsStraightLine i.fst := by
  intro i hi
  have hwire : i.fst ∈ straightOpsMC nArgs com curDepth := by
    rw [← straightOpsSimd_wire nArgs com curDepth]
    exact List.mem_map_of_mem hi
  exact straightOpsMC_isStraightLine nArgs com curDepth i.fst hwire

/-- **General-`Com` `lsem` export faithfulness, packed-lane SIMD fragment.** Over the labeled,
    typed program-indexed `lsem` on `LstateN` (under the carried leaf agreement
    `LeafAgreesN leaf`): the emitted singleton typed SIMD program drives the encoded inputs to
    a state whose result register decodes to `Com.denote`. -/
def ComLsemExportFaithfulSimd (leaf : LeafEnvN) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fn : String) {w : Nat} (hw : t = .reg w) : Prop :=
  ∀ V : Ctxt.Valuation Γ, ∃ st' : LstateN,
    lsemFuelSimd leaf (singletonProgS fn (straightOpsSimd Γ.length com Γ.length))
        (straightOpsSimd Γ.length com Γ.length).length { base := encodeN V, lfn := fn }
      = some { base := st', lfn := fn }
    ∧ decodeN st' (comRetReg Γ.length argName com Γ.length) w
        = some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧)

/-- **The export gate is genuinely discharged for the packed-lane SIMD fragment.** Any `Com`
    over `{regArith, select, immediate shifts, mulhi, addCarryLo/Hi, castW, extCall,
    vpackZMM}` satisfies `ComLsemExportFaithfulSimd` for any leaf environment whose external
    primitives agree with the dialect (`LeafAgreesN leaf`) — assembled from
    `comToLprog_faithful_simd` + the `lsemFuelSimd_straightline` bridge. The `vpackZMM` arm
    adds no new hypothesis: its packed-lane op is a verified dialect denotation; `LeafAgreesN`
    is the only carried hypothesis (for `extCall`). -/
theorem comLsemExportFaithfulSimd_of_simd {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulSimd leaf com fn hw := by
  intro V
  have hf := comToLprog_faithful_simd hleaf hcom hw V
  rcases hrun : lsemStraightSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V)
    with _ | st'
  · rw [hrun] at hf; simp at hf
  · refine ⟨st', ?_, ?_⟩
    · rw [lsemFuelSimd_straightline leaf fn (straightOpsSimd Γ.length com Γ.length)
        { base := encodeN V, lfn := fn } rfl (encodeN_lpc V), hrun]
      simp
    · rw [hrun] at hf; simp only [Option.bind_some] at hf; exact hf

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulSimd
