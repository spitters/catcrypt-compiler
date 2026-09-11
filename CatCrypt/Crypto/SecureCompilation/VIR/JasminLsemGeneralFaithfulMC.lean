/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful

@[expose] public section

set_option autoImplicit false

/-!
# General-`Com` `lsem` export faithfulness for the mul/carry fragment

`JasminLsemGeneralFaithful` lifts the plain-`Lstate` straight-line tower (`UniformScalarArith`)
into the labeled `lsem`. The wider mul/carry fragment (`ScalarMulCarryN`: `regArith`/`select`/
immediate shifts / the `mulhi`/`addCarry` trio) carries its faithfulness over the width-tagged
`LstateN` (`comToLprog_faithful_mulcarry`, body-fold `lsemStraightMC`). `JasminLsemLabeledMC`
supplies the N-state straight-line bridge `lsemFuelMC_straightline`; this file uses it to lift
that fragment into the program-indexed `lsem` over `LstateN`, the N-state analogue of
`comLsemExportFaithful_of_scalar`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful

/-- **An emitted mul/carry-fragment body is jump-free.** Each `straightOpsMC` instruction
    is a `shiftLinstr` (an `Lopn`) for the immediate shifts, or an `opToLinstrR` image
    (an `Lopn`) for every other op — hence `IsStraightLine`. -/
theorem straightOpsMC_isStraightLine (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ straightOpsMC nArgs com curDepth, IsStraightLine i := by
  induction com generalizing curDepth with
  | ret v => intro i hi; simp only [straightOpsMC, List.not_mem_nil] at hi
  | var e body ih =>
      intro i hi
      rw [straightOpsMC, List.mem_cons] at hi
      rcases hi with h | h
      · subst h
        split
        · simp [shiftLinstr, IsStraightLine]
        · simp [shiftLinstr, IsStraightLine]
        · simp [shiftLinstr, IsStraightLine]
        · exact opToLinstrR_isStraightLine _ _ _
      · exact ih (curDepth + 1) i h

/-- `encodeAuxN` only writes registers, so it leaves the program counter unchanged. -/
theorem encodeAuxN_lpc {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (st : LstateN) :
    (encodeAuxN V st).lpc = st.lpc := by
  fun_induction encodeAuxN V st <;>
    first | rfl | (simp only [LstateN.lpc_setReg]; assumption) | assumption

/-- The encoded width-tagged initial store starts at program counter `0`. -/
theorem encodeN_lpc {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    (encodeN V).lpc = 0 := encodeAuxN_lpc V _

/-- **General-`Com` `lsem` export faithfulness, mul/carry fragment.** Over the labeled
    program-indexed `lsem` on `LstateN`: the emitted singleton program drives the encoded
    inputs to a state whose result register decodes to `Com.denote`. -/
def ComLsemExportFaithfulMC {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fn : String) {w : Nat} (hw : t = .reg w) : Prop :=
  ∀ V : Ctxt.Valuation Γ, ∃ st' : LstateN,
    lsemFuelMC (singletonProg fn (straightOpsMC Γ.length com Γ.length))
        (straightOpsMC Γ.length com Γ.length).length { base := encodeN V, lfn := fn }
      = some { base := st', lfn := fn }
    ∧ decodeN st' (comRetReg Γ.length argName com Γ.length) w
        = some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧)

/-- **The export gate is genuinely discharged for the mul/carry fragment.** Any `Com` over
    `{regArith, select, immediate shifts, mulhi, addCarryLo/Hi}` satisfies
    `ComLsemExportFaithfulMC` — assembled from `comToLprog_faithful_mulcarry` + the
    jump-freeness brick + the `lsemFuelMC_straightline` bridge. -/
theorem comLsemExportFaithfulMC_of_mulcarry {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulMC com fn hw := by
  intro V
  have hf := comToLprog_faithful_mulcarry hcom hw V
  rcases hrun : lsemStraightMC (straightOpsMC Γ.length com Γ.length) (encodeN V) with _ | st'
  · rw [hrun] at hf; simp at hf
  · refine ⟨st', ?_, ?_⟩
    · rw [lsemFuelMC_straightline fn (straightOpsMC Γ.length com Γ.length)
        (straightOpsMC_isStraightLine Γ.length com Γ.length)
        { base := encodeN V, lfn := fn } rfl (encodeN_lpc V), hrun]
      simp
    · rw [hrun] at hf; simp only [Option.bind_some] at hf; exact hf

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC
