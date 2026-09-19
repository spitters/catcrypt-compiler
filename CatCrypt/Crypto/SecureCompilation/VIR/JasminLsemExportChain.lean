/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

/-!
# The export passes composed: canonicalised node, register allocation, two-address lowering

The physical export applies three transformations to the lifted loop node, each
with its own simulation:

* `canonicalizeMemrefThread ∘ aliasRegBody`, whose result computes the source
  fold (`JasminLsemExportCanon.canonNodeRM_faithful`);
* the register table, a renaming that is not injective
  (`JasminLsemExportRegAlloc.lsemFuelMemF_ranges`);
* the two-address lowering, which expands one instruction into several
  (`JasminLsemExportLower.lsemFuelMemF_lowerRM`).

The two transports carry a halting run of the canonicalised node to a halting
run of the allocated and lowered body. This module states the array conclusion
that survives both: the array the source run leaves at a name is the array the
target run leaves at the image of that name under the register table.
-/

public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

variable {σ : String → String} {Nr Na : String → Prop}

/-! ## 1. The array conclusion through each transport -/

/-- Allocated states read the array of a live name at the name's image. -/
theorem RelF2.decodeArrM_eq {t t' : LstateMF} (h : RelF2 σ Nr Na t t') {r : String}
    (hr : Na r) (w n : Nat) :
    decodeArrM t'.prog.base (σ r) w n = decodeArrM t.prog.base r w n := by
  unfold decodeArrM LstateM.getArr
  rw [h.1.2.1 r hr]

/-- Bases that differ in the program counter only read the same array. -/
theorem EqPc.decodeArrM_eq {a b : LstateM} (h : EqPc a b) (r : String) (w n : Nat) :
    decodeArrM b r w n = decodeArrM a r w n := by
  rw [h]
  exact decodeArrM_congr_larr _ _ rfl r w n

/-- Lowered states read the same array as the states they simulate. -/
theorem RelX.decodeArrM_eq {expand : LinstrRM → List LinstrRM} {P : LprogM}
    {t t' : LstateMF} (h : RelX EqPc expand P t t') (r : String) (w n : Nat) :
    decodeArrM t'.prog.base r w n = decodeArrM t.prog.base r w n :=
  EqPc.decodeArrM_eq h.base r w n

/-! ## 2. The two transports composed -/

/-- **Allocation and lowering carry the array conclusion.** A halting run of
    `body` whose final state holds an array at a name live there is matched by a
    halting run of the allocated and lowered body holding the same array at the
    image of that name under the register table. The register-allocation
    hypotheses are those of `lsemFuelMemF_ranges`, the lowering hypotheses those
    of `lsemFuelMemF_lowerRM`. -/
theorem alloc_lower_decodeArrM
    (fn : String) (body : List LinstrRM) (k0 : Nat)
    (hfix : σ "" = "") (hne : ∀ n, n ≠ "" → σ n ≠ "")
    {rr ra : String → Nat × Nat} {InR InA : String → Prop}
    (hcond : ∀ k i, k0 ≤ k → body[k]? = some i → CondOK i)
    (hjmp : ∀ l pc, findLabelMem l body = some pc → k0 ≤ pc + 1)
    (hR : RangeCert σ k0 body regDefs rr InR) (hA : RangeCert σ k0 body arrDefs ra InA)
    (huse : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ n ∈ useNames i.1, Live rr InR k n)
    (harr : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ b, arrUse? i = some b → Live ra InA k b)
    (hjR : JumpOK body k0 rr InR) (hjA : JumpOK body k0 ra InA)
    {isB : String → Bool} {movFor : String → String}
    (hlow : LowerOK isB movFor (singletonProgM fn (body.map (renRM σ))))
    (fuel : Nat) {s s' s'' t : LstateMF}
    (hrel : RelF2 σ (Live rr InR s.prog.base.lpc) (Live ra InA s.prog.base.lpc) s s')
    (hk : k0 ≤ s.prog.base.lpc)
    (hrelX : RelX EqPc (lowerRM isB movFor) (singletonProgM fn (body.map (renRM σ))) s' s'')
    (hrun : lsemFuelMemF (singletonProgM fn body) fuel s = some t)
    (r : String) (w n : Nat) (hr : Live ra InA t.prog.base.lpc r) :
    ∃ (fuel' : Nat) (t' : LstateMF),
      lsemFuelMemF
          ⟨fn, (body.map (renRM σ)).flatMap (lowerRM isB movFor)⟩ fuel' s'' = some t'
        ∧ decodeArrM t'.prog.base (σ r) w n = decodeArrM t.prog.base r w n := by
  obtain ⟨ta, hruna, hrela⟩ :=
    lsemFuelMemF_ranges (σ := σ) fn body k0 hfix hne hcond hjmp hR hA huse harr hjR hjA
      fuel hrel hk hrun
  obtain ⟨fuel', t', _, hrunl, hrell⟩ := lsemFuelMemF_lowerRM hlow fuel hrelX hruna
  exact ⟨fuel', t', hrunl, (RelX.decodeArrM_eq hrell (σ r) w n).trans
    (RelF2.decodeArrM_eq hrela hr w n)⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChain
