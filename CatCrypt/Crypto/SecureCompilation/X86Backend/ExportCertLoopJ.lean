/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieRegs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLiftJ
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

@[expose] public section

set_option autoImplicit false

/-!
# The export certificate of a counted loop with a carried register tuple

`JasminLsemMemSourceTieRegs.canonNodeJ_faithful` runs the canonicalised node of a counted
loop carrying `stackArr w n :: rs` under renaming, thread, seed and feedback hypotheses.
This module ties it to the export: the typed export node `forLoopRegsRM`, renamed by the node
renaming `rhoJ` that sends the array register and the store slots to `out`, is the
immediate-shift expansion of the canonicalised node (`forLoopRegsRM_map_eq_canonNodeJ_expand`),
and runs on the flag machine to the array component of the source fold
(`forLoopRegsRM_export_faithful`). One Boolean check `exportCertJB` computes every hypothesis:
the loop renaming `certSigmaJ` and the node renaming `rhoJ` are functions of the node's
names, the thread certificate is decided by `threadCertB`, and the renamed seeds and feedback
are decoded as register-move lists (`movPairs?`) whose parallel-assignment conditions are
checked. `singleLoopJ_export_faithful_gate` states the result for the program with one
counted carried-register loop returning its array, from the System V entry.

## Main definitions

* `movPairs?`, `movesOKB`, `carOnlyB`, `seedSrcB`, `feedSrcB` — register-move lists and
  their checks.
* `certSigmaJ`, `sigmaCJ` — the loop renaming and its computable restriction.
* `rhoJ`, `sigmaJ`, `seedsJ`, `feedJ`, `tauCJ`, `exportCertJB`, `ExportCertJ` — the
  renamings, the renamed seeds and feedback, and the certificate.
* `singleLoopJ`, `certNodeJ`, `singleLoopJB` — the program, its certified node and its gate.

## Main results

* `loopBodyWalkRM_eq_expand` — the typed export walk is the expansion image of the renamed
  model chain.
* `forLoopRegsRM_map_eq_canonNodeJ_expand` — the renamed export node is the expanded
  canonicalised node.
* `forLoopRegsRM_export_faithful` — the renamed export node realises the source fold.
* `exportCertJB_sound` — an accepted node has every hypothesis of the export theorem.
* `certNodeJ_eq` — the certified node is the seeds followed by the guarded flag loop over
  the expanded canonicalised body.
* `singleLoopJ_export_faithful_gate` — the gated export from the System V entry: whenever
  the program denotes `v`, `certNodeJ` halts with the array at `out` decoding to `v`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopJ

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom inrHom hvToHom
  lookup_inlHom lookup_inrHom)
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
  (regName_ne_loopIdx regName_ne_loopCtr loopIdx_ne_loopCtr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieRegs
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLiftJ (loopBodyWalkRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (ComOpsPlain OpPlain)

/-! ## 1. The export walk is the model chain under the loop renaming -/

/-- **The expanded chain equation of a carried-register body.** For a body whose ops lie in
    the fragment's op set, the typed export walk is the expansion image of the model chain
    `straightOpsMem` of the single-return projection under the loop renaming `σ`. -/
theorem loopBodyWalkRM_eq_expand {σ : String → String} {d nCar : Nat} {invOps : List LOperand}
    (hσ : LoopRenJ σ d nCar invOps) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ (t :: ts))
    (hcom : ComOpsPlain m.toComHead) (curDepth : Nat) :
    loopBodyWalkRM d d nCar (some (loopIdx d)) invOps m curDepth
      = ((straightOpsMem (invOps.length + 1 + nCar) m.toComHead curDepth).map
          (renRM σ)).flatMap immShiftExpand :=
  match m with
  | .ret (.cons _ _) => by rw [toComHead_ret]; rfl
  | .var e body => by
      obtain ⟨hop, hbody⟩ := comOpsPlain_toComHead_var e body hcom
      have ih := loopBodyWalkRM_eq_expand hσ body hbody (curDepth + 1)
      rw [toComHead_var]
      have hreg : ∀ o ∈ (exprArgs curDepth (invOps.length + 1 + nCar) argName
          (fun _ => none) e).map (renOperand σ), ∃ r, o = LOperand.reg r := by
        intro o ho
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨r, rfl⟩ := exprArgs_isReg e o' ho'
        exact ⟨σ r, rfl⟩
      have hargs : loopVarsR d d nCar (some (loopIdx d)) invOps curDepth e.args
          = (exprArgs curDepth (invOps.length + 1 + nCar) argName (fun _ => none) e).map
              (renOperand σ) := by
        rw [loopVarsR_eq_ren hσ]
        unfold exprArgs
        rw [exprArgs_go_eq_HV]
      simp only [loopBodyWalkRM, straightOpsMem, List.map_cons, List.flatMap_cons, ← ih]
      rw [hargs, ← hσ.reg curDepth, ← List.singleton_append]
      congr 1
      split
      · next w n h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · next w n h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · next w w' h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · next w n h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · split
        · next w n s h hs =>
            obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
            rw [hs, h]
            simp only [renRM, renLinstrR, JasminLsemShift.shiftLinstr, List.map_cons,
              List.map_nil, renOperand, immShiftExpand_structShift (Or.inl rfl),
              opToLinstrR, memTagOfOp]
            rfl
        · next w n s h hs =>
            obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
            rw [hs, h]
            simp only [renRM, renLinstrR, JasminLsemShift.shiftLinstr, List.map_cons,
              List.map_nil, renOperand, immShiftExpand_structShift (Or.inr (Or.inl rfl)),
              opToLinstrR, memTagOfOp]
            rfl
        · next w n s h hs =>
            obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
            rw [hs, h]
            simp only [renRM, renLinstrR, JasminLsemShift.shiftLinstr, List.map_cons,
              List.map_nil, renOperand, immShiftExpand_structShift (Or.inr (Or.inr rfl)),
              opToLinstrR, memTagOfOp]
            rfl
        · have htag : memTagOfOp e.op = MemTag.reg none := by
            unfold memTagOfOp; split <;> simp_all
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          rw [← htag]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
termination_by sizeOf m

/-! ## 2. The renamed export node is the expanded canonicalised node -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLiftJ
  (forLoopRegsRM forSeedsRM forLoopRegsBodyRM regsSeedsRM regsFeedbackRM forAccs forTmp0)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
  (map_renRM_flatMap_immShiftExpand flatMap_immShiftExpand_of_fixed loopAdvanceRM_fixed
    loopTouchRM_fixed guardedFlagLoopLinstrRM_flatMap)

/-- A one-source register move is fixed by the immediate-shift expansion. -/
theorem immShiftExpand_mov (t : String) (s : LOperand) (tag : MemTag) :
    immShiftExpand (.Lopn [.reg t] (withWidthTag 64 "MOV") [s], tag)
      = [(.Lopn [.reg t] (withWidthTag 64 "MOV") [s], tag)] :=
  immShiftExpand_of_not_shift _ (fun _ _ _ _ h => by simp at h)

section NodeEq

variable {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- **The renamed counted export node is the expanded canonicalised node.** For a body whose
    ops lie in the fragment's op set, a loop renaming `σ` (`LoopRenJ`), and a node renaming
    `ρ` that fixes the loop index, the counter, the count register and the invariant base
    registers, the typed export node `forLoopRegsRM` seeded from `initOps` with count
    operand `.reg c`, renamed by `ρ`, is the immediate-shift expansion of `canonNodeJ` at
    `τ = ρ ∘ σ`, whose carried seeds and feedback are the renamed seed moves and the
    renamed feedback of the export. -/
theorem forLoopRegsRM_map_eq_canonNodeJ_expand {σ ρ : String → String} {d : Nat} {c : String}
    (initOps invOps : List LOperand)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (hlen : invOps.length = invTys.length) (hcom : ComOpsPlain update.toComHead)
    (hσ : LoopRenJ σ d (rs.length + 1) invOps)
    (hidx : ρ (loopIdx d) = loopIdx d) (hctr : ρ (loopCtr d) = loopCtr d) (hc : ρ c = c)
    (hinvFix : ∀ r ∈ invRegsOf invOps, ρ r = r)
    (hGfix : ∀ i ∈ (regsSeedsRM (forAccs d initOps update invOps)).map (renRM ρ),
      immShiftExpand i = [i])
    (hFfix : ∀ i ∈ (regsFeedbackRM d (forTmp0 d update invOps)
        ((forAccs d initOps update invOps).map (·.1))
        ((forAccs d initOps update invOps).map (·.2.2))).map (renRM ρ),
      immShiftExpand i = [i]) :
    (forLoopRegsRM d initOps (.reg c) update invOps).map (renRM ρ)
      = (canonNodeJ (ρ ∘ σ) d c update
          ((regsSeedsRM (forAccs d initOps update invOps)).map (renRM ρ))
          ((regsFeedbackRM d (forTmp0 d update invOps)
            ((forAccs d initOps update invOps).map (·.1))
            ((forAccs d initOps update invOps).map (·.2.2))).map (renRM ρ))
          (invRegsOf invOps)).flatMap immShiftExpand := by
  have hN : invOps.length + 1 + (rs.length + 1) = nArgsJ rs invTys := by
    simp only [nArgsJ]; omega
  have hD : invTys.length + 1 + (JasminTy.stackArr w n :: rs).length = nArgsJ rs invTys := by
    simp only [nArgsJ, List.length_cons]; omega
  have h1 : (loopBodyWalkRM d d (JasminTy.stackArr w n :: rs).length (some (loopIdx d)) invOps
        update (invTys.length + 1 + (JasminTy.stackArr w n :: rs).length)).map (renRM ρ)
      = ((chainJ update).map (renRM (ρ ∘ σ))).flatMap immShiftExpand := by
    rw [List.length_cons, loopBodyWalkRM_eq_expand hσ update hcom,
      map_renRM_flatMap_immShiftExpand, List.map_map, chainJ, ← hN,
      show invTys.length + 1 + (rs.length + 1) = invOps.length + 1 + (rs.length + 1) by omega]
    congr 1
    exact List.map_congr_left (fun i _ => renRM_comp ρ σ i)
  have h3 : (loopAdvanceRM d).map (renRM ρ) = loopAdvanceRM d := by
    simp [loopAdvanceRM, renRM, renLinstrR, renOperand, hidx, hctr]
  have h4 : (loopTouchRM d (invRegsOf invOps)).map (renRM ρ)
      = loopTouchRM d (invRegsOf invOps) := by
    unfold loopTouchRM
    rw [List.map_map]
    refine List.map_congr_left (fun r hr => ?_)
    simp [renRM, renLinstrR, renOperand, hctr, hinvFix r hr]
  have hseeds : (forSeedsRM d initOps (.reg c) update invOps).map (renRM ρ)
      = (regsSeedsRM (forAccs d initOps update invOps)).map (renRM ρ)
          ++ idxCtrSeedsRM d c := by
    unfold forSeedsRM idxCtrSeedsRM
    simp [renRM, renLinstrR, renOperand, hidx, hctr, hc]
  have hseedsFix : ∀ i ∈ (regsSeedsRM (forAccs d initOps update invOps)).map (renRM ρ)
      ++ idxCtrSeedsRM d c, immShiftExpand i = [i] := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hGfix i hi
    · simp only [idxCtrSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact immShiftExpand_mov _ _ _
  have htail : ((regsFeedbackRM d (forTmp0 d update invOps)
        ((forAccs d initOps update invOps).map (·.1))
        ((forAccs d initOps update invOps).map (·.2.2))).map (renRM ρ)
        ++ (loopAdvanceRM d ++ loopTouchRM d (invRegsOf invOps))).flatMap immShiftExpand
      = (regsFeedbackRM d (forTmp0 d update invOps)
        ((forAccs d initOps update invOps).map (·.1))
        ((forAccs d initOps update invOps).map (·.2.2))).map (renRM ρ)
        ++ (loopAdvanceRM d ++ loopTouchRM d (invRegsOf invOps)) := by
    refine flatMap_immShiftExpand_of_fixed _ (fun i hi => ?_)
    simp only [List.mem_append] at hi
    rcases hi with hi | hi | hi
    · exact hFfix i hi
    · exact loopAdvanceRM_fixed d i hi
    · exact loopTouchRM_fixed d _ i hi
  unfold forLoopRegsRM canonNodeJ
  rw [List.map_append, hseeds, guardedFlagLoopLinstrRM_map_renRM, hctr, List.flatMap_append,
    flatMap_immShiftExpand_of_fixed _ hseedsFix, guardedFlagLoopLinstrRM_flatMap]
  congr 2
  unfold forLoopRegsBodyRM canonBodyJ
  rw [List.flatMap_append, htail]
  simp only [List.map_append, h1, h3, h4, List.append_assoc]

end NodeEq

/-! ## 3. The renamed export node realises the source fold -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
  (ComExpOK instrOK_of_fixed straightOpsMem_instrOK immShiftExpand_cmp0
    lsemFuelMemF_singleton_expand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (InstrOK EqPc)

section Faithful

variable {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- **The canonicalised carried-register node satisfies the per-instruction condition** of
    the immediate-shift expansion, for a `ComExpOK` body and seed and feedback segments of
    `Lopn`s that the expansion fixes. -/
theorem canonNodeJ_instrOK (τ : String → String) (d : Nat) (c : String)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (hexp : ComExpOK update.toComHead) (G F : List LinstrRM)
    (hG : ∀ i ∈ G, IsLopn i ∧ immShiftExpand i = [i])
    (hF : ∀ i ∈ F, IsLopn i ∧ immShiftExpand i = [i]) (regs : List String) :
    ∀ i ∈ canonNodeJ τ d c update G F regs, InstrOK EqPc immShiftExpand i := by
  intro i hi
  simp only [canonNodeJ, guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge,
    canonBodyJ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hi
  rcases hi with (hi | hi) | (rfl | rfl | rfl | ((⟨j, hj, rfl⟩ | hi | hi | hi) | rfl | rfl))
    | rfl
  · exact instrOK_of_fixed (hG i hi).1 (hG i hi).2
  · simp only [idxCtrSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact instrOK_of_fixed ⟨_, _, _, rfl⟩ (immShiftExpand_mov _ _ _)
    · exact instrOK_of_fixed ⟨_, _, _, rfl⟩ (immShiftExpand_mov _ _ _)
  · exact instrOK_of_fixed ⟨_, _, _, rfl⟩ (immShiftExpand_cmp0 _)
  · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, _, rfl, by simp [flagCondCC?]⟩)⟩
  · exact Or.inr ⟨rfl, Or.inl ⟨_, _, rfl⟩⟩
  · exact straightOpsMem_instrOK τ _ _ hexp _ j hj
  · exact instrOK_of_fixed (hF i hi).1 (hF i hi).2
  · refine instrOK_of_fixed ?_ (loopAdvanceRM_fixed d i hi)
    simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · refine instrOK_of_fixed ?_ (loopTouchRM_fixed d regs i hi)
    simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩
  · exact instrOK_of_fixed ⟨_, _, _, rfl⟩ (immShiftExpand_cmp0 _)
  · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, _, rfl, by simp [flagCondCC?]⟩)⟩
  · exact Or.inr ⟨rfl, Or.inl ⟨_, _, rfl⟩⟩

/-- **The renamed counted export node realises the source fold.** The typed export node
    `forLoopRegsRM` of a body in `ArrMemN` with `ComExpOK`, seeded from `initOps` with count
    register `c` and renamed by `ρ`, run by `lsemFuelMemF` from program counter `0`, halts
    with the array at `out` decoding to the array component of the source fold. The
    hypotheses: `LoopRenJ σ` ties the walk to the model chain; `ρ` fixes the index, the
    counter, `c` and the invariant base registers; `CanonRenJ (ρ ∘ σ)` and the thread
    certificate canonicalise the chain; the renamed seed moves and the renamed feedback are
    `Lopn`s the expansion fixes and satisfy `SeedOKJ` and `FeedOKJ`; and the entry state
    holds the seeds, the invariants and the count. -/
theorem forLoopRegsRM_export_faithful {σ ρ : String → String} {d : Nat} {S : Nat → Prop}
    {out c : String} (hNoArr : ∀ w' n', JasminTy.stackArr w' n' ∉ rs)
    (initOps invOps : List LOperand)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (hlen : invOps.length = invTys.length)
    (hupd : ArrMemN update.toComHead) (hexp : ComExpOK update.toComHead)
    (hσ : LoopRenJ σ d (rs.length + 1) invOps)
    (hidx : ρ (loopIdx d) = loopIdx d) (hctr : ρ (loopCtr d) = loopCtr d) (hcfix : ρ c = c)
    (hinvFix : ∀ r ∈ invRegsOf invOps, ρ r = r)
    (hτ : CanonRenJ (ρ ∘ σ) d invTys.length rs.length S out)
    (hcert : ThreadCert (ρ ∘ σ) (nArgsJ rs invTys) S out (chainJ update) (nArgsJ rs invTys)
      (argName (invTys.length + rs.length + 1)) (headJ update))
    (hGok : ∀ i ∈ (regsSeedsRM (forAccs d initOps update invOps)).map (renRM ρ),
      IsLopn i ∧ immShiftExpand i = [i])
    (hFok : ∀ i ∈ (regsFeedbackRM d (forTmp0 d update invOps)
        ((forAccs d initOps update invOps).map (·.1))
        ((forAccs d initOps update invOps).map (·.2.2))).map (renRM ρ),
      IsLopn i ∧ immShiftExpand i = [i])
    (srcs : Nat → String)
    (hG : SeedOKJ d rs.length srcs
      ((regsSeedsRM (forAccs d initOps update invOps)).map (renRM ρ)))
    (hF : FeedOKJ (ρ ∘ σ) d rs.length (retsJ update)
      ((regsFeedbackRM d (forTmp0 d update invOps)
        ((forAccs d initOps update invOps).map (·.1))
        ((forAccs d initOps update invOps).map (·.2.2))).map (renRM ρ)))
    (hregs : ∀ r ∈ invRegsOf invOps, ∃ j, j < invTys.length ∧ r = (ρ ∘ σ) (argName j))
    (invs : Ctxt.Valuation invTys) (fn : String) (hc : c ≠ loopIdx d)
    (hcC : ∀ k, k < rs.length → c ≠ regName (d + k))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (accs0 : Ctxt.Valuation (JasminTy.stackArr w n :: rs))
    (harr0 : b0.getArr out w n
      = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs0))
    (hcar0 : ∀ {w' : Nat} (u : Ctxt.Var rs (JasminTy.reg w')),
      b0.reg.getW (srcs (rs.length - 1 - varIndex u)) w'
        = some ((Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs0))
    (hinvR0 : ∀ {w' : Nat} (u : Ctxt.Var invTys (JasminTy.reg w')),
      b0.reg.getW ((ρ ∘ σ) (argName (invTys.length - 1 - varIndex u))) w'
        = some (u.lookup invs))
    (hinvA0 : ∀ {w' n' : Nat} (u : Ctxt.Var invTys (JasminTy.stackArr w' n')),
      b0.getArr ((ρ ∘ σ) (argName (invTys.length - 1 - varIndex u))) w' n'
        = some (u.lookup invs))
    (hinv : ∀ j, j < invTys.length → (b0.reg.getW ((ρ ∘ σ) (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64) (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          ((forLoopRegsRM d initOps (.reg c) update invOps).map (renRM ρ))) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out w n
            = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup
                ((List.range m).foldl (fun a i => update.denote (tripValJ a i invs)) accs0)) := by
  obtain ⟨k, t, hrun, hdec⟩ := canonNodeJ_faithful hNoArr update hupd hτ hcert _ hF
    (fun i hi => (hFok i hi).1) srcs _ hG (fun i hi => (hGok i hi).1) (invRegsOf invOps)
    hregs invs fn c hc hcC b0 zf hpc accs0 harr0 hcar0 hinvR0 hinvA0 hinv m hm64 hcnt
  obtain ⟨k', t', hrun', hlarr⟩ := lsemFuelMemF_singleton_expand fn _
    (canonNodeJ_instrOK _ d c update hexp _ _ hGok hFok _) b0 zf hpc k t hrun
  refine ⟨k', t', ?_, ?_⟩
  · rw [forLoopRegsRM_map_eq_canonNodeJ_expand initOps invOps update hlen
      (ComExpOK.opsPlain _ hexp) hσ hidx hctr hcfix hinvFix (fun i hi => (hGok i hi).2)
      (fun i hi => (hFok i hi).2)]
    exact hrun'
  · rw [decodeArrM_congr_larr _ _ hlarr]
    exact hdec

end Faithful

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopJ

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopJ

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
  (renRM renLinstrR renOperand immShiftExpand loopCtr_ne_argName loopCtr_ne_regName
    head?_argName head?_regName head?_loopReg loopReg_ne_regName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (storeHit? arrUse?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
  (ThreadRen ThreadCert Resolved pullM loopReg_injective)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (invRegsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLiftJ
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieRegs
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
  (argName_injective argName_ne regName_injective regName_ne_argName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (ne_empty_of_head?)
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct

/-! ## 4. Register-move lists, decoded -/

/-- The pair `(target, source)` of a register move `MOV t, s` with the register descriptor,
    or `none` when the instruction has another shape. -/
def movPair? (i : LinstrRM) : Option (String × String) :=
  match i with
  | (.Lopn [.reg t] o [.reg s], .reg none) =>
      if o = withWidthTag 64 "MOV" then some (t, s) else none
  | _ => none

theorem movPair?_sound {i : LinstrRM} {p : String × String} (h : movPair? i = some p) :
    i = (.Lopn [.reg p.1] (withWidthTag 64 "MOV") [.reg p.2], MemTag.reg none) := by
  unfold movPair? at h
  split at h
  · split at h
    · next ho =>
        cases h
        rw [ho]
    · cases h
  · cases h

/-- The pairs `(target, source)` of a list of register moves `MOV t, s` with the register
    descriptor, or `none` when an instruction has another shape. -/
def movPairs? (L : List LinstrRM) : Option (List (String × String)) := L.mapM movPair?

theorem movPairs?_sound : ∀ {L : List LinstrRM} {ps : List (String × String)},
    movPairs? L = some ps → L = movesRM ps
  | [], ps, h => by
      simp only [movPairs?, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; rfl
  | i :: rest, ps, h => by
      simp only [movPairs?, List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨p, hp, ps', hps', rfl⟩ := h
      rw [movPair?_sound hp, movPairs?_sound hps']
      rfl

/-- The parallel-assignment conditions of a move list: distinct targets, and a source that
    is a target only of its own move. -/
def movesOKB (ps : List (String × String)) : Bool :=
  decide (ps.map Prod.fst).Nodup && ps.all (fun p => ps.all (fun q => p.2 != q.1 || p == q))

/-- Every move of the list targets a carried register `regName (d + k)`, `k < nR`, or is a
    self-move. -/
def carOnlyB (d nR : Nat) (ps : List (String × String)) : Bool :=
  ps.all (fun p => (List.range nR).any (fun k => p.1 == regName (d + k)) || p.1 == p.2)

/-- **The run of a checked move list.** -/
theorem movesRM_run {d nR : Nat} {ps : List (String × String)} (hok : movesOKB ps = true)
    (hcar : carOnlyB d nR ps = true) (x : LstateM) (zf : Bool) :
    ∃ x', runStraightF (movesRM ps) x zf = some (x', zf) ∧ x'.larr = x.larr
      ∧ (∀ p ∈ ps, x'.reg.lvm p.1 = x.reg.lvm p.2)
      ∧ (∀ r, (∀ k, k < nR → r ≠ regName (d + k)) → x'.reg.lvm r = x.reg.lvm r)
      ∧ (∀ r, r ∉ ps.map Prod.fst → x'.reg.lvm r = x.reg.lvm r) := by
  simp only [movesOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at hok
  obtain ⟨hnd, hsrc⟩ := hok
  obtain ⟨x', hrun, hl, _, hps, hoth⟩ := runStraightF_movesRM ps hnd
    (fun p hp q hq he => (hsrc p hp q hq).resolve_left (fun h => h he)) x zf
  refine ⟨x', hrun, hl, hps, fun r hr => ?_, hoth⟩
  by_cases hm : r ∈ ps.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    simp only [carOnlyB, List.all_eq_true, Bool.or_eq_true, List.any_eq_true, List.mem_range,
      beq_iff_eq] at hcar
    rcases hcar p hp with ⟨k, hk, he⟩ | he
    · exact absurd he (hr k hk)
    · rw [hps p hp, ← he]
  · exact hoth r hm

/-- Every carried register `regName (d + k)`, `k < nR`, is the target of a move from
    `srcs k`. -/
def seedSrcB (d nR : Nat) (ps : List (String × String)) (srcs : Nat → String) : Bool :=
  (List.range nR).all (fun k => ps.any (fun p => p.1 == regName (d + k) && p.2 == srcs k))

/-- A checked seed move list satisfies the seed condition. -/
theorem seedOKJ_of_check {d nR : Nat} {ps : List (String × String)} {srcs : Nat → String}
    (hok : movesOKB ps = true) (hcar : carOnlyB d nR ps = true)
    (hs : seedSrcB d nR ps srcs = true) : SeedOKJ d nR srcs (movesRM ps) := by
  intro x zf
  obtain ⟨x', hrun, hl, hps, hoth, _⟩ := movesRM_run hok hcar x zf
  refine ⟨x', hrun, hl, fun k hk => ?_, hoth⟩
  simp only [seedSrcB, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hs
  obtain ⟨p, hp, h1, h2⟩ := hs k hk
  rw [← h1, hps p hp, h2]

/-- Every carried register `regName (d + k)`, `k < nR`, receives the computed image of the
    model operand of position `nR - k`: by a move from it, or, when it is that image, by no
    move at all. -/
def feedSrcB (d nR : Nat) (ps : List (String × String)) (tauC : String → Option String)
    (rets : List LOperand) : Bool :=
  (List.range nR).all (fun k =>
    match tauC (operandName (rets.getD (nR - k) (.imm 0))) with
    | some src => ps.any (fun p => p.1 == regName (d + k) && p.2 == src)
        || (src == regName (d + k) && !(ps.any (fun p => p.1 == regName (d + k))))
    | none => false)

/-- A checked feedback move list satisfies the feedback condition. -/
theorem feedOKJ_of_check {τ : String → String} {tauC : String → Option String}
    (hτ : ∀ b t, tauC b = some t → τ b = t) {d nR : Nat} {ps : List (String × String)}
    {rets : List LOperand} (hok : movesOKB ps = true) (hcar : carOnlyB d nR ps = true)
    (hs : feedSrcB d nR ps tauC rets = true) : FeedOKJ τ d nR rets (movesRM ps) := by
  intro x zf
  obtain ⟨x', hrun, hl, hps, hoth, hnot⟩ := movesRM_run hok hcar x zf
  refine ⟨x', zf, hrun, hl, fun k hk => ?_, hoth⟩
  simp only [feedSrcB, List.all_eq_true, List.mem_range] at hs
  have hk' := hs k hk
  split at hk'
  · next src hsrc =>
      rw [hτ _ _ hsrc]
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true', List.any_eq_false] at hk'
      rcases hk' with ⟨p, hp, h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, hps p hp, h2]
      · rw [h1]
        refine hnot _ (fun hm => ?_)
        obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
        have := h2 p hp
        simp_all
  · cases hk'

/-- Every instruction of a move list is an `Lopn` the expansion fixes. -/
theorem movesRM_ok (ps : List (String × String)) :
    ∀ i ∈ movesRM ps, IsLopn i ∧ immShiftExpand i = [i] := by
  intro i hi
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hi
  exact ⟨⟨_, _, _, rfl⟩, immShiftExpand_mov _ _ _⟩

/-! ## 5. The loop renaming of a carried-register node -/

attribute [local instance] Classical.propDecidable in
/-- The loop renaming of a counted carried-register node at depth `d` with `nInv`
    invariants and `nCar` carried binders: the carried argument `argName (nInv + 1 + k)` to
    `regName (d + k)`, the index argument to the loop index, an invariant argument to its
    base register in `invRegs`, a chain register `regName k` to the body temporary
    `loopReg d k`, every other name to itself. -/
noncomputable def certSigmaJ (d nInv nCar : Nat) (invRegs : List String) (r : String) :
    String :=
  if h : ∃ k, k < nCar ∧ r = argName (nInv + 1 + k) then regName (d + h.choose)
  else if r = argName nInv then loopIdx d
  else if h : ∃ j, j < nInv ∧ r = argName j then
    invRegs.getD (nInv - 1 - h.choose) ("Linv" ++ toString d ++ "_" ++ toString h.choose)
  else if h : ∃ k, r = regName k then loopReg d h.choose
  else r

section Sigma

variable {d nInv nCar : Nat} {invRegs : List String}

theorem certSigmaJ_car {k : Nat} (hk : k < nCar) :
    certSigmaJ d nInv nCar invRegs (argName (nInv + 1 + k)) = regName (d + k) := by
  have hex : ∃ k', k' < nCar ∧ argName (nInv + 1 + k) = argName (nInv + 1 + k') :=
    ⟨k, hk, rfl⟩
  rw [certSigmaJ, dif_pos hex]
  have := argName_injective hex.choose_spec.2
  rw [show hex.choose = k by omega]

theorem certSigmaJ_idx : certSigmaJ d nInv nCar invRegs (argName nInv) = loopIdx d := by
  have hn : ¬ ∃ k, k < nCar ∧ argName nInv = argName (nInv + 1 + k) := fun ⟨k, _, h⟩ => by
    have := argName_injective h; omega
  rw [certSigmaJ, dif_neg hn, if_pos rfl]

theorem certSigmaJ_inv {j : Nat} (hj : j < nInv) : certSigmaJ d nInv nCar invRegs (argName j)
    = invRegs.getD (nInv - 1 - j) ("Linv" ++ toString d ++ "_" ++ toString j) := by
  have hn : ¬ ∃ k, k < nCar ∧ argName j = argName (nInv + 1 + k) := fun ⟨k, _, h⟩ => by
    have := argName_injective h; omega
  have hex : ∃ j', j' < nInv ∧ argName j = argName j' := ⟨j, hj, rfl⟩
  rw [certSigmaJ, dif_neg hn, if_neg (argName_ne (by omega)), dif_pos hex]
  have := argName_injective hex.choose_spec.2
  rw [← this]

theorem certSigmaJ_reg (k : Nat) : certSigmaJ d nInv nCar invRegs (regName k) = loopReg d k := by
  have hn : ¬ ∃ k', k' < nCar ∧ regName k = argName (nInv + 1 + k') := fun ⟨_, _, h⟩ =>
    regName_ne_argName _ _ h
  have hna : ¬ ∃ j, j < nInv ∧ regName k = argName j := fun ⟨j, _, h⟩ =>
    regName_ne_argName k j h
  have hex : ∃ k', regName k = regName k' := ⟨k, rfl⟩
  rw [certSigmaJ, dif_neg hn, if_neg (regName_ne_argName k _), dif_neg hna,
    dif_pos hex, regName_injective hex.choose_spec.symm]

theorem certSigmaJ_other {r : String} (ha : ∀ j, r ≠ argName j) (hr : ∀ k, r ≠ regName k) :
    certSigmaJ d nInv nCar invRegs r = r := by
  rw [certSigmaJ, dif_neg (fun ⟨k, _, h⟩ => ha _ h), if_neg (ha _),
    dif_neg (fun ⟨j, _, h⟩ => ha j h), dif_neg (fun ⟨k, h⟩ => hr k h)]

end Sigma

/-- `certSigmaJ` on the argument names below `nInv + 1 + nCar` and the chain registers below
    `bound`, and `none` elsewhere. -/
def sigmaCJ (d nInv nCar : Nat) (invRegs : List String) (bound : Nat) (b : String) :
    Option String :=
  match (List.range nCar).find? (fun k => b == argName (nInv + 1 + k)) with
  | some k => some (regName (d + k))
  | none =>
      if b == argName nInv then some (loopIdx d)
      else match (List.range nInv).find? (fun j => b == argName j) with
        | some j =>
            some (invRegs.getD (nInv - 1 - j) ("Linv" ++ toString d ++ "_" ++ toString j))
        | none => match (List.range bound).find? (fun k => b == regName k) with
          | some k => some (loopReg d k)
          | none => none

theorem sigmaCJ_sound {d nInv nCar : Nat} {invRegs : List String} {bound : Nat}
    {b t : String} (h : sigmaCJ d nInv nCar invRegs bound b = some t) :
    certSigmaJ d nInv nCar invRegs b = t := by
  unfold sigmaCJ at h
  cases hf : (List.range nCar).find? (fun k => b == argName (nInv + 1 + k)) with
  | some k =>
      rw [hf] at h
      obtain rfl := Option.some.inj h
      have hb : b = argName (nInv + 1 + k) := by simpa using List.find?_some hf
      have hk : k < nCar := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      subst hb
      exact certSigmaJ_car hk
  | none =>
      rw [hf] at h
      have hnc : ∀ k, k < nCar → b ≠ argName (nInv + 1 + k) := by
        intro k hk he
        have := List.find?_eq_none.mp hf k (List.mem_range.mpr hk)
        simp [he] at this
      by_cases h2 : b = argName nInv
      · subst h2
        simp only [beq_self_eq_true, if_true, Option.some.injEq] at h
        rw [certSigmaJ_idx, h]
      rw [if_neg (by simpa using h2)] at h
      cases hg : (List.range nInv).find? (fun j => b == argName j) with
      | some j =>
          rw [hg] at h
          obtain rfl := Option.some.inj h
          have hb : b = argName j := by simpa using List.find?_some hg
          have hj : j < nInv := List.mem_range.mp (List.mem_of_find?_eq_some hg)
          subst hb
          exact certSigmaJ_inv hj
      | none =>
          rw [hg] at h
          cases hr : (List.range bound).find? (fun k => b == regName k) with
          | none => rw [hr] at h; cases h
          | some k =>
              rw [hr] at h
              obtain rfl := Option.some.inj h
              have hb : b = regName k := by simpa using List.find?_some hr
              subst hb
              exact certSigmaJ_reg k

/-- Every operand of a list is a register. -/
def allRegB (ops : List LOperand) : Bool :=
  ops.all (fun o => match o with | .reg _ => true | _ => false)

/-- A list of register operands is the registers of its names. -/
theorem eq_map_reg_of_allRegB : ∀ {ops : List LOperand}, allRegB ops = true →
    ops = (invRegsOf ops).map LOperand.reg
  | [], _ => rfl
  | o :: ops, h => by
      simp only [allRegB, List.all_cons, Bool.and_eq_true] at h
      cases o with
      | reg r =>
          have ih := eq_map_reg_of_allRegB (ops := ops) h.2
          simp only [invRegsOf, List.filterMap_cons, List.map_cons]
          exact congrArg _ ih
      | _ => simp at h

/-- **`certSigmaJ` is the export's loop renaming** for register invariant operands. -/
theorem certSigmaJ_loopRenJ {d nCar : Nat} {invOps : List LOperand}
    (hreg : allRegB invOps = true) :
    LoopRenJ (certSigmaJ d invOps.length nCar (invRegsOf invOps)) d nCar invOps where
  car := fun _ hk => certSigmaJ_car hk
  idx := certSigmaJ_idx
  inv := fun j hj => by
    have he := eq_map_reg_of_allRegB hreg
    have hl : (invRegsOf invOps).length = invOps.length := by
      conv_rhs => rw [he]
      simp
    rw [certSigmaJ_inv hj]
    conv_lhs => rw [he]
    rw [List.getD_eq_getElem _ _ (by simp [hl]; omega),
      List.getD_eq_getElem _ _ (by omega), List.getElem_map]
    simp only [List.length_map, hl]
  reg := certSigmaJ_reg

/-! ## 6. The certificate of a counted carried-register node -/

/-- No entry of a type list is an array. -/
def noArrB (rs : Ctxt jasminDialect) : Bool :=
  rs.all (fun t => match t with | .stackArr _ _ => false | _ => true)

theorem noArr_of_noArrB {rs : Ctxt jasminDialect} (h : noArrB rs = true) :
    ∀ w n, JasminTy.stackArr w n ∉ rs := by
  intro w n hm
  have := List.all_eq_true.mp h _ hm
  simp at this

/-- The seed source of the carried register `regName (d + k)`: the name of the seed operand of
    carried binder `nR - k`. -/
def srcsJ (initOps : List LOperand) (nR : Nat) (k : Nat) : String :=
  operandName (initOps.getD (nR - k) (.imm 0))

/-- `certRho` sends a name to `out` or fixes it. -/
theorem certRho_cases (d : Nat) (acc out : String) (Sl : List Nat) (r : String) :
    certRho d acc out Sl r = out ∨ certRho d acc out Sl r = r := by
  unfold certRho
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

section Cert

variable {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- The store slots of the model chain of a carried-register body. -/
abbrev certSlotsJ (update : MultiReturnCom jasminDialect
    (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    List Nat :=
  storeSlots (chainJ update) (nArgsJ rs invTys)

/-- The node renaming of a carried-register node at depth `d` with output register `out`:
    the array register `regName (d + rs.length)` and the store slots' body temporaries go to
    `out`. -/
abbrev rhoJ (d : Nat) (out : String) (update : MultiReturnCom jasminDialect
    (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    String → String :=
  certRho d (regName (d + rs.length)) out (certSlotsJ update)

/-- The loop renaming of a carried-register node. -/
noncomputable abbrev sigmaJ (d : Nat) (invOps : List LOperand) : String → String :=
  certSigmaJ d invTys.length (rs.length + 1) (invRegsOf invOps)

/-- The renamed carried seed moves of the export node. -/
abbrev seedsJ (d : Nat) (out : String) (initOps invOps : List LOperand)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    List LinstrRM :=
  (regsSeedsRM (forAccs d initOps update invOps)).map (renRM (rhoJ d out update))

/-- The renamed feedback of the export node. -/
abbrev feedJ (d : Nat) (out : String) (initOps invOps : List LOperand)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    List LinstrRM :=
  (regsFeedbackRM d (forTmp0 d update invOps)
    ((forAccs d initOps update invOps).map (·.1))
    ((forAccs d initOps update invOps).map (·.2.2))).map (renRM (rhoJ d out update))

/-- The computable image of a model name under the canonicalisation renaming. -/
def tauCJ (d : Nat) (out : String) (invOps : List LOperand)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (b : String) : Option String :=
  (sigmaCJ d invTys.length (rs.length + 1) (invRegsOf invOps)
    ((chainJ update).length + nArgsJ rs invTys) b).map (rhoJ d out update)

/-- **The export certificate of a counted carried-register node** at depth `d`, output
    register `out` and count register `c`: the body is in the fragment (`ArrMemN`,
    `ComExpOK`) and carries no second array; the invariant operands are registers, one per
    invariant; `out`, the loop index, the counter, `c`, the carried registers and the
    invariant base registers are pairwise distinct and fixed by the node renaming as the
    canonicalisation asks; the model chain has a thread certificate from the array argument
    to the returned array; and the renamed seeds and feedback are register-move lists that
    act as parallel assignments of the seed operands and of the renamed returned operands. -/
def exportCertJB (d : Nat) (out c : String)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (initOps invOps : List LOperand) : Bool :=
  let nInv := invTys.length
  let nR := rs.length
  let acc := regName (d + nR)
  let invRegs := invRegsOf invOps
  let Sl := certSlotsJ update
  (invOps.length == nInv) && allRegB invOps && noArrB rs
  && ExportCertFragment.arrMemNB update.toComHead
  && ExportCertFragment.comExpOKB update.toComHead
  && notLoopRegB out && out != loopIdx d && out != loopCtr d
  && fixB d acc Sl (loopIdx d) && fixB d acc Sl (loopCtr d) && fixB d acc Sl c
  && c != loopIdx d
  && (List.range nR).all (fun k => c != regName (d + k) && regName (d + k) != out)
  && invRegs.all (fun r => notLoopRegB r && fixB d acc Sl r && r != out && r != loopIdx d
      && r != loopCtr d && (List.range nR).all (fun k => r != regName (d + k)))
  && threadCertB (tauCJ d out invOps update) (nArgsJ rs invTys) Sl out (chainJ update)
      (nArgsJ rs invTys) (argName (nInv + nR + 1)) (headJ update)
  && (match movPairs? (seedsJ d out initOps invOps update) with
      | some ps => movesOKB ps && carOnlyB d nR ps && seedSrcB d nR ps (srcsJ initOps nR)
      | none => false)
  && (match movPairs? (feedJ d out initOps invOps update) with
      | some ps => movesOKB ps && carOnlyB d nR ps
          && feedSrcB d nR ps (tauCJ d out invOps update) (retsJ update)
      | none => false)

/-- The facts `forLoopRegsRM_export_faithful` asks of an accepted node. -/
structure ExportCertJ (d : Nat) (out c : String)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (initOps invOps : List LOperand) : Prop where
  /-- No carried register is an array. -/
  noArr : ∀ w' n', JasminTy.stackArr w' n' ∉ rs
  /-- One invariant operand per invariant. -/
  len : invOps.length = invTys.length
  /-- The invariant operands are registers. -/
  allReg : allRegB invOps = true
  /-- The body is in the array-returning stack-memory fragment. -/
  arrMem : ArrMemN update.toComHead
  /-- The body's ops are in the fragment's op set. -/
  expOK : JasminLsemExportShippedAnd.ComExpOK update.toComHead
  /-- The loop renaming. -/
  loopRen : LoopRenJ (sigmaJ (rs := rs) (invTys := invTys) d invOps) d (rs.length + 1) invOps
  /-- The node renaming fixes the loop index. -/
  idxFix : rhoJ d out update (loopIdx d) = loopIdx d
  /-- The node renaming fixes the counter. -/
  ctrFix : rhoJ d out update (loopCtr d) = loopCtr d
  /-- The node renaming fixes the count register. -/
  cntFix : rhoJ d out update c = c
  /-- The node renaming fixes the invariant base registers. -/
  invFix : ∀ r ∈ invRegsOf invOps, rhoJ d out update r = r
  /-- The canonicalisation renaming. -/
  canon : CanonRenJ (rhoJ d out update ∘ sigmaJ (rs := rs) (invTys := invTys) d invOps) d
    invTys.length rs.length (· ∈ certSlotsJ update) out
  /-- The thread certificate of the model chain. -/
  thread : ThreadCert (rhoJ d out update ∘ sigmaJ (rs := rs) (invTys := invTys) d invOps)
    (nArgsJ rs invTys) (· ∈ certSlotsJ update) out (chainJ update) (nArgsJ rs invTys)
    (argName (invTys.length + rs.length + 1)) (headJ update)
  /-- The renamed seeds are `Lopn`s the expansion fixes. -/
  seedOk : ∀ i ∈ seedsJ d out initOps invOps update, IsLopn i ∧ immShiftExpand i = [i]
  /-- The renamed feedback is `Lopn`s the expansion fixes. -/
  feedOk : ∀ i ∈ feedJ d out initOps invOps update, IsLopn i ∧ immShiftExpand i = [i]
  /-- The seed condition. -/
  seed : SeedOKJ d rs.length (srcsJ initOps rs.length) (seedsJ d out initOps invOps update)
  /-- The feedback condition. -/
  feed : FeedOKJ (rhoJ d out update ∘ sigmaJ (rs := rs) (invTys := invTys) d invOps) d
    rs.length (retsJ update) (feedJ d out initOps invOps update)
  /-- Each invariant base register is the image of an invariant argument. -/
  regs : ∀ r ∈ invRegsOf invOps, ∃ j, j < invTys.length
    ∧ r = (rhoJ d out update ∘ sigmaJ (rs := rs) (invTys := invTys) d invOps) (argName j)
  /-- The count register is not the loop index. -/
  cntIdx : c ≠ loopIdx d
  /-- The count register is no carried register. -/
  cntCar : ∀ k, k < rs.length → c ≠ regName (d + k)

/-- **Soundness of the export certificate of a carried-register node.** -/
theorem exportCertJB_sound {d : Nat} {out c : String}
    {update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)}
    {initOps invOps : List LOperand} (h : exportCertJB d out c update initOps invOps = true) :
    ExportCertJ d out c update initOps invOps := by
  unfold exportCertJB at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hreg⟩, hnoarr⟩, harrm⟩, hexp⟩, houtL⟩, houtI⟩, houtC⟩, hfI⟩,
    hfC⟩, hfc⟩, hcI⟩, hcar⟩, hinv⟩, hthr⟩, hseed⟩, hfeed⟩ := h
  set nInv := invTys.length
  set nR := rs.length
  set acc := regName (d + nR)
  set Sl := certSlotsJ update
  set invRegs := invRegsOf invOps
  set ρ := rhoJ d out update
  set σ := sigmaJ (rs := rs) (invTys := invTys) d invOps
  have hρdef : ρ = certRho d acc out Sl := rfl
  have he := eq_map_reg_of_allRegB hreg
  have hRlen : invRegs.length = nInv := by
    rw [← hlen]
    conv_rhs => rw [he]
    simp [invRegs]
  have hinv' : ∀ r ∈ invRegs, notLoopRegB r = true ∧ ρ r = r ∧ r ≠ out ∧ r ≠ loopIdx d
      ∧ r ≠ loopCtr d ∧ ∀ k, k < nR → r ≠ regName (d + k) := by
    intro r hr
    have := hinv r hr
    exact ⟨this.1.1.1.1.1, certRho_of_fixB this.1.1.1.1.2, this.1.1.1.2, this.1.1.2,
      this.1.2, this.2⟩
  have hσinv : ∀ j, j < nInv → σ (argName j) ∈ invRegs := by
    intro j hj
    show certSigmaJ _ _ _ _ _ ∈ _
    rw [certSigmaJ_inv hj]
    exact getD_mem_of_lt (by rw [hRlen]; omega) _
  have hidx : ρ (loopIdx d) = loopIdx d := certRho_of_fixB hfI
  have hctr : ρ (loopCtr d) = loopCtr d := certRho_of_fixB hfC
  have hcarFix : ∀ k, k < nR → ρ (regName (d + k)) = regName (d + k) := by
    intro k hk
    refine certRho_fix (fun he' => ?_) (fun k' _ he' => regName_ne_loopReg _ _ _ he')
    have := regName_injective he'
    omega
  have hσacc : σ (argName (nInv + nR + 1)) = acc := by
    show certSigmaJ _ _ _ _ _ = _
    rw [show nInv + nR + 1 = nInv + 1 + nR by omega, certSigmaJ_car (by omega)]
  have hσctr : σ (loopCtr d) = loopCtr d :=
    certSigmaJ_other (fun j => loopCtr_ne_argName d j) (fun k => loopCtr_ne_regName d k)
  -- every argument image is no body temporary
  have hargL : ∀ j, j < nArgsJ rs invTys → ∀ k, (ρ ∘ σ) (argName j) ≠ loopReg d k := by
    intro j hj k
    have hσL : σ (argName j) ≠ loopReg d k := by
      by_cases h1 : j < nInv
      · exact ne_loopReg_of_notLoopRegB (hinv' _ (hσinv j h1)).1 d k
      by_cases h2 : j = nInv
      · subst h2
        show certSigmaJ _ _ _ _ _ ≠ _
        rw [certSigmaJ_idx]
        exact loopIdx_ne_loopReg d d k
      · show certSigmaJ _ _ _ _ _ ≠ _
        rw [show j = nInv + 1 + (j - nInv - 1) by omega,
          certSigmaJ_car (by simp only [nArgsJ] at hj; omega)]
        exact regName_ne_loopReg _ _ _
    show ρ (σ (argName j)) ≠ _
    rcases certRho_cases d acc out Sl (σ (argName j)) with h3 | h3 <;> rw [hρdef, h3]
    · exact ne_loopReg_of_notLoopRegB houtL d k
    · exact hσL
  have hempty : (ρ ∘ σ) "" = "" := by
    show ρ (σ "") = ""
    rw [show σ "" = "" from certSigmaJ_other
      (fun j he' => ne_empty_of_head? (head?_argName j) he'.symm)
      (fun k he' => ne_empty_of_head? (head?_regName k) he'.symm)]
    exact certRho_fix (fun he' => ne_empty_of_head? (head?_regName _) he'.symm)
      (fun k _ he' => ne_empty_of_head? (head?_loopReg d k) he'.symm)
  have hcanon : CanonRenJ (ρ ∘ σ) d nInv nR (· ∈ Sl) out :=
    { fix := hempty
      tmp := fun k _ hS => by
        show ρ (σ (regName k)) = _
        rw [show σ (regName k) = loopReg d k from certSigmaJ_reg k]
        exact certRho_fix (loopReg_ne_regName d k _)
          (fun k' hk' he' => hS (by rw [loopReg_injective d he']; exact hk'))
      thr := fun k _ hS => by
        show ρ (σ (regName k)) = _
        rw [show σ (regName k) = loopReg d k from certSigmaJ_reg k]
        exact certRho_slot hS
      arg := fun j k hj => hargL j hj k
      outL := ne_loopReg_of_notLoopRegB houtL d
      acc := by
        show ρ (σ _) = _
        rw [hσacc]
        exact certRho_acc d acc out Sl
      car := fun k hk => by
        show ρ (σ _) = _
        rw [show σ (argName (nInv + 1 + k)) = regName (d + k) from certSigmaJ_car (by omega)]
        exact hcarFix k hk
      idx := by
        show ρ (σ _) = _
        rw [show σ (argName nInv) = loopIdx d from certSigmaJ_idx, hidx]
      ctr := by
        show ρ (σ _) = _
        rw [hσctr, hctr]
      invOut := fun j hj => by
        show ρ (σ _) ≠ _
        rw [(hinv' _ (hσinv j hj)).2.1]
        exact (hinv' _ (hσinv j hj)).2.2.1
      invIdx := fun j hj => by
        show ρ (σ _) ≠ _
        rw [(hinv' _ (hσinv j hj)).2.1]
        exact (hinv' _ (hσinv j hj)).2.2.2.1
      invCtr := fun j hj => by
        show ρ (σ _) ≠ _
        rw [(hinv' _ (hσinv j hj)).2.1]
        exact (hinv' _ (hσinv j hj)).2.2.2.2.1
      invCar := fun j hj k hk => by
        show ρ (σ _) ≠ _
        rw [(hinv' _ (hσinv j hj)).2.1]
        exact (hinv' _ (hσinv j hj)).2.2.2.2.2 k hk
      carOut := fun k hk => (hcar k hk).2
      outIdx := houtI
      outCtr := houtC
      ctrL := loopCtr_ne_loopReg d d }
  have htauC : ∀ b t, tauCJ d out invOps update b = some t → (ρ ∘ σ) b = t := by
    intro b t hb
    obtain ⟨t0, ht0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact congrArg ρ (sigmaCJ_sound ht0)
  -- the seed and feedback move lists
  cases hG : movPairs? (seedsJ d out initOps invOps update) with
  | none => rw [hG] at hseed; cases hseed
  | some psG =>
  rw [hG] at hseed
  simp only [Bool.and_eq_true] at hseed
  cases hF : movPairs? (feedJ d out initOps invOps update) with
  | none => rw [hF] at hfeed; cases hfeed
  | some psF =>
  rw [hF] at hfeed
  simp only [Bool.and_eq_true] at hfeed
  have hGe := movPairs?_sound hG
  have hFe := movPairs?_sound hF
  exact
    { noArr := noArr_of_noArrB hnoarr
      len := hlen
      allReg := hreg
      arrMem := ExportCertFragment.arrMemNB_sound _ harrm
      expOK := ExportCertFragment.comExpOKB_sound _ hexp
      loopRen := by
        have := certSigmaJ_loopRenJ (d := d) (nCar := rs.length + 1) hreg
        rw [hlen] at this
        exact this
      idxFix := hidx
      ctrFix := hctr
      cntFix := certRho_of_fixB hfc
      invFix := fun r hr => (hinv' r hr).2.1
      canon := hcanon
      thread := threadCertB_sound htauC _ _ _ _ hthr
      seedOk := by rw [hGe]; exact movesRM_ok psG
      feedOk := by rw [hFe]; exact movesRM_ok psF
      seed := by rw [hGe]; exact seedOKJ_of_check hseed.1.1 hseed.1.2 hseed.2
      feed := by rw [hFe]; exact feedOKJ_of_check htauC hfeed.1.1 hfeed.1.2 hfeed.2
      regs := fun r hr => by
        have hRlen' : (invRegsOf invOps).length = nInv := hRlen
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
        refine ⟨nInv - 1 - i, by omega, ?_⟩
        show _ = ρ (σ _)
        rw [show σ (argName (nInv - 1 - i)) = _ from certSigmaJ_inv (by omega),
          show nInv - 1 - (nInv - 1 - i) = i by omega, List.getD_eq_getElem _ _ hi,
          (hinv' _ (List.getElem_mem hi)).2.1]
      cntIdx := hcI
      cntCar := fun k hk => (hcar k hk).1 }

end Cert

/-! ## 7. The single counted carried-register program and its certified node -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (loopInvOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
  (AbiValOf AbiEntryM storeAgreesM_of_abi resolveVar_top loopInv_name invRegsOf_mem argIdx)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom hvToHom
  lookup_inlHom)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

section Program

variable {Γ : Ctxt jasminDialect} {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- The seed operands the export resolves for the carried seeds `inits`. -/
def loopInitOpsJ (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs)) :
    List LOperand :=
  exprArgsHV Γ.length Γ.length argName (fun _ => none) inits

/-- The program with one counted loop carrying `stackArr w n :: rs` and returning the array:
    `forLoopRegs update count inits invs` followed by the return of the final array. -/
def singleLoopJ
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) : ComLJ Γ (JasminTy.stackArr w n) :=
  .forLoopRegs update count inits invs (.lift (.ret .here))

/-- **The certified node**: the typed export node `forLoopRegsRM` at loop depth `Γ.length`,
    seeded from the export's seed operands with count register `c`, renamed by the node
    renaming `rhoJ` that sends the array register and the store slots to `out`. -/
def certNodeJ
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (out c : String) : List LinstrRM :=
  (forLoopRegsRM Γ.length (loopInitOpsJ inits) (.reg c) update (loopInvOps invs)).map
    (renRM (rhoJ Γ.length out update))

/-- **The gate of a single counted carried-register export**: the array seed and the count
    resolve to registers `out` and `c`, and the node passes `exportCertJB` there. -/
def singleLoopJB
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) : Bool :=
  match (loopInitOpsJ inits).getD 0 (.imm 0),
      resolveVar Γ.length Γ.length argName (fun _ => none) count with
  | .reg out, .reg c =>
      exportCertJB Γ.length out c update (loopInitOpsJ inits) (loopInvOps invs)
  | _, _ => false

/-- An accepted program resolves its array seed and count to registers and passes
    `exportCertJB`. -/
theorem singleLoopJB_spec
    {update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)}
    {count : Ctxt.Var Γ (JasminTy.reg 64)}
    {inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs)}
    {invs : HVector (fun ty => Ctxt.Var Γ ty) invTys}
    (h : singleLoopJB update count inits invs = true) :
    ∃ out c, (loopInitOpsJ inits).getD 0 (.imm 0) = .reg out
      ∧ resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c
      ∧ exportCertJB Γ.length out c update (loopInitOpsJ inits) (loopInvOps invs) = true := by
  unfold singleLoopJB at h
  split at h
  · next out c ho hc => exact ⟨out, c, ho, hc, h⟩
  · cases h

/-- Looking up a variable of a vector's type list in its looked-up arguments. -/
theorem lookupArgs_lookup (V : Ctxt.Valuation Γ) :
    ∀ {ts : Ctxt jasminDialect} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts) {t : JasminTy}
      (u : Ctxt.Var ts t), u.lookup (Expr.lookupArgs vs V) = (hvToHom vs u).lookup V
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ rest, _, .there u => lookupArgs_lookup V rest u

/-- The denotation of the single counted carried-register program: the array component of
    the `count`-fold of the body. -/
theorem singleLoopJ_denote
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (fuel : Nat) (V : Ctxt.Valuation Γ) :
    (singleLoopJ update count inits invs).denote fuel V
      = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup
          ((List.range (count.lookup V).toNat).foldl
            (fun a i => update.denote (tripValJ a i (Expr.lookupArgs invs V)))
            (Expr.lookupArgs inits V))) :=
  congrArg some (lookup_inlHom V (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _) _)

/-- **The certified node is the expanded canonicalised node**: the carried seeds and the
    index and counter seeds, then the zero-trip guarded flag loop over the expanded
    canonicalised body. -/
theorem certNodeJ_eq
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (out c : String)
    (hc : ExportCertJ Γ.length out c update (loopInitOpsJ inits) (loopInvOps invs)) :
    certNodeJ update inits invs out c
      = (seedsJ Γ.length out (loopInitOpsJ inits) (loopInvOps invs) update
          ++ idxCtrSeedsRM Γ.length c)
        ++ guardedFlagLoopLinstrRM Γ.length (Γ.length + 0x40000000) (loopCtr Γ.length)
          ((canonBodyJ (rhoJ Γ.length out update
              ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length (loopInvOps invs)) Γ.length update
            (feedJ Γ.length out (loopInitOpsJ inits) (loopInvOps invs) update)
            (invRegsOf (loopInvOps invs))).flatMap immShiftExpand) := by
  unfold certNodeJ
  rw [forLoopRegsRM_map_eq_canonNodeJ_expand _ _ update hc.len
    (JasminLsemExportShippedAnd.ComExpOK.opsPlain _ hc.expOK) hc.loopRen hc.idxFix hc.ctrFix
    hc.cntFix hc.invFix (fun i hi => (hc.seedOk i hi).2) (fun i hi => (hc.feedOk i hi).2)]
  unfold canonNodeJ
  rw [List.flatMap_append, JasminLsemExportShippedAnd.guardedFlagLoopLinstrRM_flatMap]
  congr 1
  refine JasminLsemExportShippedAnd.flatMap_immShiftExpand_of_fixed _ (fun i hi => ?_)
  rcases List.mem_append.mp hi with hi | hi
  · exact (hc.seedOk i hi).2
  · simp only [idxCtrSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact immShiftExpand_mov _ _ _

/-- **The gated single counted carried-register export from the System V entry.** For the
    program with one counted loop carrying the output array and registers that passes
    `singleLoopJB`: the array seed and the count resolve to registers `out` and `c`; and for
    every valuation that a layout reads off an entry state (`AbiValOf`) and every
    flag-machine ABI entry of that state (`AbiEntryM`), whenever the program denotes `v` at
    some fuel, `certNodeJ` halts under `lsemFuelMemF` with the array at `out` decoding to
    `v`. -/
theorem singleLoopJ_export_faithful_gate
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) (JasminTy.stackArr w n :: rs))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (h : singleLoopJB update count inits invs = true) :
    ∃ out c, (loopInitOpsJ inits).getD 0 (.imm 0) = .reg out
      ∧ resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c
      ∧ ∀ (σ : AbiLayout) (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM)
          (zf : Bool), AbiValOf σ sa V → AbiEntryM σ sa b0 →
          ∀ (fuel : Nat) (v : Fin n → BitVec w),
            (singleLoopJ update count inits invs).denote fuel V = some v →
            ∃ (k : Nat) (t : LstateMF),
              lsemFuelMemF (singletonProgM fn (certNodeJ update inits invs out c)) k
                  { prog := { base := b0, lfn := fn }, zf := zf } = some t
                ∧ decodeArrM t.prog.base out w n = some v := by
  obtain ⟨out, c, ho, hcn, hx⟩ := singleLoopJB_spec h
  have hc := exportCertJB_sound hx
  refine ⟨out, c, ho, hcn, fun σL sa V fn b0 zf hV hb fuel v hden => ?_⟩
  rw [singleLoopJ_denote] at hden
  obtain rfl := Option.some.inj hden
  have hag := storeAgreesM_of_abi hV hb
  set nInv := invTys.length
  set nR := rs.length
  set invRegs := invRegsOf (loopInvOps invs)
  have hRlen : invRegs.length = nInv := ExportCertEntry.invRegsOf_length invs
  have hτinv : ∀ j, j < nInv → (rhoJ Γ.length out update
      ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length (loopInvOps invs)) (argName j)
      = invRegs.getD (nInv - 1 - j) ("Linv" ++ toString Γ.length ++ "_" ++ toString j) := by
    intro j hj
    show rhoJ Γ.length out update (certSigmaJ _ _ _ _ _) = _
    rw [certSigmaJ_inv hj]
    exact hc.invFix _ (getD_mem_of_lt (by rw [hRlen]; omega) _)
  have hinvName : ∀ {τ : JasminTy} (u : Ctxt.Var invTys τ), ∃ v0 : Ctxt.Var Γ τ,
      (rhoJ Γ.length out update ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length
        (loopInvOps invs)) (argName (nInv - 1 - varIndex u)) = argName (argIdx v0)
      ∧ u.lookup (Expr.lookupArgs invs V) = v0.lookup V := by
    intro τ u
    have hu := JasminLsemSimulation.varIndex_lt u
    obtain ⟨v0, hv1, hv2⟩ := loopInv_name invs V u
    refine ⟨v0, ?_, hv2⟩
    rw [hτinv _ (by omega), show nInv - 1 - (nInv - 1 - varIndex u) = varIndex u by omega,
      List.getD_eq_getElem?_getD, hv1, Option.getD_some]
  have harr : b0.getArr out w n = some ((Ctxt.Var.here : Ctxt.Var
      (JasminTy.stackArr w n :: rs) _).lookup (Expr.lookupArgs inits V)) := by
    have h1 := exprArgsHV_getD Γ.length Γ.length inits
      (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _)
    rw [show varIndex (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _) = 0 from rfl]
      at h1
    have h2 := hag.2 (hvToHom inits (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _))
    rw [← h1] at h2
    change (loopInitOpsJ inits).getD 0 (.imm 0) = _ at h1
    rw [show exprArgsHV Γ.length Γ.length argName (fun _ => none) inits = loopInitOpsJ inits
      from rfl, ho] at h2
    rw [lookupArgs_lookup]
    exact h2
  have hcar : ∀ {w' : Nat} (u : Ctxt.Var rs (JasminTy.reg w')),
      b0.reg.getW (srcsJ (loopInitOpsJ inits) rs.length (rs.length - 1 - varIndex u)) w'
        = some ((Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup
            (Expr.lookupArgs inits V)) := by
    intro w' u
    have hu := JasminLsemSimulation.varIndex_lt u
    have h1 := exprArgsHV_getD Γ.length Γ.length inits
      (Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _)
    have h2 := hag.1
      (hvToHom inits (Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _))
    rw [resolveVar_top] at h1 h2
    rw [srcsJ, show rs.length - (rs.length - 1 - varIndex u)
      = varIndex (Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _) by
        simp only [varIndex]; omega,
      show loopInitOpsJ inits = exprArgsHV Γ.length Γ.length argName (fun _ => none) inits
        from rfl, h1, lookupArgs_lookup]
    exact h2
  have hinvR : ∀ {w' : Nat} (u : Ctxt.Var invTys (JasminTy.reg w')),
      b0.reg.getW ((rhoJ Γ.length out update ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length
        (loopInvOps invs)) (argName (nInv - 1 - varIndex u))) w'
        = some (u.lookup (Expr.lookupArgs invs V)) := by
    intro w' u
    obtain ⟨v0, h1, h2⟩ := hinvName u
    rw [h1, h2]
    have := hag.1 v0
    rw [resolveVar_top, evalOperandN] at this
    exact this
  have hinvA : ∀ {w' n' : Nat} (u : Ctxt.Var invTys (JasminTy.stackArr w' n')),
      b0.getArr ((rhoJ Γ.length out update ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length
        (loopInvOps invs)) (argName (nInv - 1 - varIndex u))) w' n'
        = some (u.lookup (Expr.lookupArgs invs V)) := by
    intro w' n' u
    obtain ⟨v0, h1, h2⟩ := hinvName u
    rw [h1, h2]
    have := hag.2 v0
    rw [resolveVar_top] at this
    exact this
  have hinv : ∀ j, j < nInv → (b0.reg.getW ((rhoJ Γ.length out update
      ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length (loopInvOps invs)) (argName j))
        64).isSome := by
    intro j hj
    have hmem : (rhoJ Γ.length out update ∘ sigmaJ (rs := rs) (invTys := invTys) Γ.length
        (loopInvOps invs)) (argName j) ∈ invRegs := by
      rw [hτinv j hj]
      exact getD_mem_of_lt (by rw [hRlen]; omega) _
    obtain ⟨t0, v0, hv⟩ := invRegsOf_mem invs _ hmem
    rw [hv]
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hV.arg v0)
    rw [hb.reg _ _ ha]
    rfl
  have hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 (count.lookup V).toNat) := by
    have hg := hag.1 count
    rw [hcn, evalOperandN] at hg
    rw [hg, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact forLoopRegsRM_export_faithful (σ := sigmaJ (rs := rs)
      (invTys := invTys) Γ.length (loopInvOps invs)) (ρ := rhoJ Γ.length out update)
    (d := Γ.length) (out := out) (c := c) hc.noArr (loopInitOpsJ inits) (loopInvOps invs)
    update hc.len hc.arrMem hc.expOK hc.loopRen hc.idxFix hc.ctrFix hc.cntFix hc.invFix
    hc.canon hc.thread hc.seedOk hc.feedOk (srcsJ (loopInitOpsJ inits) rs.length) hc.seed
    hc.feed hc.regs (Expr.lookupArgs invs V) fn hc.cntIdx hc.cntCar b0 zf hb.pc
    (Expr.lookupArgs inits V) harr hcar hinvR hinvA hinv (count.lookup V).toNat
    (count.lookup V).isLt hcnt

end Program

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopJ
