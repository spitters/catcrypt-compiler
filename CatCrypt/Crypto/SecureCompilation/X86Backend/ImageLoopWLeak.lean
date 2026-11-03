/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

@[expose] public section

set_option autoImplicit false

/-!
# The events of the loop route with carry chains and cell accesses

The route `CellFoldLReg.routeBW` compiles a loop node through the renaming of its loop, the
cell fold `cellFoldLR` of the renamed loop, the virtual body `virtBW`, the image of the cell
body of the printed body, the address machine on the printed body and the decoded bytes.
This module follows the events of the traced flag machine and of the address machine along
these comparisons, for a loop and a printed body with conditional branches.

Two runs of a program on the flag machine that start at one program counter and emit the
same events fetch the same instructions (`evalInstrPMemF_pc_det`): the event of a
conditional is the decision it takes. A trace that is computed from the events of each step
and the program counter of the step (`GTr`) is therefore equal for two such runs
(`gTr_eq`). The trace of the folded loop is of this form over the run of the renamed loop
(`cellFoldLR_gtr`), and the trace of the address machine on the printed body is of this form
over the run of the image of the cell body (`cell_image_addr_gtrW`).

## Main definitions

* `GTr`: a trace computed along a run of the flag machine from the program counter and the
  events of each step.
* `posTC`, `stepGC`: the events of the address machine at an instruction of a body with
  conditional branches under the gate with carry chains, from the events of its image.
* `foldG`: the events of an instruction of the folded loop from the events of the
  instruction of the loop.
* `routeEntryW`, `RouteEntryPubW`: the entry state of the virtual body `virtBW` and the
  public equality of two entry states.
* `LoopPubW`: public-equal entry machine states of the route, for a public equality of the
  entry states of the virtual body.

## Main results

* `evalInstrPMemF_pc_det`: two steps of one instruction from one program counter with equal
  events reach one program counter.
* `gTr_eq`: equal traces `GTr` of two runs with equal events.
* `cell_step_traceW`: one step of the image of the cell body with the events of the address
  machine.
* `cell_image_addr_gtrW`: the trace of the address machine on a body with cells, carry
  chains and conditional branches is `GTr` of the run of the image of its cell body.
* `cell_image_addr_ctW'`: constant time of the address machine on such a body from constant
  time of the image of its cell body.
* `keepReg_leak`, `foldOneLR_leak`: the events of a kept and of a folded instruction.
* `cellFoldLR_gtr`: the trace of the cell fold `cellFoldLR` of a body with branches.
* `virtBW_gtr`: the trace of the virtual body `virtBW` from a traced run of the node.
* `virtBW_memFCT`: constant time of the virtual body from the source events.
* `routeBW_entry`: the separation, cell frames, gate and relation at the entry of the route.
* `virtBW_checked_run`: the virtual body halts on checked runs.
* `loop_bytesW_ct`: constant time of the decoded bytes of the route `routeBW` from constant
  time of the virtual body `virtBW` and the check on traced runs.
* `loop_bytesW_ct_src`: constant time of the decoded bytes of the route from constant time
  of the source events of the single-loop program.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM singletonProgM
  findInstrMem evalJumpMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF evalInstrPMemF
  lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk
  evalInstrPMemFk evalInstrPMemF_of_k lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single decC
  evalInstrPMemF_cond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next
  NextPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime ConstantTimeRel)

/-! ## 1. Traces computed along a run of the flag machine -/

/-- **Two steps of one instruction from one program counter with equal events reach one
    program counter.** The event of a conditional is the decision it takes, and every other
    instruction has one successor. -/
theorem evalInstrPMemF_pc_det (P : LprogM) (i : LinstrRM) {s₁ s₂ t₁ t₂ : LstateMF}
    (hpc : s₁.prog.base.lpc = s₂.prog.base.lpc)
    (h₁ : evalInstrPMemF P i s₁ = some t₁) (h₂ : evalInstrPMemF P i s₂ = some t₂)
    (he : instrLeakF i s₁ = instrLeakF i s₂) : t₁.prog.base.lpc = t₂.prog.base.lpc := by
  have n₁ := (evalInstrPMemF_next P i s₁ t₁ h₁).2
  have n₂ := (evalInstrPMemF_next P i s₂ t₂ h₂).2
  obtain ⟨x, tag⟩ := i
  cases x with
  | Lcond c l =>
      rw [OwnedTVLeak.instrLeakF_cond, OwnedTVLeak.instrLeakF_cond] at he
      have hd : decC s₁ c = decC s₂ c := by simpa using he
      rw [evalInstrPMemF_cond] at h₁ h₂
      rw [hd] at h₁
      split at h₂
      · rename_i hdt
        rw [ite_eq_left hdt] at h₁
        obtain ⟨p₁, hp₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
        unfold evalJumpMem at hp₁ hp₂
        split at hp₁
        · rename_i q hq
          rw [hq] at hp₂
          cases hp₁
          cases hp₂
          rfl
        · cases hp₁
      · rename_i hdt
        rw [ite_eq_right hdt] at h₁
        cases h₁
        cases h₂
        show s₁.prog.base.lpc + 1 = s₂.prog.base.lpc + 1
        rw [hpc]
  | Lgoto tgt =>
      obtain ⟨f, l⟩ := tgt
      obtain ⟨q₁, hq₁, e₁⟩ := n₁
      obtain ⟨q₂, hq₂, e₂⟩ := n₂
      rw [hq₁] at hq₂
      cases hq₂
      rw [e₁, e₂]
  | Lret => exact n₁.elim
  | Lopn ds o ss => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]
  | Lsyscall _ => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]
  | Lcall _ _ => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]
  | Lalign => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]
  | Llabel _ _ => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]
  | Ligoto _ => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]
  | LstoreLabel _ _ => simp only [NextPc] at n₁ n₂; rw [n₁, n₂, hpc]

/-- **A trace computed along a run of the flag machine**: at each step, `G` of the program
    counter and of the events `instrLeakF` of the step. -/
inductive GTr (G : Nat → List CTLeak → List CTLeak) (P : LprogM) :
    LstateMF → List CTLeak → Prop
  | halt (s : LstateMF) (h : findInstrMem P s.prog = none) : GTr G P s []
  | step (s t : LstateMF) (i : LinstrRM) (g : List CTLeak)
      (hf : findInstrMem P s.prog = some i) (he : evalInstrPMemF P i s = some t)
      (h : GTr G P t g) : GTr G P s (G s.prog.base.lpc (instrLeakF i s) ++ g)

/-- **Equal computed traces of two runs with equal events.** Two terminating traced runs of
    a one-function program from states in that function at one program counter, with one
    trace, have one computed trace `GTr`. -/
theorem gTr_eq (G : Nat → List CTLeak → List CTLeak) (fn : String) (B : List LinstrRM) :
    ∀ (f₁ : Nat) (s₁ t₁ : LstateMF) (ℓ : List CTLeak),
      lsemFuelMemFLeak (singletonProgM fn B) f₁ s₁ = some (t₁, ℓ) →
      ∀ (f₂ : Nat) (s₂ t₂ : LstateMF),
        lsemFuelMemFLeak (singletonProgM fn B) f₂ s₂ = some (t₂, ℓ) →
        s₁.prog.lfn = fn → s₂.prog.lfn = fn → s₁.prog.base.lpc = s₂.prog.base.lpc →
        ∀ g₁ g₂, GTr G (singletonProgM fn B) s₁ g₁ → GTr G (singletonProgM fn B) s₂ g₂ →
          g₁ = g₂ := by
  set P := singletonProgM fn B
  have hfetch : ∀ s₁ s₂ : LstateMF, s₁.prog.lfn = fn → s₂.prog.lfn = fn →
      s₁.prog.base.lpc = s₂.prog.base.lpc →
      findInstrMem P s₁.prog = findInstrMem P s₂.prog := by
    intro s₁ s₂ h₁ h₂ hpc
    rw [findInstrMem_single h₁, findInstrMem_single h₂]
    exact congrArg (B[·]?) hpc
  have hnone : ∀ (s₁ s₂ : LstateMF) (g₁ g₂ : List CTLeak),
      findInstrMem P s₁.prog = none → findInstrMem P s₂.prog = none →
      GTr G P s₁ g₁ → GTr G P s₂ g₂ → g₁ = g₂ := by
    intro s₁ s₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂
    cases hg₁ with
    | step _ _ _ _ hf _ _ => rw [hf₁] at hf; cases hf
    | halt _ _ =>
        cases hg₂ with
        | step _ _ _ _ hf _ _ => rw [hf₂] at hf; cases hf
        | halt _ _ => rfl
  intro f₁
  induction f₁ with
  | zero =>
      intro s₁ t₁ ℓ h₁ f₂ s₂ t₂ h₂ hfn₁ hfn₂ hpc g₁ g₂ hg₁ hg₂
      cases hf : findInstrMem P s₁.prog with
      | some i => simp [lsemFuelMemFLeak, hf] at h₁
      | none => exact hnone s₁ s₂ g₁ g₂ hf (by rw [← hfetch s₁ s₂ hfn₁ hfn₂ hpc]; exact hf) hg₁ hg₂
  | succ n ih =>
      intro s₁ t₁ ℓ h₁ f₂ s₂ t₂ h₂ hfn₁ hfn₂ hpc g₁ g₂ hg₁ hg₂
      have hff := hfetch s₁ s₂ hfn₁ hfn₂ hpc
      cases hf : findInstrMem P s₁.prog with
      | none => exact hnone s₁ s₂ g₁ g₂ hf (by rw [← hff]; exact hf) hg₁ hg₂
      | some i =>
          have hf₂ : findInstrMem P s₂.prog = some i := by rw [← hff]; exact hf
          cases f₂ with
          | zero => simp [lsemFuelMemFLeak, hf₂] at h₂
          | succ m =>
              cases he₁ : evalInstrPMemF P i s₁ with
              | none => simp [lsemFuelMemFLeak, hf, he₁] at h₁
              | some u₁ =>
                  cases he₂ : evalInstrPMemF P i s₂ with
                  | none => simp [lsemFuelMemFLeak, hf₂, he₂] at h₂
                  | some u₂ =>
                      rw [lsemFuelMemFLeak_step P _ i s₁ u₁ hf he₁] at h₁
                      rw [lsemFuelMemFLeak_step P _ i s₂ u₂ hf₂ he₂] at h₂
                      obtain ⟨q₁, hq₁, hqe₁⟩ := Option.map_eq_some_iff.mp h₁
                      obtain ⟨q₂, hq₂, hqe₂⟩ := Option.map_eq_some_iff.mp h₂
                      have hℓ : instrLeakF i s₁ ++ q₁.2 = instrLeakF i s₂ ++ q₂.2 :=
                        (congrArg Prod.snd hqe₁).trans (congrArg Prod.snd hqe₂).symm
                      obtain ⟨hev, hrest⟩ := List.append_inj hℓ
                        ((instrLeakF_length i s₁).trans (instrLeakF_length i s₂).symm)
                      have hpc' := evalInstrPMemF_pc_det P i hpc he₁ he₂ hev
                      have hfn₁' := (evalInstrPMemF_next P i s₁ u₁ he₁).1.trans hfn₁
                      have hfn₂' := (evalInstrPMemF_next P i s₂ u₂ he₂).1.trans hfn₂
                      cases hg₁ with
                      | halt _ h0 => rw [hf] at h0; cases h0
                      | step _ v₁ j₁ g₁' hfj₁ hej₁ hg₁' =>
                          cases hg₂ with
                          | halt _ h0 => rw [hf₂] at h0; cases h0
                          | step _ v₂ j₂ g₂' hfj₂ hej₂ hg₂' =>
                              rw [hf] at hfj₁
                              cases hfj₁
                              rw [hf₂] at hfj₂
                              cases hfj₂
                              rw [he₁] at hej₁
                              cases hej₁
                              rw [he₂] at hej₂
                              cases hej₂
                              have hq₂' : lsemFuelMemFLeak P m u₂ = some (q₂.1, q₁.2) := by
                                rw [hq₂, hrest]
                              rw [ih u₁ q₁.1 q₁.2 hq₁ m u₂ q₂.1 hq₂' hfn₁' hfn₂' hpc' g₁' g₂'
                                hg₁' hg₂', hev, hpc]

/-! ## 2. One step of the image of a cell body with its events -/

section CellStep

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel haltedA_of)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (ImgRelW imgGateBW img_stepW
  ptr_of_reloadW haltedA_of_imgW instrGateBW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond (img_stepW_cond
  gateAtW_cond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop (cellMove_lcond
  cellMove_llabel lcond_of_cellMove llabel_of_cellMove labelAt_cellBody stepA_cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (posTW step_leakW
  stepLeakA_cellBodyW cellA?_cellBody)

/-- **The events of the address machine at an instruction of a body with conditional
    branches under the gate with carry chains**, from its image instruction `i` and the events
    `e` of `i`: `e` at a conditional branch, `posTW` of `i` and `e` at every other
    instruction. -/
def posTC (frame : String → Option (BitVec 64)) (base : String → BitVec 64) (s0 : LstateA)
    (x : LinstrR) (i : LinstrRM) (e : List CTLeak) : List CTLeak :=
  match x with
  | .Lcond _ _ => e
  | _ => posTW frame base s0 x i e

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx (CidxInv imgGateCW exemptC
  imgGateW_of_imgGateCW imgGateCW_of_imgGateBW cidxInv_of_imgGateBW cidxInv_step cidxInv_store
  rel_cidxStoreW cidxArmB_spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (ImgGateW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (step_leakWG
  step_leakCidx stepLeakA_cellBody_of_ptr)

/-- **One step of the image of the cell body with the events of the address machine, with
    indexed stores through a cell.** From states related by `ImgRelW` with the invariant of the
    window `CidxInv`, a checked step of the image of the instruction `bi` of the cell body of a
    body that passes the gate `imgGateCW` leads to a state related to an address state `sa'`,
    with the invariant; every traced run of the address machine on the body from `sa'` extends
    to a traced run from the start whose trace is prefixed by `posTC` of the events of the
    image instruction, at every fixed state `s0`. At an indexed store through a cell the
    events are those of `ImageStraightCellsLeak.step_leakCidx`. -/
theorem cell_step_traceCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateCW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (s0 : LstateA) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa s.zf)
    (hinv : CidxInv slotArr base (cellBody slotArr body) s) {bi : Linstr}
    (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t) :
    ∃ sa', ImgRelW frame slotArr base (cellBody slotArr body) t sa' t.zf
      ∧ CidxInv slotArr base (cellBody slotArr body) t
      ∧ ∀ fuel r ℓ, runALeak frame body fuel sa' t.zf = some (r, ℓ) →
          ∃ fuel', runALeak frame body fuel' sa s.zf = some (r,
            posTC frame base s0 bi.li_i
              (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i)
              (instrLeakF (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s)
              ++ ℓ) := by
  have hG := imgGateW_of_imgGateCW hgate
  have hb' := hb
  rw [cellBody_getElem?] at hb'
  obtain ⟨b0, hb0, hbe⟩ := Option.map_eq_some_iff.mp hb'
  have hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
      DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A) := by
    intro B A m hacc hg hBf
    obtain ⟨q, -, hpA⟩ := ImgGateW.ptr_of_reloadW hsep hG hrel
      (accArr_cellBody hN (hasPrefix_gpName hg) hacc) hBf
    exact hpA
  by_cases hX : exemptC frame slotArr (cellBody slotArr body) sa.reg.lpc
  · simp only [exemptC, hb, Option.any_some] at hX
    have harm := (Bool.and_eq_true_iff.mp hX).1
    obtain ⟨A, n, idx, v, c0, D, hst, hx, -, -⟩ := cidxArmB_spec harm
    have hnc' : ∀ cc l, bi.li_i ≠ .Lcond cc l := by rw [hx]; simp
    have he' := hstep
    rw [JasminLsemAddrImage.imgInstr_cellIdxStore slotArr hst] at he'
    obtain ⟨sa1, hst1, hr⟩ := rel_cidxStoreW hsep hphys _ hrel hinv hb harm hst he'
    obtain ⟨-, he⟩ := stepA_cellBody hF hptr s.zf
    have hh : haltedA body sa = false := by
      rw [← haltedA_cellBody slotArr]; exact haltedA_of hb (by rw [hx]; simp)
    have hL : stepLeakA frame body sa s.zf = posTW frame base s0 bi.li_i
        (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i)
        (instrLeakF (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s) := by
      rw [stepLeakA_cellBody_of_ptr hF hb0 (fun B A m hacc hBf hgp => hptr B A m hacc hgp hBf)]
      exact step_leakCidx hrel hinv hb harm _ hstep s0
    have hpT : ∀ i e, posTC frame base s0 bi.li_i i e = posTW frame base s0 bi.li_i i e := by
      intro i e
      unfold posTC
      split
      · rename_i heq
        exact absurd heq (hnc' _ _)
      · rfl
    refine ⟨sa1, hr, cidxInv_store _ hb hrel.pc.symm hst he', fun fuel r ℓ h => ⟨fuel + 1, ?_⟩⟩
    rw [runALeak_step frame body fuel sa s.zf hh, he, hst1, Option.bind_some, h, hL, hpT]
    rfl
  have hinv' := cidxInv_step hsep hG fn hrel hinv hb hlt hX hstep
  by_cases hcnd : ∃ cc l, b0.li_i = .Lcond cc l
  · obtain ⟨cnd, l, hx⟩ := hcnd
    have hbi : bi = b0 := by rw [← hbe, cellMove_lcond slotArr body _ hx]
    subst hbi
    have hg : instrGateBW frame slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i = true :=
      hG.instr _ _ hb (by omega) hX
    obtain ⟨cc, pol, p, rfl, hpol, hp, -⟩ := gateAtW_cond hx hg
    obtain ⟨-, -, -, sa1, hst, hcase⟩ :=
      ImageAddrSimWCond.ImgGateW.img_stepW_cond (rsp := rsp) hphys hG fn hrel hb hlt hX hx hstep
    have he : stepA frame body sa s.zf = stepA frame (cellBody slotArr body) sa s.zf := by
      unfold stepA
      rw [hb, hb0]
      obtain ⟨ii, li⟩ := bi
      simp only at hx
      subst hx
      simp only [labelAt_cellBody]
    have hh : haltedA body sa = false := haltedA_of hb0 (by rw [hx]; simp)
    have hL1 : stepLeakA frame body sa s.zf = [.branch (s.zf == pol)] := by
      obtain ⟨ii, li⟩ := bi
      simp only at hx
      subst hx
      simp only [stepLeakA, hb0, hpol]
    have hev : instrLeakF (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s
        = [.branch (s.zf == pol)] := by
      have hi : imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i
          = (bi.li_i, .reg none) := by rw [hx]; rfl
      have hcc : OwnedLprogTV.ccPol (.reg cc) = some pol := by
        revert hpol
        unfold condPol OwnedLprogTV.ccPol
        split <;> simp_all
      rw [hi, hx, OwnedTVLeak.instrLeakF_cond]
      unfold decC
      rw [hcc]
    have hpT : posTC frame base s0 bi.li_i
        (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i)
        (instrLeakF (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s)
        = [.branch (s.zf == pol)] := by
      rw [hev, hx]
      rfl
    have one : ∀ fuel r ℓ, runALeak frame body fuel sa1 t.zf = some (r, ℓ) →
        runALeak frame body (fuel + 1) sa s.zf = some (r, [.branch (s.zf == pol)] ++ ℓ) := by
      intro fuel r ℓ h
      rw [runALeak_step frame body fuel sa s.zf hh, he, hst, Option.bind_some, h, hL1]
      rfl
    rcases hcase with hrel1 | ⟨⟨bp, ii', l', hbp, hli⟩, -, -, sa2, hst2, hrel2⟩
    · exact ⟨sa1, hrel1, hinv', fun fuel r ℓ h => ⟨_, by rw [hpT]; exact one fuel r ℓ h⟩⟩
    · rw [cellBody_getElem?] at hbp
      obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp hbp
      have hl1 := llabel_of_cellMove hli
      have hC1 : (cellBody slotArr body)[sa1.reg.lpc]? = some b1 := by
        rw [cellBody_getElem?, hb1, Option.map_some, cellMove_llabel slotArr body _ hl1]
      have e : ∀ c' : Lcmd, c'[sa1.reg.lpc]? = some b1 →
          stepA frame c' sa1 t.zf = some (sa1.setLpc (sa1.reg.lpc + 1), t.zf) := by
        intro c' h'
        obtain ⟨i1, li1⟩ := b1
        simp only at hl1
        subst hl1
        simp [stepA, h']
      rw [e _ hC1] at hst2
      have hL2 : stepLeakA frame body sa1 t.zf = [] := by
        obtain ⟨i1, li1⟩ := b1
        simp only at hl1
        subst hl1
        simp [stepLeakA, hb1]
      refine ⟨sa2, hrel2, hinv', fun fuel r ℓ h => ⟨fuel + 2, ?_⟩⟩
      rw [hpT]
      refine one (fuel + 1) r ℓ ?_
      rw [runALeak_step frame body fuel sa1 t.zf (haltedA_of hb1 (by rw [hl1]; simp)), e _ hb1,
        hst2, Option.bind_some, h, hL2]
      rfl
  · have hnc' : ∀ cc l, bi.li_i ≠ .Lcond cc l := fun cc l he =>
      hcnd ⟨cc, l, lcond_of_cellMove (hbe ▸ he)⟩
    obtain ⟨hh, -, sa1, hst, hr⟩ :=
      ImgGateW.img_stepW hsep hphys hG _ hrel hb hlt hX hnc' hstep
    obtain ⟨-, he⟩ := stepA_cellBody hF hptr s.zf
    have hL : stepLeakA frame body sa s.zf = posTW frame base s0 bi.li_i
        (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i)
        (instrLeakF (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s) := by
      rw [stepLeakA_cellBody_of_ptr hF hb0 (fun B A m hacc hBf hgp => hptr B A m hacc hgp hBf)]
      exact step_leakWG hsep hG hrel hlt hb hX (cellA?_cellBody hF hb) hnc' s0
    have hpT : ∀ i e, posTC frame base s0 bi.li_i i e = posTW frame base s0 bi.li_i i e := by
      intro i
      intro e
      unfold posTC
      split
      · rename_i heq
        exact absurd heq (hnc' _ _)
      · rfl
    refine ⟨sa1, hr, hinv', fun fuel r ℓ h => ⟨fuel + 1, ?_⟩⟩
    rw [runALeak_step frame body fuel sa s.zf (by rw [← haltedA_cellBody slotArr]; exact hh),
      he, hst, Option.bind_some, h, hL, hpT]
    rfl

/-- **One step of the image of the cell body with the events of the address machine.**
    `cell_step_traceCW` at a body that passes `imgGateBW`, at which the invariant of the window
    holds at every state (`ImageAddrCidx.cidxInv_of_imgGateBW`). -/
theorem cell_step_traceW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (s0 : LstateA) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa s.zf) {bi : Linstr}
    (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t) :
    ∃ sa', ImgRelW frame slotArr base (cellBody slotArr body) t sa' t.zf
      ∧ ∀ fuel r ℓ, runALeak frame body fuel sa' t.zf = some (r, ℓ) →
          ∃ fuel', runALeak frame body fuel' sa s.zf = some (r,
            posTC frame base s0 bi.li_i
              (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i)
              (instrLeakF (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s)
              ++ ℓ) := by
  obtain ⟨sa', h1, -, h2⟩ := cell_step_traceCW hsep hphys (imgGateCW_of_imgGateBW hgate) hN hF fn
    s0 hrel (cidxInv_of_imgGateBW hgate base s) hb hlt hstep
  exact ⟨sa', h1, h2⟩

/-! ## 3. The run of the image of a cell body and constant time -/

/-- The map of `GTr` for the address machine: `posTC` at the instruction of the cell body
    `cb` at the program counter and its image. -/
def stepGC (frame : String → Option (BitVec 64)) (base : String → BitVec 64) (s0 : LstateA)
    (slotArr : String → Option (String × Nat)) (cb : Lcmd) (k : Nat) (e : List CTLeak) :
    List CTLeak :=
  match cb[k]? with
  | some bi => posTC frame base s0 bi.li_i (imgInstr slotArr cb k bi.li_i) e
  | none => []

/-- **The traced image simulation of a cell body with carry chains, conditional branches and
    indexed stores through a cell.** For a printed body whose cell body passes the gate
    `imgGateCW` and the class
    `physImgB`, at a separation `ImgSep` and cell frames `CellFrames`, every halting checked
    run of the image of the cell body from a state related to an address state, with the
    invariant of the window, has a traced
    run, and is matched by a halting traced run of the address machine on the body whose
    trace is the trace `GTr` computed along the run of the image by `stepGC`, at every fixed
    state `s0`. -/
theorem cell_image_addr_gtrCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateCW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (s0 : LstateA) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRelW frame slotArr base (cellBody slotArr body) s sa zf →
      CidxInv slotArr base (cellBody slotArr body) s →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
        = some t →
      ∃ ℓ g fuel' r,
        lsemFuelMemFLeak (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
          = some (t, ℓ)
        ∧ GTr (stepGC frame base s0 slotArr (cellBody slotArr body))
            (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) s g
        ∧ runALeak frame body fuel' sa zf = some (r, g) := by
  have hG := imgGateW_of_imgGateCW hgate
  set cb := cellBody slotArr body with hcb
  set P := singletonProgM fn (virtImg slotArr cb)
  have halt : ∀ (s : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRelW frame slotArr base cb s sa zf → findInstrMem P s.prog = none →
      ∀ fuel, ∃ ℓ g fuel' r, lsemFuelMemFLeak P fuel s = some (s, ℓ)
        ∧ GTr (stepGC frame base s0 slotArr cb) P s g
        ∧ runALeak frame body fuel' sa zf = some (r, g) := by
    intro s sa zf hfn hrel hf fuel
    have hh := ImgGateW.haltedA_of_imgW hG fn hfn hrel.pc hf
    rw [haltedA_cellBody] at hh
    exact ⟨[], [], 0, (sa, zf), lsemFuelMemFLeak_halt P fuel s hf, .halt s hf,
      runALeak_halt frame body 0 sa zf hh⟩
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hinv hrun
      cases hf : findInstrMem P s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf 0
  | succ f ih =>
      intro s t sa zf hfn hrel hinv hrun
      cases hf : findInstrMem P s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf (f + 1)
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true P i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              have hev := evalInstrPMemF_of_k he
              have hfn1 : s1.prog.lfn = fn := (evalInstrPMemF_next _ i s s1 hev).1.trans hfn
              have hz := hrel.zf
              subst hz
              have hfetch := hf
              rw [findInstrMem_single hfn, virtImg_getElem?, ← hrel.pc,
                List.getElem?_dropLast] at hfetch
              split at hfetch
              case isFalse => cases hfetch
              rename_i hlt
              obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hfetch
              obtain ⟨sa', hrel', hinv', hcomp⟩ :=
                cell_step_traceCW hsep hphys hgate hN hF fn s0 hrel hinv hb hlt he
              obtain ⟨ℓ', g', f', r, hl', hg', hr'⟩ := ih s1 t sa' s1.zf hfn1 hrel' hinv' hrun
              obtain ⟨f'', hr''⟩ := hcomp f' r g' hr'
              have hG : stepGC frame base s0 slotArr cb s.prog.base.lpc
                  (instrLeakF (imgInstr slotArr cb sa.reg.lpc bi.li_i) s)
                  = posTC frame base s0 bi.li_i (imgInstr slotArr cb sa.reg.lpc bi.li_i)
                    (instrLeakF (imgInstr slotArr cb sa.reg.lpc bi.li_i) s) := by
                have hpc : s.prog.base.lpc = sa.reg.lpc := hrel.pc.symm
                unfold stepGC
                rw [hpc, hb]
              refine ⟨instrLeakF (imgInstr slotArr cb sa.reg.lpc bi.li_i) s ++ ℓ', _, f'', r,
                ?_, ?_, hr''⟩
              · rw [lsemFuelMemFLeak_step P f _ s s1 hf hev, hl']
                rfl
              · rw [← hG]
                exact .step s s1 _ g' hf hev hg'

/-- **The traced image simulation of a cell body with carry chains and conditional
    branches.** `cell_image_addr_gtrCW` at a cell body that passes `imgGateBW`, at which the
    invariant of the window holds at every state. -/
theorem cell_image_addr_gtrW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (s0 : LstateA) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRelW frame slotArr base (cellBody slotArr body) s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
        = some t →
      ∃ ℓ g fuel' r,
        lsemFuelMemFLeak (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
          = some (t, ℓ)
        ∧ GTr (stepGC frame base s0 slotArr (cellBody slotArr body))
            (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) s g
        ∧ runALeak frame body fuel' sa zf = some (r, g) :=
  fun fuel s t sa zf hfn hrel hrun =>
    cell_image_addr_gtrCW hsep hphys (imgGateCW_of_imgGateBW hgate) hN hF fn s0 fuel s t sa zf
      hfn hrel (cidxInv_of_imgGateBW hgate base s) hrun

/-- `ImageAddrLeakPhys.AddrPub` with the invariant of the window `CidxInv` at the two image
    states. -/
def AddrPubC (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (body : Lcmd) (fn : String)
    (pubEq : LstateMF → LstateMF → Prop) (a₁ a₂ : LstateA × Bool) : Prop :=
  ∃ s₁ s₂ : LstateMF, pubEq s₁ s₂ ∧ s₁.prog.base.reg.lpc = s₂.prog.base.reg.lpc
    ∧ s₁.prog.lfn = fn ∧ s₂.prog.lfn = fn
    ∧ ImgRel frame slotArr base body s₁ a₁.1 a₁.2 ∧ ImgRel frame slotArr base body s₂ a₂.1 a₂.2
    ∧ CidxInv slotArr base body s₁ ∧ CidxInv slotArr base body s₂
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) f s₁ = some t)
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) f s₂ = some t)

/-- **Constant time of the address machine on a body from constant time of the image of its
    cell body, with carry chains, conditional branches and indexed stores through a cell**,
    between address states public-equal with the invariant of the window (`AddrPubC`). -/
theorem cell_image_addr_ctCW' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateCW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) pubEq) :
    ConstantTimeRel (AddrPubC frame slotArr base (cellBody slotArr body) fn pubEq)
      (ARun frame body) := by
  rintro ⟨sa₁, zf₁⟩ ⟨sa₂, zf₂⟩ ℓ₁ ℓ₂
    ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, hi₁, hi₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hA₁⟩ ⟨g₂, r₂, hA₂⟩
  obtain ⟨v₁, c₁, F₁, q₁, hv₁, hG₁, hL₁⟩ :=
    cell_image_addr_gtrCW hsep hphys hgate hN hF fn sa₁ f₁ s₁ t₁ sa₁ zf₁ hfn₁
      (ImageAddrSimW.imgRelW_of hr₁) hi₁ hk₁
  obtain ⟨v₂, c₂, F₂, q₂, hv₂, hG₂, hL₂⟩ :=
    cell_image_addr_gtrCW hsep hphys hgate hN hF fn sa₁ f₂ s₂ t₂ sa₂ zf₂ hfn₂
      (ImageAddrSimW.imgRelW_of hr₂) hi₂ hk₂
  have hv : v₁ = v₂ := hct s₁ s₂ v₁ v₂ hpub ⟨f₁, t₁, hv₁⟩ ⟨f₂, t₂, hv₂⟩
  subst hv
  have hc : c₁ = c₂ := gTr_eq _ fn _ f₁ s₁ t₁ v₁ hv₁ f₂ s₂ t₂ hv₂ hfn₁ hfn₂ hpc c₁ c₂ hG₁ hG₂
  have e₁ := congrArg Prod.snd (runALeak_det frame body g₁ F₁ sa₁ zf₁ _ _ hA₁ hL₁)
  have e₂ := congrArg Prod.snd (runALeak_det frame body g₂ F₂ sa₂ zf₂ _ _ hA₂ hL₂)
  simp only at e₁ e₂
  rw [e₁, e₂, hc]

/-- **Constant time of the address machine on a body from constant time of the image of its
    cell body, with carry chains and conditional branches.**
    `ImageStraightCellsLeak.cell_image_addr_ctW` without the restriction to bodies with no
    conditional branch: `cell_image_addr_ctCW'` at a cell body that passes `imgGateBW`, at which
    the invariant of the window holds at every state. -/
theorem cell_image_addr_ctW' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) pubEq) :
    ConstantTimeRel (AddrPub frame slotArr base (cellBody slotArr body) fn pubEq)
      (ARun frame body) := by
  rintro a₁ a₂ ℓ₁ ℓ₂ ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, hk₁, hk₂⟩ hA₁ hA₂
  exact cell_image_addr_ctCW' hsep hphys (imgGateCW_of_imgGateBW hgate) hN hF fn hct a₁ a₂ ℓ₁ ℓ₂
    ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, cidxInv_of_imgGateBW hgate base s₁,
      cidxInv_of_imgGateBW hgate base s₂, hk₁, hk₂⟩ hA₁ hA₂

end CellStep

/-! ## 4. The events of the cell fold of a body with branches -/

section Fold

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (findInstrMem_singleton)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (CtlI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (instrLeakF_ctl)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (foldOne_leak
  instrLeakB_length)

/-- The map of `GTr` for the cell fold: the first `evCountF` events of the step, counted at
    the instruction of the folded body `is'` at the program counter. -/
def foldG (is' : List LinstrRM) (k : Nat) (e : List CTLeak) : List CTLeak :=
  match is'[k]? with
  | some i' => e.take (evCountF i')
  | none => []

/-- An `Lopn` emits the same events from two register files that agree on the index
    registers of its indexed operands. -/
theorem instrLeakB_agree_idx {ds ss : List LOperand} {o : String} {tag : JasminLsemMem.MemTag}
    {r r' : LstateN}
    (h : ∀ b q sc, LOperand.arrIdx b q sc ∈ ds ++ ss → r'.lvm q = r.lvm q) :
    instrLeakB r' (.Lopn ds o ss, tag) = instrLeakB r (.Lopn ds o ss, tag) := by
  simp only [instrLeakB]
  split_ifs
  · rfl
  refine List.flatMap_congr fun x hx => ?_
  cases x with
  | arrIdx b q sc =>
      simp only [opLeakF, idxVal]
      rw [h b q sc hx]
  | _ => rfl

/-- **The events of an instruction kept with slot-array names as registers.** From
    cell-related states, an instruction of `keepRegB` emits the same events. -/
theorem keepReg_leak {R : Slots} {env : KEnv} {i : LinstrRM} (hk : keepRegB R i = true)
    {s s' : LstateM} (hC : CellRel R env s s') : instrLeakB s'.reg i = instrLeakB s.reg i := by
  simp only [keepRegB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨hl, -⟩, hd⟩, hr⟩, -⟩ := hk
  obtain ⟨w, tag⟩ := i
  obtain ⟨ds, o, ss, hdd⟩ := isLopnB_isLopn hl
  simp only at hdd
  subst hdd
  refine instrLeakB_agree_idx fun b q sc hm => hC.reg q ?_
  rcases List.mem_append.mp hm with hm | hm
  · refine hd q ?_
    simp only [dstNames, List.mem_flatMap]
    exact ⟨_, hm, by simp [opNames]⟩
  · refine hr q ?_
    simp only [readNames, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨_, hm, by simp [srcNames]⟩

/-- **The events of a folded instruction of a body.** From cell-related states, the fold
    `foldOneLR` of an instruction emits the first `evCountF` events of the instruction,
    counted at the fold: none where an indexed access at a known index is folded into a
    cell copy, all of them at every other instruction. -/
theorem foldOneLR_leak {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOneLR R env i = some i') {s s' : LstateMF} (hC : CellRelF R env s s') :
    instrLeakF i' s' = (instrLeakF i s).take (evCountF i') := by
  rcases foldOneLR_cases hf with ⟨hl, hl', hfo⟩ | ⟨-, hc, rfl⟩
  · rw [instrLeakF_of_lopn (isLopnB_isLopn hl') s', instrLeakF_of_lopn (isLopnB_isLopn hl) s]
    unfold foldOneR at hfo
    split at hfo
    · rename_i j hj
      cases hfo
      exact foldOne_leak hj hC.base
    · split at hfo
      · rename_i hk
        cases hfo
        rw [keepReg_leak hk hC.base, ← instrLeakB_length (isLopnB_isLopn hl) s.prog.base.reg,
          List.take_length]
      · cases hfo
  · have hi : CtlI i' := by
      obtain ⟨w, tg⟩ := i'
      unfold ctlB at hc
      dsimp only at hc
      split at hc
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr (Or.inr ⟨_, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, _, rfl, Option.isSome_iff_ne_none.mp hc⟩)
      · cases hc
    rw [instrLeakF_ctl hi hC.zf, ← instrLeakF_length i' s, List.take_length]

/-- **The trace of the cell fold of a body with branches.** For slot arrays `R` that pass
    `slotsOkB` and `cellsDistinctB` and a body `is` whose cell fold `cellFoldLR` from the
    constants `e0` is `is'`: a halting run of `is` on the flag machine from `s` is matched,
    with the same fuel, by a traced run of `is'` from every state `s'` cell-related to `s`
    under the constants known at the program counter of `s`, whose trace is the trace `GTr`
    computed along the run of `is` by `foldG`. -/
theorem cellFoldLR_gtr {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    {e0 : KEnv} {is is' : List LinstrRM} (hf : cellFoldLR R e0 is = some is') (fn : String) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      lsemFuelMemF (singletonProgM fn is) fuel s = some t →
      ∃ t' g, lsemFuelMemFLeak (singletonProgM fn is') fuel s' = some (t', g)
        ∧ GTr (foldG is') (singletonProgM fn is) s g := by
  have hfetch : ∀ {s s' : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      findInstrMem (singletonProgM fn is) s.prog = none →
      findInstrMem (singletonProgM fn is') s'.prog = none := fun {s s'} hC h => by
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hC.base.pc
    by_cases hfn : s.prog.lfn = fn
    · rw [findInstrMem_singleton _ _ _ hfn] at h
      rw [findInstrMem_singleton _ _ _ (hC.lfn.trans hfn), hpc]
      rw [List.getElem?_eq_none_iff] at h ⊢
      rw [cellFoldLR_length is e0 is' hf]
      exact h
    · exact ite_eq_right fun h' => hfn (hC.lfn.symm.trans h')
  have hfetch' : ∀ {s s' : LstateMF} {i : LinstrRM},
      CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      findInstrMem (singletonProgM fn is) s.prog = some i →
      is[s.prog.base.lpc]? = some i
        ∧ ∀ i', is'[s.prog.base.lpc]? = some i' →
          findInstrMem (singletonProgM fn is') s'.prog = some i' := fun {s s' i} hC h => by
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hC.base.pc
    by_cases hfn : s.prog.lfn = fn
    · rw [findInstrMem_singleton _ _ _ hfn] at h
      refine ⟨h, fun i' hi' => ?_⟩
      rw [findInstrMem_singleton _ _ _ (hC.lfn.trans hfn), hpc]
      exact hi'
    · have hn : findInstrMem (singletonProgM fn is) s.prog = none := ite_eq_right hfn
      rw [hn] at h
      cases h
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hC h
      unfold lsemFuelMemF at h
      cases hfi : findInstrMem (singletonProgM fn is) s.prog with
      | none =>
          exact ⟨s', [], lsemFuelMemFLeak_halt _ 0 s' (hfetch hC hfi), .halt s hfi⟩
      | some i =>
          rw [hfi] at h
          cases h
  | succ n ih =>
      intro s s' t hC h
      unfold lsemFuelMemF at h
      cases hfi : findInstrMem (singletonProgM fn is) s.prog with
      | none =>
          exact ⟨s', [], lsemFuelMemFLeak_halt _ _ s' (hfetch hC hfi), .halt s hfi⟩
      | some i =>
          rw [hfi] at h
          dsimp only at h
          cases hev : evalInstrPMemF (singletonProgM fn is) i s with
          | none => rw [hev] at h; cases h
          | some u =>
              rw [hev] at h
              dsimp only at h
              obtain ⟨hi, hfi'⟩ := hfetch' hC hfi
              obtain ⟨i', u', hi', hev', hCu⟩ :=
                evalInstrPMemF_cellFoldLR hR hD hf fn hi hC hev
              obtain ⟨i'', hi'', hfo⟩ := cellFoldLR_getElem? is e0 is' hf _ i hi
              rw [hi'] at hi''
              cases hi''
              obtain ⟨t', g', hrun', hg'⟩ := ih hCu h
              refine ⟨t', foldG is' s.prog.base.lpc (instrLeakF i s) ++ g', ?_,
                .step s u i g' hfi hev hg'⟩
              rw [lsemFuelMemFLeak_step _ n i' s' u' (hfi' i' hi') hev', hrun',
                foldOneLR_leak hfo hC]
              simp only [Option.map_some, foldG, hi']

end Fold

/-! ## 5. The virtual body of the route -/

section Route

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK shiftS)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf movesOf_isLopn
  lsemFuelMemF_seg_fuel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseOKL fuseLoPre)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (renEv straightLeakFF
  straightLeakFF_quiet lsemFuelMemFLeak_segF singleLoop_leak_abi loopT)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd (ComExpOK)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels PubEqV)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (abiEntryM AbiValOf
  singleLoop_export_faithful_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (certNode loopCertB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots KEnv isCellB
  slotsOkB cellsDistinctB CellRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (src_chain_leak movesOf_quiet
  NoCArr routeEntry fuseMulHi_lsemFuelMemFLeak_pre certNode_noCArr
  lsemFuelMemFLeak_prefix_eq)

/-- The flag-machine entry state of the virtual body `virtBW` at the machine state `sa`: the
    base `entryC`, the function `fn`, the zero flag clear. -/
abbrev routeEntryW (σ : AbiLayout) (body : Lcmd) (ps : List (String × String)) (fn : String)
    (sa : AState) : LstateMF :=
  { prog := { base := entryC σ sa ps body, lfn := fn }, zf := false }

/-- **The trace of the virtual body of the route with carry chains and cells.** Let the
    printed body, the node `seeds ++ loop`, the renaming `ps`, the fusion flag and the output
    array pass `routeBW` with the cell fold `L2` of the renamed loop, the seeds emit no event
    and the loop have no compile-time array operand. At a machine state with the stack
    parameters at entry, for every terminating traced run of the node from `routeEntry` with
    trace `ℓ`, the renamed loop has a terminating traced run from
    a state `sX` at program counter `0` with trace `ℓ` with renamed array bases, and the
    virtual body `virtBW` has a terminating traced run from `routeEntryW` whose trace is the
    trace `GTr` computed along the run of the renamed loop by `foldG L2`. -/
theorem virtBW_gtr {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} {L2 : List LinstrRM}
    (hg : routeBW σ nm body seeds loop ps fuse out m = true)
    (hfold : cellFoldLR (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) = some L2)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (ha : ∀ i ∈ loop, NoCArr i.1)
    (sa : AState) (hst : σ.StackIn sa) (fn : String) (fuel : Nat) (t : LstateMF)
    (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (seeds ++ loop)) fuel
      (routeEntry σ body ps fn sa) = some (t, ℓ)) :
    ∃ (sX tX : LstateMF) (fX : Nat) (g : List CTLeak) (fuel' : Nat) (t' : LstateMF),
      sX.prog.lfn = fn ∧ sX.prog.base.lpc = 0
      ∧ lsemFuelMemFLeak (singletonProgM fn (loop.map (renRM (renOf ps)))) fX sX
          = some (tX, ℓ.map (renEv (renOf ps)))
      ∧ GTr (foldG L2) (singletonProgM fn (loop.map (renRM (renOf ps)))) sX g
      ∧ lsemFuelMemFLeak (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) fuel'
          (routeEntryW σ body ps fn sa) = some (t', g) := by
  unfold routeBW at hg
  rw [hfold] at hg
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hent⟩, hren⟩, -⟩, -⟩,
    hN⟩, -⟩, hkeep⟩, hpsC⟩, hfuse⟩, -⟩, -⟩ := hg
  have E := entryB_spec hent sa
  have R := renB_spec hren
  have N := cellNamesRB_spec hN
  have hunr : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j :=
    fun j hj => (R.unr j hj).2
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrsR σ ps) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrsR σ ps) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hfrA : ∀ j, j < σ.args.length → frameR σ sa ps body (argName j) = none := by
    intro j hj
    simp only [frameC, N.arg j hj]
    exact E.argF j hj
  have hS := E.argSrc hst
  have hfrR : ArgSrc σ nm (frameR σ sa ps body) sa :=
    hS.congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, cellIdx_slotOfReg])
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (un := unren ps) E.argF E.argG hS false
  have hA : ∀ b2 z2, runStraightF (argBind σ nm ++ seeds)
      (entryV σ (frameE body sa) sa (unren ps)) false = some (b2, z2) →
      ∀ r, r ∈ loopNames loop → b2.larr (renOf ps r) = b2.larr r := by
    intro b2 z2 hb2 r _
    have hl := runStraightF_larr R.store hb2
    rw [hl]
    rcases renOf_cases ps r with he | ⟨p, hp, rfl, he⟩
    · rw [he]
    · rw [he]
      show (abiEntryM σ sa).larr (unren ps p.2) = (abiEntryM σ sa).larr (unren ps p.1)
      rw [unren_target R.nd hp, unren_of_not_target fun q hq => R.ts p hp q hq]
  obtain ⟨f1, t1, ht1⟩ := src_chain_leak fn (argBind σ nm) seeds loop ps (· ∈ loopNames loop)
    (movesOf_isLopn _) R.lopn R.ctl R.cond R.ren R.names R.nd R.ts R.tgt R.fresh ha
    (movesOf_quiet _) hqs (entryV σ (frameE body sa) sa (unren ps)) _ false rfl hpr0 rfl hA
    fuel t ℓ hrun
  have hXL := ctlOK_of_cellFoldLR _ _ _ hfold
  have hpreL : ∀ i ∈ argBind σ nm ++ seeds ++ movesOf ps, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact movesOf_isLopn _ i hi
      · exact R.lopn i hi
    · exact movesOf_isLopn _ i hi
  have hpreQ : ∀ i ∈ argBind σ nm ++ seeds ++ movesOf ps, ∀ r, instrLeakB r i = [] := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact movesOf_quiet _ i hi
      · exact hqs i hi
    · exact movesOf_quiet _ i hi
  have hu : lsemFuelMemF (singletonProgM fn
      (argBind σ nm ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps)))) f1
      { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
        = some t1 := by
    rw [← lsemFuelMemFLeak_fst, ht1]
    rfl
  have hpos : ∀ j, j < (argBind σ nm ++ seeds ++ movesOf ps).length →
      (singletonProgM fn (argBind σ nm ++ seeds ++ movesOf ps
        ++ loop.map (renRM (renOf ps)))).body[
          (entryV σ (frameE body sa) sa (unren ps)).lpc + j]?
        = (argBind σ nm ++ seeds ++ movesOf ps)[j]? := fun j hj => by
    simp only [singletonProgM,
      show (entryV σ (frameE body sa) sa (unren ps)).lpc = 0 from rfl, Nat.zero_add]
    exact List.getElem?_append_left hj
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (lsemFuelMemF_seg_fuel _ fn rfl _ _ false _ t1 hpreL hpos hu)
  obtain ⟨b1, z1, tX0, hb1run, -, -⟩ :=
    strip_prefix fn _ _ hpreL hXL.1 _ false rfl _ t1 hu
  rw [lsemFuelMemFLeak_segF _ fn rfl _ _ false f (b1, z1) hpreL hpos hb1run] at ht1
  obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp ht1
  have hpc1 : b1.lpc = (argBind σ nm ++ seeds ++ movesOf ps).length := by
    rw [runStraightF_lpc _ _ false b1 z1 hb1run]
    exact Nat.zero_add _
  have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS (argBind σ nm ++ seeds ++ movesOf ps).length
          { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } := by
    simp only [shiftS, JasminLsemMemLoop.LstateM.lpc_setLpc, Nat.zero_add, ← hpc1]
    rfl
  rw [hsh, lsemFuelMemFLeak_prefix_eq fn _ _ hpreL hXL.1] at hq
  obtain ⟨ql, hql, rfl⟩ := Option.map_eq_some_iff.mp hq
  have hT : ql.2 = ℓ.map (renEv (renOf ps)) := by
    have h2 : straightLeakFF (argBind σ nm ++ seeds ++ movesOf ps)
        (entryV σ (frameE body sa) sa (unren ps)) false ++ ql.2
        = ℓ.map (renEv (renOf ps)) := congrArg Prod.snd hqe
    rw [straightLeakFF_quiet _ hpreQ] at h2
    exact h2
  obtain ⟨b1C, hb1C, hC1⟩ := cellRel_pre E hS N hunr hkeep (fun p hp => by
    have := List.all_eq_true.mp hpsC p hp
    simpa using this) hb1run
  have hCF : CellRelF (cellArrsR σ ps) []
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }
      { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 } :=
    ⟨cellRel_setLpc hC1 0, rfl, rfl⟩
  have hXrun : lsemFuelMemF (singletonProgM fn (loop.map (renRM (renOf ps)))) f
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } = some ql.1 := by
    rw [← lsemFuelMemFLeak_fst, hql]
    rfl
  obtain ⟨t2, g, ht2, hG⟩ := cellFoldLR_gtr N.slots N.dist hfold fn f
    (s := { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 })
    (s' := { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 }) hCF hXrun
  have hposC : ∀ j, j < (argBind σ nm ++ seeds ++ movesOf ps).length →
      (singletonProgM fn (argBind σ nm ++ seeds ++ movesOf ps ++ L2)).body[
          (entryC σ sa ps body).lpc + j]?
        = (argBind σ nm ++ seeds ++ movesOf ps)[j]? := fun j hj => by
    simp only [singletonProgM, show (entryC σ sa ps body).lpc = 0 from rfl, Nat.zero_add]
    exact List.getElem?_append_left hj
  have hpc1C : b1C.lpc = (argBind σ nm ++ seeds ++ movesOf ps).length := by
    rw [runStraightF_lpc _ _ false b1C z1 hb1C]
    exact Nat.zero_add _
  have hshC : ({ prog := { base := b1C, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS (argBind σ nm ++ seeds ++ movesOf ps).length
          { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 } := by
    simp only [shiftS, JasminLsemMemLoop.LstateM.lpc_setLpc, Nat.zero_add, ← hpc1C]
    rfl
  have hrun0 : lsemFuelMemFLeak
      (singletonProgM fn (argBind σ nm ++ seeds ++ movesOf ps ++ L2))
      ((argBind σ nm ++ seeds ++ movesOf ps).length + f) (routeEntryW σ body ps fn sa)
        = some (shiftS (argBind σ nm ++ seeds ++ movesOf ps).length t2, g) := by
    rw [lsemFuelMemFLeak_segF _ fn rfl _ (entryC σ sa ps body) false f (b1C, z1) hpreL hposC
      hb1C, hshC, lsemFuelMemFLeak_prefix_eq fn _ L2 hpreL hXL.2, ht2,
      straightLeakFF_quiet _ hpreQ]
    rfl
  have hfin : ∃ fuel' t', lsemFuelMemFLeak (singletonProgM fn (virtBW σ nm seeds ps L2 fuse))
      fuel' (routeEntryW σ body ps fn sa) = some (t', g) := by
    cases fuse with
    | false => exact ⟨_, _, hrun0⟩
    | true =>
        simp only [Bool.true_eq_false, false_or, List.all_eq_true, bne_iff_ne, ne_eq] at hfuse
        have habiC := entryV_abiEntry (un := unren ps) (sa := sa) hfrA E.argG
          fun j hj => (R.unr j hj).1
        have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm ++ cellNames (cellArrsR σ ps))
            (entryC σ sa ps body) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habiC x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (entryV_srcOf (un := unren ps) hfrR ha)
          · obtain ⟨⟨A, j⟩, hc⟩ := Option.isSome_iff_exists.mp (cellIdx_isSome.mpr hx)
            simp only [emptyArrs, entryV, frameC, hc]
        exact fuseMulHi_lsemFuelMemFLeak_pre hfuse.1 fn (routeEntryW σ body ps fn sa) rfl hE _
          (_, g) hrun0
  obtain ⟨fuel', t', hfin⟩ := hfin
  exact ⟨_, ql.1, f, g, fuel', t', rfl, rfl, by rw [hql, ← hT], hG, hfin⟩

/-- Two entry states of the virtual body `virtBW` at machine states with the stack parameters
    at entry whose valuations, as `σ` reads them off, agree on the positions `L` marks
    public. -/
def RouteEntryPubW (σ : AbiLayout) (body : Lcmd) (ps : List (String × String)) (fn : String)
    {Γ : Ctxt jasminDialect} (L : Labels Γ) (s₁ s₂ : LstateMF) : Prop :=
  ∃ (sa₁ sa₂ : AState) (V₁ V₂ : Ctxt.Valuation Γ), AbiValOf σ sa₁ V₁ ∧ AbiValOf σ sa₂ V₂
    ∧ PubEqV L V₁ V₂ ∧ σ.StackIn sa₁ ∧ σ.StackIn sa₂ ∧ s₁ = routeEntryW σ body ps fn sa₁
    ∧ s₂ = routeEntryW σ body ps fn sa₂

/-- **Constant time of the virtual body of the route with carry chains and cells from the
    source.** Let the single-loop program pass `loopCertB` with an update in `ArrMemN` with
    `ComExpOK`, and let its certified node be `seeds ++ loop` with seeds that emit no event,
    passing `routeBW` against the printed body with the cell fold `L2` of the renamed loop.
    If the source events of the single-loop program are constant time for the labels `L`,
    the virtual body `virtBW` is constant time on the flag machine from the entry states
    `routeEntryW` of machine states whose valuations agree on the public labels. -/
theorem virtBW_memFCT (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String} {m : Nat}
    {L2 : List LinstrRM}
    (hg : routeBW σ nm body seeds loop ps fuse outR m = true)
    (hfold : cellFoldLR (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) = some L2)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (L : Labels Γ) (fn : String)
    (hct : CT.ConstantTime (PubEqV L)
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs))) :
    MemFCT (singletonProgM fn (virtBW σ nm seeds ps L2 fuse))
      (RouteEntryPubW σ body ps fn L) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨sa₁, sa₂, V₁, V₂, hV₁, hV₂, hp, hs₁, hs₂, rfl, rfl⟩ r₁ r₂
  have ha : ∀ i ∈ loop, NoCArr i.1 := fun i hi0 =>
    certNode_noCArr update count init invs outArg inArgs abiArgs hexp hcert out c hi hcn i
      (hnode ▸ List.mem_append_right _ hi0)
  have key : ∀ (sa : AState) (V : Ctxt.Valuation Γ), AbiValOf σ sa V → σ.StackIn sa →
      ∃ (ℓ : List CTLeak) (sX tX : LstateMF) (fX : Nat) (g : List CTLeak) (fuel' : Nat)
        (t' : LstateMF),
        FRun (singletonProgM fn (certNode update invs out c)) (routeEntry σ body ps fn sa) ℓ
        ∧ sX.prog.lfn = fn ∧ sX.prog.base.lpc = 0
        ∧ lsemFuelMemFLeak (singletonProgM fn (loop.map (renRM (renOf ps)))) fX sX
            = some (tX, ℓ.map (renEv (renOf ps)))
        ∧ GTr (foldG L2) (singletonProgM fn (loop.map (renRM (renOf ps)))) sX g
        ∧ lsemFuelMemFLeak (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) fuel'
            (routeEntryW σ body ps fn sa) = some (t', g) := by
    intro sa V hV hst
    have habi := routeBW_abiEntry hg sa
    obtain ⟨out', c', hi', hc', -, hrun⟩ :=
      singleLoop_export_faithful_abi update count init invs outArg inArgs abiArgs hupd hexp
        hcert
    rw [hi] at hi'
    cases hi'
    rw [hcn] at hc'
    cases hc'
    obtain ⟨k, t, hk, -⟩ := hrun σ sa V fn _ false hV habi
    have hfst := lsemFuelMemFLeak_fst (singletonProgM fn (certNode update invs out c)) k
      (routeEntry σ body ps fn sa)
    rw [hk] at hfst
    obtain ⟨r0, hr0, -⟩ := Option.map_eq_some_iff.mp hfst
    have hr0' := hr0
    rw [← hnode] at hr0'
    obtain ⟨sX, tX, fX, g, fuel', t', h1, h2, h3, h4, h5⟩ :=
      virtBW_gtr hg hfold hqs ha sa hst fn k r0.1 r0.2 hr0'
    exact ⟨r0.2, sX, tX, fX, g, fuel', t', ⟨k, r0.1, hr0⟩, h1, h2, h3, h4, h5⟩
  obtain ⟨v₁, x₁, u₁, f₁, g₁, k₁, w₁, hF₁, hfn₁, hpc₁, hx₁, hG₁, hv₁⟩ := key sa₁ V₁ hV₁ hs₁
  obtain ⟨v₂, x₂, u₂, f₂, g₂, k₂, w₂, hF₂, hfn₂, hpc₂, hx₂, hG₂, hv₂⟩ := key sa₂ V₂ hV₂ hs₂
  have hv : v₁ = v₂ := by
    rw [singleLoop_leak_abi Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out
        c hi hcn σ sa₁ V₁ fn _ false hV₁ (routeBW_abiEntry hg sa₁) hF₁,
      singleLoop_leak_abi Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out
        c hi hcn σ sa₂ V₂ fn _ false hV₂ (routeBW_abiEntry hg sa₂) hF₂, hct V₁ V₂ hp]
  subst hv
  have hgg : g₁ = g₂ := gTr_eq _ fn _ f₁ x₁ u₁ _ hx₁ f₂ x₂ u₂ hx₂ hfn₁ hfn₂
    (hpc₁.trans hpc₂.symm) g₁ g₂ hG₁ hG₂
  rw [fRun_unique r₁ ⟨k₁, w₁, hv₁⟩, fRun_unique r₂ ⟨k₂, w₂, hv₂⟩, hgg]

/-! ## 6. The entry of the route and the decoded bytes -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW imgGateBW_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody CellFrames
  CellNoSlot)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop (image_addr_simBW')
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI runA_congr
  runSafe_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (Entry runALeak_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (regLen regK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiBase abiReg
  frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub
  memFCT_of_ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak (StraightPub
  imgRel_of_base_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (SafeHaltW
  BytesTraceW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT
  (bytesTraceW_of_printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (Disjoint8)

/-- **The entry of the route with carry chains and cells.** Under `routeBW`, at every machine
    state `sa` that satisfies `σ.Regions`: the separation `ImgSep` and the cell frames
    `CellFrames` at the frame map, slot map and bases of the route; the gate `imgGateBW` of
    the cell body at that frame map; the frame map at the names of the body; and the
    relation `ImgRel` of the entry `routeEntryW` with the entry of the address machine. -/
theorem routeBW_entry {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} (hg : routeBW σ nm body seeds loop ps fuse out m = true) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) :
    ImgSep (frameR σ sa ps body) (slotR σ nm ps) (baseR σ sa ps) (frameRsp body sa)
      ∧ CellFrames (frameR σ sa ps body) (slotR σ nm ps) (baseR σ sa ps) (frameRsp body sa)
          body
      ∧ imgGateBW (frameR σ sa ps body) (slotR σ nm ps) (cellBody (slotR σ nm ps) body) = true
      ∧ (∀ q ∈ bodyNamesI body,
          frameR σ sa ps body q = frameP (Params.ofBody body) (frameRsp body sa) q)
      ∧ ImgRel (frameR σ sa ps body) (slotR σ nm ps) (baseR σ sa ps)
          (cellBody (slotR σ nm ps) body) (routeEntryW σ body ps fn sa) (entryA σ sa) false := by
  unfold routeBW at hg
  split at hg
  case h_2 => cases hg
  rename_i L2 hfold
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hphys⟩, ⟨hgW, -⟩⟩, hfr⟩, hent⟩, hren⟩, hacc⟩, -⟩,
    hN⟩, hlen⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  have E := entryB_spec hent sa
  have R := renB_spec hren
  have N := cellNamesRB_spec hN
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrsR σ ps) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrsR σ ps) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hunr : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j :=
    fun j hj => (R.unr j hj).2
  have hun : ∀ q A n, slotArrOf σ nm q = some (A, n) → unren ps (renOf ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact hunr j (List.getElem?_eq_some_iff.mp hj).1
  have hS0 := imgSep_slotRen (ren := renOf ps)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot
      ImageAddrRoute.slotArrOf_not_fa) hun
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := ImageAddrFrame.frameIn_some ha
    have := ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      regLen (rsOf σ) (unren ps A) = n := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
    exact E.len q A0 n hq0
  have hrenS : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      renOf ps (unren ps A) = A := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
  have hrenR : ∀ p ∈ cellArrsR σ ps, renOf ps (unren ps p.1) = p.1 := by
    intro p hp
    obtain ⟨j, a, hj, -, he⟩ := cellArrsR_mem hp
    rw [he, hunr j (List.getElem?_eq_some_iff.mp hj).1]
  have hRlen : ∀ p ∈ cellArrsR σ ps, regLen (rsOf σ) (unren ps p.1) = p.2 := fun p hp => by
    simpa using List.all_eq_true.mp hlen p hp
  have hslC : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      cellIdx (cellArrsR σ ps) q = none := by
    intro q A n hq'
    obtain ⟨A0, hq0, -⟩ := slotRen_some hq'
    obtain ⟨a, ha⟩ := E.slot q A0 n hq0
    exact N.body q (ImageAddrFrame.frameIn_some ha).1
  have hsep := imgSep_cellsU (ren := renOf ps) E.rs hreg hS0 hword hsl hRlen hrenR hrenS N.gp
    hslC
  have hred : ∀ A j, cellIdx (cellArrsR σ ps) (memName A (8 * j)) = some (A, j) →
      Disjoint8 (redW (frameRsp body sa)) (ImageAddrSim.cellAt (baseR σ sa ps A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := cellIdx_spec hc
    have hk : regK (rsOf σ) (unren ps A) j := by
      unfold regK
      rw [hRlen _ hn]
      exact hj
    have hr : redW (frameRsp body sa)
        = sa.regs "%rsp" + BitVec.ofInt 64 (cmovRedZone - (Params.ofBody body).frame) := by
      simp only [redW, frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hr]
    have h2 := ImageAddrFrame.frameOkB_red hfr
    exact frameSep_of_regions E.rs hreg (unren ps A) j hk _ h2.1 h2.2
  have hF := cellFrames_of (base := baseR σ sa ps) (rsp := frameRsp body sa) hacc N.gp
    (fun r hr => hS0.gp r hr) hred
  have hgate' : imgGateBW (frameR σ sa ps body) (slotR σ nm ps)
      (cellBody (slotR σ nm ps) body) = true := by
    rw [imgGateBW_congr (frame' := frameMarkC (cellArrsR σ ps) body) (frameC_isSome _ _ body sa)]
    exact hgW
  have hfr' : ∀ q ∈ bodyNamesI body,
      frameR σ sa ps body q = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq'
    simp only [frameC, N.body q hq']
    show ImageAddrFrame.frameIn body _ q = _
    unfold ImageAddrFrame.frameIn
    rw [ite_eq_left hq']
  have hrel0 := imgRel_entryV (nm := nm) (fr := frameR σ sa ps body) (sa := sa)
    (body := cellBody (slotR σ nm ps) body) (fn := fn) (ren := renOf ps) (un := unren ps)
    ((E.argSrc hreg.stackIn).congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, cellIdx_slotOfReg]))
    (fun _ _ hs => cellBody_save hent hs) hunr
  exact ⟨hsep, hF, hgate', hfr', imgRel_cellArrs (R := cellArrsR σ ps) hrel0⟩

/-- **The virtual body of the route halts on checked runs.** Under the hypotheses of
    `virtBW_gtr`, from the entry `routeEntryW` of every machine state that satisfies
    `σ.Regions` from whose entry `routeEntry` the node has a terminating traced run, the
    virtual body `virtBW` has a halting checked run. -/
theorem virtBW_checked_run {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} {L2 : List LinstrRM}
    (hg : routeBW σ nm body seeds loop ps fuse out m = true)
    (hfold : cellFoldLR (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) = some L2)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (ha : ∀ i ∈ loop, NoCArr i.1)
    (sa : AState) (hreg : σ.Regions sa) (fn : String) {ℓ : List CTLeak}
    (hrun : FRun (singletonProgM fn (seeds ++ loop)) (routeEntry σ body ps fn sa) ℓ) :
    ∃ f t, lsemFuelMemFk true (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) f
      (routeEntryW σ body ps fn sa) = some t := by
  obtain ⟨fuel, t, hrun⟩ := hrun
  obtain ⟨-, -, -, g, fuel', t', -, -, -, -, h5⟩ :=
    virtBW_gtr hg hfold hqs ha sa hreg.stackIn fn fuel t ℓ hrun
  have hrunB : lsemFuelMemF (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) fuel'
      (routeEntryW σ body ps fn sa) = some t' := by
    rw [← lsemFuelMemFLeak_fst, h5]
    rfl
  unfold routeBW at hg
  rw [hfold] at hg
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hidx⟩, -⟩, -⟩, -⟩, -⟩, hent⟩, -⟩, -⟩, -⟩,
    hN⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  have E := entryB_spec hent sa
  have N := cellNamesRB_spec hN
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrsR σ ps) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrsR σ ps) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hents := boundFacts_entryV (nm := nm) (fr := frameR σ sa ps body) (un := unren ps) hreg
    fun b hb => by
      obtain ⟨h1, h2, h3⟩ := E.bnds b hb
      refine ⟨h1, h2, ?_⟩
      simp only [frameC, hgpN _ h1]
      exact h3
  have hok := runIdxOk_of_idxInvCheckB hidx fn (routeEntryW σ body ps fn sa) t' rfl rfl (hents _)
    fuel' hrunB
  exact ⟨fuel', t', lsemFuelMemFk_of_runIdxOk true _ fuel' _ t' hrunB hok⟩

/-- **Public-equal entry machine states of the route**, for a public equality `pubEq` of the
    entry states of the virtual body `B`: the entries `routeEntryW` of the two states are
    related by `pubEq`; both states satisfy `σ.Regions`; the stack registers are equal; the
    register of every array parameter, its base address, is equal; and `B` has a halting
    checked run from each entry. -/
def LoopPubW (σ : AbiLayout) (body : Lcmd) (ps : List (String × String)) (fn : String)
    (B : List LinstrRM) (pubEq : LstateMF → LstateMF → Prop) (sa₁ sa₂ : AState) : Prop :=
  pubEq (routeEntryW σ body ps fn sa₁) (routeEntryW σ body ps fn sa₂)
    ∧ σ.Regions sa₁ ∧ σ.Regions sa₂ ∧ sa₁.regs "%rsp" = sa₂.regs "%rsp"
    ∧ (∀ a ∈ σ.args, ∀ n, a.kind = .words n → sa₁.regs a.reg = sa₂.regs a.reg)
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn B) f (routeEntryW σ body ps fn sa₁)
        = some t)
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn B) f (routeEntryW σ body ps fn sa₂)
        = some t)

/-- **Constant time of the decoded bytes of the route with carry chains and cells.** Let the
    printed body, the node, the renaming, the fusion flag and the output array pass
    `routeBW` with the cell fold `L2` of the renamed loop, let the check on traced runs
    `ownedCheckML` accept the pair that `routeBW` compares with `ownedCheckMC`, and let the
    virtual body `virtBW` be constant time on the flag machine for `pubEq`. Then every
    decoding of the function bytes of the printed body is constant time under the regime
    `doitm` and any side condition between machine states related by `LoopPubW`. -/
theorem loop_bytesW_ct {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} {L2 : List LinstrRM}
    (hg : routeBW σ nm body seeds loop ps fuse out m = true)
    (hfold : cellFoldLR (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) = some L2)
    (hlk : ownedCheckML (outCells (renOf ps out) m) (virtBW σ nm seeds ps L2 fuse)
      (virtImg (slotR σ nm ps) (cellBody (slotR σ nm ps) body)) = true)
    (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hvirt : MemFCT (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) pubEq)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (LoopPubW σ body ps fn (virtBW σ nm seeds ps L2 fuse) pubEq)
      (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  rintro sa₁ sa₂ u₁ u₂ ⟨hpub, hreg₁, hreg₂, hrspE, hbases, hk₁, hk₂⟩ ⟨sa₁', hb₁⟩ ⟨sa₂', hb₂⟩
  have himgCT := memFCT_of_ownedCheckML hlk fn hvirt
  obtain ⟨hsep, hF, hgate, hfr, hrel₁⟩ := routeBW_entry hg sa₁ hreg₁ fn
  obtain ⟨-, -, -, -, hrel₂⟩ := routeBW_entry hg sa₂ hreg₂ fn
  have R := renB_spec (routeBW_checks hg).2
  have hunr : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j :=
    fun j hj => (R.unr j hj).2
  have hg' := hg
  unfold routeBW at hg'
  rw [hfold] at hg'
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, -⟩, hpr⟩, hphys⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hns⟩,
    -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
  have hrsp : frameRsp body sa₂ = frameRsp body sa₁ := by
    unfold frameRsp
    rw [hrspE]
  have hfrE : frameE body sa₂ = frameE body sa₁ := by
    unfold frameE
    rw [hrsp]
  have hbJ : ∀ j a, σ.args[j]? = some a → ∀ n, a.kind = .words n →
      baseR σ sa₂ ps (renOf ps (argName j)) = baseR σ sa₁ ps (renOf ps (argName j)) := by
    intro j a hj n hk
    show abiBase (abiReg σ) sa₂ (unren ps (renOf ps (argName j)))
      = abiBase (abiReg σ) sa₁ (unren ps (renOf ps (argName j)))
    rw [hunr j (List.getElem?_eq_some_iff.mp hj).1, abiBase_argName hj, abiBase_argName hj]
    exact (hbases a (List.mem_of_getElem? hj) n hk).symm
  have hbA : ∀ p ∈ cellArrsR σ ps, baseR σ sa₂ ps p.1 = baseR σ sa₁ ps p.1 := by
    intro p hp
    obtain ⟨j, a, hj, hk, he⟩ := cellArrsR_mem hp
    rw [he]
    exact hbJ j a hj p.2 hk
  have hfrC : frameR σ sa₂ ps body = frameR σ sa₁ ps body := by
    funext q
    show frameC _ _ _ q = frameC _ _ _ q
    unfold frameC
    cases hc : cellIdx (cellArrsR σ ps) q with
    | none =>
        simp only
        rw [hfrE]
    | some Aj =>
        obtain ⟨A, j⟩ := Aj
        obtain ⟨n, hn, -, -⟩ := cellIdx_spec hc
        simp only
        rw [hbA _ hn]
  have hbase : ∀ q A n, slotR σ nm ps q = some (A, n) →
      baseR σ sa₂ ps A = baseR σ sa₁ ps A := by
    intro q A n hq
    obtain ⟨m', hq', -⟩ := slotArrC_some hq
    obtain ⟨A0, hA0, rfl⟩ := slotRen_some hq'
    obtain ⟨j, a0, hj, hkind, rfl, -⟩ := slotArrOf_some hA0
    exact hbJ j a0 hj _ hkind
  have hrel₂' : ImgRel (frameR σ sa₁ ps body) (slotR σ nm ps) (baseR σ sa₁ ps)
      (cellBody (slotR σ nm ps) body) (routeEntryW σ body ps fn sa₂) (entryA σ sa₂) false := by
    have key : ∀ fr : String → Option (BitVec 64), fr = frameR σ sa₁ ps body →
        ImgRel fr (slotR σ nm ps) (baseR σ sa₁ ps) (cellBody (slotR σ nm ps) body)
          (routeEntryW σ body ps fn sa₂) (entryA σ sa₂) false →
        ImgRel (frameR σ sa₁ ps body) (slotR σ nm ps) (baseR σ sa₁ ps)
          (cellBody (slotR σ nm ps) body) (routeEntryW σ body ps fn sa₂) (entryA σ sa₂)
          false := by
      rintro _ rfl h
      exact h
    exact key _ hfrC (imgRel_of_base_eq hbase hrel₂)
  have himg : ∀ sa, (∃ f t, lsemFuelMemFk true
        (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) f
        (routeEntryW σ body ps fn sa) = some t) →
      ∃ f t, lsemFuelMemFk true (singletonProgM fn
        (virtImg (slotR σ nm ps) (cellBody (slotR σ nm ps) body))) f
        (routeEntryW σ body ps fn sa) = some t := by
    rintro sa ⟨f, t, hk⟩
    obtain ⟨f', t', hr', -⟩ := ownedCheckMC_sound hck fn _ t rfl rfl f hk
    exact ⟨f', t', hr'⟩
  obtain ⟨f₁, t₁, hi₁⟩ := himg sa₁ hk₁
  obtain ⟨f₂, t₂, hi₂⟩ := himg sa₂ hk₂
  have hNS := cellNoSlotB_spec hns
  have hAP : AddrPub (frameR σ sa₁ ps body) (slotR σ nm ps) (baseR σ sa₁ ps)
      (cellBody (slotR σ nm ps) body) fn (TVPub fn (virtBW σ nm seeds ps L2 fuse) pubEq)
      (entryA σ sa₁, false) (entryA σ sa₂, false) :=
    ⟨routeEntryW σ body ps fn sa₁, routeEntryW σ body ps fn sa₂,
      ⟨hpub, rfl, rfl, rfl, rfl, hk₁, hk₂⟩, rfl, rfl, rfl, hrel₁, hrel₂', ⟨f₁, t₁, hi₁⟩,
      ⟨f₂, t₂, hi₂⟩⟩
  have hentA : ∀ sa : AState, Entry sa (entryA σ sa) := fun sa =>
    ⟨rfl, fun R hR => by
      have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (DecodePrinted.phys R)⟩ := by
        simp only [entryA, hR, ite_true]
      unfold JasminLsemWidthN.LstateN.getW
      rw [hl]
      simp, rfl⟩
  have hA := cell_image_addr_ctW' hsep hphys hgate hNS hF fn himgCT
  have hsafe : ∀ (s t : LstateMF) (a : LstateA) (f : Nat), s.prog.lfn = fn →
      ImgRel (frameR σ sa₁ ps body) (slotR σ nm ps) (baseR σ sa₁ ps)
        (cellBody (slotR σ nm ps) body) s a false →
      lsemFuelMemFk true (singletonProgM fn
        (virtImg (slotR σ nm ps) (cellBody (slotR σ nm ps) body))) f s = some t →
      SafeHaltW (frameR σ sa₁ ps body) (frameRsp body sa₁) body (a, false) := by
    intro s t a f hfn hr hk
    obtain ⟨fA, sA, zA, h1, -, h3⟩ :=
      image_addr_simBW' hsep hphys hgate hNS hF fn
        (imgStepWCond_of_gate _ hphys hgate fn) f s t a false hfn
        (ImageAddrSimW.imgRelW_of hr) hk
    exact ⟨fA, _, h1, h3⟩
  obtain ⟨g₁, r₁, hrA₁, hs₁⟩ := hsafe _ t₁ _ f₁ rfl hrel₁ hi₁
  obtain ⟨g₂, r₂, hrA₂, hs₂⟩ := hsafe _ t₂ _ f₂ rfl hrel₂' hi₂
  rw [runA_congr hfr] at hrA₁ hrA₂
  rw [runSafe_congr hfr] at hs₁ hs₂
  exact bytesTraceW_of_printedAddrWB hpr prog hdec (frameRsp body sa₁) sa₁ sa₂ rfl hrsp
    (entryA σ sa₁, false) (entryA σ sa₂, false) (hentA sa₁) (hentA sa₂) ⟨g₁, r₁, hrA₁, hs₁⟩
    ⟨g₂, r₂, hrA₂, hs₂⟩
    (fun ℓ₁ ℓ₂ h₁ h₂ => hA _ _ ℓ₁ ℓ₂ hAP
      (by simpa only [ARun, runALeak_congr hfr] using h₁)
      (by simpa only [ARun, runALeak_congr hfr] using h₂))
    ok ok u₁ u₂ sa₁' sa₂' hb₁ hb₂

/-- **Constant time of the decoded bytes of the route with carry chains and cells from the
    source.** Let the single-loop program pass `loopCertB` with an update in `ArrMemN` with
    `ComExpOK`, let its certified node be `seeds ++ loop` with seeds that emit no event,
    passing `routeBW` against the printed body with the cell fold `L2` of the renamed loop,
    and let the check on traced runs `ownedCheckML` accept the pair that `routeBW` compares
    with `ownedCheckMC`. If the source events of the single-loop program are constant time
    for the labels `L`, every decoding of the function bytes of the printed body is constant
    time under the regime `doitm` and any side condition between machine states related by
    `StraightPub`. -/
theorem loop_bytesW_ct_src (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String} {m : Nat}
    {L2 : List LinstrRM}
    (hg : routeBW σ nm body seeds loop ps fuse outR m = true)
    (hfold : cellFoldLR (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) = some L2)
    (hlk : ownedCheckML (outCells (renOf ps outR) m) (virtBW σ nm seeds ps L2 fuse)
      (virtImg (slotR σ nm ps) (cellBody (slotR σ nm ps) body)) = true)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (L : Labels Γ)
    (hct : CT.ConstantTime (PubEqV L)
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs)))
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  rintro sa₁ sa₂ u₁ u₂ ⟨V₁, V₂, hV₁, hV₂, hp, hreg₁, hreg₂, hrsp, hbases⟩ hb₁ hb₂
  have ha : ∀ i ∈ loop, NoCArr i.1 := fun i hi0 =>
    certNode_noCArr update count init invs outArg inArgs abiArgs hexp hcert out c hi hcn i
      (hnode ▸ List.mem_append_right _ hi0)
  have hk : ∀ (sa : AState) (V : Ctxt.Valuation Γ), AbiValOf σ sa V → σ.Regions sa →
      ∃ f t, lsemFuelMemFk true (singletonProgM "" (virtBW σ nm seeds ps L2 fuse)) f
        (routeEntryW σ body ps "" sa) = some t := by
    intro sa V hV hreg
    have habi := routeBW_abiEntry hg sa
    obtain ⟨out', c', hi', hc', -, hrun⟩ :=
      singleLoop_export_faithful_abi update count init invs outArg inArgs abiArgs hupd hexp
        hcert
    rw [hi] at hi'
    cases hi'
    rw [hcn] at hc'
    cases hc'
    obtain ⟨k, t, hk, -⟩ := hrun σ sa V "" _ false hV habi
    have hfst := lsemFuelMemFLeak_fst (singletonProgM "" (certNode update invs out c)) k
      (routeEntry σ body ps "" sa)
    rw [hk] at hfst
    obtain ⟨r0, hr0, -⟩ := Option.map_eq_some_iff.mp hfst
    rw [← hnode] at hr0
    exact virtBW_checked_run hg hfold hqs ha sa hreg "" ⟨k, r0.1, hr0⟩
  exact loop_bytesW_ct hg hfold hlk ""
    (virtBW_memFCT Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out c hi hcn
      hg hfold hnode hqs L "" hct) ok hdec sa₁ sa₂ u₁ u₂
    ⟨⟨sa₁, sa₂, V₁, V₂, hV₁, hV₂, hp, hreg₁.stackIn, hreg₂.stackIn, rfl, rfl⟩, hreg₁, hreg₂,
      hrsp, hbases, hk sa₁ V₁ hV₁ hreg₁,
      hk sa₂ V₂ hV₂ hreg₂⟩ hb₁ hb₂

end Route

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak
