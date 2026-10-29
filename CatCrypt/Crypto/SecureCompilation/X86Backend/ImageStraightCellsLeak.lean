/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells

@[expose] public section

set_option autoImplicit false

/-!
# The events of the straight cell route

The straight cell route of `ImageStraightCells` compiles a straight-line program through the
cell fold `ImageCellFold.cellFold` of its coalesced chain `C`, the virtual body
`cellVirt σ nm C2 fuse` of the folded chain `C2`, the image of the cell body
`ImageAddrCells.cellBody` of the printed body, the address machine on the printed body, and
the decoded bytes. This module follows the events `instrLeakF` of the traced flag machine and
the events `stepLeakA` of the address machine along these comparisons.

The fold replaces an indexed access at a known index by a copy from or to a cell name, which
emits no event; every kept instruction emits the events it emits in the chain. The trace of
the folded chain is therefore `cellT` of the trace of the chain, a map that depends on the
two chains only. On the address machine, a cell access `[B + off]` of the printed body and
its frame-word move in the cell body emit the same address when `B` holds the pointer of the
array and the cell name has the address of the word.

Under the gate with carry chains `imgGateBW`, an instruction of the cell body other than an
indexed access emits on the address machine events that no state changes: frame addresses of
its slot operands. The trace of the address machine is therefore `physTW` of the trace of the
image, a map that depends on the body, the frame, the array bases and one fixed state.

## Main definitions

* `cellT`: the events of the folded chain from the events of the chain.
* `posTW`, `physTW`: the events of the address machine from the events of the image, under
  the gate with carry chains.
* `cellEntry`: the flag-machine entry state of the virtual body of the cell route.
* `ChainCT`: equal traces of the coalesced chain behind the copies of the parameter
  registers, between machine states related by `StraightPub`.
* `straightCellLB`: the check on traced runs of the cell route, `ownedCheckML` on the pair
  that `cellRouteB` compares with `ownedCheckMC`.
* `SafeHaltW`, `BytesTraceW`: equal traces of the decoded bytes of a body from equal traces
  of the address machine, the statement of `DecodePrintedAddrLeak.bytes_trace_eq` at the
  safety condition of the class with carry chains.

## Main results

* `foldOne_leak`: the events of a folded instruction from those of the instruction.
* `straightLeakFF_cellFold`: the trace of the folded chain is `cellT` of the trace of the
  chain.
* `stepLeakA_cellBody`, `stepLeakA_cellBodyW`: a step of the address machine emits the same
  events on the printed body and on its cell body.
* `step_leakW`: the events of a step of the address machine under the gate with carry
  chains.
* `cell_image_addr_leak`, `cell_image_addr_leakW`: the traced image simulation of a cell
  body, under `imgGateB` and under `imgGateBW`.
* `cell_image_addr_ct`, `cell_image_addr_ctW`: constant time of the address machine on the
  body from constant time of the image of its cell body.
* `cellVirt_leak`, `cellVirt_checked_run`: the trace, and a halting checked run, of the
  virtual body of the cell route, with and without fusion.
* `cellRoute_entry`: the separation, cell frames, gate and relation at the entry.
* `chainCT_of_trace`, `straightCellB_spec`: `ChainCT` from a trace map, and the conjuncts of
  the gate `straightCellB`.
* `straightCell_memFCT`: constant time of the virtual body of the cell route from `ChainCT`.
* `straightCell_image_memFCT`: constant time of the image of the cell body.
* `straightCell_bytes_ct`: constant time of the decoded bytes of the cell route from
  `ChainCT` and `BytesTraceW`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF flagCondCC?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_cons fstepF isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (straightLeakFF
  straightLeakFF_cons_of_step straightLeakFF_append straightLeakFF_quiet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (instrLeakB_agree movesOf_quiet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (evCountF isArrOp
  flatMap_opLeakF_length)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime ConstantTimeRel)

/-! ## 1. The events of the cell fold -/

/-- An `Lopn` emits `evCountF` many events from every register file. -/
theorem instrLeakB_length {i : LinstrRM} (hl : IsLopn i) (r : LstateN) :
    (instrLeakB r i).length = evCountF i := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨ds, o, ss, hd⟩ := hl
  simp only at hd
  subst hd
  have hf : flagCondCC? (LinstrR.Lopn ds o ss, tag) = none := by unfold flagCondCC?; rfl
  simp only [instrLeakB, evCountF, hf]
  split_ifs
  · rfl
  · exact flatMap_opLeakF_length _ _

/-- **The forms of a folded instruction.** The instruction is an `Lopn`, and its fold is the
    instruction itself, kept under `keepB`, or a copy between registers without an array
    operand. -/
theorem foldOne_cases {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOne R env i = some i') :
    IsLopn i ∧ ((keepB R i = true ∧ i' = i)
      ∨ ∃ d o c, i' = (.Lopn [.reg d] o [.reg c], .reg none)) := by
  have hk : keepB R i = true → IsLopn i := fun h => by
    simp only [keepB, Bool.and_eq_true] at h
    exact isLopnB_isLopn h.1.1
  obtain ⟨wire, tg⟩ := i
  unfold foldOne at hf
  dsimp only at hf
  split at hf
  · rename_i w n d o b x sc
    refine ⟨⟨_, _, _, rfl⟩, ?_⟩
    split at hf
    · split at hf
      · split at hf
        · split at hf
          · cases hf
            exact Or.inr ⟨_, _, _, rfl⟩
          · cases hf
        · cases hf
      · cases hf
    · split at hf
      · rename_i hkp
        cases hf
        exact Or.inl ⟨hkp, rfl⟩
      · cases hf
  · rename_i w n d o b x sc v
    refine ⟨⟨_, _, _, rfl⟩, ?_⟩
    split at hf
    · split at hf
      · split at hf
        · split at hf
          · cases hf
            exact Or.inr ⟨_, _, _, rfl⟩
          · cases hf
        · cases hf
      · cases hf
    · split at hf
      · rename_i hkp
        cases hf
        exact Or.inl ⟨hkp, rfl⟩
      · cases hf
  · split at hf
    · rename_i hkp
      cases hf
      exact ⟨hk hkp, Or.inl ⟨hkp, rfl⟩⟩
    · cases hf

/-- **The events of a folded instruction.** From cell-related states, the fold of an
    instruction emits the first `evCountF` events of the instruction, counted at the fold: all
    of them when the instruction is kept, none when an indexed access at a known index is
    folded into a cell copy. -/
theorem foldOne_leak {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOne R env i = some i') {s s' : LstateM} (hC : CellRel R env s s') :
    instrLeakB s'.reg i' = (instrLeakB s.reg i).take (evCountF i') := by
  obtain ⟨hl, hcase⟩ := foldOne_cases hf
  rcases hcase with ⟨hk, rfl⟩ | ⟨d, o, c, rfl⟩
  · have hn : ∀ n ∈ instrNames i'.1, s'.reg.lvm n = s.reg.lvm n := by
      intro n hn
      simp only [keepB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk
      exact hC.reg n (hk.2 n hn).2
    rw [instrLeakB_agree hl hn, ← instrLeakB_length hl s.reg, List.take_length]
  · have hf0 : flagCondCC? (LinstrR.Lopn [.reg d] o [.reg c], JasminLsemMem.MemTag.reg none)
        = none := by unfold flagCondCC?; rfl
    have h0 : evCountF (LinstrR.Lopn [.reg d] o [.reg c], JasminLsemMem.MemTag.reg none) = 0 := by
      simp only [evCountF, hf0]
      split_ifs <;> rfl
    have h1 : instrLeakB s'.reg (LinstrR.Lopn [.reg d] o [.reg c], JasminLsemMem.MemTag.reg none)
        = [] := by
      simp only [instrLeakB]
      split_ifs <;> rfl
    rw [h0, h1, List.take_zero]

/-- **The events of the folded chain from the events of the chain**: along the two chains,
    the first `evCountF` events of each instruction, counted at its fold, with the events of
    the instruction dropped behind it. The map depends on the two chains only. -/
def cellT : List LinstrRM → List LinstrRM → List CTLeak → List CTLeak
  | i :: is, i' :: is', ℓ =>
      (ℓ.take (evCountF i)).take (evCountF i') ++ cellT is is' (ℓ.drop (evCountF i))
  | _, _, _ => []

/-- **The trace of the folded chain.** For slot arrays `R` that pass `slotsOkB` and
    `cellsDistinctB`, and a chain `is` whose cell fold from the known constants `env` is
    `is'`: when `is` runs on the flag machine from `s`, the trace of `is'` from every
    cell-related state `s'` is `cellT` of the trace of `is` from `s`. -/
theorem straightLeakFF_cellFold {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFold R env is = some is' →
      ∀ {s s' b : LstateM} {zf z : Bool}, CellRel R env s s' →
        runStraightF is s zf = some (b, z) →
        straightLeakFF is' s' zf = cellT is is' (straightLeakFF is s zf)
  | [], env, is', hf, s, s', b, zf, z, hC, h => by
      cases hf
      rfl
  | i :: is, env, is', hf, s, s', b, zf, z, hC, h => by
      unfold cellFold at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        rw [runStraightF_cons] at h
        cases hs : fstepF i s zf with
        | none => rw [hs] at h; cases h
        | some tz =>
            obtain ⟨t, z1⟩ := tz
            rw [hs] at h
            simp only [Option.bind_some] at h
            obtain ⟨t', h', hC'⟩ := fold_step hR hD h1 hC hs
            have ih := straightLeakFF_cellFold hR hD is _ _ h2 hC' h
            have hl := (foldOne_cases h1).1
            rw [straightLeakFF_cons_of_step h', straightLeakFF_cons_of_step hs, ih,
              foldOne_leak h1 hC]
            simp only [cellT, ← instrLeakB_length hl s.reg, List.take_left', List.drop_left']
      · cases hf

/-! ## 2. The events of a step of the address machine at a cell access -/

section CellStep

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (accArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel imgGateB
  ptr_of_reload)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (ImgRelW imgGateBW
  ptr_of_reloadW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (stepLeakA instrLeakA
  instrLeakA_ldm instrLeakA_stm instrLeakA_slotLoad instrLeakA_slotStore evA)

/-- A cell load, `LOAD:64` or `MOV:64`, accesses the address in its base plus its offset. -/
theorem instrLeakA_cellLd (frame : String → Option (BitVec 64)) {x : LinstrR} {D B : String}
    {off : Nat} (hc : cellA? x = some (.ld D B off)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) :
    instrLeakA frame (x, .reg none) sa = [evA (p + BitVec.ofNat 64 off)] := by
  have hm := slotMov_cell hc
  obtain ⟨_, n, rfl, -, -⟩ := cellA_ld hc
  simp [instrLeakA, hm, slotCmp?, hc, hB]

/-- A cell store, `STORE:64` or `MOV:64`, accesses the address in its base plus its offset. -/
theorem instrLeakA_cellSt (frame : String → Option (BitVec 64)) {x : LinstrR} {B S : String}
    {off : Nat} (hc : cellA? x = some (.st B off S)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) :
    instrLeakA frame (x, .reg none) sa = [evA (p + BitVec.ofNat 64 off)] := by
  have hm := slotMov_cell hc
  obtain ⟨_, n, rfl, -, -⟩ := cellA_st hc
  simp [instrLeakA, hm, slotCmp?, hc, hB]

/-- **A step of the address machine emits the same events on a body and on its cell body**,
    at a state in which the base register of every cell access at the program counter holds
    the pointer of its array: a cell access `[B + off]` and its frame-word move access the
    address `base A + off`; every other instruction is the same in the two bodies. -/
theorem stepLeakA_cellBody_of_ptr {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hF : CellFrames frame slotArr base rsp body) {sa : LstateA} {b0 : Linstr}
    (hb0 : body[sa.reg.lpc]? = some b0)
    (hptr : ∀ B A n, accArr slotArr body sa.reg.lpc B = some (A, n) → frame B = none →
      DecodePrinted.gpOk B = true → sa.reg.getW B 64 = some (base A)) (zf : Bool) :
    stepLeakA frame body sa zf = stepLeakA frame (cellBody slotArr body) sa zf := by
  have hbC : (cellBody slotArr body)[sa.reg.lpc]?
      = some (cellMove slotArr body sa.reg.lpc b0) := by
    rw [cellBody_getElem?, hb0]; rfl
  cases hc : cellA? b0.li_i with
  | none =>
      unfold stepLeakA
      rw [hbC, hb0, cellMove_of_none hc]
  | some op =>
      cases op with
      | ld D B off =>
          obtain ⟨A, m, hacc, hBf, hfr, -⟩ := hF.ld _ _ D B off hb0 hc
          have hp := hptr B A m hacc hBf (hF.ldGp _ _ D B off hb0 hc)
          obtain ⟨mm, nm, hx, hmm, hn⟩ := cellA_ld hc
          obtain ⟨ii, li⟩ := b0
          simp only at hx
          subst hx
          have hm : cellMove slotArr body sa.reg.lpc ⟨ii, .Lopn [.reg D] mm [.reg nm]⟩
              = ⟨ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩ := by
            simp [cellMove, hc, hacc]
          have h1 : normA (.Lopn [.reg D] mm [.reg nm])
              = .Lopn [.reg D] (LprogAsmPrinter.untagCaret mm) [.reg nm] :=
            NarrowTyping.normA_of_untagCaret rfl (by rcases hmm with h | h <;> rw [h] <;> decide)
          have h2 : tagA (.Lopn [.reg D] mm [.reg nm]) = .reg none := by
            have h := tagAt_of_untagCaret_cell [] 0 (d := D) (n := nm) (o := mm)
              (by rcases hmm with h | h <;> simp [h])
            rwa [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?])] at h
          have hc' : cellA? (.Lopn [.reg D] (LprogAsmPrinter.untagCaret mm) [.reg nm])
              = some (.ld D B off) := by
            rw [cellA?_untagCaret]; exact hc
          have h3 : normA (.Lopn [.reg D] "MOVQ" [.reg (memName A off)])
              = .Lopn [.reg D] "MOVQ" [.reg (memName A off)] := by
            rw [normA_of_caret_free (by decide)]; simp
          have h4 : tagA (.Lopn [.reg D] "MOVQ" [.reg (memName A off)]) = .reg none := by
            simp [tagA, width_tag]
          unfold stepLeakA
          rw [hbC, hb0, hm]
          simp only [h1, h2, h3, h4]
          rw [instrLeakA_cellLd frame hc' hp,
            instrLeakA_slotLoad frame (d := D) (q := memName A off) (by simp [slotMov?]) hfr]
      | st B off S =>
          obtain ⟨A, m, hacc, hBf, hSf, hfr⟩ := hF.st _ _ B off S hb0 hc
          have hp := hptr B A m hacc hBf (hF.stGp _ _ B off S hb0 hc)
          obtain ⟨mm, nm, hx, hmm, hn⟩ := cellA_st hc
          obtain ⟨ii, li⟩ := b0
          simp only at hx
          subst hx
          have hm : cellMove slotArr body sa.reg.lpc ⟨ii, .Lopn [.reg nm] mm [.reg S]⟩
              = ⟨ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩ := by
            simp [cellMove, hc, hacc]
          have h1 : normA (.Lopn [.reg nm] mm [.reg S])
              = .Lopn [.reg nm] (LprogAsmPrinter.untagCaret mm) [.reg S] :=
            NarrowTyping.normA_of_untagCaret rfl (by rcases hmm with h | h <;> rw [h] <;> decide)
          have h2 : tagA (.Lopn [.reg nm] mm [.reg S]) = .reg none := by
            have h := tagAt_of_untagCaret_cell [] 0 (d := nm) (n := S) (o := mm)
              (by rcases hmm with h | h <;> simp [h])
            rwa [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?])] at h
          have hc' : cellA? (.Lopn [.reg nm] (LprogAsmPrinter.untagCaret mm) [.reg S])
              = some (.st B off S) := by
            rw [cellA?_untagCaret]; exact hc
          have h3 : normA (.Lopn [.reg (memName A off)] "MOVQ" [.reg S])
              = .Lopn [.reg (memName A off)] "MOVQ" [.reg S] := by
            rw [normA_of_caret_free (by decide)]; simp
          have h4 : tagA (.Lopn [.reg (memName A off)] "MOVQ" [.reg S]) = .reg none := by
            simp [tagA, width_tag]
          unfold stepLeakA
          rw [hbC, hb0, hm]
          simp only [h1, h2, h3, h4]
          rw [instrLeakA_cellSt frame hc' hp,
            instrLeakA_slotStore frame (q := memName A off) (S := S) (by simp [slotMov?]) hSf
              hfr]
      | lea D B off =>
          unfold stepLeakA
          rw [hbC, hb0, cellMove_of_lea hc]

/-- **The events of a step at the relation of the image simulation.** From an address state
    related by `ImgRel` to a state of the image of the cell body, under the gate `imgGateB`,
    a step of the address machine emits the same events on the body and on its cell body. -/
theorem stepLeakA_cellBody {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) s sa zf) {b0 : Linstr}
    (hb0 : body[sa.reg.lpc]? = some b0) :
    stepLeakA frame body sa zf = stepLeakA frame (cellBody slotArr body) sa zf :=
  stepLeakA_cellBody_of_ptr hF hb0 (fun _ _ _ hacc hBf hgp =>
    (ptr_of_reload hsep (.of_imgGateB hgate) hrel (accArr_cellBody hN (hasPrefix_gpName hgp) hacc) hBf).elim
      fun _ h => h.2) zf

/-- **The events of a step at the relation with carry chains.** `stepLeakA_cellBody` at the
    relation `ImgRelW` and the gate `imgGateBW`. -/
theorem stepLeakA_cellBodyW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa zf) {b0 : Linstr}
    (hb0 : body[sa.reg.lpc]? = some b0) :
    stepLeakA frame body sa zf = stepLeakA frame (cellBody slotArr body) sa zf :=
  stepLeakA_cellBody_of_ptr hF hb0 (fun _ _ _ hacc hBf hgp =>
    (ptr_of_reloadW hsep hgate hrel (accArr_cellBody hN (hasPrefix_gpName hgp) hacc) hBf).elim
      fun _ h => h.2) zf

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg
  virtImg_getElem? virtImg_length imgInstr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findInstrMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk
  evalInstrPMemFk evalInstrPMemF_of_k)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (haltedA_of_img)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (NoCond physT step_leak
  runALeak runALeak_halt runALeak_step runALeak_det stepA_lpc_noCond instrLeakF_length AddrPub
  ARun)

/-- **The traced image simulation of a cell body.** For a printed body without a conditional
    branch whose cell body passes the gate `imgGateB` and the class `physImgB`, at a
    separation `ImgSep` and cell frames `CellFrames`, every halting checked run of the image
    of the cell body from a state related to an address state has a traced run with trace
    `ℓ`, and is matched by a halting traced run of the address machine on the body with
    trace `physT` of `ℓ` along the cell body, with the relation at the end. -/
theorem cell_image_addr_leak {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : NoCond body) (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base (cellBody slotArr body) s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
        = some t →
      ∃ ℓ fuel' sa' zf',
        lsemFuelMemFLeak (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
          = some (t, ℓ)
        ∧ runALeak frame body fuel' sa zf
            = some ((sa', zf'),
                physT frame base slotArr (cellBody slotArr body)
                  ((cellBody slotArr body).dropLast.drop sa.reg.lpc) sa.reg.lpc ℓ)
        ∧ ImgRel frame slotArr base (cellBody slotArr body) t sa' zf' := by
  set cb := cellBody slotArr body with hcb
  set P := singletonProgM fn (virtImg slotArr cb)
  have hnc' : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l :=
    fun k bi hb => hnc bi (List.mem_of_getElem? hb)
  have halt : ∀ (s : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base cb s sa zf → findInstrMem P s.prog = none →
      ∀ fuel, ∃ ℓ fuel' sa' zf',
        lsemFuelMemFLeak P fuel s = some (s, ℓ)
        ∧ runALeak frame body fuel' sa zf
            = some ((sa', zf'),
                physT frame base slotArr cb (cb.dropLast.drop sa.reg.lpc) sa.reg.lpc ℓ)
        ∧ ImgRel frame slotArr base cb s sa' zf' := by
    intro s sa zf hfn hrel hf fuel
    have hnil : cb.dropLast.drop sa.reg.lpc = [] := by
      have h := hf
      rw [findInstrMem_single hfn, List.getElem?_eq_none_iff, virtImg_length, ← hrel.pc] at h
      exact List.drop_eq_nil_of_le (by rw [List.length_dropLast]; exact h)
    have hh := haltedA_of_img (.of_imgGateB hgate) fn hfn hrel.pc hf
    rw [haltedA_cellBody] at hh
    refine ⟨[], 0, sa, zf, lsemFuelMemFLeak_halt P fuel s hf, ?_, hrel⟩
    rw [hnil, runALeak_halt frame body 0 sa zf hh]
    rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem P s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf 0
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
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
              obtain ⟨hh, -, sa1, hst1, hrel1⟩ :=
                cell_step hsep hphys hgate hN hF hnc' P hrel hb hlt he
              have hb' := hb
              rw [hcb, cellBody_getElem?] at hb'
              obtain ⟨b0, hb0, -⟩ := Option.map_eq_some_iff.mp hb'
              have hpc1 := stepA_lpc_noCond hnc hst1
              obtain ⟨ℓ', f', sa', zf', hl', hr', hrel'⟩ := ih s1 t sa1 s1.zf hfn1 hrel1 hrun
              refine ⟨instrLeakF (imgInstr slotArr cb sa.reg.lpc bi.li_i) s ++ ℓ',
                f' + 1, sa', zf', ?_, ?_, hrel'⟩
              · rw [lsemFuelMemFLeak_step P f _ s s1 hf hev, hl']
                rfl
              · have hdl : sa.reg.lpc < cb.dropLast.length := by
                  rw [List.length_dropLast]; exact hlt
                have hbi : cb.dropLast[sa.reg.lpc] = bi := by
                  rw [List.getElem_dropLast]
                  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hb)
                rw [runALeak_step frame body f' sa s.zf hh, hst1, Option.bind_some, hr',
                  List.drop_eq_getElem_cons hdl, hbi, hpc1,
                  stepLeakA_cellBody hsep hgate hN hF hrel hb0,
                  step_leak hsep hgate hrel hlt hb]
                simp only [Option.map_some, physT,
                  ← instrLeakF_length (imgInstr slotArr cb sa.reg.lpc bi.li_i) s,
                  List.take_left', List.drop_left']

/-- **Constant time of the address machine on a body from constant time of the image of its
    cell body.** For a printed body without a conditional branch whose cell body passes the
    gate `imgGateB` and the class `physImgB`, at a separation and cell frames, constant time
    of the image of the cell body on the flag machine gives constant time of the address
    machine on the body between address states public-equal through the image of the cell
    body (`AddrPub`). -/
theorem cell_image_addr_ct {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : NoCond body) (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) pubEq) :
    ConstantTimeRel (AddrPub frame slotArr base (cellBody slotArr body) fn pubEq)
      (ARun frame body) := by
  rintro ⟨sa₁, zf₁⟩ ⟨sa₂, zf₂⟩ ℓ₁ ℓ₂
    ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hA₁⟩ ⟨g₂, r₂, hA₂⟩
  obtain ⟨v₁, F₁, sa₁', zf₁', hv₁, hL₁, -⟩ :=
    cell_image_addr_leak hsep hphys hgate hN hF hnc fn f₁ s₁ t₁ sa₁ zf₁ hfn₁ hr₁ hk₁
  obtain ⟨v₂, F₂, sa₂', zf₂', hv₂, hL₂, -⟩ :=
    cell_image_addr_leak hsep hphys hgate hN hF hnc fn f₂ s₂ t₂ sa₂ zf₂ hfn₂ hr₂ hk₂
  have hv : v₁ = v₂ := hct s₁ s₂ v₁ v₂ hpub ⟨f₁, t₁, hv₁⟩ ⟨f₂, t₂, hv₂⟩
  have e₁ := congrArg Prod.snd (runALeak_det frame body g₁ F₁ sa₁ zf₁ _ _ hA₁ hL₁)
  have e₂ := congrArg Prod.snd (runALeak_det frame body g₂ F₂ sa₂ zf₂ _ _ hA₂ hL₂)
  have hsp : sa₁.reg.lpc = sa₂.reg.lpc := by rw [hr₁.pc, hr₂.pc, hpc]
  simp only at e₁ e₂
  rw [e₁, e₂, hv, hsp]

/-! ## 2b. The events of a step under the gate with carry chains -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (icase icase_ldx icase_stx
  icase_zarr icase_simm icase_label icase_cond icase_sload icase_sstore icase_scmp icase_reg slotMov?_cases
  slotCmp?_eq imgInstr_ldx imgInstr_stx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (gateAtW instrGateBW carryI?
  castGateB gateAtW_notW readNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (classifyK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (instrLeakA_reg_indep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (phiEv evA)

/-- The wire form of an indexed load: a mnemonic that `untagCaret` reads as `LOADIDX`. -/
theorem loadIdxA?_eq {x : LinstrR} {d b idx : String} {sc : Nat}
    (h : loadIdxA? x = some (d, b, idx, sc)) :
    ∃ o, LprogAsmPrinter.untagCaret o = "LOADIDX"
      ∧ x = .Lopn [.reg d] o [.arrIdx b idx sc] := by
  unfold loadIdxA? at h
  split at h
  · split_ifs at h with ho
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using h
    exact ⟨_, ho, rfl⟩
  · cases h

/-- The wire form of an indexed store: a mnemonic that `untagCaret` reads as `STOREIDX`. -/
theorem storeIdxA?_eq {x : LinstrR} {b idx v : String} {sc : Nat}
    (h : storeIdxA? x = some (b, idx, sc, v)) :
    ∃ d o, LprogAsmPrinter.untagCaret o = "STOREIDX"
      ∧ x = .Lopn [.reg d] o [.arrIdx b idx sc, .reg v] := by
  unfold storeIdxA? at h
  split at h
  · split_ifs at h with ho
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using h
    exact ⟨_, _, ho, rfl⟩
  · cases h

/-- **The gate at an indexed load**: the scale is `8`, the base is reloaded from the slot of
    an array, and the index and the base have no frame word. -/
theorem gateAtW_loadIdx {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d b idx o : String} {sc : Nat} (hu : LprogAsmPrinter.untagCaret o = "LOADIDX")
    (hg : gateAtW frame slotArr body k W (.Lopn [.reg d] o [.arrIdx b idx sc]) = true) :
    sc = 8 ∧ (∃ A n, accArr slotArr body k b = some (A, n)) ∧ frame idx = none
      ∧ frame b = none := by
  simp only [gateAtW, Bool.and_eq_true] at hg
  obtain ⟨-, hg⟩ := hg
  have hci : carryI? (.Lopn [.reg d] o [.arrIdx b idx sc]) = none := rfl
  rw [hci] at hg
  cases hc : icase frame (.Lopn [.reg d] o [.arrIdx b idx sc]) with
  | ldx d' b' idx' =>
      obtain ⟨o', -, hx⟩ := icase_ldx hc
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, LOperand.arrIdx.injEq,
        and_true] at hx
      obtain ⟨rfl, -, rfl, rfl, rfl⟩ := hx
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨⟨An, hacc⟩, -⟩, -⟩, hidx⟩, hbf⟩ := hg
      exact ⟨rfl, ⟨An.1, An.2, hacc⟩, hidx, hbf⟩
  | stx d' b' idx' v' => have hx := icase_stx hc; simp at hx
  | zarr b' n' w' => have hx := icase_zarr hc; simp at hx
  | simm d' b' v' j => have hx := icase_simm hc; simp at hx
  | label => obtain ⟨ii, l, hx⟩ := icase_label hc; simp at hx
  | cond cc l => have hx := icase_cond hc; simp at hx
  | sload d' q => rcases slotMov?_cases (icase_sload hc).1 with hx | hx <;> simp at hx
  | sstore q S => rcases slotMov?_cases (icase_sstore hc).1 with hx | hx <;> simp at hx
  | scmp d' y q =>
      have hx := slotCmp?_eq (icase_scmp hc).1
      rw [NarrowTyping.normA_of_untagCaret hu (by decide)] at hx
      simp at hx
  | reg =>
      obtain ⟨ds, o', ss, hx, ho, -⟩ := ImageAddrSim.icase_reg_untagCaret hc
      simp only [LinstrR.Lopn.injEq] at hx
      exact (ho (hx.2.1 ▸ hu)).elim
  | other =>
      rw [hc] at hg
      simp [castGateB, classifyK] at hg

/-- **The gate at an indexed store**: the scale is `8`, the base is reloaded from the slot of
    an array, and the index and the base have no frame word. -/
theorem gateAtW_storeIdx {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d b idx v o : String} {sc : Nat} (hu : LprogAsmPrinter.untagCaret o = "STOREIDX")
    (hg : gateAtW frame slotArr body k W
      (.Lopn [.reg d] o [.arrIdx b idx sc, .reg v]) = true) :
    sc = 8 ∧ (∃ A n, accArr slotArr body k b = some (A, n)) ∧ frame idx = none
      ∧ frame b = none := by
  simp only [gateAtW, Bool.and_eq_true] at hg
  obtain ⟨-, hg⟩ := hg
  have hci : carryI? (.Lopn [.reg d] o [.arrIdx b idx sc, .reg v]) = none := rfl
  rw [hci] at hg
  cases hc : icase frame (.Lopn [.reg d] o [.arrIdx b idx sc, .reg v]) with
  | stx d' b' idx' v' =>
      obtain ⟨o', -, hx⟩ := icase_stx hc
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, LOperand.arrIdx.injEq,
        and_true] at hx
      obtain ⟨rfl, -, ⟨rfl, rfl, rfl⟩, rfl⟩ := hx
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨An, hacc⟩, hidx⟩, hbf⟩, -⟩ := hg
      exact ⟨rfl, ⟨An.1, An.2, hacc⟩, hidx, hbf⟩
  | ldx d' b' idx' => have hx := icase_ldx hc; simp at hx
  | zarr b' n' w' => have hx := icase_zarr hc; simp at hx
  | simm d' b' v' j => have hx := icase_simm hc; simp at hx
  | label => obtain ⟨ii, l, hx⟩ := icase_label hc; simp at hx
  | cond cc l => have hx := icase_cond hc; simp at hx
  | sload d' q => rcases slotMov?_cases (icase_sload hc).1 with hx | hx <;> simp at hx
  | sstore q S => rcases slotMov?_cases (icase_sstore hc).1 with hx | hx <;> simp at hx
  | scmp d' y q =>
      have hx := slotCmp?_eq (icase_scmp hc).1
      rw [NarrowTyping.normA_of_untagCaret hu (by decide)] at hx
      simp at hx
  | reg =>
      obtain ⟨ds, o', ss, hx, -, ho, -⟩ := ImageAddrSim.icase_reg_untagCaret hc
      simp only [LinstrR.Lopn.injEq] at hx
      exact (ho (hx.2.1 ▸ hu)).elim
  | other =>
      rw [hc] at hg
      simp [castGateB, classifyK] at hg

/-- The physical events at an instruction other than an array zeroing or a constant-index
    store, from the events `e` of its image: `phiEv base` of `e` at an indexed access; at
    every other `Lopn` the events of the address machine at the fixed state `s0`, which no
    state changes when the instruction accesses no cell; nothing otherwise. -/
def posTWBase (frame : String → Option (BitVec 64)) (base : String → BitVec 64)
    (s0 : LstateA) (x : LinstrR) (e : List CTLeak) : List CTLeak :=
  if (loadIdxA? x).isSome || (storeIdxA? x).isSome then e.map (phiEv base)
  else
    match x with
    | .Lopn ds o ss => instrLeakA frame (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) s0
    | _ => []

/-- **The physical events at an instruction under the gate with carry chains**, from its
    image instruction `i` and the events `e` of `i`: at an array zeroing of `n` words the
    events of the words of the array `A` that `i` zeroes, at a constant-index store at the
    index `j` the event of word `j` of the array `A` that `i` stores into, and `posTWBase` of
    `e` at every other instruction. -/
def posTW (frame : String → Option (BitVec 64)) (base : String → BitVec 64) (s0 : LstateA)
    (x : LinstrR) (i : LinstrRM) (e : List CTLeak) : List CTLeak :=
  match icase frame x with
  | .zarr _ n _ =>
      match i.fst with
      | .Lopn [.reg A] _ _ => ImageAddrLeakPhys.zeroEvs (base A) n
      | _ => []
  | .simm _ _ _ j =>
      match i.fst with
      | .Lopn [.reg A] _ _ => [evA (base A + BitVec.ofNat 64 (8 * j))]
      | _ => []
  | _ => posTWBase frame base s0 x e

/-- Away from an array zeroing and a constant-index store, `posTW` is `posTWBase`. -/
theorem posTW_of_ne {frame : String → Option (BitVec 64)} {base : String → BitVec 64}
    {s0 : LstateA} {x : LinstrR} (i : LinstrRM) (e : List CTLeak)
    (hz : ∀ b n w, icase frame x ≠ .zarr b n w)
    (hs : ∀ d b v j, icase frame x ≠ .simm d b v j) :
    posTW frame base s0 x i e = posTWBase frame base s0 x e := by
  unfold posTW
  split
  · rename_i h; exact absurd h (hz _ _ _)
  · rename_i h; exact absurd h (hs _ _ _ _)
  · rfl

/-- `normA` keeps the absence of a cell access. -/
theorem cellA?_normA {x : LinstrR} (h : cellA? x = none) : cellA? (normA x) = none := by
  cases x with
  | Lopn ds o ss =>
      simp only [normA]
      split_ifs with hm
      · rw [show withWidthTag 64 "MULX" = "MULX:64" by decide +kernel]
        rcases ds with _ | ⟨d, _ | _⟩ <;> rcases ss with _ | ⟨s, _ | _⟩ <;> (try cases d) <;>
          (try cases s) <;>
          simp [cellA?, LprogAsmPrinter.untagCaret_of_caret_free
            (by decide : '^' ∉ "MULX:64".toList)]
      · rw [cellA?_untagCaret]
        exact h
  | _ => exact h

/-- The gate with carry chains refuses an instruction with the mnemonic of an array zeroing
    or a constant-index store that is not of the form of one (`icase`). -/
theorem gateAtW_arrImm (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) (W : List String)
    {ds : List LOperand} {o : String} {ss : List LOperand}
    (ho : LprogAsmPrinter.untagCaret o = "ZEROARR" ∨ LprogAsmPrinter.untagCaret o = "STOREIMM")
    (hz : ∀ b n w, icase frame (.Lopn ds o ss) ≠ .zarr b n w)
    (hs : ∀ d b v j, icase frame (.Lopn ds o ss) ≠ .simm d b v j) :
    ImageAddrSimW.gateAtW frame slotArr body k W (.Lopn ds o ss) = false := by
  have hne : ∀ {o' : String}, o = o' → LprogAsmPrinter.untagCaret o' ≠ "ZEROARR" →
      LprogAsmPrinter.untagCaret o' ≠ "STOREIMM" → False := by
    intro o' h h1 h2
    subst h
    rcases ho with h | h
    · exact h1 h
    · exact h2 h
  have hci : ImageAddrSimW.carryI? (.Lopn ds o ss) = none := by
    unfold ImageAddrSimW.carryI?
    split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      split_ifs with h1 h2
      · subst h1
        simp at ho
      · subst h2
        simp at ho
      · rfl
    · rfl
  have hk : DecodePrintedAddrW.classifyK (.Lopn ds o ss) = none := by
    unfold DecodePrintedAddrW.classifyK
    split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      grind only [LprogAsmPrinter.untagCaret_of_caret_free, castTagW_caret_free, castTagW_ne_arr]
    · rfl
  unfold ImageAddrSimW.gateAtW
  rw [hci]
  cases hc : icase frame (.Lopn ds o ss) with
  | other => simp [ImageAddrSimW.castGateB, hk]
  | zarr => exact absurd hc (hz _ _ _)
  | simm => exact absurd hc (hs _ _ _ _)
  | label =>
      obtain ⟨_, _, h⟩ := ImageAddrSim.icase_label hc
      cases h
  | cond => cases ImageAddrSim.icase_cond hc
  | ldx =>
      obtain ⟨o', hu, h⟩ := ImageAddrSim.icase_ldx hc
      simp only [LinstrR.Lopn.injEq] at h
      exact (hne h.2.1 (by rw [hu]; decide) (by rw [hu]; decide)).elim
  | stx =>
      obtain ⟨o', hu, h⟩ := ImageAddrSim.icase_stx hc
      simp only [LinstrR.Lopn.injEq] at h
      exact (hne h.2.1 (by rw [hu]; decide) (by rw [hu]; decide)).elim
  | sload =>
      rcases ImageAddrSim.slotMov?_cases (ImageAddrSim.icase_sload hc).1 with h | h <;>
        simp only [LinstrR.Lopn.injEq] at h <;>
        exact (hne h.2.1 (by simp [width_tag]) (by simp [width_tag])).elim
  | sstore =>
      rcases ImageAddrSim.slotMov?_cases (ImageAddrSim.icase_sstore hc).1 with h | h <;>
        simp only [LinstrR.Lopn.injEq] at h <;>
        exact (hne h.2.1 (by simp [width_tag]) (by simp [width_tag])).elim
  | scmp =>
      obtain ⟨o', hu, h⟩ := ImageAddrSim.eq_of_normA_lopn
        (ImageAddrSim.slotCmp?_eq (ImageAddrSim.icase_scmp hc).1) (by simp [withWidthTag])
      simp only [LinstrR.Lopn.injEq] at h
      exact (hne h.2.1 (by rw [hu]; decide) (by rw [hu]; decide)).elim
  | reg =>
      obtain ⟨ds', o', ss', hx, -, -, -, h1, h2⟩ := ImageAddrSim.icase_reg_untagCaret hc
      simp only [LinstrR.Lopn.injEq] at hx
      exact (hne hx.2.1 h1 h2).elim

/-- **The events of one step under the gate with carry chains.** From states related by
    `ImgRelW`, at an instruction `bi` of a body that passes the gate `imgGateBW`, whose only
    cell operation is the address `LEA:64` of a cell and which is no conditional branch, a
    step of the address machine emits `posTW` of the image instruction and its events, at
    every fixed state `s0`. -/
theorem step_leakW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateBW frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) (hlt : sa.reg.lpc < body.length - 1)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    (hcell : ∀ c, cellA? bi.li_i = some c → ∃ D B off, c = .lea D B off)
    (hnc : ∀ c l, bi.li_i ≠ .Lcond c l) (s0 : LstateA) :
    stepLeakA frame body sa zf
      = posTW frame base s0 bi.li_i (imgInstr slotArr body sa.reg.lpc bi.li_i)
          (instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s) := by
  have hg : instrGateBW frame slotArr body sa.reg.lpc bi.li_i = true := by
    simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  unfold instrGateBW at hg
  by_cases hz : ∃ b n w, icase frame bi.li_i = .zarr b n w
  · obtain ⟨b, n, w, hc⟩ := hz
    obtain ⟨o, ho, hx⟩ := icase_zarr hc
    simp only [gateAtW, Bool.and_eq_true] at hg
    obtain ⟨-, hg⟩ := hg
    rw [show carryI? bi.li_i = none by rw [hx]; simp [carryI?], hc] at hg
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
    obtain ⟨⟨hacc, -⟩, hbf⟩ := hg
    cases hA : accArr slotArr body sa.reg.lpc b with
    | none => rw [hA] at hacc; cases hacc
    | some An =>
    obtain ⟨A, m⟩ := An
    obtain ⟨q, -, hp⟩ := ptr_of_reloadW hsep hgate hrel hA hbf
    rw [posTW, hc, hx, ImageAddrSim.imgInstr_zeroArr_of_untagCaret slotArr body _ hA ho]
    obtain ⟨ii0, x⟩ := bi
    simp only at hx hb
    subst hx
    simp [stepLeakA, hb, instrLeakA, NarrowTyping.normA_of_untagCaret ho (by decide), tagA,
      ho, zeroTagA, zeroArrA?, hp]
  by_cases hs : ∃ d b v j, icase frame bi.li_i = .simm d b v j
  · obtain ⟨d, b, v, j, hc⟩ := hs
    obtain ⟨o, ho, hx⟩ := icase_simm hc
    simp only [gateAtW, Bool.and_eq_true] at hg
    obtain ⟨-, hg⟩ := hg
    rw [show carryI? bi.li_i = none by rw [hx]; simp [carryI?], hc] at hg
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
    obtain ⟨⟨hacc, hbf⟩, -⟩ := hg
    cases hA : accArr slotArr body sa.reg.lpc b with
    | none => rw [hA] at hacc; cases hacc
    | some An =>
    obtain ⟨A, m⟩ := An
    obtain ⟨q, -, hp⟩ := ptr_of_reloadW hsep hgate hrel hA hbf
    rw [posTW, hc, hx, ImageAddrSim.imgInstr_storeImm_of_untagCaret slotArr body _ hA ho]
    obtain ⟨ii0, x⟩ := bi
    simp only at hx hb
    subst hx
    simp [stepLeakA, hb, instrLeakA, NarrowTyping.normA_of_untagCaret ho (by decide), tagA,
      ho, storeImmTagA, JasminLsemMem.storeImmStruct?, hp,
      storeImmAddr?_of_lt _ (Nat.lt_succ_self j)]
  rw [posTW_of_ne _ _ (fun b n w h => hz ⟨b, n, w, h⟩) (fun d b v j h => hs ⟨d, b, v, j, h⟩)]
  obtain ⟨ii0, x⟩ := bi
  simp only at hg hcell hnc hz hs ⊢
  cases x with
  | Lopn ds o ss =>
      cases hld : loadIdxA? (.Lopn ds o ss) with
      | some p =>
          obtain ⟨d, b, idx, sc⟩ := p
          obtain ⟨o', ho', hx⟩ := loadIdxA?_eq hld
          rw [hx] at hg hb ⊢
          obtain ⟨rfl, ⟨A, n, hacc⟩, hidx, hbf⟩ := gateAtW_loadIdx ho' hg
          obtain ⟨q, -, hp⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
          have hidxW := gateAtW_notW hg rfl (r := idx)
            (by simp [readNames, JasminLsemAddrCongr.srcNames])
            (by simp [DecodePrintedAddrW.carryIns])
            (fun q h => by simp [icase, ho'] at h)
            (fun q h => by simp [icase, ho'] at h)
          have hidxv : idxVal s.prog.base.reg idx = idxVal sa.reg idx := by
            unfold idxVal
            rw [hrel.regsEq hidx hidxW]
          rw [ImageAddrSim.imgInstr_ldx_of_untagCaret slotArr body _ hacc ho']
          simp [stepLeakA, hb, posTWBase, instrLeakA,
            NarrowTyping.normA_of_untagCaret ho' (by decide), tagA, loadIdxA?, hp, instrLeakF,
            flagCondCC?, instrLeakB, opLeakF, hidxv, phiEv, ho', width_tag]
          norm_cast
      | none =>
          cases hst : storeIdxA? (.Lopn ds o ss) with
          | some p =>
              obtain ⟨b, idx, sc, v⟩ := p
              obtain ⟨d, o', ho', hx⟩ := storeIdxA?_eq hst
              rw [hx] at hg hb ⊢
              obtain ⟨rfl, ⟨A, n, hacc⟩, hidx, hbf⟩ := gateAtW_storeIdx ho' hg
              obtain ⟨q, -, hp⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
              have hidxW := gateAtW_notW hg rfl (r := idx)
                (by simp [readNames, JasminLsemAddrCongr.srcNames])
                (by simp [DecodePrintedAddrW.carryIns])
                (fun q h => by simp [icase, ho'] at h)
                (fun q h => by simp [icase, ho'] at h)
              have hidxv : idxVal s.prog.base.reg idx = idxVal sa.reg idx := by
                unfold idxVal
                rw [hrel.regsEq hidx hidxW]
              rw [ImageAddrSim.imgInstr_stx_of_untagCaret slotArr body _ hacc ho']
              simp [stepLeakA, hb, posTWBase, instrLeakA,
                NarrowTyping.normA_of_untagCaret ho' (by decide), tagA, storeIdxA?, loadIdxA?, hp,
                instrLeakF, flagCondCC?, instrLeakB, opLeakF, hidxv, phiEv, ho', width_tag]
              norm_cast
          | none =>
              simp only [stepLeakA, hb, posTWBase, hld, hst, Option.isSome_none, Bool.or_self,
                Bool.false_eq_true, ite_false]
              by_cases h1 : LprogAsmPrinter.untagCaret o = "LOADIDX"
              · have hl' : loadIdxA? (normA (.Lopn ds o ss)) = none := by
                  rw [NarrowTyping.normA_of_untagCaret h1 (by decide)]
                  unfold loadIdxA? at hld ⊢
                  split
                  · rename_i heq
                    simp only [LinstrR.Lopn.injEq] at heq
                    obtain ⟨rfl, -, rfl⟩ := heq
                    simp [h1] at hld
                  · rfl
                simp [instrLeakA, tagA, h1, hl']
              · by_cases h2 : LprogAsmPrinter.untagCaret o = "STOREIDX"
                · have hs' : storeIdxA? (normA (.Lopn ds o ss)) = none := by
                    rw [NarrowTyping.normA_of_untagCaret h2 (by decide)]
                    unfold storeIdxA? at hst ⊢
                    split
                    · rename_i heq
                      simp only [LinstrR.Lopn.injEq] at heq
                      obtain ⟨rfl, -, rfl⟩ := heq
                      simp [h2] at hst
                    · rfl
                  simp [instrLeakA, tagA, h2, hs']
                · rcases tagA_lopn_cases h1 h2 with ht | ⟨_, _, ht⟩ | ⟨_, _, ht⟩ <;> rw [ht]
                  · cases hc : cellA? (.Lopn ds o ss) with
                    | none => exact instrLeakA_reg_indep (cellA?_normA hc) _ sa s0
                    | some c =>
                        obtain ⟨D, B, off, rfl⟩ := hcell c hc
                        obtain ⟨m, n, hx, hm, hn⟩ := cellA_lea hc
                        rw [hx, NarrowTyping.normA_of_untagCaret hm (by decide)]
                        simp [instrLeakA, slotMov?, slotCmp?, cellA?, hn,
                          LprogAsmPrinter.untagCaret_of_caret_free (m := "LEA:64") (by decide)]
                  · have ho : LprogAsmPrinter.untagCaret o = "ZEROARR" := by
                      by_contra h3
                      simp only [tagA, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at ht
                      split_ifs at ht
                      unfold storeImmTagA at ht
                      split at ht <;> simp at ht
                    rw [gateAtW_arrImm _ _ _ _ _ (Or.inl ho) (fun b n w h => hz ⟨b, n, w, h⟩)
                      (fun d b v j h => hs ⟨d, b, v, j, h⟩)] at hg
                    cases hg
                  · have ho : LprogAsmPrinter.untagCaret o = "STOREIMM" := by
                      by_contra h4
                      have h3 : LprogAsmPrinter.untagCaret o ≠ "ZEROARR" := by
                        intro h3
                        simp only [tagA, h3, zeroTagA, String.reduceEq, ite_true,
                          ite_false] at ht
                        split at ht <;> simp at ht
                      simp only [tagA, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] at ht
                      split_ifs at ht
                    rw [gateAtW_arrImm _ _ _ _ _ (Or.inr ho) (fun b n w h => hz ⟨b, n, w, h⟩)
                      (fun d b v j h => hs ⟨d, b, v, j, h⟩)] at hg
                    cases hg
  | Lcond c l => exact absurd rfl (hnc c l)
  | _ => simp [stepLeakA, hb, posTWBase, loadIdxA?, storeIdxA?]

/-- The only cell operation of an instruction of the cell body of a body with cell frames is
    the address `LEA:64` of a cell. -/
theorem cellA?_cellBody {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hF : CellFrames frame slotArr base rsp body) {k : Nat} {bi : Linstr}
    (hb : (cellBody slotArr body)[k]? = some bi) :
    ∀ c, cellA? bi.li_i = some c → ∃ D B off, c = .lea D B off := by
  rw [cellBody_getElem?] at hb
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  intro c hc'
  cases hc : cellA? b0.li_i with
  | none => rw [cellMove_of_none hc, hc] at hc'; cases hc'
  | some op =>
      cases op with
      | ld D B off =>
          obtain ⟨A, m, hacc, -⟩ := hF.ld _ _ D B off hb0 hc
          have hm : cellMove slotArr body k b0
              = ⟨b0.li_ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩ := by
            simp [cellMove, hc, hacc]
          rw [hm] at hc'
          simp [cellA?, LprogAsmPrinter.untagCaret_of_caret_free
            (by decide : '^' ∉ "MOVQ".toList)] at hc'
      | st B off S =>
          obtain ⟨A, m, hacc, -⟩ := hF.st _ _ B off S hb0 hc
          have hm : cellMove slotArr body k b0
              = ⟨b0.li_ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩ := by
            simp [cellMove, hc, hacc]
          rw [hm] at hc'
          simp [cellA?, LprogAsmPrinter.untagCaret_of_caret_free
            (by decide : '^' ∉ "MOVQ".toList)] at hc'
      | lea D B off =>
          rw [cellMove_of_lea hc, hc] at hc'
          exact ⟨D, B, off, (Option.some.inj hc').symm⟩

/-- **The physical trace of the image simulation under the gate with carry chains** along
    the instructions `xs` of `body` from position `k`: at each instruction `x`, `posTW` of
    the image of `x` and the next `evCountF` events of the virtual trace `ℓ`, the count of
    the image of `x`. -/
def physTW (frame : String → Option (BitVec 64)) (base : String → BitVec 64)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) (s0 : LstateA) :
    List Linstr → Nat → List CTLeak → List CTLeak
  | [], _, _ => []
  | x :: xs, k, ℓ =>
      posTW frame base s0 x.li_i (imgInstr slotArr body k x.li_i)
          (ℓ.take (evCountF (imgInstr slotArr body k x.li_i)))
        ++ physTW frame base slotArr body s0 xs (k + 1)
          (ℓ.drop (evCountF (imgInstr slotArr body k x.li_i)))

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (haltedA_of_imgW)

/-- **The traced image simulation of a cell body with carry chains.**
    `cell_image_addr_leak` at the relation `ImgRelW` and the gate `imgGateBW`: the address
    machine on the body emits `physTW` of the trace of the image of the cell body, at every
    fixed state `s0`. -/
theorem cell_image_addr_leakW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : NoCond body) (fn : String) (s0 : LstateA) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRelW frame slotArr base (cellBody slotArr body) s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
        = some t →
      ∃ ℓ fuel' sa' zf',
        lsemFuelMemFLeak (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) fuel s
          = some (t, ℓ)
        ∧ runALeak frame body fuel' sa zf
            = some ((sa', zf'),
                physTW frame base slotArr (cellBody slotArr body) s0
                  ((cellBody slotArr body).dropLast.drop sa.reg.lpc) sa.reg.lpc ℓ)
        ∧ ImgRelW frame slotArr base (cellBody slotArr body) t sa' zf' := by
  set cb := cellBody slotArr body with hcb
  set P := singletonProgM fn (virtImg slotArr cb)
  have hnc' : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l :=
    fun k bi hb => hnc bi (List.mem_of_getElem? hb)
  have halt : ∀ (s : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRelW frame slotArr base cb s sa zf → findInstrMem P s.prog = none →
      ∀ fuel, ∃ ℓ fuel' sa' zf',
        lsemFuelMemFLeak P fuel s = some (s, ℓ)
        ∧ runALeak frame body fuel' sa zf
            = some ((sa', zf'),
                physTW frame base slotArr cb s0 (cb.dropLast.drop sa.reg.lpc) sa.reg.lpc ℓ)
        ∧ ImgRelW frame slotArr base cb s sa' zf' := by
    intro s sa zf hfn hrel hf fuel
    have hnil : cb.dropLast.drop sa.reg.lpc = [] := by
      have h := hf
      rw [findInstrMem_single hfn, List.getElem?_eq_none_iff, virtImg_length, ← hrel.pc] at h
      exact List.drop_eq_nil_of_le (by rw [List.length_dropLast]; exact h)
    have hh := haltedA_of_imgW hgate fn hfn hrel.pc hf
    rw [haltedA_cellBody] at hh
    refine ⟨[], 0, sa, zf, lsemFuelMemFLeak_halt P fuel s hf, ?_, hrel⟩
    rw [hnil, runALeak_halt frame body 0 sa zf hh]
    rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem P s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf 0
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
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
              obtain ⟨hh, -, sa1, hst1, hrel1⟩ :=
                cell_stepW hsep hphys hgate hN hF hnc' P hrel hb hlt he
              have hb' := hb
              rw [hcb, cellBody_getElem?] at hb'
              obtain ⟨b0, hb0, hbe⟩ := Option.map_eq_some_iff.mp hb'
              have hncb : ∀ c l, bi.li_i ≠ .Lcond c l := by
                intro c l he'
                rw [← hbe] at he'
                unfold cellMove at he'
                split at he'
                · split at he'
                  · cases he'
                  · exact hnc' _ _ hb0 c l he'
                · split at he'
                  · cases he'
                  · exact hnc' _ _ hb0 c l he'
                · exact hnc' _ _ hb0 c l he'
              have hpc1 := stepA_lpc_noCond hnc hst1
              obtain ⟨ℓ', f', sa', zf', hl', hr', hrel'⟩ := ih s1 t sa1 s1.zf hfn1 hrel1 hrun
              refine ⟨instrLeakF (imgInstr slotArr cb sa.reg.lpc bi.li_i) s ++ ℓ',
                f' + 1, sa', zf', ?_, ?_, hrel'⟩
              · rw [lsemFuelMemFLeak_step P f _ s s1 hf hev, hl']
                rfl
              · have hdl : sa.reg.lpc < cb.dropLast.length := by
                  rw [List.length_dropLast]; exact hlt
                have hbi : cb.dropLast[sa.reg.lpc] = bi := by
                  rw [List.getElem_dropLast]
                  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hb)
                rw [runALeak_step frame body f' sa s.zf hh, hst1, Option.bind_some, hr',
                  List.drop_eq_getElem_cons hdl, hbi, hpc1,
                  stepLeakA_cellBodyW hsep hgate hN hF hrel hb0,
                  step_leakW hsep hgate hrel hlt hb (cellA?_cellBody hF hb) hncb s0]
                simp only [Option.map_some, physTW,
                  ← instrLeakF_length (imgInstr slotArr cb sa.reg.lpc bi.li_i) s,
                  List.take_left', List.drop_left']

/-- **Constant time of the address machine on a body from constant time of the image of its
    cell body, with carry chains.** `cell_image_addr_ct` at the gate `imgGateBW`. -/
theorem cell_image_addr_ctW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : NoCond body) (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr (cellBody slotArr body))) pubEq) :
    ConstantTimeRel (AddrPub frame slotArr base (cellBody slotArr body) fn pubEq)
      (ARun frame body) := by
  rintro ⟨sa₁, zf₁⟩ ⟨sa₂, zf₂⟩ ℓ₁ ℓ₂
    ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hA₁⟩ ⟨g₂, r₂, hA₂⟩
  obtain ⟨v₁, F₁, sa₁', zf₁', hv₁, hL₁, -⟩ :=
    cell_image_addr_leakW hsep hphys hgate hN hF hnc fn sa₁ f₁ s₁ t₁ sa₁ zf₁ hfn₁
      (ImageAddrSimW.imgRelW_of hr₁) hk₁
  obtain ⟨v₂, F₂, sa₂', zf₂', hv₂, hL₂, -⟩ :=
    cell_image_addr_leakW hsep hphys hgate hN hF hnc fn sa₁ f₂ s₂ t₂ sa₂ zf₂ hfn₂
      (ImageAddrSimW.imgRelW_of hr₂) hk₂
  have hv : v₁ = v₂ := hct s₁ s₂ v₁ v₂ hpub ⟨f₁, t₁, hv₁⟩ ⟨f₂, t₂, hv₂⟩
  have e₁ := congrArg Prod.snd (runALeak_det frame body g₁ F₁ sa₁ zf₁ _ _ hA₁ hL₁)
  have e₂ := congrArg Prod.snd (runALeak_det frame body g₂ F₂ sa₂ zf₂ _ _ hA₂ hL₂)
  have hsp : sa₁.reg.lpc = sa₂.reg.lpc := by rw [hr₁.pc, hr₂.pc, hpc]
  simp only at e₁ e₂
  rw [e₁, e₂, hv, hsp]

end CellStep

/-! ## 3. The virtual body of the cell route -/

section Route

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind slotArrOf slotRen
  entryV entryB_spec frameE fuseRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (fuseMulHi_lsemFuelMemFLeak_pre)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (afterArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub
  memFCT_of_ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiBase abiReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- The flag-machine entry state of the virtual body of the cell route at the machine state
    `sa`: the base `entryV` at the frame map with the cells of the layout, with the cell
    arrays emptied, the function `fn`, the zero flag clear. -/
abbrev cellEntry (σ : AbiLayout) (body : Lcmd) (fn : String) (sa : AState) : LstateMF :=
  { prog :=
      { base := emptyArrs (cellArrs σ) (entryV σ
          (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa (fun x => x))
        lfn := fn }
    zf := false }

/-- **The trace of the virtual body of the cell route.** Let the folded chain `C2` pass
    `cellRouteB` against the printed body, the cell names pass `cellNamesOkB`, and `C2` be
    the cell fold of a chain `C` that runs from the state `afterArgs` behind the copies of
    the parameter registers. At a machine state with the stack parameters at entry, every
    terminating traced run of the virtual body `cellVirt σ nm C2 fuse` from `cellEntry` emits
    `cellT` of the events of `C` from `afterArgs`. -/
theorem cellVirt_leak {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C C2 : List LinstrRM} {fuse : Bool}
    (hg : cellRouteB σ nm body outs C2 fuse = true) (hN : cellNamesOkB σ body = true)
    (hfold : cellFold (cellArrs σ) [] C = some C2) (sa : AState) (hst : σ.StackIn sa)
    (fn : String)
    {bz : LstateM × Bool} (hrun : runStraightF C (afterArgs σ body sa) false = some bz)
    {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (cellVirt σ nm C2 fuse)) (cellEntry σ body fn sa) ℓ) :
    ℓ = cellT C C2 (straightLeakFF C (afterArgs σ body sa) false) := by
  simp only [cellRouteB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hent⟩, -⟩, -⟩, -⟩, hlop⟩, hfuse⟩, -⟩ := hg
  have N := cellNamesOkB_spec hN
  have E := entryB_spec hent sa
  obtain ⟨b, z⟩ := bz
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrs σ) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrs σ) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hfrA : ∀ j, j < σ.args.length →
      frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) (argName j) = none := by
    intro j hj
    simp only [frameC, N.arg j hj]
    exact E.argF j hj
  have hfrR : ImageAddrRoute.ArgSrc σ nm
      (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa :=
    (E.argSrc hst).congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, cellIdx_slotOfReg])
  have hpr0 := ImageAddrRoute.argBind_entryV (nm := nm) (sa := sa) (un := fun x => x) hfrA
    E.argG hfrR false
  have hpr1 := runStraightF_argBind_empty (R := cellArrs σ) hpr0
  obtain ⟨env', b2, hF2, -⟩ :=
    runStraightF_cellFold N.slots N.dist C [] C2 hfold (cellRel_entry N.dist) hrun
  have hB : runStraightF (argBind σ nm ++ C2) (emptyArrs (cellArrs σ)
      (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa fun x => x))
      false = some (b2, z) := by
    rw [JasminLsemAddrMem.runStraightF_append, hpr1, Option.bind_some]
    exact hF2
  have hl : ∀ i ∈ argBind σ nm ++ C2, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact isLopnB_isLopn (List.all_eq_true.mp hlop i hi)
  have hfr0 := fRun_of_runStraightF fn _ hl _ false (b2, z) rfl hB
  have htr : straightLeakFF (argBind σ nm ++ C2) (emptyArrs (cellArrs σ)
      (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa fun x => x))
      false = cellT C C2 (straightLeakFF C (afterArgs σ body sa) false) := by
    have hq : ∀ i ∈ argBind σ nm, ∀ r, instrLeakB r i = [] := movesOf_quiet _
    rw [straightLeakFF_append _ _ _ _ _ hpr1, straightLeakFF_quiet _ hq, List.nil_append]
    exact straightLeakFF_cellFold N.slots N.dist C [] C2 hfold (cellRel_entry N.dist) hrun
  rw [← htr]
  cases fuse with
  | false => exact fRun_unique hr hfr0
  | true =>
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hfuse
      have habiC := ImageAddrRoute.entryV_abiEntry (un := fun x => x) (sa := sa) hfrA E.argG
        fun _ _ => rfl
      have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm ++ cellNames (cellArrs σ))
          (emptyArrs (cellArrs σ)
          (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa
            fun x => x)) := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact e64_of_abiEntryM habiC x hx
          · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
            exact congrArg (·.1) (ImageAddrRoute.entryV_srcOf (un := fun x => x) hfrR ha)
        · obtain ⟨⟨A, j⟩, hc⟩ := Option.isSome_iff_exists.mp (cellIdx_isSome.mpr hx)
          simp only [emptyArrs, entryV, frameC, hc]
      obtain ⟨fuel, t, hrun0⟩ := hfr0
      obtain ⟨fuel', t', hrun'⟩ := fuseMulHi_lsemFuelMemFLeak_pre hfuse.1 fn
        (cellEntry σ body fn sa) rfl hE fuel (t, _) hrun0
      exact fRun_unique hr ⟨fuel', t', hrun'⟩

/-- **Equal traces of the chain between public-equal entries.** From the states `afterArgs`
    behind the copies of the parameter registers of two machine states related by
    `StraightPub`, the chain `C` runs and emits the same events `straightLeakFF`. -/
def ChainCT (σ : AbiLayout) {Γ : Ctxt jasminDialect} (L : Labels Γ) (body : Lcmd)
    (C : List LinstrRM) : Prop :=
  ∀ sa₁ sa₂ : AState, StraightPub σ L sa₁ sa₂ →
    (∃ bz, runStraightF C (afterArgs σ body sa₁) false = some bz)
      ∧ (∃ bz, runStraightF C (afterArgs σ body sa₂) false = some bz)
      ∧ straightLeakFF C (afterArgs σ body sa₁) false
        = straightLeakFF C (afterArgs σ body sa₂) false

/-- `ChainCT` from a trace of the chain that is a map `T` of the valuation the layout reads
    off the entry state, equal at valuations that agree on the public labels. -/
theorem chainCT_of_trace {σ : AbiLayout} {Γ : Ctxt jasminDialect} {L : Labels Γ} {body : Lcmd}
    {C : List LinstrRM} (T : Ctxt.Valuation Γ → List CTLeak)
    (hrun : ∀ (sa : AState) (V : Ctxt.Valuation Γ), ExportCertEntry.AbiValOf σ sa V →
      (∃ bz, runStraightF C (afterArgs σ body sa) false = some bz)
        ∧ straightLeakFF C (afterArgs σ body sa) false = T V)
    (hct : ∀ V₁ V₂, PubEqV L V₁ V₂ → T V₁ = T V₂) : ChainCT σ L body C := by
  rintro sa₁ sa₂ ⟨V₁, V₂, hV₁, hV₂, hp, -⟩
  obtain ⟨h₁, e₁⟩ := hrun sa₁ V₁ hV₁
  obtain ⟨h₂, e₂⟩ := hrun sa₂ V₂ hV₂
  exact ⟨h₁, h₂, by rw [e₁, e₂, hct V₁ V₂ hp]⟩

/-- **The conjuncts of the gate of the cell route** used on traced runs: the check of the
    cell names, and a cell fold `C2` of the coalesced chain of the program that passes
    `cellRouteB` with the cells of the result observed. -/
theorem straightCellB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd} {fuse : Bool}
    {Γ : Ctxt jasminDialect} {m : Nat} {com : Com jasminDialect Γ (.stackArr 64 m)}
    (hg : straightCellB σ nm body fuse com = true) :
    cellNamesOkB σ body = true
      ∧ ∃ C2, cellFold (cellArrs σ) []
          ((JasminLsemMem.straightOpsMem Γ.length com Γ.length).map
            (JasminLsemExportTransfer.renRM (ImageStraightRoute.chainAlias
              (JasminLsemMem.straightOpsMem Γ.length com Γ.length)))) = some C2
        ∧ cellRouteB σ nm body ((List.range m).map fun j =>
            memName (ImageStraightRoute.chainAlias
              (JasminLsemMem.straightOpsMem Γ.length com Γ.length)
              (comRetReg Γ.length argName com Γ.length)) (8 * j)) C2 fuse = true := by
  simp only [straightCellB, Bool.and_eq_true] at hg
  obtain ⟨⟨-, hN⟩, hroute⟩ := hg
  split at hroute
  · rename_i C2 hfold
    exact ⟨hN, C2, hfold, hroute⟩
  · cases hroute

/-- **Constant time of the virtual body of the cell route.** Let the folded chain `C2` pass
    `cellRouteB` against the printed body, the cell names pass `cellNamesOkB`, and `C2` be
    the cell fold of a chain `C` with equal traces between public-equal entries (`ChainCT`).
    The virtual body `cellVirt σ nm C2 fuse` is constant time on the flag machine between the
    entries `cellEntry` of machine states related by `StraightPub`. -/
theorem straightCell_memFCT {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C C2 : List LinstrRM} {fuse : Bool} {Γ : Ctxt jasminDialect}
    {L : Labels Γ} (hg : cellRouteB σ nm body outs C2 fuse = true)
    (hN : cellNamesOkB σ body = true) (hfold : cellFold (cellArrs σ) [] C = some C2)
    (hC : ChainCT σ L body C) (fn : String) :
    MemFCT (singletonProgM fn (cellVirt σ nm C2 fuse))
      (StraightEntryPub σ L (cellEntry σ body fn)) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨sa₁, sa₂, hpub, rfl, rfl⟩ r₁ r₂
  obtain ⟨⟨bz₁, h₁⟩, ⟨bz₂, h₂⟩, he⟩ := hC sa₁ sa₂ hpub
  obtain ⟨-, -, -, -, -, hr₁, hr₂, -⟩ := hpub
  rw [cellVirt_leak hg hN hfold sa₁ hr₁.stackIn fn h₁ r₁,
    cellVirt_leak hg hN hfold sa₂ hr₂.stackIn fn h₂ r₂, he]

/-- **The check on traced runs of the cell route**: `ownedCheckML` observing `outs` on the
    virtual body `cellVirt σ nm C2 fuse` and the image of the cell body of the printed body,
    the pair that `cellRouteB` compares with `ownedCheckMC`. -/
def straightCellLB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (outs : List String)
    (C2 : List LinstrRM) (fuse : Bool) : Bool :=
  let sl := slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)
  ownedCheckML outs (cellVirt σ nm C2 fuse) (virtImg sl (cellBody sl body))

/-- **Constant time of the image of the cell body.** Under the hypotheses of
    `straightCell_memFCT` and the check on traced runs `straightCellLB`, the image of the
    cell body of the printed body is constant time on the flag machine between entries of the
    virtual body, public-equal by `StraightEntryPub`, at pc `0` and with halting checked runs
    (`TVPub`). -/
theorem straightCell_image_memFCT {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C C2 : List LinstrRM} {fuse : Bool} {Γ : Ctxt jasminDialect}
    {L : Labels Γ} (hg : cellRouteB σ nm body outs C2 fuse = true)
    (hlk : straightCellLB σ nm body outs C2 fuse = true)
    (hN : cellNamesOkB σ body = true) (hfold : cellFold (cellArrs σ) [] C = some C2)
    (hC : ChainCT σ L body C) (fn : String) :
    MemFCT (singletonProgM fn (virtImg (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm)
        fun x => x)) (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
        body)))
      (TVPub fn (cellVirt σ nm C2 fuse) (StraightEntryPub σ L (cellEntry σ body fn))) :=
  memFCT_of_ownedCheckML hlk fn (straightCell_memFCT hg hN hfold hC fn)

/-! ## 4. The entry of the cell route and the decoded bytes -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk
  lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotRen_some slotArrOf_some
  imgSep_slotRen imgRel_entryV boundFacts_entryV entryA rsOf abiBase_argName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel imgGateB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW imgGateBW_congr
  retOutsB retOutsB_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (CellFrames CellNoSlot
  image_addr_simB image_addr_simBW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI frameIn runA_congr
  runSafe_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (AddrPub ARun NoCond
  runALeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (regK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (SafeW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (Entry runALeak_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
  (lsemFuelMemF_of_runStraightF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHi_lsemFuelMemF_pre)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (Disjoint8)

/-- **The virtual body of the cell route halts on checked runs.** Under the hypotheses of
    `cellVirt_leak`, from the entry `cellEntry` of every machine state that satisfies
    `σ.Regions`, the virtual body `cellVirt σ nm C2 fuse` has a halting checked run. -/
theorem cellVirt_checked_run {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C C2 : List LinstrRM} {fuse : Bool}
    (hg : cellRouteB σ nm body outs C2 fuse = true) (hN : cellNamesOkB σ body = true)
    (hfold : cellFold (cellArrs σ) [] C = some C2) (sa : AState) (hreg : σ.Regions sa)
    (fn : String) {bz : LstateM × Bool}
    (hrun : runStraightF C (afterArgs σ body sa) false = some bz) :
    ∃ f t, lsemFuelMemFk true (singletonProgM fn (cellVirt σ nm C2 fuse)) f
      (cellEntry σ body fn sa) = some t := by
  simp only [cellRouteB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hidx⟩, -⟩, -⟩, -⟩, -⟩, hent⟩, -⟩, -⟩, -⟩, hlop⟩, hfuse⟩, -⟩ := hg
  have hst := hreg.stackIn
  have N := cellNamesOkB_spec hN
  have E := entryB_spec hent sa
  obtain ⟨b, z⟩ := bz
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrs σ) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrs σ) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hfrA : ∀ j, j < σ.args.length →
      frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) (argName j) = none := by
    intro j hj
    simp only [frameC, N.arg j hj]
    exact E.argF j hj
  have hfrR : ImageAddrRoute.ArgSrc σ nm
      (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa :=
    (E.argSrc hst).congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, cellIdx_slotOfReg])
  have hpr0 := ImageAddrRoute.argBind_entryV (nm := nm) (sa := sa) (un := fun x => x) hfrA
    E.argG hfrR false
  have hpr1 := runStraightF_argBind_empty (R := cellArrs σ) hpr0
  obtain ⟨env', b2, hF2, -⟩ :=
    runStraightF_cellFold N.slots N.dist C [] C2 hfold (cellRel_entry N.dist) hrun
  have hB : runStraightF (argBind σ nm ++ C2) (emptyArrs (cellArrs σ)
      (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa fun x => x))
      false = some (b2, z) := by
    rw [JasminLsemAddrMem.runStraightF_append, hpr1, Option.bind_some]
    exact hF2
  have hl : ∀ i ∈ argBind σ nm ++ C2, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact isLopnB_isLopn (List.all_eq_true.mp hlop i hi)
  have hrun' := lsemFuelMemF_of_runStraightF fn _ hl _ b2 false z rfl hB
  obtain ⟨fuelB, tB, hrunB⟩ : ∃ fuelB tB, JasminLsemMemFlagGuard.lsemFuelMemF
      (singletonProgM fn (cellVirt σ nm C2 fuse)) fuelB (cellEntry σ body fn sa) = some tB := by
    cases fuse with
    | false => exact ⟨_, _, hrun'⟩
    | true =>
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hfuse
        have habiC := ImageAddrRoute.entryV_abiEntry (un := fun x => x) (sa := sa) hfrA E.argG
          fun _ _ => rfl
        have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm ++ cellNames (cellArrs σ))
            (emptyArrs (cellArrs σ)
            (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa
              fun x => x)) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habiC x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (ImageAddrRoute.entryV_srcOf (un := fun x => x) hfrR ha)
          · obtain ⟨⟨A, j⟩, hc⟩ := Option.isSome_iff_exists.mp (cellIdx_isSome.mpr hx)
            simp only [emptyArrs, entryV, frameC, hc]
        obtain ⟨f2, t2, -, ht2, -⟩ := fuseMulHi_lsemFuelMemF_pre hfuse.1 fn _ _ rfl hE _ hrun'
        exact ⟨f2, t2, ht2⟩
  have hents := boundFacts_entryV (nm := nm)
    (fr := frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) (un := fun x => x) hreg
    fun b hb => by
      obtain ⟨h1, h2, h3⟩ := E.bnds b hb
      refine ⟨h1, h2, ?_⟩
      simp only [frameC, hgpN _ h1]
      exact h3
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ _ rfl rfl (hents _) _ hrunB
  exact ⟨_, _, lsemFuelMemFk_of_runIdxOk true _ _ _ _ hrunB hok⟩

/-- **The entry facts of the cell route.** For a folded chain that passes `cellRouteB` and
    cell names that pass `cellNamesOkB`, at every machine state `sa` satisfying `σ.Regions`,
    with the frame map with the cells, the slot map with the cell arrays at length `0` and
    the array bases of `sa`: the separation, the cell frames, the gate `imgGateB` or the gate
    with carry chains, the agreement of the frame map with the stack frame on the names of
    the body, and the relation of the image simulation between `cellEntry` and the address
    entry. -/
theorem cellRoute_entry {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C2 : List LinstrRM} {fuse : Bool}
    (hg : cellRouteB σ nm body outs C2 fuse = true) (hN : cellNamesOkB σ body = true)
    (sa : AState) (hreg : σ.Regions sa) (fn : String) :
    ImgSep (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
        (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) (abiBase (abiReg σ) sa)
        (frameRsp body sa)
      ∧ CellFrames (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
        (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) (abiBase (abiReg σ) sa)
        (frameRsp body sa) body
      ∧ (imgGateB (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
          (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
          (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
        || (imgGateBW (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
          (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
          (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
        && retOutsB (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
          (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body) outs))
        = true
      ∧ (∀ q ∈ bodyNamesI body,
        frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) q
          = frameP (Params.ofBody body) (frameRsp body sa) q)
      ∧ ImgRel (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
        (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) (abiBase (abiReg σ) sa)
        (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
        (cellEntry σ body fn sa) (entryA σ sa) false := by
  simp only [cellRouteB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hgate⟩, hfr⟩, hent⟩, hacc⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  have N := cellNamesOkB_spec hN
  have E := entryB_spec hent sa
  have hS0 := imgSep_slotRen (ren := fun x => x) (un := fun x => x)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot
      ImageAddrRoute.slotArrOf_not_fa) fun _ _ _ _ => rfl
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := ImageAddrFrame.frameIn_some ha
    have := ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (fun x => x) q = some (A, n) →
      DecodeGenMem.regLen (rsOf σ) A = n := by
    intro q A n hq
    obtain ⟨A0, hq0, hA⟩ := slotRen_some hq
    rw [hA]
    exact E.len q A0 n hq0
  have hslC : ∀ q A n, slotRen (slotArrOf σ nm) (fun x => x) q = some (A, n) →
      cellIdx (cellArrs σ) q = none := by
    intro q A n hq
    obtain ⟨A0, hq0, -⟩ := slotRen_some hq
    obtain ⟨a, ha⟩ := E.slot q A0 n hq0
    exact N.body q (ImageAddrFrame.frameIn_some ha).1
  have hsep := imgSep_cells E.rs hreg hS0 hword hsl N.len N.gp hslC
  have hred : ∀ A j, cellIdx (cellArrs σ) (memName A (8 * j)) = some (A, j) →
      Disjoint8 (redW (frameRsp body sa))
        (ImageAddrSim.cellAt (abiBase (abiReg σ) sa A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := cellIdx_spec hc
    have hk : regK (rsOf σ) A j := by
      unfold regK
      rw [N.len _ hn]
      exact hj
    have hr : redW (frameRsp body sa)
        = sa.regs "%rsp" + BitVec.ofInt 64 (cmovRedZone - (Params.ofBody body).frame) := by
      simp only [redW, frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hr]
    have h2 := ImageAddrFrame.frameOkB_red hfr
    exact frameSep_of_regions E.rs hreg A j hk _ h2.1 h2.2
  have hF := cellFrames_of (base := abiBase (abiReg σ) sa) (rsp := frameRsp body sa) hacc N.gp
    (fun r hr => hS0.gp r hr) hred
  have hgate' : (imgGateB (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
      || (imgGateBW (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
      && retOutsB (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body) outs))
      = true := by
    rw [ImageAddrFrame.imgGateB_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa), imgGateBW_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa), retOutsB_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa)]
    exact hgate
  have hfr' : ∀ q ∈ bodyNamesI body,
      frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) q
        = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq
    simp only [frameC, N.body q hq]
    show frameIn body _ q = _
    unfold frameIn
    rw [ite_eq_left hq]
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrs σ) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrs σ) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hrel0 := imgRel_entryV (nm := nm)
    (fr := frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) (sa := sa)
    (body := cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
    (fn := fn) (ren := fun x => x) (un := fun x => x)
    ((E.argSrc hreg.stackIn).congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, cellIdx_slotOfReg]))
    (fun _ _ hs => cellBody_save hent hs) fun _ _ => rfl
  exact ⟨hsep, hF, hgate', hfr', imgRel_cellArrs (R := cellArrs σ) hrel0⟩

/-- The slot map of the cell route: the slot map of the layout with the cell arrays at
    length `0`. -/
abbrev cellSl (σ : AbiLayout) (nm : String → String) : String → Option (String × Nat) :=
  slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)

/-- The frame map of the cell route at the machine state `sa`: the frame of the printed body
    with the cells of the layout at the array bases of `sa`. -/
abbrev cellFr (σ : AbiLayout) (body : Lcmd) (sa : AState) : String → Option (BitVec 64) :=
  frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)

/-- A terminating run of the address machine on `body` from `a` every state of which
    satisfies the safety condition `SafeW` of the class with carry chains at `rsp`. -/
def SafeHaltW (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (body : Lcmd)
    (a : LstateA × Bool) : Prop :=
  ∃ fuel t, runA frame body fuel a.1 a.2 = some t
    ∧ RunSafe frame body (SafeW rsp body) fuel a.1 a.2

/-- **Equal traces of the decoded bytes of a body.** For two machine states with one frame
    address `rsp`, corresponding at entry to address states whose runs terminate safely
    (`SafeHaltW`) and whose traces of the address machine at the frame below `rsp` are equal,
    every two runs with leakage of the decoded bytes of `body` under the regime `doitm` have
    equal traces. `DecodePrintedAddrLeak.bytes_trace_eq` is this statement for the class
    `printedAddrB`, with `SafeHalt`. -/
def BytesTraceW (body : Lcmd) : Prop :=
  ∀ prog : List RInstr, decodeLprog (encodeLfundefBytes body) = some prog →
    ∀ (rsp : BitVec 64) (sa₁ sa₂ : AState), frameRsp body sa₁ = rsp → frameRsp body sa₂ = rsp →
      ∀ a₁ a₂ : LstateA × Bool, Entry sa₁ a₁.1 → Entry sa₂ a₂.1 →
        SafeHaltW (frameP (Params.ofBody body) rsp) rsp body a₁ →
        SafeHaltW (frameP (Params.ofBody body) rsp) rsp body a₂ →
        (∀ ℓ₁ ℓ₂, ARun (frameP (Params.ofBody body) rsp) body a₁ ℓ₁ →
          ARun (frameP (Params.ofBody body) rsp) body a₂ ℓ₂ → ℓ₁ = ℓ₂) →
        ∀ (ok₁ ok₂ : AState → JInstr 64 → Prop) (u₁ u₂ : List CTLeak) (sa₁' sa₂' : AState),
          RunL .doitm ok₁ prog 0 sa₁ u₁ sa₁' → RunL .doitm ok₂ prog 0 sa₂ u₂ sa₂' → u₁ = u₂

/-- **Constant time of the decoded bytes of the cell route.** Let the folded chain `C2` pass
    `cellRouteB` and the check on traced runs `straightCellLB` against the printed body, the
    cell names pass `cellNamesOkB`, and `C2` be the cell fold of a chain `C` with equal
    traces between public-equal entries (`ChainCT`). Given the passage `BytesTraceW` from the
    address machine to the decoded bytes, every decoding of the function bytes of the printed
    body is constant time under the regime `doitm` and any side condition between machine
    states related by `StraightPub`. The passage from the image of the cell body to the
    address machine is `cell_image_addr_ct` under the gate `imgGateB` and
    `cell_image_addr_ctW` under the gate with carry chains. -/
theorem straightCell_bytes_ct {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C C2 : List LinstrRM} {fuse : Bool} {Γ : Ctxt jasminDialect}
    {L : Labels Γ} (hg : cellRouteB σ nm body outs C2 fuse = true)
    (hlk : straightCellLB σ nm body outs C2 fuse = true)
    (hN : cellNamesOkB σ body = true) (hfold : cellFold (cellArrs σ) [] C = some C2)
    (hC : ChainCT σ L body C) (hB : BytesTraceW body) (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  rintro sa₁ sa₂ u₁ u₂ hpub ⟨sa₁', hb₁⟩ ⟨sa₂', hb₂⟩
  have himgCT := straightCell_image_memFCT hg hlk hN hfold hC ""
  obtain ⟨⟨bz₁, hrun₁⟩, ⟨bz₂, hrun₂⟩, -⟩ := hC sa₁ sa₂ hpub
  have hpub' := hpub
  obtain ⟨V₁, V₂, -, -, -, hreg₁, hreg₂, hrspE, hbases⟩ := hpub'
  have hk₁ := cellVirt_checked_run hg hN hfold sa₁ hreg₁ "" hrun₁
  have hk₂ := cellVirt_checked_run hg hN hfold sa₂ hreg₂ "" hrun₂
  obtain ⟨hsep, hF, hgate, hfr, hrel₁⟩ := cellRoute_entry hg hN sa₁ hreg₁ ""
  obtain ⟨-, -, -, -, hrel₂⟩ := cellRoute_entry hg hN sa₂ hreg₂ ""
  have hg' := hg
  simp only [cellRouteB, Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, -⟩, -⟩, hphys⟩, -⟩, -⟩, -⟩, -⟩, hnc⟩, hns⟩, -⟩, -⟩, -⟩ := hg'
  have hrsp : frameRsp body sa₂ = frameRsp body sa₁ := by
    unfold frameRsp
    rw [hrspE]
  have hfrE : frameE body sa₂ = frameE body sa₁ := by
    unfold frameE
    rw [hrsp]
  have hbA : ∀ p ∈ cellArrs σ,
      abiBase (abiReg σ) sa₂ p.1 = abiBase (abiReg σ) sa₁ p.1 := by
    intro p hp
    obtain ⟨j, a, hj, hk, he⟩ := cellArrs_mem hp
    rw [he, abiBase_argName hj, abiBase_argName hj]
    exact (hbases a (List.mem_of_getElem? hj) p.2 hk).symm
  have hfrC : cellFr σ body sa₂ = cellFr σ body sa₁ := by
    funext q
    show frameC _ _ _ q = frameC _ _ _ q
    unfold frameC
    cases hc : cellIdx (cellArrs σ) q with
    | none =>
        simp only
        rw [hfrE]
    | some Aj =>
        obtain ⟨A, j⟩ := Aj
        obtain ⟨n, hn, -, -⟩ := cellIdx_spec hc
        simp only
        rw [hbA _ hn]
  have hbase : ∀ q A n, cellSl σ nm q = some (A, n) →
      abiBase (abiReg σ) sa₂ A = abiBase (abiReg σ) sa₁ A := by
    intro q A n hq
    obtain ⟨m, hq', -⟩ := slotArrC_some hq
    obtain ⟨A0, hA0, rfl⟩ := slotRen_some hq'
    obtain ⟨j, a0, hj, hkind, rfl, -⟩ := slotArrOf_some hA0
    rw [abiBase_argName hj, abiBase_argName hj]
    exact (hbases a0 (List.mem_of_getElem? hj) _ hkind).symm
  have hrel₂' : ImgRel (cellFr σ body sa₁) (cellSl σ nm) (abiBase (abiReg σ) sa₁)
      (cellBody (cellSl σ nm) body) (cellEntry σ body "" sa₂) (entryA σ sa₂) false := by
    have key : ∀ fr : String → Option (BitVec 64), fr = cellFr σ body sa₁ →
        ImgRel fr (cellSl σ nm) (abiBase (abiReg σ) sa₁) (cellBody (cellSl σ nm) body)
          (cellEntry σ body "" sa₂) (entryA σ sa₂) false →
        ImgRel (cellFr σ body sa₁) (cellSl σ nm) (abiBase (abiReg σ) sa₁)
          (cellBody (cellSl σ nm) body) (cellEntry σ body "" sa₂) (entryA σ sa₂) false := by
      rintro _ rfl h
      exact h
    exact key _ hfrC (imgRel_of_base_eq hbase hrel₂)
  have himg : ∀ sa, (∃ f t, lsemFuelMemFk true (singletonProgM "" (cellVirt σ nm C2 fuse)) f
        (cellEntry σ body "" sa) = some t) →
      ∃ f t, lsemFuelMemFk true (singletonProgM ""
        (virtImg (cellSl σ nm) (cellBody (cellSl σ nm) body))) f
        (cellEntry σ body "" sa) = some t := by
    rintro sa ⟨f, t, hk⟩
    obtain ⟨f', t', hr', -⟩ := ownedCheckMC_sound hck "" _ t rfl rfl f hk
    exact ⟨f', t', hr'⟩
  obtain ⟨f₁, t₁, hi₁⟩ := himg sa₁ hk₁
  obtain ⟨f₂, t₂, hi₂⟩ := himg sa₂ hk₂
  have hncI := noCondB_spec hnc
  have hncP : NoCond body := fun bi hbi c l he => by
    have := List.all_eq_true.mp hnc bi hbi
    rw [he] at this
    cases this
  have hNS := cellNoSlotB_spec hns
  have hAP : AddrPub (cellFr σ body sa₁) (cellSl σ nm) (abiBase (abiReg σ) sa₁)
      (cellBody (cellSl σ nm) body) ""
      (TVPub "" (cellVirt σ nm C2 fuse) (StraightEntryPub σ L (cellEntry σ body "")))
      (entryA σ sa₁, false) (entryA σ sa₂, false) :=
    ⟨cellEntry σ body "" sa₁, cellEntry σ body "" sa₂,
      ⟨straightEntryPub_of_pub _ hpub, rfl, rfl, rfl, rfl, hk₁, hk₂⟩, rfl, rfl, rfl, hrel₁,
      hrel₂', ⟨f₁, t₁, hi₁⟩, ⟨f₂, t₂, hi₂⟩⟩
  have hentA : ∀ sa : AState, Entry sa (entryA σ sa) := fun sa =>
    ⟨rfl, fun R hR => by
      have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (DecodePrinted.phys R)⟩ := by
        simp only [entryA, hR, ite_true]
      unfold JasminLsemWidthN.LstateN.getW
      rw [hl]
      simp, rfl⟩
  have hsim : ConstantTimeRel (AddrPub (cellFr σ body sa₁) (cellSl σ nm)
        (abiBase (abiReg σ) sa₁) (cellBody (cellSl σ nm) body) ""
        (TVPub "" (cellVirt σ nm C2 fuse) (StraightEntryPub σ L (cellEntry σ body ""))))
        (ARun (cellFr σ body sa₁) body)
      ∧ ∀ (s t : LstateMF) (a : LstateA) (f : Nat), s.prog.lfn = "" →
        ImgRel (cellFr σ body sa₁) (cellSl σ nm) (abiBase (abiReg σ) sa₁)
          (cellBody (cellSl σ nm) body) s a false →
        lsemFuelMemFk true (singletonProgM ""
          (virtImg (cellSl σ nm) (cellBody (cellSl σ nm) body))) f s = some t →
        SafeHaltW (cellFr σ body sa₁) (frameRsp body sa₁) body (a, false) := by
    rcases Bool.or_eq_true_iff.mp hgate with hgn | hgw
    · refine ⟨cell_image_addr_ct hsep hphys hgn hNS hF hncP "" himgCT,
        fun s t a f hfn hr hk => ?_⟩
      obtain ⟨fA, sA, zA, h1, -, h3⟩ :=
        image_addr_simB hsep hphys hgn hNS hF hncI "" f s t a false hfn hr hk
      exact ⟨fA, _, h1, h3⟩
    · obtain ⟨hgw, -⟩ := Bool.and_eq_true_iff.mp hgw
      refine ⟨cell_image_addr_ctW hsep hphys hgw hNS hF hncP "" himgCT,
        fun s t a f hfn hr hk => ?_⟩
      obtain ⟨fA, sA, zA, h1, -, h3⟩ :=
        image_addr_simBW hsep hphys hgw hNS hF hncI "" f s t a false hfn
          (ImageAddrSimW.imgRelW_of hr) hk
      exact ⟨fA, _, h1, h3⟩
  obtain ⟨hA, hsafe⟩ := hsim
  obtain ⟨g₁, r₁, hrA₁, hs₁⟩ := hsafe _ t₁ _ f₁ rfl hrel₁ hi₁
  obtain ⟨g₂, r₂, hrA₂, hs₂⟩ := hsafe _ t₂ _ f₂ rfl hrel₂' hi₂
  rw [runA_congr hfr] at hrA₁ hrA₂
  rw [runSafe_congr hfr] at hs₁ hs₂
  exact hB prog hdec (frameRsp body sa₁) sa₁ sa₂ rfl hrsp (entryA σ sa₁, false)
    (entryA σ sa₂, false) (hentA sa₁) (hentA sa₂) ⟨g₁, r₁, hrA₁, hs₁⟩ ⟨g₂, r₂, hrA₂, hs₂⟩
    (fun ℓ₁ ℓ₂ h₁ h₂ => hA _ _ ℓ₁ ℓ₂ hAP
      (by simpa only [ARun, runALeak_congr hfr] using h₁)
      (by simpa only [ARun, runALeak_congr hfr] using h₂))
    ok ok u₁ u₂ sa₁' sa₂' hb₁ hb₂

end Route

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak
