/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells

@[expose] public section

set_option autoImplicit false

/-!
# Cell accesses on the image route across labels and conditional branches

The cell body `ImageAddrCells.cellBody` rewrites the cell accesses of a body and keeps every
label and every branch at its position, so a label of the body has the same position in the
cell body. This module simulates the image of the cell body of a body with labels and
conditional branches on the body itself. At a branch that the image takes, the image jumps
one past the label and the address machine stops at the label, so one step of the image is
matched by one or two steps of the address machine. The step of the image with carry chains
at a conditional branch is a parameter, `ImgStepWCond`.

## Main definitions

* `CondStep`: the step of the image of a body at a conditional branch, for a relation between
  the states of the image and of the address machine.
* `ImgStepWCond`: `CondStep` at the relation with carry chains `ImageAddrSimW.ImgRelW`.

## Main results

* `isLabelB_cellMove`, `cellMove_lcond`, `cellMove_llabel`, `labelAt_cellBody`: the cell body
  keeps labels and branches, and the position of a label.
* `stepA_cellBody`: the address machine steps a body with cells as its cell body, where the
  base register of a cell access holds the pointer of its array.
* `img_step_cond`: `CondStep` at the relation `ImageAddrSim.ImgRel`, for a body that passes
  `imgGateB`.
* `cell_step'`, `cell_stepW'`: one step of the image of the cell body on the body.
* `image_addr_simB'`, `image_addr_simBW'`: the run of the image of the cell body on the body.
* `virt_bytesC'`: a virtual body on the decoded bytes of a body with cells, labels and
  conditional branches.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (accArr imgInstr virtImg
  physImgB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM singletonProgM
  findInstrMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk
  lsemFuelMemFk RunIdxOk lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (ImgRelW imgGateBW img_stepW
  ptr_of_reloadW haltedA_of_imgW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (LoadSafeAt RunSafe
  labelAt_spec frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW frameP
  read64_eq_of_agree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (SafeW WideSafeAt
  CellSafeAt printedAddrWB printedAddr_simW)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (read64 Disjoint8 AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
  (ownedCheckMC ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (runA_congr runSafe_congr)

/-! ## 1. Labels and branches of the cell body -/

/-- The frame-word move of an instruction defines the label `l` exactly where the instruction
    does. -/
theorem isLabelB_cellMove (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : Linstr) (l : LLabel) :
    isLabelB l (cellMove slotArr body k i).li_i = isLabelB l i.li_i := by
  cases hc : cellA? i.li_i with
  | none => rw [cellMove_of_none hc]
  | some c =>
      obtain ⟨d, o, n, hx, -⟩ := cellA_some hc
      unfold cellMove
      rw [hc]
      cases c <;> simp only <;> split <;> simp [hx, isLabelB]

/-- A conditional branch is its own frame-word move. -/
theorem cellMove_lcond (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {i : Linstr} {cc : _} {l : LLabel} (h : i.li_i = .Lcond cc l) :
    cellMove slotArr body k i = i :=
  cellMove_of_none (by rw [h]; rfl)

/-- A label is its own frame-word move. -/
theorem cellMove_llabel (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {i : Linstr} {ii : _} {l : LLabel} (h : i.li_i = .Llabel ii l) :
    cellMove slotArr body k i = i :=
  cellMove_of_none (by rw [h]; rfl)

/-- A frame-word move that is a label is the frame-word move of that label. -/
theorem llabel_of_cellMove {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} {ii : _} {l : LLabel} (h : (cellMove slotArr body k i).li_i = .Llabel ii l) :
    i.li_i = .Llabel ii l := by
  cases hc : cellA? i.li_i with
  | none => rwa [cellMove_of_none hc] at h
  | some c =>
      exfalso
      obtain ⟨d, o, n, hx, -⟩ := cellA_some hc
      unfold cellMove at h
      rw [hc] at h
      cases c <;> simp only at h <;> split at h <;> simp [hx] at h

/-- **The cell body keeps the position of a label.** -/
theorem labelAt_cellBody (slotArr : String → Option (String × Nat)) (body : Lcmd)
    (l : LLabel) : labelAt (cellBody slotArr body) l = labelAt body l := by
  have hmap : (cellBody slotArr body).map (fun i => isLabelB l i.li_i)
      = body.map (fun i => isLabelB l i.li_i) := by
    apply List.ext_getElem
    · simp [cellBody_length]
    · intro n h1 h2
      simp only [cellBody, List.getElem_map, List.getElem_mapIdx]
      exact isLabelB_cellMove slotArr body n _ l
  have e : ∀ c : Lcmd, labelAt c l = (c.map (fun i => isLabelB l i.li_i)).findIdx? id := by
    intro c
    rw [List.findIdx?_map]
    rfl
  rw [e, e, hmap]

/-- **The address machine steps a body with cells as its cell body**, at a state where the
    base register of each cell access holds the pointer of its array; a cell load there is
    disjoint from the red-zone word. -/
theorem stepA_cellBody {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hF : CellFrames frame slotArr base rsp body) {sa : LstateA}
    (hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
      DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A))
    (zf : Bool) :
    CellSafeAt rsp body sa
      ∧ stepA frame body sa zf = stepA frame (cellBody slotArr body) sa zf := by
  cases hb0 : body[sa.reg.lpc]? with
  | none =>
      refine ⟨fun ii D n B off p hbi => ?_, ?_⟩
      · rw [hb0] at hbi; cases hbi
      · unfold stepA
        rw [cellBody_getElem?, hb0]
        rfl
  | some b0 =>
      have hbC : (cellBody slotArr body)[sa.reg.lpc]?
          = some (cellMove slotArr body sa.reg.lpc b0) := by
        rw [cellBody_getElem?, hb0]; rfl
      refine ⟨?_, ?_⟩
      · intro ii D n B off p hbi hn hp
        rw [hb0] at hbi
        cases hbi
        have hc : cellA? (.Lopn [.reg D] "LOAD:64" [.reg n]) = some (.ld D B off) := by
          simp [cellA?, hn]
        obtain ⟨A, m, hacc, hBf, -, hred⟩ := hF.ld _ _ D B off hb0 hc
        have hpA := hptr B A m hacc (hF.ldGp _ _ D B off hb0 hc) hBf
        rw [hp] at hpA
        cases hpA
        exact hred
      · cases hc : cellA? b0.li_i with
        | none =>
            unfold stepA
            rw [hbC, hb0, cellMove_of_none hc]
            obtain ⟨ii, li⟩ := b0
            cases li <;> simp only [tagAt_cellBody, labelAt_cellBody]
        | some op =>
            cases op with
            | ld D B off =>
                obtain ⟨A, m, hacc, hBf, hfr, -⟩ := hF.ld _ _ D B off hb0 hc
                exact stepA_cellBody_ld hb0 hc hacc
                  (hptr B A m hacc (hF.ldGp _ _ D B off hb0 hc) hBf) hfr
            | st B off S =>
                obtain ⟨A, m, hacc, hBf, hSf, hfr⟩ := hF.st _ _ B off S hb0 hc
                exact stepA_cellBody_st hb0 hc hacc
                  (hptr B A m hacc (hF.stGp _ _ B off S hb0 hc) hBf) hfr hSf

/-- A frame-word move that is a conditional branch is the frame-word move of that branch. -/
theorem lcond_of_cellMove {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} {cc : _} {l : LLabel} (h : (cellMove slotArr body k i).li_i = .Lcond cc l) :
    i.li_i = .Lcond cc l := by
  cases hc : cellA? i.li_i with
  | none => rwa [cellMove_of_none hc] at h
  | some c =>
      exfalso
      obtain ⟨d, o, n, hx, -⟩ := cellA_some hc
      unfold cellMove at h
      rw [hc] at h
      cases c <;> simp only at h <;> split at h <;> simp [hx] at h

/-! ## 2. The step at a conditional branch -/

/-- **The step of the image at a conditional branch**, for a relation `R` between the states
    of the image of the body `c` and of the address machine. From related states at a
    conditional branch before the last position, a checked step of the image instruction is
    matched on `c` by a step of the address machine, which does not halt and reads outside
    the red-zone word, to a state `sa1` that is related to the image state, or that stands at
    a label, from where a second step reaches a related state. -/
def CondStep (R : LstateMF → LstateA → Bool → Prop) (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (rsp : BitVec 64) (c : Lcmd) (fn : String) :
    Prop :=
  ∀ (s t : LstateMF) (sa : LstateA) (bi : Linstr) (cnd : _) (l : LLabel),
    R s sa s.zf → c[sa.reg.lpc]? = some bi → sa.reg.lpc < c.length - 1 →
    bi.li_i = .Lcond cnd l →
    evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t →
    haltedA c sa = false ∧ LoadSafeAt rsp c sa
      ∧ ∃ sa1, stepA frame c sa s.zf = some (sa1, t.zf)
        ∧ (R t sa1 t.zf
          ∨ ((∃ bp ii l, c[sa1.reg.lpc]? = some bp ∧ bp.li_i = .Llabel ii l)
            ∧ haltedA c sa1 = false ∧ LoadSafeAt rsp c sa1
            ∧ ∃ sa2, stepA frame c sa1 t.zf = some (sa2, t.zf) ∧ R t sa2 t.zf))

/-- **The step of the image with carry chains at a conditional branch**: `CondStep` at the
    relation `ImgRelW` of the body `c`. -/
abbrev ImgStepWCond (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (c : Lcmd) (fn : String) : Prop :=
  CondStep (ImgRelW frame slotArr base c) frame slotArr rsp c fn

/-- **The step of the image at a conditional branch of a body that passes `imgGateB`.** -/
theorem img_step_cond {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} (rsp : BitVec 64)
    {body : Lcmd} (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) :
    CondStep (ImgRel frame slotArr base body) frame slotArr rsp body fn := by
  intro s t sa bi cc0 l hrel hb hlt hx hstep
  have hg : instrGateB frame slotArr body sa.reg.lpc bi.li_i = true := by
    simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  unfold instrGateB at hg
  rw [hx] at hg
  cases cc0 with
  | reg cc =>
      simp only [icase, Bool.and_eq_true, Option.isSome_iff_exists] at hg
      obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hg
      have hi : imgInstr slotArr body sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
        rw [hx]; rfl
      obtain ⟨r, hr, hret⟩ := imgGateB_last hgate
      have hfl := findLabel_virtImg slotArr body l (fun r' hr' => by
        rw [hr] at hr'
        cases hr'
        rw [hret]; rfl)
      rw [hp] at hfl
      rw [hi, evalInstrPMemFk_reg, hx, eval_cond fn _ cc l _ hpol hfl] at hstep
      have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
      obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
      have hbp : body[p]? = some body[p] := List.getElem?_eq_getElem hpl
      have hlabp : ∃ ii', body[p].li_i = .Llabel ii' l := by
        revert hlab
        cases body[p].li_i <;> simp [isLabelB]
      obtain ⟨ii', hli⟩ := hlabp
      have hstepA : stepA frame body sa s.zf = if s.zf = pol then some (sa.setLpc p, s.zf)
          else some (sa.setLpc (sa.reg.lpc + 1), s.zf) := by
        obtain ⟨ii0, li⟩ := bi
        simp only at hx
        subst hx
        simp only [stepA, hb, hpol, hp, Option.map_some]
      refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), ?_⟩
      by_cases hzp : s.zf = pol
      · rw [if_pos hzp] at hstep hstepA
        cases hstep
        refine ⟨_, hstepA, Or.inr ⟨⟨body[p], ii', l, by simp [LstateA.setLpc], hli⟩,
          haltedA_of (bi := body[p]) (by simp [LstateA.setLpc]) (by rw [hli]; simp),
          loadSafe_of (bi := body[p]) (by simp [LstateA.setLpc]) (by rw [hli]; simp),
          sa.setLpc (p + 1), ?_, rel_jump hphys hrel hb hnm hbp (by rw [hli]; rfl)
            (fun ds o ss h => by rw [hli] at h; cases h)⟩⟩
        have hb' : body[p]? = some body[p] := hbp
        generalize body[p] = bp at hli hb'
        obtain ⟨ii1, li1⟩ := bp
        simp only at hli
        subst hli
        simp [stepA, LstateA.setLpc, hb']
      · rw [if_neg hzp] at hstep hstepA
        cases hstep
        exact ⟨_, hstepA, Or.inl (rel_label hphys hrel hb hnm)⟩
  | _ => simp [icase] at hg

/-- **A conditional branch of the cell body on the body.** The step `CondStep` of the image
    of the cell body at a conditional branch is matched on the body by one step of the
    address machine, or by two when the first stops at a label; the address machine does not
    halt and is safe in the sense of `SafeW` at each state it steps from. -/
theorem cell_cond {R : LstateMF → LstateA → Bool → Prop}
    {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {rsp : BitVec 64} {body : Lcmd} {fn : String}
    (hcond : CondStep R frame slotArr rsp (cellBody slotArr body) fn)
    {s t : LstateMF} {sa : LstateA} (hrel : R s sa s.zf) {b0 : Linstr}
    (hb0 : body[sa.reg.lpc]? = some b0) {cc : _} {l : LLabel} (hx : b0.li_i = .Lcond cc l)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc b0.li_i) s = some t) :
    haltedA body sa = false ∧ SafeW rsp body sa
      ∧ ∃ sa1, stepA frame body sa s.zf = some (sa1, t.zf)
        ∧ (R t sa1 t.zf
          ∨ (haltedA body sa1 = false ∧ SafeW rsp body sa1
            ∧ ∃ sa2, stepA frame body sa1 t.zf = some (sa2, t.zf) ∧ R t sa2 t.zf)) := by
  have hbC : (cellBody slotArr body)[sa.reg.lpc]? = some b0 := by
    rw [cellBody_getElem?, hb0, Option.map_some, cellMove_lcond slotArr body _ hx]
  obtain ⟨-, -, sa1, hst, hcase⟩ := hcond s t sa b0 cc l hrel hbC hlt hx hstep
  have hsafe : ∀ {sx : LstateA} {bx : Linstr}, body[sx.reg.lpc]? = some bx →
      (∀ ds o ss, bx.li_i ≠ .Lopn ds o ss) → SafeW rsp body sx := by
    intro sx bx hbx hno
    refine ⟨loadSafe_of hbx (fun D B I => hno _ _ _), fun ii ds o ss hb => ?_,
      fun ii D n B off p hb => ?_⟩
    · rw [hbx] at hb; cases hb; exact absurd rfl (hno ds o ss)
    · rw [hbx] at hb; cases hb; exact absurd rfl (hno _ _ _)
  have he : stepA frame body sa s.zf = stepA frame (cellBody slotArr body) sa s.zf := by
    unfold stepA
    rw [hbC, hb0]
    obtain ⟨ii, li⟩ := b0
    simp only at hx
    subst hx
    cases cc <;> simp only [labelAt_cellBody]
  refine ⟨haltedA_of hb0 (by rw [hx]; simp), hsafe hb0 (by rw [hx]; simp), sa1,
    by rw [he]; exact hst, ?_⟩
  rcases hcase with h | ⟨⟨bl, ii, l', hbl, hli⟩, -, -, sa2, hst2, h⟩
  · exact Or.inl h
  · rw [cellBody_getElem?] at hbl
    obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp hbl
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
    exact Or.inr ⟨haltedA_of hb1 (by rw [hl1]; simp), hsafe hb1 (by rw [hl1]; simp), sa2,
      by rw [e _ hb1]; exact hst2, h⟩

/-! ## 3. One step of a body with cells -/

/-- **One step of a body with cells through its cell body.** `ImageAddrCells.cell_step` at
    every instruction: a branch that the image takes is matched by two steps of the address
    machine. -/
theorem cell_step' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) s sa s.zf) {bi : Linstr}
    (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t) :
    haltedA body sa = false ∧ SafeW rsp body sa
      ∧ ∃ sa1, stepA frame body sa s.zf = some (sa1, t.zf)
        ∧ (ImgRel frame slotArr base (cellBody slotArr body) t sa1 t.zf
          ∨ (haltedA body sa1 = false ∧ SafeW rsp body sa1
            ∧ ∃ sa2, stepA frame body sa1 t.zf = some (sa2, t.zf)
              ∧ ImgRel frame slotArr base (cellBody slotArr body) t sa2 t.zf)) := by
  rw [cellBody_getElem?] at hb
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  by_cases hcnd : ∃ cc l, b0.li_i = .Lcond cc l
  · obtain ⟨cc, l, hx⟩ := hcnd
    rw [cellMove_lcond slotArr body _ hx] at hstep
    exact cell_cond (img_step_cond rsp hphys hgate fn) hrel hb0 hx hlt hstep
  · have hnc' : ∀ cc l, (cellMove slotArr body sa.reg.lpc b0).li_i ≠ .Lcond cc l :=
      fun cc l he => hcnd ⟨cc, l, lcond_of_cellMove he⟩
    have hbC : (cellBody slotArr body)[sa.reg.lpc]?
        = some (cellMove slotArr body sa.reg.lpc b0) := by
      rw [cellBody_getElem?, hb0]; rfl
    obtain ⟨hh, hsafe, sa1, hst, hr⟩ :=
      img_stepStraight hsep hphys hgate _ hrel hbC hlt hnc' hstep
    have hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
        DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A) := by
      intro B A m hacc hg hBf
      obtain ⟨q, -, hpA⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel
        (accArr_cellBody hN (hasPrefix_gpName hg) hacc) hBf
      exact hpA
    obtain ⟨hcell, he⟩ := stepA_cellBody hF hptr s.zf
    have hwide : WideSafeAt body sa := by
      intro ii ds o ss _ r _ hr _ _
      exact hrel.wid r hr
    exact ⟨by rw [← haltedA_cellBody slotArr]; exact hh,
      ⟨(loadSafeAt_cellBody slotArr rsp body sa).mp hsafe, hwide, hcell⟩, sa1,
      by rw [he]; exact hst, Or.inl hr⟩

/-- **One step of a body with cells and carry chains through its cell body.**
    `ImageAddrCells.cell_stepW` at every instruction, with the step of the image at a
    conditional branch as the hypothesis `ImgStepWCond`. -/
theorem cell_stepW' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (hcond : ImgStepWCond frame slotArr base rsp (cellBody slotArr body) fn)
    {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa s.zf) {bi : Linstr}
    (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t) :
    haltedA body sa = false ∧ SafeW rsp body sa
      ∧ ∃ sa1, stepA frame body sa s.zf = some (sa1, t.zf)
        ∧ (ImgRelW frame slotArr base (cellBody slotArr body) t sa1 t.zf
          ∨ (haltedA body sa1 = false ∧ SafeW rsp body sa1
            ∧ ∃ sa2, stepA frame body sa1 t.zf = some (sa2, t.zf)
              ∧ ImgRelW frame slotArr base (cellBody slotArr body) t sa2 t.zf)) := by
  rw [cellBody_getElem?] at hb
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  by_cases hcnd : ∃ cc l, b0.li_i = .Lcond cc l
  · obtain ⟨cc, l, hx⟩ := hcnd
    rw [cellMove_lcond slotArr body _ hx] at hstep
    exact cell_cond hcond hrel hb0 hx hlt hstep
  · have hnc' : ∀ cc l, (cellMove slotArr body sa.reg.lpc b0).li_i ≠ .Lcond cc l :=
      fun cc l he => hcnd ⟨cc, l, lcond_of_cellMove he⟩
    have hbC : (cellBody slotArr body)[sa.reg.lpc]?
        = some (cellMove slotArr body sa.reg.lpc b0) := by
      rw [cellBody_getElem?, hb0]; rfl
    obtain ⟨hh, hsafe, sa1, hst, hr⟩ :=
      img_stepW hsep hphys hgate _ hrel hbC hlt hnc' hstep
    have hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
        DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A) := by
      intro B A m hacc hg hBf
      obtain ⟨q, -, hpA⟩ := ptr_of_reloadW hsep hgate hrel
        (accArr_cellBody hN (hasPrefix_gpName hg) hacc) hBf
      exact hpA
    obtain ⟨hcell, he⟩ := stepA_cellBody hF hptr s.zf
    exact ⟨by rw [← haltedA_cellBody slotArr]; exact hh,
      ⟨(loadSafeAt_cellBody slotArr rsp body sa).mp hsafe,
        wideSafe_cellBody hsep hgate hN hF hrel, hcell⟩, sa1,
      by rw [he]; exact hst, Or.inl hr⟩

/-! ## 4. The run of a body with cells -/

/-- **A run of the address machine from steps.** Let every checked step of the program `P`
    from a state related by `R` to an address state be matched by one or two steps of the
    address machine on `body` that re-establish `R`, from states that are not halted and are
    safe in the sense of `SafeW`, and let the address machine have halted where `P` has no
    instruction. Then a halting checked run of `P` is matched by a halting, safe run of the
    address machine that ends in related states. -/
theorem runA_of_steps {frame : String → Option (BitVec 64)} {rsp : BitVec 64} {body : Lcmd}
    {P : LprogM} {R : LstateMF → LstateA → Bool → Prop}
    (hhalt : ∀ s sa zf, R s sa zf → findInstrMem P s.prog = none → haltedA body sa = true)
    (hstep : ∀ s t sa zf i, R s sa zf → findInstrMem P s.prog = some i →
      evalInstrPMemFk true P i s = some t →
      haltedA body sa = false ∧ SafeW rsp body sa
        ∧ ∃ sa1 z1, stepA frame body sa zf = some (sa1, z1)
          ∧ (R t sa1 z1
            ∨ (haltedA body sa1 = false ∧ SafeW rsp body sa1
              ∧ ∃ sa2 z2, stepA frame body sa1 z1 = some (sa2, z2) ∧ R t sa2 z2))) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), R s sa zf →
      lsemFuelMemFk true P fuel s = some t →
      ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf') ∧ R t sa' zf'
        ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hrel hrun
      cases hf : findInstrMem P s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf (hhalt _ _ _ hrel hf), hrel, trivial⟩
  | succ f ih =>
      intro s t sa zf hrel hrun
      cases hf : findInstrMem P s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf (hhalt _ _ _ hrel hf), hrel, trivial⟩
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true P i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              obtain ⟨hh, hsafe, sa1, z1, hst1, hcase⟩ := hstep s s1 sa zf i hrel hf he
              rcases hcase with hrel1 | ⟨hh1, hsafe1, sa2, z2, hst2, hrel2⟩
              · obtain ⟨f', sa', zf', hr', hrel', hsafe'⟩ := ih s1 t sa1 z1 hrel1 hrun
                refine ⟨f' + 1, sa', zf', ?_, hrel', hsafe, fun s' zf'' hs' => ?_⟩
                · rw [runA_step frame body f' sa zf hh, hst1]
                  exact hr'
                · rw [hst1] at hs'
                  cases hs'
                  exact hsafe'
              · obtain ⟨f', sa', zf', hr', hrel', hsafe'⟩ := ih s1 t sa2 z2 hrel2 hrun
                refine ⟨f' + 2, sa', zf', ?_, hrel', hsafe, fun s' zf'' hs' => ?_⟩
                · rw [runA_step frame body (f' + 1) sa zf hh, hst1]
                  simp only [Option.bind_some]
                  rw [runA_step frame body f' sa1 z1 hh1, hst2]
                  exact hr'
                · rw [hst1] at hs'
                  cases hs'
                  refine ⟨hsafe1, fun s'' z'' hs'' => ?_⟩
                  rw [hst2] at hs''
                  cases hs''
                  exact hsafe'

/-- **The image of the cell body simulated on the body.** `ImageAddrCells.image_addr_simB`
    for a body with labels and conditional branches. -/
theorem image_addr_simB' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool)
    (hfn : s.prog.lfn = fn)
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) s sa zf)
    (hrun : lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      fuel s = some t) :
    ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
      ∧ ImgRel frame slotArr base (cellBody slotArr body) t sa' zf'
      ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf := by
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps (frame := frame) (rsp := rsp)
    (body := body) (P := singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
    (R := fun s sa zf => s.prog.lfn = fn
      ∧ ImgRel frame slotArr base (cellBody slotArr body) s sa zf)
    (fun s sa zf h hf => by
      have hh := haltedA_of_img (.of_imgGateB hgate) fn h.1 h.2.pc hf
      rwa [haltedA_cellBody] at hh)
    (fun s s1 sa zf i h hf he => by
      obtain ⟨hfn, hrel⟩ := h
      have hlfn : s1.prog.lfn = fn :=
        (evalInstrPMemF_next _ i s s1 (JasminLsemMemChecked.evalInstrPMemF_of_k he)).1.trans hfn
      have hz := hrel.zf
      subst hz
      rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
        List.getElem?_dropLast] at hf
      split at hf
      case isFalse => cases hf
      rename_i hlt
      obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
      obtain ⟨hh, hsafe, sa1, hst, hc⟩ := cell_step' hsep hphys hgate hN hF fn hrel hb hlt he
      refine ⟨hh, hsafe, sa1, s1.zf, hst, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · exact Or.inr ⟨hh1, hsafe1, sa2, s1.zf, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3⟩

/-- **The image of the cell body simulated on the body, with carry chains.**
    `ImageAddrCells.image_addr_simBW` for a body with labels and conditional branches, with
    the step of the image at a conditional branch as the hypothesis `ImgStepWCond`. -/
theorem image_addr_simBW' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (hcond : ImgStepWCond frame slotArr base rsp (cellBody slotArr body) fn)
    (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool) (hfn : s.prog.lfn = fn)
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa zf)
    (hrun : lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      fuel s = some t) :
    ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
      ∧ ImgRelW frame slotArr base (cellBody slotArr body) t sa' zf'
      ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf := by
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps (frame := frame) (rsp := rsp)
    (body := body) (P := singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
    (R := fun s sa zf => s.prog.lfn = fn
      ∧ ImgRelW frame slotArr base (cellBody slotArr body) s sa zf)
    (fun s sa zf h hf => by
      have hh := haltedA_of_imgW hgate fn h.1 h.2.pc hf
      rwa [haltedA_cellBody] at hh)
    (fun s s1 sa zf i h hf he => by
      obtain ⟨hfn, hrel⟩ := h
      have hlfn : s1.prog.lfn = fn :=
        (evalInstrPMemF_next _ i s s1 (JasminLsemMemChecked.evalInstrPMemF_of_k he)).1.trans hfn
      have hz := hrel.zf
      subst hz
      rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
        List.getElem?_dropLast] at hf
      split at hf
      case isFalse => cases hf
      rename_i hlt
      obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
      obtain ⟨hh, hsafe, sa1, hst, hc⟩ :=
        cell_stepW' hsep hphys hgate hN hF fn hcond hrel hb hlt he
      refine ⟨hh, hsafe, sa1, s1.zf, hst, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · exact Or.inr ⟨hh1, hsafe1, sa2, s1.zf, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3⟩

/-! ## 5. A virtual body on the decoded bytes of a body with cells -/

/-- **A virtual body on the decoded bytes of a body with cells, labels and conditional
    branches.** `ImageAddrCells.virt_bytesC` without the restriction to straight bodies, with
    the step of the image with carry chains at a conditional branch as the hypothesis
    `ImgStepWCond`. -/
theorem virt_bytesC' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {sa : AState} {outs : List String} {B : List LinstrRM}
    (hck : ownedCheckMC outs B (virtImg slotArr (cellBody slotArr body)) = true)
    (hpr : printedAddrWB body = true)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : (imgGateB frame slotArr (cellBody slotArr body)
      || (imgGateBW frame slotArr (cellBody slotArr body)
        && ImageAddrSimW.retOutsB frame (cellBody slotArr body) outs)) = true)
    (hsep : ImgSep frame slotArr base (frameRsp body sa))
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base (frameRsp body sa) body)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = frameP (Params.ofBody body) (frameRsp body sa) q)
    (fn : String)
    (hcond : ImgStepWCond frame slotArr base (frameRsp body sa) (cellBody slotArr body) fn)
    (b t : LstateMF) (hfn : b.prog.lfn = fn) (hbpc : b.prog.base.reg.lpc = 0)
    (s : LstateA) (zf : Bool)
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) b s zf)
    (hpc : s.reg.lpc = 0)
    (hent : ∀ R, DecodePrinted.gpOk R = true →
      s.reg.getW R 64 = some (sa.regs (DecodePrinted.phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel b = some t)
    (hok : RunIdxOk (singletonProgM fn B) fuel b) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∀ r a, r ∈ outs → frame r = some a → Disjoint8 (redW (frameRsp body sa)) a →
        t.prog.base.reg.lvm r = ⟨64, read64 sa'.mem a⟩ := by
  have hck' := lsemFuelMemFk_of_runIdxOk true _ fuel b t hrun hok
  obtain ⟨f', t', hr', hobs⟩ := ownedCheckMC_sound hck fn b t hfn hbpc fuel hck'
  have hsim : ∃ fA sA zA, runA frame body fA s zf = some (sA, zA)
      ∧ (∀ q a, q ∈ outs → frame q = some a → t'.prog.base.reg.lvm q = ⟨64, read64 sA.mem a⟩)
      ∧ RunSafe frame body (SafeW (frameRsp body sa) body) fA s zf := by
    rcases Bool.or_eq_true_iff.mp hgate with hg | hg
    · obtain ⟨fA, sA, zA, h1, h2, h3⟩ :=
        image_addr_simB' hsep hphys hg hN hF fn f' b t' s zf hfn hrel hr'
      exact ⟨fA, sA, zA, h1, fun q a _ ha => h2.slots q a ha, h3⟩
    · obtain ⟨hg, hro⟩ := Bool.and_eq_true_iff.mp hg
      obtain ⟨fA, sA, zA, h1, h2, h3⟩ :=
        image_addr_simBW' hsep hphys hg hN hF fn hcond f' b t' s zf hfn
          (ImageAddrSimW.imgRelW_of hrel) hr'
      have hh : haltedA (cellBody slotArr body) sA = true := by
        rw [haltedA_cellBody]
        exact JasminLsemAddrRun.haltedA_of_runA frame body fA s zf (sA, zA) h1
      exact ⟨fA, sA, zA, h1, fun q a hq ha => (h2.slots q a ha).word
        (ImageAddrSimW.not_mem_oneBitAt_of_halted hg hh
          (ImageAddrSimW.not_mem_of_retOutsB hro hq)), h3⟩
  obtain ⟨fA, sA, zA, hrA, hslots, hsafe⟩ := hsim
  rw [runA_congr hfr] at hrA
  rw [runSafe_congr hfr] at hsafe
  obtain ⟨prog, sa', hdec, hh, -, -, hm'⟩ :=
    printedAddr_simW body hpr sa s zf hpc (fun R hR => Or.inl (hent R hR)) hmem fA (sA, zA) hrA
      hsafe
  refine ⟨prog, sa', hdec, hh, fun r a hr ha hd => ?_⟩
  rw [← hobs.1 r hr, hslots r a hr ha, read64_eq_of_agree hm' hd]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop
