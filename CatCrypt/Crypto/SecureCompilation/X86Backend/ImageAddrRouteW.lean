/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL

@[expose] public section

set_option autoImplicit false

/-!
# The image route of a looped program with carry chains and cell accesses

`ImageAddrRoute.routeB` checks the printed body of a looped program against the virtual body
`argBind ++ seeds ++ movesOf ps ++ loop` in the class of printed bodies without carry chains
and without cell accesses. This module gives the route for a printed body whose
constant-index array accesses are cell accesses and whose arithmetic uses carry chains.

The virtual body keeps the prefix `argBind ++ seeds ++ movesOf ps` and replaces the renamed
loop by a cell fold at the cell arrays of the layout under the renaming (`cellArrsR`). The
register allocation check compares it with the image of the cell body of the printed body,
and the image is simulated on the decoded bytes by `ImageAddrCellsLoop.virt_bytesC'`, with
the step at a conditional branch from `ImageAddrSimWCond.img_stepW_cond`. This module holds
the definitions and lemmas of the route that do not depend on the fold; the check of the
route over the fold `CellFoldLReg.cellFoldLR` and its theorem on the decoded bytes are in
`CellFoldLReg`.

## Main definitions

* `cellArrsR`, `baseR`, `frameR`, `slotR`, `entryC`: the cell arrays, entry bases, frame map,
  slot map and virtual entry state of the route under the renaming.
* `cellNamesRB`: the check of the cell names of a list of cell arrays against a printed body.
* `routeBW0`: the check of the route with the fold `cellFoldL` and an empty width analysis at
  every branch. The check of the route, `CellFoldLReg.routeBW`, and the theorem on the
  decoded bytes, `CellFoldLReg.loop_image_bytesW`, are over the fold
  `CellFoldLReg.cellFoldLR`.

## Main results

* `lsemFuelMemF_add`: a halting run of the flag machine is the run at every larger fuel.
* `strip_prefix`: a halting run of `pre ++ X` is a straight run of `pre` followed by a run
  of `X`.
* `ctlOK_of_cellFoldL`: a body with a cell fold, and the fold, are in the class `CtlOK`.
* `keep_run`, `cellRel_movesState`: a straight run of kept instructions and the copies of a
  renaming keep the cell relation.
* `imgSep_cellsU`: `ImageStraightCells.imgSep_cells` at bases read through a name map.
* `cellRel_entryR`, `cellRel_pre`: the cell relation at the entry states and behind the
  prefix of the virtual body.
* `imgStepWCond_of_gate`: the step of the image at a conditional branch from the gate.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM singletonProgM findInstrMem
  IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF evalInstrPMemF
  lsemFuelMemF lsemFuelMemF_halt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF fstepF
  runStraightF_cons runStraightF_lpc lsemFuelMemF_segF isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK shiftS
  lsemFuelMemF_of_prefix lsemFuelMemF_prepend)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf movesState
  runStraightF_movesOf movesOf_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA runStraightF_append)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseOKL fuseLoPre fuseMulHiRM)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64 Disjoint8)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen regK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (rsOK abiBase abiReg
  cells_disjoint frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiEntryM abiEntryM
  abiEntryM_lookup wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW imgGateBW_congr
  retOutsB retOutsB_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond (img_stepW_cond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop (ImgStepWCond virt_bytesC')
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots KEnv isArrB isCellB keepB
  slotsOkB cellsDistinctB CellRel keep_step isCellB_cell isArrB_mem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells

/-! ## 1. Runs of the flag machine -/

/-- **A halting run is the run at every larger fuel.** -/
theorem lsemFuelMemF_add (P : LprogM) : ∀ (fuel : Nat) (s t : LstateMF),
    lsemFuelMemF P fuel s = some t → ∀ k, lsemFuelMemF P (fuel + k) s = some t := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h k
      unfold lsemFuelMemF at h
      cases hf : findInstrMem P s.prog with
      | none =>
          rw [hf] at h
          cases h
          exact lsemFuelMemF_halt P _ s hf
      | some i =>
          rw [hf] at h
          cases h
  | succ n ih =>
      intro s t h k
      rw [Nat.add_right_comm]
      unfold lsemFuelMemF at h ⊢
      cases hf : findInstrMem P s.prog with
      | none =>
          rw [hf] at h
          exact h
      | some i =>
          rw [hf] at h
          dsimp only at h ⊢
          cases he : evalInstrPMemF P i s with
          | none =>
              rw [he] at h
              cases h
          | some u =>
              rw [he] at h
              exact ih u t h k

/-- **The body behind a straight prefix.** A halting run of `pre ++ X` from a base at program
    counter `0` is a straight run of the prefix to a base `b1`, followed by a halting run of
    `X` from `b1` at program counter `0`, with the same fuel, into the final state with the
    program counter moved back by the length of the prefix. -/
theorem strip_prefix (fn : String) (pre X : List LinstrRM) (hpre : ∀ i ∈ pre, IsLopn i)
    (hX : ∀ i ∈ X, CtlOK i) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0) (fuel : Nat)
    (t' : LstateMF)
    (h : lsemFuelMemF (singletonProgM fn (pre ++ X)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t') :
    ∃ b1 z1 t, runStraightF pre b0 zf = some (b1, z1)
      ∧ lsemFuelMemF (singletonProgM fn X) fuel
          { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } = some t
      ∧ t' = shiftS pre.length t := by
  have h' := lsemFuelMemF_add _ fuel _ _ h pre.length
  rw [Nat.add_comm] at h'
  have hseg := lsemFuelMemF_segF (singletonProgM fn (pre ++ X)) fn rfl pre b0 zf fuel hpre
    (fun k hk => by
      simp only [singletonProgM, h0, Nat.zero_add]
      exact List.getElem?_append_left hk)
  rw [hseg] at h'
  obtain ⟨⟨b1, z1⟩, hb1, hrest⟩ := Option.bind_eq_some_iff.mp h'
  have hpc := runStraightF_lpc pre b0 zf b1 z1 hb1
  rw [h0, Nat.zero_add] at hpc
  have hbase : b1 = (b1.setLpc 0).setLpc ((b1.setLpc 0).lpc + pre.length) := by
    rw [JasminLsemMemLoop.LstateM.lpc_setLpc, Nat.zero_add, ← hpc]
    rfl
  have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS pre.length { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } :=
    congrArg (fun b => ({ prog := { base := b, lfn := fn }, zf := z1 } : LstateMF)) hbase
  rw [hsh] at hrest
  obtain ⟨t, ht, rfl⟩ := lsemFuelMemF_of_prefix fn pre X hpre hX fuel _ _ hrest
  exact ⟨b1, z1, t, hb1, ht, rfl⟩

/-! ## 2. The class of a folded body -/

/-- An instruction with a fold, and its fold, are in the class `CtlOK`. -/
theorem ctlOK_of_foldOneL {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (h : foldOneL R env i = some i') : CtlOK i ∧ CtlOK i' := by
  rcases foldOneL_cases h with ⟨h1, h2, -⟩ | ⟨-, hc, rfl⟩
  · exact ⟨Or.inl (isLopnB_isLopn h1), Or.inl (isLopnB_isLopn h2)⟩
  · have hi : CtlOK i' := by
      obtain ⟨w, tg⟩ := i'
      unfold ctlB at hc
      dsimp only at hc
      split at hc
      · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Option.isSome_iff_ne_none.mp hc⟩))
      · cases hc
    exact ⟨hi, hi⟩

/-- **A body with a cell fold, and the fold, are in the class `CtlOK`.** -/
theorem ctlOK_of_cellFoldL {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldL R env is = some is' →
      (∀ i ∈ is, CtlOK i) ∧ (∀ i ∈ is', CtlOK i)
  | [], _, _, hf => by
      cases hf
      exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | i :: is, env, is', hf => by
      unfold cellFoldL at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        obtain ⟨a, b⟩ := ctlOK_of_foldOneL h1
        obtain ⟨c, d⟩ := ctlOK_of_cellFoldL is _ _ h2
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact a
          · exact c j hj
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact b
          · exact d j hj
      · cases hf

/-! ## 3. Straight runs that keep the cell relation -/

/-- **A straight run of kept instructions** from cell-related states is matched by a run into
    cell-related states. -/
theorem keep_run {R : Slots} (hR : slotsOkB R = true) :
    ∀ (is : List LinstrRM), is.all (keepB R) = true →
      ∀ {env : KEnv} {s s' t : LstateM} {zf z : Bool}, CellRel R env s s' →
        runStraightF is s zf = some (t, z) →
        ∃ t', runStraightF is s' zf = some (t', z) ∧ CellRel R [] t t'
  | [], _, env, s, s', t, zf, z, hC, h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨s', rfl, cellRel_nil hC⟩
  | i :: is, hall, env, s, s', t, zf, z, hC, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rw [runStraightF_cons] at h ⊢
      obtain ⟨⟨u, zu⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨u', h1', hCu⟩ := keep_step hR hall.1 hC h1
      rw [h1', Option.bind_some]
      exact keep_run hR is hall.2 hCu h2

/-- A copy between two names that are no cell names keeps the cell relation. -/
theorem cellRel_setReg {R : Slots} {env : KEnv} {s s' : LstateM} (hC : CellRel R env s s')
    {d x : String} (hd : isCellB R d = false) (hx : isCellB R x = false) :
    CellRel R [] ((s.setReg d (s.reg.lvm x).2).nextPc)
      ((s'.setReg d (s'.reg.lvm x).2).nextPc) := by
  have hx' := hC.reg x hx
  refine ⟨fun r hr => ?_, ?_, fun r hr => hC.arr r hr, hC.mem, hC.cf, hC.of, fun p hp => ?_,
    fun y k h => by simp [ImageCellFold.kval] at h⟩
  · simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc]
    split
    · rw [hx']
    · exact hC.reg r hr
  · simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hC.pc]
  · obtain ⟨arr, ha, hc⟩ := hC.cells p hp
    refine ⟨arr, ha, fun j hj => ?_⟩
    have hne : memName p.1 (8 * j) ≠ d := fun he => by
      rw [← he, isCellB_cell hp hj] at hd
      cases hd
    simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, if_neg hne]
    exact hc j hj

/-- **The copies of a renaming keep the cell relation** when no source and no target is a
    cell name. -/
theorem cellRel_movesState {R : Slots} :
    ∀ (ps : List (String × String)) {env : KEnv} {s s' : LstateM}, CellRel R env s s' →
      (∀ p ∈ ps, isCellB R p.1 = false ∧ isCellB R p.2 = false) →
      CellRel R [] (movesState ps s) (movesState ps s')
  | [], _, _, _, hC, _ => cellRel_nil hC
  | p :: ps, _, _, _, hC, h => by
      simp only [movesState]
      exact cellRel_movesState ps
        (cellRel_setReg hC (h p (List.mem_cons_self ..)).2 (h p (List.mem_cons_self ..)).1)
        fun q hq => h q (List.mem_cons_of_mem _ hq)

/-! ## 4. The separation with the cells at bases read through a name map -/

/-- **The separation with the cells, at bases read through a name map.**
    `ImageStraightCells.imgSep_cells` for bases `abiBase (abiReg σ) sa (un A)`: the slot arrays
    and the cell arrays are regions at their lengths under `un`, and a map `ren` undoes `un`
    on their names. -/
theorem imgSep_cellsU {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true) {sa : AState}
    (hreg : σ.Regions sa) {fr : String → Option (BitVec 64)}
    {sl : String → Option (String × Nat)} {rsp : BitVec 64} {R : Slots} {un ren : String → String}
    (hS : ImgSep fr sl (fun A => abiBase (abiReg σ) sa (un A)) rsp)
    (hword : ∀ q a, fr q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o)
    (hsl : ∀ q A n, sl q = some (A, n) → regLen rs (un A) = n)
    (hRlen : ∀ p ∈ R, regLen rs (un p.1) = p.2)
    (hrenR : ∀ p ∈ R, ren (un p.1) = p.1)
    (hrenS : ∀ q A n, sl q = some (A, n) → ren (un A) = A)
    (hgpC : ∀ q, (cellIdx R q).isSome = true → gpOk q = false)
    (hslC : ∀ q A n, sl q = some (A, n) → cellIdx R q = none) :
    ImgSep (frameC (fun A => abiBase (abiReg σ) sa (un A)) R fr) (slotArrC R sl)
      (fun A => abiBase (abiReg σ) sa (un A)) rsp := by
  have hkR : ∀ q A j, cellIdx R q = some (A, j) → regK rs (un A) j := by
    intro q A j h
    obtain ⟨n, hn, hj, -⟩ := cellIdx_spec h
    unfold regK
    rw [hRlen _ hn]
    exact hj
  have hksl : ∀ q A n j, sl q = some (A, n) → j < n → regK rs (un A) j := by
    intro q A n j h hj
    unfold regK
    rw [hsl q A n h]
    exact hj
  have hArr : ∀ q A j, cellIdx R q = some (A, j) → isArrB R A = true := by
    intro q A j h
    obtain ⟨n, hn, -, -⟩ := cellIdx_spec h
    exact isArrB_mem hn
  have hrenC : ∀ q A j, cellIdx R q = some (A, j) → ren (un A) = A := by
    intro q A j h
    obtain ⟨n, hn, -, -⟩ := cellIdx_spec h
    exact hrenR _ hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q q' a a' ha ha' hne
    unfold frameC at ha ha'
    cases hc : cellIdx R q with
    | some Aj =>
        obtain ⟨A, j⟩ := Aj
        rw [hc] at ha
        cases ha
        cases hc' : cellIdx R q' with
        | some Aj' =>
            obtain ⟨A', j'⟩ := Aj'
            rw [hc'] at ha'
            cases ha'
            refine cells_disjoint hrs hreg (hkR q A j hc) (hkR q' A' j' hc') ?_
            rintro ⟨hA, rfl⟩
            have hAA : A = A' := by rw [← hrenC q A j hc, ← hrenC q' A' j hc', hA]
            subst hAA
            obtain ⟨-, -, -, hq⟩ := cellIdx_spec hc
            obtain ⟨-, -, -, hq'⟩ := cellIdx_spec hc'
            exact hne (hq.trans hq'.symm)
        | none =>
            rw [hc'] at ha'
            obtain ⟨o, h1, h2, rfl⟩ := hword q' a' ha'
            exact (frameSep_of_regions hrs hreg (un A) j (hkR q A j hc) o h1 h2).symm
    | none =>
        rw [hc] at ha
        cases hc' : cellIdx R q' with
        | some Aj' =>
            obtain ⟨A', j'⟩ := Aj'
            rw [hc'] at ha'
            cases ha'
            obtain ⟨o, h1, h2, rfl⟩ := hword q a ha
            exact frameSep_of_regions hrs hreg (un A') j' (hkR q' A' j' hc') o h1 h2
        | none =>
            rw [hc'] at ha'
            exact hS.frames q q' a a' ha ha' hne
  · intro q A n j hq hj q' a ha
    obtain ⟨m, hsq, hcase⟩ := slotArrC_some hq
    rcases hcase with ⟨-, rfl⟩ | ⟨hA, rfl⟩
    · exact absurd hj (Nat.not_lt_zero j)
    · unfold frameC at ha
      cases hc : cellIdx R q' with
      | some Aj' =>
          obtain ⟨A', j'⟩ := Aj'
          rw [hc] at ha
          cases ha
          refine cells_disjoint hrs hreg (hksl q A n j hsq hj) (hkR q' A' j' hc) ?_
          rintro ⟨hAA, -⟩
          have hAA' : A = A' := by rw [← hrenS q A n hsq, ← hrenC q' A' j' hc, hAA]
          subst hAA'
          rw [hArr q' A j' hc] at hA
          cases hA
      | none =>
          rw [hc] at ha
          exact hS.cellFrame q A n j hsq hj q' a ha
  · intro q A n q' A' n' j j' hq hq' hj hj' hne
    obtain ⟨m, hsq, hcase⟩ := slotArrC_some hq
    obtain ⟨m', hsq', hcase'⟩ := slotArrC_some hq'
    rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd hj (Nat.not_lt_zero j)
    rcases hcase' with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd hj' (Nat.not_lt_zero j')
    exact hS.cells q A n q' A' n' j j' hsq hsq' hj hj' hne
  · intro q q' A n n' hq hq'
    obtain ⟨m, hsq, hcase⟩ := slotArrC_some hq
    obtain ⟨m', hsq', hcase'⟩ := slotArrC_some hq'
    have hm := hS.len q q' A m m' hsq hsq'
    rcases hcase with ⟨hA, rfl⟩ | ⟨hA, rfl⟩ <;> rcases hcase' with ⟨hA', rfl⟩ | ⟨hA', rfl⟩
    · rfl
    · rw [hA] at hA'; cases hA'
    · rw [hA] at hA'; cases hA'
    · exact hm
  · intro q A n j hq hj
    obtain ⟨m, hsq, hcase⟩ := slotArrC_some hq
    rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd hj (Nat.not_lt_zero j)
    · exact hS.red q A n j hsq hj
  · intro r hr
    unfold frameC
    cases hc : cellIdx R r with
    | some Aj =>
        have := hgpC r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
    | none => exact hS.gp r hr
  · intro q A n hq
    obtain ⟨m, hsq, -⟩ := slotArrC_some hq
    obtain ⟨a, ha⟩ := hS.slotFrame q A m hsq
    refine ⟨a, ?_⟩
    unfold frameC
    rw [hslC q A m hsq]
    exact ha

/-! ## 5. The cell arrays under the renaming -/

/-- The cell arrays of a layout under the renaming `ps`: its word-array parameters under the
    renamed argument names, at their lengths. -/
def cellArrsR (σ : AbiLayout) (ps : List (String × String)) : Slots :=
  (cellArrs σ).map fun p => (renOf ps p.1, p.2)

/-- The entry bases of the renamed array names: the entry value of the register of the
    parameter a name stands for under `unren ps`. -/
abbrev baseR (σ : AbiLayout) (sa : AState) (ps : List (String × String)) : String → BitVec 64 :=
  fun A => abiBase (abiReg σ) sa (unren ps A)

/-- The frame map of the route: the frame words of the printed body and the cells of the
    renamed cell arrays. -/
abbrev frameR (σ : AbiLayout) (sa : AState) (ps : List (String × String)) (body : Lcmd) :
    String → Option (BitVec 64) :=
  frameC (baseR σ sa ps) (cellArrsR σ ps) (frameE body sa)

/-- The slot map of the route: the slots of the array parameters under the renamed names,
    with the cell arrays at length `0`. -/
abbrev slotR (σ : AbiLayout) (nm : String → String) (ps : List (String × String)) :
    String → Option (String × Nat) :=
  slotArrC (cellArrsR σ ps) (slotRen (slotArrOf σ nm) (renOf ps))

/-- The virtual entry state of the route: `entryV` at the frame map with the cells, with the
    cell arrays emptied. -/
abbrev entryC (σ : AbiLayout) (sa : AState) (ps : List (String × String)) (body : Lcmd) :
    LstateM :=
  emptyArrs (cellArrsR σ ps) (entryV σ (frameR σ sa ps body) sa (unren ps))

/-- A word-array parameter is a cell array of the layout. -/
theorem mem_cellArrs {σ : AbiLayout} {j n : Nat} {a : Haxc.AbiArg} (hj : σ.args[j]? = some a)
    (hk : a.kind = .words n) : (argName j, n) ∈ cellArrs σ := by
  unfold cellArrs rsOf
  refine List.mem_map.mpr ⟨⟨argName j, n, 0⟩, List.mem_filterMap.mpr ⟨j, ?_, ?_⟩, rfl⟩
  · exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1
  · simp only [hj, hk]

/-- A cell array under the renaming is the renamed argument name of a word-array
    parameter. -/
theorem cellArrsR_mem {σ : AbiLayout} {ps : List (String × String)} {p : String × Nat}
    (hp : p ∈ cellArrsR σ ps) :
    ∃ j a, σ.args[j]? = some a ∧ a.kind = .words p.2 ∧ p.1 = renOf ps (argName j) := by
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j, a, hj, hk, he⟩ := cellArrs_mem hp0
  exact ⟨j, a, hj, hk, by rw [he]⟩

/-- The check of the cell names of the cell arrays `R` against a printed body: the cell
    arrays are well formed with distinct cells, and no cell name is a general-purpose name, a
    name of the body or an argument name of `σ`. -/
def cellNamesRB (R : Slots) (σ : AbiLayout) (body : Lcmd) : Bool :=
  slotsOkB R && cellsDistinctB R
    && (cellNames R).all fun q => !gpOk q && !(bodyNamesI body).contains q
      && !(List.range σ.args.length).any fun j => argName j == q

/-- The facts the check of the cell names decides. -/
structure CellNamesR (R : Slots) (σ : AbiLayout) (body : Lcmd) : Prop where
  slots : slotsOkB R = true
  dist : cellsDistinctB R = true
  gp : ∀ q, (cellIdx R q).isSome = true → gpOk q = false
  body : ∀ q ∈ bodyNamesI body, cellIdx R q = none
  arg : ∀ j, j < σ.args.length → cellIdx R (argName j) = none

theorem cellNamesRB_spec {R : Slots} {σ : AbiLayout} {body : Lcmd}
    (h : cellNamesRB R σ body = true) : CellNamesR R σ body := by
  simp only [cellNamesRB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h4⟩ := h
  have h4' : ∀ q ∈ cellNames R, gpOk q = false ∧ q ∉ bodyNamesI body
      ∧ ∀ j, j < σ.args.length → argName j ≠ q := by
    intro q hq
    have := h4 q hq
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.any_eq_false, List.mem_range, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨h1, h2, fun q hq => (h4' q (cellIdx_isSome.mp hq)).1, fun q hq => ?_,
    fun j hj => ?_⟩
  · exact cellIdx_none fun hc => (h4' q hc).2.1 hq
  · exact cellIdx_none fun hc => (h4' _ hc).2.2 j hj rfl

/-! ## 6. The cell relation at the entry and behind the prefix -/

/-- **The cell relation at the entry.** The entry state `entryV` at the frame map of the
    printed body and the virtual entry state `entryC` are cell-related at the renamed cell
    arrays, at every program counter, when `unren ps` undoes the renaming on the argument
    names. -/
theorem cellRel_entryR {σ : AbiLayout} {ps : List (String × String)} {body : Lcmd} {sa : AState}
    (hD : cellsDistinctB (cellArrsR σ ps) = true)
    (hunr : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (k : Nat) :
    CellRel (cellArrsR σ ps) []
      { entryV σ (frameE body sa) sa (unren ps) with
        reg := { (entryV σ (frameE body sa) sa (unren ps)).reg with lpc := k } }
      (emptyArrs (cellArrsR σ ps)
        { entryV σ (frameR σ sa ps body) sa (unren ps) with
          reg := { (entryV σ (frameR σ sa ps body) sa (unren ps)).reg with lpc := k } }) := by
  refine ⟨fun r hr => ?_, rfl, fun r hr => ?_, rfl, rfl, rfl, fun p hp => ?_,
    fun x k h => by simp [ImageCellFold.kval] at h⟩
  · rw [isCellB_eq] at hr
    have hn : cellIdx (cellArrsR σ ps) r = none := by
      cases h : cellIdx (cellArrsR σ ps) r with
      | none => rfl
      | some _ => rw [h] at hr; cases hr
    simp [emptyArrs, entryV, frameC, hn]
  · simp [emptyArrs, entryV, hr]
  · obtain ⟨j, a, hj, hk, he⟩ := cellArrsR_mem hp
    have hu := hunr j (List.getElem?_eq_some_iff.mp hj).1
    refine ⟨wordsFn sa (sa.regs a.reg) p.2, ?_, fun i hi => ?_⟩
    · have hl : (entryV σ (frameE body sa) sa (unren ps)).larr p.1
          = ⟨64, p.2, wordsFn sa (sa.regs a.reg) p.2⟩ := by
        simp only [entryV, he, hu, abiEntryM, abiEntryM_lookup hj, hk]
      unfold LstateM.getArr
      show (if h : _ then _ else _) = _
      rw [hl]
      simp
    · have hc := cellIdx_memName hD hp hi
      simp only [emptyArrs, entryV, frameC, hc]
      have hb : baseR σ sa ps (renOf ps (argName j)) = sa.regs a.reg := by
        show abiBase (abiReg σ) sa (unren ps (renOf ps (argName j))) = _
        rw [hu, abiBase_argName hj]
      rw [he, hb]
      rfl

/-- **The cell relation behind the prefix of the virtual body.** A straight run of the copies
    of the parameter registers, the seeds and the copies of the renaming from `entryV` is
    matched by a run from the virtual entry state `entryC` into a cell-related state, when
    the seeds are kept instructions and no source or target of the renaming is a cell name. -/
theorem cellRel_pre {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds : List LinstrRM} {ps : List (String × String)} {sa : AState}
    (E : EntryFacts σ nm (frameE body sa)) (N : CellNamesR (cellArrsR σ ps) σ body)
    (hunr : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j)
    (hkeep : seeds.all (keepB (cellArrsR σ ps)) = true)
    (hps : ∀ p ∈ ps, isCellB (cellArrsR σ ps) p.1 = false ∧ isCellB (cellArrsR σ ps) p.2 = false)
    {b1 : LstateM} {z1 : Bool}
    (h : runStraightF (argBind σ nm ++ seeds ++ movesOf ps)
      (entryV σ (frameE body sa) sa (unren ps)) false = some (b1, z1)) :
    ∃ b1C, runStraightF (argBind σ nm ++ seeds ++ movesOf ps) (entryC σ sa ps body) false
        = some (b1C, z1) ∧ CellRel (cellArrsR σ ps) [] b1 b1C := by
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
  have hfrR : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg
      ∧ frameR σ sa ps body (nm a.reg) = none := by
    intro a ha
    obtain ⟨h1, h2, h3⟩ := E.regs a ha
    refine ⟨h1, h2, ?_⟩
    simp only [frameC, hgpN _ h1]
    exact h3
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (un := unren ps) E.argF E.argG E.regs false
  have hpr0C := runStraightF_argBind_empty (R := cellArrsR σ ps)
    (argBind_entryV (nm := nm) (sa := sa) (un := unren ps) hfrA E.argG hfrR false)
  rw [List.append_assoc, runStraightF_append, hpr0, Option.bind_some, runStraightF_append] at h
  obtain ⟨⟨bs, zs⟩, hs, hm⟩ := Option.bind_eq_some_iff.mp h
  rw [runStraightF_movesOf] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨bsC, hsC, hCs⟩ := keep_run N.slots seeds hkeep
    (cellRel_entryR (body := body) (sa := sa) N.dist hunr σ.args.length) hs
  refine ⟨movesState ps bsC, ?_, cellRel_movesState ps hCs hps⟩
  rw [List.append_assoc, runStraightF_append, hpr0C, Option.bind_some, runStraightF_append, hsC,
    Option.bind_some, runStraightF_movesOf]

/-! ## 7. The checks of the route -/

/-- **The step of the image with carry chains at a conditional branch, from the gate.** -/
theorem imgStepWCond_of_gate {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} (rsp : BitVec 64)
    {c : Lcmd} (hphys : physImgB slotArr c = true) (hgate : imgGateBW frame slotArr c = true)
    (fn : String) : ImgStepWCond frame slotArr base rsp c fn :=
  fun _ _ _ _ _ _ hrel hb hlt hc hstep => (img_stepW_cond hphys hgate fn hrel hb hlt hc hstep).2

/-- The cell names of the array `A` of `m` words. -/
def outCells (A : String) (m : Nat) : List String := (List.range m).map fun j => memName A (8 * j)

/-- **The virtual body of the route**: the copies of the parameter registers, the seeds, the
    copies of the loop-carried names into their renamed names and the folded loop `L2`, with
    its high products fused when `fuse` holds. -/
def virtBW (σ : AbiLayout) (nm : String → String) (seeds : List LinstrRM)
    (ps : List (String × String)) (L2 : List LinstrRM) (fuse : Bool) : List LinstrRM :=
  argBind σ nm ++ seeds ++ movesOf ps ++ if fuse then fuseMulHiRM L2 else L2

/-- **The check of the image route with the fold `cellFoldL` and an empty width analysis at
    every branch** of the node `seeds ++ loop` with the renaming `ps`, the fusion flag `fuse`
    and the output array `out` of `m` words, against the printed body `body`: the conjuncts
    of `CellFoldLReg.routeBW`, with the cell fold `L2` of the renamed loop taken by
    `CellFoldL.cellFoldL`, the gate `ImageAddrSimW.imgGateBW0` and the check
    `ImageAddrSimW.retOutsB0` of the observed names. A program that passes it passes
    `CellFoldLReg.routeBW` (`CellFoldLReg.routeBW_of_old`). -/
def routeBW0 (σ : AbiLayout) (nm : String → String) (body : Lcmd) (seeds loop : List LinstrRM)
    (ps : List (String × String)) (fuse : Bool) (out : String) (m : Nat) : Bool :=
  match cellFoldL (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) with
  | some L2 =>
      ownedCheckMC (outCells (renOf ps out) m) (virtBW σ nm seeds ps L2 fuse)
          (virtImg (slotR σ nm ps) (cellBody (slotR σ nm ps) body))
        && idxInvCheckB (boundFacts σ nm)
          (idxAnnot (boundFacts σ nm) (virtBW σ nm seeds ps L2 fuse)) (virtBW σ nm seeds ps L2 fuse)
        && printedAddrWB body && physImgB (slotR σ nm ps) (cellBody (slotR σ nm ps) body)
        && (ImageAddrSimW.imgGateBW0 (frameMarkC (cellArrsR σ ps) body) (slotR σ nm ps)
            (cellBody (slotR σ nm ps) body)
          && ImageAddrSimW.retOutsB0 (frameMarkC (cellArrsR σ ps) body)
            (cellBody (slotR σ nm ps) body) (outCells (renOf ps out) m))
        && frameOkB σ body && entryB σ nm body && renB σ nm seeds loop ps
        && cellAccB (slotR σ nm ps) (cellArrsR σ ps) body && cellNoSlotB (slotR σ nm ps) body
        && cellNamesRB (cellArrsR σ ps) σ body
        && (cellArrsR σ ps).all (fun p => regLen (rsOf σ) (unren ps p.1) == p.2)
        && seeds.all (keepB (cellArrsR σ ps))
        && ps.all (fun p => !isCellB (cellArrsR σ ps) p.1 && !isCellB (cellArrsR σ ps) p.2)
        && (!fuse || (fuseOKL (fuseRegs σ nm ++ cellNames (cellArrsR σ ps))
            (fuseLoPre (argBind σ nm ++ seeds ++ movesOf ps) L2)
            (argBind σ nm ++ seeds ++ movesOf ps ++ L2)
          && (outCells (renOf ps out) m).all (· != "R15")))
        && (loopNames loop).contains out
  | none => false

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW
