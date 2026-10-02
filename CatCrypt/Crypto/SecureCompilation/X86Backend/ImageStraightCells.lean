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
# The straight route with cell accesses

The frame map and the slot map of the straight image route for a body whose word arrays
are accessed through cells (`ImageAddrCells`): every cell name `memName A (8 j)` of a cell
array `(A, n)` of `R` has the frame word `cellAt (base A) j` (`frameC`), and the cell arrays
enter the slot map with length `0` (`slotArrC`), so that the slot map still names the
pointer slot of each array while no cell of a cell array is an indexed cell.

## Main definitions

* `cellIdx`, `frameC`, `slotArrC`.
* `cellNamesOkB`, `cellRouteB`: the checks of the cell names and of the cell route.
* `straightCellB`: the gate of an array-returning straight-line program through the cell
  route.

## Main results

* `cellIdx_spec`, `cellIdx_memName`: the array and index of a cell name.
* `imgSep_cells`: the separation of the image simulation at `frameC` and `slotArrC`, from
  the separation at the stack frame and the regions of the layout.
* `cellRel_entry`: the cell relation at the entry of the folded chain.
* `cell_route_bytes`: a run of the folded chain on the decoded bytes, with the observed
  cells read back from memory.
* `straight_cell_bytes`: an array-returning program accepted by `straightCellB` at the
  bytes, its result read back by the layout.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB isCellB
  cellsDistinctB cellsDistinct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen regK regLay)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (rsOK abiBase abiReg
  cells_disjoint frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8)

/-! ## 1. Cell names -/

/-- The array and index `(A, j)` of a cell name `memName A (8 j)` of a cell array of `R`. -/
def cellIdx (R : Slots) (q : String) : Option (String × Nat) :=
  R.findSome? fun p => ((List.range p.2).find? fun j => q == memName p.1 (8 * j)).map
    fun j => (p.1, j)

theorem cellIdx_spec {R : Slots} {q A : String} {j : Nat} (h : cellIdx R q = some (A, j)) :
    ∃ n, (A, n) ∈ R ∧ j < n ∧ q = memName A (8 * j) := by
  unfold cellIdx at h
  obtain ⟨p, hp, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨j', hj', he⟩ := Option.map_eq_some_iff.mp hf
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hm := List.mem_of_find?_eq_some hj'
  have hq : q = memName p.1 (8 * j') := by simpa using List.find?_some hj'
  exact ⟨p.2, hp, List.mem_range.mp hm, hq⟩

theorem cellIdx_memName {R : Slots} (hD : cellsDistinctB R = true) {p : String × Nat}
    (hp : p ∈ R) {j : Nat} (hj : j < p.2) : cellIdx R (memName p.1 (8 * j)) = some (p.1, j) := by
  cases hc : cellIdx R (memName p.1 (8 * j)) with
  | none =>
      exfalso
      unfold cellIdx at hc
      rw [List.findSome?_eq_none_iff] at hc
      have := hc p hp
      rw [Option.map_eq_none_iff, List.find?_eq_none] at this
      exact absurd (by simp) (this j (List.mem_range.mpr hj))
  | some Aj =>
      obtain ⟨A, j'⟩ := Aj
      obtain ⟨n, hn, hj', he⟩ := cellIdx_spec hc
      obtain ⟨h1, h2⟩ := cellsDistinct hD hp hn hj hj' he
      rw [h1, h2]

/-! ## 2. The frame and slot maps -/

/-- The frame map with the cells: the cell name `memName A (8 j)` of a cell array has the
    frame word `cellAt (base A) j`; every other name its frame word under `fr`. -/
def frameC (base : String → BitVec 64) (R : Slots) (fr : String → Option (BitVec 64))
    (q : String) : Option (BitVec 64) :=
  match cellIdx R q with
  | some (A, j) => some (cellAt (base A) j)
  | none => fr q

/-- The slot map with the cell arrays at length `0`. -/
def slotArrC (R : Slots) (sl : String → Option (String × Nat)) (q : String) :
    Option (String × Nat) :=
  (sl q).map fun p => if isArrB R p.1 then (p.1, 0) else p

theorem slotArrC_some {R : Slots} {sl : String → Option (String × Nat)} {q A : String}
    {n : Nat} (h : slotArrC R sl q = some (A, n)) :
    ∃ m, sl q = some (A, m) ∧ (isArrB R A = true ∧ n = 0 ∨ isArrB R A = false ∧ n = m) := by
  unfold slotArrC at h
  obtain ⟨⟨A', m⟩, hq, he⟩ := Option.map_eq_some_iff.mp h
  refine ⟨m, ?_, ?_⟩
  · split at he <;> simp_all
  · split at he
    · rename_i hA
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inl ⟨hA, rfl⟩
    · rename_i hA
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨by simpa using hA, rfl⟩

/-! ## 3. The separation with the cells -/

/-- **The separation with the cells.** From the separation at a stack frame whose words lie
    in the frame range of the layout `σ`, a slot map whose arrays are regions of `rs` at their
    lengths, and cell arrays that are regions at their lengths, whose cell names are no
    general-purpose names and no slot names: the separation at `frameC` and `slotArrC`. -/
theorem imgSep_cells {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true) {sa : AState}
    (hreg : σ.Regions sa) {fr : String → Option (BitVec 64)}
    {sl : String → Option (String × Nat)} {rsp : BitVec 64} {R : Slots}
    (hS : ImgSep fr sl (abiBase (abiReg σ) sa) rsp)
    (hword : ∀ q a, fr q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o)
    (hsl : ∀ q A n, sl q = some (A, n) → regLen rs A = n)
    (hRlen : ∀ p ∈ R, regLen rs p.1 = p.2)
    (hgpC : ∀ q, (cellIdx R q).isSome = true → gpOk q = false)
    (hslC : ∀ q A n, sl q = some (A, n) → cellIdx R q = none) :
    ImgSep (frameC (abiBase (abiReg σ) sa) R fr) (slotArrC R sl) (abiBase (abiReg σ) sa) rsp := by
  have hkR : ∀ q A j, cellIdx R q = some (A, j) → regK rs A j := by
    intro q A j h
    obtain ⟨n, hn, hj, -⟩ := cellIdx_spec h
    unfold regK
    rw [hRlen _ hn]
    exact hj
  have hksl : ∀ q A n j, sl q = some (A, n) → j < n → regK rs A j := by
    intro q A n j h hj
    unfold regK
    rw [hsl q A n h]
    exact hj
  have hArr : ∀ q A j, cellIdx R q = some (A, j) → isArrB R A = true := by
    intro q A j h
    obtain ⟨n, hn, -, -⟩ := cellIdx_spec h
    exact ImageCellFold.isArrB_mem hn
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
            rintro ⟨rfl, rfl⟩
            obtain ⟨-, -, -, hq⟩ := cellIdx_spec hc
            obtain ⟨-, -, -, hq'⟩ := cellIdx_spec hc'
            exact hne (hq.trans hq'.symm)
        | none =>
            rw [hc'] at ha'
            obtain ⟨o, h1, h2, rfl⟩ := hword q' a' ha'
            exact (frameSep_of_regions hrs hreg A j (hkR q A j hc) o h1 h2).symm
    | none =>
        rw [hc] at ha
        cases hc' : cellIdx R q' with
        | some Aj' =>
            obtain ⟨A', j'⟩ := Aj'
            rw [hc'] at ha'
            cases ha'
            obtain ⟨o, h1, h2, rfl⟩ := hword q a ha
            exact frameSep_of_regions hrs hreg A' j' (hkR q' A' j' hc') o h1 h2
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
          rintro ⟨rfl, -⟩
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

/-! ## 4. Decided conditions -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellA? CellOp slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (accArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellMove cellBody CellNoSlot)

/-- The cell names of the cell arrays. -/
def cellNames (R : Slots) : List String :=
  R.flatMap fun p => (List.range p.2).map fun j => memName p.1 (8 * j)

theorem cellIdx_isSome {R : Slots} {q : String} :
    (cellIdx R q).isSome = true ↔ q ∈ cellNames R := by
  constructor
  · intro h
    obtain ⟨⟨A, j⟩, hq⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨n, hn, hj, rfl⟩ := cellIdx_spec hq
    exact List.mem_flatMap.mpr ⟨(A, n), hn, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
  · intro h
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    unfold cellIdx
    rw [Option.isSome_iff_exists]
    cases hc : R.findSome? (fun p' => ((List.range p'.2).find? fun j' =>
        memName p.1 (8 * j) == memName p'.1 (8 * j')).map fun j' => (p'.1, j')) with
    | some v => exact ⟨v, rfl⟩
    | none =>
        exfalso
        rw [List.findSome?_eq_none_iff] at hc
        have := hc p hp
        rw [Option.map_eq_none_iff, List.find?_eq_none] at this
        exact absurd (by simp) (this j hj)

/-- No position of the body is a conditional branch. -/
def noCondB (body : Lcmd) : Bool :=
  body.all fun i => match i.li_i with
    | .Lcond _ _ => false
    | _ => true

theorem noCondB_spec {body : Lcmd} (h : noCondB body = true) :
    ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l := by
  intro k bi hb cc l he
  have := List.all_eq_true.mp h bi (List.mem_of_getElem? hb)
  rw [he] at this
  cases this

/-- A decision of `ImageAddrCells.CellNoSlot`. -/
def cellNoSlotB (sl : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i => (cellA? i.li_i).isNone ||
        match slotMov? (cellMove sl body k i).li_i with
        | some (d, q) => (sl d).isNone && (sl q).isNone
        | none => true
    | none => true

theorem cellNoSlotB_spec {sl : String → Option (String × Nat)} {body : Lcmd}
    (h : cellNoSlotB sl body = true) : CellNoSlot sl body := by
  intro k i d q hb hm hc
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [hb] at this
  simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at this
  rcases this with h1 | h1
  · exact absurd h1 hc
  · rw [hm] at h1
    simpa using h1

/-! ## 5. The relation with the cell arrays emptied -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LstateM ArrCell)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgRel)

/-- The state with the array of every cell array of `R` emptied (`64` bits wide, length
    `0`). -/
def emptyArrs (R : Slots) (b : LstateM) : LstateM :=
  { b with larr := fun x => if isArrB R x then ⟨64, 0, Fin.elim0⟩ else b.larr x }

theorem getArr_emptyArrs {R : Slots} {b : LstateM} {A : String} (h : isArrB R A = true) :
    (emptyArrs R b).getArr A 64 0 = some Fin.elim0 := by
  have hc : (emptyArrs R b).larr A = ⟨64, 0, Fin.elim0⟩ := by simp [emptyArrs, h]
  rw [LstateM.getArr, hc]
  simp only [dite_true]

/-- **The relation with the cell arrays at length `0`.** A relation of the image
    simulation at a slot map is one at `slotArrC` from the state with the cell arrays
    emptied. -/
theorem imgRel_cellArrs {frame : String → Option (BitVec 64)}
    {sl : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {R : Slots} {s : LstateMF} {sa : LstateA} {zf : Bool}
    (h : ImgRel frame sl base body s sa zf) :
    ImgRel frame (slotArrC R sl) base body
      { s with prog := { s.prog with base := emptyArrs R s.prog.base } } sa zf := by
  refine ⟨h.pc, h.regs, h.slots, h.zf, h.cf, h.of, h.wid, fun q A n hq => ?_,
    fun k R' A n a hk hA ha => ?_, h.reload⟩
  · obtain ⟨m, hsq, hcase⟩ := slotArrC_some hq
    rcases hcase with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
    · exact ⟨Fin.elim0, getArr_emptyArrs hA, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · obtain ⟨arr, harr, hc⟩ := h.cells q A n hsq
      refine ⟨arr, ?_, hc⟩
      have he : (emptyArrs R s.prog.base).larr A = s.prog.base.larr A := by
        simp [emptyArrs, hA]
      show (emptyArrs R s.prog.base).getArr A 64 n = some arr
      unfold LstateM.getArr
      rw [he]
      exact harr
  · obtain ⟨m, hsq, -⟩ := slotArrC_some hA
    exact h.saved k R' A m a hk hsq ha

/-! ## 6. The entry of the cell fold -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryV entryA rsOf frameE
  abiBase_argName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (afterArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (abiEntryM abiEntryM_lookup
  wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (CellRel)

/-- The cell arrays of a layout: its word-array parameters under their argument names, at
    their lengths. -/
def cellArrs (σ : AbiLayout) : Slots := (rsOf σ).map fun g => (g.name, g.len)

theorem cellArrs_mem {σ : AbiLayout} {p : String × Nat} (hp : p ∈ cellArrs σ) :
    ∃ j a, σ.args[j]? = some a ∧ a.kind = .words p.2 ∧ p.1 = argName j := by
  unfold cellArrs rsOf at hp
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hg
  cases ha : σ.args[j]? with
  | none => rw [ha] at hj; cases hj
  | some a =>
      rw [ha] at hj
      cases hk : a.kind with
      | scalar => simp [hk] at hj
      | words n =>
          simp only [hk, Option.some.injEq] at hj
          subst hj
          exact ⟨j, a, ha, hk, rfl⟩

theorem isCellB_eq {R : Slots} (q : String) : ImageCellFold.isCellB R q = (cellIdx R q).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [cellIdx_isSome]
  constructor
  · intro h
    obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
    obtain ⟨j, hj, he⟩ := List.any_eq_true.mp hq
    have := beq_iff_eq.mp he
    subst this
    exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨j, hj, rfl⟩⟩
  · intro h
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact ImageCellFold.isCellB_cell hp (List.mem_range.mp hj)

/-- The virtual entry of the folded chain: `entryV` at the frame map with the cells, with the
    cell arrays emptied, after the copies of the parameter registers. -/
def afterArgsC (σ : AbiLayout) (body : Lcmd) (sa : AState) (R : Slots) : LstateM :=
  let b0 := entryV σ (frameC (abiBase (abiReg σ) sa) R (frameE body sa)) sa fun x => x
  emptyArrs R { b0 with reg := { b0.reg with lpc := σ.args.length } }

/-- **The cell relation at the entry.** The entry state of the chain and the virtual entry of
    the folded chain are cell-related, for the cell arrays of the layout. -/
theorem cellRel_entry {σ : AbiLayout} {body : Lcmd} {sa : AState}
    (hD : cellsDistinctB (cellArrs σ) = true) :
    CellRel (cellArrs σ) [] (afterArgs σ body sa) (afterArgsC σ body sa (cellArrs σ)) := by
  refine ⟨fun r hr => ?_, rfl, fun r hr => ?_, rfl, rfl, rfl, fun p hp => ?_,
    fun x k h => by simp [ImageCellFold.kval] at h⟩
  · rw [isCellB_eq] at hr
    have hn : cellIdx (cellArrs σ) r = none := by
      cases h : cellIdx (cellArrs σ) r with
      | none => rfl
      | some _ => rw [h] at hr; cases hr
    simp [afterArgsC, afterArgs, emptyArrs, entryV, frameC, hn]
  · simp [afterArgsC, afterArgs, emptyArrs, entryV, hr]
  · obtain ⟨j, a, hj, hk, he⟩ := cellArrs_mem hp
    refine ⟨wordsFn sa (sa.regs a.reg) p.2, ?_, fun i hi => ?_⟩
    · have hl : (afterArgs σ body sa).larr p.1 = ⟨64, p.2, wordsFn sa (sa.regs a.reg) p.2⟩ := by
        simp only [afterArgs, entryV, he, abiEntryM, abiEntryM_lookup hj, hk]
      unfold LstateM.getArr
      rw [hl]
      simp
    · have hc := cellIdx_memName hD hp hi
      simp only [afterArgsC, emptyArrs, entryV, frameC, hc]
      rw [he, abiBase_argName hj]
      rfl

/-! ## 7. The copies of the parameter registers and the cell frames -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind argPairs argBind_entryV)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesState
  runStraightF_movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (CellFrames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW)

theorem movesState_emptyArrs (R : Slots) :
    ∀ (ps : List (String × String)) (b : LstateM),
      movesState ps (emptyArrs R b) = emptyArrs R (movesState ps b)
  | [], _ => rfl
  | p :: ps, b => by
      simp only [movesState]
      rw [← movesState_emptyArrs R ps]
      rfl

theorem runStraightF_argBind_empty {σ : AbiLayout} {nm : String → String} {R : Slots}
    {b c : LstateM} {zf : Bool} (h : runStraightF (argBind σ nm) b zf = some (c, zf)) :
    runStraightF (argBind σ nm) (emptyArrs R b) zf = some (emptyArrs R c, zf) := by
  unfold argBind at h ⊢
  rw [runStraightF_movesOf] at h ⊢
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h
  rw [movesState_emptyArrs, h]

/-- A decision of the cell frames of a body: the base of every cell access, and the stored
    register of every cell store, are general-purpose names; the base is reloaded from the
    slot of an array `A`; the offset is `8 j` with `memName A (8 j)` a cell of `A`. -/
def cellAccB (sl : String → Option (String × Nat)) (R : Slots) (body : Lcmd) : Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i =>
        let arrOk : String → Nat → Bool := fun B off =>
          match accArr sl body k B with
          | some (A, _) => off % 8 == 0 && cellIdx R (memName A off) == some (A, off / 8)
          | none => false
        match cellA? i.li_i with
        | some (.ld _ B off) => gpOk B && arrOk B off
        | some (.st B off S) => gpOk B && gpOk S && arrOk B off
        | none => true
    | none => true

/-- **The cell frames from the decided check.** At the frame map with the cells, the cell
    accesses of a body accepted by `cellAccB` have their arrays and frame words. -/
theorem cellFrames_of {sl : String → Option (String × Nat)} {R : Slots} {body : Lcmd}
    {base : String → BitVec 64} {rsp : BitVec 64} {fr : String → Option (BitVec 64)}
    (h : cellAccB sl R body = true)
    (hgpC : ∀ q, (cellIdx R q).isSome = true → gpOk q = false)
    (hfrgp : ∀ r, gpOk r = true → fr r = none)
    (hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Disjoint8 (redW rsp) (cellAt (base A) j)) :
    CellFrames (frameC base R fr) sl base rsp body := by
  have hgpN : ∀ r, gpOk r = true → frameC base R fr r = none := by
    intro r hr
    unfold frameC
    cases hc : cellIdx R r with
    | some _ =>
        have := hgpC r (by rw [hc]; rfl)
        rw [hr] at this; cases this
    | none => exact hfrgp r hr
  have hcell : ∀ A off, off % 8 = 0 → cellIdx R (memName A off) = some (A, off / 8) →
      frameC base R fr (memName A off) = some (base A + BitVec.ofNat 64 off)
        ∧ Disjoint8 (redW rsp) (base A + BitVec.ofNat 64 off) := by
    intro A off h8 hc
    have hoff : off = 8 * (off / 8) := by omega
    refine ⟨?_, ?_⟩
    · unfold frameC
      rw [hc]
      show some (base A + BitVec.ofNat 64 (8 * (off / 8))) = _
      rw [← hoff]
    · have := hred A (off / 8) (by rw [← hoff]; exact hc)
      show Disjoint8 (redW rsp) (base A + BitVec.ofNat 64 off)
      rw [hoff]
      exact this
  have hat : ∀ k i, body[k]? = some i →
      ((match cellA? i.li_i with
        | some (.ld _ B off) => gpOk B && (match accArr sl body k B with
            | some (A, _) => off % 8 == 0 && cellIdx R (memName A off) == some (A, off / 8)
            | none => false)
        | some (.st B off S) => gpOk B && gpOk S && (match accArr sl body k B with
            | some (A, _) => off % 8 == 0 && cellIdx R (memName A off) == some (A, off / 8)
            | none => false)
        | none => true) = true) := by
    intro k i hb
    have hk : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
    have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    rw [hb] at this
    exact this
  refine ⟨fun k bi D B off hb hc => ?_, fun k bi B off S hb hc => ?_⟩
  · have := hat k bi hb
    rw [hc] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨hB, ha⟩ := this
    cases hacc : accArr sl body k B with
    | none => rw [hacc] at ha; cases ha
    | some An =>
        obtain ⟨A, n⟩ := An
        rw [hacc] at ha
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨h1, h2⟩ := hcell A off (by simpa using ha.1) ha.2
        exact ⟨A, n, rfl, hgpN B hB, h1, h2⟩
  · have := hat k bi hb
    rw [hc] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨hB, hS⟩, ha⟩ := this
    cases hacc : accArr sl body k B with
    | none => rw [hacc] at ha; cases ha
    | some An =>
        obtain ⟨A, n⟩ := An
        rw [hacc] at ha
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        obtain ⟨h1, -⟩ := hcell A off (by simpa using ha.1) ha.2
        exact ⟨A, n, rfl, hgpN B hB, hgpN S hS, h1⟩

/-! ## 8. The names of the cells -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI frameIn frameNames
  frameMark frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (slotsOkB)

/-- The check of the cell names of a layout against a printed body: the cell arrays are
    well formed with distinct cells and are regions at their lengths, and no cell name is a
    general-purpose name, a name of the body or an argument name. -/
def cellNamesOkB (σ : AbiLayout) (body : Lcmd) : Bool :=
  slotsOkB (cellArrs σ) && cellsDistinctB (cellArrs σ)
    && (cellArrs σ).all (fun p => regLen (rsOf σ) p.1 == p.2)
    && (cellNames (cellArrs σ)).all fun q => !gpOk q && !(bodyNamesI body).contains q
      && !(List.range σ.args.length).any fun j => argName j == q

/-- The facts the check of the cell names decides. -/
structure CellNamesOk (σ : AbiLayout) (body : Lcmd) : Prop where
  slots : slotsOkB (cellArrs σ) = true
  dist : cellsDistinctB (cellArrs σ) = true
  len : ∀ p ∈ cellArrs σ, regLen (rsOf σ) p.1 = p.2
  gp : ∀ q, (cellIdx (cellArrs σ) q).isSome = true → gpOk q = false
  body : ∀ q ∈ bodyNamesI body, cellIdx (cellArrs σ) q = none
  arg : ∀ j, j < σ.args.length → cellIdx (cellArrs σ) (argName j) = none

theorem cellIdx_none {R : Slots} {q : String} (h : q ∉ cellNames R) : cellIdx R q = none := by
  cases hc : cellIdx R q with
  | none => rfl
  | some _ => exact absurd (cellIdx_isSome.mp (by rw [hc]; rfl)) h

theorem cellNamesOkB_spec {σ : AbiLayout} {body : Lcmd} (h : cellNamesOkB σ body = true) :
    CellNamesOk σ body := by
  simp only [cellNamesOkB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : ∀ q ∈ cellNames (cellArrs σ), gpOk q = false ∧ q ∉ bodyNamesI body
      ∧ ∀ j, j < σ.args.length → argName j ≠ q := by
    intro q hq
    have := h4 q hq
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.any_eq_false, List.mem_range, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨h1, h2, h3, fun q hq => (h4' q (cellIdx_isSome.mp hq)).1, fun q hq => ?_,
    fun j hj => ?_⟩
  · exact cellIdx_none fun hc => (h4' q hc).2.1 hq
  · exact cellIdx_none fun hc => (h4' _ hc).2.2 j hj rfl

/-! ## 9. The cell route on the decoded bytes -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen slotRen_some
  imgSep_slotRen imgRel_entryV boundFacts_entryV entryB entryB_spec frameE)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (imgGateB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW imgGateBW_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (read64)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (lsemFuelMemF_of_runStraightF)

/-- The frame marks of a body with the cells: a mark at every cell name, and the frame
    marks of the body elsewhere. -/
def frameMarkC (R : Slots) (body : Lcmd) (q : String) : Option (BitVec 64) :=
  match cellIdx R q with
  | some _ => some 0
  | none => frameMark (frameNames body) q

theorem frameC_isSome (base : String → BitVec 64) (R : Slots) (body : Lcmd) (sa : AState)
    (q : String) :
    (frameC base R (frameE body sa) q).isSome = (frameMarkC R body q).isSome := by
  unfold frameC frameMarkC
  cases cellIdx R q with
  | some _ => rfl
  | none => exact (ImageAddrFrame.frameMark_isSome body (frameRsp body sa) q).symm

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM fuseOKL fuseLoPre
  fuseMulHi_lsemFuelMemF_pre)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (fuseRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)

/-- The virtual body of the cell route: the copies of the parameter registers followed by
    the folded chain `C2`, with its high products fused (`fuseMulHiRM`) when `fuse` holds. -/
def cellVirt (σ : AbiLayout) (nm : String → String) (C2 : List LinstrRM) (fuse : Bool) :
    List LinstrRM :=
  argBind σ nm ++ if fuse then fuseMulHiRM C2 else C2

/-- **The check of the cell route** of the folded chain `C2` against the printed body `body`,
    with the observed names `outs` and the fusion flag `fuse`: with the virtual body
    `cellVirt σ nm C2 fuse`, the slot map `slotArrC` of the cell arrays of `σ` and the cell
    body of `body`, the register allocation check of the virtual body against the image of
    the cell body, the bounds invariant of the virtual body, the W class of printed bodies,
    the image class and the gate `imgGateB` or the gate with carry chains `imgGateBW` at the
    frame marks with the cells, the frame and entry checks, the cell frames, no conditional
    branch, no slot name in a cell move, `C2` a list of `Lopn`s, and, when `fuse` holds, the
    fusion check of `argBind σ nm ++ C2` and no observed name `R15`. -/
def cellRouteB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (outs : List String)
    (C2 : List LinstrRM) (fuse : Bool) : Bool :=
  let R := cellArrs σ
  let B := cellVirt σ nm C2 fuse
  let sl := slotArrC R (slotRen (slotArrOf σ nm) fun x => x)
  let body' := cellBody sl body
  ownedCheckMC outs B (virtImg sl body')
    && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
    && printedAddrWB body && physImgB sl body'
    && (imgGateB (frameMarkC R body) sl body' || imgGateBW (frameMarkC R body) sl body')
    && frameOkB σ body && entryB σ nm body
    && cellAccB sl R body && noCondB body && cellNoSlotB sl body && C2.all isLopnB
    && (!fuse || (fuseOKL (fuseRegs σ nm) (fuseLoPre (argBind σ nm) C2) (argBind σ nm ++ C2)
      && outs.all (· != "R15")))

theorem cellRouteB_entryB {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C2 : List LinstrRM} {fuse : Bool}
    (h : cellRouteB σ nm body outs C2 fuse = true) : entryB σ nm body = true := by
  simp only [cellRouteB, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

/-- **The cell route on the decoded bytes.** Let the folded chain `C2` pass `cellRouteB`
    against the printed body `body` with the observed names `outs`, and the cell names of
    `σ` pass `cellNamesOkB`. From every machine state `sa` satisfying `σ.Regions`, a run of
    `C2` from the virtual entry of the folded chain is matched by a halting run of the
    decoded bytes of `body` from `sa`, at the end of which every observed cell name
    `memName A (8 j)` holds the machine word at the cell `j` of the array `A`. -/
theorem cell_route_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C2 : List LinstrRM} {fuse : Bool}
    (hg : cellRouteB σ nm body outs C2 fuse = true)
    (hN : cellNamesOkB σ body = true) (sa : AState) (hreg : σ.Regions sa) (b : LstateM)
    (z : Bool) (hrun : runStraightF C2 (afterArgsC σ body sa (cellArrs σ)) false = some (b, z)) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∀ A j, memName A (8 * j) ∈ outs → cellIdx (cellArrs σ) (memName A (8 * j)) = some (A, j) →
        b.reg.lvm (memName A (8 * j))
          = ⟨64, read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j)⟩ := by
  simp only [cellRouteB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩, hacc⟩, hnc⟩, hns⟩, hlop⟩,
    hfuse⟩ := hg
  have N := cellNamesOkB_spec hN
  have E := entryB_spec hent sa
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
  have hfrR : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ DecodePrinted.phys (nm a.reg) = a.reg
      ∧ frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) (nm a.reg) = none := by
    intro a ha
    obtain ⟨h1, h2, h3⟩ := E.regs a ha
    refine ⟨h1, h2, ?_⟩
    simp only [frameC, hgpN _ h1]
    exact h3
  have hpr0 := ImageAddrRoute.argBind_entryV (nm := nm) (sa := sa) (un := fun x => x) hfrA E.argG
    hfrR false
  have hB : runStraightF (argBind σ nm ++ C2) (emptyArrs (cellArrs σ)
      (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa fun x => x))
      false = some (b, z) := by
    rw [JasminLsemAddrMem.runStraightF_append, runStraightF_argBind_empty hpr0, Option.bind_some]
    exact hrun
  have hl : ∀ i ∈ argBind σ nm ++ C2, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact isLopnB_isLopn (List.all_eq_true.mp hlop i hi)
  have hrun' := lsemFuelMemF_of_runStraightF "" _ hl _ b false z rfl hB
  obtain ⟨fuelB, tB, hrunB, hagB⟩ : ∃ fuelB tB, JasminLsemMemFlagGuard.lsemFuelMemF
      (JasminLsemMemLoop.singletonProgM ""
      (cellVirt σ nm C2 fuse)) fuelB
      { prog := { base := emptyArrs (cellArrs σ) (entryV σ (frameC (abiBase (abiReg σ) sa)
        (cellArrs σ) (frameE body sa)) sa fun x => x), lfn := "" }, zf := false } = some tB
      ∧ ∀ r ∈ outs, tB.prog.base.reg.lvm r = b.reg.lvm r := by
    cases fuse with
    | false => exact ⟨_, _, hrun', fun _ _ => rfl⟩
    | true =>
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
          bne_iff_ne, ne_eq] at hfuse
        have habiC := ImageAddrRoute.entryV_abiEntry (un := fun x => x) (sa := sa) hfrA E.argG fun _ _ => rfl
        have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm) (emptyArrs (cellArrs σ)
            (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa
              fun x => x)) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact e64_of_abiEntryM habiC x hx
          · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
            obtain ⟨h1, -, h3⟩ := hfrR a ha
            simp only [emptyArrs, entryV, h3, ImageAddrRoute.entryA, h1, if_true]
        obtain ⟨f2, t2, -, ht2, hag, -, -⟩ :=
          fuseMulHi_lsemFuelMemF_pre hfuse.1 "" _ _ rfl hE _ hrun'
        exact ⟨f2, t2, ht2, fun r hr => hag.reg r (hfuse.2 r hr)⟩
  have hents := boundFacts_entryV (nm := nm)
    (fr := frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) (un := fun x => x) hreg
    fun b hb => by
      obtain ⟨h1, h2, h3⟩ := E.bnds b hb
      refine ⟨h1, h2, ?_⟩
      simp only [frameC, hgpN _ h1]
      exact h3
  have hok := runIdxOk_of_idxInvCheckB hidx "" _ _ rfl rfl hents _ hrunB
  have hS0 := imgSep_slotRen (ren := fun x => x) (un := fun x => x)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot) fun _ _ _ _ => rfl
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := ImageAddrFrame.frameIn_some ha
    have := ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (fun x => x) q = some (A, n) →
      regLen (rsOf σ) A = n := by
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
      Disjoint8 (redW (frameRsp body sa)) (cellAt (abiBase (abiReg σ) sa A) j) := by
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
      || imgGateBW (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)) = true := by
    rw [ImageAddrFrame.imgGateB_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa), imgGateBW_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa)]
    exact hgate
  have hfr' : ∀ q ∈ bodyNamesI body,
      frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) q
        = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq
    simp only [frameC, N.body q hq]
    show frameIn body _ q = _
    unfold frameIn
    rw [if_pos hq]
  have hrel0 := imgRel_entryV (nm := nm)
    (fr := frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) (sa := sa)
    (body := cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
    (fn := "") (ren := fun x => x) (un := fun x => x)
    (fun a ha => ⟨(E.regs a ha).1, (E.regs a ha).2.1⟩) fun _ _ => rfl
  have hrel := imgRel_cellArrs (R := cellArrs σ) hrel0
  obtain ⟨prog, sa', hdec, hh, hobs⟩ := ImageAddrCells.virt_bytesC
    (base := abiBase (abiReg σ) sa) hck hpr hphys hgate' hsep (cellNoSlotB_spec hns) hF
    (noCondB_spec hnc) hfr' "" _ _ rfl rfl (ImageAddrRoute.entryA σ sa) false hrel rfl
    (fun R' hR => by
      have hl : (ImageAddrRoute.entryA σ sa).reg.lvm R'
          = ⟨64, sa.regs (DecodePrinted.phys R')⟩ := by
        simp only [ImageAddrRoute.entryA, hR, if_true]
      unfold JasminLsemWidthN.LstateN.getW
      rw [hl]
      simp) rfl _ hrunB hok
  refine ⟨prog, sa', hdec, hh, fun A j hA hc => ?_⟩
  rw [← hagB _ hA]
  exact hobs _ _ hA (by simp only [frameC, hc]) (hred A j hc)

/-! ## 10. An array-returning program through the cell route -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (straightOpsMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
  (runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (arrMemNB arrMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (chainAlias coalesceB liveArr
  plainB plainB_sound CoRel lsemStraightMem_coalesce storeAgreesM_lpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryV_abiEntry resultOf_words)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (cellFold runStraightF_cellFold)

/-- **The gate of an array-returning straight-line program through the cell route.** For a
    program returning a word array of `m` words: the fragment `arrMemNB`; with its chain, its
    return name `ret` and the coalescing renaming `ρ` of the chain, the coalescing check, `ρ`
    fixing every array name live at the entry, the coalesced chain `C` plain; the result of
    `σ` the `m` words at the register `RA` of the parameter `ρ ret`, a cell array of `σ` of
    length `m`; the cell names of `σ` checked against `body`; and the cell fold of `C` from the
    empty constant environment some chain `C2` that passes the cell route against `body` with
    the cells of `ρ ret` observed, at the fusion flag `fuse`. -/
def straightCellB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (fuse : Bool) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | Γ, .stackArr 64 m, com =>
      let ch := straightOpsMem Γ.length com Γ.length
      let ret := comRetReg Γ.length argName com Γ.length
      let ρ := chainAlias ch
      let C := ch.map (renRM ρ)
      arrMemNB com && coalesceB ρ ch [ret] && (liveArr ch [ret]).all (fun r => ρ r == r)
        && plainB C
        && (match σ.result with
          | .words RA k => k == m && abiReg σ (ρ ret) == some RA
              && (cellArrs σ).contains (ρ ret, m)
          | _ => false)
        && cellNamesOkB σ body
        && (match cellFold (cellArrs σ) [] C with
          | some C2 =>
              cellRouteB σ nm body ((List.range m).map fun j => memName (ρ ret) (8 * j)) C2
                fuse
          | none => false)
  | _, _, _ => false

/-- A program accepted by `straightCellB` returns a word array. -/
theorem straightCellB_ty {σ : AbiLayout} {nm : String → String} {body : Lcmd} {fuse : Bool}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {c : Com jasminDialect Γ t}
    (h : straightCellB σ nm body fuse c = true) : ∃ m, t = .stackArr 64 m := by
  unfold straightCellB at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- **An array-returning straight-line program at the bytes through the cell route.** For a
    program returning a word array of `m` words that passes `straightCellB` against the
    printed body `body`: from every entry state `sa` satisfying `σ.Regions`, at every
    valuation `V` the layout reads off `sa` (`AbiValOf`), the decoded bytes of `body` halt in
    a state from which `σ` reads back the words of the program's denotation. -/
theorem straight_cell_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd} {fuse : Bool}
    {Γ : Ctxt jasminDialect} {m : Nat} (com : Com jasminDialect Γ (.stackArr 64 m))
    (hg : straightCellB σ nm body fuse com = true) (sa : AState) (V : Ctxt.Valuation Γ)
    (hV : AbiValOf σ sa V) (hreg : σ.Regions sa) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (.array ((List.range m).map fun j =>
          .int (stackGet (com.denote V) j).toNat)) := by
  simp only [straightCellB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨hmem, hco⟩, hfix⟩, hpl⟩, hres⟩, hN⟩, hroute⟩ := hg
  have N := cellNamesOkB_spec hN
  split at hroute
  · rename_i C2 hfold
    have E := entryB_spec (cellRouteB_entryB hroute) sa
    have habi := entryV_abiEntry (un := fun x => x) (sa := sa) E.argF E.argG fun _ _ => rfl
    have hagr := storeAgreesM_lpc σ.args.length (storeAgreesM_of_abi hV habi)
    obtain ⟨b, hrun, -, harr⟩ :=
      (arrMemNB_sound com hmem).straightOps_full rfl le_rfl hagr
    set ch := straightOpsMem Γ.length com Γ.length with hch
    set ret := comRetReg Γ.length argName com Γ.length with hret
    set ρ := chainAlias ch with hρ
    have hR0 : CoRel ρ (liveArr ch [ret]) (afterArgs σ body sa) (afterArgs σ body sa) :=
      ⟨rfl, rfl, rfl, rfl, fun r hr => by
        rw [show ρ r = r from by simpa using (List.all_eq_true.mp hfix) r hr]⟩
    obtain ⟨b', hrun', hR⟩ := lsemStraightMem_coalesce ch [ret] hco hR0 hrun
    obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ (plainB_sound hpl) _ b' false hrun'
    obtain ⟨env', b2, hF2, hCR⟩ :=
      runStraightF_cellFold N.slots N.dist _ [] C2 hfold (cellRel_entry N.dist) hF
    obtain ⟨prog, sa', hdec, hh, hcells⟩ := cell_route_bytes hroute hN sa hreg b2 false hF2
    split at hres
    · rename_i RA k hσ
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hres
      obtain ⟨⟨hk, hA⟩, hmR⟩ := hres
      subst hk
      obtain ⟨arr, h1, h2⟩ := hCR.cells (ρ ret, k) hmR
      have he : arr = com.denote V := by
        have h3 : ({ b' with cf := c, of := o } : LstateM).getArr (ρ ret) 64 k
            = b.getArr ret 64 k := by
          unfold LstateM.getArr
          rw [show ({ b' with cf := c, of := o } : LstateM).larr (ρ ret) = b.larr ret from
            hR.arr ret (List.mem_singleton_self _)]
        rw [h1, harr] at h3
        exact Option.some.inj h3
      have hb : abiBase (abiReg σ) sa (ρ ret) = sa.regs RA := by
        simp [abiBase, hA]
      have hw : ∀ j (hj : j < k), read64 sa'.mem (cellAt (sa.regs RA) j) = arr ⟨j, hj⟩ := by
        intro j hj
        have hc := cellIdx_memName N.dist hmR hj
        have h4 := hcells (ρ ret) j (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) hc
        rw [h2 j hj, hb] at h4
        exact (eq_of_heq (Sigma.mk.inj h4).2).symm
      refine ⟨prog, sa', hdec, hh, ?_⟩
      have hR' := resultOf_words (σ := σ) (sa' := sa') hσ hw
      rw [he] at hR'
      exact hR'
    · cases hres
  · cases hroute

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
