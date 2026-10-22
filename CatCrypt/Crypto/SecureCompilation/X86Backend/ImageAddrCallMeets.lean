/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract

@[expose] public section

set_option autoImplicit false

/-!
# The image relation across a linked call, by the frame rule of the contract

`ImageAddrCall.call_reestablishes` re-establishes `ImageAddrSim.ImgRel` and
`DecodePrintedAddr.ACorr` after a callee given by a `Callee.CalleeSpec`, from the hypothesis
`ImageCallProbe.FootClear` that the frame words and the array words lie outside the footprint
of the callee and the return word. For a run relation `X` that meets the contract of a
linked function `l` (`SContract X l.contract`), the same conclusion follows from the frame
rule `SContract.frame` with the frame `callerFrameA` of the caller.

## The frame of the caller

`callerFrameA frame slotArr base passed K` owns the frame words, the cells of the slot arrays
whose names are outside `passed`, and the registers of `K`: the frame words and the cells are
each pairwise separated and separated from each other, as in `X86.imgSepA`. It owns no
red-zone word, and no cell of an array of `passed`, the arrays whose regions the callee
reads.

## Main definitions

* `cellLocsOff`, `callerCells`: the cells of the slot arrays outside a set of names.
* `callerFrameA`: the frame of the caller at a linked call.

## Main results

* `callerFrameA_holds`: the frame of the caller holds under `ImgSep`.
* `mem_contractPre_fp`: the locations of the precondition of the contract.
* `callerFrameA_sep_pre`: under `ImageAddrCall.CallerSep` at the frame size of `l`, the
  precondition of the contract and the frame of the caller are separated at the entry state
  of the call.
* `call_reestablishes_meets`: after every run of `X` from the framed
  precondition, `ACorr` and `ImgRel` hold for the summary step, and the framed
  postcondition holds at the return state of the callee.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpFacts evalInstrA_leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
  (retWord entryOf entryOf_regs entryOf_mem retOps_eq CallOut outOf memAfter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (retOps)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState InRange8)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax (LinkedFn)
open Footprinted SAssert

/-! ## 1. The frame of the caller -/

/-- The locations of the cell `c` of a slot array whose name is outside `passed`. -/
def cellLocsOff (slotArr : String → Option (String × Nat)) (base : String → BitVec 64)
    (passed : Set String) (c : String × Nat) : Set Loc :=
  {l | c.1 ∉ passed ∧ l ∈ cellLocs slotArr base c}

/-- The cells of the slot arrays whose names are outside `passed`, owned and pairwise
    separated. -/
def callerCells (slotArr : String → Option (String × Nat)) (base : String → BitVec 64)
    (passed : Set String) : SAssert AState Loc :=
  iSep fun c => own (cellLocsOff slotArr base passed c)

/-- **The frame of the caller at a linked call**: the frame words, the cells of the slot
    arrays whose names are outside `passed`, and the registers of `K`, separated. -/
def callerFrameA (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (passed K : Set String) : SAssert AState Loc :=
  imgFrames frame ∗ callerCells slotArr base passed ∗ own (Loc.reg '' K)

/-- A location of the frame words is a byte of a frame word. -/
theorem mem_imgFrames_fp {frame : String → Option (BitVec 64)} {x : Loc}
    (h : x ∈ (imgFrames frame).fp) :
    ∃ q a y, frame q = some a ∧ InRange8 a y ∧ x = Loc.mem y := by
  simp only [imgFrames, fp_iSep, fp_own, Set.mem_iUnion] at h
  obtain ⟨q, hq⟩ := h
  cases ha : frame q with
  | none => simp [ha, optWordLocs] at hq
  | some a =>
    simp only [ha, optWordLocs, wordLocs, Set.mem_image] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨q, a, y, ha, hy, rfl⟩

/-- A location of the cells outside `passed` is a byte of a cell of an array outside
    `passed`. -/
theorem mem_callerCells_fp {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {passed : Set String} {x : Loc}
    (h : x ∈ (callerCells slotArr base passed).fp) :
    ∃ q A n j y, slotArr q = some (A, n) ∧ j < n ∧ A ∉ passed
      ∧ InRange8 (cellAt (base A) j) y ∧ x = Loc.mem y := by
  simp only [callerCells, fp_iSep, fp_own, Set.mem_iUnion] at h
  obtain ⟨⟨A, j⟩, hA, ⟨q, n, hq, hj⟩, hx⟩ := h
  simp only [wordLocs, Set.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨q, A, n, j, y, hq, hj, hA, hy, rfl⟩

/-- **The locations of the frame of the caller**: a byte of a frame word, a byte of a cell
    of an array outside `passed`, or a register of `K`. -/
theorem mem_callerFrameA_fp {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64}
    {passed K : Set String} {x : Loc} (h : x ∈ (callerFrameA frame slotArr base passed K).fp) :
    (∃ q a y, frame q = some a ∧ InRange8 a y ∧ x = Loc.mem y)
      ∨ (∃ q A n j y, slotArr q = some (A, n) ∧ j < n ∧ A ∉ passed
          ∧ InRange8 (cellAt (base A) j) y ∧ x = Loc.mem y)
      ∨ ∃ r ∈ K, x = Loc.reg r := by
  rcases h with h | h | ⟨r, hr, rfl⟩
  · exact Or.inl (mem_imgFrames_fp h)
  · exact Or.inr (Or.inl (mem_callerCells_fp h))
  · exact Or.inr (Or.inr ⟨r, hr, rfl⟩)

/-- **The frame of the caller holds under `ImgSep`**, at every state. -/
theorem callerFrameA_holds {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep frame slotArr base rsp) (passed K : Set String) (s : AState) :
    (callerFrameA frame slotArr base passed K).holds s := by
  have h := (imgSep_iff_sep frame slotArr base rsp s).1 hsep
  have hcf : Disjoint (⋃ c, cellLocs slotArr base c) (⋃ q, optWordLocs (frame q)) :=
    h.2.2.1.mono_right Set.subset_union_left
  have hsub : ∀ c, cellLocsOff slotArr base passed c ⊆ cellLocs slotArr base c :=
    fun _ _ hl => hl.2
  refine ⟨?_, h.2.2.2.2.1, ?_, ⟨fun i j hij => ?_, fun _ => trivial⟩, trivial⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨q, a, y, ha, hy, rfl⟩ := mem_imgFrames_fp hx
    rcases hx' with hx' | ⟨r, -, hr⟩
    · exact Set.disjoint_left.1 hcf (Set.iUnion_mono hsub hx') hx
    · cases hr
  · rw [Set.disjoint_left]
    rintro x hx ⟨r, -, hr⟩
    obtain ⟨q, A, n, j, y, -, -, -, -, rfl⟩ := mem_callerCells_fp hx
    cases hr
  · exact (h.2.2.2.1.1 i j hij).mono (hsub i) (hsub j)

/-! ## 2. The locations of the precondition -/

/-- The locations of the pointer regions owned by the precondition are the locations of the
    regions. -/
theorem regionsOwn_fp_subset (σ : Haxc.AbiLayout) (rv : String → BitVec 64) :
    (regionsOwn σ rv).fp ⊆ regionLocs σ rv := by
  have hc : ∀ L : List (String × Nat), (∀ p ∈ L, p ∈ σ.regions) →
      ((L.map fun p => arrOwn (rv p.1) p.2).foldr conj emp).fp ⊆ regionLocs σ rv := by
    intro L hL
    induction L with
    | nil => intro x hx; exact absurd hx (Set.notMem_empty x)
    | cons p L ih =>
      rintro x (hx | hx)
      · exact Set.mem_biUnion (hL p List.mem_cons_self) hx
      · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hx
  rintro x (hx | hx)
  · exact hc _ (fun p hp => (List.mem_filter.1 hp).1) hx
  · obtain ⟨P, hP, hx⟩ := mem_fp_bigSep.1 hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hP
    exact Set.mem_biUnion (List.mem_filter.1 hp).1 hx

/-- **The locations of the precondition of the contract**: the registers of the layout, the
    scratch registers, the flags, the return word, the `frame` bytes below the stack register,
    and the locations the callee reads: the pointer regions, the stack parameters and the
    result. -/
theorem mem_contractPre_fp {l : LinkedFn} {a : CallVar} {x : Loc}
    (h : x ∈ (l.contractPre a).fp) :
    x ∈ (regsAt (abiRegs l.layout) a.rv).fp ∨ x ∈ l.scratch ∨ x ∈ flagLocs
      ∨ x ∈ (retAt a.sp a.ret).fp ∨ x ∈ stackRoom a.sp l.frame
      ∨ x ∈ regionLocs l.layout a.rv ∪ (stackAt l.layout a.rv).fp
          ∪ resLocs (entryRegs a.rv) l.layout.result := by
  rcases h with ((h | (h | h) | h | h | h | h) | h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
      (regionsOwn_fp_subset _ _ h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact absurd h (Set.notMem_empty x)

/-- The stack register at the entry of a call from a state with stack register `rsp`. -/
theorem sp_of_pre {l : LinkedFn} {a : CallVar} {sA : AState} {ret : Nat}
    (hpre : (l.contractPre a).holds (entryOf ret sA)) : retWord sA = a.sp := by
  rw [← (holds_entryAt (entryAt_of_pre hpre)).2.1, entryOf_regs, if_pos rfl]

/-! ## 3. The separation of the precondition and the frame of the caller -/

/-- **The precondition and the frame of the caller are separated at the entry of a call.**
    Let the frame words lie above the stack register `rsp` of the caller and the cells of the
    slot arrays avoid the return word and the `frame` bytes of `l` below it
    (`CallerSep` at `l.frame`), the registers of `K` be outside the registers of the layout
    and the clobbered registers of `l`, and the frame of the caller be disjoint from the
    locations the callee reads: its pointer regions, its stack parameters and its result.
    Then at the entry state of a call that satisfies the precondition of the contract, the
    precondition and the frame of the caller hold separated. -/
theorem callerFrameA_sep_pre {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep frame slotArr base rsp) {l : LinkedFn}
    (hS : CallerSep frame slotArr base rsp l.frame) {passed K : Set String}
    (hK : ∀ r ∈ K, r ∉ abiRegs l.layout ∧ r ∉ l.clob) {a : CallVar}
    (hext : Disjoint (callerFrameA frame slotArr base passed K).fp
      (regionLocs l.layout a.rv ∪ (stackAt l.layout a.rv).fp
        ∪ resLocs (entryRegs a.rv) l.layout.result))
    {sA : AState} (hsp : sA.regs "%rsp" = rsp) (ret : Nat)
    (hpre : (l.contractPre a).holds (entryOf ret sA)) :
    (l.contractPre a ∗ callerFrameA frame slotArr base passed K).holds (entryOf ret sA) := by
  have hra : a.sp = rsp + BitVec.ofInt 64 (-8) := by
    rw [← sp_of_pre hpre, retWord, hsp]
  refine ⟨Set.disjoint_left.2 fun x hx hR => ?_, hpre, callerFrameA_holds hsep passed K _⟩
  rcases mem_contractPre_fp hx with h | h | h | h | h | h
  · obtain ⟨r, hr, rfl⟩ := h
    rcases mem_callerFrameA_fp hR with ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ |
      ⟨r', hr', he⟩
    · cases he
    · cases he
    · cases he
      exact (hK r hr').1 hr
  · obtain ⟨r, ⟨hc, -⟩, rfl⟩ := h
    rcases mem_callerFrameA_fp hR with ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ |
      ⟨r', hr', he⟩
    · cases he
    · cases he
    · cases he
      exact (hK r hr').2 hc
  · obtain ⟨f, rfl⟩ := h
    rcases mem_callerFrameA_fp hR with ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ |
      ⟨_, _, he⟩ <;> cases he
  · obtain ⟨y, hy, rfl⟩ := h
    rw [hra] at hy
    rcases mem_callerFrameA_fp hR with ⟨q, b, z, hb, hz, he⟩ |
      ⟨q, A, n, j, z, hq, hj, -, hz, he⟩ | ⟨_, _, he⟩
    · cases he
      obtain ⟨o, h1, rfl⟩ := hS.frames q b hb
      exact above_not_retWord rsp y o (by omega) hz hy
    · cases he
      exact (hS.cells q A n j hq hj y hz).1 hy
    · cases he
  · obtain ⟨y, hy, rfl⟩ := h
    rw [hra] at hy
    rcases mem_callerFrameA_fp hR with ⟨q, b, z, hb, hz, he⟩ |
      ⟨q, A, n, j, z, hq, hj, -, hz, he⟩ | ⟨_, _, he⟩
    · cases he
      obtain ⟨o, h1, rfl⟩ := hS.frames q b hb
      exact above_not_inFrame rsp y o l.frame h1 hz hy
    · cases he
      exact (hS.cells q A n j hq hj y hz).2 hy
    · cases he
  · exact Set.disjoint_left.1 hext hR h

/-! ## 4. The image relation across a linked call -/

/-- States that agree on a set of locations hold the same byte at a memory location of it. -/
theorem mem_eq_of_agreeOn {S : Set Loc} {s t : AState} (h : AgreeOn S s t) {x : BitVec 64}
    (hx : Loc.mem x ∈ S) : s.mem x = t.mem x :=
  h (.mem x) hx

/-- **The memory after a call outside the write set.** If the run of the callee from the
    entry state of a call to the state `sc` keeps the locations outside a set `W`, then at a
    byte `x` outside `W` and outside the return word, the memory `memAfter` after the return
    holds the byte of the address state before the call. -/
theorem memAfter_of_keep {rsp : BitVec 64} {sA sc : AState} {sa : LstateA} {ret : Nat}
    {W : Set Loc} (hc : ACorr rsp sA sa) (hkeep : AgreeOn Wᶜ (entryOf ret sA) sc)
    (x : BitVec 64) (hw : Loc.mem x ∉ W) (hr : ¬ InRange8 (retWord sA) x) :
    memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x := by
  have h1 : (entryOf ret sA).mem x = sc.mem x := mem_eq_of_agreeOn hkeep hw
  have h2 : (retOps.foldl aMachine.exec sc).mem = sc.mem := by
    rw [retOps_eq]
    exact (evalInstrA_leaFrame sc 8).2
  unfold memAfter
  split_ifs with hred
  · rfl
  · rw [h2, ← h1, entryOf_mem ret sA x hr]
    exact (hc.mem x hred).symm

/-- **A linked call re-establishes the relations, by the frame rule of the contract.** Let the
    image state `s`, the address state `sa` and the byte state `sA` be related by `ImgRel` and
    `ACorr`, the instruction at the program counter be a call in a body of the class
    `physImgB`, and the run relation `X` meet the contract of the linked function `l`.
    Let the entry state of the call satisfy the precondition of the contract separated from
    the frame of the caller, and every cell of an array of `passed` lie in a pointer region of
    the layout outside the locations of the result. Then for every run of `X` and every
    oracle `ω`, after the return: `ACorr` holds for the address state `callAC` with the
    oracle `outOf`; `ImgRel` holds for the summary step with that oracle; and the
    postcondition of the contract separated from the frame of the caller holds at the return
    state of the callee. -/
theorem call_reestablishes_meets {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {l : LinkedFn} {X : CalleeRun} (hX : SContract X l.contract)
    (args : List String) (res : Option String) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt) (ret : Nat)
    {passed K : Set String} {a : CallVar}
    (hpre : (l.contractPre a ∗ callerFrameA frame slotArr base passed K).holds (entryOf ret sA))
    (hpass : ∀ q A n j, slotArr q = some (A, n) → j < n → A ∈ passed →
      ∀ x, InRange8 (cellAt (base A) j) x →
        Loc.mem x ∈ regionLocs l.layout a.rv
          ∧ Loc.mem x ∉ resLocs (entryRegs a.rv) l.layout.result)
    {t : List CTLeak} {sc : AState} (hrun : X (entryOf ret sA) t sc) (ω : CallOut) :
    ACorr rsp (retOps.foldl aMachine.exec sc)
        (callAC (l.contractSig args res) (outOf (retOps.foldl aMachine.exec sc) ω)
          (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa)
      ∧ ImgRel frame slotArr base body
          (callSumC (l.contractSig args res) (outOf (retOps.foldl aMachine.exec sc) ω) s)
          (callAC (l.contractSig args res) (outOf (retOps.foldl aMachine.exec sc) ω)
            (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa) ω.zf
      ∧ (l.contractPost a ∗ callerFrameA frame slotArr base passed K).holds sc := by
  have hC := hX.frame (fun _ => callerFrameA frame slotArr base passed K)
    (fun a _ _ => contractWrites_subset l a) (fun a => contractPost_fp_subset l a)
  have hS := calleeSpec_of_sContract hX args res
  have hpost := hC.post a _ t sc hpre hrun
  have hkeep := hC.keep a _ t sc hpre hrun
  obtain ⟨hsp, -, hk, -, -⟩ := call_return hS ret sA ⟨a, hpre.2.1⟩ hrun
  have hra := sp_of_pre hpre.2.1
  have hmem : ∀ x, Loc.mem x ∉ l.contractWrites a → ¬ InRange8 (retWord sA) x →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x :=
    fun x hw hr => memAfter_of_keep hc hkeep x hw hr
  have hframe : ∀ x, Loc.mem x ∈ (callerFrameA frame slotArr base passed K).fp →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x := by
    intro x hx
    have hnp : Loc.mem x ∉ (l.contractPre a).fp := fun h => Set.disjoint_left.1 hpre.1 h hx
    refine hmem x (fun hw => hnp (contractWrites_subset l a hw)) fun hr => hnp ?_
    rw [hra] at hr
    exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨x, hr, rfl⟩))))
  obtain ⟨⟨-, -, d2, -⟩, -⟩ := entryAt_of_pre hpre.2.1
  refine ⟨acorr_callC _ ω hc hsp fun r hg hcl => hk _ (gpFacts hg).physNe hcl,
    imgRel_callC hsep hphys _ _ hrel hb hbi (fun q b hb x hx => hframe x ?_)
      (fun q' A n j hq' hj x hx => ?_), hpost⟩
  · exact Or.inl (Set.mem_iUnion.2 ⟨q, by simp only [hb, fp_own, optWordLocs]; exact ⟨x, hx, rfl⟩⟩)
  · by_cases hA : A ∈ passed
    · obtain ⟨hin, hnr⟩ := hpass q' A n j hq' hj hA x hx
      have hreg : Loc.mem x ∈ (conj (regionsOwn l.layout a.rv)
          (inputsAt l.layout a.rv a.vals)).fp := Or.inr hin
      refine hmem x ?_ fun hr => ?_
      · rintro (hw | hw)
        · exact Set.disjoint_left.1 d2 hreg (Or.inr (Or.inr (Or.inr ⟨x, hw, rfl⟩)))
        · exact hnr hw
      · rw [hra] at hr
        exact Set.disjoint_left.1 d2 hreg (Or.inl ⟨x, hr, rfl⟩)
    · exact hframe x (Or.inr (Or.inl (Set.mem_iUnion.2 ⟨(A, j), hA, ⟨q', n, hq', hj⟩,
        ⟨x, hx, rfl⟩⟩)))

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets
