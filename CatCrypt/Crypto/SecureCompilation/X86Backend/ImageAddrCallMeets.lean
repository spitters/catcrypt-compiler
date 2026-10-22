/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOutChain
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
* `callVarOf`, `passedOf`: the logical variables of a call and the arrays it passes.

## Main results

* `callerFrameA_holds`: the frame of the caller holds under `ImgSep`.
* `mem_contractPre_fp`: the locations of the precondition of the contract.
* `callerFrameA_sep_pre`: under `ImageAddrCall.CallerSep` at the frame size of `l`, the
  precondition of the contract and the frame of the caller are separated at the entry state
  of the call.
* `call_reestablishes_meets`: after every run of `X` from the framed
  precondition, `ACorr` and `ImgRel` hold for the summary step, and the framed
  postcondition holds at the return state of the callee.
* `insCallee_of_contract`: a linked function with an `InsLayout` is an `InsCallee` at the
  interface of the contract.
* `entryAt_at_call`, `framedPre_at_call`: at a call site whose operands pass the parameters
  of the layout, the resources of the call hold at the entry state, and the precondition of
  the contract holds there separated from the frame of the caller.
* `call_reestablishes_meets_out`: the call step of an out layout by the frame rule.
* `siteStep_contract_ins`, `siteStep_contract_out`, `haltsC_of_contract_ins`,
  `haltsO_of_contract_ins`, `haltsC_of_contract_out`, `haltsO_of_contract_out`: the site
  steps and the linked run chains for a run relation that meets the contract.
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr read64_eq_of_agree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
  (retWord entryOf entryOf_regs entryOf_mem retOps_eq CallOut outOf memAfter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (retOps)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState InRange8 read64)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax (LinkedFn insVals dec_wordVal)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open CatCrypt.Crypto.SecureCompilation.Haxc (ArgKind stackArgReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpList mem_gpList phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
  (readIns ParamAt readIns_entry OutLayout outSummary)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOut
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOutChain
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

/-! ## 5. The ins reading of the interface of the contract -/

/-- **A linked function with a layout on parameters is a callee on those parameters at the
    interface of the contract**, with the summary `insSummary` and the entry states at which
    the resources of a call hold. -/
theorem insCallee_of_contract {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hL : InsLayout l ins res) :
    InsCallee (l.contractSig (ins.map (·.1)) (some res)) (readIns ins) res (insSummary l ins)
      l.Room where
  res_eq := rfl
  res_gp := hL.res_gp
  res_clob := hL.res_clob
  pre s := by
    rintro ⟨a, ha⟩ hd
    obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt ha
    refine ⟨a, Set.disjoint_empty _, ha, ?_⟩
    change ((l.sem (insVals (ins.map (·.2)) (readIns ins s))).bind
      (dec (.word 64))).isSome = true at hd
    rw [← read_insLayout hL s, hvals] at hd
    exact Option.isSome_of_isSome_bind hd
  post s s' _ := by
    rintro ⟨a, ha, hp⟩
    obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt (entryAt_of_pre ha)
    obtain ⟨v, hv, hR⟩ := hp.2.2.2
    simp only [Haxc.AbiLayout.ResultOf, hL.result, Haxc.ResultKind.read] at hR
    change (l.sem (insVals (ins.map (·.2)) (readIns ins s))).bind (dec (.word 64)) = _
    rw [← read_insLayout hL s, hvals, hv, Option.bind_some, hR]
    exact dec_wordVal _

/-! ## 6. The resources at the entry of a call -/

/-- The logical variables of a call of `l` from `sA` with return index `ret`: the registers at
    the entry state, the values the layout reads there, and `ret`. -/
def callVarOf (l : LinkedFn) (ret : Nat) (sA : AState) : CallVar :=
  ⟨(entryOf ret sA).regs, l.layout.args.map (·.read (entryOf ret sA)), ret⟩

/-- The array names a call passes at the array parameters of `ins`. -/
def passedOf (ins : List (String × ArgKind)) (args : List String) : Set String :=
  {x | ∃ p, (p, x) ∈ ins.zip args ∧ p.2 ≠ .scalar}

/-- An entry of a list related to a second list by `Forall₂` is paired, in the zip of the two
    lists, with a related entry of the second list. -/
theorem exists_mem_zip_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ {a : α}, a ∈ xs →
      ∃ b, (a, b) ∈ xs.zip ys ∧ R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons (a := a') (b := b') hab hrest, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨b', List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := exists_mem_zip_of_forall₂ hrest h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- The register of a pointer region of a parameter is the register of the parameter. -/
theorem fst_of_mem_region {a : Haxc.AbiArg} {b : String × Nat} (h : b ∈ a.region) :
    b.1 = a.reg := by
  unfold Haxc.AbiArg.region at h
  split at h
  · simp at h
  · simp only [Option.mem_def, Option.some.injEq] at h
    subst h
    rfl

/-- Under parameter registers without repetition, distinct pointer regions of a layout have
    distinct registers. -/
theorem regions_pairwise {σ : Haxc.AbiLayout} (hnd : (σ.args.map (·.reg)).Nodup) :
    σ.regions.Pairwise fun p p' => p.1 ≠ p'.1 := by
  unfold Haxc.AbiLayout.regions
  rw [List.pairwise_filterMap]
  refine (List.pairwise_map.1 hnd).imp fun hne b hb b' hb' => ?_
  rw [fst_of_mem_region hb, fst_of_mem_region hb']
  exact hne

/-- Under parameter registers without repetition, a register has at most one pointer
    region. -/
theorem eq_of_mem_regions {σ : Haxc.AbiLayout} (hnd : (σ.args.map (·.reg)).Nodup)
    {r : String} {m m' : Nat} (h : (r, m) ∈ σ.regions) (h' : (r, m') ∈ σ.regions) :
    m = m' := by
  by_contra hne
  have : Std.Symm (fun p p' : String × Nat => p.1 ≠ p'.1) := ⟨fun _ _ e => Ne.symm e⟩
  exact (regions_pairwise hnd).forall h h' (by simp [hne]) rfl

/-- **The parameter of a pointer region.** Under a layout whose parameters are those of
    `ins` in the registers of their names, a pointer region of the layout is the register of
    an array parameter of `ins` with its length. -/
theorem exists_ins_of_mem_regions {l : LinkedFn} {ins : List (String × ArgKind)}
    (hargs : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2))
    {r : String} {m : Nat} (h : (r, m) ∈ l.layout.regions) :
    ∃ p ∈ ins, phys p.1 = r ∧ p.2 = .words m := by
  obtain ⟨a, ha, hr⟩ := List.mem_filterMap.1 h
  have hm : (a.reg, a.kind) ∈ ins.map fun p => (phys p.1, p.2) :=
    hargs ▸ List.mem_map_of_mem (f := fun a : Haxc.AbiArg => (a.reg, a.kind)) ha
  obtain ⟨p, hp, he⟩ := List.mem_map.1 hm
  cases hk : a.kind with
  | scalar => simp [Haxc.AbiArg.region, hk] at hr
  | words n =>
    simp only [Haxc.AbiArg.region, hk, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [hk] at he
    simp only [Prod.mk.injEq] at he
    exact ⟨p, hp, he.1, he.2⟩

/-- The register of a general-purpose name is the carrier name of no stack parameter. -/
theorem phys_ne_stackArgReg {r : String} (h : gpOk r = true) (k : Nat) :
    phys r ≠ stackArgReg k := by
  apply Haxc.ne_stackArgReg
  have key : ∀ r ∈ gpList, ¬ "%rsp+".toList <+: (phys r).toList := by decide
  exact key r (mem_gpList h)

/-- Under a layout whose parameters are those of `ins` in the registers of general-purpose
    names, no parameter is a stack parameter. -/
theorem reg_ne_stackArgReg {l : LinkedFn} {ins : List (String × ArgKind)}
    (hargs : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2))
    (hgp : ∀ p ∈ ins, gpOk p.1 = true) {a : Haxc.AbiArg} (ha : a ∈ l.layout.args) (k : Nat) :
    a.reg ≠ stackArgReg k := by
  have hm : (a.reg, a.kind) ∈ ins.map fun p => (phys p.1, p.2) :=
    hargs ▸ List.mem_map_of_mem (f := fun a : Haxc.AbiArg => (a.reg, a.kind)) ha
  obtain ⟨p, hp, he⟩ := List.mem_map.1 hm
  rw [← (Prod.mk.inj he).1]
  exact phys_ne_stackArgReg (hgp p hp) k

/-- **The register of an array parameter at the entry of a call** holds the base of the
    array it passes, an array of a frame slot of the length of the parameter. -/
theorem entry_of_paramAt {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {sA : AState} {sa : LstateA}
    (hc : ACorr rsp sA sa) {p : String × ArgKind} {x : String} {m : Nat}
    (h : ParamAt slotArr base sa p x) (hk : p.2 = .words m) (ret : Nat) :
    (entryOf ret sA).regs (phys p.1) = base x ∧ ∃ q, slotArr q = some (x, m) := by
  obtain ⟨pn, k⟩ := p
  obtain ⟨hgp, hm⟩ := h
  simp only at hk
  subst hk
  obtain ⟨hq, hptr⟩ := hm
  refine ⟨?_, hq⟩
  rw [entryOf_regs, if_neg (gpFacts hgp).physNe]
  exact Option.some.inj ((hc.regs pn hgp).symm.trans hptr)

/-- **The array of a pointer region at the entry of a call.** For parameters `ins` passed by
    the operands `args`, the register of a pointer region holds at the entry state the base
    of the array its parameter passes. -/
theorem region_at_call {l : LinkedFn} {ins : List (String × ArgKind)}
    (hargs : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2))
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {sA : AState} {sa : LstateA} (hc : ACorr rsp sA sa) {args : List String}
    (hpar : List.Forall₂ (ParamAt slotArr base sa) ins args) (ret : Nat) {r : String}
    {m : Nat} (h : (r, m) ∈ l.layout.regions) :
    ∃ p x q, (p, x) ∈ ins.zip args ∧ phys p.1 = r ∧ p.2 = .words m
      ∧ (entryOf ret sA).regs r = base x ∧ slotArr q = some (x, m) := by
  obtain ⟨p, hp, hr, hk⟩ := exists_ins_of_mem_regions hargs h
  obtain ⟨x, hz, hpx⟩ := exists_mem_zip_of_forall₂ hpar hp
  obtain ⟨he, q, hq⟩ := entry_of_paramAt hc hpx hk ret
  exact ⟨p, x, q, hz, hr, hk, hr ▸ he, hq⟩

/-- A location of the pointer regions of a layout is a byte of a word of a region. -/
theorem mem_regionLocs {σ : Haxc.AbiLayout} {rv : String → BitVec 64} {x : Loc}
    (h : x ∈ regionLocs σ rv) :
    ∃ r m k y, (r, m) ∈ σ.regions ∧ k < m ∧ InRange8 (cellAt (rv r) k) y ∧ x = Loc.mem y := by
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 h
  obtain ⟨w, ⟨k, hk, rfl⟩, hw⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨p.1, p.2, k, y, hp, hk, hy, rfl⟩

/-- **A location of the pointer regions at the entry of a call** is a byte of a cell of an
    array the call passes. -/
theorem passed_cell {l : LinkedFn} {ins : List (String × ArgKind)}
    (hargs : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2))
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {sA : AState} {sa : LstateA} (hc : ACorr rsp sA sa) {args : List String}
    (hpar : List.Forall₂ (ParamAt slotArr base sa) ins args) (ret : Nat) {x : Loc}
    (h : x ∈ regionLocs l.layout (entryOf ret sA).regs) :
    ∃ q A n j y, slotArr q = some (A, n) ∧ j < n ∧ A ∈ passedOf ins args
      ∧ InRange8 (cellAt (base A) j) y ∧ x = Loc.mem y := by
  obtain ⟨r, m, k, y, hr, hk, hy, rfl⟩ := mem_regionLocs h
  obtain ⟨p, A, q, hz, -, hpk, he, hq⟩ := region_at_call hargs hc hpar ret hr
  rw [he] at hy
  exact ⟨q, A, m, k, y, hq, hk, ⟨p, hz, by rw [hpk]; exact nofun⟩, hy, rfl⟩

/-- The locations of a `conj` of a mapped list lie in the locations of an entry. -/
theorem mem_fp_foldr_conj {σ' L ι : Type} [Footprinted σ' L] {f : ι → SAssert σ' L} {x : L} :
    ∀ {ps : List ι}, x ∈ ((ps.map f).foldr conj emp).fp → ∃ p ∈ ps, x ∈ (f p).fp
  | [], h => absurd h (Set.notMem_empty x)
  | p :: _, h => by
    rcases h with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hx⟩ := mem_fp_foldr_conj h
      exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩

/-- A `conj` of a mapped list holds where every entry holds. -/
theorem holds_foldr_conj {σ' L ι : Type} [Footprinted σ' L] {f : ι → SAssert σ' L} {s : σ'} :
    ∀ {ps : List ι}, (∀ p ∈ ps, (f p).holds s) → ((ps.map f).foldr conj emp).holds s
  | [], _ => trivial
  | p :: _, h => ⟨h p List.mem_cons_self,
      holds_foldr_conj fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- A region of `isResRegion` is the region of an out result. -/
theorem eq_of_isResRegion {σ : Haxc.AbiLayout} {p : String × Nat}
    (h : isResRegion σ p = true) : ∃ r n, σ.result = .words r n ∧ p = (r, n) := by
  unfold isResRegion at h
  split at h
  · rename_i r n hr
    exact ⟨r, n, hr, by simpa using h⟩
  · cases h

/-- A byte of the word at `e` is not among the `F` bytes below `e`, for `F + 8 ≤ 2 ^ 64`. -/
theorem not_inFrame_of_inRange8_self {e x : BitVec 64} {F : Nat} (hF : F + 8 ≤ 2 ^ 64)
    (hx : InRange8 e x) : ¬ InFrame e F x := by
  intro hf
  unfold InRange8 at hx
  unfold InFrame at hf
  have he := e.isLt
  have hx' := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at hx hf
  omega

/-- **The resources at the entry of a call hold.** Let the parameters of the layout of `l` be
    those of `ins` in the registers of their names, without repetition, and the frame size of
    `l` be below `2 ^ 64 - 8`. Let the caller be separated (`CallerSep` at `l.frame`), the
    operands `args` pass the parameters `ins` (`ParamAt`), and the destination array of an
    out result differ from every array an array parameter of another register passes. Then
    the resources of a call of `l` hold at the entry state at the logical variables
    `callVarOf`. -/
theorem entryAt_at_call {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep frame slotArr base rsp) {l : LinkedFn} {ins : List (String × ArgKind)}
    (hargs : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2))
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame) {sa : LstateA} {sA : AState}
    (hc : ACorr rsp sA sa) {args : List String}
    (hpar : List.Forall₂ (ParamAt slotArr base sa) ins args)
    (hdst : ∀ r n, l.layout.result = .words r n → ∀ p x, (p, x) ∈ ins.zip args →
      p.2 ≠ .scalar → phys p.1 ≠ r → ∀ p' x', (p', x') ∈ ins.zip args → phys p'.1 = r →
        x ≠ x')
    (ret : Nat) : (l.entryAt (callVarOf l ret sA)).holds (entryOf ret sA) := by
  have hasp : (callVarOf l ret sA).sp = rsp + BitVec.ofInt 64 (-8) := by
    show (entryOf ret sA).regs "%rsp" = _
    rw [entryOf_regs, if_pos rfl, retWord, hc.sp]
  have hgp : ∀ p ∈ ins, gpOk p.1 = true := fun p hp => by
    obtain ⟨_, -, hpx⟩ := exists_mem_zip_of_forall₂ hpar hp
    exact hpx.1
  have harr : ∀ r m, (r, m) ∈ l.layout.regions →
      (arrOwn ((entryOf ret sA).regs r) m).holds (entryOf ret sA) := by
    intro r m hp
    obtain ⟨_, A, q, -, -, -, he, hq⟩ := region_at_call hargs hc hpar ret hp
    refine holds_arrOwn.2 fun i j hij hj => ?_
    rw [he]
    exact hsep.cells q A m q A m i j hq hq (by omega) hj (Or.inr (by omega))
  refine ⟨⟨?d1, fun _ _ => rfl, ?d2, ⟨⟨?dro, holds_foldr_conj fun (p : String × Nat) hp =>
    harr p.1 p.2 (List.mem_filter.1 hp).1, ?res⟩, rfl⟩, ?d3, ?hret, ?d4, trivial, ?d5, trivial,
    trivial⟩,
    fun a ha k hk => absurd hk (reg_ne_stackArgReg hargs hgp ha k), trivial⟩
  case d1 =>
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ h
    rcases h with (h | h) | h | h | h | h
    · obtain ⟨_, _, _, _, _, _, _, he⟩ := mem_regionLocs (regionsOwn_fp_subset _ _ h)
      cases he
    · obtain ⟨_, _, _, _, _, _, _, he⟩ := mem_regionLocs h
      cases he
    · obtain ⟨_, _, he⟩ := h
      cases he
    · obtain ⟨_, ⟨_, hn⟩, he⟩ := h
      cases he
      exact hn hr
    · obtain ⟨_, he⟩ := h
      cases he
    · obtain ⟨_, _, he⟩ := h
      cases he
  case d2 =>
    rw [Set.disjoint_left]
    intro x hx hR
    have hx' : x ∈ regionLocs l.layout (entryOf ret sA).regs := by
      rcases hx with hx | hx
      · exact regionsOwn_fp_subset _ _ hx
      · exact hx
    obtain ⟨q, A, n, j, y, hq, hj, -, hy, rfl⟩ := passed_cell hargs hc hpar ret hx'
    obtain ⟨n1, n2⟩ := hS.cells q A n j hq hj y hy
    rcases hR with ⟨z, hz, he⟩ | ⟨_, -, he⟩ | ⟨_, he⟩ | ⟨z, hz, he⟩
    · cases he
      rw [hasp] at hz
      exact n1 hz
    · cases he
    · cases he
    · cases he
      rw [hasp] at hz
      exact n2 hz
  case d3 =>
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hR
    rcases hR with ⟨_, -, he⟩ | ⟨_, he⟩ | ⟨z, hz, he⟩
    · cases he
    · cases he
    · cases he
      exact not_inFrame_of_inRange8_self hfb hy hz
  case d4 =>
    rw [Set.disjoint_left]
    rintro _ ⟨r, -, rfl⟩ (⟨_, he⟩ | ⟨_, -, he⟩) <;> cases he
  case d5 =>
    rw [Set.disjoint_left]
    rintro _ ⟨f, rfl⟩ ⟨_, -, he⟩
    cases he
  case hret =>
    show readLE 8 (entryOf ret sA).mem ((entryOf ret sA).regs "%rsp") = BitVec.ofNat 64 ret
    rw [readLE_eight_eq_addrMem_read64, entryOf_mem_eq, entryOf_regs, if_pos rfl,
      Ascent.AddrMem.read64_write64_same]
  case res =>
    refine holds_bigSep.2 ⟨List.pairwise_map.2 ((((regions_pairwise hnd).filter _)).imp_of_mem
      fun hp hp' hne => ?_), fun P hP => ?_⟩
    · exfalso
      apply hne
      obtain ⟨r, n, hr, rfl⟩ := eq_of_isResRegion (List.mem_filter.1 hp).2
      obtain ⟨r', n', hr', rfl⟩ := eq_of_isResRegion (List.mem_filter.1 hp').2
      rw [hr] at hr'
      cases hr'
      rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hP
      exact harr p.1 p.2 (List.mem_filter.1 hp).1
  case dro =>
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨⟨r0, m0⟩, hp, hxp⟩ := mem_fp_foldr_conj hx
    obtain ⟨P, hP, hxP⟩ := mem_fp_bigSep.1 hx'
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hP
    obtain ⟨hpr, hpn⟩ := List.mem_filter.1 hp
    obtain ⟨hpr', hpn'⟩ := List.mem_filter.1 hp'
    obtain ⟨r, n, hres, rfl⟩ := eq_of_isResRegion hpn'
    have hne : r0 ≠ r := by
      rintro rfl
      obtain rfl := eq_of_mem_regions hnd hpr hpr'
      simp [isResRegion, hres] at hpn
    obtain ⟨p0, x0, q0, hz0, hph0, hk0, he0, hq0⟩ := region_at_call hargs hc hpar ret hpr
    obtain ⟨p1, x1, q1, hz1, hph1, -, he1, hq1⟩ := region_at_call hargs hc hpar ret hpr'
    have hx01 := hdst r n hres p0 x0 hz0 (by rw [hk0]; exact nofun) (by rw [hph0]; exact hne)
      p1 x1 hz1 hph1
    obtain ⟨w, ⟨k, hk, rfl⟩, y, hy, rfl⟩ := Set.mem_iUnion₂.1 hxp
    obtain ⟨w', ⟨k', hk', rfl⟩, y', hy', he⟩ := Set.mem_iUnion₂.1 hxP
    cases he
    change InRange8 ((entryOf ret sA).regs r0 + _) y at hy
    change InRange8 ((entryOf ret sA).regs r + _) y at hy'
    rw [he0] at hy
    rw [he1] at hy'
    exact Set.disjoint_left.1 (disjoint_wordLocs_iff.2
      (hsep.cells q0 x0 m0 q1 x1 n k k' hq0 hq1 hk hk' (Or.inl hx01))) ⟨y, hy, rfl⟩
      ⟨y, hy', rfl⟩

/-- **The framed precondition at a call site.** Under the hypotheses of `entryAt_at_call`,
    for a layout whose result is a register or the region of a parameter, and a meaning
    defined at the values the layout reads at the entry state, the precondition of the
    contract at `callVarOf` and the frame of the caller off the passed arrays hold separated
    at the entry state of the call. -/
theorem framedPre_at_call {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep frame slotArr base rsp) {l : LinkedFn} {ins : List (String × ArgKind)}
    (hargs : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2))
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hres : (∃ r, l.layout.result = .reg r)
      ∨ ∃ r n, l.layout.result = .words r n ∧ (r, n) ∈ l.layout.regions)
    (hS : CallerSep frame slotArr base rsp l.frame) {sa : LstateA} {sA : AState}
    (hc : ACorr rsp sA sa) {args : List String}
    (hpar : List.Forall₂ (ParamAt slotArr base sa) ins args)
    (hdst : ∀ r n, l.layout.result = .words r n → ∀ p x, (p, x) ∈ ins.zip args →
      p.2 ≠ .scalar → phys p.1 ≠ r → ∀ p' x', (p', x') ∈ ins.zip args → phys p'.1 = r →
        x ≠ x')
    (ret : Nat) (hsem : (l.sem (l.layout.args.map (·.read (entryOf ret sA)))).isSome = true) :
    (l.contractPre (callVarOf l ret sA)
      ∗ callerFrameA frame slotArr base (passedOf ins args) ∅).holds (entryOf ret sA) := by
  have hgp : ∀ p ∈ ins, gpOk p.1 = true := fun p hp => by
    obtain ⟨_, -, hpx⟩ := exists_mem_zip_of_forall₂ hpar hp
    exact hpx.1
  refine callerFrameA_sep_pre hsep hS (fun r hr => absurd hr (Set.notMem_empty r)) ?_ hc.sp ret
    ⟨Set.disjoint_empty _, entryAt_at_call hsep hargs hnd hfb hS hc hpar hdst ret, hsem⟩
  rw [Set.disjoint_left]
  intro x hx hR
  have hreg : x ∈ regionLocs l.layout (entryOf ret sA).regs := by
    rcases hR with (hR | hR) | hR
    · exact hR
    · exfalso
      obtain ⟨w, ⟨a, ha, k, hk, rfl⟩, -⟩ := Set.mem_iUnion₂.1 hR
      exact reg_ne_stackArgReg hargs hgp ha k hk
    · rcases hres with ⟨r, hr⟩ | ⟨r, n, hr, hrn⟩
      · exfalso
        rw [hr] at hR
        change x ∈ ({Loc.reg r} : Set Loc) at hR
        rw [Set.mem_singleton_iff] at hR
        subst hR
        rcases mem_callerFrameA_fp hx with ⟨_, _, _, _, _, he⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he⟩ | ⟨_, hr', -⟩
        · cases he
        · cases he
        · exact hr'
      · rw [hr] at hR
        exact Set.mem_biUnion hrn hR
  obtain ⟨q, A, n, j, y, hq, hj, hA, hy, rfl⟩ := passed_cell hargs hc hpar ret hreg
  rcases mem_callerFrameA_fp hx with ⟨q', b, z, hb, hz, he⟩ |
    ⟨q', A', n', j', z, hq', hj', hA', hz, he⟩ | ⟨_, hr', -⟩
  · cases he
    exact Set.disjoint_left.1 (disjoint_wordLocs_iff.2 (hsep.cellFrame q A n j hq hj q' b hb))
      ⟨y, hy, rfl⟩ ⟨y, hz, rfl⟩
  · cases he
    exact Set.disjoint_left.1 (disjoint_wordLocs_iff.2 (hsep.cells q' A' n' q A n j' j hq' hq
      hj' hj (Or.inl fun h => hA' (h ▸ hA)))) ⟨y, hz, rfl⟩ ⟨y, hy, rfl⟩
  · exact hr'

/-! ## 7. The out call step by the frame rule -/

/-- **A call of a linked function with an out layout re-establishes the relaxed relation, by
    the frame rule of the contract.** Let `ImgRel` and `ACorr` hold at a call instruction of a
    body of the class `physImgB`, the run relation `X` meet the contract of `l`, the pointer
    name `po` hold the base of the array `A` of a frame slot of length `n`, the entry state
    satisfy the precondition of the contract separated from the frame of the caller off the
    arrays of `passed`, every cell of an array of `passed` other than `A` lie in a pointer
    region outside the result, and the summary give the array `arr` at the summary input of
    the entry state. Then for every run of `X`, after the return: the words at the base of
    `A` are `arr`, and there is an address state at the next position that corresponds to
    the byte state and is related, up to the names `exemptC` of the interface of the contract
    and the flags, to the image state with `arr` in the carrier of `A`. -/
theorem call_reestablishes_meets_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {l : LinkedFn} {X : CalleeRun} (hX : SContract X l.contract)
    {ins : List (String × ArgKind)} {po : String} {n : Nat} (hL : OutLayout l ins po n)
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf)
    {sA : AState} (hc : ACorr rsp sA sa) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    {ra : Option String} {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    {q A : String} (hq : slotArr q = some (A, n)) (hptr : sa.reg.getW po 64 = some (base A))
    (ret : Nat) {passed : Set String} {a : CallVar}
    (hpre : (l.contractPre a ∗ callerFrameA frame slotArr base passed ∅).holds (entryOf ret sA))
    (hpass : ∀ q' A' n' j, slotArr q' = some (A', n') → j < n' → A' ∈ passed → A' ≠ A →
      ∀ x, InRange8 (cellAt (base A') j) x →
        Loc.mem x ∈ regionLocs l.layout a.rv ∧ Loc.mem x ∉ resLocs (entryRegs a.rv) l.layout.result)
    {arr : Fin n → BitVec 64}
    (hv : (outSummary l ins n).runOut n (readIns ins (entryOf ret sA)) = some arr)
    {t : List CTLeak} {sc : AState} (hrun : X (entryOf ret sA) t sc) :
    (∀ j (hj : j < n),
        read64 (retOps.foldl aMachine.exec sc).mem (cellAt (base A) j) = arr ⟨j, hj⟩)
      ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
        ∧ ImgRelF frame slotArr base body (exemptC (l.contractSig (ins.map (·.1)) none))
            (LprogIsa.retArr A arr s) sa' := by
  have hw := outCallee_of_meets hL
  have hS := calleeSpec_of_sContract hX (ins.map (·.1)) none
  have hC := hX.frame (fun _ => callerFrameA frame slotArr base passed ∅)
    (fun a _ _ => contractWrites_subset l a) (fun a => contractPost_fp_subset l a)
  have hpost := hC.post a _ t sc hpre hrun
  have hkeep := hC.keep a _ t sc hpre hrun
  have hcpre : (l.contractSig (ins.map (·.1)) none).pre (entryOf ret sA) := ⟨a, hpre.2.1⟩
  obtain ⟨hsp, -, hk, -, -⟩ := call_return hS ret sA hcpre hrun
  have hra := sp_of_pre hpre.2.1
  have hpo : sA.regs (phys po) = base A :=
    Option.some.inj ((hc.regs po hw.po_gp).symm.trans hptr)
  have hmR : (retOps.foldl aMachine.exec sc).mem = sc.mem := by
    rw [retOps_eq, (evalInstrA_leaFrame sc 8).2]
  have hwr : ∀ j (hj : j < n),
      read64 (retOps.foldl aMachine.exec sc).mem (cellAt (base A) j) = arr ⟨j, hj⟩ := by
    intro j hj
    have h1 := hw.post _ _ hcpre ⟨a, hpre.2.1, hpost.2.1⟩
    rw [hv, entryOf_regs, if_neg (gpFacts hw.po_gp).physNe, hpo] at h1
    rw [hmR, Option.some.inj h1]
  have hmem : ∀ x, Loc.mem x ∉ l.contractWrites a → ¬ InRange8 (retWord sA) x →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x :=
    fun x hw hr => memAfter_of_keep hc hkeep x hw hr
  have hframe : ∀ x, Loc.mem x ∈ (callerFrameA frame slotArr base passed ∅).fp →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x := by
    intro x hx
    have hnp : Loc.mem x ∉ (l.contractPre a).fp := fun h => Set.disjoint_left.1 hpre.1 h hx
    refine hmem x (fun hw => hnp (contractWrites_subset l a hw)) fun hr => hnp ?_
    rw [hra] at hr
    exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨x, hr, rfl⟩))))
  obtain ⟨⟨-, -, d2, -⟩, -⟩ := entryAt_of_pre hpre.2.1
  have harr : ∀ j (hj : j < n),
      read64 (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) (cellAt (base A) j)
        = arr ⟨j, hj⟩ := by
    intro j hj
    rw [read64_eq_of_agree (m' := (retOps.foldl aMachine.exec sc).mem)
      (fun x hx => by simp [memAfter, hx]) (hsep.red q A n j hq hj)]
    exact hwr j hj
  let ω : CallOut := ⟨fun _ => 0, false, false, false⟩
  refine ⟨hwr, _, rfl, acorr_callC _ ω hc hsp fun r hg hcl => hk _ (gpFacts hg).physNe hcl,
    _, _, agreeOffF_retArr _ (outOf _ ω) s A arr hw.res_none,
    imgRel_callC_out hsep hphys _ (outOf _ ω) hrel hb hbi (fun q' b hb' x hx => hframe x ?_) hq
      (fun q' A' n' j hq' hA' hj x hx => ?_) harr⟩
  · exact Or.inl (Set.mem_iUnion.2 ⟨q', by
      simp only [hb', fp_own, optWordLocs]; exact ⟨x, hx, rfl⟩⟩)
  · by_cases hAp : A' ∈ passed
    · obtain ⟨hin, hnr⟩ := hpass q' A' n' j hq' hj hAp hA' x hx
      have hreg : Loc.mem x ∈ (conj (regionsOwn l.layout a.rv)
          (inputsAt l.layout a.rv a.vals)).fp := Or.inr hin
      refine hmem x ?_ fun hr => ?_
      · rintro (hw | hw)
        · exact Set.disjoint_left.1 d2 hreg (Or.inr (Or.inr (Or.inr ⟨x, hw, rfl⟩)))
        · exact hnr hw
      · rw [hra] at hr
        exact Set.disjoint_left.1 d2 hreg (Or.inl ⟨x, hr, rfl⟩)
    · exact hframe x (Or.inr (Or.inl (Set.mem_iUnion.2 ⟨(A', j), hAp, ⟨q', n', hq', hj⟩,
        ⟨x, hx, rfl⟩⟩)))

/-! ## 8. Site steps and chains at the interface of the contract -/

/-- **The step of a call site of a linked function on scalars and read-only arrays, at the
    interface of the contract.** As `ImageAddrCallArrChain.siteStep_ins` for a run relation
    `X` that meets the contract of `l`: the room at each call is the resources at the entry
    of the call (`entryAt_at_call`), and the summary input comes from the parameters `ins`
    passed by the operands `args`. -/
theorem siteStep_contract_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} (hXc : SContract X l.contract)
    {ins : List (String × ArgKind)} {res : String} (hL : InsLayout l ins res)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame) {args : List String}
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (ParamAt slotArr base sa) ins args)
    {E : Nat → List String}
    (hdead : callDeadInsB (l.contractSig (ins.map (·.1)) (some res)) res args E body = true)
    {p : Nat} (hb : ∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) {u v : LstateMF}
    (hv : ∃ vs w, LprogIsa.argsRead (insSummary l ins).arrArgs u.prog.base 0
        (args.map LOperand.reg) = some vs ∧ (insSummary l ins).run vs = some w
        ∧ v = LprogIsa.retWord res w u) :
    SiteStep frame slotArr base rsp body X (l.contractSig (ins.map (·.1)) (some res)) (E p)
      (E (p + 1)) u v :=
  siteStep_ins hsep hphys (calleeSpec_of_sContract hXc _ _) (insCallee_of_contract hL) hS
    (footBelow_contractSig hL.result _ _)
    (fun s sa zf sA hrel hc hcall ret => ⟨_, entryAt_at_call hsep hL.args hnd hfb hS hc
      (hpar s sa zf sA hrel hc hcall) (fun r n h => by rw [hL.result] at h; cases h) ret⟩)
    (fun s sa zf sA hrel hc hcall ret _ h =>
      readIns_entry hsep hS hrel hc ret (hpar s sa zf sA hrel hc hcall) h)
    hdead hb hv

/-- **A halting run of the image of a calling body whose call sites call one linked function
    on scalars and read-only arrays is a run through calls of the program its linked bytes
    decode to**, for a callee block whose code `q` meets the contract of `l`. The hypotheses
    are those of `ImageAddrCallArrChain.haltsC_of_linkedChecks_arr` with the specification of
    `insSig` replaced by the contract, and the precondition and the entry hypotheses at the
    calls replaced by the parameters passed at each call (`hpar`). -/
theorem haltsC_of_contract_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {l : LinkedFn}
    {ins : List (String × ArgKind)} {res : String} (hL : InsLayout l ins res)
    (hXc : SContract (Callee.runOf r q) l.contract) (hq : ∀ tg, RInstr.call tg ∉ q)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame) {args : List String}
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (ParamAt slotArr base sa) ins args)
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB l.frame body = true)
    (hshapes : DecodeGen.shapesOf (LprogBytesDecode.Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = DecodePrintedAddr.frameP (LprogBytesDecode.Params.ofBody body) rsp q)
    (symBase : String → Option Int) {cb : List (BitVec 8)} {prog : List RInstr}
    (hcb : LprogBytesDecode.decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
          body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
          body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadInsB (l.contractSig (ins.map (·.1)) (some res)) res args D.dead body
      = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some (insSummary l ins))
    (hshape : siteShapeB f res args (callImg slotArr res (args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr res (args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (LprogBytesDecode.Params.ofBody body).frame sa sA →
        Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (k : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res (args.map LOperand.reg) body)) k s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL0 : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA0 : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  haltsC_of_linkedChecksS hsep hphys hgate hsites r (calleeSpec_of_sContract hXc _ _) hq hcls
    hshapes hfr symBase hcb hne hbr hP hflags hcond hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_contract_ins hsep hphys hXc hL hnd hfb hS hpar hdead hb
      (glue_ins (insSummary_retWord l ins) (sitesOf_of_siteShapeB hshape hT) hg))
    k hrun hfn hlen hL0 hI0 hA0

/-- **A halting run of the image of a calling body whose call sites call one linked function
    on scalars and read-only arrays is a run of the program of its relocated item list under
    the oracle of the callee**, for a run relation `X` that meets the contract of `l`. The
    hypotheses are those of `haltsC_of_contract_ins` with the bytes of the callee replaced by
    the program `prog` of the relocated item list in front of a callee block at the index
    `tgt`. -/
theorem haltsO_of_contract_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hL : InsLayout l ins res) (hXc : SContract X l.contract)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame) {args : List String}
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (ParamAt slotArr base sa) ins args)
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB l.frame body = true)
    (hshapes : DecodeGen.shapesOf (LprogBytesDecode.Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = DecodePrintedAddr.frameP (LprogBytesDecode.Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr} {tgt L : Nat}
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) tgt L
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadInsB (l.contractSig (ins.map (·.1)) (some res)) res args D.dead body
      = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some (insSummary l ins))
    (hshape : siteShapeB f res args (callImg slotArr res (args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr res (args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (LprogBytesDecode.Params.ofBody body).frame sa sA →
        Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (k : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res (args.map LOperand.reg) body)) k s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL0 : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA0 : ACorr rsp sA sa) :
    ∃ sA', Callee.HaltsO aMachine (Callee.oracleAt tgt X) prog
        (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' :=
  haltsO_of_linkedChecksS hsep hphys hgate hsites (calleeSpec_of_sContract hXc _ _) hcls
    hshapes hfr symBase hP hflags hcond hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_contract_ins hsep hphys hXc hL hnd hfb hS hpar hdead hb
      (glue_ins (insSummary_retWord l ins) (sitesOf_of_siteShapeB hshape hT) hg))
    k hrun hfn hlen hL0 hI0 hA0

/-- **The step of a call site of a linked function with an out layout, at the interface of
    the contract.** As `ImageAddrCallOutChain.siteStep_out` for a run relation `X` that meets
    the contract of `l`: the room at each call is the resources at the entry of the call
    (`entryAt_at_call`), and the pointer and the summary input come from the parameters
    `ins` passed by the operands `args`, the destination parameter passing `A`. -/
theorem siteStep_contract_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} (hXc : SContract X l.contract)
    {ins : List (String × ArgKind)} {po : String} {n : Nat} (hL : OutLayout l ins po n)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame) {qA A : String}
    (hqA : slotArr qA = some (A, n)) {args : List String}
    (hA : ((po, ArgKind.words n), A) ∈ ins.zip args)
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (ParamAt slotArr base sa) ins args)
    (hdst : ∀ r n, l.layout.result = .words r n → ∀ p x, (p, x) ∈ ins.zip args →
      p.2 ≠ .scalar → phys p.1 ≠ r → ∀ p' x', (p', x') ∈ ins.zip args → phys p'.1 = r →
        x ≠ x')
    {E : Nat → List String}
    (hdead : callDeadOutB (l.contractSig (ins.map (·.1)) none) args E body = true) {p : Nat}
    (hb : ∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) {u v : LstateMF}
    (hv : ∃ vs arr, LprogIsa.argsRead (outSummary l ins n).arrArgs u.prog.base 0
        (args.map LOperand.reg) = some vs ∧ (outSummary l ins n).runOut n vs = some arr
        ∧ v = LprogIsa.retArr A arr u) :
    SiteStep frame slotArr base rsp body X (l.contractSig (ins.map (·.1)) none) (E p)
      (E (p + 1)) u v :=
  siteStep_out hsep hphys (calleeSpec_of_sContract hXc _ _) (outCallee_of_meets hL) hS
    (footBelowOut_contractSig hL _ _)
    (fun s sa zf sA hrel hc hcall ret => ⟨_, entryAt_at_call hsep hL.args hnd hfb hS hc
      (hpar s sa zf sA hrel hc hcall) hdst ret⟩)
    hqA
    (fun s sa zf sA hrel hc hcall =>
      ⟨((List.forall₂_iff_zip.1 (hpar s sa zf sA hrel hc hcall)).2 hA).2.2,
        fun ret _ h => readIns_entry hsep hS hrel hc ret (hpar s sa zf sA hrel hc hcall) h⟩)
    hdead hb hv

/-- **A halting run of the image of a calling body whose call sites call one linked function
    with an out layout is a run through calls of the program its linked bytes decode to**, for
    a callee block whose code `q` meets the contract of `l`. The hypotheses are those of
    `ImageAddrCallOutChain.haltsC_of_linkedChecks_out` with the specification of the out
    interface replaced by the contract, and the precondition and the entry hypotheses at the
    calls replaced by the parameters passed at each call (`hpar`), the destination passing
    `A` (`hA`) and separated from the other arrays (`hdst`). -/
theorem haltsC_of_contract_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {l : LinkedFn}
    {ins : List (String × ArgKind)} {po : String} {n : Nat} (hL : OutLayout l ins po n)
    (hXc : SContract (Callee.runOf r q) l.contract) (hq : ∀ tg, RInstr.call tg ∉ q)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame)
    {qA A : String} (hqA : slotArr qA = some (A, n)) {args : List String}
    (hA : ((po, ArgKind.words n), A) ∈ ins.zip args)
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (ParamAt slotArr base sa) ins args)
    (hdst : ∀ r n, l.layout.result = .words r n → ∀ p x, (p, x) ∈ ins.zip args →
      p.2 ≠ .scalar → phys p.1 ≠ r → ∀ p' x', (p', x') ∈ ins.zip args → phys p'.1 = r →
        x ≠ x')
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB l.frame body = true)
    (hshapes : DecodeGen.shapesOf (LprogBytesDecode.Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = DecodePrintedAddr.frameP (LprogBytesDecode.Params.ofBody body) rsp q)
    (symBase : String → Option Int) {cb : List (BitVec 8)} {prog : List RInstr}
    (hcb : LprogBytesDecode.decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
          body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
          body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadOutB (l.contractSig (ins.map (·.1)) none) args D.dead body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some (outSummary l ins n))
    (hshape : siteShapeB f A args (callImg slotArr A (args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (LprogBytesDecode.Params.ofBody body).frame sa sA →
        Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (k : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)) k s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL0 : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA0 : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  haltsC_of_linkedChecksS hsep hphys hgate hsites r (calleeSpec_of_sContract hXc _ _) hq hcls
    hshapes hfr symBase hcb hne hbr hP hflags hcond hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_contract_out hsep hphys hXc hL hnd hfb hS hqA hA hpar hdst
      hdead hb
      (glue_out (pr := outSummary l ins n) rfl (fun _ => rfl)
        (sitesOf_of_siteShapeB hshape hT) hg))
    k hrun hfn hlen hL0 hI0 hA0

/-- **A halting run of the image of a calling body whose call sites call one linked function
    with an out layout is a run of the program of its relocated item list under the oracle
    of the callee**, for a run relation `X` that meets the contract of `l`. The hypotheses
    are those of `haltsC_of_contract_out` with the bytes of the callee replaced by the program
    `prog` of the relocated item list in front of a callee block at the index `tgt`. -/
theorem haltsO_of_contract_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : OutLayout l ins po n) (hXc : SContract X l.contract)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame)
    {qA A : String} (hqA : slotArr qA = some (A, n)) {args : List String}
    (hA : ((po, ArgKind.words n), A) ∈ ins.zip args)
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (ParamAt slotArr base sa) ins args)
    (hdst : ∀ r n, l.layout.result = .words r n → ∀ p x, (p, x) ∈ ins.zip args →
      p.2 ≠ .scalar → phys p.1 ≠ r → ∀ p' x', (p', x') ∈ ins.zip args → phys p'.1 = r →
        x ≠ x')
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB l.frame body = true)
    (hshapes : DecodeGen.shapesOf (LprogBytesDecode.Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = DecodePrintedAddr.frameP (LprogBytesDecode.Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr} {tgt L : Nat}
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) tgt L
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (LprogBytesDecode.Params.ofBody body)
        body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadOutB (l.contractSig (ins.map (·.1)) none) args D.dead body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some (outSummary l ins n))
    (hshape : siteShapeB f A args (callImg slotArr A (args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (LprogBytesDecode.Params.ofBody body).frame sa sA →
        Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (k : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr A (args.map LOperand.reg) body)) k s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL0 : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA0 : ACorr rsp sA sa) :
    ∃ sA', Callee.HaltsO aMachine (Callee.oracleAt tgt X) prog
        (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' :=
  haltsO_of_linkedChecksS hsep hphys hgate hsites (calleeSpec_of_sContract hXc _ _) hcls
    hshapes hfr symBase hP hflags hcond hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_contract_out hsep hphys hXc hL hnd hfb hS hqA hA hpar hdst
      hdead hb
      (glue_out (pr := outSummary l ins n) rfl (fun _ => rfl)
        (sitesOf_of_siteShapeB hshape hT) hg))
    k hrun hfn hlen hL0 hI0 hA0

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets
