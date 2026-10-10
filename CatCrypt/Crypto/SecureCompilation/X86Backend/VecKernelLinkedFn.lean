/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
public import CatCrypt.Crypto.SecureCompilation.Ascent.Footprint

@[expose] public section

set_option autoImplicit false

/-!
# A vector kernel as a linked function with a word-array result

A spec-carrying vector kernel `VecKernelLink.VecKernelCallee` at the signature
`VecKernelSpec.kernelSig` reads its input at `%rsi` and writes its output region at `%rdi`.
Read as a linked function `Hax.LinkedFn` in the destination-argument convention, the kernel
has two array parameters: the destination, the words of the output region at `%rdi`, and the
input, the words at `%rsi`; its result is the destination array after the run. The meaning
`sem` of the linked function is related to the lane-wise contract of the kernel by
`VecOutSem`: where the meaning is defined at the words an entry state holds, the input region
holds the parameters of the scalar program lane-wise for some valuations, and every return
state whose output region holds the outputs on those valuations holds the value of the
meaning in the destination words.

## Main definitions

* `outWords`: the number of words of the output region of a kernel.
* `vecOutLayout`: the layout of the two array parameters at `%rdi` and `%rsi`, with the
  result the destination words at `%rdi`.
* `VecOutSem`: the relation between a meaning on source values and the lane-wise contract
  of the kernel.
* `Hax.LinkedFn.ofVecOut`: the linked function of a spec-carrying vector kernel, with the
  precondition `KernelRegions` and the footprint, postcondition and public relation of
  `kernelSig`.

## Main results

* `lane_readBytes`: lane `k < 8` of the 64 bytes at an address is the word at eight times
  `k` past it.
* `ofVecOut_outLayout`: the linked function has the out layout with the destination at
  `RDI` and the input at `RSI`.
* `ofVecOut_calleeSpec`: the callee of the kernel meets the out interface `outSig` of the
  linked function.
* `room_of_callSite`: at a call site whose destination and input pointers are the bases of
  two distinct arrays of frame slots, the entry state of the call has the disjoint regions
  `KernelRegions`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLinkedFn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect (NfTy)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode lane getLsbD_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState AMem read64 InRange8 Disjoint8)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (readBytes getLsbD_readBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage (VecAsm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage (lineBytes frameEnc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink (VecKernelCallee)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig CalleeSpec InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (CallerSep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf entryOf_regs retWord)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout AbiArg ArgKind ResultKind wordsAt)
open CatCrypt.Crypto.SecureCompilation.CT (DoitRegime)
open CatCrypt.Crypto.Hax (LinkedFn insVals)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open _root_.Hax (Value)

/-! ## 1. Lanes of a 64-byte read -/

/-- **Lane `k < 8` of a 64-byte read is a word.** Lane `k` of width `64` of the 64 bytes of
    `mem` from `a` is the little-endian word at `a + 8 k`. -/
theorem lane_readBytes (mem : AMem) (a : BitVec 64) {k : Nat} (hk : k < 8) :
    lane 64 (readBytes 64 mem a) k = read64 mem (a + BitVec.ofNat 64 (8 * k)) := by
  rw [CatCrypt.Crypto.SecureCompilation.Ascent.Footprint.read64_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_lane, getLsbD_readBytes]
  have hq : (64 * k + i) / 8 = 8 * k + i / 8 := by omega
  have hr : (64 * k + i) % 8 = i % 8 := by omega
  have haddr : ∀ j : Nat, a + BitVec.ofNat 64 (8 * k + j) =
      a + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j := by
    intro j
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hq, hr, haddr]
  simp only [hi, decide_true, Bool.true_and, show 64 * k + i < 512 by omega,
    show 8 * k + i / 8 < 64 by omega]
  generalize a + BitVec.ofNat 64 (8 * k) = b
  simp only [CatCrypt.Crypto.SecureCompilation.MachineMem64.read64, BitVec.getLsbD_cast,
    BitVec.getLsbD_append]
  interval_cases i <;> simp

/-! ## 2. The linked function of a vector kernel -/

/-- The number of words of the output region of a kernel of `nOut` outputs in the mode `m`:
    `m.stride / 8` words per output. -/
def outWords (m : Mode) (nOut : Nat) : Nat := m.stride / 8 * nOut

/-- The output region of a kernel is `8` bytes per word. -/
theorem eight_mul_outWords (m : Mode) (nOut : Nat) : 8 * outWords m nOut = m.stride * nOut := by
  rcases Mode.act_cases m with h | h <;>
    simp only [outWords, CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel.Mode.stride, h] <;>
    omega

/-- **The layout of a vector kernel in the destination-argument convention**: the parameter
    `outN`, the `nw` words at `%rdi`, then the parameter `inN`, the `ni` words at `%rsi`; the
    result is the `nw` words at the entry value of `%rdi`; no constants and no bounds; the
    stack words of the frame of `F` bytes below the entry stack register. -/
def vecOutLayout (outN inN : String) (nw ni F : Nat) : AbiLayout where
  args := [⟨outN, "%rdi", .words nw⟩, ⟨inN, "%rsi", .words ni⟩]
  consts := []
  result := .words "%rdi" nw
  bounds := []
  frameLo := -(F : Int)
  frameHi := -8

/-- **The meaning of a vector kernel on source values.** Let `sem` be defined at the source
    arrays of the `nw` words at `%rdi` and the `ni` words at `%rsi` of an entry state `s`,
    with the value `v`. Then the input region of `s` holds the parameters of the scalar
    program `c` lane-wise for some valuations `Vs`, and every state whose output region holds
    lane-wise the outputs of `c` on `Vs` holds `v` as the source array of the `nw` words at
    the entry value of `%rdi`. -/
def VecOutSem (V : VecShape) (inOffset : Nat → Nat) (inBound : Option Nat) (nOut : Nat)
    {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (nw ni : Nat)
    (sem : List Value → Option Value) : Prop :=
  ∀ (s : AState) (v : Value),
    sem [.array (wordsAt s.mem (s.regs "%rdi") nw), .array (wordsAt s.mem (s.regs "%rsi") ni)]
      = some v →
    ∃ Vs : Nat → Ctxt.Valuation Γ, LaneInputs V inOffset inBound Vs s ∧
      ∀ s' : AState, LaneOutputs V nOut c Vs s s' → v = .array (wordsAt s'.mem (s.regs "%rdi") nw)

variable {r : DoitRegime} {V : VecShape} {inOffset : Nat → Nat} {inBound : Option Nat}
  {nOut : Nat} {Γ : JCtxt} {t : JasminTy} {c : Com jasminDialect Γ t} {inLen F : Nat}

/-- **The linked function of a spec-carrying vector kernel**, in the destination-argument
    convention. Its name is `name`; its parameters are the destination `outN` and the input
    `inN`, arrays of `outWords V.mode nOut` and `ni` words; its result type is the
    destination array type; its meaning is `sem`, related to the kernel contract by
    `VecOutSem`; its layout is `vecOutLayout`; its precondition is `KernelRegions`; its
    footprint, postcondition and public relation are those of `kernelSig`; it clobbers
    `%rax`, uses a frame of `F` bytes, and its machine code is the bytes of the block of the
    kernel under the table `A`. -/
def _root_.CatCrypt.Crypto.Hax.LinkedFn.ofVecOut (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    (k : VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F))
    (A : VecAsm) : LinkedFn where
  name := name
  params := [(outN, .arr (outWords V.mode nOut) (.word 64)), (inN, .arr ni (.word 64))]
  res := .arr (outWords V.mode nOut) (.word 64)
  sem := sem
  sem_res := sem_res
  layout := vecOutLayout outN inN (outWords V.mode nOut) ni F
  pre := KernelRegions V.mode inLen nOut F
  foot := (kernelSig V inOffset inBound nOut c inLen F).foot
  post := (kernelSig V inOffset inBound nOut c inLen F).post
  pub := (kernelSig V inOffset inBound nOut c inLen F).pub
  pub_of_regs s₁ s₂ hrsp hregs :=
    ⟨hregs ⟨inN, "%rsi", .words ni⟩ (by simp [vecOutLayout]) rfl,
      hregs ⟨outN, "%rdi", .words (outWords V.mode nOut)⟩ (by simp [vecOutLayout]) rfl, hrsp⟩
  post_sem sa sa' v _ hpost hv := by
    obtain ⟨Vs, hin, hout⟩ := hsem sa v hv
    exact hout sa' (hpost Vs hin)
  clob := ["%rax"]
  frame := F
  bytes := lineBytes A frameEnc k.ops

/-- The parameters of the out interface of `LinkedFn.ofVecOut`: the destination of
    `outWords V.mode nOut` words at `RDI`, then the input of `ni` words at `RSI`. -/
def vecOutIns (nw ni : Nat) : List (String × ArgKind) := [("RDI", .words nw), ("RSI", .words ni)]

theorem phys_RDI : phys "RDI" = "%rdi" := by decide

theorem phys_RSI : phys "RSI" = "%rsi" := by decide

/-- **The out layout of a vector kernel.** `LinkedFn.ofVecOut` has the out layout with the
    parameters `vecOutIns`, the destination at `RDI` of `outWords V.mode nOut` words. -/
theorem ofVecOut_outLayout (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    (k : VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F)) (A : VecAsm) :
    OutLayout (LinkedFn.ofVecOut name outN inN ni sem sem_res hsem k A)
      (vecOutIns (outWords V.mode nOut) ni) "RDI" (outWords V.mode nOut) where
  args := by simp [LinkedFn.ofVecOut, vecOutLayout, vecOutIns, phys_RDI, phys_RSI]
  dest := rfl
  result := by simp [LinkedFn.ofVecOut, vecOutLayout, phys_RDI]
  ins_gp p hp := by
    simp only [vecOutIns, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (by decide : DecodePrinted.gpOk "RDI" = true)
    · exact (by decide : DecodePrinted.gpOk "RSI" = true)
  foot s x hx := by
    rcases hx with hx | hx
    · refine Or.inr ⟨(x - s.regs "%rdi").toNat / 8, ?_, ?_⟩
      · have := eight_mul_outWords V.mode nOut
        omega
      · rw [phys_RDI]
        unfold InRange8
        bv_omega
    · exact Or.inl hx

/-- **The callee of a vector kernel meets the out interface of its linked function.** The
    callee of `k` meets `outSig` of `LinkedFn.ofVecOut` at the parameters `vecOutIns`: an
    entry state at which the array result of the summary is defined satisfies the
    precondition of `kernelSig` by `VecOutSem`, and the other fields are those of
    `kernelSig`. -/
theorem ofVecOut_calleeSpec (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    (k : VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F)) (A : VecAsm) :
    CalleeSpec k.run (outSig (LinkedFn.ofVecOut name outN inN ni sem sem_res hsem k A)
      (vecOutIns (outWords V.mode nOut) ni) (outWords V.mode nOut)) := by
  have hL := ofVecOut_outLayout name outN inN ni sem sem_res hsem k A
  have hP : ∀ s, (outSig (LinkedFn.ofVecOut name outN inN ni sem sem_res hsem k A)
      (vecOutIns (outWords V.mode nOut) ni) (outWords V.mode nOut)).pre s →
      (kernelSig V inOffset inBound nOut c inLen F).pre s := by
    rintro s ⟨hreg, hd⟩
    change ((sem (insVals _ (readIns _ s))).bind _).isSome = true at hd
    rw [← read_outLayout hL s] at hd
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind hd)
    obtain ⟨Vs, hin, -⟩ := hsem s v hv
    exact ⟨hreg, Vs, hin⟩
  have hX := CalleeSpec.restrictPre k.spec hP
  exact
    { halts := hX.halts
      rsp := hX.rsp
      keep := fun s t s' h hr x hx => hX.keep s t s' h hr x (by
        simpa [LinkedFn.ofVecOut, outSig, kernelSig] using hx)
      frame := hX.frame
      post := hX.post
      ct := hX.ct }

/-! ## 3. The disjoint regions at a call site -/

/-- **The regions of a vector kernel at a call site.** Let `ImgSep` and `CallerSep` hold at
    the stack register `rsp` for the frame size `F`, let the destination pointer and the input
    pointer of the byte state `sA`, whose stack register is `rsp`, be the bases of two
    distinct arrays `D` and `B` of frame slots, of `nd` and `nb` words, with the output region
    of the kernel within `D`, its input region within `B`, and the output region and the frame
    at most `2 ^ 64` bytes. Then for every return index the
    entry state of the call has the disjoint regions `KernelRegions`. -/
theorem room_of_callSite {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep frame slotArr base rsp) (hS : CallerSep frame slotArr base rsp F)
    {m : Mode} {qd qb D B : String} {nd nb : Nat} (hd : slotArr qd = some (D, nd))
    (hb : slotArr qb = some (B, nb)) (hDB : D ≠ B) (hout : m.stride * nOut ≤ 8 * nd)
    (hin : inLen ≤ 8 * nb) (hle : m.stride * nOut ≤ 2 ^ 64) (hF : F ≤ 2 ^ 64) {sA : AState} (hsp : sA.regs "%rsp" = rsp)
    (hrdi : sA.regs "%rdi" = base D) (hrsi : sA.regs "%rsi" = base B) (ret : Nat) :
    KernelRegions m inLen nOut F (entryOf ret sA) := by
  have hdis : ∀ {a w x : BitVec 64}, Disjoint8 a w → InRange8 w x → ¬ InRange8 a x := by
    intro a w x hd hx ha
    obtain ⟨h1, h2⟩ := hd
    unfold InRange8 at hx ha
    simp only [BitVec.toNat_sub] at h1 h2 hx ha
    have := a.isLt
    have := w.isLt
    have := x.isLt
    omega
  have hcell : ∀ (p : BitVec 64) (i : Nat), InRange8 (cellAt p (i / 8)) (p + BitVec.ofNat 64 i) := by
    intro p i
    unfold InRange8 cellAt
    have : (8 * (i / 8)) ≤ i := Nat.mul_div_le i 8
    bv_omega
  have he : (entryOf ret sA).regs "%rsp" = rsp + BitVec.ofInt 64 (-8) := by
    rw [entryOf_regs, if_pos rfl, retWord, hsp]
  have h1 : (entryOf ret sA).regs "%rdi" = base D := by
    rw [entryOf_regs, if_neg (by decide), hrdi]
  have h2 : (entryOf ret sA).regs "%rsi" = base B := by
    rw [entryOf_regs, if_neg (by decide), hrsi]
  have hfr : ∀ x : BitVec 64, ∀ j < F,
      x = rsp + BitVec.ofInt 64 (-8) - BitVec.ofNat 64 F + BitVec.ofNat 64 j →
      InFrame (rsp + BitVec.ofInt 64 (-8)) F x := by
    intro x j hj hx
    unfold InFrame
    subst hx
    have e : BitVec.ofInt 64 (-(F : Int)) = - BitVec.ofNat 64 F := by
      rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
    rw [e]
    bv_omega
  refine ⟨?_, ?_, ?_, hle, hF⟩
  · intro i hi j hj heq
    rw [h1, h2] at heq
    have hc := hcell (base D) i
    rw [heq] at hc
    exact hdis (hsep.cells qd D nd qb B nb (i / 8) (j / 8) hd hb (by omega) (by omega)
      (Or.inl hDB)) (hcell (base B) j) hc
  · intro i hi j hj heq
    rw [h1, he] at heq
    exact (hS.cells qd D nd (i / 8) hd (by omega) _ (hcell (base D) i)).2
      (hfr _ j hj heq)
  · intro i hi j hj heq
    rw [h2, he] at heq
    exact (hS.cells qb B nb (j / 8) hb (by omega) _ (hcell (base B) j)).2
      (hfr _ i hi heq.symm)

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLinkedFn
