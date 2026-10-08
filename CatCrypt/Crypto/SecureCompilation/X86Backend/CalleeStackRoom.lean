/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame

@[expose] public section

set_option autoImplicit false

/-!
# The stack room of a callee from the layout of the caller

`ImageAddrCall.CallerSep` asks that no array word of a calling body meets the return word
of a call or the `G` bytes below it. With the frame of the body of size `Fc`, the return
word is the stack word at offset `-(Fc + 8)` from the entry `%rsp` and the `G` bytes below
it are at offsets `[-(Fc + 8 + G), -(Fc + 8))`. The entry precondition of the layout
(`AbiLayout.Regions`, conjunct three) keeps every array word disjoint from the stack words
at the offsets `[σ.frameLo, σ.frameHi]`. The check `stackRoomB` decides that these offsets
cover the return word and the `G` bytes below it, and `callerSep_of_regions` derives
`CallerSep` from it, from the entry precondition and from the frame check
`ImageAddrCall.frameNonnegB`.

## Main results

* `stackRoomB`: the frame range of the layout covers the return word and the `G` bytes
  below it.
* `byte_notInCell`: a byte of a word disjoint from every stack word of a range is not in a
  stack word of the range and not among the bytes below such a word inside the range.
* `callerSep_of_regions`: `CallerSep` from the layout.
* `footBelow_inFrame`, `footBelow_mono`: a callee whose footprint is the `F` bytes below its
  entry stack register satisfies `FootBelow` at every `G ≥ F`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeStackRoom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen regK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
  (rsOK abiBase abiReg frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8 InRange8)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
  (frameNonnegB frameAbove_of_frameNonnegB CallerSep FootBelow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig InFrame)

/-- **The stack room check.** The frame range `[σ.frameLo, σ.frameHi]` of the layout covers
    the offsets from the entry `%rsp` of the return word of a call from `body` and of the `G`
    bytes below it, with `Params.ofBody body` giving the frame size of the body. -/
def stackRoomB (σ : AbiLayout) (body : Lcmd) (G : Nat) : Bool :=
  decide (σ.frameLo ≤ -(((Params.ofBody body).frame : Int) + 8 + G)
    ∧ -(((Params.ofBody body).frame : Int) + 8) ≤ σ.frameHi)

/-- No byte lies in two disjoint eight-byte ranges. -/
theorem not_inRange8_of_disjoint8 {a w x : BitVec 64} (hd : Disjoint8 a w)
    (hx : InRange8 w x) : ¬ InRange8 a x := by
  intro ha
  obtain ⟨h1, h2⟩ := hd
  unfold InRange8 at hx ha
  simp only [BitVec.toNat_sub] at h1 h2 hx ha
  have := a.isLt
  have := w.isLt
  have := x.isLt
  omega

/-- **A byte of a word apart from a stack range.** Let the word at `w` be disjoint from every
    stack word `r + o` with `lo ≤ o ≤ hi`, and let `lo ≤ H - G` and `H ≤ hi`. A byte of the
    word at `w` is not a byte of the stack word `r + H` and not among the `G` bytes below
    `r + H`. -/
theorem byte_notInCell {r w x : BitVec 64} {lo hi H : Int} {G : Nat}
    (hd : ∀ o : Int, lo ≤ o → o ≤ hi → Disjoint8 (r + BitVec.ofInt 64 o) w)
    (hlo : lo ≤ H - G) (hhi : H ≤ hi) (hx : InRange8 w x) :
    ¬ InRange8 (r + BitVec.ofInt 64 H) x ∧ ¬ InFrame (r + BitVec.ofInt 64 H) G x := by
  refine ⟨not_inRange8_of_disjoint8 (hd H (by omega) hhi) hx, fun hF => ?_⟩
  unfold InFrame at hF
  set d := (x - (r + BitVec.ofInt 64 H + BitVec.ofInt 64 (-(G : Int)))).toNat with hdd
  have hxe : x = r + BitVec.ofInt 64 H + BitVec.ofInt 64 (-(G : Int)) + BitVec.ofNat 64 d := by
    rw [hdd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    ring
  apply not_inRange8_of_disjoint8 (hd (H - G + d) (by omega) (by omega)) hx
  have he : r + BitVec.ofInt 64 (H - G + d) = x := by
    rw [hxe, BitVec.ofInt_add, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_natCast]
    ring
  unfold InRange8
  rw [he, BitVec.sub_self]
  decide

/-- **The separation of a caller from the layout.** At the entry state `sa0` of a layout `σ`
    whose regions `rs` pass `rsOK`, under the entry precondition `σ.Regions sa0`, the stack
    room check and the frame check of the body, the restricted frame of the body, an array
    map whose arrays are the regions at their lengths, and the entry bases of the regions are
    separated at the stack register after the prologue. -/
theorem callerSep_of_regions {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true)
    {sa0 : AState} (h : σ.Regions sa0) {body : Lcmd} {G : Nat}
    (hr : stackRoomB σ body G = true) (hn : frameNonnegB body G = true)
    {slotArr : String → Option (String × Nat)}
    (hsl : ∀ q A n, slotArr q = some (A, n) → regLen rs A = n) :
    CallerSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) slotArr
      (abiBase (abiReg σ) sa0) (frameRsp body sa0) G := by
  refine ⟨frameAbove_of_frameNonnegB hn sa0, fun q A n j hq hj x hx => ?_⟩
  simp only [stackRoomB, decide_eq_true_eq] at hr
  have hk : regK rs A j := by
    unfold regK
    rw [hsl q A n hq]
    exact hj
  have hret : frameRsp body sa0 + BitVec.ofInt 64 (-8)
      = sa0.regs "%rsp" + BitVec.ofInt 64 (-(((Params.ofBody body).frame : Int) + 8)) := by
    simp only [frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
    congr 2
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hret]
  exact byte_notInCell (fun o h1 h2 => frameSep_of_regions hrs h A j hk o h1 h2)
    (by omega) hr.2 hx

/-- A callee whose footprint is the `F` bytes below its entry stack register satisfies
    `FootBelow` at `F`. -/
theorem footBelow_inFrame {c : CalleeSig} {F : Nat}
    (h : c.foot = fun s x => InFrame (s.regs "%rsp") F x) : FootBelow c F := by
  intro s x hx
  rw [h] at hx
  exact hx

/-- The `F` bytes below an address are among the `G` bytes below it, for `F ≤ G ≤ 2 ^ 64`. -/
theorem inFrame_mono {e x : BitVec 64} {F G : Nat} (hFG : F ≤ G) (hG : G ≤ 2 ^ 64)
    (h : InFrame e F x) : InFrame e G x := by
  unfold InFrame at h ⊢
  have hF : (F : Int) ≤ 2 ^ 64 := by omega
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at h ⊢
  have := e.isLt
  have := x.isLt
  omega

/-- `FootBelow` holds at every `G` from `F` up to `2 ^ 64`. -/
theorem footBelow_mono {c : CalleeSig} {F G : Nat} (h : FootBelow c F) (hFG : F ≤ G)
    (hG : G ≤ 2 ^ 64) : FootBelow c G :=
  fun s x hx => inFrame_mono hFG hG (h s x hx)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeStackRoom
