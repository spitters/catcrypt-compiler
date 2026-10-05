/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.FootprintEA
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-!
# The footprint layer on the shipped `ed25519_sc_reduce`

`Ed25519ScReduceShippedProof.footOK K blk` and `footOKP P blk` state that every cell of
`AddrMem.footprint blk` lies in `K`, respectively satisfies `P`. This module states both
as instances of the footprint layer and derives the footprint checks of the shipped
`ed25519_sc_reduce` block from `Footprint.footCheckFrom`, the one-pass check of the
discipline and the cells, evaluated by the kernel.

## Main results

* `footOKP_iff`, `footOK_iff`: the two predicates in terms of `AddrMem.footprint`.
* `footOK_of_footCheckFrom`: the one-pass check gives `footOK` of the canonical block.
* `scr_footCheck1` … `scr_footCheck8`, `scr_footCheck`: the one-pass check of each of the
  eight parts against `scrCells`, by kernel evaluation, and of the whole block.
* `scr_foot8_decide`, `scr_foot_decide`, `scReduce_disciplinedD_decide`: the statements of
  `Ed25519ScReduceShippedProof.scr_foot8`, `scr_foot` and
  `AddrMemDerived.ed25519ScReduce_disciplinedD`, from the one-pass check.
* `scReduceShipped_frame`: when the cells of `scrCells` are separated, the block changes
  no byte outside their word ranges.
* `scReduceShipped_local`: the registers, the flags and the bytes of those ranges after
  the block depend only on the registers, the flags and the bytes of those ranges.
* `scReduceShipped_read_frame_ea`: a read through an effective-address operand whose word
  is disjoint from the word ranges of `scrCells` is unchanged by the block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.FootprintDemo

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
open CatCrypt.Crypto.SecureCompilation.Ascent.FootprintEA
open CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddr
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-- `footOKP P blk` states `P` at every cell of the footprint of `blk`. -/
theorem footOKP_iff (P : String × Int → Bool) (blk : List (JInstr 64)) :
    footOKP P blk = true ↔ ∀ k ∈ AddrMem.footprint blk, P k = true := by
  simp only [footOKP, List.all_eq_true, Bool.and_eq_true, AddrMem.footprint, writeKeys,
    List.mem_append, List.mem_filterMap]
  constructor
  · rintro h k (⟨i, hi, hk⟩ | ⟨i, hi, hk⟩)
    · have := (h i hi).1
      rw [hk] at this
      exact this
    · have := (h i hi).2
      rw [hk] at this
      exact this
  · intro h i hi
    constructor
    · cases hr : readKey i with
      | none => rfl
      | some k => exact h k (Or.inl ⟨i, hi, hr⟩)
    · cases hw : writeKey i with
      | none => rfl
      | some k => exact h k (Or.inr ⟨i, hi, hw⟩)

/-- `footOK K blk` states that the footprint of `blk` lies in `K`. -/
theorem footOK_iff (K : List (String × Int)) (blk : List (JInstr 64)) :
    footOK K blk = true ↔ ∀ k ∈ AddrMem.footprint blk, k ∈ K := by
  have h := footOKP_iff (fun k => decide (k ∈ K)) blk
  simp only [decide_eq_true_eq] at h
  exact h

/-- The one-pass check against membership in `K` gives `footOK K` of the canonical
    block. -/
theorem footOK_of_footCheckFrom {bank : String → Option String} {K : List (String × Int)}
    {Pc : String × Int → Bool} (hPc : ∀ k, Pc k = true → k ∈ K)
    {A : DState} {blk : List (JInstr 64)} (h : footCheckFrom bank Pc A blk = true) :
    footOK K (canonFromD bank A blk) = true :=
  (footOK_iff K _).2 fun k hk => hPc k ((footCheckFrom_sound bank Pc blk A h).2 k hk)

/-! ## The eight parts of `ed25519_sc_reduce` -/

/-- Membership in `scrCells`, the predicate the one-pass check evaluates at each cell. -/
def scrCellB (k : String × Int) : Bool := decide (k ∈ scrCells)

theorem scrCellB_mem (k : String × Int) (h : scrCellB k = true) : k ∈ scrCells :=
  of_decide_eq_true h

theorem scr_footCheck1 :
    footCheckFrom shippedBank scrCellB {} ed25519ScReduceShippedPart01 = true := by
  decide +kernel
theorem scr_footCheck2 :
    footCheckFrom shippedBank scrCellB (scrState 1) ed25519ScReduceShippedPart02 = true := by
  decide +kernel
theorem scr_footCheck3 :
    footCheckFrom shippedBank scrCellB (scrState 2) ed25519ScReduceShippedPart03 = true := by
  decide +kernel
theorem scr_footCheck4 :
    footCheckFrom shippedBank scrCellB (scrState 3) ed25519ScReduceShippedPart04 = true := by
  decide +kernel
theorem scr_footCheck5 :
    footCheckFrom shippedBank scrCellB (scrState 4) ed25519ScReduceShippedPart05 = true := by
  decide +kernel
theorem scr_footCheck6 :
    footCheckFrom shippedBank scrCellB (scrState 5) ed25519ScReduceShippedPart06 = true := by
  decide +kernel
theorem scr_footCheck7 :
    footCheckFrom shippedBank scrCellB (scrState 6) ed25519ScReduceShippedPart07 = true := by
  decide +kernel
theorem scr_footCheck8 :
    footCheckFrom shippedBank scrCellB (scrState 7) ed25519ScReduceShippedPart08 = true := by
  decide +kernel

/-- The statement of `Ed25519ScReduceShippedProof.scr_foot8`, by the one-pass check. -/
theorem scr_foot8_decide :
    footOK scrCells (canonFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08) =
      true :=
  footOK_of_footCheckFrom scrCellB_mem scr_footCheck8

/-- The one-pass check of the whole block, from the checks of its parts and the abstract
    states between them. -/
theorem scr_footCheck :
    footCheckFrom shippedBank scrCellB {} ed25519ScReduceShippedBlock = true := by
  unfold ed25519ScReduceShippedBlock
  simp only [List.append_assoc]
  rw [footCheckFrom_append, scReduce_D_part01.2, footCheckFrom_append, scReduce_D_part02.2,
    footCheckFrom_append, scReduce_D_part03.2, footCheckFrom_append, scReduce_D_part04.2,
    footCheckFrom_append, scReduce_D_part05.2, footCheckFrom_append, scReduce_D_part06.2,
    footCheckFrom_append, scReduce_D_part07.2]
  simp only [scr_footCheck1, scr_footCheck2, scr_footCheck3, scr_footCheck4, scr_footCheck5,
    scr_footCheck6, scr_footCheck7, scr_footCheck8, Bool.and_self]

/-- The statement of `Ed25519ScReduceShippedProof.scr_foot`, by the one-pass check. -/
theorem scr_foot_decide :
    footOK scrCells (canonD shippedBank ed25519ScReduceShippedBlock) = true :=
  footOK_of_footCheckFrom scrCellB_mem scr_footCheck

/-- The statement of `AddrMemDerived.ed25519ScReduce_disciplinedD`, by the one-pass
    check. -/
theorem scReduce_disciplinedD_decide :
    disciplinedD shippedBank ed25519ScReduceShippedBlock = true :=
  (footCheckFrom_sound shippedBank scrCellB _ {} scr_footCheck).1

/-- **Frame of the shipped `ed25519_sc_reduce`.** When the cells of `scrCells` occupy
    pairwise disjoint eight-byte ranges, the block changes no byte outside the word ranges
    of those cells. -/
theorem scReduceShipped_frame (sa : AState) (hsep : Separated shippedBank sa.regs scrCells)
    (x : BitVec 64) (hx : ∀ k ∈ scrCells, x ∉ cellRng shippedBank sa.regs k) :
    (runBlockA sa ed25519ScReduceShippedBlock).mem x = sa.mem x := by
  obtain ⟨F, hF, -, hw⟩ := cellFootprint_of_footCheck scr_footCheck
  have hmem : ∀ k ∈ F.writes, k ∈ scrCells := fun k hk => scrCellB_mem k (hw k hk)
  exact footprint_sound hF sa
    (fun k hk k' hk' hne => hsep k (hmem k hk) k' (hmem k' hk') hne) x
    (fun k hk => hx k (hmem k hk))

/-- **Locality of the shipped `ed25519_sc_reduce`.** A state with the registers and flags
    of `sa` that agrees with it on the word ranges of the cells of `scrCells` runs to the
    same registers and flags, and to the same bytes on those ranges. -/
theorem scReduceShipped_local (sa sb : AState)
    (hsep : Separated shippedBank sa.regs scrCells) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ k ∈ scrCells, ∀ x, x ∈ cellRng shippedBank sa.regs k → sb.mem x = sa.mem x) :
    (runBlockA sb ed25519ScReduceShippedBlock).regs =
        (runBlockA sa ed25519ScReduceShippedBlock).regs ∧
      (runBlockA sb ed25519ScReduceShippedBlock).flags =
        (runBlockA sa ed25519ScReduceShippedBlock).flags ∧
      ∀ k ∈ scrCells, ∀ x, x ∈ cellRng shippedBank sa.regs k →
        (runBlockA sb ed25519ScReduceShippedBlock).mem x =
          (runBlockA sa ed25519ScReduceShippedBlock).mem x := by
  obtain ⟨F, hF, hrd, hw⟩ := cellFootprint_of_footCheck scr_footCheck
  have hmemW : ∀ k ∈ F.writes, k ∈ scrCells := fun k hk => scrCellB_mem k (hw k hk)
  have hmemR : ∀ k ∈ F.reads, k ∈ scrCells := fun k hk => scrCellB_mem k (hrd k hk)
  obtain ⟨h1, h2, h3, -⟩ := footprint_sound_reads hF sa sb
    (fun k hk k' hk' hne => hsep k (hmemW k hk) k' (hmemW k' hk') hne) hr hf
    (fun k hk => hm k (hmemR k hk))
  exact ⟨h1, h2, fun k hk x hx => h3 x (hm k hk x hx)⟩

/-- **Frame of the shipped `ed25519_sc_reduce` on an operand.** When the cells of
    `scrCells` are separated, the word at the address an effective-address operand `e`
    denotes at entry, disjoint from the word range of every cell of `scrCells`, is
    unchanged by the block. -/
theorem scReduceShipped_read_frame_ea (sa : AState)
    (hsep : Separated shippedBank sa.regs scrCells) (e : EA)
    (hd : ∀ k ∈ scrCells, (cellRng shippedBank sa.regs k).Disj (eaRng sa 8 e)) :
    read64 (runBlockA sa ed25519ScReduceShippedBlock).mem (eaVal sa e) =
      read64 sa.mem (eaVal sa e) :=
  footCheckFrom_frame_ea scr_footCheck sa
    (fun k k' hk hk' hne => hsep k (scrCellB_mem k hk) k' (scrCellB_mem k' hk') hne) e
    (fun k hk => hd k (scrCellB_mem k hk))

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.FootprintDemo
