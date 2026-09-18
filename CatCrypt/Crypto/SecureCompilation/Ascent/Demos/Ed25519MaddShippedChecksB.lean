/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedChecksA

/-!
# The fifteen calls of the shipped `ed25519_madd`

The block's eighteen segments are taken one at a time by `maddTail` and `mg`, the entry
segment establishes the state description of `Ed25519MaddShippedChecksA`, and the
fourteen field calls and the concatenation call extend it to the four coordinates in the
result block at `%rsp + 448`.

## Main definitions

* `maddTail k`, `mg k`: the segments of the block from the `k`-th on, and the `k`-th
  segment.
* `maddSlots`: the fourteen intermediate field elements of the mixed addition, by slot
  index, each reduced modulo `2 ^ 255 - 19`.
* `maddSpecN`: the four coordinates of the mixed addition, the last four slots.
* `maddIn`, `maddSV`: the input coordinates of a state and the value table on them.

## Main results

* `segsRunA_tail_call`, `segsRunA_tail_plain`: one segment of the run.
* `maddEntry`: the entry segment establishes the state description.
* `maddCallsRun`: after the fifteen calls the result block holds the four coordinates.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym addSym subSym join16Sym)

/-! ## 11. The segments of the block, one at a time -/

/-- The segments of the block from the `k`-th on. -/
def maddTail (k : Nat) : List CallSeg := ed25519MaddShippedBlock.drop k

/-- The `k`-th segment of the block. -/
def mg (k : Nat) : CallSeg := ed25519MaddShippedBlock.getD k ⟨[], none⟩

theorem maddTail_zero : maddTail 0 = ed25519MaddShippedBlock := rfl

theorem tail_succ (k : Nat) (h : k < 18) : maddTail k = mg k :: maddTail (k + 1) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

theorem segsRunA_tail_call (C : ACallModel) (s : AState) (k : Nat) (h : k < 18) (f : String)
    (hf : (mg k).callee = some f) :
    segsRunA C s (maddTail k)
      = segsRunA C (C f (runBlockA s (mg k).body)) (maddTail (k + 1)) := by
  rw [tail_succ k h]
  simp only [segsRunA, hf]

theorem segsRunA_tail_plain (C : ACallModel) (s : AState) (k : Nat) (h : k < 18)
    (hf : (mg k).callee = none) :
    segsRunA C s (maddTail k) = segsRunA C (runBlockA s (mg k).body) (maddTail (k + 1)) := by
  rw [tail_succ k h]
  simp only [segsRunA, hf]

/-! ## 12. The value table of the mixed addition -/

/-- The fourteen intermediate field elements of the mixed addition, by slot index,
    each reduced modulo `pM`. -/
def maddSlots (x1 y1 z1 t1 ypx ymx t2d : Nat) : Nat → Nat := fun i =>
  let s1 := (y1 + x1) % pM
  let a := (s1 * ypx) % pM
  let s2 := (y1 + (pM - x1)) % pM
  let b := (s2 * ymx) % pM
  let c := (t1 * t2d) % pM
  let dd := (z1 + z1) % pM
  let e := (a + (pM - b)) % pM
  let h := (a + b) % pM
  let g := (dd + c) % pM
  let f := (dd + (pM - c)) % pM
  match i with
  | 0 => s1
  | 1 => a
  | 2 => s2
  | 3 => b
  | 4 => c
  | 5 => dd
  | 6 => e
  | 7 => h
  | 8 => g
  | 9 => f
  | 10 => (e * f) % pM
  | 11 => (h * g) % pM
  | 12 => (g * f) % pM
  | _ => (e * h) % pM

theorem maddSlots_lt (x1 y1 z1 t1 ypx ymx t2d : Nat) (i : Nat) :
    maddSlots x1 y1 z1 t1 ypx ymx t2d i < pM := by
  simp only [maddSlots]
  split <;> exact Nat.mod_lt _ pM_pos

/-- The four coordinates of the mixed addition: the last four intermediate slots. -/
def maddSpecN (x1 y1 z1 t1 ypx ymx t2d : Nat) : Nat × Nat × Nat × Nat :=
  (maddSlots x1 y1 z1 t1 ypx ymx t2d 10, maddSlots x1 y1 z1 t1 ypx ymx t2d 11,
   maddSlots x1 y1 z1 t1 ypx ymx t2d 12, maddSlots x1 y1 z1 t1 ypx ymx t2d 13)

/-- The value of input coordinate `j`: the four limbs at `%rsi + 32 j`. -/
def maddIn (sa : AState) (j : Nat) : Nat := feO sa.mem (sa.regs "%rsi") (slotOff j)

/-! ## 13. The entry segment -/

theorem feO_write_disj (m : AMem) (a v p : BitVec 64) (o : Int)
    (hd : ∀ j ∈ limbOffs, Disjoint8 a (p + BitVec.ofInt 64 (o + j))) :
    feO (write64 m a v) p o = feO m p o :=
  congrArg bignumVal (List.map_congr_left fun j hj =>
    read64_write64_of_disjoint _ _ _ _ (hd j hj))

/-- The entry segment establishes the state description with no intermediate slot. -/
theorem maddEntry (sa : AState) (hX : CrossIn (sa.regs "%rsp") (sa.regs "%rsi"))
    (SV : Nat → Nat) :
    MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") SV (maddIn sa) 0
      (runBlockA sa (mg 0).body) := by
  obtain ⟨hr, hm⟩ := runEntry sa
  have hmm : (runBlockA sa (mg 0).body).mem
      = write64 (write64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 576) (sa.regs "%rsi"))
        (sa.regs "%rsp" + BitVec.ofInt 64 584) (sa.regs "%rdi") := hm
  have hrr : (runBlockA sa (mg 0).body).regs = sa.regs := hr
  refine ⟨by rw [hrr], by intro i hi; omega, ?_, ?_, ?_⟩
  · intro j hj
    rw [hmm]
    rw [feO_write_disj _ _ _ _ _ (by
        intro u hu
        simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hu
        refine hX 584 _ (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
          simp only [slotOff] <;> rcases hu with rfl | rfl | rfl | rfl <;> omega)]
    rw [feO_write_disj _ _ _ _ _ (by
        intro u hu
        simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hu
        refine hX 576 _ (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
          simp only [slotOff] <;> rcases hu with rfl | rfl | rfl | rfl <;> omega)]
    rfl
  · rw [hmm, read64_write64_of_disjoint _ _ _ _ (djSS _ 584 576 (by decide) (by decide)),
      read64_write64_same]
  · rw [hmm, read64_write64_same]

/-! ## 14. The fifteen calls -/

/-- The value table of the mixed addition on the block's input point. -/
def maddSV (sa : AState) : Nat → Nat :=
  maddSlots (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
    (maddIn sa 5) (maddIn sa 6)

theorem maddSV_lt (sa : AState) (i : Nat) : maddSV sa i < pM := maddSlots_lt _ _ _ _ _ _ _ i

/-- After the fifteen calls the result block at `%rsp + 448` holds the four coordinates
    of the mixed addition and the output pointer is still in its slot. -/
theorem maddCallsRun {C : ACallModel} (hC : MaddCallees C) (sa : AState)
    (hX : CrossIn (sa.regs "%rsp") (sa.regs "%rsi"))
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    ∃ s : AState,
      segsRunA C sa ed25519MaddShippedBlock = segsRunA C s (maddTail 16)
        ∧ s.regs "%rsp" = sa.regs "%rsp"
        ∧ read64 s.mem (sa.regs "%rsp" + BitVec.ofInt 64 584) = sa.regs "%rdi"
        ∧ feO s.mem (sa.regs "%rsp") 448 = maddSV sa 10
        ∧ feO s.mem (sa.regs "%rsp") 480 = maddSV sa 11
        ∧ feO s.mem (sa.regs "%rsp") 512 = maddSV sa 12
        ∧ feO s.mem (sa.regs "%rsp") 544 = maddSV sa 13 := by
  obtain ⟨hadd, hsub, hmul, hjoin⟩ := hC
  obtain ⟨s0, hs0⟩ : ∃ s, runBlockA sa (mg 0).body = s := ⟨_, rfl⟩
  have i0 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 0 s0 := by rw [← hs0]; exact maddEntry sa hX _
  obtain ⟨s1, hs1⟩ : ∃ s, C addSym (runBlockA s0 (mg 1).body) = s := ⟨_, rfl⟩
  have i1 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 1 s1 := by
    rw [← hs1]
    exact stepRR hadd (by omega) hX i0 0 32 0 1 0 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (hb 1 (by omega)) (hb 0 (by omega)) rfl
  obtain ⟨s2, hs2⟩ : ∃ s, C mulSym (runBlockA s1 (mg 2).body) = s := ⟨_, rfl⟩
  have i2 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 2 s2 := by
    rw [← hs2]
    exact stepSR hmul (by omega) hX i1 32 0 128 0 4 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 0) (hb 4 (by omega)) rfl
  obtain ⟨s3, hs3⟩ : ∃ s, C subSym (runBlockA s2 (mg 3).body) = s := ⟨_, rfl⟩
  have i3 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 3 s3 := by
    rw [← hs3]
    exact stepRR hsub (by omega) hX i2 64 32 0 1 0 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (hb 1 (by omega)) (hb 0 (by omega)) rfl
  obtain ⟨s4, hs4⟩ : ∃ s, C mulSym (runBlockA s3 (mg 4).body) = s := ⟨_, rfl⟩
  have i4 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 4 s4 := by
    rw [← hs4]
    exact stepSR hmul (by omega) hX i3 96 64 160 2 5 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 2) (hb 5 (by omega)) rfl
  obtain ⟨s5, hs5⟩ : ∃ s, C mulSym (runBlockA s4 (mg 5).body) = s := ⟨_, rfl⟩
  have i5 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 5 s5 := by
    rw [← hs5]
    exact stepRR hmul (by omega) hX i4 128 96 192 3 6 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (hb 3 (by omega)) (hb 6 (by omega)) rfl
  obtain ⟨s6, hs6⟩ : ∃ s, C addSym (runBlockA s5 (mg 6).body) = s := ⟨_, rfl⟩
  have i6 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 6 s6 := by
    rw [← hs6]
    exact stepRR hadd (by omega) hX i5 160 64 64 2 2 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (hb 2 (by omega)) (hb 2 (by omega)) rfl
  obtain ⟨s7, hs7⟩ : ∃ s, C subSym (runBlockA s6 (mg 7).body) = s := ⟨_, rfl⟩
  have i7 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 7 s7 := by
    rw [← hs7]
    exact stepSS hsub (by omega) hX i6 192 32 96 1 3 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 1) (maddSV_lt sa 3) rfl
  obtain ⟨s8, hs8⟩ : ∃ s, C addSym (runBlockA s7 (mg 8).body) = s := ⟨_, rfl⟩
  have i8 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 8 s8 := by
    rw [← hs8]
    exact stepSS hadd (by omega) hX i7 224 32 96 1 3 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 1) (maddSV_lt sa 3) rfl
  obtain ⟨s9, hs9⟩ : ∃ s, C addSym (runBlockA s8 (mg 9).body) = s := ⟨_, rfl⟩
  have i9 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 9 s9 := by
    rw [← hs9]
    exact stepSS hadd (by omega) hX i8 256 160 128 5 4 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 5) (maddSV_lt sa 4) rfl
  obtain ⟨s10, hs10⟩ : ∃ s, C subSym (runBlockA s9 (mg 10).body) = s := ⟨_, rfl⟩
  have i10 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 10 s10 := by
    rw [← hs10]
    exact stepSS hsub (by omega) hX i9 288 160 128 5 4 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 5) (maddSV_lt sa 4) rfl
  obtain ⟨s11, hs11⟩ : ∃ s, C mulSym (runBlockA s10 (mg 11).body) = s := ⟨_, rfl⟩
  have i11 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 11 s11 := by
    rw [← hs11]
    exact stepSS hmul (by omega) hX i10 320 192 288 6 9 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 6) (maddSV_lt sa 9) rfl
  obtain ⟨s12, hs12⟩ : ∃ s, C mulSym (runBlockA s11 (mg 12).body) = s := ⟨_, rfl⟩
  have i12 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 12 s12 := by
    rw [← hs12]
    exact stepSS hmul (by omega) hX i11 352 224 256 7 8 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 7) (maddSV_lt sa 8) rfl
  obtain ⟨s13, hs13⟩ : ∃ s, C mulSym (runBlockA s12 (mg 13).body) = s := ⟨_, rfl⟩
  have i13 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 13 s13 := by
    rw [← hs13]
    exact stepSS hmul (by omega) hX i12 384 256 288 8 9 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 8) (maddSV_lt sa 9) rfl
  obtain ⟨s14, hs14⟩ : ∃ s, C mulSym (runBlockA s13 (mg 14).body) = s := ⟨_, rfl⟩
  have i14 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 14 s14 := by
    rw [← hs14]
    exact stepSS hmul (by omega) hX i13 416 192 224 6 7 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff]) (maddSV_lt sa 6) (maddSV_lt sa 7) rfl
  obtain ⟨s15, hs15⟩ : ∃ s, C join16Sym (runBlockA s14 (mg 15).body) = s := ⟨_, rfl⟩
  obtain ⟨hj0, hj1, hj2, hj3, hj4, hj5⟩ : (C join16Sym (runBlockA s14 (mg 15).body)).regs "%rsp"
        = sa.regs "%rsp"
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 448 = maddSV sa 10
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 480 = maddSV sa 11
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 512 = maddSV sa 12
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 544 = maddSV sa 13
      ∧ read64 (C join16Sym (runBlockA s14 (mg 15).body)).mem
          (sa.regs "%rsp" + BitVec.ofInt 64 584) = sa.regs "%rdi" := by
    obtain ⟨hm, hsp, hdi, hsi, hdx, hcx, hr8⟩ := runArgsJoin s14 448 320 352 384 416
    rw [i14.rsp] at hsp hdi hsi hdx hcx hr8
    exact joinStep hjoin i14 hm hsp hdi hsi hdx hcx hr8
  refine ⟨s15, ?_, by rw [← hs15]; exact hj0, by rw [← hs15]; exact hj5,
    by rw [← hs15]; exact hj1, by rw [← hs15]; exact hj2, by rw [← hs15]; exact hj3,
    by rw [← hs15]; exact hj4⟩
  rw [← maddTail_zero, segsRunA_tail_plain C sa 0 (by omega) rfl, hs0,
    segsRunA_tail_call C s0 1 (by omega) addSym rfl, hs1,
    segsRunA_tail_call C s1 2 (by omega) mulSym rfl, hs2,
    segsRunA_tail_call C s2 3 (by omega) subSym rfl, hs3,
    segsRunA_tail_call C s3 4 (by omega) mulSym rfl, hs4,
    segsRunA_tail_call C s4 5 (by omega) mulSym rfl, hs5,
    segsRunA_tail_call C s5 6 (by omega) addSym rfl, hs6,
    segsRunA_tail_call C s6 7 (by omega) subSym rfl, hs7,
    segsRunA_tail_call C s7 8 (by omega) addSym rfl, hs8,
    segsRunA_tail_call C s8 9 (by omega) addSym rfl, hs9,
    segsRunA_tail_call C s9 10 (by omega) subSym rfl, hs10,
    segsRunA_tail_call C s10 11 (by omega) mulSym rfl, hs11,
    segsRunA_tail_call C s11 12 (by omega) mulSym rfl, hs12,
    segsRunA_tail_call C s12 13 (by omega) mulSym rfl, hs13,
    segsRunA_tail_call C s13 14 (by omega) mulSym rfl, hs14,
    segsRunA_tail_call C s14 15 (by omega) join16Sym rfl, hs15]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
