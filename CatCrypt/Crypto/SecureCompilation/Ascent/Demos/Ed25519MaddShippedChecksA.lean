/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedParts

/-!
# The state description of the shipped `ed25519_madd` across one call

The block keeps its intermediate field elements in the stack slots at `%rsp + 32 i`,
the input point at the pointer in the slot at `%rsp + 576` and the output pointer in
the slot at `%rsp + 584`. `MaddInv` is that description, and the theorems here carry it
across one field call, across the concatenation call and across the output copy.

## Main definitions

* `slotOff i`: the stack displacement `32 i` of intermediate field element `i`.
* `CrossIn`, `CrossOut`: the disjointness of a stack word from an input-point word and
  from an output word.
* `MaddInv`: the state description the block maintains between calls.
* `outOffs`: the sixteen word offsets of the output copy.

## Main results

* `invStep`: one field call extends the description by the slot it writes.
* `joinStep`: the concatenation call leaves the four coordinates in the 128-byte result
  block at `%rsp + 448`.
* `copyOut`: the copy leaves at the output pointer the sixteen words of that block.
* `stepRR`, `stepSR`, `stepSS`: `invStep` at each of the three argument shapes the
  block's call segments have.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (join16Sym)

/-! ## 8. The invariant across one call -/

/-- The stack slot of the intermediate field element `i`. -/
def slotOff (i : Nat) : Int := ((32 * i : Nat) : Int)

/-- The disjointness of a stack word and an input-point word. -/
def CrossIn (SP P : BitVec 64) : Prop :=
  ∀ o o' : Int, 0 ≤ o → o ≤ 584 → o % 8 = 0 → 0 ≤ o' → o' ≤ 216 → o' % 8 = 0 →
    Disjoint8 (SP + BitVec.ofInt 64 o) (P + BitVec.ofInt 64 o')

/-- The disjointness of a stack word and an output word. -/
def CrossOut (SP Q : BitVec 64) : Prop :=
  ∀ o o' : Int, 0 ≤ o → o ≤ 584 → o % 8 = 0 → 0 ≤ o' → o' ≤ 120 → o' % 8 = 0 →
    Disjoint8 (SP + BitVec.ofInt 64 o) (Q + BitVec.ofInt 64 o')

/-- The state between two calls: `%rsp` at `SP`, the first `k` intermediate slots at the
    values of `SV`, the seven input coordinates at `P` at the values of `IN`, and the two
    pointers in their slots. -/
structure MaddInv (SP P Q : BitVec 64) (SV IN : Nat → Nat) (k : Nat) (s : AState) : Prop where
  /-- The stack pointer. -/
  rsp : s.regs "%rsp" = SP
  /-- The intermediate field elements computed so far. -/
  slots : ∀ i, i < k → feO s.mem SP (slotOff i) = SV i
  /-- The seven input coordinates. -/
  inp : ∀ j, j < 7 → feO s.mem P (slotOff j) = IN j
  /-- The input pointer in its stack slot. -/
  ptrIn : read64 s.mem (SP + BitVec.ofInt 64 576) = P
  /-- The output pointer in its stack slot. -/
  ptrOut : read64 s.mem (SP + BitVec.ofInt 64 584) = Q

/-- A stack word outside the written slot survives a call. -/
theorem read64_stack_frame {m m' : AMem} {SP : BitVec 64} {d o : Int} {n : Nat}
    (hf : FrameC m m' (SP + BitVec.ofInt 64 d) n)
    (h : ∀ k, k < n → 8 ≤ ((d + 8 * (k : Nat)) - o).natAbs
      ∧ ((d + 8 * (k : Nat)) - o).natAbs ≤ 2 ^ 64 - 8) :
    read64 m' (SP + BitVec.ofInt 64 o) = read64 m (SP + BitVec.ofInt 64 o) :=
  read64_frameC hf _ fun k hk => by rw [addI]; exact djSS _ _ _ (h k hk).1 (h k hk).2

/-- A stack field slot outside the written slot survives a call. -/
theorem feO_slot_frame {m m' : AMem} {SP : BitVec 64} {d o : Int} {n : Nat}
    (hf : FrameC m m' (SP + BitVec.ofInt 64 d) n)
    (h : ∀ k, k < n → ∀ j ∈ limbOffs, 8 ≤ ((d + 8 * (k : Nat)) - (o + j)).natAbs
      ∧ ((d + 8 * (k : Nat)) - (o + j)).natAbs ≤ 2 ^ 64 - 8) :
    feO m' SP o = feO m SP o := by
  refine feO_frame hf fun k hk j hj => ?_
  rw [addI]
  exact djSS _ _ _ (h k hk j hj).1 (h k hk j hj).2

/-- An input coordinate survives a call writing a stack slot. -/
theorem feO_in_frame {m m' : AMem} {SP P : BitVec 64} {d o : Int} {n : Nat}
    (hX : CrossIn SP P) (hf : FrameC m m' (SP + BitVec.ofInt 64 d) n)
    (hn : 0 < n) (hd0 : 0 ≤ d) (hd1 : d + 8 * n ≤ 592) (hd8 : d % 8 = 0)
    (ho0 : 0 ≤ o) (ho1 : o + 24 ≤ 216) (ho8 : o % 8 = 0) :
    feO m' P o = feO m P o := by
  refine feO_frame hf fun k hk j hj => ?_
  rw [addI]
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  refine hX _ _ (by omega) (by omega) (by omega) (by omega) ?_ ?_ <;>
    rcases hj with rfl | rfl | rfl | rfl <;> omega

/-- One field call extends the state description by the slot it writes. -/
theorem invStep {C : ACallModel} {f : String} {op : Nat → Nat → Nat}
    (hC : FieldCallee C f op) {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat}
    (hk : k < 14) (hX : CrossIn SP P) {s : AState} (hI : MaddInv SP P Q SV IN k s)
    {body : List (JInstr 64)} {a1 a2 : BitVec 64} {v1 v2 : Nat}
    (hm : (runBlockA s body).mem = s.mem)
    (hsp : (runBlockA s body).regs "%rsp" = SP)
    (hdi : (runBlockA s body).regs "%rdi" = SP + BitVec.ofInt 64 (slotOff k))
    (hsi : (runBlockA s body).regs "%rsi" = a1)
    (hdx : (runBlockA s body).regs "%rdx" = a2)
    (hA1 : feO s.mem a1 0 = v1) (hA2 : feO s.mem a2 0 = v2)
    (hb1 : v1 < pM) (hb2 : v2 < pM) (hv : op v1 v2 % pM = SV k) :
    MaddInv SP P Q SV IN (k + 1) (C f (runBlockA s body)) := by
  obtain ⟨hrsp, hval, hfr⟩ := fieldStep hC s body SP a1 a2 (slotOff k) hm hsp hdi hsi hdx
    (by rw [hA1]; exact hb1) (by rw [hA2]; exact hb2)
  refine ⟨hrsp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [feO_slot_frame hfr (by
        intro u hu j hj
        simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
        simp only [slotOff]
        rcases hj with rfl | rfl | rfl | rfl <;> omega)]
      exact hI.slots i hik
    · have hik' : i = k := by omega
      subst hik'
      rw [hval, hA1, hA2]
      exact hv
  · intro j hj
    rw [feO_in_frame hX hfr (by omega) (by simp only [slotOff]; omega)
      (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)
      (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)
      (by simp only [slotOff]; omega)]
    exact hI.inp j hj
  · rw [read64_stack_frame hfr (by intro u hu; simp only [slotOff]; omega)]
    exact hI.ptrIn
  · rw [read64_stack_frame hfr (by intro u hu; simp only [slotOff]; omega)]
    exact hI.ptrOut

/-! ## 9. The concatenation call and the output copy -/

/-- The concatenation call leaves the four coordinates in the result block at
    `%rsp + 448`. -/
theorem joinStep {C : ACallModel} (hC : JoinCallee C join16Sym)
    {SP P Q : BitVec 64} {SV IN : Nat → Nat} {s : AState}
    (hI : MaddInv SP P Q SV IN 14 s) {body : List (JInstr 64)}
    (hm : (runBlockA s body).mem = s.mem)
    (hsp : (runBlockA s body).regs "%rsp" = SP)
    (hdi : (runBlockA s body).regs "%rdi" = SP + BitVec.ofInt 64 448)
    (hsi : (runBlockA s body).regs "%rsi" = SP + BitVec.ofInt 64 320)
    (hdx : (runBlockA s body).regs "%rdx" = SP + BitVec.ofInt 64 352)
    (hcx : (runBlockA s body).regs "%rcx" = SP + BitVec.ofInt 64 384)
    (hr8 : (runBlockA s body).regs "%r8" = SP + BitVec.ofInt 64 416) :
    (C join16Sym (runBlockA s body)).regs "%rsp" = SP
      ∧ feO (C join16Sym (runBlockA s body)).mem SP 448 = SV 10
      ∧ feO (C join16Sym (runBlockA s body)).mem SP 480 = SV 11
      ∧ feO (C join16Sym (runBlockA s body)).mem SP 512 = SV 12
      ∧ feO (C join16Sym (runBlockA s body)).mem SP 544 = SV 13
      ∧ read64 (C join16Sym (runBlockA s body)).mem (SP + BitVec.ofInt 64 584) = Q := by
  obtain ⟨⟨h0, h1, h2, h3⟩, hfr, hrsp⟩ := hC (runBlockA s body)
  rw [hdi, hsi, hm] at h0
  rw [hdi, hdx, hm] at h1
  rw [hdi, hcx, hm] at h2
  rw [hdi, hr8, hm] at h3
  rw [hdi, hm] at hfr
  rw [feO_base] at h0 h1 h2 h3
  have e10 : feO s.mem SP 320 = SV 10 := by
    have := hI.slots 10 (by omega); simpa [slotOff] using this
  have e11 : feO s.mem SP 352 = SV 11 := by
    have := hI.slots 11 (by omega); simpa [slotOff] using this
  have e12 : feO s.mem SP 384 = SV 12 := by
    have := hI.slots 12 (by omega); simpa [slotOff] using this
  have e13 : feO s.mem SP 416 = SV 13 := by
    have := hI.slots 13 (by omega); simpa [slotOff] using this
  refine ⟨by rw [hrsp, hsp], ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (448 : Int) = 448 + 0 by norm_num, h0, feO_base,
      show (320 : Int) + 0 = 320 by norm_num]
    exact e10
  · rw [show (480 : Int) = 448 + 32 by norm_num, h1, feO_base,
      show (352 : Int) + 0 = 352 by norm_num]
    exact e11
  · rw [show (512 : Int) = 448 + 64 by norm_num, h2, feO_base,
      show (384 : Int) + 0 = 384 by norm_num]
    exact e12
  · rw [show (544 : Int) = 448 + 96 by norm_num, h3, feO_base,
      show (416 : Int) + 0 = 416 by norm_num]
    exact e13
  · rw [read64_stack_frame hfr (by intro u hu; omega)]
    exact hI.ptrOut

/-- The sixteen word offsets of the output copy. -/
def outOffs : List Int :=
  [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120]

theorem outOffs_nodup : outOffs.Nodup := by decide

/-- The copy leaves at the output pointer the sixteen words of the result block. -/
theorem copyOut {SP Q : BitVec 64} (hOut : CrossOut SP Q) (s : AState)
    (h10 : s.regs "%r10" = Q) (h9 : s.regs "%r9" = SP + BitVec.ofInt 64 448)
    (o : Int) (ho : o ∈ outOffs) :
    read64 (runBlockA s (copyBlk outOffs)).mem (Q + BitVec.ofInt 64 o)
      = read64 s.mem (SP + BitVec.ofInt 64 (448 + o)) := by
  have hrange : ∀ u ∈ outOffs, 0 ≤ u ∧ u ≤ 120 ∧ u % 8 = 0 := by decide
  have key := copyBlk_val s outOffs outOffs_nodup
    (by
      rw [h10]
      intro x hx y hy hxy
      obtain ⟨hx0, hx1, hx8⟩ := hrange x hx
      obtain ⟨hy0, hy1, hy8⟩ := hrange y hy
      exact djSS _ _ _ (by omega) (by omega))
    (by
      rw [h10, h9]
      intro x hx y hy
      obtain ⟨hx0, hx1, hx8⟩ := hrange x hx
      obtain ⟨hy0, hy1, hy8⟩ := hrange y hy
      rw [addI]
      exact (hOut (448 + y) x (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)).symm)
    o ho
  rw [h10, h9, addI] at key
  exact key

/-! ## 10. One call of each argument shape -/

theorem inPtr_eq {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat} {s : AState}
    (hI : MaddInv SP P Q SV IN k s) : inPtr s = P := by
  rw [inPtr, hI.rsp]; exact hI.ptrIn

theorem argIn {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat} {s : AState}
    (hI : MaddInv SP P Q SV IN k s) (j : Nat) (hj : j < 7) (o : Int) (ho : o = slotOff j) :
    feO s.mem (P + BitVec.ofInt 64 o) 0 = IN j := by
  rw [feO_base, ho, show slotOff j + (0 : Int) = slotOff j by omega]
  exact hI.inp j hj

theorem argSlot {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat} {s : AState}
    (hI : MaddInv SP P Q SV IN k s) (i : Nat) (hi : i < k) (o : Int) (ho : o = slotOff i) :
    feO s.mem (SP + BitVec.ofInt 64 o) 0 = SV i := by
  rw [feO_base, ho, show slotOff i + (0 : Int) = slotOff i by omega]
  exact hI.slots i hi

/-- A call whose two arguments are input coordinates. -/
theorem stepRR {C : ACallModel} {f : String} {op : Nat → Nat → Nat}
    (hC : FieldCallee C f op) {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat}
    (hk : k < 14) (hX : CrossIn SP P) {s : AState} (hI : MaddInv SP P Q SV IN k s)
    (d o1 o2 : Int) (j1 j2 : Nat) (hd : d = slotOff k) (hj1 : j1 < 7) (hj2 : j2 < 7)
    (ho1 : o1 = slotOff j1) (ho2 : o2 = slotOff j2)
    (hb1 : IN j1 < pM) (hb2 : IN j2 < pM) (hv : op (IN j1) (IN j2) % pM = SV k) :
    MaddInv SP P Q SV IN (k + 1) (C f (runBlockA s
      [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
       .lea "%rsi" "%r10" "%r10" 0 o1, .lea "%rdx" "%r10" "%r10" 0 o2])) := by
  subst hd
  obtain ⟨hm, hsp, hdi, hsi, hdx⟩ := runArgsRR s (slotOff k) o1 o2
  rw [hI.rsp] at hdi hsp
  rw [inPtr_eq hI] at hsi hdx
  exact invStep hC hk hX hI hm hsp hdi hsi hdx (argIn hI j1 hj1 o1 ho1)
    (argIn hI j2 hj2 o2 ho2) hb1 hb2 hv

/-- A call whose first argument is an intermediate slot and whose second is an input
    coordinate. -/
theorem stepSR {C : ACallModel} {f : String} {op : Nat → Nat → Nat}
    (hC : FieldCallee C f op) {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat}
    (hk : k < 14) (hX : CrossIn SP P) {s : AState} (hI : MaddInv SP P Q SV IN k s)
    (d o1 o2 : Int) (i1 j2 : Nat) (hd : d = slotOff k) (hi1 : i1 < k) (hj2 : j2 < 7)
    (ho1 : o1 = slotOff i1) (ho2 : o2 = slotOff j2)
    (hb1 : SV i1 < pM) (hb2 : IN j2 < pM) (hv : op (SV i1) (IN j2) % pM = SV k) :
    MaddInv SP P Q SV IN (k + 1) (C f (runBlockA s
      [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
       .lea "%rsi" "%rsp" "%rsp" 0 o1, .lea "%rdx" "%r10" "%r10" 0 o2])) := by
  subst hd
  obtain ⟨hm, hsp, hdi, hsi, hdx⟩ := runArgsSR s (slotOff k) o1 o2
  rw [hI.rsp] at hdi hsp hsi
  rw [inPtr_eq hI] at hdx
  exact invStep hC hk hX hI hm hsp hdi hsi hdx (argSlot hI i1 hi1 o1 ho1)
    (argIn hI j2 hj2 o2 ho2) hb1 hb2 hv

/-- A call whose two arguments are intermediate slots. -/
theorem stepSS {C : ACallModel} {f : String} {op : Nat → Nat → Nat}
    (hC : FieldCallee C f op) {SP P Q : BitVec 64} {SV IN : Nat → Nat} {k : Nat}
    (hk : k < 14) (hX : CrossIn SP P) {s : AState} (hI : MaddInv SP P Q SV IN k s)
    (d o1 o2 : Int) (i1 i2 : Nat) (hd : d = slotOff k) (hi1 : i1 < k) (hi2 : i2 < k)
    (ho1 : o1 = slotOff i1) (ho2 : o2 = slotOff i2)
    (hb1 : SV i1 < pM) (hb2 : SV i2 < pM) (hv : op (SV i1) (SV i2) % pM = SV k) :
    MaddInv SP P Q SV IN (k + 1) (C f (runBlockA s
      [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
       .lea "%rsi" "%rsp" "%rsp" 0 o1, .lea "%rdx" "%rsp" "%rsp" 0 o2])) := by
  subst hd
  obtain ⟨hm, hsp, hdi, hsi, hdx⟩ := runArgsSS s (slotOff k) o1 o2
  rw [hI.rsp] at hdi hsp hsi hdx
  exact invStep hC hk hX hI hm hsp hdi hsi hdx (argSlot hI i1 hi1 o1 ho1)
    (argSlot hI i2 hi2 o2 ho2) hb1 hb2 hv

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
