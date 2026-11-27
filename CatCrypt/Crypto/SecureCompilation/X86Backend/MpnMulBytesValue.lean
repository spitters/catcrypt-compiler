/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCarryIdiomsHand

@[expose] public section

set_option autoImplicit false

/-!
# The linked `mpn_mul_basecase_rt` computes the schoolbook product

The decoded program `MpnMulShipped.mulDec` of the linked object is run on the address machine
`aMachine`. One inner trip (`MpnMulTrip.mulInner`) performs `MpnMulBasecaseFrontEmit.bcStep`
on the words of the output array (`mul_trip`); the inner loop performs the row `bcRow`, the
outer loop the fold `bcFold`, and `bcFold_val_zero` reads the product off the output words.

## The state of the loops

At the head of an inner trip the registers hold the frame base `%rsp = SP`, `%rdi = un`,
`%rax = jd` (the row), `%r10 = t` (the inner index), `%r11` the inner count and `%r8` the
outer count; the frame words hold the pointers (`rp` at `120`, `up` at `112`, `vp` at `-8`),
`vn` at `24` and the callee-saved registers at `64`–`104` (`MulMem.saved`); the words of
`up` and `vp` are unchanged; the `un + vn + 1` words of `rp` hold the accumulator.

## Main results

* `mul_trip`: one inner trip is `bcStep` on the accumulator words.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulShipped
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn memGetDyn_memSetDyn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (mulHiW)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
  (bcStep bcLimb mulAddLimb bcPartial bcRow bcFold bcPartial_succ bcFold_succ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach (reaches_doWhile step_je)

/-! ## 1. Words and arrays -/

/-- The array of the first `n` words of `f`. -/
def arr (n : Nat) (f : Nat → BitVec 64) : Fin n → BitVec 64 := fun i => f i.val

theorem memGetDyn_arr (n : Nat) (f : Nat → BitVec 64) (k : Nat) (hk : k < n) :
    memGetDyn (arr n f) k = f k := by
  cases n with
  | zero => omega
  | succ m => simp [memGetDyn, arr, Nat.mod_eq_of_lt hk]

theorem mulx_hi (a b : BitVec 64) : (x86_MULX_lo_hi a b).2 = mulHiW a b := by
  simp only [x86_MULX_lo_hi, wumul, mulHiW, high_bits]

theorem bSltu_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    bSltu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = if a < b then 1 else 0 := by
  rw [MpnCarryIdiomsHand.bSltu_eq_hand]
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b <;> simp [h]

/-- The masked limb of the trip is `bcLimb`. -/
theorem masked_limb (U : Nat → BitVec 64) (UP : BitVec 64) (m : AMem) (un k : Nat)
    (hun : un < 2 ^ 64) (hk : k < 2 ^ 64)
    (hU : ∀ j, j < un → read64 m (ix UP (BitVec.ofNat 64 j)) = U j) :
    read64 m (ix UP (BitVec.ofNat 64 k &&& (0 - bSltu (BitVec.ofNat 64 k) (BitVec.ofNat 64 un))))
        &&& (0 - bSltu (BitVec.ofNat 64 k) (BitVec.ofNat 64 un))
      = bcLimb (arr un U) un k := by
  rw [bSltu_ofNat k un hk hun, bcLimb]
  by_cases h : k < un
  · have hones : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
    simp only [h, ite_true, hones, BitVec.and_allOnes, hU k h, memGetDyn_arr un U k h]
  · simp [h]

/-! ## 2. The memory invariant -/

/-- The frame words an inner trip does not write, by offset from the frame base. -/
def keepOffs : List Int := [-24, -16, -8, 24, 40, 56, 64, 72, 80, 88, 96, 104, 112, 120]

/-- The frame words an inner trip writes. -/
def tripOffs : List Int := [8, 16, 32, 48]

/-- All frame words of the function. -/
def slotOffs : List Int := keepOffs ++ tripOffs

theorem keep_trip_far : ∀ a ∈ keepOffs, ∀ b ∈ tripOffs,
    8 ≤ (b - a).natAbs ∧ (b - a).natAbs ≤ 2 ^ 64 - 8 := by decide

/-- The `152` bytes of the frame: from `SP - 24` (the lowest red-zone word the function writes)
    to `SP + 128` (the entry stack pointer). -/
def InFrB (SP x : BitVec 64) : Prop := (x - at' SP (-24)).toNat < 152

/-- The bytes of the first `n` words of `rp`. -/
def InOutB (RP : BitVec 64) (n : Nat) (x : BitVec 64) : Prop :=
  ∃ j, j < n ∧ InRange8 (ix RP (BitVec.ofNat 64 j)) x

/-- **Word-level separation.** The words of `rp` (`un + vn + 1` of them) are pairwise
    disjoint and disjoint from the frame words and from the words of `up` and `vp`, which are
    disjoint from the frame words. -/
structure MulSep (SP RP UP VP : BitVec 64) (un vn : Nat) : Prop where
  rr : ∀ i j, i ≤ un + vn → j ≤ un + vn → i ≠ j →
    Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix RP (BitVec.ofNat 64 j))
  rs : ∀ i, i ≤ un + vn → ∀ o ∈ slotOffs, Disjoint8 (ix RP (BitVec.ofNat 64 i)) (at' SP o)
  ru : ∀ i j, i ≤ un + vn → j < un →
    Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix UP (BitVec.ofNat 64 j))
  rv : ∀ i j, i ≤ un + vn → j < vn →
    Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix VP (BitVec.ofNat 64 j))
  us : ∀ j, j < un → ∀ o ∈ slotOffs, Disjoint8 (ix UP (BitVec.ofNat 64 j)) (at' SP o)
  vs : ∀ j, j < vn → ∀ o ∈ slotOffs, Disjoint8 (ix VP (BitVec.ofNat 64 j)) (at' SP o)
  bound : un + vn + 1 < 2 ^ 64
  fr : ∀ o ∈ slotOffs, ∀ x, InRange8 (at' SP o) x → InFrB SP x

/-- **The memory invariant of the loops.** The pointer and count words of the frame, the
    words `saved` (at offsets in `keepOffs`), the words `U` of `up`, `V` of `vp`, and the
    accumulator `R` in the `un + vn + 1` words of `rp`. -/
structure MulMem (SP RP UP VP : BitVec 64) (un vn : Nat) (U V R : Nat → BitVec 64)
    (saved : List (Int × BitVec 64)) (m : AMem) : Prop where
  rp : read64 m (at' SP 120) = RP
  up : read64 m (at' SP 112) = UP
  vp : read64 m (at' SP (-8)) = VP
  vnw : read64 m (at' SP 24) = BitVec.ofNat 64 vn
  saved : ∀ e ∈ saved, read64 m (at' SP e.1) = e.2
  upw : ∀ j, j < un → read64 m (ix UP (BitVec.ofNat 64 j)) = U j
  vpw : ∀ j, j < vn → read64 m (ix VP (BitVec.ofNat 64 j)) = V j
  rpw : ∀ i, i ≤ un + vn → read64 m (ix RP (BitVec.ofNat 64 i)) = R i

section Inv

variable {SP RP UP VP : BitVec 64} {un vn : Nat} {U V R : Nat → BitVec 64}
  {saved : List (Int × BitVec 64)}

/-- A store to a frame word of the trip keeps the invariant. -/
theorem MulMem.slot (hS : MulSep SP RP UP VP un vn) (hsv : ∀ e ∈ saved, e.1 ∈ keepOffs)
    {m : AMem} (h : MulMem SP RP UP VP un vn U V R saved m) (o : Int) (ho : o ∈ tripOffs)
    (v : BitVec 64) : MulMem SP RP UP VP un vn U V R saved (write64 m (at' SP o) v) := by
  have far : ∀ a ∈ keepOffs, read64 (write64 m (at' SP o) v) (at' SP a) = read64 m (at' SP a) :=
    fun a ha => rd_at_ne m SP v o a (keep_trip_far a ha o ho).1 (keep_trip_far a ha o ho).2
  have hso : o ∈ slotOffs := List.mem_append_right _ ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [far 120 (by decide)]; exact h.rp
  · rw [far 112 (by decide)]; exact h.up
  · rw [far (-8) (by decide)]; exact h.vp
  · rw [far 24 (by decide)]; exact h.vnw
  · intro e he; rw [far e.1 (hsv e he)]; exact h.saved e he
  · intro j hj
    rw [read64_write64_of_disjoint _ _ _ _ (hS.us j hj o hso).symm]; exact h.upw j hj
  · intro j hj
    rw [read64_write64_of_disjoint _ _ _ _ (hS.vs j hj o hso).symm]; exact h.vpw j hj
  · intro i hi
    rw [read64_write64_of_disjoint _ _ _ _ (hS.rs i hi o hso).symm]; exact h.rpw i hi

/-- A store to word `p` of `rp` keeps the invariant with the accumulator updated at `p`. -/
theorem MulMem.out (hS : MulSep SP RP UP VP un vn) (hsv : ∀ e ∈ saved, e.1 ∈ keepOffs)
    {m : AMem} (h : MulMem SP RP UP VP un vn U V R saved m) (p : Nat) (hp : p ≤ un + vn)
    (v : BitVec 64) :
    MulMem SP RP UP VP un vn U V (fun i => if i = p then v else R i) saved
      (write64 m (ix RP (BitVec.ofNat 64 p)) v) := by
  have hk : ∀ a ∈ keepOffs, a ∈ slotOffs := fun a ha => List.mem_append_left _ ha
  have far : ∀ a ∈ keepOffs, read64 (write64 m (ix RP (BitVec.ofNat 64 p)) v) (at' SP a)
      = read64 m (at' SP a) :=
    fun a ha => read64_write64_of_disjoint _ _ _ _ (hS.rs p hp a (hk a ha))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [far 120 (by decide)]; exact h.rp
  · rw [far 112 (by decide)]; exact h.up
  · rw [far (-8) (by decide)]; exact h.vp
  · rw [far 24 (by decide)]; exact h.vnw
  · intro e he; rw [far e.1 (hsv e he)]; exact h.saved e he
  · intro j hj
    rw [read64_write64_of_disjoint _ _ _ _ (hS.ru p j hp hj)]; exact h.upw j hj
  · intro j hj
    rw [read64_write64_of_disjoint _ _ _ _ (hS.rv p j hp hj)]; exact h.vpw j hj
  · intro i hi
    by_cases hip : i = p
    · subst hip; simp [read64_write64_same]
    · rw [read64_write64_of_disjoint _ _ _ _ (hS.rr p i hp hi (Ne.symm hip))]
      simp [hip, h.rpw i hi]

/-- The invariant depends on the accumulator only at the `un + vn + 1` words. -/
theorem MulMem.congr {m : AMem} {R' : Nat → BitVec 64}
    (h : MulMem SP RP UP VP un vn U V R saved m) (hR : ∀ i, i ≤ un + vn → R i = R' i) :
    MulMem SP RP UP VP un vn U V R' saved m :=
  ⟨h.rp, h.up, h.vp, h.vnw, h.saved, h.upw, h.vpw, fun i hi => (h.rpw i hi).trans (hR i hi)⟩

end Inv

/-- The memory `m'` agrees with `m` outside the frame bytes and the first `n` words of `rp`. -/
def Keeps (SP RP : BitVec 64) (n : Nat) (m m' : AMem) : Prop :=
  ∀ x, ¬ InFrB SP x → ¬ InOutB RP n x → m' x = m x

theorem Keeps.refl {SP RP : BitVec 64} {n : Nat} (m : AMem) : Keeps SP RP n m m :=
  fun _ _ _ => rfl

theorem Keeps.trans {SP RP : BitVec 64} {n : Nat} {m m' m'' : AMem} (h : Keeps SP RP n m m')
    (h' : Keeps SP RP n m' m'') : Keeps SP RP n m m'' :=
  fun x a b => (h' x a b).trans (h x a b)

theorem Keeps.slot {SP RP UP VP : BitVec 64} {un vn : Nat} (hS : MulSep SP RP UP VP un vn)
    {m m' : AMem} (o : Int) (ho : o ∈ slotOffs) (v : BitVec 64)
    (h : Keeps SP RP (un + vn + 1) m m') :
    Keeps SP RP (un + vn + 1) m (write64 m' (at' SP o) v) := fun x a b => by
  rw [write64_of_not_inRange _ _ _ _ (fun hr => a (hS.fr o ho x hr))]; exact h x a b

theorem Keeps.out {SP RP : BitVec 64} {n : Nat} {m m' : AMem} (p : Nat) (hp : p < n)
    (v : BitVec 64) (h : Keeps SP RP n m m') :
    Keeps SP RP n m (write64 m' (ix RP (BitVec.ofNat 64 p)) v) := fun x a b => by
  rw [write64_of_not_inRange _ _ _ _ (fun hr => b ⟨p, hp, hr⟩)]; exact h x a b

/-! ## 3. One inner trip -/

/-- The registers an inner trip writes. -/
def tripRegs : List String :=
  ["%r9", "%r12", "%r13", "%rsi", "%r14", "%r15", "%rcx", "%rbp", "%r10", "%r11"]

theorem ix_ofNat_add (b : BitVec 64) (x y : Nat) :
    ix b (BitVec.ofNat 64 x + BitVec.ofNat 64 y) = ix b (BitVec.ofNat 64 (x + y)) := by
  rw [BitVec.ofNat_add]

/-- **One inner trip is `bcStep`.** From a state at the head of the inner trip `k ≤ un` of
    row `jd < vn`, with the accumulator `acc` in the words of `rp`, `runBlockA` of the trip
    leaves `bcStep` of `acc` in the words of `rp`, keeps the rest of the invariant, steps the
    index and the count, writes no register outside `tripRegs`, and sets the zero flag
    exactly when the decremented count is zero. -/
theorem mul_trip {SP RP UP VP : BitVec 64} {un vn : Nat} {U V : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : MulSep SP RP UP VP un vn)
    (hsv : ∀ e ∈ saved, e.1 ∈ keepOffs) (jd k : Nat) (hjd : jd < vn) (hk : k ≤ un)
    (acc : Fin (un + vn + 1) → BitVec 64) (sa : AState)
    (hrsp : sa.regs "%rsp" = SP) (hrdi : sa.regs "%rdi" = BitVec.ofNat 64 un)
    (hrax : sa.regs "%rax" = BitVec.ofNat 64 jd) (hr10 : sa.regs "%r10" = BitVec.ofNat 64 k)
    (hM : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved sa.mem) :
    MulMem SP RP UP VP un vn U V
        (memGetDyn (bcStep (arr un U) (arr vn V) un (un + vn) jd acc k)) saved
        (runBlockA sa mulInner).mem
    ∧ (runBlockA sa mulInner).regs "%r10" = BitVec.ofNat 64 (k + 1)
    ∧ (runBlockA sa mulInner).regs "%r11" = sa.regs "%r11" - 1
    ∧ (∀ r, r ∉ tripRegs → (runBlockA sa mulInner).regs r = sa.regs r)
    ∧ (runBlockA sa mulInner).view.flagB (·.zf) = decide (sa.regs "%r11" - 1 = 0)
    ∧ Keeps SP RP (un + vn + 1) sa.mem (runBlockA sa mulInner).mem := by
  have hb := hS.bound
  have hun : un < 2 ^ 64 := by omega
  have hk64 : k < 2 ^ 64 := by omega
  have hslot : ∀ o ∈ tripOffs, o ∈ slotOffs := fun o ho => List.mem_append_right _ ho
  rw [mulInner_eq]
  simp only [runBlockA_append]
  -- segment 1
  obtain ⟨e1si, e1r12, f1, m1⟩ := tS1_run sa
  generalize hs1 : runBlockA sa tS1 = s1 at e1si e1r12 f1 m1
  rw [hr10, hrdi] at e1si e1r12
  -- segment 2
  have e1rsp : s1.regs "%rsp" = SP := (f1 _ (by decide) (by decide) (by decide) (by decide)).trans hrsp
  have e1rax : s1.regs "%rax" = BitVec.ofNat 64 jd :=
    (f1 _ (by decide) (by decide) (by decide) (by decide)).trans hrax
  have e1rdi : s1.regs "%rdi" = BitVec.ofNat 64 un :=
    (f1 _ (by decide) (by decide) (by decide) (by decide)).trans hrdi
  have e1r10 : s1.regs "%r10" = BitVec.ofNat 64 k :=
    (f1 _ (by decide) (by decide) (by decide) (by decide)).trans hr10
  obtain ⟨e2si, e2r13, f2, m2⟩ := tS2_run s1 UP VP (by rw [e1rsp, m1]; exact hM.up)
    (by rw [e1rsp, m1]; exact hM.vp)
  generalize hs2 : runBlockA s1 tS2 = s2 at e2si e2r13 f2 m2
  simp only [e1r12, e1si, m1, e1rsp, e1rax] at e2si e2r13 m2
  rw [masked_limb U UP sa.mem un k hun hk64 hM.upw] at e2si e2r13 m2
  rw [hM.vpw jd hjd] at e2r13 m2
  rw [mulx_hi] at m2
  have fr2 : ∀ r, r ≠ "%r9" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rsi" → r ≠ "%r14" →
      r ≠ "%r15" → s2.regs r = sa.regs r := fun r a b c d e g =>
    (f2 r a b c d e g).trans (f1 r a b c d)
  have e2rsp : s2.regs "%rsp" = SP := (fr2 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hrsp
  have e2rdi : s2.regs "%rdi" = BitVec.ofNat 64 un := (fr2 _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hrdi
  -- the memory after the high-product spill keeps the invariant
  have M2 : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s2.mem := by
    rw [m2]; exact hM.slot hS hsv 48 (by decide) _
  -- segment 3
  obtain ⟨e3r9, f3, m3⟩ := tS3_run s2 (BitVec.ofNat 64 vn) RP (by rw [e2rsp]; exact M2.vnw)
    (by rw [e2rsp]; exact M2.rp)
  generalize hs3 : runBlockA s2 tS3 = s3 at e3r9 f3 m3
  rw [e2rsp, e2rdi, ix_ofNat_add,
    read64_write64_of_disjoint _ _ _ _ (hS.rs (un + vn) (Nat.le_refl _) 32 (by decide)).symm,
    M2.rpw (un + vn) (Nat.le_refl _)] at e3r9
  rw [e2rsp, e2rdi] at m3
  have M3 : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s3.mem := by
    rw [m3]; exact M2.slot hS hsv 32 (by decide) _
  have fr3 : ∀ r, r ≠ "%r9" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rsi" → r ≠ "%r14" →
      r ≠ "%r15" → s3.regs r = sa.regs r := fun r a b c d e g =>
    (f3 r a e g).trans (fr2 r a b c d e g)
  have e3r13 : s3.regs "%r13" = bcLimb (arr un U) un k * V jd :=
    (f3 _ (by decide) (by decide) (by decide)).trans e2r13
  have e3rsp : s3.regs "%rsp" = SP := (fr3 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hrsp
  -- segment 4
  obtain ⟨e4r9, f4, m4⟩ := tS4_run s3
  generalize hs4 : runBlockA s3 tS4 = s4 at e4r9 f4 m4
  rw [e3r13, e3r9] at e4r9 m4
  rw [e3rsp] at m4
  have M4 : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s4.mem := by
    rw [m4]; exact M3.slot hS hsv 16 (by decide) _
  have fr4 : ∀ r, r ≠ "%r9" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rsi" → r ≠ "%r14" →
      r ≠ "%r15" → r ≠ "%rcx" → r ≠ "%rbp" → s4.regs r = sa.regs r := fun r a b c d e g h i =>
    (f4 r a d h b i g).trans (fr3 r a b c d e g)
  have e4rsp : s4.regs "%rsp" = SP := (fr4 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans hrsp
  have e4rax : s4.regs "%rax" = BitVec.ofNat 64 jd := (fr4 _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrax
  have e4r10 : s4.regs "%r10" = BitVec.ofNat 64 k := (fr4 _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr10
  -- segment 5
  have hjk : jd + k ≤ un + vn := by omega
  obtain ⟨e5si, f5, m5⟩ := tS5_run s4 RP (by rw [e4rsp]; exact M4.rp)
  generalize hs5 : runBlockA s4 tS5 = s5 at e5si f5 m5
  rw [e4rsp, e4rax, e4r10, ix_ofNat_add,
    read64_write64_of_disjoint _ _ _ _ (hS.rs (jd + k) hjk 8 (by decide)).symm,
    M4.rpw (jd + k) hjk, e4r9] at e5si
  rw [e4rsp, e4rax, e4r10] at m5
  have M5 : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s5.mem := by
    rw [m5]; exact M4.slot hS hsv 8 (by decide) _
  have e5r9 : s5.regs "%r9" = bcLimb (arr un U) un k * V jd + memGetDyn acc (un + vn) :=
    (f5 _ (by decide) (by decide) (by decide) (by decide)).trans e4r9
  -- segment 6
  obtain ⟨e6rcx, f6, m6⟩ := tS6_run s5
  generalize hs6 : runBlockA s5 tS6 = s6 at e6rcx f6 m6
  rw [e5si, e5r9] at e6rcx
  have e6si := (f6 "%rsi" (by decide) (by decide) (by decide) (by decide) (by decide)).trans e5si
  have fr6 : ∀ r, r ≠ "%r9" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rsi" → r ≠ "%r14" →
      r ≠ "%r15" → r ≠ "%rcx" → r ≠ "%rbp" → s6.regs r = sa.regs r := fun r a b c d e g h i =>
    (f6 r a h b c i).trans ((f5 r d e g b).trans (fr4 r a b c d e g h i))
  have e6rsp : s6.regs "%rsp" = SP := (fr6 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans hrsp
  have e6r10 : s6.regs "%r10" = BitVec.ofNat 64 k := (fr6 _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr10
  have e6r11 : s6.regs "%r11" = sa.regs "%r11" := fr6 _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have M6 : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s6.mem := m6 ▸ M5
  -- segment 7
  obtain ⟨e7r10, e7r11, f7, m7, z7⟩ := tS7_run s6 _ _ RP (BitVec.ofNat 64 jd + BitVec.ofNat 64 k)
    (BitVec.ofNat 64 un + BitVec.ofNat 64 vn)
    (by rw [e6rsp, m6, m5, rd_at_ne _ _ _ 8 48 (by decide) (by decide), m4,
      rd_at_ne _ _ _ 16 48 (by decide) (by decide), m3, rd_at_ne _ _ _ 32 48 (by decide) (by decide),
      m2, rd_at_same])
    (by rw [e6rsp, m6, m5, rd_at_ne _ _ _ 8 16 (by decide) (by decide), m4, rd_at_same])
    (by rw [e6rsp]; exact M6.rp)
    (by rw [e6rsp, m6, m5, rd_at_same])
    (by rw [e6rsp, m6, m5, rd_at_ne _ _ _ 8 32 (by decide) (by decide), m4,
      rd_at_ne _ _ _ 16 32 (by decide) (by decide), m3, rd_at_same])
    (by rw [e6rsp, ix_ofNat_add]; exact hS.rs (jd + k) hjk 120 (by decide))
    (by rw [e6rsp, ix_ofNat_add]; exact hS.rs (jd + k) hjk 32 (by decide))
  generalize hs7 : runBlockA s6 tS7 = s7 at e7r10 e7r11 f7 m7 z7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m7, ix_ofNat_add, ix_ofNat_add, e6si, e6rcx]
    refine ((M6.out hS hsv (jd + k) hjk _).out hS hsv (un + vn) (Nat.le_refl _) _).congr ?_
    intro i hi
    have hn : un + vn < un + vn + 1 := Nat.lt_succ_self _
    have hjn : jd + k < un + vn + 1 := by omega
    simp only [bcStep, mulAddLimb, memGetDyn_memSetDyn _ hn (Nat.lt_succ_of_le hi),
      memGetDyn_memSetDyn _ hjn (Nat.lt_succ_of_le hi), memGetDyn_arr vn V jd hjd]
  · rw [e7r10, e6r10]; simp [BitVec.ofNat_add]
  · rw [e7r11, e6r11]
  · intro r hr
    simp only [tripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, g, h, i, j, l⟩ := hr
    rw [f7 r a h i e g j l]
    exact fr6 r a b c d e g h i
  · rw [z7, e6r11]
  · rw [m7, ix_ofNat_add, ix_ofNat_add, m6, m5, m4, m3, m2]
    refine Keeps.out _ (by omega) _ (Keeps.out _ (by omega) _ ?_)
    iterate 4 refine Keeps.slot hS _ (by decide) _ ?_
    exact Keeps.refl _

/-! ## 4. The inner loop -/

/-- The decoded program around the inner trip. -/
theorem mulDec_inner : mulDec = (mulPre.map RInstr.op ++ [RInstr.jcc 4 182] ++ mulOHead.map RInstr.op
      ++ [RInstr.jcc 4 174]) ++ mulInner.map RInstr.op
      ++ ([RInstr.jcc 5 34] ++ mulOTail.map RInstr.op ++ [RInstr.jcc 5 26]
        ++ mulPost.map RInstr.op ++ [RInstr.ret]) := by
  simp only [mulDec, List.append_assoc]

/-- The prologue has `25` instructions. -/
theorem mulPre_length : mulPre.length = 25 := by simp [mulPre]

/-- The outer head has `7` instructions. -/
theorem mulOHead_length : mulOHead.length = 7 := by simp [mulOHead]

/-- The inner trip has `139` instructions. -/
theorem mulInner_length : mulInner.length = 139 := by simp [mulInner]

/-- The outer tail has `7` instructions. -/
theorem mulOTail_length : mulOTail.length = 7 := by simp [mulOTail]

/-- From index `34`, the inner trip runs as `runBlockA` to the back edge at `173`. -/
theorem reach_inner (s : AState) : Reaches aMachine mulDec 34 s 173 (runBlockA s mulInner) := by
  have h := reaches_ops aMachine (mulPre.map RInstr.op ++ [RInstr.jcc 4 182]
      ++ mulOHead.map RInstr.op ++ [RInstr.jcc 4 174]) mulInner
    ([RInstr.jcc 5 34] ++ mulOTail.map RInstr.op ++ [RInstr.jcc 5 26]
      ++ mulPost.map RInstr.op ++ [RInstr.ret]) s
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    mulPre_length, mulOHead_length, mulInner_length] at h
  rw [aMachine_runBlock, ← mulDec_inner] at h
  exact h

theorem mulDec_173 : mulDec[173]? = some (.jcc 5 34) := rfl

theorem cnt_dec (n : Nat) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]; simp

theorem cnt_dec1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := cnt_dec n

theorem ofNat_eq_zero_iff (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
    simpa using this
  · rintro rfl; rfl

/-- **The inner loop is the row `bcRow`.** From index `34` with the inner index `0` and
    the count `un + 1`, the machine reaches index `174` with `bcRow` of the accumulator in the
    words of `rp`, the invariant kept, and no register outside `tripRegs` written. -/
theorem inner_loop {SP RP UP VP : BitVec 64} {un vn : Nat} {U V : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : MulSep SP RP UP VP un vn)
    (hsv : ∀ e ∈ saved, e.1 ∈ keepOffs) (jd : Nat) (hjd : jd < vn)
    (acc : Fin (un + vn + 1) → BitVec 64) (s0 : AState)
    (hrsp : s0.regs "%rsp" = SP) (hrdi : s0.regs "%rdi" = BitVec.ofNat 64 un)
    (hrax : s0.regs "%rax" = BitVec.ofNat 64 jd) (hr10 : s0.regs "%r10" = BitVec.ofNat 64 0)
    (hr11 : s0.regs "%r11" = BitVec.ofNat 64 (un + 1))
    (hM : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s0.mem) :
    ∃ s', Reaches aMachine mulDec 34 s0 174 s'
      ∧ (∀ r, r ∉ tripRegs → s'.regs r = s0.regs r)
      ∧ MulMem SP RP UP VP un vn U V
          (memGetDyn (bcRow (arr un U) (arr vn V) un (un + vn) jd acc)) saved s'.mem
      ∧ Keeps SP RP (un + vn + 1) s0.mem s'.mem := by
  have hb := hS.bound
  let Inv : Nat → AState → Prop := fun k s =>
    (∀ r, r ∉ tripRegs → s.regs r = s0.regs r) ∧ s.regs "%r10" = BitVec.ofNat 64 k
      ∧ s.regs "%r11" = BitVec.ofNat 64 (un + 1 - k)
      ∧ MulMem SP RP UP VP un vn U V
          (memGetDyn (bcPartial (arr un U) (arr vn V) un (un + vn) jd acc k)) saved s.mem
      ∧ Keeps SP RP (un + vn + 1) s0.mem s.mem
  have hbody : ∀ k s, k < un + 1 → Inv k s → ∃ s', Reaches aMachine mulDec 34 s 173 s' ∧
      (aMachine.view s').flagB (·.zf) = decide (k + 1 = un + 1) ∧ Inv (k + 1) s' := by
    intro k s hk ⟨hf, h10, h11, hm, hkp⟩
    obtain ⟨M', e10, e11, f', z', kp'⟩ := mul_trip hS hsv jd k hjd (by omega) _ s
      ((hf _ (by simp [tripRegs])).trans hrsp) ((hf _ (by simp [tripRegs])).trans hrdi)
      ((hf _ (by simp [tripRegs])).trans hrax) h10 hm
    have h11' : s.regs "%r11" = BitVec.ofNat 64 (un - k + 1) := by
      rw [h11]; grind
    refine ⟨runBlockA s mulInner, reach_inner s, ?_, ?_, e10, ?_, ?_, hkp.trans kp'⟩
    · show (runBlockA s mulInner).view.flagB (·.zf) = _
      rw [z', h11', cnt_dec]
      exact decide_eq_decide.mpr ((ofNat_eq_zero_iff _ (by omega)).trans (by omega))
    · intro r hr; exact (f' r hr).trans (hf r hr)
    · rw [e11, h11', cnt_dec]; grind
    · rw [bcPartial_succ]; exact M'
  have h0 : Inv 0 s0 :=
    ⟨fun _ _ => rfl, hr10, by simpa using hr11, by simpa [bcPartial] using hM, Keeps.refl _⟩
  obtain ⟨s', hr, hf, -, -, hm, hkp⟩ :=
    reaches_doWhile aMachine mulDec 34 173 mulDec_173 Inv (un + 1) hbody 0 s0 (by omega) h0
  exact ⟨s', hr, hf, hm, hkp⟩

/-! ## 5. The outer loop -/

theorem mulDec_head : mulDec = (mulPre.map RInstr.op ++ [RInstr.jcc 4 182]) ++ mulOHead.map RInstr.op
      ++ ([RInstr.jcc 4 174] ++ mulInner.map RInstr.op ++ [RInstr.jcc 5 34]
        ++ mulOTail.map RInstr.op ++ [RInstr.jcc 5 26] ++ mulPost.map RInstr.op ++ [RInstr.ret]) := by
  simp only [mulDec, List.append_assoc]

theorem mulDec_tail : mulDec = (mulPre.map RInstr.op ++ [RInstr.jcc 4 182] ++ mulOHead.map RInstr.op
      ++ [RInstr.jcc 4 174] ++ mulInner.map RInstr.op ++ [RInstr.jcc 5 34]) ++ mulOTail.map RInstr.op
      ++ ([RInstr.jcc 5 26] ++ mulPost.map RInstr.op ++ [RInstr.ret]) := by
  simp only [mulDec, List.append_assoc]

theorem mulDec_pre : mulDec = ([] : List RInstr) ++ mulPre.map RInstr.op
      ++ ([RInstr.jcc 4 182] ++ mulOHead.map RInstr.op ++ [RInstr.jcc 4 174] ++ mulInner.map RInstr.op
        ++ [RInstr.jcc 5 34] ++ mulOTail.map RInstr.op ++ [RInstr.jcc 5 26] ++ mulPost.map RInstr.op
        ++ [RInstr.ret]) := by
  simp only [mulDec, List.append_assoc, List.nil_append]

theorem mulDec_post : mulDec = (mulPre.map RInstr.op ++ [RInstr.jcc 4 182] ++ mulOHead.map RInstr.op
      ++ [RInstr.jcc 4 174] ++ mulInner.map RInstr.op ++ [RInstr.jcc 5 34] ++ mulOTail.map RInstr.op
      ++ [RInstr.jcc 5 26]) ++ mulPost.map RInstr.op ++ [RInstr.ret] := by
  simp only [mulDec, List.append_assoc]

theorem reach_head (s : AState) : Reaches aMachine mulDec 26 s 33 (runBlockA s mulOHead) := by
  have h := reaches_ops aMachine (mulPre.map RInstr.op ++ [RInstr.jcc 4 182]) mulOHead
    ([RInstr.jcc 4 174] ++ mulInner.map RInstr.op ++ [RInstr.jcc 5 34]
        ++ mulOTail.map RInstr.op ++ [RInstr.jcc 5 26] ++ mulPost.map RInstr.op ++ [RInstr.ret]) s
  rw [aMachine_runBlock, ← mulDec_head] at h
  exact h

theorem reach_tail (s : AState) : Reaches aMachine mulDec 174 s 181 (runBlockA s mulOTail) := by
  have h := reaches_ops aMachine (mulPre.map RInstr.op ++ [RInstr.jcc 4 182] ++ mulOHead.map RInstr.op
      ++ [RInstr.jcc 4 174] ++ mulInner.map RInstr.op ++ [RInstr.jcc 5 34]) mulOTail
    ([RInstr.jcc 5 26] ++ mulPost.map RInstr.op ++ [RInstr.ret]) s
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    mulPre_length, mulOHead_length, mulInner_length, mulOTail_length] at h
  rw [aMachine_runBlock, ← mulDec_tail] at h
  exact h

theorem reach_pre (s : AState) : Reaches aMachine mulDec 0 s 25 (runBlockA s mulPre) := by
  have h := reaches_ops aMachine [] mulPre
    ([RInstr.jcc 4 182] ++ mulOHead.map RInstr.op ++ [RInstr.jcc 4 174] ++ mulInner.map RInstr.op
        ++ [RInstr.jcc 5 34] ++ mulOTail.map RInstr.op ++ [RInstr.jcc 5 26] ++ mulPost.map RInstr.op
        ++ [RInstr.ret]) s
  rw [aMachine_runBlock, ← mulDec_pre] at h
  exact h

theorem reach_post (s : AState) : Reaches aMachine mulDec 182 s 189 (runBlockA s mulPost) := by
  have h := reaches_ops aMachine (mulPre.map RInstr.op ++ [RInstr.jcc 4 182] ++ mulOHead.map RInstr.op
      ++ [RInstr.jcc 4 174] ++ mulInner.map RInstr.op ++ [RInstr.jcc 5 34] ++ mulOTail.map RInstr.op
      ++ [RInstr.jcc 5 26]) mulPost [RInstr.ret] s
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    mulPre_length, mulOHead_length, mulInner_length, mulOTail_length] at h
  rw [aMachine_runBlock, ← mulDec_post] at h
  exact h

theorem mulDec_25 : mulDec[25]? = some (.jcc 4 182) := rfl
theorem mulDec_33 : mulDec[33]? = some (.jcc 4 174) := rfl
theorem mulDec_181 : mulDec[181]? = some (.jcc 5 26) := rfl
theorem mulDec_189 : mulDec[189]? = some .ret := rfl

/-- The head of an outer trip: the inner count `un + 1` and the zero inner index. -/
theorem head_run (s : AState) :
    (runBlockA s mulOHead).regs "%r10" = BitVec.ofNat 64 0
    ∧ (runBlockA s mulOHead).regs "%r11" = s.regs "%rdi" + BitVec.ofNat 64 1
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%r10" → r ≠ "%r11" → (runBlockA s mulOHead).regs r = s.regs r)
    ∧ (runBlockA s mulOHead).mem = s.mem
    ∧ (runBlockA s mulOHead).view.flagB (·.zf) = decide (s.regs "%rdi" + BitVec.ofNat 64 1 = 0) := by
  have hsplit : mulOHead = mulOHead.dropLast ++ [.cmp "%r11" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, mulOHead, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_add,
    eA_cmp, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro r h1 h2 h3; simp [h1, h2, h3]
  · trivial
  · simp

/-- The tail of an outer trip: the row index and the outer count stepped. -/
theorem tail_run (s : AState) :
    (runBlockA s mulOTail).regs "%rax" = s.regs "%rax" + BitVec.ofNat 64 1
    ∧ (runBlockA s mulOTail).regs "%r8" = s.regs "%r8" - BitVec.ofNat 64 1
    ∧ (∀ r, r ≠ "%rax" → r ≠ "%r8" → (runBlockA s mulOTail).regs r = s.regs r)
    ∧ (runBlockA s mulOTail).mem = s.mem
    ∧ (runBlockA s mulOTail).view.flagB (·.zf) = decide (s.regs "%r8" - BitVec.ofNat 64 1 = 0) := by
  have hsplit : mulOTail = mulOTail.dropLast ++ [.cmp "%r8" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, mulOTail, runBlockA_cons, runBlockA_nil, eA_add_imm, eA_sub_imm,
    eA_cmp, eA_cmpMem, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro r h1 h2; simp [h1, h2]
  · trivial
  · simp

/-- **The outer loop is the fold `bcFold`.** From index `26`, with the row index `0` and the
    outer count `vn > 0`, the machine reaches index `182` with `bcFold` of the accumulator in
    the words of `rp` and the frame base, `un`, and the invariant kept. -/
theorem outer_loop {SP RP UP VP : BitVec 64} {un vn : Nat} {U V : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : MulSep SP RP UP VP un vn)
    (hsv : ∀ e ∈ saved, e.1 ∈ keepOffs) (hvn : 0 < vn)
    (acc : Fin (un + vn + 1) → BitVec 64) (s0 : AState)
    (hrsp : s0.regs "%rsp" = SP) (hrdi : s0.regs "%rdi" = BitVec.ofNat 64 un)
    (hrax : s0.regs "%rax" = BitVec.ofNat 64 0) (hr8 : s0.regs "%r8" = BitVec.ofNat 64 vn)
    (hM : MulMem SP RP UP VP un vn U V (memGetDyn acc) saved s0.mem) :
    ∃ s', Reaches aMachine mulDec 26 s0 182 s'
      ∧ s'.regs "%rsp" = SP
      ∧ MulMem SP RP UP VP un vn U V
          (memGetDyn (bcFold (arr un U) (arr vn V) un (un + vn) vn acc)) saved s'.mem
      ∧ Keeps SP RP (un + vn + 1) s0.mem s'.mem := by
  have hb := hS.bound
  let Inv : Nat → AState → Prop := fun j s =>
    s.regs "%rsp" = SP ∧ s.regs "%rdi" = BitVec.ofNat 64 un ∧ s.regs "%rax" = BitVec.ofNat 64 j
      ∧ s.regs "%r8" = BitVec.ofNat 64 (vn - j)
      ∧ MulMem SP RP UP VP un vn U V
          (memGetDyn (bcFold (arr un U) (arr vn V) un (un + vn) j acc)) saved s.mem
      ∧ Keeps SP RP (un + vn + 1) s0.mem s.mem
  have hbody : ∀ j s, j < vn → Inv j s → ∃ s', Reaches aMachine mulDec 26 s 181 s' ∧
      (aMachine.view s').flagB (·.zf) = decide (j + 1 = vn) ∧ Inv (j + 1) s' := by
    intro j s hj ⟨hsp, hdi, hax, h8, hm, hkp⟩
    obtain ⟨e10, e11, fh, mh, zh⟩ := head_run s
    have hguard : RInstrSemantics.step aMachine mulDec 33 (runBlockA s mulOHead)
        = some (.go 34 (runBlockA s mulOHead)) := by
      rw [step_je aMachine mulDec 33 174 _ mulDec_33]
      show some (if (runBlockA s mulOHead).view.flagB (·.zf) = true then _ else _) = _
      rw [zh, hdi, ← BitVec.ofNat_add]
      have hne : ¬ BitVec.ofNat 64 (un + 1) = 0#64 := fun h =>
        absurd ((ofNat_eq_zero_iff (un + 1) (by omega)).mp h) (by omega)
      simp [hne]
    obtain ⟨s2, hr2, f2, m2, k2⟩ := inner_loop hS hsv j hj _ (runBlockA s mulOHead)
      ((fh _ (by decide) (by decide) (by decide)).trans hsp)
      ((fh _ (by decide) (by decide) (by decide)).trans hdi)
      ((fh _ (by decide) (by decide) (by decide)).trans hax) e10
      (by rw [e11, hdi, ← BitVec.ofNat_add]) (by rw [mh]; exact hm)
    have g2 : ∀ r, r ∉ tripRegs → r ≠ "%r9" → r ≠ "%r10" → r ≠ "%r11" → s2.regs r = s.regs r :=
      fun r hr a b c => (f2 r hr).trans (fh r a b c)
    obtain ⟨t1, t2, ft, mt, zt⟩ := tail_run s2
    have e2rax : s2.regs "%rax" = BitVec.ofNat 64 j :=
      (g2 _ (by simp [tripRegs]) (by decide) (by decide) (by decide)).trans hax
    have e2r8 : s2.regs "%r8" = BitVec.ofNat 64 (vn - j - 1 + 1) := by
      rw [g2 _ (by simp [tripRegs]) (by decide) (by decide) (by decide), h8]; congr 1; omega
    refine ⟨runBlockA s2 mulOTail,
      ((reach_head s).trans (.next hguard hr2)).trans (reach_tail s2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runBlockA s2 mulOTail).view.flagB (·.zf) = _
      rw [zt, e2r8, cnt_dec1]
      exact decide_eq_decide.mpr ((ofNat_eq_zero_iff _ (by omega)).trans (by omega))
    · rw [ft _ (by decide) (by decide), g2 _ (by simp [tripRegs]) (by decide) (by decide)
        (by decide), hsp]
    · rw [ft _ (by decide) (by decide), g2 _ (by simp [tripRegs]) (by decide) (by decide)
        (by decide), hdi]
    · rw [t1, e2rax, ← BitVec.ofNat_add]
    · rw [t2, e2r8, cnt_dec1, Nat.sub_sub]
    · rw [mt, bcFold_succ]; exact m2
    · rw [mt]; rw [mh] at k2; exact hkp.trans k2
  have h0 : Inv 0 s0 :=
    ⟨hrsp, hrdi, hrax, by simpa using hr8, by simpa [bcFold] using hM, Keeps.refl _⟩
  obtain ⟨s', hr, hsp, -, -, -, hm, hkp⟩ :=
    reaches_doWhile aMachine mulDec 26 181 mulDec_181 Inv vn hbody 0 s0 hvn h0
  exact ⟨s', hr, hsp, hm, hkp⟩

/-! ## 6. Prologue and epilogue -/

theorem eA_lea_self (sa : AState) (d : String) (o : Int) :
    evalInstrA sa (.lea d d d 0 o) = ⟨upd sa.regs d (at' (sa.regs d) o), sa.flags, sa.mem⟩ := by
  show (⟨_, _, _⟩ : AState) = _
  congr 1
  funext r
  simp [evalInstr, JState.setReg, x86_LEA, AState.view, upd, at']

/-- A word at one frame offset read through a store at another frame offset. -/
theorem rd_at (m : AMem) (p v : BitVec 64) (o o' : Int)
    (h : o = o' ∨ (8 ≤ (o - o').natAbs ∧ (o - o').natAbs ≤ 2 ^ 64 - 8)) :
    read64 (write64 m (at' p o) v) (at' p o') = if o = o' then v else read64 m (at' p o') := by
  by_cases e : o = o'
  · subst e; simp [rd_at_same]
  · simp only [e, ite_false]
    exact rd_at_ne m p v o o' (h.resolve_left e).1 (h.resolve_left e).2

/-- The array part of the memory invariant. -/
structure ArrOK (SP RP UP VP : BitVec 64) (un vn : Nat) (U V R : Nat → BitVec 64) (m : AMem) :
    Prop where
  upw : ∀ j, j < un → read64 m (ix UP (BitVec.ofNat 64 j)) = U j
  vpw : ∀ j, j < vn → read64 m (ix VP (BitVec.ofNat 64 j)) = V j
  rpw : ∀ i, i ≤ un + vn → read64 m (ix RP (BitVec.ofNat 64 i)) = R i

theorem ArrOK.slot {SP RP UP VP : BitVec 64} {un vn : Nat} {U V R : Nat → BitVec 64} {m : AMem}
    (hS : MulSep SP RP UP VP un vn) (o : Int) (ho : o ∈ slotOffs) (v : BitVec 64)
    (h : ArrOK SP RP UP VP un vn U V R m) :
    ArrOK SP RP UP VP un vn U V R (write64 m (at' SP o) v) where
  upw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.us j hj o ho).symm]; exact h.upw j hj
  vpw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.vs j hj o ho).symm]; exact h.vpw j hj
  rpw i hi := by rw [read64_write64_of_disjoint _ _ _ _ (hS.rs i hi o ho).symm]; exact h.rpw i hi

theorem MulMem.of_parts {SP RP UP VP : BitVec 64} {un vn : Nat} {U V R : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} {m : AMem}
    (h1 : read64 m (at' SP 120) = RP) (h2 : read64 m (at' SP 112) = UP)
    (h3 : read64 m (at' SP (-8)) = VP) (h4 : read64 m (at' SP 24) = BitVec.ofNat 64 vn)
    (h5 : ∀ e ∈ saved, read64 m (at' SP e.1) = e.2) (h6 : ArrOK SP RP UP VP un vn U V R m) :
    MulMem SP RP UP VP un vn U V R saved m :=
  ⟨h1, h2, h3, h4, h5, h6.upw, h6.vpw, h6.rpw⟩

/-- The words of the entry memory. -/
def wordsOf (m : AMem) (p : BitVec 64) : Nat → BitVec 64 :=
  fun j => read64 m (ix p (BitVec.ofNat 64 j))

/-- The callee-saved words the prologue stores. -/
def savedOf (s0 : AState) : List (Int × BitVec 64) :=
  [(104, s0.regs "%rbx"), (96, s0.regs "%rbp"), (88, s0.regs "%r12"), (80, s0.regs "%r13"),
    (72, s0.regs "%r14"), (64, s0.regs "%r15")]

theorem savedOf_keep (s0 : AState) : ∀ e ∈ savedOf s0, e.1 ∈ keepOffs := by
  intro e he
  simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepOffs]

/-- **The prologue.** From the entry state, the frame base is `%rsp - 128`, `%rdi` holds
    `un`, `%rax` is `0`, `%r8` holds `vn`, the invariant holds with the entry words of `up`,
    `vp`, `rp` and the callee-saved registers saved, and the zero flag says whether `vn = 0`. -/
theorem pre_run (s0 : AState) (un vn : Nat)
    (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 un) (hr8 : s0.regs "%r8" = BitVec.ofNat 64 vn)
    (hS : MulSep (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      un vn) :
    (runBlockA s0 mulPre).regs "%rsp" = at' (s0.regs "%rsp") (-128)
    ∧ (runBlockA s0 mulPre).regs "%rdi" = BitVec.ofNat 64 un
    ∧ (runBlockA s0 mulPre).regs "%rax" = BitVec.ofNat 64 0
    ∧ (runBlockA s0 mulPre).regs "%r8" = BitVec.ofNat 64 vn
    ∧ MulMem (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") un vn
        (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
        (wordsOf s0.mem (s0.regs "%rdi")) (savedOf s0) (runBlockA s0 mulPre).mem
    ∧ (runBlockA s0 mulPre).view.flagB (·.zf) = decide (BitVec.ofNat 64 vn = 0)
    ∧ Keeps (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (un + vn + 1) s0.mem
        (runBlockA s0 mulPre).mem := by
  have hsplit : mulPre = mulPre.dropLast ++ [.cmp "%r8" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, mulPre, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm,
    eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply, String.reduceEq, ↓reduceIte]
  generalize at' (s0.regs "%rsp") (-128) = SP at hS ⊢
  simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte, true_and]
  refine ⟨hrcx, hr8, MulMem.of_parts ?_ ?_ ?_ ?_ ?_ ?_, by rw [hr8], ?_⟩
  · simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte]
  · simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte]
  · simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte]
  · simp (disch := decide) only [rd_at, Int.reduceNeg, ↓reduceIte, hr8]
  · intro e he
    simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte]
  · iterate 14 refine ArrOK.slot hS _ (by decide) _ ?_
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · iterate 14 refine Keeps.slot hS _ (by decide) _ ?_
    exact Keeps.refl _

/-- The callee-saved registers of the System V ABI. -/
abbrev calleeSavedL : List String := ["%rbx", "%rbp", "%r12", "%r13", "%r14", "%r15"]

/-- **The epilogue.** The callee-saved registers are reloaded from their frame words and the
    frame is released. -/
theorem post_run (s0 s : AState) (SP : BitVec 64) (hrsp : s.regs "%rsp" = SP)
    (hsv : ∀ e ∈ savedOf s0, read64 s.mem (at' SP e.1) = e.2) :
    (runBlockA s mulPost).regs "%rsp" = at' SP 128
    ∧ (∀ R ∈ calleeSavedL, (runBlockA s mulPost).regs R = s0.regs R)
    ∧ (runBlockA s mulPost).mem = s.mem := by
  simp only [mulPost, runBlockA_cons, runBlockA_nil, eA_loadMem, eA_lea_self, upd_apply,
    String.reduceEq, ↓reduceIte]
  refine ⟨by rw [hrsp], ?_, trivial⟩
  intro R hR
  simp only [calleeSavedL, List.mem_cons, List.not_mem_nil, or_false] at hR
  have h := fun o v (h : (o, v) ∈ savedOf s0) => hsv (o, v) h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [String.reduceEq, ↓reduceIte] <;>
    rw [hrsp] <;> exact h _ _ (by simp [savedOf])

theorem at'_at' (E : BitVec 64) : at' (at' E (-128)) 128 = E := by
  simp only [at']
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]
  simp

/-- **The linked `mpn_mul_basecase_rt` halts with the schoolbook fold in `rp`.** From an entry
    state with `rp`, `up`, `vp`, `un`, `vn` in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8` and the words
    separated (`MulSep`, frame base `%rsp - 128`), the machine runs the decoded program to its
    `ret` with the `un + vn + 1` words of `rp` holding `bcFold` of the entry words, `%rsp` and
    the callee-saved registers as at the entry. -/
theorem mul_halts (s0 : AState) (un vn : Nat)
    (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 un) (hr8 : s0.regs "%r8" = BitVec.ofNat 64 vn)
    (hS : MulSep (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      un vn) :
    ∃ s', Halts aMachine mulDec 0 s0 s'
      ∧ (∀ i, i ≤ un + vn → wordsOf s'.mem (s0.regs "%rdi") i
          = memGetDyn (bcFold (arr un (wordsOf s0.mem (s0.regs "%rsi")))
              (arr vn (wordsOf s0.mem (s0.regs "%rdx"))) un (un + vn) vn
              (arr (un + vn + 1) (wordsOf s0.mem (s0.regs "%rdi")))) i)
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
      ∧ Keeps (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (un + vn + 1) s0.mem s'.mem := by
  have hb := hS.bound
  obtain ⟨p1, p2, p3, p4, pM, pz, pk⟩ := pre_run s0 un vn hrcx hr8 hS
  generalize hs1 : runBlockA s0 mulPre = s1 at p1 p2 p3 p4 pM pz pk
  have hr1 : Reaches aMachine mulDec 0 s0 25 s1 := hs1 ▸ reach_pre s0
  have pM' := pM.congr (R' := memGetDyn (arr (un + vn + 1) (wordsOf s0.mem (s0.regs "%rdi"))))
    (fun i hi => (memGetDyn_arr _ _ i (by omega)).symm)
  -- the state at index 182 and its invariant
  obtain ⟨s2, hr2, e2, M2, K2⟩ : ∃ s2, Reaches aMachine mulDec 0 s0 182 s2
      ∧ s2.regs "%rsp" = at' (s0.regs "%rsp") (-128)
      ∧ MulMem (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
          un vn (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
          (memGetDyn (bcFold (arr un (wordsOf s0.mem (s0.regs "%rsi")))
              (arr vn (wordsOf s0.mem (s0.regs "%rdx"))) un (un + vn) vn
              (arr (un + vn + 1) (wordsOf s0.mem (s0.regs "%rdi"))))) (savedOf s0) s2.mem
      ∧ Keeps (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (un + vn + 1) s0.mem s2.mem := by
    by_cases hv : vn = 0
    · subst hv
      refine ⟨s1, hr1.trans (.single ?_), p1, by simpa [bcFold] using pM', pk⟩
      rw [step_je aMachine mulDec 25 182 s1 mulDec_25]
      show some (if s1.view.flagB (·.zf) = true then _ else _) = _
      rw [pz]; simp
    · have hstep : RInstrSemantics.step aMachine mulDec 25 s1 = some (.go 26 s1) := by
        rw [step_je aMachine mulDec 25 182 s1 mulDec_25]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        have hne : ¬ BitVec.ofNat 64 vn = 0#64 := fun h =>
          hv ((ofNat_eq_zero_iff vn (by omega)).mp h)
        rw [pz]; simp [hne]
      obtain ⟨s2, hr2, e2, M2, K2⟩ := outer_loop hS (savedOf_keep s0) (Nat.pos_of_ne_zero hv) _ s1
        p1 p2 p3 p4 pM'
      exact ⟨s2, hr1.trans (.next hstep hr2), e2, M2, pk.trans K2⟩
  obtain ⟨q1, q2, q3⟩ := post_run s0 s2 _ e2 M2.saved
  refine ⟨runBlockA s2 mulPost, halts_of_reaches (hr2.trans (reach_post s2)) mulDec_189, ?_,
    by rw [q1, at'_at'], q2, by rw [q3]; exact K2⟩
  intro i hi
  rw [wordsOf, q3]
  exact M2.rpw i hi

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
