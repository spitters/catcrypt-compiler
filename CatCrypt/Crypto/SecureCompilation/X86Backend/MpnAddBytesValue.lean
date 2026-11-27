/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubShipped
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCarryIdiomsHand

@[expose] public section

set_option autoImplicit false

/-!
# The linked `mpn_add_n_loop_owned` writes the sum and returns the carry

The decoded program `MpnAddSubShipped.addDec` of the linked object is run on the address
machine `aMachine`. One trip (`addBody`, four straight segments) performs
`MpnAddSubFrontDenote.addStep` on the output words and the carry register `%rax`
(`add_trip`); the loop performs the fold `addFold` (`add_loop`); with the prologue and the
epilogue the machine halts at the `ret` with `addFold` of the entry words in `rp` and its carry
in `%rax` (`add_halts`).

## The state of the loop

At the head of trip `k` the registers hold the frame base `%rsp = SP`, the index `%rdi = k`,
the count `%rbp = n - k` and the carry `%rax`; the frame words hold the pointers (`rp` at `56`,
`ap` at `48`, `bp` at `-8`) and the callee-saved registers at `0`–`40` (`AddMem.saved`); the
words `k ≤ j < n` of `ap` and `bp` are unchanged; the `n` words of `rp` hold the accumulator.
Only the words of `ap` and `bp` from the trip index on are kept, so `rp` may coincide with
`ap` or `bp` (in-place, as GMP's `mpn_add_n` allows) or lie below them.

## Main results

* `add_trip`: one trip of the add loop applies `addStep` to the output word and the carry register.
* `add_loop`: the loop computes the fold `addFold` over the `n` limbs of `ap` and `bp`.
* `add_halts`: from every entry state with the words separated, the machine halts at the `ret`
  with `addFold` of the entry words in `rp` and its carry in `%rax`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubShipped
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
  (upd upd_apply flA ix at' eA_mov_reg eA_mov_imm eA_xor eA_and eA_add eA_add_imm eA_sub_imm
   eA_shr63 eA_cmp eA_loadMem eA_loadMemIdx eA_storeMem eA_storeMemIdx cmp0_zf rd_at_ne
   rd_at_same)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
  (arr memGetDyn_arr cnt_dec ofNat_eq_zero_iff eA_lea_self rd_at wordsOf calleeSavedL)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn memGetDyn_memSetDyn)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
  (halfCarryW addLimbW addStep addFold addFold_succ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach (reaches_doWhile step_je)

/-! ## 1. The segments of the trip -/

theorem eA_shr1 (sa : AState) (d : String) :
    evalInstrA sa (.shr d (.imm 1))
      = ⟨upd sa.regs d (sa.regs d >>> 1), flA sa (.shr d (.imm 1)), sa.mem⟩ := by
  have h : (x86_SHR (sa.regs d) (BitVec.ofNat 64 1)).word = sa.regs d >>> 1 := by
    simp [x86_SHR, shiftCount, rflags_OF, wshr]
  show (⟨_, _, _⟩ : AState) = _
  congr 1

theorem and_allOnes (x : BitVec 64) : x &&& 18446744073709551615#64 = x := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

def aL : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rdi")
  , .loadMem "%r14" "%rsp" 48
  , .loadMemIdx "%r8" "%r14" "%rsi" 8
  , .loadMem "%r14" "%rsp" (-8)
  , .loadMemIdx "%r9" "%r14" "%rsi" 8 ]

def aC1 : List (JInstr 64) :=
  [ .mov "%r10" (.imm 1)
  , .mov "%r10" (.reg "%r8")
  , .shr "%r10" (.imm 1)
  , .mov "%r11" (.imm 1)
  , .mov "%r11" (.reg "%r9")
  , .shr "%r11" (.imm 1)
  , .mov "%r12" (.reg "%r10")
  , .add "%r12" (.reg "%r11")
  , .mov "%r10" (.reg "%r8")
  , .and_ "%r10" (.reg "%r9")
  , .mov "%r11" (.imm 1)
  , .mov "%r13" (.reg "%r10")
  , .and_ "%r13" (.reg "%r11")
  , .mov "%r10" (.reg "%r12")
  , .add "%r10" (.reg "%r13")
  , .mov "%r11" (.imm 63)
  , .mov "%r11" (.reg "%r10")
  , .shr "%r11" (.imm 63)
  , .mov "%r10" (.reg "%r11")
  , .mov "%r11" (.reg "%r8")
  , .add "%r11" (.reg "%r9")
  , .mov "%r8" (.imm 18446744073709551615)
  , .mov "%r9" (.reg "%r11")
  , .and_ "%r9" (.reg "%r8")
  , .mov "%r8" (.reg "%r9") ]

def aC2 : List (JInstr 64) :=
  [ .mov "%r9" (.imm 1)
  , .mov "%r9" (.reg "%r8")
  , .shr "%r9" (.imm 1)
  , .mov "%r11" (.imm 1)
  , .mov "%r11" (.reg "%rax")
  , .shr "%r11" (.imm 1)
  , .mov "%r12" (.reg "%r9")
  , .add "%r12" (.reg "%r11")
  , .mov "%r9" (.reg "%r8")
  , .and_ "%r9" (.reg "%rax")
  , .mov "%r11" (.imm 1)
  , .mov "%r13" (.reg "%r9")
  , .and_ "%r13" (.reg "%r11")
  , .mov "%r9" (.reg "%r12")
  , .add "%r9" (.reg "%r13")
  , .mov "%r11" (.imm 63)
  , .mov "%r11" (.reg "%r9")
  , .shr "%r11" (.imm 63)
  , .mov "%r9" (.reg "%r11")
  , .mov "%r11" (.reg "%r8")
  , .add "%r11" (.reg "%rax")
  , .mov "%r8" (.imm 18446744073709551615)
  , .mov "%r12" (.reg "%r11")
  , .and_ "%r12" (.reg "%r8")
  , .mov "%r8" (.reg "%r12") ]

def aT : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rsi" 8 (.reg "%r8")
  , .mov "%rsi" (.reg "%r10")
  , .add "%rsi" (.reg "%r9")
  , .mov "%r8" (.reg "%rsi")
  , .mov "%rax" (.reg "%r8")
  , .add "%rdi" (.imm 1)
  , .sub "%rbp" (.imm 1)
  , .cmp "%rbp" (.reg "%rcx")
  , .cmp "%rbp" (.reg "%rdx")
  , .cmp "%rbp" (.reg "%rbx")
  , .cmp "%rbp" (.imm 0) ]

theorem addBody_eq : addBody = aL ++ aC1 ++ aC2 ++ aT := rfl

/-- The limb loads: `%r8 = ap[i]`, `%r9 = bp[i]` for the index `i` in `%rdi`. -/
theorem aL_run (sa : AState) (AP BP : BitVec 64)
    (hap : read64 sa.mem (at' (sa.regs "%rsp") 48) = AP)
    (hbp : read64 sa.mem (at' (sa.regs "%rsp") (-8)) = BP) :
    (runBlockA sa aL).regs "%r8" = read64 sa.mem (ix AP (sa.regs "%rdi"))
    ∧ (runBlockA sa aL).regs "%r9" = read64 sa.mem (ix BP (sa.regs "%rdi"))
    ∧ (runBlockA sa aL).regs "%rsi" = sa.regs "%rdi"
    ∧ (∀ r, r ≠ "%rsi" → r ≠ "%r14" → r ≠ "%r8" → r ≠ "%r9" →
        (runBlockA sa aL).regs r = sa.regs r)
    ∧ (runBlockA sa aL).mem = sa.mem := by
  simp only [aL, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_loadMem, eA_loadMemIdx, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hap]
  · simp [hbp]
  · simp
  · intro r h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  · trivial

/-- The first half-add: `%r10` is the carry of `x + y`, `%r8` the sum, for `x`, `y` in
    `%r8`, `%r9`. -/
theorem aC1_run (sa : AState) :
    (runBlockA sa aC1).regs "%r10" = halfCarryW (sa.regs "%r8") (sa.regs "%r9")
    ∧ (runBlockA sa aC1).regs "%r8" = sa.regs "%r8" + sa.regs "%r9"
    ∧ (∀ r, r ≠ "%r8" → r ≠ "%r9" → r ≠ "%r10" → r ≠ "%r11" → r ≠ "%r12" → r ≠ "%r13" →
        (runBlockA sa aC1).regs r = sa.regs r)
    ∧ (runBlockA sa aC1).mem = sa.mem := by
  simp only [aC1, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_add, eA_and,
    eA_shr1, eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]; rfl
  · simp only [String.reduceEq, ↓reduceIte]; exact and_allOnes _
  · intro r h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
  · trivial

/-- The second half-add: `%r9` is the carry of `s + c`, `%r8` the sum, for `s`, `c` in
    `%r8`, `%rax`. -/
theorem aC2_run (sa : AState) :
    (runBlockA sa aC2).regs "%r9" = halfCarryW (sa.regs "%r8") (sa.regs "%rax")
    ∧ (runBlockA sa aC2).regs "%r8" = sa.regs "%r8" + sa.regs "%rax"
    ∧ (∀ r, r ≠ "%r8" → r ≠ "%r9" → r ≠ "%r11" → r ≠ "%r12" → r ≠ "%r13" →
        (runBlockA sa aC2).regs r = sa.regs r)
    ∧ (runBlockA sa aC2).mem = sa.mem := by
  simp only [aC2, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_add, eA_and,
    eA_shr1, eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]; rfl
  · simp only [String.reduceEq, ↓reduceIte]; exact and_allOnes _
  · intro r h1 h2 h3 h4 h5
    simp [h1, h2, h3, h4, h5]
  · trivial

/-- The output store `rp[i] = %r8` at the index `i` in `%rsi`, the carry-out
    `%rax = %r10 + %r9`, the index and count steps and the back-edge compare. -/
theorem aT_run (sa : AState) (RP : BitVec 64)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 56) = RP) :
    (runBlockA sa aT).mem = write64 sa.mem (ix RP (sa.regs "%rsi")) (sa.regs "%r8")
    ∧ (runBlockA sa aT).regs "%rax" = sa.regs "%r10" + sa.regs "%r9"
    ∧ (runBlockA sa aT).regs "%rdi" = sa.regs "%rdi" + 1
    ∧ (runBlockA sa aT).regs "%rbp" = sa.regs "%rbp" - 1
    ∧ (∀ r, r ≠ "%r14" → r ≠ "%rsi" → r ≠ "%r8" → r ≠ "%rax" → r ≠ "%rdi" → r ≠ "%rbp" →
        (runBlockA sa aT).regs r = sa.regs r)
    ∧ (runBlockA sa aT).view.flagB (·.zf) = decide (sa.regs "%rbp" - 1 = 0) := by
  have hsplit : aT = aT.dropLast ++ [.cmp "%rbp" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, aT, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_add, eA_add_imm,
    eA_sub_imm, eA_loadMem, eA_storeMemIdx, eA_cmp, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrp]
  · simp
  · simp
  · simp
  · intro r h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
  · simp

/-! ## 2. Separation and the memory invariant -/

/-- The frame words of the function, by offset from the frame base. -/
def addOffs : List Int := [-16, -8, 0, 8, 16, 24, 32, 40, 48, 56]

/-- The `80` bytes of the frame: from `SP - 16` (the lowest red-zone word the function
    writes) to `SP + 64` (the entry stack pointer). -/
def InFrB (SP x : BitVec 64) : Prop := (x - at' SP (-16)).toNat < 80

/-- The bytes of the first `n` words of `rp`. -/
def InOutB (RP : BitVec 64) (n : Nat) (x : BitVec 64) : Prop :=
  ∃ j, j < n ∧ InRange8 (ix RP (BitVec.ofNat 64 j)) x

/-- **Word-level separation.** The `n` words of `rp` are pairwise disjoint and disjoint from
    the frame words; word `i` of `rp` is disjoint from the words `j > i` of `ap` and `bp` (so
    `rp = ap`, `rp = bp` and `rp` below the sources are allowed); the words of `ap` and `bp`
    are disjoint from the frame words. -/
structure AddSep (SP RP AP BP : BitVec 64) (n : Nat) : Prop where
  rr : ∀ i j, i < n → j < n → i ≠ j →
    Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix RP (BitVec.ofNat 64 j))
  rs : ∀ i, i < n → ∀ o ∈ addOffs, Disjoint8 (ix RP (BitVec.ofNat 64 i)) (at' SP o)
  ra : ∀ i j, i < j → j < n → Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix AP (BitVec.ofNat 64 j))
  rb : ∀ i j, i < j → j < n → Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix BP (BitVec.ofNat 64 j))
  as : ∀ j, j < n → ∀ o ∈ addOffs, Disjoint8 (ix AP (BitVec.ofNat 64 j)) (at' SP o)
  bs : ∀ j, j < n → ∀ o ∈ addOffs, Disjoint8 (ix BP (BitVec.ofNat 64 j)) (at' SP o)
  bound : n < 2 ^ 64
  fr : ∀ o ∈ addOffs, ∀ x, InRange8 (at' SP o) x → InFrB SP x

/-- **The memory invariant of the loop at trip `k`.** The pointer words of the frame, the
    words `saved`, the words `k ≤ j < n` of `ap` and `bp`, and the accumulator `R` in the `n`
    words of `rp`. -/
structure AddMem (SP RP AP BP : BitVec 64) (n k : Nat) (A B R : Nat → BitVec 64)
    (saved : List (Int × BitVec 64)) (m : AMem) : Prop where
  rp : read64 m (at' SP 56) = RP
  ap : read64 m (at' SP 48) = AP
  bp : read64 m (at' SP (-8)) = BP
  saved : ∀ e ∈ saved, read64 m (at' SP e.1) = e.2
  apw : ∀ j, k ≤ j → j < n → read64 m (ix AP (BitVec.ofNat 64 j)) = A j
  bpw : ∀ j, k ≤ j → j < n → read64 m (ix BP (BitVec.ofNat 64 j)) = B j
  rpw : ∀ i, i < n → read64 m (ix RP (BitVec.ofNat 64 i)) = R i

/-- A store to word `k` of `rp` moves the invariant to trip `k + 1` with the accumulator
    updated at `k`. -/
theorem AddMem.out {SP RP AP BP : BitVec 64} {n k : Nat} {A B R : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : AddSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) {m : AMem} (h : AddMem SP RP AP BP n k A B R saved m)
    (hk : k < n) (v : BitVec 64) :
    AddMem SP RP AP BP n (k + 1) A B (fun i => if i = k then v else R i) saved
      (write64 m (ix RP (BitVec.ofNat 64 k)) v) := by
  have far : ∀ a ∈ addOffs, read64 (write64 m (ix RP (BitVec.ofNat 64 k)) v) (at' SP a)
      = read64 m (at' SP a) :=
    fun a ha => read64_write64_of_disjoint _ _ _ _ (hS.rs k hk a ha)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [far 56 (by decide)]; exact h.rp
  · rw [far 48 (by decide)]; exact h.ap
  · rw [far (-8) (by decide)]; exact h.bp
  · intro e he; rw [far e.1 (hsv e he)]; exact h.saved e he
  · intro j hj hjn
    rw [read64_write64_of_disjoint _ _ _ _ (hS.ra k j (by omega) hjn)]
    exact h.apw j (by omega) hjn
  · intro j hj hjn
    rw [read64_write64_of_disjoint _ _ _ _ (hS.rb k j (by omega) hjn)]
    exact h.bpw j (by omega) hjn
  · intro i hi
    by_cases hik : i = k
    · subst hik; simp [read64_write64_same]
    · rw [read64_write64_of_disjoint _ _ _ _ (hS.rr k i hk hi (Ne.symm hik))]
      simp [hik, h.rpw i hi]

theorem AddMem.congr {SP RP AP BP : BitVec 64} {n k : Nat} {A B R R' : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} {m : AMem} (h : AddMem SP RP AP BP n k A B R saved m)
    (hR : ∀ i, i < n → R i = R' i) : AddMem SP RP AP BP n k A B R' saved m :=
  ⟨h.rp, h.ap, h.bp, h.saved, h.apw, h.bpw, fun i hi => (h.rpw i hi).trans (hR i hi)⟩

/-- The memory `m'` agrees with `m` outside the frame bytes and the first `n` words of `rp`. -/
def Keeps (SP RP : BitVec 64) (n : Nat) (m m' : AMem) : Prop :=
  ∀ x, ¬ InFrB SP x → ¬ InOutB RP n x → m' x = m x

theorem Keeps.refl {SP RP : BitVec 64} {n : Nat} (m : AMem) : Keeps SP RP n m m :=
  fun _ _ _ => rfl

theorem Keeps.trans {SP RP : BitVec 64} {n : Nat} {m m' m'' : AMem} (h : Keeps SP RP n m m')
    (h' : Keeps SP RP n m' m'') : Keeps SP RP n m m'' :=
  fun x a b => (h' x a b).trans (h x a b)

theorem Keeps.slot {SP RP AP BP : BitVec 64} {n : Nat} (hS : AddSep SP RP AP BP n)
    {m m' : AMem} (o : Int) (ho : o ∈ addOffs) (v : BitVec 64) (h : Keeps SP RP n m m') :
    Keeps SP RP n m (write64 m' (at' SP o) v) := fun x a b => by
  rw [write64_of_not_inRange _ _ _ _ (fun hr => a (hS.fr o ho x hr))]; exact h x a b

theorem Keeps.out {SP RP : BitVec 64} {n : Nat} {m m' : AMem} (p : Nat) (hp : p < n)
    (v : BitVec 64) (h : Keeps SP RP n m m') :
    Keeps SP RP n m (write64 m' (ix RP (BitVec.ofNat 64 p)) v) := fun x a b => by
  rw [write64_of_not_inRange _ _ _ _ (fun hr => b ⟨p, hp, hr⟩)]; exact h x a b

/-! ## 3. One trip -/

/-- The registers a trip writes. -/
def addTripRegs : List String :=
  ["%rsi", "%r14", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%rax", "%rdi", "%rbp"]

/-- The machine's carry-out is the word model's. -/
theorem add_carry (x y c : BitVec 64) :
    halfCarryW x y + halfCarryW (x + y) c = (addLimbW x y c).2 := by
  rw [MpnCarryIdiomsHand.halfCarryW_eq_hand, MpnCarryIdiomsHand.halfCarryW_eq_hand]; rfl

/-- **One trip is `addStep`.** From a state at the head of trip `k < n` with the accumulator
    `acc` in the words of `rp` and the carry `c` in `%rax`, `runBlockA` of the trip leaves the
    first component of `addStep (acc, c) k` in the words of `rp` and the second in `%rax`,
    moves the invariant to trip `k + 1`, steps the index and the count, writes no register
    outside `addTripRegs`, and sets the zero flag exactly when the decremented count is zero. -/
theorem add_trip {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : AddSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) (k : Nat) (hk : k < n)
    (acc : Fin n → BitVec 64) (c : BitVec 64) (sa : AState)
    (hrsp : sa.regs "%rsp" = SP) (hrdi : sa.regs "%rdi" = BitVec.ofNat 64 k)
    (hrax : sa.regs "%rax" = c)
    (hM : AddMem SP RP AP BP n k A B (memGetDyn acc) saved sa.mem) :
    AddMem SP RP AP BP n (k + 1) A B
        (memGetDyn (addStep (arr n A) (arr n B) (acc, c) k).1) saved (runBlockA sa addBody).mem
    ∧ (runBlockA sa addBody).regs "%rax" = (addStep (arr n A) (arr n B) (acc, c) k).2
    ∧ (runBlockA sa addBody).regs "%rdi" = BitVec.ofNat 64 (k + 1)
    ∧ (runBlockA sa addBody).regs "%rbp" = sa.regs "%rbp" - 1
    ∧ (∀ r, r ∉ addTripRegs → (runBlockA sa addBody).regs r = sa.regs r)
    ∧ (runBlockA sa addBody).view.flagB (·.zf) = decide (sa.regs "%rbp" - 1 = 0)
    ∧ Keeps SP RP n sa.mem (runBlockA sa addBody).mem := by
  rw [addBody_eq]
  simp only [runBlockA_append]
  -- loads
  obtain ⟨l8, l9, lsi, fL, mL⟩ := aL_run sa AP BP (by rw [hrsp]; exact hM.ap)
    (by rw [hrsp]; exact hM.bp)
  generalize hs1 : runBlockA sa aL = s1 at l8 l9 lsi fL mL
  rw [hrdi, hM.apw k le_rfl hk] at l8
  rw [hrdi, hM.bpw k le_rfl hk] at l9
  rw [hrdi] at lsi
  -- first half-add
  obtain ⟨c10, c8, fC1, mC1⟩ := aC1_run s1
  generalize hs2 : runBlockA s1 aC1 = s2 at c10 c8 fC1 mC1
  rw [l8, l9] at c10 c8
  -- second half-add
  obtain ⟨d9, d8, fC2, mC2⟩ := aC2_run s2
  generalize hs3 : runBlockA s2 aC2 = s3 at d9 d8 fC2 mC2
  have e2rax : s2.regs "%rax" = c :=
    (fC1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((fL _ (by decide) (by decide) (by decide) (by decide)).trans hrax)
  rw [c8, e2rax] at d9 d8
  have fr3 : ∀ r, r ∉ addTripRegs → s3.regs r = sa.regs r := by
    intro r hr
    simp only [addTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, d, e, g, h, i, j, -, -, -⟩ := hr
    exact (fC2 r d e h i j).trans ((fC1 r d e g h i j).trans (fL r a b d e))
  have e3rsp : s3.regs "%rsp" = SP := (fr3 _ (by decide)).trans hrsp
  have e3r10 : s3.regs "%r10" = halfCarryW (A k) (B k) :=
    (fC2 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans c10
  have e3rsi : s3.regs "%rsi" = BitVec.ofNat 64 k :=
    (fC2 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((fC1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans lsi)
  have e3rdi : s3.regs "%rdi" = BitVec.ofNat 64 k :=
    (fC2 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((fC1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((fL _ (by decide) (by decide) (by decide) (by decide)).trans hrdi))
  have e3rbp : s3.regs "%rbp" = sa.regs "%rbp" :=
    (fC2 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((fC1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (fL _ (by decide) (by decide) (by decide) (by decide)))
  have m3 : s3.mem = sa.mem := by rw [mC2, mC1, mL]
  -- tail
  obtain ⟨tm, trax, trdi, trbp, fT, tz⟩ := aT_run s3 RP (by rw [e3rsp, m3]; exact hM.rp)
  generalize hs4 : runBlockA s3 aT = s4 at tm trax trdi trbp fT tz
  rw [e3rsi, d8, m3] at tm
  rw [e3r10, d9, add_carry] at trax
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm]
    refine (hM.out hS hsv hk _).congr ?_
    intro i hi
    simp only [addStep, memGetDyn_memSetDyn _ hk hi, memGetDyn_arr n A k hk,
      memGetDyn_arr n B k hk, addLimbW]
  · rw [trax]; simp only [addStep, memGetDyn_arr n A k hk, memGetDyn_arr n B k hk]
  · rw [trdi, e3rdi]; simp [BitVec.ofNat_add]
  · rw [trbp, e3rbp]
  · intro r hr
    have hr' := hr
    simp only [addTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨a, b, d, -, -, -, -, -, g, h, i⟩ := hr'
    rw [fT r b a d g h i]; exact fr3 r hr
  · rw [tz, e3rbp]
  · rw [tm]; exact Keeps.out _ hk _ (Keeps.refl _)

/-! ## 4. The loop -/

theorem addDec_body : addDec = (addPre.map RInstr.op ++ [RInstr.jcc 4 88]) ++ addBody.map RInstr.op
      ++ ([RInstr.jcc 5 20] ++ addPost.map RInstr.op ++ [RInstr.ret]) := by
  simp only [addDec, List.append_assoc]

theorem addDec_pre : addDec = ([] : List RInstr) ++ addPre.map RInstr.op
      ++ ([RInstr.jcc 4 88] ++ addBody.map RInstr.op ++ [RInstr.jcc 5 20]
        ++ addPost.map RInstr.op ++ [RInstr.ret]) := by
  simp only [addDec, List.append_assoc, List.nil_append]

theorem addDec_post : addDec = (addPre.map RInstr.op ++ [RInstr.jcc 4 88] ++ addBody.map RInstr.op
      ++ [RInstr.jcc 5 20]) ++ addPost.map RInstr.op ++ [RInstr.ret] := by
  simp only [addDec, List.append_assoc]

/-- From index `20`, a trip runs as `runBlockA` to the back edge at `87`. -/
theorem reach_body (s : AState) : Reaches aMachine addDec 20 s 87 (runBlockA s addBody) := by
  have h := reaches_ops aMachine (addPre.map RInstr.op ++ [RInstr.jcc 4 88]) addBody
    ([RInstr.jcc 5 20] ++ addPost.map RInstr.op ++ [RInstr.ret]) s
  rw [aMachine_runBlock, ← addDec_body] at h
  exact h

theorem reach_pre (s : AState) : Reaches aMachine addDec 0 s 19 (runBlockA s addPre) := by
  have h := reaches_ops aMachine [] addPre
    ([RInstr.jcc 4 88] ++ addBody.map RInstr.op ++ [RInstr.jcc 5 20]
      ++ addPost.map RInstr.op ++ [RInstr.ret]) s
  rw [aMachine_runBlock, ← addDec_pre] at h
  exact h

theorem reach_post (s : AState) : Reaches aMachine addDec 88 s 95 (runBlockA s addPost) := by
  have h := reaches_ops aMachine (addPre.map RInstr.op ++ [RInstr.jcc 4 88]
      ++ addBody.map RInstr.op ++ [RInstr.jcc 5 20]) addPost [RInstr.ret] s
  rw [aMachine_runBlock, ← addDec_post] at h
  exact h

theorem addDec_19 : addDec[19]? = some (.jcc 4 88) := rfl
theorem addDec_87 : addDec[87]? = some (.jcc 5 20) := rfl
theorem addDec_95 : addDec[95]? = some .ret := rfl

/-- **The loop is the fold `addFold`.** From index `20` with the index `0`, the count `n > 0`
    and the carry `0`, the machine reaches index `88` with the first component of
    `addFold (acc, 0) n` in the words of `rp`, its carry in `%rax`, the invariant at trip `n`,
    and no register outside `addTripRegs` written. -/
theorem add_loop {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : AddSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) (hn : 0 < n) (acc : Fin n → BitVec 64) (s0 : AState)
    (hrsp : s0.regs "%rsp" = SP) (hrdi : s0.regs "%rdi" = BitVec.ofNat 64 0)
    (hrbp : s0.regs "%rbp" = BitVec.ofNat 64 n) (hrax : s0.regs "%rax" = BitVec.ofNat 64 0)
    (hM : AddMem SP RP AP BP n 0 A B (memGetDyn acc) saved s0.mem) :
    ∃ s', Reaches aMachine addDec 20 s0 88 s'
      ∧ (∀ r, r ∉ addTripRegs → s'.regs r = s0.regs r)
      ∧ s'.regs "%rax" = (addFold (arr n A) (arr n B) n (acc, 0#64)).2
      ∧ AddMem SP RP AP BP n n A B
          (memGetDyn (addFold (arr n A) (arr n B) n (acc, 0#64)).1) saved s'.mem
      ∧ Keeps SP RP n s0.mem s'.mem := by
  have hb := hS.bound
  let Inv : Nat → AState → Prop := fun k s =>
    (∀ r, r ∉ addTripRegs → s.regs r = s0.regs r) ∧ s.regs "%rdi" = BitVec.ofNat 64 k
      ∧ s.regs "%rbp" = BitVec.ofNat 64 (n - k)
      ∧ s.regs "%rax" = (addFold (arr n A) (arr n B) k (acc, 0#64)).2
      ∧ AddMem SP RP AP BP n k A B
          (memGetDyn (addFold (arr n A) (arr n B) k (acc, 0#64)).1) saved s.mem
      ∧ Keeps SP RP n s0.mem s.mem
  have hbody : ∀ k s, k < n → Inv k s → ∃ s', Reaches aMachine addDec 20 s 87 s' ∧
      (aMachine.view s').flagB (·.zf) = decide (k + 1 = n) ∧ Inv (k + 1) s' := by
    intro k s hk ⟨hf, hdi, hbp, hax, hm, hkp⟩
    obtain ⟨M', eax, edi, ebp, f', z', kp'⟩ := add_trip hS hsv k hk _ _ s
      ((hf _ (by simp [addTripRegs])).trans hrsp) hdi hax hm
    have hbp' : s.regs "%rbp" = BitVec.ofNat 64 (n - k - 1 + 1) := by
      rw [hbp]; congr 1; omega
    refine ⟨runBlockA s addBody, reach_body s, ?_, ?_, edi, ?_, ?_, ?_, hkp.trans kp'⟩
    · show (runBlockA s addBody).view.flagB (·.zf) = _
      rw [z', hbp', cnt_dec]
      exact decide_eq_decide.mpr ((ofNat_eq_zero_iff _ (by omega)).trans (by omega))
    · intro r hr; exact (f' r hr).trans (hf r hr)
    · rw [ebp, hbp', cnt_dec]; congr 1
    · rw [eax, addFold_succ]
    · rw [addFold_succ]; exact M'
  have h0 : Inv 0 s0 :=
    ⟨fun _ _ => rfl, hrdi, by simpa using hrbp, by simpa [addFold] using hrax,
      by simpa [addFold] using hM, Keeps.refl _⟩
  obtain ⟨s', hr, hf, -, -, hax, hm, hkp⟩ :=
    reaches_doWhile aMachine addDec 20 87 addDec_87 Inv n hbody 0 s0 hn h0
  exact ⟨s', hr, hf, hax, hm, hkp⟩

/-! ## 5. Prologue and epilogue -/

/-- The callee-saved words the prologue stores. -/
def savedOf (s0 : AState) : List (Int × BitVec 64) :=
  [(40, s0.regs "%rbx"), (32, s0.regs "%rbp"), (24, s0.regs "%r12"), (16, s0.regs "%r13"),
    (8, s0.regs "%r14"), (0, s0.regs "%r15")]

theorem savedOf_offs (s0 : AState) : ∀ e ∈ savedOf s0, e.1 ∈ addOffs := by
  intro e he
  simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [addOffs]

/-- The array part of the invariant at trip `0`. -/
structure ArrOK (RP AP BP : BitVec 64) (n : Nat) (A B R : Nat → BitVec 64) (m : AMem) :
    Prop where
  apw : ∀ j, j < n → read64 m (ix AP (BitVec.ofNat 64 j)) = A j
  bpw : ∀ j, j < n → read64 m (ix BP (BitVec.ofNat 64 j)) = B j
  rpw : ∀ i, i < n → read64 m (ix RP (BitVec.ofNat 64 i)) = R i

theorem ArrOK.slot {SP RP AP BP : BitVec 64} {n : Nat} {A B R : Nat → BitVec 64} {m : AMem}
    (hS : AddSep SP RP AP BP n) (o : Int) (ho : o ∈ addOffs) (v : BitVec 64)
    (h : ArrOK RP AP BP n A B R m) : ArrOK RP AP BP n A B R (write64 m (at' SP o) v) where
  apw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.as j hj o ho).symm]; exact h.apw j hj
  bpw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.bs j hj o ho).symm]; exact h.bpw j hj
  rpw i hi := by rw [read64_write64_of_disjoint _ _ _ _ (hS.rs i hi o ho).symm]; exact h.rpw i hi

/-- **The prologue.** From the entry state, the frame base is `%rsp - 64`, `%rdi` and `%rax`
    are `0`, `%rbp` holds `n`, the invariant at trip `0` holds with the entry words of `ap`,
    `bp`, `rp` and the callee-saved registers saved, and the zero flag says whether `n = 0`. -/
theorem pre_run (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      n) :
    (runBlockA s0 addPre).regs "%rsp" = at' (s0.regs "%rsp") (-64)
    ∧ (runBlockA s0 addPre).regs "%rdi" = BitVec.ofNat 64 0
    ∧ (runBlockA s0 addPre).regs "%rax" = BitVec.ofNat 64 0
    ∧ (runBlockA s0 addPre).regs "%rbp" = BitVec.ofNat 64 n
    ∧ AddMem (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n 0
        (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
        (wordsOf s0.mem (s0.regs "%rdi")) (savedOf s0) (runBlockA s0 addPre).mem
    ∧ (runBlockA s0 addPre).view.flagB (·.zf) = decide (BitVec.ofNat 64 n = 0)
    ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem (runBlockA s0 addPre).mem := by
  have arr0 : ArrOK (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
      (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
      (wordsOf s0.mem (s0.regs "%rdi")) s0.mem :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hA : ArrOK (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
      (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
      (wordsOf s0.mem (s0.regs "%rdi")) (runBlockA s0 addPre).mem ∧
      Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem (runBlockA s0 addPre).mem := by
    simp only [addPre, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_lea_self,
      eA_loadMem, eA_storeMem, eA_cmp, upd_apply, String.reduceEq, ↓reduceIte]
    generalize at' (s0.regs "%rsp") (-64) = SP at hS ⊢
    constructor
    · iterate 10 refine ArrOK.slot hS _ (by decide) _ ?_
      exact arr0
    · iterate 10 refine Keeps.slot hS _ (by decide) _ ?_
      exact Keeps.refl _
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, fun j _ hj => hA.1.apw j hj,
    fun j _ hj => hA.1.bpw j hj, fun i hi => hA.1.rpw i hi⟩, ?_, hA.2⟩
  all_goals
    have hsplit : addPre = addPre.dropLast ++ [.cmp "%rbp" (.imm 0)] := rfl
    rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil]
  all_goals try rw [cmp0_zf]
  all_goals
    simp only [List.dropLast, addPre, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm,
      eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply, String.reduceEq, ↓reduceIte]
  all_goals generalize at' (s0.regs "%rsp") (-64) = SP at hS ⊢
  all_goals first
    | (simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte, hrcx]; done)
    | (intro e he
       simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
       rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
         simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte])

/-- **The epilogue.** The callee-saved registers are reloaded from their frame words and the
    frame is released; `%rax` and the memory are unchanged. -/
theorem post_run (s0 s : AState) (SP : BitVec 64) (hrsp : s.regs "%rsp" = SP)
    (hsv : ∀ e ∈ savedOf s0, read64 s.mem (at' SP e.1) = e.2) :
    (runBlockA s addPost).regs "%rsp" = at' SP 64
    ∧ (∀ R ∈ calleeSavedL, (runBlockA s addPost).regs R = s0.regs R)
    ∧ (runBlockA s addPost).regs "%rax" = s.regs "%rax"
    ∧ (runBlockA s addPost).mem = s.mem := by
  simp only [addPost, runBlockA_cons, runBlockA_nil, eA_loadMem, eA_lea_self, upd_apply,
    String.reduceEq, ↓reduceIte]
  refine ⟨by rw [hrsp], ?_, trivial, trivial⟩
  intro R hR
  simp only [calleeSavedL, List.mem_cons, List.not_mem_nil, or_false] at hR
  have h := fun o v (h : (o, v) ∈ savedOf s0) => hsv (o, v) h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [String.reduceEq, ↓reduceIte] <;>
    rw [hrsp] <;> exact h _ _ (by simp [savedOf])

theorem at'_at' (E : BitVec 64) : at' (at' E (-64)) 64 = E := by
  simp only [at']
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]
  simp

/-! ## 6. The run of the linked program -/

/-- **The linked `mpn_add_n_loop_owned` halts with the add fold in `rp` and its carry in
    `%rax`.** From an entry state with `rp`, `ap`, `bp`, `n` in `%rdi`, `%rsi`, `%rdx`, `%rcx`
    and the words separated (`AddSep`, frame base `%rsp - 64`), the machine runs the decoded
    program to its `ret` with the `n` words of `rp` holding the first component of `addFold`
    of the entry words from carry `0`, `%rax` its carry, `%rsp` and the callee-saved registers
    as at the entry, and the memory outside the frame bytes and the `n` words of `rp` as at the
    entry. -/
theorem add_halts (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      n) :
    ∃ s', Halts aMachine addDec 0 s0 s'
      ∧ (∀ i, i < n → wordsOf s'.mem (s0.regs "%rdi") i
          = memGetDyn (addFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) n
              (arr n (wordsOf s0.mem (s0.regs "%rdi")), 0#64)).1 i)
      ∧ s'.regs "%rax" = (addFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) n
              (arr n (wordsOf s0.mem (s0.regs "%rdi")), 0#64)).2
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
      ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s'.mem := by
  have hb := hS.bound
  obtain ⟨p1, p2, p3, p4, pM, pz, pk⟩ := pre_run s0 n hrcx hS
  generalize hs1 : runBlockA s0 addPre = s1 at p1 p2 p3 p4 pM pz pk
  have hr1 : Reaches aMachine addDec 0 s0 19 s1 := hs1 ▸ reach_pre s0
  have pM' := pM.congr (R' := memGetDyn (arr n (wordsOf s0.mem (s0.regs "%rdi"))))
    (fun i hi => (memGetDyn_arr _ _ i hi).symm)
  obtain ⟨s2, hr2, e2, e2ax, M2, K2⟩ : ∃ s2, Reaches aMachine addDec 0 s0 88 s2
      ∧ s2.regs "%rsp" = at' (s0.regs "%rsp") (-64)
      ∧ s2.regs "%rax" = (addFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) n
              (arr n (wordsOf s0.mem (s0.regs "%rdi")), 0#64)).2
      ∧ AddMem (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
          n n (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
          (memGetDyn (addFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) n
              (arr n (wordsOf s0.mem (s0.regs "%rdi")), 0#64)).1) (savedOf s0) s2.mem
      ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s2.mem := by
    by_cases hn : n = 0
    · subst hn
      refine ⟨s1, hr1.trans (.single ?_), p1, by simpa [addFold] using p3, ?_, pk⟩
      · rw [step_je aMachine addDec 19 88 s1 addDec_19]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        rw [pz]; simp
      · exact ⟨pM'.rp, pM'.ap, pM'.bp, pM'.saved, fun j _ hj => absurd hj (Nat.not_lt_zero _),
          fun j _ hj => absurd hj (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · have hstep : RInstrSemantics.step aMachine addDec 19 s1 = some (.go 20 s1) := by
        rw [step_je aMachine addDec 19 88 s1 addDec_19]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        have hne : ¬ BitVec.ofNat 64 n = 0#64 := fun h =>
          hn ((ofNat_eq_zero_iff n (by omega)).mp h)
        rw [pz]; simp [hne]
      obtain ⟨s2, hr2, hf, e2ax, M2, K2⟩ := add_loop hS (savedOf_offs s0)
        (Nat.pos_of_ne_zero hn) _ s1 p1 p2 p4 p3 pM'
      have e2 : s2.regs "%rsp" = at' (s0.regs "%rsp") (-64) := (hf _ (by decide)).trans p1
      exact ⟨s2, hr1.trans (.next hstep hr2), e2, e2ax, M2, pk.trans K2⟩
  obtain ⟨q1, q2, q3, q4⟩ := post_run s0 s2 _ e2 M2.saved
  refine ⟨runBlockA s2 addPost, halts_of_reaches (hr2.trans (reach_post s2)) addDec_95, ?_,
    by rw [q3, e2ax], by rw [q1, at'_at'], q2, by rw [q4]; exact K2⟩
  intro i hi
  rw [wordsOf, q4]
  exact M2.rpw i hi

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue
