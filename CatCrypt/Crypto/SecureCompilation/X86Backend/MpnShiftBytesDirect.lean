/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinBytesDirect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShiftReg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubBytesCorrect

@[expose] public section

set_option autoImplicit false

/-!
# The linked `mpn_shift_rt` for every count

`MpnChainFrame.mpn_shift_rt_frame_correct` states the result of the linked `mpn_shift_rt` for
counts up to the model's array size (`8`). This module runs the decoded program
(`MpnRtExportTerm`'s `nodeLayout shiftDecPre shiftDecLoop shiftDecPost`) on the address machine
directly, for every count: one trip reads `rp[i]` (the spill of the previous trip) and
`up[i]`, writes `up[i] << sh + rp[i]` to `rp[i]` and `up[i] >> (64 - sh)` to `rp[i+1]`
(`MpnShiftFrontEmit.shiftFoldStep`); `shiftFold_val` reads the value off the `n + 1` words.
`rp` may lie below `up` (word `i` of `rp` is only required to be disjoint from the words
`j ≥ i` of `up`), so the overlapping operation of GMP's `mpn_lshift` with `rp ≤ up` is covered;
`rp = up` is not, since trip `i` writes `rp[i+1]` before trip `i + 1` reads `up[i+1]`.

## Main results

* `shift_halts`: the machine run, with the `n + 1` words of `rp` the shift fold.
* `mpn_shift_rt_direct_correct`: for the program `MpnRuntimeBytesEmit.kernels` maps to the
  symbol, `value(rp'[0..n]) = value(up[0..n)) · 2^sh + rp[0]`, `%rsp` and the callee-saved
  registers restored, no byte written outside the frame and the `n + 1` words of `rp`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesDirect

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
  (upd upd_apply flA ix at' eA_mov_reg eA_mov_imm eA_xor eA_and eA_add eA_add_imm eA_sub_imm
   eA_sub eA_cmp eA_loadMem eA_loadMemIdx eA_storeMem eA_storeMemIdx cmp0_zf rd_at_ne rd_at_same)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
  (arr memGetDyn_arr cnt_dec ofNat_eq_zero_iff eA_lea_self rd_at wordsOf calleeSavedL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue
  (InFrB addOffs savedOf savedOf_offs at'_at')
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinBytesDirect
  (node_reach_body node_reach_pre node_reach_post node_je node_jne node_ret)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn memGetDyn_memSetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
  (shiftLimb shiftFoldStep shiftFold shiftFold_succ shiftFold_val)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach (reaches_doWhile step_je)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShiftReg (x86_SHLX_reg x86_SHRX_reg)

/-! ## 1. The segments of a trip -/

theorem eA_shlx (sa : AState) (d s c : String) :
    evalInstrA sa (.shlx d s c)
      = ⟨upd sa.regs d (x86_SHLX (sa.regs s) (sa.regs c)), sa.flags, sa.mem⟩ := rfl

theorem eA_shrx (sa : AState) (d s c : String) :
    evalInstrA sa (.shrx d s c)
      = ⟨upd sa.regs d (x86_SHRX (sa.regs s) (sa.regs c)), sa.flags, sa.mem⟩ := rfl

/-- The loads: `%rdx = rp[i]`, `%rbp = up[i]` for the index `i` in `%rax`. -/
def hA : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 56, .loadMemIdx "%rdx" "%r14" "%rax" 8
  , .loadMem "%r14" "%rsp" 48, .loadMemIdx "%rbp" "%r14" "%rax" 8 ]

/-- The funnel: `%rdx = up[i] << sh + rp[i]`, `%rbp = up[i] >> (64 - sh)` for `sh` in `%rsi`. -/
def hB : List (JInstr 64) :=
  [ .mov "%r8" (.imm 64), .mov "%r9" (.reg "%r8"), .sub "%r9" (.reg "%rsi")
  , .mov "%r8" (.reg "%r9"), .mov "%r9" (.reg "%rbp"), .shlx "%r9" "%r9" "%rsi"
  , .mov "%r10" (.reg "%r9"), .mov "%r9" (.reg "%rbp"), .shrx "%r9" "%r9" "%r8"
  , .mov "%rbp" (.reg "%r9"), .mov "%r8" (.reg "%r10"), .add "%r8" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r8") ]

/-- The two stores `rp[i] = %rdx`, `rp[i+1] = %rbp`, the index and counter steps, the invariant
    touches and the back-edge compare. -/
def hC : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rax" 8 (.reg "%rdx")
  , .mov "%rdx" (.imm 1), .mov "%r8" (.reg "%rax"), .add "%r8" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r8"), .loadMem "%r14" "%rsp" 56
  , .storeMemIdx "%r14" "%rdx" 8 (.reg "%rbp"), .mov "%rbx" (.reg "%rbx")
  , .add "%rax" (.imm 1), .sub "%rdi" (.imm 1), .cmp "%rdi" (.reg "%rcx")
  , .cmp "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0) ]

theorem shiftBody_eq : shiftDecLoop.body ++ [shiftDecLoop.cmpInstr] = hA ++ hB ++ hC := rfl

theorem hA_run (sa : AState) (RP UP : BitVec 64)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 56) = RP)
    (hup : read64 sa.mem (at' (sa.regs "%rsp") 48) = UP) :
    (runBlockA sa hA).regs "%rdx" = read64 sa.mem (ix RP (sa.regs "%rax"))
    ∧ (runBlockA sa hA).regs "%rbp" = read64 sa.mem (ix UP (sa.regs "%rax"))
    ∧ (∀ r, r ≠ "%r14" → r ≠ "%rdx" → r ≠ "%rbp" → (runBlockA sa hA).regs r = sa.regs r)
    ∧ (runBlockA sa hA).mem = sa.mem := by
  simp only [hA, runBlockA_cons, runBlockA_nil, eA_loadMem, eA_loadMemIdx, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hrp]
  · simp [hup]
  · intro r h1 h2 h3
    simp [h1, h2, h3]
  · trivial

theorem hB_run (sa : AState) (hsh : 0 < (sa.regs "%rsi").toNat ∧ (sa.regs "%rsi").toNat < 64) :
    (runBlockA sa hB).regs "%rdx"
        = (shiftLimb (sa.regs "%rsi").toNat (sa.regs "%rbp") (sa.regs "%rdx")).1
    ∧ (runBlockA sa hB).regs "%rbp"
        = (shiftLimb (sa.regs "%rsi").toNat (sa.regs "%rbp") (sa.regs "%rdx")).2
    ∧ (∀ r, r ≠ "%r8" → r ≠ "%r9" → r ≠ "%r10" → r ≠ "%rbp" → r ≠ "%rdx" →
        (runBlockA sa hB).regs r = sa.regs r)
    ∧ (runBlockA sa hB).mem = sa.mem := by
  have hc : (BitVec.ofNat 64 64 - sa.regs "%rsi").toNat = 64 - (sa.regs "%rsi").toNat := by
    rw [BitVec.toNat_sub]; simp; omega
  simp only [hB, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_sub, eA_add, eA_shlx,
    eA_shrx, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte, shiftLimb]
    rw [x86_SHLX_reg (by omega)]
  · simp only [String.reduceEq, ↓reduceIte, shiftLimb]
    rw [x86_SHRX_reg (by omega), hc]
  · intro r h1 h2 h3 h4 h5
    simp [h1, h2, h3, h4, h5]
  · trivial

theorem hC_run (sa : AState) (RP : BitVec 64)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 56) = RP)
    (hd : Disjoint8 (ix RP (sa.regs "%rax")) (at' (sa.regs "%rsp") 56)) :
    (runBlockA sa hC).mem = write64 (write64 sa.mem (ix RP (sa.regs "%rax")) (sa.regs "%rdx"))
        (ix RP (sa.regs "%rax" + 1)) (sa.regs "%rbp")
    ∧ (runBlockA sa hC).regs "%rax" = sa.regs "%rax" + 1
    ∧ (runBlockA sa hC).regs "%rdi" = sa.regs "%rdi" - 1
    ∧ (∀ r, r ≠ "%r14" → r ≠ "%rdx" → r ≠ "%r8" → r ≠ "%rax" → r ≠ "%rdi" →
        (runBlockA sa hC).regs r = sa.regs r)
    ∧ (runBlockA sa hC).view.flagB (·.zf) = decide (sa.regs "%rdi" - 1 = 0) := by
  have hsplit : hC = hC.dropLast ++ [.cmp "%rdi" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, hC, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_add,
    eA_add_imm, eA_sub_imm, eA_loadMem, eA_storeMemIdx, eA_cmp, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hrp, String.reduceEq, ↓reduceIte]
    rw [read64_write64_of_disjoint _ _ _ _ hd, hrp]; rfl
  · simp
  · simp
  · intro r h1 h2 h3 h4 h5
    by_cases hb : r = "%rbx"
    · subst hb; simp
    · simp [h1, h2, h3, h4, h5, hb]
  · simp

/-! ## 2. Separation and the memory invariant -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue (Keeps Keeps.refl Keeps.trans Keeps.out)

/-- **Word-level separation.** The `n + 1` words of `rp` are pairwise disjoint and disjoint
    from the frame words; word `i` of `rp` is disjoint from the words `j ≥ i` of `up`; the
    words of `up` are disjoint from the frame words. -/
structure ShSep (SP RP UP : BitVec 64) (n : Nat) : Prop where
  rr : ∀ i j, i ≤ n → j ≤ n → i ≠ j →
    Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix RP (BitVec.ofNat 64 j))
  rs : ∀ i, i ≤ n → ∀ o ∈ addOffs, Disjoint8 (ix RP (BitVec.ofNat 64 i)) (at' SP o)
  ru : ∀ i j, i ≤ j → j < n → Disjoint8 (ix RP (BitVec.ofNat 64 i)) (ix UP (BitVec.ofNat 64 j))
  us : ∀ j, j < n → ∀ o ∈ addOffs, Disjoint8 (ix UP (BitVec.ofNat 64 j)) (at' SP o)
  bound : n + 1 < 2 ^ 64
  fr : ∀ o ∈ addOffs, ∀ x, InRange8 (at' SP o) x → InFrB SP x

/-- **The memory invariant at trip `k`.** -/
structure ShMem (SP RP UP : BitVec 64) (n k : Nat) (U R : Nat → BitVec 64)
    (saved : List (Int × BitVec 64)) (m : AMem) : Prop where
  rp : read64 m (at' SP 56) = RP
  up : read64 m (at' SP 48) = UP
  saved : ∀ e ∈ saved, read64 m (at' SP e.1) = e.2
  upw : ∀ j, k ≤ j → j < n → read64 m (ix UP (BitVec.ofNat 64 j)) = U j
  rpw : ∀ i, i ≤ n → read64 m (ix RP (BitVec.ofNat 64 i)) = R i

/-- A store to word `p ≤ n` of `rp`, `p` at or below every source word kept from trip `k'` on. -/
theorem ShMem.out {SP RP UP : BitVec 64} {n k : Nat} {U R : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : ShSep SP RP UP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) {m : AMem} (h : ShMem SP RP UP n k U R saved m)
    (k' p : Nat) (hk' : k ≤ k') (hp : p ≤ n) (hpk : p ≤ k') (v : BitVec 64) :
    ShMem SP RP UP n k' U (fun i => if i = p then v else R i) saved
      (write64 m (ix RP (BitVec.ofNat 64 p)) v) := by
  have far : ∀ a ∈ addOffs, read64 (write64 m (ix RP (BitVec.ofNat 64 p)) v) (at' SP a)
      = read64 m (at' SP a) :=
    fun a ha => read64_write64_of_disjoint _ _ _ _ (hS.rs p hp a ha)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [far 56 (by decide)]; exact h.rp
  · rw [far 48 (by decide)]; exact h.up
  · intro e he; rw [far e.1 (hsv e he)]; exact h.saved e he
  · intro j hj hjn
    rw [read64_write64_of_disjoint _ _ _ _ (hS.ru p j (by omega) hjn)]
    exact h.upw j (by omega) hjn
  · intro i hi
    by_cases hip : i = p
    · subst hip; simp [read64_write64_same]
    · rw [read64_write64_of_disjoint _ _ _ _ (hS.rr p i hp hi (Ne.symm hip))]
      simp [hip, h.rpw i hi]

theorem ShMem.congr {SP RP UP : BitVec 64} {n k : Nat} {U R R' : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} {m : AMem} (h : ShMem SP RP UP n k U R saved m)
    (hR : ∀ i, i ≤ n → R i = R' i) : ShMem SP RP UP n k U R' saved m :=
  ⟨h.rp, h.up, h.saved, h.upw, fun i hi => (h.rpw i hi).trans (hR i hi)⟩

theorem Keeps.slot' {SP RP UP : BitVec 64} {n : Nat} (hS : ShSep SP RP UP n)
    {m m' : AMem} (o : Int) (ho : o ∈ addOffs) (v : BitVec 64) (h : Keeps SP RP (n + 1) m m') :
    Keeps SP RP (n + 1) m (write64 m' (at' SP o) v) := fun x a b => by
  rw [write64_of_not_inRange _ _ _ _ (fun hr => a (hS.fr o ho x hr))]; exact h x a b

/-! ## 3. One trip -/

/-- The registers a trip may write. -/
def shTripRegs : List String := ["%r14", "%rdx", "%rbp", "%r8", "%r9", "%r10", "%rax", "%rdi"]

/-- **One trip is `shiftFoldStep`.** -/
theorem shift_trip {SP RP UP : BitVec 64} {n : Nat} {U : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : ShSep SP RP UP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) (k : Nat) (hk : k < n)
    (acc : Fin (n + 1) → BitVec 64) (sa : AState)
    (hsh : 0 < (sa.regs "%rsi").toNat ∧ (sa.regs "%rsi").toNat < 64)
    (hrsp : sa.regs "%rsp" = SP) (hrax : sa.regs "%rax" = BitVec.ofNat 64 k)
    (hM : ShMem SP RP UP n k U (memGetDyn acc) saved sa.mem) :
    ShMem SP RP UP n (k + 1) U
        (memGetDyn (shiftFoldStep (arr n U) (sa.regs "%rsi").toNat acc k)) saved
        (runBlockA sa (hA ++ hB ++ hC)).mem
    ∧ (runBlockA sa (hA ++ hB ++ hC)).regs "%rax" = BitVec.ofNat 64 (k + 1)
    ∧ (runBlockA sa (hA ++ hB ++ hC)).regs "%rdi" = sa.regs "%rdi" - 1
    ∧ (∀ r, r ∉ shTripRegs → (runBlockA sa (hA ++ hB ++ hC)).regs r = sa.regs r)
    ∧ (runBlockA sa (hA ++ hB ++ hC)).view.flagB (·.zf) = decide (sa.regs "%rdi" - 1 = 0)
    ∧ Keeps SP RP (n + 1) sa.mem (runBlockA sa (hA ++ hB ++ hC)).mem := by
  have hb := hS.bound
  simp only [runBlockA_append]
  obtain ⟨a1, a2, fA, mA⟩ := hA_run sa RP UP (by rw [hrsp]; exact hM.rp)
    (by rw [hrsp]; exact hM.up)
  generalize hs1 : runBlockA sa hA = s1 at a1 a2 fA mA
  rw [hrax, hM.rpw k (by omega)] at a1
  rw [hrax, hM.upw k le_rfl hk] at a2
  have e1si : s1.regs "%rsi" = sa.regs "%rsi" := fA _ (by decide) (by decide) (by decide)
  obtain ⟨b1, b2, fB, mB⟩ := hB_run s1 (by rw [e1si]; exact hsh)
  generalize hs2 : runBlockA s1 hB = s2 at b1 b2 fB mB
  rw [a1, a2, e1si] at b1 b2
  have fr2 : ∀ r, r ∉ shTripRegs → s2.regs r = sa.regs r := by
    intro r hr
    simp only [shTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, g, -, -⟩ := hr
    exact (fB r d e g c b).trans (fA r a b c)
  have e2rsp : s2.regs "%rsp" = SP := (fr2 _ (by decide)).trans hrsp
  have e2rax : s2.regs "%rax" = BitVec.ofNat 64 k :=
    (fB _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((fA _ (by decide) (by decide) (by decide)).trans hrax)
  have e2rdi : s2.regs "%rdi" = sa.regs "%rdi" :=
    (fB _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (fA _ (by decide) (by decide) (by decide))
  have m2 : s2.mem = sa.mem := by rw [mB, mA]
  obtain ⟨cm, cax, cdi, fC, cz⟩ := hC_run s2 RP (by rw [e2rsp, m2]; exact hM.rp)
    (by rw [e2rsp, e2rax]; exact hS.rs k (by omega) 56 (by decide))
  generalize hs3 : runBlockA s2 hC = s3 at cm cax cdi fC cz
  rw [e2rax, b1, b2, m2] at cm
  have hk1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by simp [BitVec.ofNat_add]
  rw [hk1] at cm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cm]
    refine ((hM.out hS hsv k k (by omega) (by omega) le_rfl _).out hS hsv (k + 1) (k + 1)
      (by omega) (by omega) le_rfl _).congr ?_
    intro i hi
    simp only [shiftFoldStep, memGetDyn_memSetDyn _ (show k + 1 < n + 1 by omega)
      (show i < n + 1 by omega), memGetDyn_memSetDyn _ (show k < n + 1 by omega)
      (show i < n + 1 by omega), memGetDyn_arr n U k hk]
  · rw [cax, e2rax, hk1]
  · rw [cdi, e2rdi]
  · intro r hr
    have hr' := hr
    simp only [shTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨a, b, -, d, -, -, g, h⟩ := hr'
    rw [fC r a b d g h]; exact fr2 r hr
  · rw [cz, e2rdi]
  · rw [cm]
    exact Keeps.out _ (by omega) _ (Keeps.out _ (by omega) _ (Keeps.refl _))

/-! ## 4. The loop, the prologue, the epilogue -/

theorem shiftDecPre_length : shiftDecPre.length = 18 := rfl

/-- **The loop is `shiftFold`.** -/
theorem shift_loop {SP RP UP : BitVec 64} {n : Nat} {U : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : ShSep SP RP UP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) (hn : 0 < n) (acc : Fin (n + 1) → BitVec 64)
    (s0 : AState) (hsh : 0 < (s0.regs "%rsi").toNat ∧ (s0.regs "%rsi").toNat < 64)
    (hrsp : s0.regs "%rsp" = SP) (hrax : s0.regs "%rax" = BitVec.ofNat 64 0)
    (hrdi : s0.regs "%rdi" = BitVec.ofNat 64 n)
    (hM : ShMem SP RP UP n 0 U (memGetDyn acc) saved s0.mem) :
    ∃ s', Reaches aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 20 s0
        (shiftDecPre.length + 2 + (shiftDecLoop.body.length + 1) + 1) s'
      ∧ (∀ r, r ∉ shTripRegs → s'.regs r = s0.regs r)
      ∧ ShMem SP RP UP n n U
          (memGetDyn (shiftFold (arr n U) (s0.regs "%rsi").toNat n acc)) saved s'.mem
      ∧ Keeps SP RP (n + 1) s0.mem s'.mem := by
  have hb := hS.bound
  let Inv : Nat → AState → Prop := fun k s =>
    (∀ r, r ∉ shTripRegs → s.regs r = s0.regs r) ∧ s.regs "%rax" = BitVec.ofNat 64 k
      ∧ s.regs "%rdi" = BitVec.ofNat 64 (n - k)
      ∧ ShMem SP RP UP n k U
          (memGetDyn (shiftFold (arr n U) (s0.regs "%rsi").toNat k acc)) saved s.mem
      ∧ Keeps SP RP (n + 1) s0.mem s.mem
  have hbody : ∀ k s, k < n → Inv k s → ∃ s', Reaches aMachine
      (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 20 s
      (shiftDecPre.length + 2 + (shiftDecLoop.body.length + 1)) s' ∧
      (aMachine.view s').flagB (·.zf) = decide (k + 1 = n) ∧ Inv (k + 1) s' := by
    intro k s hk ⟨hf, hax, hdi, hm, hkp⟩
    have hsi : s.regs "%rsi" = s0.regs "%rsi" := hf _ (by decide)
    obtain ⟨M', eax, edi, f', z', kp'⟩ := shift_trip hS hsv k hk _ s (by rw [hsi]; exact hsh)
      ((hf _ (by decide)).trans hrsp) hax hm
    have hdi' : s.regs "%rdi" = BitVec.ofNat 64 (n - k - 1 + 1) := by
      rw [hdi]; congr 1; omega
    refine ⟨runBlockA s (hA ++ hB ++ hC), ?_, ?_, ?_, eax, ?_, ?_, hkp.trans kp'⟩
    · have h := node_reach_body shiftDecPre shiftDecPost shiftDecLoop s
      rw [shiftBody_eq] at h
      exact h
    · show (runBlockA s (hA ++ hB ++ hC)).view.flagB (·.zf) = _
      rw [z', hdi', cnt_dec]
      exact decide_eq_decide.mpr ((ofNat_eq_zero_iff _ (by omega)).trans (by omega))
    · intro r hr; exact (f' r hr).trans (hf r hr)
    · rw [edi, hdi', cnt_dec]; congr 1
    · rw [shiftFold_succ]; rw [hsi] at M'; exact M'
  have h0 : Inv 0 s0 :=
    ⟨fun _ _ => rfl, hrax, by simpa using hrdi, by simpa [shiftFold] using hM, Keeps.refl _⟩
  obtain ⟨s', hr, hf, -, -, hm, hkp⟩ :=
    reaches_doWhile aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 20
      (shiftDecPre.length + 2 + (shiftDecLoop.body.length + 1))
      (node_jne shiftDecPre shiftDecPost shiftDecLoop) Inv n hbody 0 s0 hn h0
  exact ⟨s', hr, hf, hm, hkp⟩

/-- The array part of the invariant at trip `0`. -/
structure ShArr (RP UP : BitVec 64) (n : Nat) (U R : Nat → BitVec 64) (m : AMem) : Prop where
  upw : ∀ j, j < n → read64 m (ix UP (BitVec.ofNat 64 j)) = U j
  rpw : ∀ i, i ≤ n → read64 m (ix RP (BitVec.ofNat 64 i)) = R i

theorem ShArr.slot {SP RP UP : BitVec 64} {n : Nat} {U R : Nat → BitVec 64} {m : AMem}
    (hS : ShSep SP RP UP n) (o : Int) (ho : o ∈ addOffs) (v : BitVec 64)
    (h : ShArr RP UP n U R m) : ShArr RP UP n U R (write64 m (at' SP o) v) where
  upw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.us j hj o ho).symm]; exact h.upw j hj
  rpw i hi := by rw [read64_write64_of_disjoint _ _ _ _ (hS.rs i hi o ho).symm]; exact h.rpw i hi

/-- **The prologue** (with the loop guard). -/
theorem shift_pre_run (s0 : AState) (n : Nat) (hrdx : s0.regs "%rdx" = BitVec.ofNat 64 n)
    (hS : ShSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") n) :
    (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rsp"
        = at' (s0.regs "%rsp") (-64)
    ∧ (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rax" = BitVec.ofNat 64 0
    ∧ (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rdi" = BitVec.ofNat 64 n
    ∧ (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rsi" = s0.regs "%rcx"
    ∧ ShMem (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") n 0
        (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdi")) (savedOf s0)
        (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).mem
    ∧ (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).view.flagB (·.zf)
        = decide (BitVec.ofNat 64 n = 0)
    ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (n + 1) s0.mem
        (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).mem := by
  have arr0 : ShArr (s0.regs "%rdi") (s0.regs "%rsi") n (wordsOf s0.mem (s0.regs "%rsi"))
      (wordsOf s0.mem (s0.regs "%rdi")) s0.mem := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hA' : ShArr (s0.regs "%rdi") (s0.regs "%rsi") n (wordsOf s0.mem (s0.regs "%rsi"))
      (wordsOf s0.mem (s0.regs "%rdi")) (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).mem ∧
      Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (n + 1) s0.mem
        (runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)])).mem := by
    simp only [shiftDecPre, List.cons_append, List.nil_append, runBlockA_cons, runBlockA_nil,
      eA_mov_reg, eA_mov_imm, eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply,
      String.reduceEq, ↓reduceIte]
    generalize at' (s0.regs "%rsp") (-64) = SP at hS ⊢
    constructor
    · iterate 10 refine ShArr.slot hS _ (by decide) _ ?_
      exact arr0
    · iterate 10 refine Keeps.slot' hS _ (by decide) _ ?_
      exact Keeps.refl _
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, fun j _ hj => hA'.1.upw j hj,
    fun i hi => hA'.1.rpw i hi⟩, ?_, hA'.2⟩
  all_goals rw [runBlockA_append, runBlockA_cons, runBlockA_nil]
  all_goals try rw [cmp0_zf]
  all_goals
    simp only [shiftDecPre, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm,
      eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply, String.reduceEq, ↓reduceIte]
  all_goals generalize at' (s0.regs "%rsp") (-64) = SP at hS ⊢
  all_goals first
    | (simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte, hrdx]; done)
    | (intro e he
       simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
       rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
         simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte])

theorem shiftPost_eq : shiftDecPost = MpnBinExportTerm.andDecPost := rfl

/-! ## 5. The run of the linked `mpn_shift_rt` -/

/-- **The machine run.** From an entry state with `rp`, `up`, `n`, `sh` in `%rdi`, `%rsi`,
    `%rdx`, `%rcx`, `0 < sh < 64` and `ShSep` (frame base `%rsp - 64`), the machine halts with
    the `n + 1` words of `rp` the shift fold of the entry words, `%rsp` and the callee-saved
    registers restored, and the memory outside the frame bytes and the `n + 1` words of `rp` as
    at the entry. -/
theorem shift_halts (s0 : AState) (n : Nat) (hrdx : s0.regs "%rdx" = BitVec.ofNat 64 n)
    (hsh : 0 < (s0.regs "%rcx").toNat ∧ (s0.regs "%rcx").toNat < 64)
    (hS : ShSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") n) :
    ∃ s', Halts aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 s0 s'
      ∧ (∀ i, i ≤ n → wordsOf s'.mem (s0.regs "%rdi") i
          = memGetDyn (shiftFold (arr n (wordsOf s0.mem (s0.regs "%rsi"))) (s0.regs "%rcx").toNat
              n (arr (n + 1) (wordsOf s0.mem (s0.regs "%rdi")))) i)
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
      ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (n + 1) s0.mem s'.mem := by
  have hb := hS.bound
  have hcmp : shiftDecLoop.cmpInstr = .cmp "%rdi" (.imm 0) := rfl
  obtain ⟨p1, p3, p4, p5, pM, pz, pk⟩ := shift_pre_run s0 n hrdx hS
  have hr1 := node_reach_pre shiftDecPre shiftDecPost shiftDecLoop s0
  rw [hcmp] at hr1
  generalize hs1 : runBlockA s0 (shiftDecPre ++ [.cmp "%rdi" (.imm 0)]) = s1
    at p1 p3 p4 p5 pM pz pk hr1
  have pM' := pM.congr (R' := memGetDyn (arr (n + 1) (wordsOf s0.mem (s0.regs "%rdi"))))
    (fun i hi => (memGetDyn_arr _ _ i (by omega)).symm)
  let E := shiftDecPre.length + shiftDecLoop.body.length + 4
  have hje := node_je shiftDecPre shiftDecPost shiftDecLoop
  obtain ⟨s2, hr2, e2, M2, K2⟩ : ∃ s2, Reaches aMachine
        (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 s0 E s2
      ∧ s2.regs "%rsp" = at' (s0.regs "%rsp") (-64)
      ∧ ShMem (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") n n
          (wordsOf s0.mem (s0.regs "%rsi"))
          (memGetDyn (shiftFold (arr n (wordsOf s0.mem (s0.regs "%rsi"))) (s0.regs "%rcx").toNat
              n (arr (n + 1) (wordsOf s0.mem (s0.regs "%rdi"))))) (savedOf s0) s2.mem
      ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (n + 1) s0.mem s2.mem := by
    by_cases hn : n = 0
    · subst hn
      refine ⟨s1, hr1.trans (.single ?_), p1, ?_, pk⟩
      · rw [step_je aMachine _ _ _ s1 hje]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        rw [pz]; simp [E]
      · exact ⟨pM'.rp, pM'.up, pM'.saved, fun j _ hj => absurd hj (Nat.not_lt_zero _),
          fun i hi => by simpa [shiftFold] using pM'.rpw i hi⟩
    · have hstep : RInstrSemantics.step aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost)
          (shiftDecPre.length + 1) s1 = some (.go (shiftDecPre.length + 1 + 1) s1) := by
        rw [step_je aMachine _ _ _ s1 hje]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        have hne : ¬ BitVec.ofNat 64 n = 0#64 := fun h =>
          hn ((ofNat_eq_zero_iff n (by omega)).mp h)
        rw [pz]; simp [hne]
      obtain ⟨s2, hr2, hf, M2, K2⟩ := shift_loop hS (savedOf_offs s0) (Nat.pos_of_ne_zero hn)
        _ s1 (by rw [p5]; exact hsh) p1 p3 p4 pM'
      have e2 : s2.regs "%rsp" = at' (s0.regs "%rsp") (-64) := (hf _ (by decide)).trans p1
      rw [p5] at M2
      refine ⟨s2, hr1.trans (.next hstep ?_), e2, M2, pk.trans K2⟩
      have e : shiftDecPre.length + 2 + (shiftDecLoop.body.length + 1) + 1 = E := by
        simp only [E]; omega
      rw [← e]
      exact hr2
  obtain ⟨q1, q2, q3⟩ := MpnBinBytesDirect.bin_post_run s0 s2 _ e2 M2.saved
  rw [← shiftPost_eq] at q1 q2 q3
  refine ⟨runBlockA s2 shiftDecPost, halts_of_reaches (hr2.trans
    (node_reach_post shiftDecPre shiftDecPost shiftDecLoop s2))
    (node_ret shiftDecPre shiftDecPost shiftDecLoop), ?_,
    by rw [q1, at'_at'], q2, by rw [q3]; exact K2⟩
  intro i hi
  rw [wordsOf, q3]
  exact M2.rpw i hi

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lfundef)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)

/-- **The linked `mpn_shift_rt`, for every count.** The program
    `MpnRuntimeBytesEmit.kernels` maps to the symbol is one function whose function bytes
    decode to `nodeLayout shiftDecPre shiftDecLoop shiftDecPost`; from every entry state with
    `rp`, `up`, `n`, `sh` in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `0 < sh < 64`, `rp[0] < 2^sh` (the
    model's spill-in) and `ShSep` (any `n` with `n + 1 < 2^64`; `rp` below `up` allowed), the
    machine halts with `value(rp'[0..n]) = value(up[0..n)) · 2^sh + rp[0]`, `%rsp` and the
    callee-saved registers restored, and no byte written outside the 80 frame bytes and the
    `n + 1` words of `rp`. -/
theorem mpn_shift_rt_direct_correct :
    ∃ fd : Lfundef,
      (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt").map (·.lp_funcs)
        = some [("mpn_shift_rt", fd)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes fd.lfd_body)
          = some (nodeLayout shiftDecPre shiftDecLoop shiftDecPost)
      ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rdx" = BitVec.ofNat 64 n →
        0 < (s0.regs "%rcx").toNat ∧ (s0.regs "%rcx").toNat < 64 →
        (wordsOf s0.mem (s0.regs "%rdi") 0).toNat < 2 ^ (s0.regs "%rcx").toNat →
        ShSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") n →
        ∃ s', Halts aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 s0 s'
          ∧ bignumVal ((List.range (n + 1)).map (wordsOf s'.mem (s0.regs "%rdi")))
            = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
                * 2 ^ (s0.regs "%rcx").toNat + (wordsOf s0.mem (s0.regs "%rdi") 0).toNat
          ∧ s'.regs "%rsp" = s0.regs "%rsp"
          ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
          ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (n + 1) s0.mem s'.mem := by
  refine ⟨_, by rw [shiftLprog_eq]; rfl, by rw [shiftPhysAbi_eq]; exact shiftPhysLit_decode, ?_⟩
  intro s0 n hrdx hsh h0 hS
  obtain ⟨s', hh, hw, hsp, hcs, hk⟩ := shift_halts s0 n hrdx hsh hS
  refine ⟨s', hh, ?_, hsp, hcs, hk⟩
  have hv := shiftFold_val (arr n (wordsOf s0.mem (s0.regs "%rsi"))) (s0.regs "%rcx").toNat
    (by omega) (arr (n + 1) (wordsOf s0.mem (s0.regs "%rdi")))
    (by rw [memGetDyn_arr _ _ 0 (by omega)]; exact h0) n (by omega)
  rw [MpnAddSubBytesCorrect.cells_words _ _ (n + 1) _ (fun i hi => hw i (by omega)), hv,
    MpnMulBytesCorrect.cells_arr n n _ le_rfl, memGetDyn_arr _ _ 0 (by omega)]

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesDirect
