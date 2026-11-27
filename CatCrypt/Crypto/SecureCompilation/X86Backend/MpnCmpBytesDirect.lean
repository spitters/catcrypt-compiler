/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesDirect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCarryIdiomsHand

@[expose] public section

set_option autoImplicit false

/-!
# The linked `mpn_cmp_ct` for every count

`MpnChainFrame.mpn_cmp_ct_frame_correct` states the result of the linked `mpn_cmp_ct` for
counts up to the model's array size (`8`). This module runs the decoded program
(`MpnRtExportTerm`'s `nodeLayout cmpDecPre cmpDecLoop cmpDecPost`) on the address machine
directly, for every count `0 < n < 2^64`: trip `k` reads the limbs `ap[n-1-k]`, `bp[n-1-k]`
and the running sign in `rp[0]` and writes `MpnCmpFrontEmit.cmpSelW` of them back to `rp[0]`
(`cmpFoldStep` at `top = n - 1`); `cmpFold_val_full` reads the sign off `rp[0]`.

## Main results

* `cmp_halts`: the machine run, with `rp[0]` the compare fold.
* `mpn_cmp_ct_direct_correct`: for the program `MpnRuntimeBytesEmit.kernels` maps to the
  symbol, `rp'[0] = cmpSign (value ap[0..n)) (value bp[0..n))` when `rp[0] = 0` at the entry,
  `%rsp` and the callee-saved registers restored, no byte written outside the frame and
  `rp[0]`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesDirect

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
  (upd upd_apply flA ix at' eA_mov_reg eA_mov_imm eA_xor eA_and eA_add eA_add_imm eA_sub_imm
   eA_sub eA_shr63 eA_cmp eA_cmpMem eA_loadMem eA_loadMemIdx eA_storeMem eA_storeMemIdx cmp0_zf
   ltu_idiom rd_at_ne rd_at_same)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
  (arr memGetDyn_arr cnt_dec ofNat_eq_zero_iff eA_lea_self rd_at wordsOf calleeSavedL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnSubBytesValue
  (InFrB InOutB Keeps Keeps.refl Keeps.trans Keeps.out savedOf at'_at')
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinBytesDirect
  (node_reach_body node_reach_pre node_reach_post node_je node_jne node_ret)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn memGetDyn_memSetDyn)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
  (cmpSign cmpStepW cmpSelW cmpFoldStep cmpFold cmpFold_succ cmpFold_val_full)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach (reaches_doWhile step_je)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm

/-! ## 1. The segments of a trip -/

def cI : List (JInstr 64) :=
  [ .mov "%rbp" (.imm 1)
  , .mov "%r8" (.reg "%rsi")
  , .sub "%r8" (.reg "%rbp")
  , .mov "%rbp" (.reg "%r8")
  , .mov "%r8" (.reg "%rbp")
  , .sub "%r8" (.reg "%rax")
  , .mov "%rbp" (.reg "%r8")
  , .mov "%r8" (.imm 0)
  , .mov "%r9" (.reg "%r8") ]

def cL : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 64
  , .loadMemIdx "%r8" "%r14" "%rbp" 8
  , .loadMem "%r14" "%rsp" (-8)
  , .loadMemIdx "%r10" "%r14" "%rbp" 8
  , .loadMem "%r14" "%rsp" 72
  , .loadMemIdx "%rbp" "%r14" "%r9" 8 ]

def cLt : List (JInstr 64) :=
  [ .mov "%r11" (.imm 18446744073709551615)
  , .mov "%r12" (.reg "%r8")
  , .xor_ "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r12")
  , .and_ "%r11" (.reg "%r10")
  , .mov "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r8")
  , .xor_ "%r11" (.reg "%r10")
  , .mov "%r13" (.imm 18446744073709551615)
  , .mov "%rdx" (.reg "%r11")
  , .xor_ "%rdx" (.reg "%r13")
  , .mov "%r11" (.reg "%r8")
  , .sub "%r11" (.reg "%r10")
  , .mov "%r13" (.reg "%rdx")
  , .and_ "%r13" (.reg "%r11")
  , .mov "%rdx" (.reg "%r13")
  , .mov "%r11" (.reg "%r12")
  , .xor_ "%r11" (.reg "%rdx")
  , .mov "%r13" (.reg "%r12")
  , .and_ "%r13" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r11")
  , .xor_ "%rdx" (.reg "%r13")
  , .mov "%r11" (.imm 63)
  , .mov "%r11" (.reg "%rdx")
  , .shr "%r11" (.imm 63)
  , .mov "%rdx" (.reg "%r11") ]

def cGt : List (JInstr 64) :=
  [ .mov "%r11" (.imm 18446744073709551615)
  , .mov "%r12" (.reg "%r10")
  , .xor_ "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r12")
  , .and_ "%r11" (.reg "%r8")
  , .mov "%r12" (.reg "%r11")
  , .mov "%r11" (.reg "%r10")
  , .xor_ "%r11" (.reg "%r8")
  , .mov "%r13" (.imm 18446744073709551615)
  , .mov "%rcx" (.reg "%r11")
  , .xor_ "%rcx" (.reg "%r13")
  , .mov "%r11" (.reg "%r10")
  , .sub "%r11" (.reg "%r8")
  , .mov "%r8" (.reg "%rcx")
  , .and_ "%r8" (.reg "%r11")
  , .mov "%rcx" (.reg "%r8")
  , .mov "%r8" (.reg "%r12")
  , .xor_ "%r8" (.reg "%rcx")
  , .mov "%r10" (.reg "%r12")
  , .and_ "%r10" (.reg "%rcx")
  , .mov "%rcx" (.reg "%r8")
  , .xor_ "%rcx" (.reg "%r10")
  , .mov "%r8" (.imm 63)
  , .mov "%r8" (.reg "%rcx")
  , .shr "%r8" (.imm 63)
  , .mov "%rcx" (.reg "%r8") ]

def cD : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%rcx")
  , .sub "%r8" (.reg "%rdx")
  , .mov "%rcx" (.reg "%r8") ]

def cS : List (JInstr 64) :=
  [ .mov "%rdx" (.imm 0)
  , .mov "%r8" (.imm 18446744073709551615)
  , .mov "%r10" (.reg "%rdx")
  , .xor_ "%r10" (.reg "%r8")
  , .mov "%rdx" (.reg "%r10")
  , .and_ "%rdx" (.reg "%rbp")
  , .mov "%r8" (.reg "%rdx")
  , .mov "%rdx" (.imm 0)
  , .mov "%r10" (.reg "%rdx")
  , .xor_ "%r10" (.reg "%rbp")
  , .mov "%rdx" (.imm 18446744073709551615)
  , .mov "%r11" (.reg "%r10")
  , .xor_ "%r11" (.reg "%rdx")
  , .mov "%rdx" (.imm 0)
  , .mov "%r10" (.reg "%rdx")
  , .sub "%r10" (.reg "%rbp")
  , .mov "%rdx" (.reg "%r11")
  , .and_ "%rdx" (.reg "%r10")
  , .mov "%r10" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r8")
  , .xor_ "%rdx" (.reg "%r10")
  , .mov "%r11" (.reg "%r8")
  , .and_ "%r11" (.reg "%r10")
  , .mov "%r8" (.reg "%rdx")
  , .xor_ "%r8" (.reg "%r11")
  , .mov "%rdx" (.imm 63)
  , .mov "%rdx" (.reg "%r8")
  , .shr "%rdx" (.imm 63)
  , .mov "%r8" (.reg "%rdx")
  , .mov "%rdx" (.imm 1)
  , .mov "%r10" (.reg "%r8")
  , .sub "%r10" (.reg "%rdx")
  , .mov "%rdx" (.reg "%r10")
  , .mov "%r8" (.reg "%rcx")
  , .xor_ "%r8" (.reg "%rbp")
  , .mov "%rcx" (.reg "%r8")
  , .mov "%r8" (.reg "%rdx")
  , .and_ "%r8" (.reg "%rcx")
  , .mov "%rcx" (.reg "%rbp")
  , .xor_ "%rcx" (.reg "%r8")
  , .mov "%rdx" (.reg "%rcx") ]

def cT : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 72
  , .storeMemIdx "%r14" "%r9" 8 (.reg "%rdx")
  , .mov "%rbx" (.reg "%rbx")
  , .add "%rax" (.imm 1)
  , .sub "%rdi" (.imm 1)
  , .cmpMem "%rdi" "%rsp" 0
  , .cmpMem "%rdi" "%rsp" 8
  , .cmp "%rdi" (.reg "%rsi") 
  , .cmp "%rdi" (.imm 0) ]

theorem cmpBody_eq : cmpDecLoop.body ++ [cmpDecLoop.cmpInstr]
    = cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT := rfl

/-- The descending index `%rbp = (n - 1) - k` and the output index `%r9 = 0`. -/
theorem cI_run (sa : AState) :
    (runBlockA sa cI).regs "%rbp" = sa.regs "%rsi" - 1 - sa.regs "%rax"
    ∧ (runBlockA sa cI).regs "%r9" = 0#64
    ∧ (∀ r, r ≠ "%rbp" → r ≠ "%r8" → r ≠ "%r9" → (runBlockA sa cI).regs r = sa.regs r)
    ∧ (runBlockA sa cI).mem = sa.mem := by
  simp only [cI, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_sub, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro r h1 h2 h3
    simp [h1, h2, h3]
  · trivial

/-- The loads: `%r8 = ap[%rbp]`, `%r10 = bp[%rbp]`, `%rbp = rp[%r9]`. -/
theorem cL_run (sa : AState) (RP AP BP : BitVec 64)
    (hap : read64 sa.mem (at' (sa.regs "%rsp") 64) = AP)
    (hbp : read64 sa.mem (at' (sa.regs "%rsp") (-8)) = BP)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 72) = RP) :
    (runBlockA sa cL).regs "%r8" = read64 sa.mem (ix AP (sa.regs "%rbp"))
    ∧ (runBlockA sa cL).regs "%r10" = read64 sa.mem (ix BP (sa.regs "%rbp"))
    ∧ (runBlockA sa cL).regs "%rbp" = read64 sa.mem (ix RP (sa.regs "%r9"))
    ∧ (∀ r, r ≠ "%r14" → r ≠ "%r8" → r ≠ "%r10" → r ≠ "%rbp" → (runBlockA sa cL).regs r = sa.regs r)
    ∧ (runBlockA sa cL).mem = sa.mem := by
  simp only [cL, runBlockA_cons, runBlockA_nil, eA_loadMem, eA_loadMemIdx, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hap]
  · simp [hbp]
  · simp [hrp]
  · intro r h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  · trivial

/-- `%rdx = bSltu x y` for `x`, `y` in `%r8`, `%r10`. -/
theorem cLt_run (sa : AState) :
    (runBlockA sa cLt).regs "%rdx" = bSltu (sa.regs "%r8") (sa.regs "%r10")
    ∧ (∀ r, r ≠ "%r11" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rdx" →
        (runBlockA sa cLt).regs r = sa.regs r)
    ∧ (runBlockA sa cLt).mem = sa.mem := by
  simp only [cLt, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_xor, eA_and,
    eA_sub, eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]
    rw [ltu_idiom]
  · intro r h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  · trivial

/-- `%rcx = bSltu y x` for `x`, `y` in `%r8`, `%r10`. -/
theorem cGt_run (sa : AState) :
    (runBlockA sa cGt).regs "%rcx" = bSltu (sa.regs "%r10") (sa.regs "%r8")
    ∧ (∀ r, r ≠ "%r8" → r ≠ "%r10" → r ≠ "%r11" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rcx" →
        (runBlockA sa cGt).regs r = sa.regs r)
    ∧ (runBlockA sa cGt).mem = sa.mem := by
  simp only [cGt, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_xor, eA_and,
    eA_sub, eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]
    rw [ltu_idiom]
  · intro r h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
  · trivial

theorem cD_run (sa : AState) :
    (runBlockA sa cD).regs "%rcx" = sa.regs "%rcx" - sa.regs "%rdx"
    ∧ (∀ r, r ≠ "%r8" → r ≠ "%rcx" → (runBlockA sa cD).regs r = sa.regs r)
    ∧ (runBlockA sa cD).mem = sa.mem := by
  simp only [cD, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_sub, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro r h1 h2
    simp [h1, h2]
  · trivial

/-- The selection: `%rdx = prev ^ ((bSltu 0 prev - 1) & (d ^ prev))` for `prev`, `d` in
    `%rbp`, `%rcx`. -/
theorem cS_run (sa : AState) :
    (runBlockA sa cS).regs "%rdx" = sa.regs "%rbp" ^^^ ((bSltu 0 (sa.regs "%rbp") - 1)
        &&& (sa.regs "%rcx" ^^^ sa.regs "%rbp"))
    ∧ (∀ r, r ≠ "%rdx" → r ≠ "%r8" → r ≠ "%r10" → r ≠ "%r11" → r ≠ "%rcx" →
        (runBlockA sa cS).regs r = sa.regs r)
    ∧ (runBlockA sa cS).mem = sa.mem := by
  simp only [cS, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_xor, eA_and,
    eA_sub, eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]
    rw [ltu_idiom]
    rfl
  · intro r h1 h2 h3 h4 h5
    simp [h1, h2, h3, h4, h5]
  · trivial

theorem cT_run (sa : AState) (RP : BitVec 64)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 72) = RP) :
    (runBlockA sa cT).mem = write64 sa.mem (ix RP (sa.regs "%r9")) (sa.regs "%rdx")
    ∧ (runBlockA sa cT).regs "%rax" = sa.regs "%rax" + 1
    ∧ (runBlockA sa cT).regs "%rdi" = sa.regs "%rdi" - 1
    ∧ (∀ r, r ≠ "%r14" → r ≠ "%rax" → r ≠ "%rdi" → (runBlockA sa cT).regs r = sa.regs r)
    ∧ (runBlockA sa cT).view.flagB (·.zf) = decide (sa.regs "%rdi" - 1 = 0) := by
  have hsplit : cT = cT.dropLast ++ [.cmp "%rdi" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, cT, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_add_imm,
    eA_sub_imm, eA_loadMem, eA_storeMemIdx, eA_cmp, eA_cmpMem, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hrp]
  · simp
  · simp
  · intro r h1 h2 h3
    by_cases hb : r = "%rbx"
    · subst hb; simp
    · simp [h1, h2, h3, hb]
  · simp

/-! ## 2. Separation and the memory invariant -/

/-- The frame words of the function, by offset from the frame base `%rsp - 80`. -/
def cmpOffs : List Int := [-16, -8, 0, 8, 16, 24, 32, 40, 48, 56, 64, 72]

/-- **Word-level separation.** `rp[0]` is disjoint from the frame words and from the `n` words
    of `ap` and `bp`, which are disjoint from the frame words. -/
structure CmpSep (SP RP AP BP : BitVec 64) (n : Nat) : Prop where
  rs : ∀ o ∈ cmpOffs, Disjoint8 (ix RP (BitVec.ofNat 64 0)) (at' SP o)
  ra : ∀ j, j < n → Disjoint8 (ix RP (BitVec.ofNat 64 0)) (ix AP (BitVec.ofNat 64 j))
  rb : ∀ j, j < n → Disjoint8 (ix RP (BitVec.ofNat 64 0)) (ix BP (BitVec.ofNat 64 j))
  as : ∀ j, j < n → ∀ o ∈ cmpOffs, Disjoint8 (ix AP (BitVec.ofNat 64 j)) (at' SP o)
  bs : ∀ j, j < n → ∀ o ∈ cmpOffs, Disjoint8 (ix BP (BitVec.ofNat 64 j)) (at' SP o)
  bound : n < 2 ^ 64
  fr : ∀ o ∈ cmpOffs, ∀ x, InRange8 (at' SP o) x → InFrB SP x

/-- **The memory invariant.** The pointer words of the frame, the words `saved`, the words of
    `ap` and `bp`, and the running sign `r` in `rp[0]`. -/
structure CmpMem (SP RP AP BP : BitVec 64) (n : Nat) (A B : Nat → BitVec 64) (r : BitVec 64)
    (saved : List (Int × BitVec 64)) (m : AMem) : Prop where
  rp : read64 m (at' SP 72) = RP
  ap : read64 m (at' SP 64) = AP
  bp : read64 m (at' SP (-8)) = BP
  saved : ∀ e ∈ saved, read64 m (at' SP e.1) = e.2
  apw : ∀ j, j < n → read64 m (ix AP (BitVec.ofNat 64 j)) = A j
  bpw : ∀ j, j < n → read64 m (ix BP (BitVec.ofNat 64 j)) = B j
  r0 : read64 m (ix RP (BitVec.ofNat 64 0)) = r

theorem CmpMem.out {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64} {r : BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : CmpSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ cmpOffs) {m : AMem} (h : CmpMem SP RP AP BP n A B r saved m)
    (v : BitVec 64) :
    CmpMem SP RP AP BP n A B v saved (write64 m (ix RP (BitVec.ofNat 64 0)) v) := by
  have far : ∀ a ∈ cmpOffs, read64 (write64 m (ix RP (BitVec.ofNat 64 0)) v) (at' SP a)
      = read64 m (at' SP a) :=
    fun a ha => read64_write64_of_disjoint _ _ _ _ (hS.rs a ha)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [far 72 (by decide)]; exact h.rp
  · rw [far 64 (by decide)]; exact h.ap
  · rw [far (-8) (by decide)]; exact h.bp
  · intro e he; rw [far e.1 (hsv e he)]; exact h.saved e he
  · intro j hj
    rw [read64_write64_of_disjoint _ _ _ _ (hS.ra j hj)]; exact h.apw j hj
  · intro j hj
    rw [read64_write64_of_disjoint _ _ _ _ (hS.rb j hj)]; exact h.bpw j hj
  · exact read64_write64_same _ _ _

theorem Keeps.slot' {SP RP AP BP : BitVec 64} {n : Nat} (hS : CmpSep SP RP AP BP n)
    {m m' : AMem} (o : Int) (ho : o ∈ cmpOffs) (v : BitVec 64) (h : Keeps SP RP 1 m m') :
    Keeps SP RP 1 m (write64 m' (at' SP o) v) := fun x a b => by
  rw [write64_of_not_inRange _ _ _ _ (fun hr => a (hS.fr o ho x hr))]; exact h x a b

/-! ## 3. One trip -/

/-- The registers a trip may write. -/
def cmpTripRegs : List String :=
  ["%rbp", "%r8", "%r9", "%r14", "%r10", "%r11", "%r12", "%r13", "%rdx", "%rcx", "%rax", "%rdi"]

theorem idx_eq (n k : Nat) (hk : k < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - 1 - k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n - 1 - k < 2 ^ 64 by omega)]
  omega

/-- **One trip is `cmpFoldStep`.** -/
theorem cmp_trip {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : CmpSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ cmpOffs) (k : Nat) (hk : k < n) (r : BitVec 64) (sa : AState)
    (hrsp : sa.regs "%rsp" = SP) (hrsi : sa.regs "%rsi" = BitVec.ofNat 64 n)
    (hrax : sa.regs "%rax" = BitVec.ofNat 64 k)
    (hM : CmpMem SP RP AP BP n A B r saved sa.mem) :
    CmpMem SP RP AP BP n A B (cmpSelW r (A (n - 1 - k)) (B (n - 1 - k))) saved
        (runBlockA sa (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).mem
    ∧ (runBlockA sa (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).regs "%rax" = BitVec.ofNat 64 (k + 1)
    ∧ (runBlockA sa (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).regs "%rdi" = sa.regs "%rdi" - 1
    ∧ (∀ r, r ∉ cmpTripRegs →
        (runBlockA sa (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).regs r = sa.regs r)
    ∧ (runBlockA sa (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).view.flagB (·.zf)
        = decide (sa.regs "%rdi" - 1 = 0)
    ∧ Keeps SP RP 1 sa.mem (runBlockA sa (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).mem := by
  have hb := hS.bound
  simp only [runBlockA_append]
  -- index
  obtain ⟨i1, i9, fI, mI⟩ := cI_run sa
  generalize hs1 : runBlockA sa cI = s1 at i1 i9 fI mI
  rw [hrsi, hrax, idx_eq n k hk hb] at i1
  have e1 := fun r (h1 : r ≠ "%rbp") (h2 : r ≠ "%r8") (h3 : r ≠ "%r9") => fI r h1 h2 h3
  -- loads
  obtain ⟨l8, l10, lbp, fL, mL⟩ := cL_run s1 RP AP BP
    (by rw [e1 _ (by decide) (by decide) (by decide), hrsp, mI]; exact hM.ap)
    (by rw [e1 _ (by decide) (by decide) (by decide), hrsp, mI]; exact hM.bp)
    (by rw [e1 _ (by decide) (by decide) (by decide), hrsp, mI]; exact hM.rp)
  generalize hs2 : runBlockA s1 cL = s2 at l8 l10 lbp fL mL
  rw [i1, mI, hM.apw _ (by omega)] at l8
  rw [i1, mI, hM.bpw _ (by omega)] at l10
  rw [i9, mI] at lbp
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hM.r0] at lbp
  -- lt
  obtain ⟨t1, fT1, mT1⟩ := cLt_run s2
  generalize hs3 : runBlockA s2 cLt = s3 at t1 fT1 mT1
  rw [l8, l10] at t1
  have e3r8 : s3.regs "%r8" = A (n - 1 - k) :=
    (fT1 _ (by decide) (by decide) (by decide) (by decide)).trans l8
  have e3r10 : s3.regs "%r10" = B (n - 1 - k) :=
    (fT1 _ (by decide) (by decide) (by decide) (by decide)).trans l10
  -- gt
  obtain ⟨g1, fG, mG⟩ := cGt_run s3
  generalize hs4 : runBlockA s3 cGt = s4 at g1 fG mG
  rw [e3r8, e3r10] at g1
  have e4rdx : s4.regs "%rdx" = bSltu (A (n - 1 - k)) (B (n - 1 - k)) :=
    (fG _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans t1
  -- difference
  obtain ⟨d1, fD, mD⟩ := cD_run s4
  generalize hs5 : runBlockA s4 cD = s5 at d1 fD mD
  rw [g1, e4rdx] at d1
  have e5rbp : s5.regs "%rbp" = r :=
    (fD _ (by decide) (by decide)).trans ((fG _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ((fT1 _ (by decide) (by decide) (by decide)
        (by decide)).trans lbp))
  -- selection
  obtain ⟨c1, fS, mS⟩ := cS_run s5
  generalize hs6 : runBlockA s5 cS = s6 at c1 fS mS
  rw [e5rbp, d1] at c1
  have fr6 : ∀ q, q ∉ cmpTripRegs → s6.regs q = sa.regs q := by
    intro q hq
    simp only [cmpTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨a, b, c, d, e, g, h, i, j, l, -, -⟩ := hq
    rw [fS q j b e g l, fD q b l, fG q b e g h i l, fT1 q g h i j, fL q d b e a,
      fI q a b c]
  have e6rsp : s6.regs "%rsp" = SP := (fr6 _ (by decide)).trans hrsp
  have e6r9 : s6.regs "%r9" = 0#64 := by
    rw [fS _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fD _ (by decide) (by decide),
      fG _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      fT1 _ (by decide) (by decide) (by decide) (by decide),
      fL _ (by decide) (by decide) (by decide) (by decide), i9]
  have e6rax : s6.regs "%rax" = BitVec.ofNat 64 k := by
    rw [fS _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fD _ (by decide) (by decide),
      fG _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      fT1 _ (by decide) (by decide) (by decide) (by decide),
      fL _ (by decide) (by decide) (by decide) (by decide),
      fI _ (by decide) (by decide) (by decide), hrax]
  have e6rdi : s6.regs "%rdi" = sa.regs "%rdi" := by
    rw [fS _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fD _ (by decide) (by decide),
      fG _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      fT1 _ (by decide) (by decide) (by decide) (by decide),
      fL _ (by decide) (by decide) (by decide) (by decide),
      fI _ (by decide) (by decide) (by decide)]
  have m6 : s6.mem = sa.mem := by rw [mS, mD, mG, mT1, mL, mI]
  -- tail
  obtain ⟨tm, tax, tdi, fT, tz⟩ := cT_run s6 RP (by rw [e6rsp, m6]; exact hM.rp)
  generalize hs7 : runBlockA s6 cT = s7 at tm tax tdi fT tz
  rw [e6r9, c1, m6] at tm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm]
    exact hM.out hS hsv _
  · rw [tax, e6rax]; simp [BitVec.ofNat_add]
  · rw [tdi, e6rdi]
  · intro q hq
    have hq' := hq
    simp only [cmpTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
    obtain ⟨-, -, -, a, -, -, -, -, -, -, b, c⟩ := hq'
    rw [fT q a b c]; exact fr6 q hq
  · rw [tz, e6rdi]
  · rw [tm]; exact Keeps.out 0 (by omega) _ (Keeps.refl _)

/-! ## 4. The loop, the prologue, the epilogue -/

theorem cmpDecPre_length : cmpDecPre.length = 21 := rfl

theorem cmpFold_get_succ {n : Nat} (A B : Nat → BitVec 64) (acc : Fin 1 → BitVec 64) (k : Nat)
    (hk : k < n) :
    memGetDyn (cmpFold (arr n A) (arr n B) (n - 1) (k + 1) acc) 0
      = cmpSelW (memGetDyn (cmpFold (arr n A) (arr n B) (n - 1) k acc) 0)
          (A (n - 1 - k)) (B (n - 1 - k)) := by
  rw [cmpFold_succ, cmpFoldStep, memGetDyn_memSetDyn _ (by omega) (by omega),
    memGetDyn_arr _ _ _ (by omega), memGetDyn_arr _ _ _ (by omega)]
  simp

/-- **The loop is `cmpFold`.** -/
theorem cmp_loop {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : CmpSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ cmpOffs) (hn : 0 < n) (acc : Fin 1 → BitVec 64) (s0 : AState)
    (hrsp : s0.regs "%rsp" = SP) (hrsi : s0.regs "%rsi" = BitVec.ofNat 64 n)
    (hrax : s0.regs "%rax" = BitVec.ofNat 64 0) (hrdi : s0.regs "%rdi" = BitVec.ofNat 64 n)
    (hM : CmpMem SP RP AP BP n A B (memGetDyn acc 0) saved s0.mem) :
    ∃ s', Reaches aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 23 s0
        (cmpDecPre.length + 2 + (cmpDecLoop.body.length + 1) + 1) s'
      ∧ (∀ r, r ∉ cmpTripRegs → s'.regs r = s0.regs r)
      ∧ CmpMem SP RP AP BP n A B (memGetDyn (cmpFold (arr n A) (arr n B) (n - 1) n acc) 0)
          saved s'.mem
      ∧ Keeps SP RP 1 s0.mem s'.mem := by
  have hb := hS.bound
  let Inv : Nat → AState → Prop := fun k s =>
    (∀ r, r ∉ cmpTripRegs → s.regs r = s0.regs r) ∧ s.regs "%rax" = BitVec.ofNat 64 k
      ∧ s.regs "%rdi" = BitVec.ofNat 64 (n - k)
      ∧ CmpMem SP RP AP BP n A B (memGetDyn (cmpFold (arr n A) (arr n B) (n - 1) k acc) 0)
          saved s.mem
      ∧ Keeps SP RP 1 s0.mem s.mem
  have hbody : ∀ k s, k < n → Inv k s → ∃ s', Reaches aMachine
      (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 23 s
      (cmpDecPre.length + 2 + (cmpDecLoop.body.length + 1)) s' ∧
      (aMachine.view s').flagB (·.zf) = decide (k + 1 = n) ∧ Inv (k + 1) s' := by
    intro k s hk ⟨hf, hax, hdi, hm, hkp⟩
    obtain ⟨M', eax, edi, f', z', kp'⟩ := cmp_trip hS hsv k hk _ s
      ((hf _ (by decide)).trans hrsp) ((hf _ (by decide)).trans hrsi) hax hm
    have hdi' : s.regs "%rdi" = BitVec.ofNat 64 (n - k - 1 + 1) := by
      rw [hdi]; grind
    refine ⟨runBlockA s (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT), ?_, ?_, ?_, eax, ?_, ?_,
      hkp.trans kp'⟩
    · have h := node_reach_body cmpDecPre cmpDecPost cmpDecLoop s
      rw [cmpBody_eq] at h
      exact h
    · show (runBlockA s (cI ++ cL ++ cLt ++ cGt ++ cD ++ cS ++ cT)).view.flagB (·.zf) = _
      rw [z', hdi', cnt_dec]
      exact decide_eq_decide.mpr ((ofNat_eq_zero_iff _ (by omega)).trans (by omega))
    · intro r hr; exact (f' r hr).trans (hf r hr)
    · rw [edi, hdi', cnt_dec]; congr 1
    · rw [cmpFold_get_succ A B acc k hk]; exact M'
  have h0 : Inv 0 s0 :=
    ⟨fun _ _ => rfl, hrax, by simpa using hrdi, by simpa [cmpFold] using hM, Keeps.refl _⟩
  obtain ⟨s', hr, hf, -, -, hm, hkp⟩ :=
    reaches_doWhile aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 23
      (cmpDecPre.length + 2 + (cmpDecLoop.body.length + 1))
      (node_jne cmpDecPre cmpDecPost cmpDecLoop) Inv n hbody 0 s0 hn h0
  exact ⟨s', hr, hf, hm, hkp⟩

theorem savedOf_cmpOffs (s0 : AState) : ∀ e ∈ savedOf s0, e.1 ∈ cmpOffs := by
  intro e he
  simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cmpOffs]

/-- The array part of the invariant. -/
structure CmpArr (RP AP BP : BitVec 64) (n : Nat) (A B : Nat → BitVec 64) (r : BitVec 64)
    (m : AMem) : Prop where
  apw : ∀ j, j < n → read64 m (ix AP (BitVec.ofNat 64 j)) = A j
  bpw : ∀ j, j < n → read64 m (ix BP (BitVec.ofNat 64 j)) = B j
  r0 : read64 m (ix RP (BitVec.ofNat 64 0)) = r

theorem CmpArr.slot {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64} {r : BitVec 64}
    {m : AMem} (hS : CmpSep SP RP AP BP n) (o : Int) (ho : o ∈ cmpOffs) (v : BitVec 64)
    (h : CmpArr RP AP BP n A B r m) : CmpArr RP AP BP n A B r (write64 m (at' SP o) v) where
  apw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.as j hj o ho).symm]; exact h.apw j hj
  bpw j hj := by rw [read64_write64_of_disjoint _ _ _ _ (hS.bs j hj o ho).symm]; exact h.bpw j hj
  r0 := by rw [read64_write64_of_disjoint _ _ _ _ (hS.rs o ho).symm]; exact h.r0

/-- **The prologue** (with the loop guard). -/
theorem cmp_pre_run (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : CmpSep (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      n) :
    (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rsp" = at' (s0.regs "%rsp") (-80)
    ∧ (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rax" = BitVec.ofNat 64 0
    ∧ (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rdi" = BitVec.ofNat 64 n
    ∧ (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rsi" = BitVec.ofNat 64 n
    ∧ CmpMem (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
        (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
        (wordsOf s0.mem (s0.regs "%rdi") 0) (savedOf s0)
        (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).mem
    ∧ (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).view.flagB (·.zf)
        = decide (BitVec.ofNat 64 n = 0)
    ∧ Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") 1 s0.mem
        (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).mem := by
  have arr0 : CmpArr (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
      (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
      (wordsOf s0.mem (s0.regs "%rdi") 0) s0.mem := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  have hA' : CmpArr (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
      (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
      (wordsOf s0.mem (s0.regs "%rdi") 0)
        (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).mem ∧
      Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") 1 s0.mem
        (runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)])).mem := by
    simp only [cmpDecPre, List.cons_append, List.nil_append, runBlockA_cons, runBlockA_nil,
      eA_mov_reg, eA_mov_imm, eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply,
      String.reduceEq, ↓reduceIte]
    generalize at' (s0.regs "%rsp") (-80) = SP at hS ⊢
    constructor
    · iterate 12 refine CmpArr.slot hS _ (by decide) _ ?_
      exact arr0
    · iterate 12 refine Keeps.slot' hS _ (by decide) _ ?_
      exact Keeps.refl _
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, fun j hj => hA'.1.apw j hj,
    fun j hj => hA'.1.bpw j hj, hA'.1.r0⟩, ?_, hA'.2⟩
  all_goals rw [runBlockA_append, runBlockA_cons, runBlockA_nil]
  all_goals try rw [cmp0_zf]
  all_goals
    simp only [cmpDecPre, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm,
      eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply, String.reduceEq, ↓reduceIte]
  all_goals generalize at' (s0.regs "%rsp") (-80) = SP at hS ⊢
  all_goals first
    | (simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte, hrcx]; done)
    | (intro e he
       simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
       rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
         simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte])

theorem cmpPost_eq : cmpDecPost = MpnAddSubShipped.subPost := rfl

/-! ## 5. The run of the linked `mpn_cmp_ct` -/

/-- **The machine run.** From an entry state with `rp`, `ap`, `bp`, `n` in `%rdi`, `%rsi`,
    `%rdx`, `%rcx` and `CmpSep` (frame base `%rsp - 80`), the machine halts with `rp[0]` the
    compare fold of the entry words, `%rsp` and the callee-saved registers restored, and the
    memory outside the frame bytes and `rp[0]` as at the entry. -/
theorem cmp_halts (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : CmpSep (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      n) :
    ∃ s', Halts aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 s0 s'
      ∧ wordsOf s'.mem (s0.regs "%rdi") 0
          = memGetDyn (cmpFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) (n - 1) n
              (arr 1 (fun _ => wordsOf s0.mem (s0.regs "%rdi") 0))) 0
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
      ∧ Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") 1 s0.mem s'.mem := by
  have hb := hS.bound
  have hcmp : cmpDecLoop.cmpInstr = .cmp "%rdi" (.imm 0) := rfl
  obtain ⟨p1, p3, p4, p5, pM, pz, pk⟩ := cmp_pre_run s0 n hrcx hS
  have hr1 := node_reach_pre cmpDecPre cmpDecPost cmpDecLoop s0
  rw [hcmp] at hr1
  generalize hs1 : runBlockA s0 (cmpDecPre ++ [.cmp "%rdi" (.imm 0)]) = s1
    at p1 p3 p4 p5 pM pz pk hr1
  let acc0 : Fin 1 → BitVec 64 := arr 1 (fun _ => wordsOf s0.mem (s0.regs "%rdi") 0)
  have hacc : memGetDyn acc0 0 = wordsOf s0.mem (s0.regs "%rdi") 0 := memGetDyn_arr _ _ 0 (by omega)
  let E := cmpDecPre.length + cmpDecLoop.body.length + 4
  have hje := node_je cmpDecPre cmpDecPost cmpDecLoop
  obtain ⟨s2, hr2, e2, M2, K2⟩ : ∃ s2, Reaches aMachine
        (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 s0 E s2
      ∧ s2.regs "%rsp" = at' (s0.regs "%rsp") (-80)
      ∧ CmpMem (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
          (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
          (memGetDyn (cmpFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) (n - 1) n acc0) 0) (savedOf s0) s2.mem
      ∧ Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") 1 s0.mem s2.mem := by
    by_cases hn : n = 0
    · subst hn
      refine ⟨s1, hr1.trans (.single ?_), p1, ?_, pk⟩
      · rw [step_je aMachine _ _ _ s1 hje]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        rw [pz]; simp [E]
      · simpa [cmpFold, hacc] using pM
    · have hstep : RInstrSemantics.step aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost)
          (cmpDecPre.length + 1) s1 = some (.go (cmpDecPre.length + 1 + 1) s1) := by
        rw [step_je aMachine _ _ _ s1 hje]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        have hne : ¬ BitVec.ofNat 64 n = 0#64 := fun h =>
          hn ((ofNat_eq_zero_iff n (by omega)).mp h)
        rw [pz]; simp [hne]
      obtain ⟨s2, hr2, hf, M2, K2⟩ := cmp_loop hS (savedOf_cmpOffs s0) (Nat.pos_of_ne_zero hn)
        acc0 s1 p1 p5 p3 p4 (by rw [hacc]; exact pM)
      have e2 : s2.regs "%rsp" = at' (s0.regs "%rsp") (-80) := (hf _ (by decide)).trans p1
      refine ⟨s2, hr1.trans (.next hstep ?_), e2, M2, pk.trans K2⟩
      have e : cmpDecPre.length + 2 + (cmpDecLoop.body.length + 1) + 1 = E := by
        simp only [E]; omega
      rw [← e]
      exact hr2
  obtain ⟨q1, q2, -, q3⟩ := MpnSubBytesValue.post_run s0 s2 _ e2 M2.saved
  rw [← cmpPost_eq] at q1 q2 q3
  refine ⟨runBlockA s2 cmpDecPost, halts_of_reaches (hr2.trans
    (node_reach_post cmpDecPre cmpDecPost cmpDecLoop s2))
    (node_ret cmpDecPre cmpDecPost cmpDecLoop), ?_,
    by rw [q1, at'_at'], q2, by rw [q3]; exact K2⟩
  rw [wordsOf, q3]
  exact M2.r0

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lfundef)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)

/-- **The linked `mpn_cmp_ct`, for every count.** The program `MpnRuntimeBytesEmit.kernels`
    maps to the symbol is one function whose function bytes decode to
    `nodeLayout cmpDecPre cmpDecLoop cmpDecPost`; from every entry state with `rp`, `ap`, `bp`,
    `n` in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `rp[0] = 0` (the model's seed) and `CmpSep` (any
    `n < 2^64`, including `0`), the machine halts with
    `rp'[0] = cmpSign (value ap[0..n)) (value bp[0..n))`, `%rsp` and the callee-saved registers
    restored, and no byte written outside the 96 frame bytes and `rp[0]`. -/
theorem mpn_cmp_ct_direct_correct :
    ∃ fd : Lfundef,
      (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct").map (·.lp_funcs) = some [("mpn_cmp_ct", fd)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes fd.lfd_body)
          = some (nodeLayout cmpDecPre cmpDecLoop cmpDecPost)
      ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
        wordsOf s0.mem (s0.regs "%rdi") 0 = 0 →
        CmpSep (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n →
        ∃ s', Halts aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 s0 s'
          ∧ wordsOf s'.mem (s0.regs "%rdi") 0
              = cmpSign (bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi"))))
                  (bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx"))))
          ∧ s'.regs "%rsp" = s0.regs "%rsp"
          ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
          ∧ Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") 1 s0.mem s'.mem := by
  refine ⟨_, by rw [cmpLprog_eq]; rfl, by rw [cmpPhysAbi_eq]; exact cmpPhysLit_decode, ?_⟩
  intro s0 n hrcx h0 hS
  obtain ⟨s', hh, hw, hsp, hcs, hk⟩ := cmp_halts s0 n hrcx hS
  refine ⟨s', hh, ?_, hsp, hcs, hk⟩
  rw [hw]
  by_cases hn : n = 0
  · subst hn
    simp [cmpFold, memGetDyn_arr, h0, cmpSign, bignumVal]
  · have hv := MpnCarryIdiomsHand.cmpFold_val_full_hand (arr n (wordsOf s0.mem (s0.regs "%rsi")))
      (arr n (wordsOf s0.mem (s0.regs "%rdx"))) (n - 1)
      (arr 1 (fun _ => wordsOf s0.mem (s0.regs "%rdi") 0)) (by omega)
      (by rw [memGetDyn_arr _ _ 0 (by omega)]; exact h0)
    rw [show n - 1 + 1 = n by omega] at hv
    rw [hv]
    have hseg : ∀ (f : Nat → BitVec 64), segCells (arr n f) 0 n = (List.range n).map f := by
      intro f
      simp only [segCells]
      refine List.map_congr_left (fun i hi => ?_)
      rw [List.mem_range] at hi
      rw [Nat.zero_add, memGetDyn_arr _ _ _ hi]
    rw [hseg, hseg]

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesDirect
