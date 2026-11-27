/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue

@[expose] public section

set_option autoImplicit false

/-!
# The linked bitwise kernels for every count, in place

`MpnChainFrame.mpn_and_n_frame_correct` and its siblings state the result of the linked
`mpn_{and,ior,xor}_n_loop_owned` for counts up to the model's array size (`4`) and with the
output disjoint from the sources, because they go through the canonical node of the
front-compiled body. This module runs the decoded programs (`MpnBinExportTerm`'s
`nodeLayout <k>DecPre <k>DecLoop <k>DecPost`) on the address machine directly, as
`MpnAddBytesValue` does for add: one trip is three segments (the loads `bL`, the limb
operation, the store and counter steps `bT`), the loop is a do-while loop by its invariant.
The result holds for every count `n < 2^64`, with `rp` equal to `ap` or `bp`, or below them,
or disjoint from them (`MpnAddBytesValue.AddSep`, the frame of the three kernels being that of
add).

## Main results

* `bin_halts`: the generic run, for a limb operation segment `op` that computes `f a b`.
* `mpn_and_n_direct_correct`, `mpn_ior_n_direct_correct`, `mpn_xor_n_direct_correct`: for the
  program `MpnLoopBytesEmit.kernels` maps to the symbol, its function bytes decode to the node
  layout and from every entry state with `AddSep` the machine halts with
  `rp'[j] = ap[j] op bp[j]` for every `j < n`, `%rsp` and the callee-saved registers restored,
  and no byte written outside the frame and the `n` words of `rp`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinBytesDirect

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
  (upd upd_apply flA ix at' eA_mov_reg eA_mov_imm eA_xor eA_and eA_add eA_add_imm eA_sub_imm
   eA_cmp eA_loadMem eA_loadMemIdx eA_storeMem eA_storeMemIdx cmp0_zf xor_xor_and)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
  (cnt_dec ofNat_eq_zero_iff eA_lea_self rd_at wordsOf calleeSavedL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue
  (AddSep AddMem Keeps Keeps.refl Keeps.trans Keeps.slot Keeps.out addOffs savedOf savedOf_offs
   ArrOK ArrOK.slot at'_at')
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout guardedLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach (reaches_doWhile step_je)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm

/-! ## 1. The segments of a trip -/

/-- The loads of a trip: `%rbp = ap[i]`, `%r8 = bp[i]` for the index `i` in `%rax`. -/
def bL : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax")
  , .loadMem "%r14" "%rsp" 48, .loadMemIdx "%rbp" "%r14" "%rsi" 8
  , .loadMem "%r14" "%rsp" (-8), .loadMemIdx "%r8" "%r14" "%rsi" 8 ]

/-- The store of `D` to `rp[i]`, the index and counter steps, the invariant touches and the
    back-edge compare. -/
def bT (D : String) : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg D)
  , .mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rdi" (.imm 1)
  , .cmp "%rdi" (.reg "%rcx"), .cmp "%rdi" (.reg "%rdx"), .cmp "%rdi" (.imm 0) ]

def andOp : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rbp"), .and_ "%r9" (.reg "%r8"), .mov "%rbp" (.reg "%r9") ]

def xorOp : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rbp"), .xor_ "%r9" (.reg "%r8"), .mov "%rbp" (.reg "%r9") ]

def iorOp : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rbp"), .xor_ "%r9" (.reg "%r8"), .mov "%r10" (.reg "%rbp")
  , .and_ "%r10" (.reg "%r8"), .mov "%rbp" (.reg "%r9"), .xor_ "%rbp" (.reg "%r10")
  , .mov "%r8" (.reg "%rbp") ]

theorem andBody_eq : andDecLoop.body ++ [andDecLoop.cmpInstr] = bL ++ andOp ++ bT "%rbp" := rfl
theorem xorBody_eq : xorDecLoop.body ++ [xorDecLoop.cmpInstr] = bL ++ xorOp ++ bT "%rbp" := rfl
theorem iorBody_eq : iorDecLoop.body ++ [iorDecLoop.cmpInstr] = bL ++ iorOp ++ bT "%r8" := rfl

/-- The registers a trip may write. -/
def binTripRegs : List String := ["%rsi", "%r14", "%rbp", "%r8", "%r9", "%r10", "%rax", "%rdi"]

/-- A limb operation segment: it leaves `f a b` in `D` for `a`, `b` in `%rbp`, `%r8`, writes
    only `%rbp`, `%r8`, `%r9`, `%r10`, and keeps the memory. -/
structure OpSpec (op : List (JInstr 64)) (D : String) (f : BitVec 64 → BitVec 64 → BitVec 64) :
    Prop where
  val : ∀ sa : AState, (runBlockA sa op).regs D = f (sa.regs "%rbp") (sa.regs "%r8")
  keep : ∀ (sa : AState) (r : String), r ≠ "%rbp" → r ≠ "%r8" → r ≠ "%r9" → r ≠ "%r10" →
    (runBlockA sa op).regs r = sa.regs r
  mem : ∀ sa : AState, (runBlockA sa op).mem = sa.mem
  dst : D = "%rbp" ∨ D = "%r8"

theorem andOp_spec : OpSpec andOp "%rbp" (· &&& ·) where
  val sa := by simp [andOp, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_and, upd_apply]
  keep sa r h1 h2 h3 h4 := by
    simp [andOp, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_and, upd_apply, h1, h3]
  mem sa := rfl
  dst := .inl rfl

theorem xorOp_spec : OpSpec xorOp "%rbp" (· ^^^ ·) where
  val sa := by simp [xorOp, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_xor, upd_apply]
  keep sa r h1 h2 h3 h4 := by
    simp [xorOp, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_xor, upd_apply, h1, h3]
  mem sa := rfl
  dst := .inl rfl

theorem iorOp_spec : OpSpec iorOp "%r8" (· ||| ·) where
  val sa := by
    simp only [iorOp, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_xor, eA_and, upd_apply,
      String.reduceEq, ↓reduceIte]
    exact xor_xor_and _ _
  keep sa r h1 h2 h3 h4 := by
    simp [iorOp, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_xor, eA_and, upd_apply, h1, h2,
      h3, h4]
  mem sa := rfl
  dst := .inr rfl

theorem bL_run (sa : AState) (AP BP : BitVec 64)
    (hap : read64 sa.mem (at' (sa.regs "%rsp") 48) = AP)
    (hbp : read64 sa.mem (at' (sa.regs "%rsp") (-8)) = BP) :
    (runBlockA sa bL).regs "%rbp" = read64 sa.mem (ix AP (sa.regs "%rax"))
    ∧ (runBlockA sa bL).regs "%r8" = read64 sa.mem (ix BP (sa.regs "%rax"))
    ∧ (runBlockA sa bL).regs "%rsi" = sa.regs "%rax"
    ∧ (∀ r, r ≠ "%rsi" → r ≠ "%r14" → r ≠ "%rbp" → r ≠ "%r8" →
        (runBlockA sa bL).regs r = sa.regs r)
    ∧ (runBlockA sa bL).mem = sa.mem := by
  simp only [bL, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_loadMem, eA_loadMemIdx, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hap]
  · simp [hbp]
  · simp
  · intro r h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  · trivial

theorem bT_run (D : String) (hD : D = "%rbp" ∨ D = "%r8") (sa : AState) (RP : BitVec 64)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 56) = RP) :
    (runBlockA sa (bT D)).mem = write64 sa.mem (ix RP (sa.regs "%rsi")) (sa.regs D)
    ∧ (runBlockA sa (bT D)).regs "%rax" = sa.regs "%rax" + 1
    ∧ (runBlockA sa (bT D)).regs "%rdi" = sa.regs "%rdi" - 1
    ∧ (∀ r, r ≠ "%r14" → r ≠ "%rax" → r ≠ "%rdi" → (runBlockA sa (bT D)).regs r = sa.regs r)
    ∧ (runBlockA sa (bT D)).view.flagB (·.zf) = decide (sa.regs "%rdi" - 1 = 0) := by
  have hsplit : bT D = (bT D).dropLast ++ [.cmp "%rdi" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  have hD14 : D ≠ "%r14" := by rcases hD with rfl | rfl <;> decide
  simp only [List.dropLast, bT, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_add_imm,
    eA_sub_imm, eA_loadMem, eA_storeMemIdx, eA_cmp, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hrp, hD14]
  · simp
  · simp
  · intro r h1 h2 h3
    by_cases hb : r = "%rbx"
    · subst hb; simp
    · simp [h1, h2, h3, hb]
  · simp

/-! ## 2. One trip -/

/-- The output words after `k` trips: `f a b` below `k`, the entry words from `k` on. -/
def binOut (f : BitVec 64 → BitVec 64 → BitVec 64) (A B R : Nat → BitVec 64) (k : Nat) :
    Nat → BitVec 64 :=
  fun i => if i < k then f (A i) (B i) else R i

/-- **One trip.** From a state at the head of trip `k < n`, `runBlockA` of the trip writes
    `f (ap[k]) (bp[k])` to `rp[k]`, moves the invariant to trip `k + 1`, steps the index and
    the counter, writes no register outside `binTripRegs`, and sets the zero flag exactly when
    the decremented counter is zero. -/
theorem bin_trip {op : List (JInstr 64)} {D : String} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hop : OpSpec op D f) {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : AddSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) (k : Nat) (hk : k < n) (R : Nat → BitVec 64)
    (sa : AState) (hrsp : sa.regs "%rsp" = SP) (hrax : sa.regs "%rax" = BitVec.ofNat 64 k)
    (hM : AddMem SP RP AP BP n k A B (binOut f A B R k) saved sa.mem) :
    AddMem SP RP AP BP n (k + 1) A B (binOut f A B R (k + 1)) saved
        (runBlockA sa (bL ++ op ++ bT D)).mem
    ∧ (runBlockA sa (bL ++ op ++ bT D)).regs "%rax" = BitVec.ofNat 64 (k + 1)
    ∧ (runBlockA sa (bL ++ op ++ bT D)).regs "%rdi" = sa.regs "%rdi" - 1
    ∧ (∀ r, r ∉ binTripRegs → (runBlockA sa (bL ++ op ++ bT D)).regs r = sa.regs r)
    ∧ (runBlockA sa (bL ++ op ++ bT D)).view.flagB (·.zf) = decide (sa.regs "%rdi" - 1 = 0)
    ∧ Keeps SP RP n sa.mem (runBlockA sa (bL ++ op ++ bT D)).mem := by
  simp only [runBlockA_append]
  obtain ⟨l1, l2, lsi, fL, mL⟩ := bL_run sa AP BP (by rw [hrsp]; exact hM.ap)
    (by rw [hrsp]; exact hM.bp)
  generalize hs1 : runBlockA sa bL = s1 at l1 l2 lsi fL mL
  rw [hrax, hM.apw k le_rfl hk] at l1
  rw [hrax, hM.bpw k le_rfl hk] at l2
  rw [hrax] at lsi
  have v2 := hop.val s1
  have f2 := hop.keep s1
  have m2 := hop.mem s1
  generalize hs2 : runBlockA s1 op = s2 at v2 f2 m2
  rw [l1, l2] at v2
  have e2rsp : s2.regs "%rsp" = SP :=
    (f2 _ (by decide) (by decide) (by decide) (by decide)).trans
      ((fL _ (by decide) (by decide) (by decide) (by decide)).trans hrsp)
  have e2rsi : s2.regs "%rsi" = BitVec.ofNat 64 k :=
    (f2 _ (by decide) (by decide) (by decide) (by decide)).trans lsi
  have e2rax : s2.regs "%rax" = BitVec.ofNat 64 k :=
    (f2 _ (by decide) (by decide) (by decide) (by decide)).trans
      ((fL _ (by decide) (by decide) (by decide) (by decide)).trans hrax)
  have e2rdi : s2.regs "%rdi" = sa.regs "%rdi" :=
    (f2 _ (by decide) (by decide) (by decide) (by decide)).trans
      (fL _ (by decide) (by decide) (by decide) (by decide))
  have m2' : s2.mem = sa.mem := by rw [m2, mL]
  obtain ⟨tm, tax, tdi, fT, tz⟩ := bT_run D hop.dst s2 RP (by rw [e2rsp, m2']; exact hM.rp)
  generalize hs3 : runBlockA s2 (bT D) = s3 at tm tax tdi fT tz
  rw [e2rsi, v2, m2'] at tm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm]
    refine (hM.out hS hsv hk _).congr ?_
    intro i hi
    simp only [binOut]
    by_cases hik : i = k
    · subst hik; simp
    · have : (i < k + 1) = (i < k) := propext ⟨fun h => by omega, fun h => by omega⟩
      simp [hik, this]
  · rw [tax, e2rax]; simp [BitVec.ofNat_add]
  · rw [tdi, e2rdi]
  · intro r hr
    simp only [binTripRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, g, h, i⟩ := hr
    rw [fT r b h i, f2 r c d e g, fL r a b c d]
  · rw [tz, e2rdi]
  · rw [tm]; exact Keeps.out _ hk _ (Keeps.refl _)

/-! ## 3. The program -/

section Prog

variable (pre post : List (JInstr 64)) (l : XLoop 64)

theorem node_split_body :
    nodeLayout pre l post = (pre.map RInstr.op ++ [RInstr.op l.cmpInstr,
        .jcc 4 (pre.length + l.body.length + 4)]) ++ (l.body ++ [l.cmpInstr]).map RInstr.op
      ++ ([.jcc 5 (pre.length + 2)] ++ post.map RInstr.op ++ [.ret]) := by
  simp only [nodeLayout, guardedLayout, List.length_map, List.append_assoc]

theorem node_split_pre :
    nodeLayout pre l post = ([] : List RInstr) ++ (pre ++ [l.cmpInstr]).map RInstr.op
      ++ ([.jcc 4 (pre.length + l.body.length + 4)] ++ (l.body ++ [l.cmpInstr]).map RInstr.op
        ++ [.jcc 5 (pre.length + 2)] ++ post.map RInstr.op ++ [.ret]) := by
  simp only [nodeLayout, guardedLayout, List.length_map, List.append_assoc, List.map_append,
    List.nil_append, List.map_cons, List.map_nil, List.cons_append]

theorem node_split_post :
    nodeLayout pre l post = (pre.map RInstr.op ++ [RInstr.op l.cmpInstr,
        .jcc 4 (pre.length + l.body.length + 4)] ++ (l.body ++ [l.cmpInstr]).map RInstr.op
        ++ [.jcc 5 (pre.length + 2)]) ++ post.map RInstr.op ++ [.ret] := by
  simp only [nodeLayout, guardedLayout, List.length_map, List.append_assoc]

theorem node_reach_body (s : AState) :
    Reaches aMachine (nodeLayout pre l post) (pre.length + 2) s
      (pre.length + 2 + (l.body.length + 1)) (runBlockA s (l.body ++ [l.cmpInstr])) := by
  have h := reaches_ops aMachine (pre.map RInstr.op ++ [RInstr.op l.cmpInstr,
        .jcc 4 (pre.length + l.body.length + 4)]) (l.body ++ [l.cmpInstr])
      ([.jcc 5 (pre.length + 2)] ++ post.map RInstr.op ++ [.ret]) s
  rw [aMachine_runBlock, ← node_split_body] at h
  simpa using h

theorem node_reach_pre (s : AState) :
    Reaches aMachine (nodeLayout pre l post) 0 s (pre.length + 1)
      (runBlockA s (pre ++ [l.cmpInstr])) := by
  have h := reaches_ops aMachine [] (pre ++ [l.cmpInstr])
      ([.jcc 4 (pre.length + l.body.length + 4)] ++ (l.body ++ [l.cmpInstr]).map RInstr.op
        ++ [.jcc 5 (pre.length + 2)] ++ post.map RInstr.op ++ [.ret]) s
  rw [aMachine_runBlock, ← node_split_pre] at h
  simpa using h

theorem node_reach_post (s : AState) :
    Reaches aMachine (nodeLayout pre l post) (pre.length + l.body.length + 4) s
      (pre.length + l.body.length + 4 + post.length) (runBlockA s post) := by
  have h := reaches_ops aMachine (pre.map RInstr.op ++ [RInstr.op l.cmpInstr,
        .jcc 4 (pre.length + l.body.length + 4)] ++ (l.body ++ [l.cmpInstr]).map RInstr.op
        ++ [.jcc 5 (pre.length + 2)]) post [.ret] s
  rw [aMachine_runBlock, ← node_split_post] at h
  have e : (pre.map RInstr.op ++ [RInstr.op l.cmpInstr,
        RInstr.jcc 4 (pre.length + l.body.length + 4)]
        ++ (l.body ++ [l.cmpInstr]).map RInstr.op ++ [RInstr.jcc 5 (pre.length + 2)]).length
      = pre.length + l.body.length + 4 := by simp; omega
  rw [e] at h
  exact h

theorem node_je : (nodeLayout pre l post)[pre.length + 1]?
    = some (.jcc 4 (pre.length + l.body.length + 4)) := by
  have := DecodedLsemLoop.guardedLayout_je (pre.map RInstr.op) l (post.map RInstr.op ++ [.ret])
  simpa [nodeLayout] using this

theorem node_jne : (nodeLayout pre l post)[pre.length + 2 + (l.body.length + 1)]?
    = some (.jcc 5 (pre.length + 2)) := by
  rw [node_split_body]
  simp only [List.getElem?_append, List.length_append, List.length_map, List.length_cons,
    List.length_nil]
  split <;> simp_all

theorem node_ret : (nodeLayout pre l post)[pre.length + l.body.length + 4 + post.length]?
    = some .ret := by
  rw [node_split_post]
  simp only [List.getElem?_append, List.length_append, List.length_map, List.length_cons,
    List.length_nil]
  rw [ite_eq_right (by omega), show pre.length + l.body.length + 4 + post.length - (pre.length
    + (0 + 1 + 1) + (l.body.length + (0 + 1)) + (0 + 1) + post.length) = 0 by omega]
  rfl

end Prog

/-! ## 4. The loop, the prologue, the epilogue -/

theorem andDecPre_length : andDecPre.length = 18 := rfl

/-- **The loop.** From index `20` with the index `0` and the counter `n > 0`, the machine
    reaches the exit index with `f ap[j] bp[j]` in the words `j < n` of `rp`. -/
theorem bin_loop {op : List (JInstr 64)} {D : String} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hop : OpSpec op D f) (l : XLoop 64) (hl : l.body ++ [l.cmpInstr] = bL ++ op ++ bT D)
    {SP RP AP BP : BitVec 64} {n : Nat} {A B : Nat → BitVec 64}
    {saved : List (Int × BitVec 64)} (hS : AddSep SP RP AP BP n)
    (hsv : ∀ e ∈ saved, e.1 ∈ addOffs) (hn : 0 < n) (R : Nat → BitVec 64) (s0 : AState)
    (hrsp : s0.regs "%rsp" = SP) (hrax : s0.regs "%rax" = BitVec.ofNat 64 0)
    (hrdi : s0.regs "%rdi" = BitVec.ofNat 64 n)
    (hM : AddMem SP RP AP BP n 0 A B R saved s0.mem) :
    ∃ s', Reaches aMachine (nodeLayout andDecPre l andDecPost) 20 s0
        (andDecPre.length + 2 + (l.body.length + 1) + 1) s'
      ∧ (∀ r, r ∉ binTripRegs → s'.regs r = s0.regs r)
      ∧ AddMem SP RP AP BP n n A B (binOut f A B R n) saved s'.mem
      ∧ Keeps SP RP n s0.mem s'.mem := by
  have hb := hS.bound
  let Inv : Nat → AState → Prop := fun k s =>
    (∀ r, r ∉ binTripRegs → s.regs r = s0.regs r) ∧ s.regs "%rax" = BitVec.ofNat 64 k
      ∧ s.regs "%rdi" = BitVec.ofNat 64 (n - k)
      ∧ AddMem SP RP AP BP n k A B (binOut f A B R k) saved s.mem
      ∧ Keeps SP RP n s0.mem s.mem
  have hbody : ∀ k s, k < n → Inv k s → ∃ s', Reaches aMachine (nodeLayout andDecPre l andDecPost)
      20 s (andDecPre.length + 2 + (l.body.length + 1)) s' ∧
      (aMachine.view s').flagB (·.zf) = decide (k + 1 = n) ∧ Inv (k + 1) s' := by
    intro k s hk ⟨hf, hax, hdi, hm, hkp⟩
    obtain ⟨M', eax, edi, f', z', kp'⟩ := bin_trip hop hS hsv k hk R s
      ((hf _ (by simp [binTripRegs])).trans hrsp) hax hm
    have hdi' : s.regs "%rdi" = BitVec.ofNat 64 (n - k - 1 + 1) := by
      rw [hdi]; congr 1; omega
    refine ⟨runBlockA s (bL ++ op ++ bT D), ?_, ?_, ?_, eax, ?_, M', hkp.trans kp'⟩
    · have h := node_reach_body andDecPre andDecPost l s
      rw [hl] at h
      exact h
    · show (runBlockA s (bL ++ op ++ bT D)).view.flagB (·.zf) = _
      rw [z', hdi', cnt_dec]
      exact decide_eq_decide.mpr ((ofNat_eq_zero_iff _ (by omega)).trans (by omega))
    · intro r hr; exact (f' r hr).trans (hf r hr)
    · rw [edi, hdi', cnt_dec]; congr 1
  have h0 : Inv 0 s0 :=
    ⟨fun _ _ => rfl, hrax, by simpa using hrdi, hM.congr (fun i _ => by simp [binOut]),
      Keeps.refl _⟩
  obtain ⟨s', hr, hf, -, -, hm, hkp⟩ :=
    reaches_doWhile aMachine (nodeLayout andDecPre l andDecPost) 20
      (andDecPre.length + 2 + (l.body.length + 1)) (node_jne andDecPre andDecPost l) Inv n
      hbody 0 s0 hn h0
  exact ⟨s', hr, hf, hm, hkp⟩

/-- **The prologue** (with the loop guard `cmp %rdi, 0`). -/
theorem bin_pre_run (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      n) :
    (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rsp" = at' (s0.regs "%rsp") (-64)
    ∧ (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rax" = BitVec.ofNat 64 0
    ∧ (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).regs "%rdi" = BitVec.ofNat 64 n
    ∧ AddMem (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n 0
        (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
        (wordsOf s0.mem (s0.regs "%rdi")) (savedOf s0)
        (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).mem
    ∧ (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).view.flagB (·.zf)
        = decide (BitVec.ofNat 64 n = 0)
    ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem
        (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).mem := by
  have arr0 : ArrOK (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
      (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
      (wordsOf s0.mem (s0.regs "%rdi")) s0.mem :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hA : ArrOK (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n
      (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
      (wordsOf s0.mem (s0.regs "%rdi")) (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).mem ∧
      Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem
        (runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)])).mem := by
    simp only [andDecPre, List.cons_append, List.nil_append, runBlockA_cons, runBlockA_nil,
      eA_mov_reg, eA_mov_imm, eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply,
      String.reduceEq, ↓reduceIte]
    generalize at' (s0.regs "%rsp") (-64) = SP at hS ⊢
    constructor
    · iterate 10 refine ArrOK.slot hS _ (by decide) _ ?_
      exact arr0
    · iterate 10 refine Keeps.slot hS _ (by decide) _ ?_
      exact Keeps.refl _
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, fun j _ hj => hA.1.apw j hj,
    fun j _ hj => hA.1.bpw j hj, fun i hi => hA.1.rpw i hi⟩, ?_, hA.2⟩
  all_goals rw [runBlockA_append, runBlockA_cons, runBlockA_nil]
  all_goals try rw [cmp0_zf]
  all_goals
    simp only [andDecPre, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm,
      eA_lea_self, eA_loadMem, eA_storeMem, eA_cmp, upd_apply, String.reduceEq, ↓reduceIte]
  all_goals generalize at' (s0.regs "%rsp") (-64) = SP at hS ⊢
  all_goals first
    | (simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte, hrcx]; done)
    | (intro e he
       simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at he
       rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
         simp (disch := decide) only [rd_at, Int.reduceEq, Int.reduceNeg, ↓reduceIte])

/-- **The epilogue.** -/
theorem bin_post_run (s0 s : AState) (SP : BitVec 64) (hrsp : s.regs "%rsp" = SP)
    (hsv : ∀ e ∈ savedOf s0, read64 s.mem (at' SP e.1) = e.2) :
    (runBlockA s andDecPost).regs "%rsp" = at' SP 64
    ∧ (∀ R ∈ calleeSavedL, (runBlockA s andDecPost).regs R = s0.regs R)
    ∧ (runBlockA s andDecPost).mem = s.mem := by
  simp only [andDecPost, runBlockA_cons, runBlockA_nil, eA_loadMem, eA_lea_self, upd_apply,
    String.reduceEq, ↓reduceIte]
  refine ⟨by rw [hrsp], ?_, trivial⟩
  intro R hR
  simp only [calleeSavedL, List.mem_cons, List.not_mem_nil, or_false] at hR
  have h := fun o v (h : (o, v) ∈ savedOf s0) => hsv (o, v) h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [String.reduceEq, ↓reduceIte] <;>
    rw [hrsp] <;> exact h _ _ (by simp [savedOf])

/-! ## 5. The run of a linked bitwise kernel -/

/-- **The generic run.** For a loop `l` with counter `%rdi` whose trip is `bL ++ op ++ bT D`,
    with `op` computing `f`, the machine halts on `nodeLayout andDecPre l andDecPost` from every
    entry state with `AddSep` (frame base `%rsp - 64`) with `f ap[j] bp[j]` in the words
    `j < n` of `rp`, `%rsp` and the callee-saved registers restored, and the memory outside
    the frame bytes and the `n` words of `rp` as at the entry. -/
theorem bin_halts {op : List (JInstr 64)} {D : String} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hop : OpSpec op D f) (l : XLoop 64) (hctr : l.ctr = "%rdi")
    (hl : l.body ++ [l.cmpInstr] = bL ++ op ++ bT D)
    (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
      n) :
    ∃ s', Halts aMachine (nodeLayout andDecPre l andDecPost) 0 s0 s'
      ∧ (∀ j, j < n → wordsOf s'.mem (s0.regs "%rdi") j
          = f (wordsOf s0.mem (s0.regs "%rsi") j) (wordsOf s0.mem (s0.regs "%rdx") j))
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
      ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s'.mem := by
  have hb := hS.bound
  have hcmp : l.cmpInstr = .cmp "%rdi" (.imm 0) := by
    simp [LprogControlFlow.XLoop.cmpInstr, hctr]
  obtain ⟨p1, p3, p4, pM, pz, pk⟩ := bin_pre_run s0 n hrcx hS
  have hr1 := node_reach_pre andDecPre andDecPost l s0
  rw [hcmp] at hr1
  generalize hs1 : runBlockA s0 (andDecPre ++ [.cmp "%rdi" (.imm 0)]) = s1 at p1 p3 p4 pM pz pk hr1
  let E := andDecPre.length + l.body.length + 4
  have hje := node_je andDecPre andDecPost l
  obtain ⟨s2, hr2, e2, M2, K2⟩ : ∃ s2, Reaches aMachine (nodeLayout andDecPre l andDecPost) 0 s0
        E s2
      ∧ s2.regs "%rsp" = at' (s0.regs "%rsp") (-64)
      ∧ AddMem (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
          n n (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
          (binOut f (wordsOf s0.mem (s0.regs "%rsi")) (wordsOf s0.mem (s0.regs "%rdx"))
            (wordsOf s0.mem (s0.regs "%rdi")) n) (savedOf s0) s2.mem
      ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s2.mem := by
    by_cases hn : n = 0
    · subst hn
      refine ⟨s1, hr1.trans (.single ?_), p1, ?_, pk⟩
      · rw [step_je aMachine _ _ _ s1 hje]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        rw [pz]; simp [E]
      · exact ⟨pM.rp, pM.ap, pM.bp, pM.saved, fun j _ hj => absurd hj (Nat.not_lt_zero _),
          fun j _ hj => absurd hj (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · have hstep : RInstrSemantics.step aMachine (nodeLayout andDecPre l andDecPost)
          (andDecPre.length + 1) s1 = some (.go (andDecPre.length + 1 + 1) s1) := by
        rw [step_je aMachine _ _ _ s1 hje]
        show some (if s1.view.flagB (·.zf) = true then _ else _) = _
        have hne : ¬ BitVec.ofNat 64 n = 0#64 := fun h =>
          hn ((ofNat_eq_zero_iff n (by omega)).mp h)
        rw [pz]; simp [hne]
      obtain ⟨s2, hr2, hf, M2, K2⟩ := bin_loop hop l hl hS (savedOf_offs s0)
        (Nat.pos_of_ne_zero hn) _ s1 p1 p3 p4 pM
      have e2 : s2.regs "%rsp" = at' (s0.regs "%rsp") (-64) := (hf _ (by decide)).trans p1
      refine ⟨s2, hr1.trans (.next hstep ?_), e2, M2, pk.trans K2⟩
      have e : andDecPre.length + 2 + (l.body.length + 1) + 1 = E := by simp only [E]; omega
      rw [← e]
      exact hr2
  obtain ⟨q1, q2, q3⟩ := bin_post_run s0 s2 _ e2 M2.saved
  refine ⟨runBlockA s2 andDecPost, halts_of_reaches (hr2.trans
    (node_reach_post andDecPre andDecPost l s2)) (node_ret andDecPre andDecPost l), ?_,
    by rw [q1, at'_at'], q2, by rw [q3]; exact K2⟩
  intro j hj
  rw [wordsOf, q3, M2.rpw j hj]
  simp [binOut, hj]

/-! ## 6. The linked kernels -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lfundef ComL)

theorem iorLprog_decode' :
    ∃ f : Lfundef, (MpnLoopFrontEmit.iorLprog ()).map (·.lp_funcs)
        = some [("mpn_ior_n_loop_owned", f)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes f.lfd_body)
          = some (nodeLayout iorDecPre iorDecLoop iorDecPost) := by
  refine ⟨_, by rw [iorLprog_eq]; rfl, ?_⟩
  rw [iorPhysAbi_eq]
  exact iorPhysLit_decode

theorem xorLprog_decode' :
    ∃ f : Lfundef, (MpnLoopFrontEmit.xorLprog ()).map (·.lp_funcs)
        = some [("mpn_xor_n_loop_owned", f)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes f.lfd_body)
          = some (nodeLayout xorDecPre xorDecLoop xorDecPost) := by
  refine ⟨_, by rw [xorLprog_eq]; rfl, ?_⟩
  rw [xorPhysAbi_eq]
  exact xorPhysLit_decode

theorem iorPre_eq : iorDecPre = andDecPre := rfl
theorem iorPost_eq : iorDecPost = andDecPost := rfl
theorem xorPre_eq : xorDecPre = andDecPre := rfl
theorem xorPost_eq : xorDecPost = andDecPost := rfl

/-- **The linked `mpn_and_n_loop_owned`, for every count, in place.** The program
    `MpnLoopBytesEmit.kernels` maps to the symbol is one function whose function bytes decode
    to `nodeLayout andDecPre andDecLoop andDecPost`; from every entry state (`rp`, `ap`, `bp`,
    `n` in `%rdi`, `%rsi`, `%rdx`, `%rcx`) with `AddSep` (any `n < 2^64`; `rp` equal to, below,
    or disjoint from `ap` and `bp`), the machine halts with `rp'[j] = ap[j] &&& bp[j]` for
    `j < n`, `%rsp` and the callee-saved registers restored, and no byte written outside the
    80 frame bytes and the `n` words of `rp`. -/
theorem mpn_and_n_direct_correct :
    ∃ fd : Lfundef,
      (MpnLoopFrontEmit.andLprog ()).map (·.lp_funcs) = some [("mpn_and_n_loop_owned", fd)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes fd.lfd_body)
          = some (nodeLayout andDecPre andDecLoop andDecPost)
      ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
        AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n →
        ∃ s', Halts aMachine (nodeLayout andDecPre andDecLoop andDecPost) 0 s0 s'
          ∧ (∀ j, j < n → wordsOf s'.mem (s0.regs "%rdi") j
              = wordsOf s0.mem (s0.regs "%rsi") j &&& wordsOf s0.mem (s0.regs "%rdx") j)
          ∧ s'.regs "%rsp" = s0.regs "%rsp"
          ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
          ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s'.mem := by
  obtain ⟨fd, hf, hdec⟩ := andLprog_decode
  exact ⟨fd, hf, hdec, fun s0 n hc hS => bin_halts andOp_spec andDecLoop rfl andBody_eq s0 n hc hS⟩

/-- **The linked `mpn_xor_n_loop_owned`, for every count, in place.** As
    `mpn_and_n_direct_correct`, with `rp'[j] = ap[j] ^^^ bp[j]`. -/
theorem mpn_xor_n_direct_correct :
    ∃ fd : Lfundef,
      (MpnLoopFrontEmit.xorLprog ()).map (·.lp_funcs) = some [("mpn_xor_n_loop_owned", fd)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes fd.lfd_body)
          = some (nodeLayout xorDecPre xorDecLoop xorDecPost)
      ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
        AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n →
        ∃ s', Halts aMachine (nodeLayout xorDecPre xorDecLoop xorDecPost) 0 s0 s'
          ∧ (∀ j, j < n → wordsOf s'.mem (s0.regs "%rdi") j
              = wordsOf s0.mem (s0.regs "%rsi") j ^^^ wordsOf s0.mem (s0.regs "%rdx") j)
          ∧ s'.regs "%rsp" = s0.regs "%rsp"
          ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
          ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s'.mem := by
  obtain ⟨fd, hf, hdec⟩ := xorLprog_decode'
  refine ⟨fd, hf, hdec, fun s0 n hc hS => ?_⟩
  rw [xorPre_eq, xorPost_eq]
  exact bin_halts xorOp_spec xorDecLoop rfl xorBody_eq s0 n hc hS

/-- **The linked `mpn_ior_n_loop_owned`, for every count, in place.** As
    `mpn_and_n_direct_correct`, with `rp'[j] = ap[j] ||| bp[j]` (the shipped code computes
    `(a ^ b) ^ (a & b)`). -/
theorem mpn_ior_n_direct_correct :
    ∃ fd : Lfundef,
      (MpnLoopFrontEmit.iorLprog ()).map (·.lp_funcs) = some [("mpn_ior_n_loop_owned", fd)]
      ∧ decodeLprog (LprogBytes.encodeLfundefBytes fd.lfd_body)
          = some (nodeLayout iorDecPre iorDecLoop iorDecPost)
      ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
        AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n →
        ∃ s', Halts aMachine (nodeLayout iorDecPre iorDecLoop iorDecPost) 0 s0 s'
          ∧ (∀ j, j < n → wordsOf s'.mem (s0.regs "%rdi") j
              = wordsOf s0.mem (s0.regs "%rsi") j ||| wordsOf s0.mem (s0.regs "%rdx") j)
          ∧ s'.regs "%rsp" = s0.regs "%rsp"
          ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
          ∧ Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem s'.mem := by
  obtain ⟨fd, hf, hdec⟩ := iorLprog_decode'
  refine ⟨fd, hf, hdec, fun s0 n hc hS => ?_⟩
  rw [iorPre_eq, iorPost_eq]
  exact bin_halts iorOp_spec iorDecLoop rfl iorBody_eq s0 n hc hS

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinBytesDirect
