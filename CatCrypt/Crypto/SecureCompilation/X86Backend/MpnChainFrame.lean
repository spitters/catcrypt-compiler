/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry

@[expose] public section

set_option autoImplicit false

/-!
# The frame of the chain kernels

The `*_entry_correct` theorems of `MpnChainEntry` state the result words. This module adds
the frame of a run: the stack pointer and the callee-saved registers `%rbx`, `%rbp`,
`%r12`–`%r15` hold their entry values at the end, and every byte outside the frame bytes
below the entry stack pointer and outside the output words holds its entry value. The
proof conjoins a memory invariant (`FrameMem`) to the relations of the simulation of the
decoded node; only the stores of the prologue (into the frame) and the store of the loop
(into the output words) write memory.

## Main results

* `mpn_and_n_frame_correct`, `mpn_xor_n_frame_correct`, `mpn_ior_n_frame_correct`: the bitwise
  kernels halt with the result words and the frame preserved.
* `mpn_shift_rt_frame_correct`: the runtime shift kernel halts with the shifted value and the
  frame preserved.
* `mpn_cmp_ct_frame_correct`: the constant-time compare kernel halts with the comparison sign and
  the frame preserved.
* `and_linked`, `xor_linked`, `ior_linked`, `shift_linked`, `cmp_linked`: each kernel is the entry
  of the linked kernel table under its owned name.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainFrame

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)

/-! ## 1. Generic facts -/

/-- **A halting run has one final state.** -/
theorem haltsC_det {σ : Type} {M : Machine σ} {prog : List LprogBytesDecode.RInstr} {pc : Nat}
    {s s₁ s₂ : σ} (h₁ : HaltsC M prog pc s s₁) (h₂ : HaltsC M prog pc s s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | ret h =>
    cases h₂ with
    | ret _ => rfl
    | go hs _ => rw [RInstrSemantics.step, h] at hs; cases hs
    | call hc _ _ => rw [h] at hc; cases hc
  | go hs _ ih =>
    cases h₂ with
    | ret h => rw [RInstrSemantics.step, h] at hs; cases hs
    | go hs' hr' =>
      rw [hs] at hs'
      cases hs'
      exact ih hr'
    | call hc _ _ => rw [RInstrSemantics.step, hc] at hs; cases hs
  | call hc _ _ ihc ihr =>
    cases h₂ with
    | ret h => rw [h] at hc; cases hc
    | go hs _ => rw [RInstrSemantics.step, hc] at hs; cases hs
    | call hc' hcc' hr' =>
      rw [hc] at hc'
      cases hc'
      have := ihc hcc'
      subst this
      exact ihr hr'

/-- A machine-state predicate preserved by the machine block of a segment, under the
    segment's precondition, conjoined to both relations. -/
theorem DecSim.withF {I J : AState → LstateM → Bool → Prop} {ls : List LinstrRM}
    {js : List (JInstr 64)} (F : AState → Prop) (h : DecSim I J ls js)
    (hF : ∀ sa b zf, I sa b zf → F sa → F (aMachine.runBlock sa js)) :
    DecSim (fun sa b zf => I sa b zf ∧ F sa) (fun sa b zf => J sa b zf ∧ F sa) ls js :=
  fun sa b zf hi => by
    obtain ⟨b₁, z₁, hr, hj⟩ := h sa b zf hi.1
    exact ⟨b₁, z₁, hr, hj, hF sa b zf hi.1 hi.2⟩

/-- The frame bytes: `fsz` bytes from `rsp + flo`. -/
def InFr (rsp : BitVec 64) (flo : Int) (fsz : Nat) (x : BitVec 64) : Prop :=
  (x - (rsp + BitVec.ofInt 64 flo)).toNat < fsz

/-- The output bytes: the `n` words from `p`. -/
def InOut (p : BitVec 64) (n : Nat) (x : BitVec 64) : Prop :=
  ∃ j, j < n ∧ InRange8 (p + BitVec.ofNat 64 (8 * j)) x

/-- **The memory invariant.** The words `saved` at their offsets from `rsp`, and every byte
    outside the frame bytes and the output words as in `M0`. -/
structure FrameMem (M0 : AMem) (rsp : BitVec 64) (flo : Int) (fsz : Nat) (p : BitVec 64)
    (n : Nat) (saved : List (Int × BitVec 64)) (m : AMem) : Prop where
  saved : ∀ e ∈ saved, read64 m (rsp + BitVec.ofInt 64 e.1) = e.2
  outside : ∀ x, ¬ InFr rsp flo fsz x → ¬ InOut p n x → m x = M0 x

theorem disjoint8_comm {a b : BitVec 64} (h : Disjoint8 a b) : Disjoint8 b a := ⟨h.2, h.1⟩

/-- A store to an output word keeps the invariant when the word is disjoint from the saved
    words. -/
theorem FrameMem.store_out {M0 : AMem} {rsp : BitVec 64} {flo : Int} {fsz : Nat}
    {p : BitVec 64} {n : Nat} {saved : List (Int × BitVec 64)} {m : AMem}
    (h : FrameMem M0 rsp flo fsz p n saved m) (j : Nat) (hj : j < n) (v : BitVec 64)
    (hd : ∀ e ∈ saved, Disjoint8 (p + BitVec.ofNat 64 (8 * j)) (rsp + BitVec.ofInt 64 e.1)) :
    FrameMem M0 rsp flo fsz p n saved (write64 m (p + BitVec.ofNat 64 (8 * j)) v) where
  saved e he := by rw [read64_write64_of_disjoint _ _ _ _ (hd e he)]; exact h.saved e he
  outside x hx ho := by
    rw [write64_of_not_inRange _ _ _ _ (fun hr => ho ⟨j, hj, hr⟩)]
    exact h.outside x hx ho

/-- Two predicates, the second established by the machine block from the first under the
    segment's precondition. -/
theorem DecSim.withFG {I J : AState → LstateM → Bool → Prop} {ls : List LinstrRM}
    {js : List (JInstr 64)} (P Q : AState → Prop) (h : DecSim I J ls js)
    (hF : ∀ sa b zf, I sa b zf → P sa → Q (aMachine.runBlock sa js)) :
    DecSim (fun sa b zf => I sa b zf ∧ P sa) (fun sa b zf => J sa b zf ∧ Q sa) ls js :=
  fun sa b zf hi => by
    obtain ⟨b₁, z₁, hr, hj⟩ := h sa b zf hi.1
    exact ⟨b₁, z₁, hr, hj, hF sa b zf hi.1 hi.2⟩

theorem inFr_of_inRange (rsp x : BitVec 64) (flo o : Int) (fsz : Nat) (hlo : flo ≤ o)
    (hhi : o + 8 ≤ flo + fsz) (hfsz : fsz < 2 ^ 63) (hflo : -2 ^ 62 < flo) (ho : o < 2 ^ 62)
    (h : InRange8 (rsp + BitVec.ofInt 64 o) x) : InFr rsp flo fsz x := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, o = flo + d := ⟨(o - flo).toNat, by omega⟩
  subst hd
  have he : rsp + BitVec.ofInt 64 (flo + (d : Int))
      = (rsp + BitVec.ofInt 64 flo) + BitVec.ofNat 64 d := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  unfold InRange8 at h
  unfold InFr
  rw [he] at h
  generalize rsp + BitVec.ofInt 64 flo = A at h ⊢
  have hd8 : d + 8 ≤ fsz := by omega
  have hd64 : d < 2 ^ 64 := by omega
  bv_omega

/-- The callee-saved registers. -/
abbrev calleeSaved : List String := ["%rbx", "%rbp", "%r12", "%r13", "%r14", "%r15"]

/-! ## 2. `mpn_and_n_loop_owned` and its two siblings -/

section And

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm

variable (rp ap bp rsp : BitVec 64) (s0 : AState)

/-- The callee-saved words of the prologue: `%rbx` at `40`, …, `%r15` at `0`. -/
def andSaved : List (Int × BitVec 64) :=
  [(40, s0.regs "%rbx"), (32, s0.regs "%rbp"), (24, s0.regs "%r12"), (16, s0.regs "%r13"),
    (8, s0.regs "%r14"), (0, s0.regs "%r15")]

/-- The memory invariant of the bitwise kernels: frame bytes from `rsp - 16` to `rsp + 64`,
    output the `m` words at `rp`. -/
abbrev andF (m : Nat) (sa : AState) : Prop :=
  FrameMem s0.mem rsp (-16) 80 rp m (andSaved s0) sa.mem

theorem andSaved_disj (hstk : andStackSep rp ap bp rsp) (j : Nat) (hj : j < 4) :
    ∀ e ∈ andSaved s0, Disjoint8 (rp + BitVec.ofNat 64 (8 * j)) (rsp + BitVec.ofInt 64 e.1) := by
  have ha : (andLay rp ap bp).addr "a3" j = rp + BitVec.ofNat 64 (8 * j) := by
    simp (config := { decide := true }) [Layout.addr, andLay]
  intro e he
  simp only [andSaved, List.mem_cons, List.not_mem_nil, or_false] at he
  rw [← ha]
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact disjoint8_comm (hstk "a3" j ⟨Or.inl rfl, hj⟩ _ (by simp) (by simp))

/-- The store of a trip keeps the memory invariant, at any register map `π`, live set `L`
    and stored register `V`. -/
theorem and_store_F (π : String → String) (L : String → Prop) (V : String) (m t y : Nat)
    (htm : t < m) (hm : m ≤ 4) (hstk : andStackSep rp ap bp rsp) :
    ∀ sa b zf, (DecLsemCorr π L (andLay rp ap bp) (andFrame rsp) andK False sa b zf
        ∧ andPI rsp t y t sa) →
      andF rp rsp s0 m sa →
      andF rp rsp s0 m (aMachine.runBlock sa
        [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg V)]) := by
  intro sa b zf ⟨h, hp⟩ hF
  obtain ⟨a, ha, hra⟩ := h.slots "a3" "s0" (by simp (config := { decide := true }) [andLay])
  have ha' : a = rsp + BitVec.ofInt 64 56 := by
    simp (config := { decide := true }) [andFrame] at ha
    exact ha.symm
  have hbase : (andLay rp ap bp).base "a3" = rp := by
    simp (config := { decide := true }) [andLay]
  have hr14 : read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 56) = rp := by
    rw [hp.1.1, ← ha', hra, hbase]
  have hmem : (aMachine.runBlock sa
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg V)]).mem
      = write64 sa.mem (rp + BitVec.ofNat 64 (8 * t))
          ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs V) := by
    show write64 sa.mem ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs "%r14"
      + BitVec.ofInt 64 ((8 * ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs "%rsi").toNat
        : Nat) : Int)) ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs V) = _
    rw [evalInstrA_loadMem_regs, hr14,
      evalInstrA_regs_of_not_mem_dsts _ _ "%rsi" (by decide +kernel), hp.2,
      ofNat_toNat_lt t (by omega), BitVec.ofInt_natCast]
  show FrameMem _ _ _ _ _ _ _ (aMachine.runBlock sa _).mem
  rw [hmem]
  exact hF.store_out t htm _ (andSaved_disj rp ap bp rsp s0 hstk t (by omega))

/-- **One trip with the memory invariant.** -/
theorem and_tripF (m : Nat) (hm : m ≤ 4) (hsep : (andLay rp ap bp).Sep (andFrame rsp))
    (hdis : andDis rp ap bp) (hstk : andStackSep rp ap bp rsp) (t : Nat) (ht : t < m) :
    DecSim (fun sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)) sa b zf
        ∧ andF rp rsp s0 m sa)
      (fun sa b zf => andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf
        ∧ andF rp rsp s0 m sa)
      (andLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (andDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (DecSim.withF _ (and_seg_idx rp ap bp rsp t (m - t) False) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_load1 rp ap bp rsp t (m - t) (by omega))
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_load0 rp ap bp rsp t (m - t) (by omega))
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_and rp ap bp rsp t (m - t)) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_store rp ap bp rsp t (m - t) (by omega) hsep hdis)
    (and_store_F rp ap bp rsp s0 andPi andLiveD "%rbp" m t (m - t) ht hm hstk)).append <|
  DecSim.withF _ (and_seg_tail rp ap bp rsp m t ht) (fun _ _ _ _ h => h)

/-- The prologue writes only frame words, and saves the callee-saved registers. -/
theorem and_pre_F (m : Nat) :
    ∀ sa b zf, (DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b zf
        ∧ andEntry rp ap bp rsp m sa) → sa = s0 →
      andF rp rsp s0 m (aMachine.runBlock sa andDecPre) := by
  rintro sa b zf ⟨-, hrsp, -⟩ rfl
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emo : ∀ (s : AState) (X : String) (o : JOperand), (evalInstrA s (.mov X o)).mem
      = s.mem := fun _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elem : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int),
      (evalInstrA s (.lea D B I sc o)).mem = s.mem := fun _ _ _ _ _ _ => rfl
  have hlea : sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (-64)
      = rsp := by
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero, BitVec.add_assoc,
      show BitVec.ofInt 64 64 + BitVec.ofInt 64 (-64) = 0#64 by decide +kernel, BitVec.add_zero]
  show FrameMem _ _ _ _ _ _ _ (aMachine.runBlock sa andDecPre).mem
  simp only [andDecPre_eq, andPre15, List.cons_append, List.nil_append, Machine.runBlock_cons,
    Machine.runBlock_nil, aMachine_exec]
  simp (config := { decide := true }) only [em, emo, es, esm, elm, ele, elem,
    ite_true, ite_false, hlea]
  refine ⟨fun e he => ?_, fun x hx _ => ?_⟩
  · simp only [andSaved, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
  · have hn : ∀ o : Int, -16 ≤ o → o ≤ 56 → ∀ (M : AMem) (v : BitVec 64),
        write64 M (rsp + BitVec.ofInt 64 o) v x = M x := fun o h1 h2 M v =>
      write64_of_not_inRange _ _ _ _ (fun hr => hx (inFr_of_inRange rsp x (-16) o 80 h1
        (by omega) (by norm_num) (by norm_num) (by omega) hr))
    simp only [hn 56 (by norm_num) (by norm_num), hn 48 (by norm_num) (by norm_num),
      hn 40 (by norm_num) (by norm_num), hn 32 (by norm_num) (by norm_num),
      hn 24 (by norm_num) (by norm_num), hn 16 (by norm_num) (by norm_num),
      hn 8 (by norm_num) (by norm_num), hn 0 (by norm_num) (by norm_num),
      hn (-8) (by norm_num) (by norm_num), hn (-16) (by norm_num) (by norm_num)]

/-- The exit condition with the frame: the result as in `andOut`, the stack pointer `64`
    above the body's, the callee-saved registers of `s0`, and the memory of `s0` outside the
    frame bytes and the output words. -/
def andOutF (m : Nat) (sa : AState) (b : LstateM) : Prop :=
  andOut rp ap bp sa b ∧ sa.regs "%rsp" = rsp + BitVec.ofInt 64 64
    ∧ (∀ R ∈ calleeSaved, sa.regs R = s0.regs R)
    ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp m x → sa.mem x = s0.mem x

/-- **The epilogue with the frame.** -/
theorem and_postF (m : Nat) :
    ∀ sa b, (andRel rp ap bp rsp andLive andK False (andP rsp m (m - m)) sa b true
        ∧ andF rp rsp s0 m sa) →
      andOutF rp ap bp rsp s0 m (aMachine.runBlock sa andDecPost) b := by
  intro sa b ⟨hr, hF⟩
  have hrsp : sa.regs "%rsp" = rsp := hr.2.1
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have hsv : ∀ (o : Int) (v : BitVec 64), (o, v) ∈ andSaved s0 →
      read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 o) = v := fun o v h => by
    rw [hrsp]; exact hF.saved (o, v) h
  refine ⟨and_post rp ap bp rsp m sa b hr, ?_, ?_, fun x hx ho => ?_⟩
  · simp only [andDecPost, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    simp (config := { decide := true }) only [ele, evalInstrA_loadMem_regs', elm, ite_true,
      ite_false]
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero]
  · intro R hR
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hR
    simp only [andDecPost, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [ele, evalInstrA_loadMem_regs', elm, ite_true,
      ite_false] <;>
    exact hsv _ _ (by simp [andSaved])
  · exact hF.outside x hx ho

/-- **The node of a bitwise kernel with the frame**, for any looped segment `body` and decoded
    loop `l` with counter `%rdi` whose trips keep the memory invariant. -/
theorem bin_node_frame (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hstk : andStackSep rp ap bp rsp) (body : List LinstrRM) (l : XLoop 64)
    (hcmp : l.cmpInstr = JInstr.cmp "%rdi" (.imm 0)) (hbody : ∀ i ∈ body, IsLopn i)
    (htop : findLabelMem 4 ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
      ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" body) = some (3 + 2))
    (hend : findLabelMem (4 + 0x40000000) ([movRI "a3" "a3", movII "Lidx4" 0,
      movRI "Lctr4" "a2"] ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" body)
      = some (3 + body.length + 5))
    (s0 : AState)
    (hsim : ∀ t, t < m →
      DecSim (fun sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)) sa b zf
          ∧ andF rp rsp s0 m sa)
        (fun sa b zf => andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf
          ∧ andF rp rsp s0 m sa)
        (body ++ [cmpRI "Lctr4" (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (fn : String) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False s0 b zf
      ∧ andEntry rp ap bp rsp m s0) :
    ∃ sa', Halts aMachine (nodeLayout andDecPre l andDecPost) 0 s0 sa'
      ∧ sa'.regs "%rsp" = rsp + BitVec.ofInt 64 64
      ∧ (∀ R ∈ calleeSaved, sa'.regs R = s0.regs R)
      ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp m x → sa'.mem x = s0.mem x := by
  have hg : DecSim (fun sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp 0 m) sa b zf
        ∧ andF rp rsp s0 m sa)
      (fun sa b zf => andG rp ap bp rsp m sa b zf ∧ andF rp rsp s0 m sa)
      [cmpRI "Lctr4" (.imm 0)] [l.cmpInstr] := by
    rw [hcmp]
    exact DecSim.withF _ (and_guard rp ap bp rsp m False) (fun _ _ _ _ h => h)
  obtain ⟨sa', t, k, hh, -, -, h2, h3, h4⟩ := decNode_halts fn
    [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"] body 4 (4 + 0x40000000)
    "Lctr4" l m
    (fun sa b zf => (DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False
      sa b zf ∧ andEntry rp ap bp rsp m sa) ∧ sa = s0)
    (fun sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp 0 m) sa b zf
      ∧ andF rp rsp s0 m sa)
    (fun sa b zf => andG rp ap bp rsp m sa b zf ∧ andF rp rsp s0 m sa)
    (fun t sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)) sa b zf
      ∧ andF rp rsp s0 m sa)
    (fun t sa b zf => andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf
      ∧ andF rp rsp s0 m sa)
    (andOutF rp ap bp rsp s0 m)
    andDecPre andDecPost andSeeds_isLopn hbody htop hend
    (DecSim.withFG _ _ (and_pre rp ap bp rsp m False hstk) (and_pre_F rp ap bp rsp s0 m))
    hg
    (fun sa b zf h => and_guard_flag rp ap bp rsp m hm sa b zf h.1)
    (fun sa b zf pc h => ⟨and_guard_inv rp ap bp rsp m sa b zf pc h.1, h.2⟩)
    hsim
    (fun t ht sa b zf h => and_trip_flag rp ap bp rsp m hm t ht sa b zf h.1)
    (fun t ht sa b zf pc h => ⟨and_trip_next rp ap bp rsp m t ht sa b zf pc h.1, h.2⟩)
    (and_postF rp ap bp rsp s0 m) s0 b zf hpc ⟨hE, rfl⟩
  exact ⟨sa', hh, h2, h3, h4⟩

theorem and_node_frame (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp) (fn : String) (s0 : AState) (b : LstateM) (zf : Bool)
    (hpc : b.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False s0 b zf
      ∧ andEntry rp ap bp rsp m s0) :
    ∃ sa', Halts aMachine (nodeLayout andDecPre andDecLoop andDecPost) 0 s0 sa'
      ∧ sa'.regs "%rsp" = rsp + BitVec.ofInt 64 64
      ∧ (∀ R ∈ calleeSaved, sa'.regs R = s0.regs R)
      ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp m x → sa'.mem x = s0.mem x :=
  bin_node_frame rp ap bp rsp m hm hstk andLoopBodyLit andDecLoop rfl andLoopBody_isLopn
    andNode_top andNode_end s0 (fun t ht => and_tripF rp ap bp rsp s0 m hm hsep hdis hstk t ht)
    fn b zf hpc hE

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry
  (wd andB0 andB0_corr entryM_lpc mpn_and_n_entry_correct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)

/-- **`mpn_and_n_loop_owned` with its frame.** The linked program is one function whose
    function bytes decode to the node layout; from every machine entry state as in
    `mpn_and_n_entry_correct` the machine halts with `ap[j] &&& bp[j]` at `rp + 8 j` for
    `j < m`, the stack pointer and the callee-saved registers `%rbx`, `%rbp`, `%r12`–`%r15`
    as at the entry, and every byte outside the `80` frame bytes below the entry stack
    pointer (from `rsp - 16`, `rsp` the body's stack pointer) and outside the `m` output
    words as at the entry. -/
theorem mpn_and_n_frame_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.andLprog ()).map (·.lp_funcs) = some [("mpn_and_n_loop_owned", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout andDecPre andDecLoop andDecPost)
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ sa : AState, andEntry rp ap bp rsp m sa →
        ∃ sa', Halts aMachine (nodeLayout andDecPre andDecLoop andDecPost) 0 sa sa'
          ∧ (∀ j, j < m → wd sa' rp j = wd sa ap j &&& wd sa bp j)
          ∧ sa'.regs "%rsp" = sa.regs "%rsp"
          ∧ (∀ R ∈ calleeSaved, sa'.regs R = sa.regs R)
          ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp m x → sa'.mem x = sa.mem x := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_and_n_entry_correct
  obtain ⟨f', hf', hdec'⟩ := andLprog_decode
  rw [hf] at hf'
  obtain rfl : f = f' := by simpa using hf'
  rw [hdec] at hdec'
  obtain rfl := Option.some.inj hdec'
  refine ⟨f, hf, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa hE => ?_⟩
  obtain ⟨sa1, hh1, hw⟩ := H rp ap bp rsp m hm hsep hdis hstk sa hE
  obtain ⟨sa2, hh2, hr, hc, hmem⟩ := and_node_frame rp ap bp rsp m hm hsep hdis hstk
    "mpn_and_n_loop_owned" sa (andB0 sa) false entryM_lpc
    ⟨andB0_corr rp ap bp rsp m sa hE false, hE⟩
  obtain rfl := haltsC_det hh1 hh2
  exact ⟨sa1, hh1, hw, hr.trans hE.1.symm, hc, hmem⟩

end And

/-! ## 3. `mpn_xor_n_loop_owned` and `mpn_ior_n_loop_owned` -/

section XorIor

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnXorBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnIorBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry
  (wd andB0 andB0_corr entryM_lpc mpn_xor_n_entry_correct mpn_ior_n_entry_correct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)

variable (rp ap bp rsp : BitVec 64) (s0 : AState)

theorem xor_tripF (m : Nat) (hm : m ≤ 4) (hsep : (andLay rp ap bp).Sep (andFrame rsp))
    (hdis : andDis rp ap bp) (hstk : andStackSep rp ap bp rsp) (t : Nat) (ht : t < m) :
    DecSim (fun sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)) sa b zf
        ∧ andF rp rsp s0 m sa)
      (fun sa b zf => andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf
        ∧ andF rp rsp s0 m sa)
      (xorLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (xorDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (DecSim.withF _ (and_seg_idx rp ap bp rsp t (m - t) False) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_load1 rp ap bp rsp t (m - t) (by omega))
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_load0 rp ap bp rsp t (m - t) (by omega))
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (xor_seg_op rp ap bp rsp t (m - t)) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_store rp ap bp rsp t (m - t) (by omega) hsep hdis)
    (and_store_F rp ap bp rsp s0 andPi andLiveD "%rbp" m t (m - t) ht hm hstk)).append <|
  DecSim.withF _ (and_seg_tail rp ap bp rsp m t ht) (fun _ _ _ _ h => h)

theorem ior_tripF (m : Nat) (hm : m ≤ 4) (hsep : (andLay rp ap bp).Sep (andFrame rsp))
    (hdis : andDis rp ap bp) (hstk : andStackSep rp ap bp rsp) (t : Nat) (ht : t < m) :
    DecSim (fun sa b zf => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)) sa b zf
        ∧ andF rp rsp s0 m sa)
      (fun sa b zf => andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf
        ∧ andF rp rsp s0 m sa)
      (iorLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (iorDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (DecSim.withF _ (and_seg_idx rp ap bp rsp t (m - t) False) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_load1 rp ap bp rsp t (m - t) (by omega))
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (and_seg_load0 rp ap bp rsp t (m - t) (by omega))
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (ior_seg_op rp ap bp rsp t (m - t)) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (ior_seg_store rp ap bp rsp t (m - t) (by omega) hsep hdis)
    (and_store_F rp ap bp rsp s0 iorPi iorLiveD "%r8" m t (m - t) ht hm hstk)).append <|
  DecSim.withF _ (ior_seg_tail rp ap bp rsp m t ht) (fun _ _ _ _ h => h)

/-- **`mpn_xor_n_loop_owned` with its frame**, as `mpn_and_n_frame_correct`. -/
theorem mpn_xor_n_frame_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.xorLprog ()).map (·.lp_funcs) = some [("mpn_xor_n_loop_owned", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout xorDecPre xorDecLoop xorDecPost)
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ sa : AState, andEntry rp ap bp rsp m sa →
        ∃ sa', Halts aMachine (nodeLayout xorDecPre xorDecLoop xorDecPost) 0 sa sa'
          ∧ (∀ j, j < m → wd sa' rp j = wd sa ap j ^^^ wd sa bp j)
          ∧ sa'.regs "%rsp" = sa.regs "%rsp"
          ∧ (∀ R ∈ calleeSaved, sa'.regs R = sa.regs R)
          ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp m x → sa'.mem x = sa.mem x := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_xor_n_entry_correct
  obtain ⟨f', hf', hdec'⟩ : ∃ f : Lfundef,
      (MpnLoopFrontEmit.xorLprog ()).map (·.lp_funcs) = some [("mpn_xor_n_loop_owned", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout xorDecPre xorDecLoop xorDecPost) :=
    ⟨_, by rw [MpnBinExportTerm.xorLprog_eq]; rfl,
      by rw [MpnBinExportTerm.xorPhysAbi_eq]; exact MpnBinExportTerm.xorPhysLit_decode⟩
  rw [hf] at hf'
  obtain rfl : f = f' := by simpa using hf'
  rw [hdec] at hdec'
  obtain rfl := Option.some.inj hdec'
  refine ⟨f, hf, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa hE => ?_⟩
  obtain ⟨sa1, hh1, hw⟩ := H rp ap bp rsp m hm hsep hdis hstk sa hE
  obtain ⟨sa2, hh2, hr, hc, hmem⟩ := bin_node_frame rp ap bp rsp m hm hstk xorLoopBodyLit
    xorDecLoop rfl xorLoopBody_isLopn xorNode_top xorNode_end sa
    (fun t ht => xor_tripF rp ap bp rsp sa m hm hsep hdis hstk t ht)
    "mpn_xor_n_loop_owned" (andB0 sa) false entryM_lpc
    ⟨andB0_corr rp ap bp rsp m sa hE false, hE⟩
  obtain rfl := haltsC_det hh1 hh2
  exact ⟨sa1, hh1, hw, hr.trans hE.1.symm, hc, hmem⟩

/-- **`mpn_ior_n_loop_owned` with its frame**, as `mpn_and_n_frame_correct`. -/
theorem mpn_ior_n_frame_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.iorLprog ()).map (·.lp_funcs) = some [("mpn_ior_n_loop_owned", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout iorDecPre iorDecLoop iorDecPost)
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ sa : AState, andEntry rp ap bp rsp m sa →
        ∃ sa', Halts aMachine (nodeLayout iorDecPre iorDecLoop iorDecPost) 0 sa sa'
          ∧ (∀ j, j < m → wd sa' rp j = wd sa ap j ||| wd sa bp j)
          ∧ sa'.regs "%rsp" = sa.regs "%rsp"
          ∧ (∀ R ∈ calleeSaved, sa'.regs R = sa.regs R)
          ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp m x → sa'.mem x = sa.mem x := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_ior_n_entry_correct
  obtain ⟨f', hf', hdec'⟩ : ∃ f : Lfundef,
      (MpnLoopFrontEmit.iorLprog ()).map (·.lp_funcs) = some [("mpn_ior_n_loop_owned", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout iorDecPre iorDecLoop iorDecPost) :=
    ⟨_, by rw [MpnBinExportTerm.iorLprog_eq]; rfl,
      by rw [MpnBinExportTerm.iorPhysAbi_eq]; exact MpnBinExportTerm.iorPhysLit_decode⟩
  rw [hf] at hf'
  obtain rfl : f = f' := by simpa using hf'
  rw [hdec] at hdec'
  obtain rfl := Option.some.inj hdec'
  refine ⟨f, hf, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa hE => ?_⟩
  obtain ⟨sa1, hh1, hw⟩ := H rp ap bp rsp m hm hsep hdis hstk sa hE
  obtain ⟨sa2, hh2, hr, hc, hmem⟩ := bin_node_frame rp ap bp rsp m hm hstk iorLoopBodyLit
    iorDecLoop rfl iorLoopBody_isLopn iorNode_top iorNode_end sa
    (fun t ht => ior_tripF rp ap bp rsp sa m hm hsep hdis hstk t ht)
    "mpn_ior_n_loop_owned" (andB0 sa) false entryM_lpc
    ⟨andB0_corr rp ap bp rsp m sa hE false, hE⟩
  obtain rfl := haltsC_det hh1 hh2
  exact ⟨sa1, hh1, hw, hr.trans hE.1.symm, hc, hmem⟩

end XorIor

/-! ## 4. The common prologue and epilogue -/

section Common

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm

/-- **The fifteen-instruction prologue** writes only the `80` frame bytes from `rsp - 16`
    and saves the callee-saved registers at `40`, …, `0`. -/
theorem pre15_F (rp rsp : BitVec 64) (n : Nat) (sa : AState)
    (hrsp : sa.regs "%rsp" = rsp + BitVec.ofInt 64 64) :
    FrameMem sa.mem rsp (-16) 80 rp n (andSaved sa) (aMachine.runBlock sa andPre15).mem := by
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emo : ∀ (s : AState) (X : String) (o : JOperand), (evalInstrA s (.mov X o)).mem
      = s.mem := fun _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elem : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int),
      (evalInstrA s (.lea D B I sc o)).mem = s.mem := fun _ _ _ _ _ _ => rfl
  have hlea : sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (-64)
      = rsp := by
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero, BitVec.add_assoc,
      show BitVec.ofInt 64 64 + BitVec.ofInt 64 (-64) = 0#64 by decide +kernel, BitVec.add_zero]
  simp only [andPre15, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
  simp (config := { decide := true }) only [em, emo, es, esm, elm, ele, elem,
    ite_true, ite_false, hlea]
  refine ⟨fun e he => ?_, fun x hx _ => ?_⟩
  · simp only [andSaved, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
  · have hn : ∀ o : Int, -16 ≤ o → o ≤ 56 → ∀ (M : AMem) (v : BitVec 64),
        write64 M (rsp + BitVec.ofInt 64 o) v x = M x := fun o h1 h2 M v =>
      write64_of_not_inRange _ _ _ _ (fun hr => hx (inFr_of_inRange rsp x (-16) o 80 h1
        (by omega) (by norm_num) (by norm_num) (by omega) hr))
    simp only [hn 56 (by norm_num) (by norm_num), hn 48 (by norm_num) (by norm_num),
      hn 40 (by norm_num) (by norm_num), hn 32 (by norm_num) (by norm_num),
      hn 24 (by norm_num) (by norm_num), hn 16 (by norm_num) (by norm_num),
      hn 8 (by norm_num) (by norm_num), hn 0 (by norm_num) (by norm_num),
      hn (-8) (by norm_num) (by norm_num), hn (-16) (by norm_num) (by norm_num)]

/-- **The common epilogue** restores the callee-saved registers from the saved words, sets
    the stack pointer `64` above `rsp`, and writes no memory. -/
theorem post_frame (rsp p : BitVec 64) (n : Nat) (M0 : AMem) (s0 sa : AState)
    (hrsp : sa.regs "%rsp" = rsp) (hF : FrameMem M0 rsp (-16) 80 p n (andSaved s0) sa.mem) :
    (aMachine.runBlock sa andDecPost).regs "%rsp" = rsp + BitVec.ofInt 64 64
      ∧ (∀ R ∈ calleeSaved, (aMachine.runBlock sa andDecPost).regs R = s0.regs R)
      ∧ (aMachine.runBlock sa andDecPost).mem = sa.mem := by
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have hsv : ∀ (o : Int) (v : BitVec 64), (o, v) ∈ andSaved s0 →
      read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 o) = v := fun o v h => by
    rw [hrsp]; exact hF.saved (o, v) h
  refine ⟨?_, fun R hR => ?_, rfl⟩
  · simp only [andDecPost, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    simp (config := { decide := true }) only [ele, evalInstrA_loadMem_regs', elm, ite_true,
      ite_false]
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hR
    simp only [andDecPost, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [ele, evalInstrA_loadMem_regs', elm, ite_true,
      ite_false] <;>
    exact hsv _ _ (by simp [andSaved])

end Common

/-! ## 5. `mpn_shift_rt` -/

section Shift

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue (andSeeds_isLopn andPre15)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm (andDecPost)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry
  (wd shiftB0 shiftB0_corr entryM_lpc mpn_shift_rt_entry_correct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)

variable (rp up rsp : BitVec 64) (s0 : AState)

/-- The memory invariant of the shift: output the `m + 1` words at `rp`. -/
abbrev shiftF (m : Nat) (sa : AState) : Prop :=
  FrameMem s0.mem rsp (-16) 80 rp (m + 1) (andSaved s0) sa.mem

/-- A store of the shift trip, to the output word `j ≤ m` indexed by `I`, keeps the memory
    invariant. -/
theorem shift_store_F (L : String → Prop) (P : AState → Prop) (I V : String) (m j : Nat)
    (hjm : j < m + 1) (hm : m ≤ 8) (hstk : shiftStackSep rp up rsp)
    (hP : ∀ sa, P sa → sa.regs "%rsp" = rsp ∧ sa.regs I = BitVec.ofNat 64 j)
    (hI : I ∉ dsts (.loadMem "%r14" "%rsp" 56)) :
    ∀ sa b zf, (DecLsemCorr shiftPi L (shiftLay rp up) (shiftFrame rsp) shiftK False sa b zf
        ∧ P sa) →
      shiftF rp rsp s0 m sa →
      shiftF rp rsp s0 m (aMachine.runBlock sa
        [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" I 8 (.reg V)]) := by
  intro sa b zf ⟨h, hp⟩ hF
  obtain ⟨hrsp, hIv⟩ := hP sa hp
  obtain ⟨a, ha, hra⟩ := h.slots "a3" "s0" (by simp (config := { decide := true }) [shiftLay])
  have ha' : a = rsp + BitVec.ofInt 64 56 := by
    simp (config := { decide := true }) [shiftFrame] at ha
    exact ha.symm
  have hbase : (shiftLay rp up).base "a3" = rp := by
    simp (config := { decide := true }) [shiftLay]
  have hr14 : read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 56) = rp := by
    rw [hrsp, ← ha', hra, hbase]
  have hmem : (aMachine.runBlock sa
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" I 8 (.reg V)]).mem
      = write64 sa.mem (rp + BitVec.ofNat 64 (8 * j))
          ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs V) := by
    show write64 sa.mem ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs "%r14"
      + BitVec.ofInt 64 ((8 * ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs I).toNat
        : Nat) : Int)) ((evalInstrA sa (.loadMem "%r14" "%rsp" 56)).regs V) = _
    rw [evalInstrA_loadMem_regs, hr14, evalInstrA_regs_of_not_mem_dsts _ _ I hI, hIv,
      ofNat_toNat_lt j (by omega), BitVec.ofInt_natCast]
  show FrameMem _ _ _ _ _ _ _ (aMachine.runBlock sa _).mem
  rw [hmem]
  refine hF.store_out j hjm _ ?_
  have hadd : (shiftLay rp up).addr "a3" j = rp + BitVec.ofNat 64 (8 * j) := by
    simp (config := { decide := true }) [Layout.addr, shiftLay]
  intro e he
  simp only [andSaved, List.mem_cons, List.not_mem_nil, or_false] at he
  rw [← hadd]
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact disjoint8_comm (hstk "a3" j (Or.inl ⟨rfl, by omega⟩) _ (by simp) (by simp))

theorem shift_tripF (m : Nat) (hm : m ≤ 8) (hsep : (shiftLay rp up).Sep (shiftFrame rsp))
    (hdis : shiftDis rp up) (hstk : shiftStackSep rp up rsp) (t : Nat) (ht : t < m) :
    DecSim (fun sa b zf => shiftRel rp up rsp shLive shiftK False (shiftP rsp t (m - t)) sa b zf
        ∧ shiftF rp rsp s0 m sa)
      (fun sa b zf => shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t) sa b zf
        ∧ shiftF rp rsp s0 m sa)
      (shiftLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
      (shiftDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (DecSim.withF _ (shift_seg_load3 rp up rsp t (m - t) (by omega) False)
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (shift_seg_load1 rp up rsp t (m - t) (by omega) False)
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (shift_seg_funnel rp up rsp t (m - t) False) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (shift_seg_store0 rp up rsp t (m - t) (by omega) hsep hdis)
    (shift_store_F rp up rsp s0 shLiveC (shiftP rsp t (m - t)) "%rax" "%rdx" m t (by omega) hm
      hstk (fun _ hp => ⟨hp.1, hp.2.1⟩) (by decide +kernel))).append <|
  (DecSim.withF _ (shift_seg_idx1 rp up rsp t (m - t)) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (shift_seg_store1 rp up rsp t (m - t) (by omega) hsep hdis)
    (shift_store_F rp up rsp s0 shLiveD _ "%rdx" "%rbp" m (t + 1) (by omega) hm
      hstk (fun _ hp => ⟨hp.1.1, hp.2⟩) (by decide +kernel))).append <|
  DecSim.withF _ (shift_seg_tail rp up rsp m t ht) (fun _ _ _ _ h => h)

/-- **The shift node with the frame.** -/
theorem shift_node_frame (m : Nat) (hm : m ≤ 8) (hsep : (shiftLay rp up).Sep (shiftFrame rsp))
    (hdis : shiftDis rp up) (hstk : shiftStackSep rp up rsp) (fn : String) (b : LstateM)
    (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp up) (fun _ => none) shiftK False s0 b zf
      ∧ shiftEntry rp up rsp m s0) :
    ∃ sa', Halts aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 s0 sa'
      ∧ sa'.regs "%rsp" = rsp + BitVec.ofInt 64 64
      ∧ (∀ R ∈ calleeSaved, sa'.regs R = s0.regs R)
      ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp (m + 1) x → sa'.mem x = s0.mem x := by
  obtain ⟨sa', t, k, hh, -, h2, h3, h4⟩ := decNode_halts fn
    [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"] shiftLoopBodyLit 4 (4 + 0x40000000)
    "Lctr4" shiftDecLoop m
    (fun sa b zf => (DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp up) (fun _ => none) shiftK
      False sa b zf ∧ shiftEntry rp up rsp m sa) ∧ sa = s0)
    (fun sa b zf => shiftRel rp up rsp shLive shiftK False (shiftP rsp 0 m) sa b zf
      ∧ shiftF rp rsp s0 m sa)
    (fun sa b zf => shiftG rp up rsp m sa b zf ∧ shiftF rp rsp s0 m sa)
    (fun t sa b zf => shiftRel rp up rsp shLive shiftK False (shiftP rsp t (m - t)) sa b zf
      ∧ shiftF rp rsp s0 m sa)
    (fun t sa b zf => shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t) sa b zf
      ∧ shiftF rp rsp s0 m sa)
    (fun sa _ => sa.regs "%rsp" = rsp + BitVec.ofInt 64 64
      ∧ (∀ R ∈ calleeSaved, sa.regs R = s0.regs R)
      ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp (m + 1) x → sa.mem x = s0.mem x)
    shiftDecPre shiftDecPost andSeeds_isLopn shiftLoopBody_isLopn shiftNode_top shiftNode_end
    (DecSim.withFG _ _ (shift_pre rp up rsp m False hstk) (fun sa _ _ h hs => by
      subst hs
      have hs3 : ∀ s : AState, (aMachine.runBlock s [.mov "%rbx" (.reg "%rbx"),
          .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rdx")]).mem = s.mem := fun _ => rfl
      show FrameMem _ _ _ _ _ _ _ (aMachine.runBlock sa shiftDecPre).mem
      rw [shiftDecPre_eq, Machine.runBlock_append, hs3]
      exact pre15_F rp rsp (m + 1) sa h.2.1))
    (DecSim.withF _ (shift_guard rp up rsp m False) (fun _ _ _ _ h => h))
    (fun sa b zf h => shift_guard_flag rp up rsp m hm sa b zf h.1)
    (fun sa b zf pc h => ⟨shift_guard_inv rp up rsp m sa b zf pc h.1, h.2⟩)
    (fun t ht => shift_tripF rp up rsp s0 m hm hsep hdis hstk t ht)
    (fun t ht sa b zf h => shift_trip_flag rp up rsp m hm t ht sa b zf h.1)
    (fun t ht sa b zf pc h => ⟨shift_trip_next rp up rsp m t ht sa b zf pc h.1, h.2⟩)
    (fun sa b ⟨hr, hF⟩ => by
      rw [show shiftDecPost = andDecPost from rfl]
      obtain ⟨h1, h2, h3⟩ := post_frame rsp rp (m + 1) s0.mem s0 sa hr.2.1 hF
      exact ⟨h1, h2, fun x hx ho => by rw [h3]; exact hF.outside x hx ho⟩)
    s0 b zf hpc ⟨hE, rfl⟩
  exact ⟨sa', hh, h2, h3, h4⟩

/-- **`mpn_shift_rt` with its frame.** The result of `mpn_shift_rt_entry_correct`, the stack
    pointer and the callee-saved registers as at the entry, and every byte outside the `80`
    frame bytes from `rsp - 16` and the `m + 1` output words as at the entry. -/
theorem mpn_shift_rt_frame_correct :
    ∃ f : Lfundef,
      (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt").map (·.lp_funcs)
        = some [("mpn_shift_rt", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout shiftDecPre shiftDecLoop shiftDecPost)
      ∧ ∀ (rp upp rsp : BitVec 64) (m : Nat), m ≤ 8 →
        (shiftLay rp upp).Sep (shiftFrame rsp) → shiftDis rp upp → shiftStackSep rp upp rsp →
        ∀ sa : AState, shiftEntry rp upp rsp m sa →
        0 < (sa.regs "%rcx").toNat ∧ (sa.regs "%rcx").toNat < 64 →
        (wd sa rp 0).toNat < 2 ^ (sa.regs "%rcx").toNat →
        ∃ sa', Halts aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 sa sa'
          ∧ bignumVal ((List.range (m + 1)).map (wd sa' rp))
            = bignumVal ((List.range m).map (wd sa upp)) * 2 ^ (sa.regs "%rcx").toNat
              + (wd sa rp 0).toNat
          ∧ sa'.regs "%rsp" = sa.regs "%rsp"
          ∧ (∀ R ∈ calleeSaved, sa'.regs R = sa.regs R)
          ∧ ∀ x, ¬ InFr rsp (-16) 80 x → ¬ InOut rp (m + 1) x → sa'.mem x = sa.mem x := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_shift_rt_entry_correct
  obtain ⟨f', hf', hdec'⟩ : ∃ f : Lfundef,
      (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt").map (·.lp_funcs)
        = some [("mpn_shift_rt", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) :=
    ⟨_, by rw [MpnRtExportTerm.shiftLprog_eq]; rfl,
      by rw [MpnRtExportTerm.shiftPhysAbi_eq]; exact MpnRtExportTerm.shiftPhysLit_decode⟩
  rw [hf] at hf'
  obtain rfl : f = f' := by simpa using hf'
  rw [hdec] at hdec'
  obtain rfl := Option.some.inj hdec'
  refine ⟨f, hf, hdec, fun rp upp rsp m hm hsep hdis hstk sa hE hsh h0 => ?_⟩
  obtain ⟨sa1, hh1, hw⟩ := H rp upp rsp m hm hsep hdis hstk sa hE hsh h0
  obtain ⟨sa2, hh2, hr, hc, hmem⟩ := shift_node_frame rp upp rsp sa m hm hsep hdis hstk
    "mpn_shift_rt" (shiftB0 sa) false entryM_lpc ⟨shiftB0_corr rp upp rsp m sa hE false, hE⟩
  obtain rfl := haltsC_det hh1 hh2
  exact ⟨sa1, hh1, hw, hr.trans hE.1.symm, hc, hmem⟩

end Shift

/-! ## 6. `mpn_cmp_ct` -/

section Cmp

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry
  (wd cmpB0 cmpB0_corr entryM_lpc mpn_cmp_ct_entry_correct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit (cmpSign)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)

variable (rp ap bp rsp : BitVec 64) (s0 : AState)

/-- The callee-saved words of the compare's prologue: `%rbx` at `56`, …, `%r15` at `16`. -/
def cmpSaved : List (Int × BitVec 64) :=
  [(56, s0.regs "%rbx"), (48, s0.regs "%rbp"), (40, s0.regs "%r12"), (32, s0.regs "%r13"),
    (24, s0.regs "%r14"), (16, s0.regs "%r15")]

/-- The memory invariant of the compare: frame bytes from `rsp - 16` to `rsp + 80`, output
    the word at `rp`. -/
abbrev cmpF (sa : AState) : Prop :=
  FrameMem s0.mem rsp (-16) 96 rp 1 (cmpSaved s0) sa.mem

theorem cmp_pre18_F (sa : AState) (hrsp : sa.regs "%rsp" = rsp + BitVec.ofInt 64 80) :
    FrameMem sa.mem rsp (-16) 96 rp 1 (cmpSaved sa) (aMachine.runBlock sa cmpPre18).mem := by
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emo : ∀ (s : AState) (X : String) (o : JOperand), (evalInstrA s (.mov X o)).mem
      = s.mem := fun _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elem : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int),
      (evalInstrA s (.lea D B I sc o)).mem = s.mem := fun _ _ _ _ _ _ => rfl
  have hlea : sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (-80)
      = rsp := by
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero, BitVec.add_assoc,
      show BitVec.ofInt 64 80 + BitVec.ofInt 64 (-80) = 0#64 by decide +kernel, BitVec.add_zero]
  simp only [cmpPre18, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
  simp (config := { decide := true }) only [em, emo, es, esm, elm, ele, elem,
    evalInstrA_loadMem_regs', ite_true, ite_false, hlea]
  refine ⟨fun e he => ?_, fun x hx _ => ?_⟩
  · simp only [cmpSaved, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
  · have hn : ∀ o : Int, -16 ≤ o → o ≤ 72 → ∀ (M : AMem) (v : BitVec 64),
        write64 M (rsp + BitVec.ofInt 64 o) v x = M x := fun o h1 h2 M v =>
      write64_of_not_inRange _ _ _ _ (fun hr => hx (inFr_of_inRange rsp x (-16) o 96 h1
        (by omega) (by norm_num) (by norm_num) (by omega) hr))
    simp only [hn 72 (by norm_num) (by norm_num), hn 64 (by norm_num) (by norm_num),
      hn 56 (by norm_num) (by norm_num), hn 48 (by norm_num) (by norm_num),
      hn 40 (by norm_num) (by norm_num), hn 32 (by norm_num) (by norm_num),
      hn 24 (by norm_num) (by norm_num), hn 16 (by norm_num) (by norm_num),
      hn 8 (by norm_num) (by norm_num), hn 0 (by norm_num) (by norm_num),
      hn (-8) (by norm_num) (by norm_num), hn (-16) (by norm_num) (by norm_num)]

theorem cmp_post_frame (sa : AState) (hrsp : sa.regs "%rsp" = rsp)
    (hF : FrameMem s0.mem rsp (-16) 96 rp 1 (cmpSaved s0) sa.mem) :
    (aMachine.runBlock sa cmpDecPost).regs "%rsp" = rsp + BitVec.ofInt 64 80
      ∧ (∀ R ∈ calleeSaved, (aMachine.runBlock sa cmpDecPost).regs R = s0.regs R)
      ∧ (aMachine.runBlock sa cmpDecPost).mem = sa.mem := by
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have hsv : ∀ (o : Int) (v : BitVec 64), (o, v) ∈ cmpSaved s0 →
      read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 o) = v := fun o v h => by
    rw [hrsp]; exact hF.saved (o, v) h
  refine ⟨?_, fun R hR => ?_, rfl⟩
  · simp only [cmpDecPost, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    simp (config := { decide := true }) only [ele, evalInstrA_loadMem_regs', elm, ite_true,
      ite_false]
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hR
    simp only [cmpDecPost, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [ele, evalInstrA_loadMem_regs', elm, ite_true,
      ite_false] <;>
    exact hsv _ _ (by simp [cmpSaved])

/-- The store of the compare trip, to the output word, keeps the memory invariant. -/
theorem cmp_store_F (n t y : Nat) (hstk : cmpStackSep rp ap bp rsp) :
    ∀ sa b zf, cmpRel rp ap bp rsp cmLiveE cmpK False (cmpPR rsp n t y) sa b zf →
      cmpF rp rsp s0 sa →
      cmpF rp rsp s0 (aMachine.runBlock sa
        [.loadMem "%r14" "%rsp" 72, .storeMemIdx "%r14" "%r9" 8 (.reg "%rdx")]) := by
  intro sa b zf ⟨h, hp⟩ hF
  obtain ⟨a, ha, hra⟩ := h.slots "a4" "s0" (by simp (config := { decide := true }) [cmpLay])
  have ha' : a = rsp + BitVec.ofInt 64 72 := by
    simp (config := { decide := true }) [cmpFrame] at ha
    exact ha.symm
  have hbase : (cmpLay rp ap bp).base "a4" = rp := by
    simp (config := { decide := true }) [cmpLay]
  have hr14 : read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 72) = rp := by
    rw [hp.1.1, ← ha', hra, hbase]
  have hmem : (aMachine.runBlock sa
      [.loadMem "%r14" "%rsp" 72, .storeMemIdx "%r14" "%r9" 8 (.reg "%rdx")]).mem
      = write64 sa.mem (rp + BitVec.ofNat 64 (8 * 0))
          ((evalInstrA sa (.loadMem "%r14" "%rsp" 72)).regs "%rdx") := by
    show write64 sa.mem ((evalInstrA sa (.loadMem "%r14" "%rsp" 72)).regs "%r14"
      + BitVec.ofInt 64 ((8 * ((evalInstrA sa (.loadMem "%r14" "%rsp" 72)).regs "%r9").toNat
        : Nat) : Int)) ((evalInstrA sa (.loadMem "%r14" "%rsp" 72)).regs "%rdx") = _
    rw [evalInstrA_loadMem_regs, hr14,
      evalInstrA_regs_of_not_mem_dsts _ _ "%r9" (by decide +kernel), hp.2]
    rfl
  show FrameMem _ _ _ _ _ _ _ (aMachine.runBlock sa _).mem
  rw [hmem]
  refine hF.store_out 0 (by decide) _ ?_
  have hadd : (cmpLay rp ap bp).addr "a4" 0 = rp + BitVec.ofNat 64 (8 * 0) := by
    simp (config := { decide := true }) [Layout.addr, cmpLay]
  intro e he
  simp only [cmpSaved, List.mem_cons, List.not_mem_nil, or_false] at he
  rw [← hadd]
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact disjoint8_comm (hstk "a4" 0 (Or.inl ⟨rfl, by decide⟩) _ (by simp) (by simp))

theorem cmp_tripF (m : Nat) (hm : m ≤ 8) (hsep : (cmpLay rp ap bp).Sep (cmpFrame rsp))
    (hdis : cmpDis rp ap bp) (hstk : cmpStackSep rp ap bp rsp) (t : Nat) (ht : t < m) :
    DecSim (fun sa b zf => cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m t (m - t)) sa b zf
        ∧ cmpF rp rsp s0 sa)
      (fun sa b zf => cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t) sa b zf
        ∧ cmpF rp rsp s0 sa)
      (cmpLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (cmpDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (DecSim.withF _ (cmp_seg_idx rp ap bp rsp m t (m - t) ht hm False)
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (cmp_seg_load2 rp ap bp rsp m t (m - t) ht hm)
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (cmp_seg_load1 rp ap bp rsp m t (m - t) ht hm)
    (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (cmp_seg_load4 rp ap bp rsp m t (m - t)) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (cmp_seg_chain rp ap bp rsp m t (m - t)) (fun _ _ _ _ h => h)).append <|
  (DecSim.withF _ (cmp_seg_store rp ap bp rsp m t (m - t) hsep hdis)
    (cmp_store_F rp ap bp rsp s0 m t (m - t) hstk)).append <|
  DecSim.withF _ (cmp_seg_tail rp ap bp rsp m t ht) (fun _ _ _ _ h => h)

/-- **The compare node with the frame.** -/
theorem cmp_node_frame (m : Nat) (hm : m ≤ 8) (hsep : (cmpLay rp ap bp).Sep (cmpFrame rsp))
    (hdis : cmpDis rp ap bp) (hstk : cmpStackSep rp ap bp rsp) (fn : String) (b : LstateM)
    (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp ap bp) (fun _ => none) cmpK False s0 b zf
      ∧ cmpEntry rp ap bp rsp m s0) :
    ∃ sa', Halts aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 s0 sa'
      ∧ sa'.regs "%rsp" = rsp + BitVec.ofInt 64 80
      ∧ (∀ R ∈ calleeSaved, sa'.regs R = s0.regs R)
      ∧ ∀ x, ¬ InFr rsp (-16) 96 x → ¬ InOut rp 1 x → sa'.mem x = s0.mem x := by
  obtain ⟨sa', t, k, hh, -, h2, h3, h4⟩ := decNode_halts fn
    [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"] cmpLoopBodyLit 4 (4 + 0x40000000)
    "Lctr4" cmpDecLoop m
    (fun sa b zf => (DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp ap bp) (fun _ => none) cmpK
      False sa b zf ∧ cmpEntry rp ap bp rsp m sa) ∧ sa = s0)
    (fun sa b zf => cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m 0 m) sa b zf
      ∧ cmpF rp rsp s0 sa)
    (fun sa b zf => cmpG rp ap bp rsp m sa b zf ∧ cmpF rp rsp s0 sa)
    (fun t sa b zf => cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m t (m - t)) sa b zf
      ∧ cmpF rp rsp s0 sa)
    (fun t sa b zf => cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t) sa b zf
      ∧ cmpF rp rsp s0 sa)
    (fun sa _ => sa.regs "%rsp" = rsp + BitVec.ofInt 64 80
      ∧ (∀ R ∈ calleeSaved, sa.regs R = s0.regs R)
      ∧ ∀ x, ¬ InFr rsp (-16) 96 x → ¬ InOut rp 1 x → sa.mem x = s0.mem x)
    cmpDecPre cmpDecPost cmpSeeds_isLopn cmpLoopBody_isLopn cmpNode_top cmpNode_end
    (DecSim.withFG _ _ (cmp_pre rp ap bp rsp m False hstk) (fun sa _ _ h hs => by
      subst hs
      have hs3 : ∀ s : AState, (aMachine.runBlock s [.mov "%rbx" (.reg "%rbx"),
          .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rsi")]).mem = s.mem := fun _ => rfl
      show FrameMem _ _ _ _ _ _ _ (aMachine.runBlock sa cmpDecPre).mem
      rw [cmpDecPre_eq, Machine.runBlock_append, hs3]
      exact cmp_pre18_F rp rsp sa h.2.1))
    (DecSim.withF _ (cmp_guard rp ap bp rsp m False) (fun _ _ _ _ h => h))
    (fun sa b zf h => cmp_guard_flag rp ap bp rsp m hm sa b zf h.1)
    (fun sa b zf pc h => ⟨cmp_guard_inv rp ap bp rsp m sa b zf pc h.1, h.2⟩)
    (fun t ht => cmp_tripF rp ap bp rsp s0 m hm hsep hdis hstk t ht)
    (fun t ht sa b zf h => cmp_trip_flag rp ap bp rsp m hm t ht sa b zf h.1)
    (fun t ht sa b zf pc h => ⟨cmp_trip_next rp ap bp rsp m t ht sa b zf pc h.1, h.2⟩)
    (fun sa b ⟨hr, hF⟩ => by
      obtain ⟨h1, h2, h3⟩ := cmp_post_frame rp rsp s0 sa hr.2.1 hF
      exact ⟨h1, h2, fun x hx ho => by rw [h3]; exact hF.outside x hx ho⟩)
    s0 b zf hpc ⟨hE, rfl⟩
  exact ⟨sa', hh, h2, h3, h4⟩

/-- **`mpn_cmp_ct` with its frame.** The result of `mpn_cmp_ct_entry_correct`, the stack
    pointer and the callee-saved registers as at the entry, and every byte outside the `96`
    frame bytes from `rsp - 16` (`rsp` the body's stack pointer, `80` below the entry's) and
    outside the output word at `rp` as at the entry. -/
theorem mpn_cmp_ct_frame_correct :
    ∃ f : Lfundef,
      (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct").map (·.lp_funcs) = some [("mpn_cmp_ct", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout cmpDecPre cmpDecLoop cmpDecPost)
      ∧ ∀ (rp app bpp rsp : BitVec 64) (m : Nat), 0 < m → m ≤ 8 →
        (cmpLay rp app bpp).Sep (cmpFrame rsp) → cmpDis rp app bpp →
        cmpStackSep rp app bpp rsp →
        ∀ sa : AState, cmpEntry rp app bpp rsp m sa → wd sa rp 0 = 0 →
        ∃ sa', Halts aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 sa sa'
          ∧ read64 sa'.mem rp
              = cmpSign (bignumVal ((List.range m).map (wd sa app)))
                  (bignumVal ((List.range m).map (wd sa bpp)))
          ∧ sa'.regs "%rsp" = sa.regs "%rsp"
          ∧ (∀ R ∈ calleeSaved, sa'.regs R = sa.regs R)
          ∧ ∀ x, ¬ InFr rsp (-16) 96 x → ¬ InOut rp 1 x → sa'.mem x = sa.mem x := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_cmp_ct_entry_correct
  obtain ⟨f', hf', hdec'⟩ : ∃ f : Lfundef,
      (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct").map (·.lp_funcs) = some [("mpn_cmp_ct", f)]
      ∧ decodeLprog (encodeLfundefBytes f.lfd_body)
          = some (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) :=
    ⟨_, by rw [MpnRtExportTerm.cmpLprog_eq]; rfl,
      by rw [MpnRtExportTerm.cmpPhysAbi_eq]; exact MpnRtExportTerm.cmpPhysLit_decode⟩
  rw [hf] at hf'
  obtain rfl : f = f' := by simpa using hf'
  rw [hdec] at hdec'
  obtain rfl := Option.some.inj hdec'
  refine ⟨f, hf, hdec, fun rp app bpp rsp m hm0 hm hsep hdis hstk sa hE h0 => ?_⟩
  obtain ⟨sa1, hh1, hw⟩ := H rp app bpp rsp m hm0 hm hsep hdis hstk sa hE h0
  obtain ⟨sa2, hh2, hr, hc, hmem⟩ := cmp_node_frame rp app bpp rsp sa m hm hsep hdis hstk
    "mpn_cmp_ct" (cmpB0 sa) false entryM_lpc ⟨cmpB0_corr rp app bpp rsp m sa hE false, hE⟩
  obtain rfl := haltsC_det hh1 hh2
  exact ⟨sa1, hh1, hw, hr.trans hE.1.symm, hc, hmem⟩

end Cmp

/-! ## 7. The referents -/

/-- The program the object list maps to the linked `mpn_and_n_loop_owned`. -/
theorem and_linked :
    (MpnLoopBytesEmit.kernels ()).lookup "mpn_and_n_loop_owned"
      = some (MpnLoopFrontEmit.andLprog ()) := by
  simp [MpnLoopBytesEmit.kernels, List.lookup]

theorem xor_linked :
    (MpnLoopBytesEmit.kernels ()).lookup "mpn_xor_n_loop_owned"
      = some (MpnLoopFrontEmit.xorLprog ()) := by
  simp [MpnLoopBytesEmit.kernels, List.lookup]

theorem ior_linked :
    (MpnLoopBytesEmit.kernels ()).lookup "mpn_ior_n_loop_owned"
      = some (MpnLoopFrontEmit.iorLprog ()) := by
  simp [MpnLoopBytesEmit.kernels, List.lookup]

theorem shift_linked :
    MpnRuntimeBytesEmit.kernels.lookup "mpn_shift_rt_owned"
      = some (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt") := by
  simp [MpnRuntimeBytesEmit.kernels]

theorem cmp_linked :
    MpnRuntimeBytesEmit.kernels.lookup "mpn_cmp_ct_owned"
      = some (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct") := by
  simp [MpnRuntimeBytesEmit.kernels, List.lookup]

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainFrame
