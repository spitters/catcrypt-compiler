/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedParts

/-!
# The three field callees of the shipped `ed25519_madd` on the address machine

`Fe25519AddShipped.fe25519AddShippedBlock`, `Fe25519SubShipped.fe25519SubShippedBlock` and
`Fe25519MulShipped.fe25519MulShippedBlock` are the bodies of `fe25519_add`, `fe25519_sub`
and `fe25519_mul` as printed by the owned backend. This module carries their correctness
to `AddrMem.runBlockA`, in the form the callee specifications of
`Ed25519MaddShippedParts` read: the four-limb value at the callee's own `%rdi`, the memory
outside the callee's output, and `%rsp`.

## The route

Each block is `canonD shippedBank` of itself, up to the bank of the second argument, so
`AddrMemDerived.runBlockA_simD_readsBeforeWrites` (add, sub) and
`AddrMemDerived.runBlockA_simD_from` (mul) carry a name-keyed statement about the block to
the address machine. The name-keyed statements are those of
`Fe25519AddSubSelectProof.feAddBlock_correct`, `feSubBlock_correct` and
`Fe25519MulSqrProof.feMulBlock_mod`, transported along the register allocation by
`Fe25519KernelsBytes.runBlock_renameBlock_mem` and `framed_mem`.

`fe25519_mul` passes its second argument in `%rdx` and moves it to `%rcx`, so its abstract
entry state `mulEntryD` gives `%rdx` the bank `%rcx`, and its pointers `mulP` base that
bank at the second argument. It also writes six red-zone slots below `%rsp`, which
`FrameCRed` states alongside the output.

## Main definitions

* `outCells`, `mulCells`: the cells a field leaf accesses.
* `mulEntryD`, `mulP`: the abstract entry state and entry pointers of the multiply block.
* `deImulri`: the two-operand form of a three-operand multiply by an immediate.
* `FrameCRed`: a frame over the output and the red-zone slots.

## Main results

* `addShipped_correct_addr`, `subShipped_correct_addr`: with both inputs below
  `2 ^ 255 - 19`, the block leaves their sum, resp. difference, modulo that prime at
  `%rdi`, changes no byte outside the 32 bytes at `%rdi`, and keeps `%rsp`.
* `mulShipped_correct_addr`: for separated cells, the block leaves the product modulo
  `2 ^ 255 - 19` at `%rdi`, changes no byte outside the 32 bytes at `%rdi` and the 48
  bytes below `%rsp`, and keeps `%rsp`.
* `separated_mulCells`: the cells of the multiply block are separated when its two
  argument buffers, its output buffer and its red-zone slots are pairwise disjoint.
* `leafOut`, `runBlockA_regs_of_not_dsts`, `feO_eq_limbsNat`, `mem4_jOf`: the transport
  lemmas the three leaves share.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519 limbsNat)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (nameOf)

/-! ## Generic transport -/

/-- A sublist of a separated cell list is separated. -/
theorem separated_of_subset {bank : String → Option String} {P : String → BitVec 64}
    {K K' : List (String × Int)} (hsub : ∀ k ∈ K', k ∈ K) (h : Separated bank P K) :
    Separated bank P K' := fun k hk k' hk' hne => h k (hsub k hk) k' (hsub k' hk') hne

/-- A shipped bank's cell address is its base register plus the offset. -/
theorem absMem_shipped (P : String → BitVec 64) (m : AMem) (b : String) (o : Int)
    (hb : shippedBank b = some b) :
    absMem shippedBank P m b o = read64 m (P b + BitVec.ofInt 64 o) := by
  simp [absMem, keyAddr, basePtr, hb]

/-- A self-move leaves the state unchanged. -/
theorem evalInstr_mov_self (s : JState 64) (d : String) :
    evalInstr s (.mov d (.reg d)) = s := by
  show s.setReg d (x86_MOV (s.regs d)) = s
  simp only [JState.setReg, x86_MOV]
  congr 1
  funext r
  split <;> simp_all

/-- A register no instruction of the block writes keeps its value. -/
theorem runBlockA_regs_of_not_dsts (sa : AState) (blk : List (JInstr 64)) (r : String)
    (h : ∀ i ∈ blk, r ∉ dsts i) : (runBlockA sa blk).regs r = sa.regs r := by
  induction blk generalizing sa with
  | nil => rfl
  | cons i is ih =>
    rw [runBlockA_cons, ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    show (evalInstr sa.view i).regs r = sa.regs r
    rw [evalInstr_regs_of_not_mem_dsts _ _ _ (h i List.mem_cons_self)]
    rfl

/-- The register `%rsp` is written by no instruction of a block that passes the check. -/
theorem rsp_not_dst_of_all {blk : List (JInstr 64)}
    (h : blk.all (fun i => decide ("%rsp" ∉ dsts i)) = true) : ∀ i ∈ blk, "%rsp" ∉ dsts i :=
  fun i hi => by simpa using List.all_eq_true.1 h i hi

/-- The four-limb value at a pointer is `limbsNat` of the four cell reads. -/
theorem feO_eq_limbsNat (m : AMem) (p : BitVec 64) :
    feO m p 0 = limbsNat (read64 m (p + BitVec.ofInt 64 0)) (read64 m (p + BitVec.ofInt 64 8))
      (read64 m (p + BitVec.ofInt 64 16)) (read64 m (p + BitVec.ofInt 64 24)) := by
  simp only [feO, limbOffs, List.map_cons, List.map_nil, bignumVal, limbsNat]
  norm_num
  ring

/-! ## The field cells -/

/-- The four output cells of a field leaf. -/
def outCells : List (String × Int) :=
  [("%rdi", 0), ("%rdi", 8), ("%rdi", 16), ("%rdi", 24)]

theorem shippedBank_rdi : shippedBank "%rdi" = some "%rdi" := by decide
theorem shippedBank_rsi : shippedBank "%rsi" = some "%rsi" := by decide
theorem shippedBank_rdx : shippedBank "%rdx" = some "%rdx" := by decide
theorem shippedBank_rsp : shippedBank "%rsp" = some "%rsp" := by decide
theorem shippedBank_rcx : shippedBank "%rcx" = some "%rcx" := by decide
theorem shippedBank_r8 : shippedBank "%r8" = some "%r8" := by decide

/-- Each register the shipped leaves address memory through is its own bank. -/
macro "bank_self" : tactic =>
  `(tactic| first
      | exact shippedBank_rdi | exact shippedBank_rsi | exact shippedBank_rdx
      | exact shippedBank_rsp | exact shippedBank_rcx | exact shippedBank_r8)

/-- The four output cells occupy disjoint ranges at every pointer. -/
theorem separated_outCells (R : String → BitVec 64) : Separated shippedBank R outCells := by
  intro k hk k' hk' hne
  simp only [outCells, List.mem_cons, List.not_mem_nil, or_false] at hk hk'
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl <;>
    simp only [keyAddr_shipped _ _ _ shippedBank_rdi] <;>
    first
      | exact absurd rfl hne
      | exact djSS _ _ _ (by norm_num) (by norm_num)

theorem canonD_add :
    canonD shippedBank Fe25519AddShipped.fe25519AddShippedBlock
      = Fe25519AddShipped.fe25519AddShippedBlock := by decide +kernel

theorem add_split :
    Fe25519AddShipped.fe25519AddShippedBlock = JInstr.mov "%rdx" (.reg "%rdx") :: feAddPhys := by
  decide +kernel

theorem rho_add_z : nameOf feAddAllocL "z" = "%rdi" := by decide
theorem rho_add_x : nameOf feAddAllocL "x" = "%rsi" := by decide
theorem rho_add_y : nameOf feAddAllocL "y" = "%rdx" := by decide

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
  (mem4 feAddBlock_correct feSubBlock_correct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel (feAddBlock feSubBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (feMulBlock)

/-- The shipped add block, over the name-keyed memory, stores the sum modulo `p25519`
    at `%rdi`. -/
theorem addShipped_nameKeyed (st : JState 64)
    (h : mem4 st.mem "%rsi" + mem4 st.mem "%rdx" < 2 * p25519) :
    mem4 (runBlock st Fe25519AddShipped.fe25519AddShippedBlock).mem "%rdi"
      = (mem4 st.mem "%rsi" + mem4 st.mem "%rdx") % p25519 := by
  rw [add_split, runBlock_cons, evalInstr_mov_self]
  have hm := runBlock_renameBlock_mem (nameOf feAddAllocL) feAddBlock feAdd_renInjOn st "z"
    (by decide +kernel)
  rw [rho_add_z] at hm
  have hx : (pullState (nameOf feAddAllocL) st).mem "x" = st.mem "%rsi" := by
    simp only [pullState, rho_add_x]
  have hy : (pullState (nameOf feAddAllocL) st).mem "y" = st.mem "%rdx" := by
    simp only [pullState, rho_add_y]
  have h' : mem4 (pullState (nameOf feAddAllocL) st).mem "x"
      + mem4 (pullState (nameOf feAddAllocL) st).mem "y" < 2 * p25519 := by
    simpa only [mem4, hx, hy] using h
  obtain ⟨h0, -, -, -⟩ := feAddBlock_correct (pullState (nameOf feAddAllocL) st) h'
  simp only [mem4, hx, hy] at h0
  show mem4 (runBlock st feAddPhys).mem "%rdi" = _
  simp only [mem4, feAddPhys, hm]
  simpa only [mem4] using h0

theorem pM_eq : pM = p25519 := rfl

/-- The output cells and the frame of a leaf whose canonical block writes exactly the four
    cells at `%rdi` and reads every cell it reads before writing it. -/
theorem leafOut (blk : List (JInstr 64)) (hd : disciplinedD shippedBank blk = true)
    (hrw : readsBeforeWritesB (canonD shippedBank blk) = true)
    (hwk : writeKeys (canonD shippedBank blk) = outCells) (sa : AState) :
    (∀ o : Int, ("%rdi", o) ∈ outCells →
        read64 (runBlockA sa blk).mem (sa.regs "%rdi" + BitVec.ofInt 64 o)
          = (runBlock (jOf shippedBank sa) (canonD shippedBank blk)).mem "%rdi" o)
      ∧ FrameC sa.mem (runBlockA sa blk).mem (sa.regs "%rdi") 4 := by
  have hsepW : Separated shippedBank sa.regs (writeKeys (canonD shippedBank blk)) := by
    rw [hwk]; exact separated_outCells _
  obtain ⟨-, -, hK⟩ := runBlockA_simD_readsBeforeWrites shippedBank blk hd hrw sa hsepW
  refine ⟨fun o ho => ?_, fun x hx => ?_⟩
  · have := hK ("%rdi", o) (by rw [hwk]; exact ho)
    rwa [absMem_shipped _ _ _ _ shippedBank_rdi] at this
  · refine runBlockA_mem_frameD shippedBank _ hd sa x hsepW ?_
    intro k hk
    rw [hwk] at hk
    have : k = ("%rdi", 0) ∨ k = ("%rdi", 8) ∨ k = ("%rdi", 16) ∨ k = ("%rdi", 24) := by
      simpa [outCells] using hk
    rcases this with rfl | rfl | rfl | rfl
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 0 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 1 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 2 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 3 (by omega)

/-- The four-limb value at a shipped bank's base register, as `mem4` of the name-keyed
    memory. -/
theorem mem4_jOf (sa : AState) (b : String) (hb : shippedBank b = some b) :
    mem4 (jOf shippedBank sa).mem b = feO sa.mem (sa.regs b) 0 := by
  simp only [mem4, jOf, absMem_shipped _ _ _ _ hb, feO_eq_limbsNat]

theorem add_rbw : readsBeforeWritesB (canonD shippedBank Fe25519AddShipped.fe25519AddShippedBlock)
    = true := by decide +kernel

theorem add_wk : writeKeys (canonD shippedBank Fe25519AddShipped.fe25519AddShippedBlock)
    = outCells := by decide +kernel

/-- **The shipped `fe25519_add` block on the address machine.** With both inputs below
    `2 ^ 255 - 19`, the block leaves their sum modulo that prime at `%rdi`, changes no byte
    outside the 32 bytes at `%rdi`, and keeps `%rsp`. -/
theorem addShipped_correct_addr (sa : AState) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (runBlockA sa Fe25519AddShipped.fe25519AddShippedBlock).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + feO sa.mem (sa.regs "%rdx") 0) % pM)
      ∧ FrameC sa.mem (runBlockA sa Fe25519AddShipped.fe25519AddShippedBlock).mem
          (sa.regs "%rdi") 4
      ∧ (runBlockA sa Fe25519AddShipped.fe25519AddShippedBlock).regs "%rsp"
          = sa.regs "%rsp" := by
  obtain ⟨hout, hfr⟩ := leafOut _ fe25519Add_disciplinedD add_rbw add_wk sa
  refine ⟨fun h1 h2 => ?_, hfr,
    runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  rw [feO_eq_limbsNat, hout 0 (by simp [outCells]), hout 8 (by simp [outCells]),
    hout 16 (by simp [outCells]), hout 24 (by simp [outCells]), canonD_add]
  show mem4 (runBlock (jOf shippedBank sa) Fe25519AddShipped.fe25519AddShippedBlock).mem "%rdi"
    = _
  rw [pM_eq] at h1 h2
  rw [addShipped_nameKeyed (jOf shippedBank sa)
    (by rw [mem4_jOf _ _ shippedBank_rsi, mem4_jOf _ _ shippedBank_rdx]; omega)]
  rw [mem4_jOf _ _ shippedBank_rsi, mem4_jOf _ _ shippedBank_rdx, pM_eq]

/-! ## The shipped `fe25519_sub` -/

theorem canonD_sub :
    canonD shippedBank Fe25519SubShipped.fe25519SubShippedBlock
      = Fe25519SubShipped.fe25519SubShippedBlock := by decide +kernel

theorem sub_split :
    Fe25519SubShipped.fe25519SubShippedBlock = JInstr.mov "%rdx" (.reg "%rdx") :: feSubPhys := by
  decide +kernel

theorem rho_sub_z : nameOf feSubAllocL "z" = "%rdi" := by decide
theorem rho_sub_x : nameOf feSubAllocL "x" = "%rsi" := by decide
theorem rho_sub_y : nameOf feSubAllocL "y" = "%rdx" := by decide

/-- The shipped subtract block, over the name-keyed memory, stores the difference modulo
    `p25519` at `%rdi`. -/
theorem subShipped_nameKeyed (st : JState 64)
    (h1 : mem4 st.mem "%rsi" < mem4 st.mem "%rdx" + p25519)
    (h2 : mem4 st.mem "%rdx" ≤ mem4 st.mem "%rsi" + p25519) :
    mem4 (runBlock st Fe25519SubShipped.fe25519SubShippedBlock).mem "%rdi"
      = (mem4 st.mem "%rsi" + p25519 - mem4 st.mem "%rdx") % p25519 := by
  rw [sub_split, runBlock_cons, evalInstr_mov_self]
  have hm := runBlock_renameBlock_mem (nameOf feSubAllocL) feSubBlock feSub_renInjOn st "z"
    (by decide +kernel)
  rw [rho_sub_z] at hm
  have hx : (pullState (nameOf feSubAllocL) st).mem "x" = st.mem "%rsi" := by
    simp only [pullState, rho_sub_x]
  have hy : (pullState (nameOf feSubAllocL) st).mem "y" = st.mem "%rdx" := by
    simp only [pullState, rho_sub_y]
  have h1' : mem4 (pullState (nameOf feSubAllocL) st).mem "x"
      < mem4 (pullState (nameOf feSubAllocL) st).mem "y" + p25519 := by
    simpa only [mem4, hx, hy] using h1
  have h2' : mem4 (pullState (nameOf feSubAllocL) st).mem "y"
      ≤ mem4 (pullState (nameOf feSubAllocL) st).mem "x" + p25519 := by
    simpa only [mem4, hx, hy] using h2
  obtain ⟨h0, -, -, -⟩ := feSubBlock_correct (pullState (nameOf feSubAllocL) st) h1' h2'
  simp only [mem4, hx, hy] at h0
  show mem4 (runBlock st feSubPhys).mem "%rdi" = _
  simp only [mem4, feSubPhys, hm]
  simpa only [mem4] using h0

theorem sub_rbw : readsBeforeWritesB (canonD shippedBank Fe25519SubShipped.fe25519SubShippedBlock)
    = true := by decide +kernel

theorem sub_wk : writeKeys (canonD shippedBank Fe25519SubShipped.fe25519SubShippedBlock)
    = outCells := by decide +kernel

/-- **The shipped `fe25519_sub` block on the address machine.** With both inputs below
    `2 ^ 255 - 19`, the block leaves their difference modulo that prime at `%rdi`, changes
    no byte outside the 32 bytes at `%rdi`, and keeps `%rsp`. -/
theorem subShipped_correct_addr (sa : AState) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (runBlockA sa Fe25519SubShipped.fe25519SubShippedBlock).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + (pM - feO sa.mem (sa.regs "%rdx") 0)) % pM)
      ∧ FrameC sa.mem (runBlockA sa Fe25519SubShipped.fe25519SubShippedBlock).mem
          (sa.regs "%rdi") 4
      ∧ (runBlockA sa Fe25519SubShipped.fe25519SubShippedBlock).regs "%rsp"
          = sa.regs "%rsp" := by
  obtain ⟨hout, hfr⟩ := leafOut _ fe25519Sub_disciplinedD sub_rbw sub_wk sa
  refine ⟨fun h1 h2 => ?_, hfr,
    runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  rw [feO_eq_limbsNat, hout 0 (by simp [outCells]), hout 8 (by simp [outCells]),
    hout 16 (by simp [outCells]), hout 24 (by simp [outCells]), canonD_sub]
  show mem4 (runBlock (jOf shippedBank sa) Fe25519SubShipped.fe25519SubShippedBlock).mem "%rdi"
    = _
  rw [pM_eq] at h1 h2
  rw [subShipped_nameKeyed (jOf shippedBank sa)
    (by rw [mem4_jOf _ _ shippedBank_rsi, mem4_jOf _ _ shippedBank_rdx]; omega)
    (by rw [mem4_jOf _ _ shippedBank_rsi, mem4_jOf _ _ shippedBank_rdx]; omega)]
  rw [mem4_jOf _ _ shippedBank_rsi, mem4_jOf _ _ shippedBank_rdx, pM_eq]
  congr 1
  omega

/-! ## The shipped `fe25519_mul` -/

/-- The two-operand form of a three-operand multiply by an immediate whose source and
    destination are the same register. -/
def deImulri : JInstr 64 → JInstr 64
  | .imulri d s k => if d = s then .imul d (.imm k) else .imulri d s k
  | i => i

theorem evalInstr_deImulri (st : JState 64) (i : JInstr 64) :
    evalInstr st (deImulri i) = evalInstr st i := by
  unfold deImulri
  split
  · rename_i d s k
    split
    · subst_vars; rfl
    · rfl
  · rfl

theorem runBlock_map_deImulri (st : JState 64) (blk : List (JInstr 64)) :
    runBlock st (blk.map deImulri) = runBlock st blk := by
  induction blk generalizing st with
  | nil => rfl
  | cons i is ih => rw [List.map_cons, runBlock_cons, runBlock_cons, evalInstr_deImulri, ih]

theorem mul_deImulri :
    Fe25519MulShipped.fe25519MulShippedBlock.map deImulri = feMulFramed := by decide +kernel

theorem runBlock_mulShipped (st : JState 64) :
    runBlock st Fe25519MulShipped.fe25519MulShippedBlock = runBlock st feMulFramed := by
  rw [← mul_deImulri, runBlock_map_deImulri]

/-- The shipped multiply block, over the name-keyed memory, stores the product modulo
    `p25519` at `%rdi`. -/
theorem mulShipped_nameKeyed (st : JState 64) :
    mem4 (runBlock st Fe25519MulShipped.fe25519MulShippedBlock).mem "%rdi"
      = mem4 st.mem "%rsi" * mem4 st.mem "%rcx" % p25519 := by
  rw [runBlock_mulShipped]
  have hz : nameOf feMulAllocL "z" = "%rdi" := by decide
  have hm := framed_mem st feMulPre _ feMulBlock feMul_body_frameSafe feMul_renInjOn "z"
    (by decide +kernel) (by rw [hz]; decide)
  rw [hz] at hm
  have hx : (pullState (nameOf feMulAllocL) (runBlock st feMulPre)).mem "x" = st.mem "%rsi" := by
    have h : nameOf feMulAllocL "x" = "%rsi" := by decide
    simp only [pullState, h]
    rfl
  have hy : (pullState (nameOf feMulAllocL) (runBlock st feMulPre)).mem "y" = st.mem "%rcx" := by
    have h : nameOf feMulAllocL "y" = "%rcx" := by decide
    simp only [pullState, h]
    rfl
  have h0 := CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof.feMulBlock_mod
    (pullState (nameOf feMulAllocL) (runBlock st feMulPre))
  simp only [CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof.mem4,
    hx, hy] at h0
  have e : mem4 (runBlock st feMulFramed).mem "%rdi"
      = mem4 (runBlock (pullState (nameOf feMulAllocL) (runBlock st feMulPre)) feMulBlock).mem
          "z" := by
    simp only [mem4, feMulFramed, feMulPhys, hm]
  rw [e]
  simpa only [mem4, limbsNat] using h0

/-- The abstract state of the multiply block's entry: the output and first-input pointers
    and `%rsp` at their own banks, and the second-input pointer, passed in `%rdx`, at the
    bank `%rcx` the block moves it to. -/
def mulEntryD : DState :=
  { entry := false
    regs := [("%rdi", some (.ptr "%rdi" 0)), ("%rsi", some (.ptr "%rsi" 0)),
             ("%rdx", some (.ptr "%rcx" 0)), ("%rsp", some (.ptr "%rsp" 0))]
    cells := [] }

/-- The cells the multiply block reads or writes: the four limbs at each of `%rsi`, the
    second input `%rcx` and `%rdi`, and the six red-zone slots below `%rsp`. -/
def mulCells : List (String × Int) :=
  [("%rsi", 0), ("%rsi", 8), ("%rsi", 16), ("%rsi", 24),
   ("%rcx", 0), ("%rcx", 8), ("%rcx", 16), ("%rcx", 24),
   ("%rdi", 0), ("%rdi", 8), ("%rdi", 16), ("%rdi", 24),
   ("%rsp", -8), ("%rsp", -16), ("%rsp", -24), ("%rsp", -32), ("%rsp", -40), ("%rsp", -48)]

theorem mulCells_mem : ∀ k ∈ mulCells,
    (k.1 = "%rsi" ∧ 0 ≤ k.2 ∧ k.2 ≤ 24 ∧ k.2 % 8 = 0)
      ∨ (k.1 = "%rcx" ∧ 0 ≤ k.2 ∧ k.2 ≤ 24 ∧ k.2 % 8 = 0)
      ∨ (k.1 = "%rdi" ∧ 0 ≤ k.2 ∧ k.2 ≤ 24 ∧ k.2 % 8 = 0)
      ∨ (k.1 = "%rsp" ∧ -48 ≤ k.2 ∧ k.2 ≤ -8 ∧ k.2 % 8 = 0) := by decide

/-- The cells of the multiply block are separated when its two argument buffers, its
    output buffer and its red-zone slots are pairwise disjoint. -/
theorem separated_mulCells {R : String → BitVec 64}
    (h1 : RangeDisj (R "%rsi") 0 24 (R "%rcx") 0 24)
    (h2 : RangeDisj (R "%rsi") 0 24 (R "%rdi") 0 24)
    (h3 : RangeDisj (R "%rcx") 0 24 (R "%rdi") 0 24)
    (h4 : RangeDisj (R "%rsi") 0 24 (R "%rsp") (-48) (-8))
    (h5 : RangeDisj (R "%rcx") 0 24 (R "%rsp") (-48) (-8))
    (h6 : RangeDisj (R "%rdi") 0 24 (R "%rsp") (-48) (-8)) :
    Separated shippedBank R mulCells := by
  intro k hk k' hk' hne
  rcases mulCells_mem k hk with ⟨hb, p0, p1, p8⟩ | ⟨hb, p0, p1, p8⟩ | ⟨hb, p0, p1, p8⟩ |
      ⟨hb, p0, p1, p8⟩ <;>
    rcases mulCells_mem k' hk' with ⟨hb', q0, q1, q8⟩ | ⟨hb', q0, q1, q8⟩ |
        ⟨hb', q0, q1, q8⟩ | ⟨hb', q0, q1, q8⟩ <;>
    rw [keyAddr_of hb (by bank_self), keyAddr_of hb' (by bank_self)]
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)
  · exact h1 _ _ p0 p1 p8 q0 q1 q8
  · exact h2 _ _ p0 p1 p8 q0 q1 q8
  · exact h4 _ _ p0 p1 p8 q0 q1 q8
  · exact (h1 _ _ q0 q1 q8 p0 p1 p8).symm
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)
  · exact h3 _ _ p0 p1 p8 q0 q1 q8
  · exact h5 _ _ p0 p1 p8 q0 q1 q8
  · exact (h2 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact (h3 _ _ q0 q1 q8 p0 p1 p8).symm
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)
  · exact h6 _ _ p0 p1 p8 q0 q1 q8
  · exact (h4 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact (h5 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact (h6 _ _ q0 q1 q8 p0 p1 p8).symm
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)

theorem mul_disciplinedFromD :
    disciplinedFromD shippedBank mulEntryD Fe25519MulShipped.fe25519MulShippedBlock = true := by
  decide +kernel

theorem canonFromD_mul :
    canonFromD shippedBank mulEntryD Fe25519MulShipped.fe25519MulShippedBlock
      = Fe25519MulShipped.fe25519MulShippedBlock := by decide +kernel

theorem mul_rbw :
    readsBeforeWritesFromB mulCells false
      (canonFromD shippedBank mulEntryD Fe25519MulShipped.fe25519MulShippedBlock) = true := by
  decide +kernel

theorem mul_wkList :
    writeKeys (canonFromD shippedBank mulEntryD Fe25519MulShipped.fe25519MulShippedBlock)
      = [("%rsp", -8), ("%rsp", -16), ("%rsp", -24), ("%rsp", -32), ("%rsp", -40),
         ("%rsp", -48), ("%rdi", 0), ("%rdi", 8), ("%rdi", 16), ("%rdi", 24)] := by
  decide +kernel

theorem mul_wk :
    ∀ k ∈ writeKeys (canonFromD shippedBank mulEntryD Fe25519MulShipped.fe25519MulShippedBlock),
      k ∈ mulCells := by decide +kernel

/-- The entry pointers of the multiply block: the bank `%rcx` is based at the second
    argument, which the block moves out of `%rdx`. -/
def mulP (sa : AState) : String → BitVec 64 :=
  fun b => if b = "%rcx" then sa.regs "%rdx" else sa.regs b

theorem mulEntryD_get (r : String) (v : AVal) (h : mulEntryD.get shippedBank r = some v) :
    (r = "%rdi" ∧ v = .ptr "%rdi" 0) ∨ (r = "%rsi" ∧ v = .ptr "%rsi" 0) ∨
      (r = "%rdx" ∧ v = .ptr "%rcx" 0) ∨ (r = "%rsp" ∧ v = .ptr "%rsp" 0) := by
  simp only [DState.get, mulEntryD, lookupR] at h
  split_ifs at h <;> simp_all

theorem mulRegInv (sa : AState) : RegInvD shippedBank (mulP sa) mulEntryD sa.regs := by
  intro r v h
  rcases mulEntryD_get r v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [AVal.denote, basePtr, mulP, shippedBank]

theorem mulCellInv (sa : AState) : CellInvD shippedBank (mulP sa) mulEntryD sa.mem := by
  intro c v h
  simp [mulEntryD, lookupC] at h

/-- `m'` differs from `m` only in the `8 * n` bytes from `a` and the `8 * k` bytes below
    `b`. -/
def FrameCRed (m m' : AMem) (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop :=
  ∀ x : BitVec 64,
    (∀ i, i < n → ¬ InRange8 (a + BitVec.ofInt 64 (8 * i : Nat)) x) →
    (∀ i, i < k → ¬ InRange8 (b + BitVec.ofInt 64 (-(8 * (i + 1) : Nat) : Int)) x) →
    m' x = m x

/-- **The shipped `fe25519_mul` block on the address machine.** When the input, output and
    red-zone cells occupy pairwise disjoint eight-byte ranges, the block leaves the product
    of the four-limb values at `%rsi` and at `%rdx`, reduced modulo `2 ^ 255 - 19`, at
    `%rdi`; it changes no byte outside the 32 bytes at `%rdi` and the 48 bytes below
    `%rsp`, and keeps `%rsp`. -/
theorem mulShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank (mulP sa) mulCells) :
    feO (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameCRed sa.mem (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).mem
          (sa.regs "%rdi") 4 (sa.regs "%rsp") 6
      ∧ (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).regs "%rsp"
          = sa.regs "%rsp" := by
  have hP : ∀ b : String, b ≠ "%rcx" → mulP sa b = sa.regs b := by
    intro b hb; simp [mulP, hb]
  obtain ⟨-, -, hK, -, -⟩ := runBlockA_simD_from shippedBank (mulP sa) mulEntryD
    Fe25519MulShipped.fe25519MulShippedBlock mulCells mul_disciplinedFromD mul_rbw mul_wk
    (by simp [mulEntryD, DState.cellKeys]) sa hsep (mulRegInv sa) (mulCellInv sa)
  refine ⟨?_, ?_, runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  · have hout : ∀ o : Int, ("%rdi", o) ∈ mulCells →
        read64 (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).mem
            (sa.regs "%rdi" + BitVec.ofInt 64 o)
          = (runBlock (jOfD shippedBank (mulP sa) sa)
              Fe25519MulShipped.fe25519MulShippedBlock).mem "%rdi" o := by
      intro o ho
      have := hK ("%rdi", o) ho
      rw [absMem_shipped _ _ _ _ shippedBank_rdi, hP _ (by decide), canonFromD_mul] at this
      exact this
    have hin : ∀ (b c : String), shippedBank b = some b → mulP sa b = sa.regs c →
        mem4 (jOfD shippedBank (mulP sa) sa).mem b = feO sa.mem (sa.regs c) 0 := by
      intro b c hb hbc
      simp only [mem4, jOfD, absMem_shipped _ _ _ _ hb, hbc, feO_eq_limbsNat]
    rw [feO_eq_limbsNat, hout 0 (by simp [mulCells]), hout 8 (by simp [mulCells]),
      hout 16 (by simp [mulCells]), hout 24 (by simp [mulCells])]
    show mem4 (runBlock (jOfD shippedBank (mulP sa) sa)
      Fe25519MulShipped.fe25519MulShippedBlock).mem "%rdi" = _
    rw [mulShipped_nameKeyed, hin "%rsi" "%rsi" shippedBank_rsi (hP _ (by decide)),
      hin "%rcx" "%rdx" (by decide) (by simp [mulP]), pM_eq]
  · intro x hx hy
    refine runBlockA_mem_frameD_from shippedBank (mulP sa) x _ mulEntryD sa
      mul_disciplinedFromD (mulRegInv sa) (mulCellInv sa) ?_ ?_
    · intro k hk
      rw [mul_wkList] at hk
      have hrsp : mulP sa "%rsp" = sa.regs "%rsp" := by simp [mulP]
      have hrdi : mulP sa "%rdi" = sa.regs "%rdi" := by simp [mulP]
      have hk' : k = ("%rsp", -8) ∨ k = ("%rsp", -16) ∨ k = ("%rsp", -24) ∨
          k = ("%rsp", -32) ∨ k = ("%rsp", -40) ∨ k = ("%rsp", -48) ∨
          k = ("%rdi", 0) ∨ k = ("%rdi", 8) ∨ k = ("%rdi", 16) ∨ k = ("%rdi", 24) := by
        simpa using hk
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [keyAddr_shipped _ _ _ shippedBank_rsp, hrsp] using hy 0 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rsp, hrsp] using hy 1 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rsp, hrsp] using hy 2 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rsp, hrsp] using hy 3 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rsp, hrsp] using hy 4 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rsp, hrsp] using hy 5 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 0 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 1 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 2 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 3 (by omega)
    · intro k hk c hc hne
      have hc' : c ∈ writeKeys (canonFromD shippedBank mulEntryD
          Fe25519MulShipped.fe25519MulShippedBlock) := by
        simpa [mulEntryD, DState.cellKeys] using hc
      exact hsep k (mul_wk k hk) c (mul_wk c hc') (Ne.symm hne)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
