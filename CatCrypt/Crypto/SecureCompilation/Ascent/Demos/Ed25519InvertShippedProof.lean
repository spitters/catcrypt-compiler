/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertTable
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertCallModel
public import CatCrypt.Crypto.Util.P25519PrimeCert

/-!
# Correctness of the shipped `ed25519_invert`

`Imported.Ed25519InvertShipped.ed25519InvertShippedBlock` is the body of
`ed25519_invert_x86_from_lean` as printed by the owned backend: 265 calls to
`fe25519_sqr` and `fe25519_mul`. Run over `Ed25519MaddShippedProof.segsRunA` with each
callee symbol at the shipped block of that function, it leaves at the output pointer the
input raised to `2 ^ 255 - 21` modulo `2 ^ 255 - 19`, which for a nonzero input is the
inverse in `ZMod (2 ^ 255 - 19)`.

## The route

Segment 1 stores the output pointer in the slot at `%rsp + 128`, copies the input pointer
to `%rbx` and squares the input into the first field slot; `invertEntry` states the
invariant of `Ed25519InvertChain` at that point. `Ed25519InvertChain.chainRun` runs
segments 2 to 264 over the step list of `Ed25519InvertTable`, whose final exponents
`invertEnv_final` gives. Segment 265 reloads the output pointer and multiplies the two
slots whose exponents sum to `2 ^ 255 - 21`.

## Main results

* `invertShipped_correct_addr`, `invertShipped_inv_zmod`: the power and the inverse, over
  callees at their specifications.
* `invertShipped_correct`, `invertShipped_inv`: the same over the shipped callees.
* `pM_prime`: `2 ^ 255 - 19` is prime, by the certificate of `P25519PrimeCert`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (mulSym sqrSym)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)

theorem feO_write64 (m : AMem) (a v p : BitVec 64) (o : Int)
    (h : ∀ j ∈ limbOffs, Disjoint8 a (p + BitVec.ofInt 64 (o + j))) :
    feO (write64 m a v) p o = feO m p o := by
  simp only [feO]
  refine congrArg bignumVal (List.map_congr_left fun j hj => ?_)
  exact read64_write64_of_disjoint m a _ v (h j hj)

/-- The body of segment 1: the input pointer to `%rbx`, the output pointer to its stack
    slot, and the arguments of the first square. -/
theorem runEntryBody (sa : AState) :
    let s' := runBlockA sa
      [.mov "%rbx" (.reg "%rsi"), .storeMem "%rsp" 128 (.reg "%rdi"),
       .lea "%rdi" "%rsp" "%rsp" 0 0, .mov "%rsi" (.reg "%rbx")]
    s'.mem = write64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 128) (sa.regs "%rdi")
      ∧ s'.regs "%rsp" = sa.regs "%rsp" ∧ s'.regs "%rbx" = sa.regs "%rsi"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 0
      ∧ s'.regs "%rsi" = sa.regs "%rsi" := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 0 = _
  exact leaZero _ _

/-- **The first segment.** -/
theorem invertEntry {C : ACallModel} (hC : InvertCallees C) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi")) :
    ChainInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi")
      (feO sa.mem (sa.regs "%rsi") 0) invertEnv1
      (segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedSeg001) := by
  obtain ⟨hm, hrsp, hrbx, hrdi, hrsi⟩ := runEntryBody sa
  set sb := runBlockA sa
    [JInstr.mov "%rbx" (.reg "%rsi"), JInstr.storeMem "%rsp" 128 (.reg "%rdi"),
     JInstr.lea "%rdi" "%rsp" "%rsp" 0 0, JInstr.mov "%rsi" (.reg "%rbx")] with hsb
  have hslot : ∀ j ∈ limbOffs,
      Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 128)
        (sa.regs "%rsi" + BitVec.ofInt 64 (0 + j)) := by
    intro j hj
    simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
    exact hsep.si 128 (0 + j) (by omega) (by omega) (by omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
  have hpre : ChainInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi")
      (feO sa.mem (sa.regs "%rsi") 0) ⟨none, none, none, none⟩ sb := by
    refine ⟨hrsp, hrbx, ?_, ?_, fun b e hb => ?_⟩
    · rw [hm, read64_write64_same]
    · rw [hm, feO_write64 _ _ _ _ _ hslot]
    · cases b <;> exact absurd hb (by simp [Env.get])
  obtain ⟨hv, hfr, hcr, hcb⟩ := hC.sqr sb
  rw [hrdi, hrsi] at hv
  rw [hrdi, hrsp] at hfr
  rw [hrsp] at hcr
  rw [hrbx] at hcb
  show ChainInv _ _ _ _ ((⟨none, none, none, none⟩ : Env).set Buf.b0 (some 2)) (C sqrSym sb)
  refine chainInv_write hsep hpre hcr hcb hfr fun e he => ?_
  have h2 : (2 : Nat) = e := Option.some.inj he
  subst h2
  rw [feO_base, show (0 : Int) + 0 = 0 from rfl] at hv
  show feO (C sqrSym sb).mem (sa.regs "%rsp") 0 = _
  rw [hv, hm, feO_write64 _ _ _ _ _ hslot]

/-- The body of segment 265: the output pointer back from its stack slot, and the
    arguments of the last multiply. -/
theorem runExitBody (sa : AState) :
    let s' := runBlockA sa
      [.loadMem "%rdi" "%rsp" 128, .lea "%rsi" "%rsp" "%rsp" 0 32,
       .lea "%rdx" "%rsp" "%rsp" 0 0]
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 128)
      ∧ s'.regs "%rsi" = sa.regs "%rsp" + BitVec.ofInt 64 32
      ∧ s'.regs "%rdx" = sa.regs "%rsp" + BitVec.ofInt 64 0 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 32 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 0 = _
    exact leaZero _ _

theorem segsRunA_exit (C : ACallModel) (s : AState) :
    segsRunA C s Ed25519InvertShipped.ed25519InvertShippedSeg265
      = C mulSym (runBlockA s [.loadMem "%rdi" "%rsp" 128, .lea "%rsi" "%rsp" "%rsp" 0 32,
          .lea "%rdx" "%rsp" "%rsp" 0 0]) := rfl

/-- The last segment, appended by the stack-clearing pass: a store of zero to the saved
    output pointer at `128(%rsp)`. -/
theorem segsRunA_clear (C : ACallModel) (s : AState) :
    segsRunA C s Ed25519InvertShipped.ed25519InvertShippedSeg266
      = runBlockA s [.storeMem "%rsp" 128 (.imm 0)] := rfl

/-- A store of zero to `c(%rsp)` leaves the four limbs at `Q` unchanged when they are
    disjoint from that word. -/
theorem feO_clearSlot (c : Int) (hc : c % 8 = 0) {t : AState} {Q : BitVec 64}
    (hq : RangeDisj Q 0 24 (t.regs "%rsp") c c) :
    feO (runBlockA t [.storeMem "%rsp" c (.imm 0)]).mem Q 0 = feO t.mem Q 0 := by
  simp only [runBlockA, evalInstrA, writeAddr]
  refine feO_write64 _ _ _ _ _ fun j hj => ?_
  have hr : 0 ≤ j ∧ j ≤ 24 ∧ j % 8 = 0 := by
    simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  exact (hq (0 + j) c (by omega) (by omega) (by omega) le_rfl le_rfl hc).symm

/-- **The shipped `ed25519_invert` over callees at their specifications.** For a state
    whose input buffer is disjoint from the inversion frame, whose output buffer is disjoint
    from the saved output pointer at `128(%rsp)` and whose input is below `2 ^ 255 - 19`,
    the four-limb value at the output pointer after the block is the input raised to
    `2 ^ 255 - 21` modulo `2 ^ 255 - 19`. -/
theorem invertShipped_correct_addr {C : ACallModel} (hC : InvertCallees C) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (hout : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") 128 128) :
    feO (segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedBlock).mem
        (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM := by
  rw [invertBlock_eq]
  simp only [segsRunA_append]
  have h2 := chainRun hC hz hsep invertSteps invertEnv1 _ (invertEntry hC sa hsep)
  rw [invertEnv_final] at h2
  set s2 := segsRunA C (segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedSeg001)
    (invertSteps.map segOfStep) with hs2
  obtain ⟨hm, hrsp, hrdi, hrsi, hrdx⟩ := runExitBody s2
  set sb := runBlockA s2 [JInstr.loadMem "%rdi" "%rsp" 128,
    JInstr.lea "%rsi" "%rsp" "%rsp" 0 32, JInstr.lea "%rdx" "%rsp" "%rsp" 0 0] with hsb
  rw [h2.rsp] at hrsp hrdi hrsi hrdx
  rw [h2.outp] at hrdi
  have hargs : ArgsBelowSep sb := by
    refine ⟨?_, ?_⟩
    · rw [hrsi, hrsp]
      exact srcBelowSep hsep (.buf .b1)
    · rw [hrdx, hrsp]
      exact srcBelowSep hsep (.buf .b0)
  obtain ⟨hv, -, hcsp, -⟩ := hC.mul sb hargs
  have hq : RangeDisj (sa.regs "%rdi") 0 24 ((C mulSym sb).regs "%rsp") 128 128 := by
    rw [hcsp, hrsp]; exact hout
  rw [hrdi, hrsi, hrdx, hm, feO_base, feO_base] at hv
  rw [segsRunA_exit, ← hsb, segsRunA_clear, feO_clearSlot 128 (by decide) hq, hv,
    show (32 : Int) + 0 = bufOff Buf.b1 from rfl,
    show (0 : Int) + 0 = bufOff Buf.b0 from rfl,
    h2.vals Buf.b1 _ rfl, h2.vals Buf.b0 _ rfl, pow_mul_mod]
  norm_num [pM]

/-- The prime `2 ^ 255 - 19`, by the nested Lucas certificate of `P25519PrimeCert`. -/
theorem pM_prime : Nat.Prime pM := by
  have h : pM = CatCrypt.Crypto.Util.P25519PrimeCert.p25519lit := by
    unfold pM CatCrypt.Crypto.Util.P25519PrimeCert.p25519lit
    norm_num
  rw [h]
  exact CatCrypt.Crypto.Util.P25519PrimeCert.p25519lit_prime

/-- **The shipped `ed25519_invert` computes the field inverse.** For a nonzero input below
    `2 ^ 255 - 19` the four-limb value at the output pointer is the inverse of the input in
    `ZMod (2 ^ 255 - 19)`. -/
theorem invertShipped_inv_zmod {C : ACallModel} (hC : InvertCallees C) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (hout : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") 128 128)
    (hnz : feO sa.mem (sa.regs "%rsi") 0 ≠ 0) :
    ((feO (segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedBlock).mem
          (sa.regs "%rdi") 0 : Nat) : ZMod pM)
      * (feO sa.mem (sa.regs "%rsi") 0 : ZMod pM) = 1 := by
  have : Fact (Nat.Prime pM) := ⟨pM_prime⟩
  rw [invertShipped_correct_addr hC sa hsep hz hout, ZMod.natCast_mod, Nat.cast_pow]
  set z : Nat := feO sa.mem (sa.regs "%rsi") 0 with hzdef
  have hne : (z : ZMod pM) ≠ 0 := by
    intro h
    have hv := ZMod.val_cast_of_lt hz
    rw [h] at hv
    exact hnz (by simpa using hv.symm)
  rw [← pow_succ, show pM - 2 + 1 = pM - 1 from by unfold pM; omega]
  have hcard : Fintype.card (ZMod pM) = pM := ZMod.card pM
  have := FiniteField.pow_card_sub_one_eq_one (a := (z : ZMod pM)) hne
  rwa [hcard] at this

/-- **The shipped `ed25519_invert` over the shipped callees.** For a state whose input
    buffer is disjoint from the inversion frame, whose output buffer is disjoint from
    `128(%rsp)` and whose input is below `2 ^ 255 - 19`, the four-limb value at the output
    pointer after the block, run with each callee symbol
    at the shipped block of that function, is the input raised to `2 ^ 255 - 21` modulo
    `2 ^ 255 - 19`. -/
theorem invertShipped_correct (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (hout : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") 128 128) :
    feO (segsRunA invertCallModel sa
        Ed25519InvertShipped.ed25519InvertShippedBlock).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM :=
  invertShipped_correct_addr invertCallees_invertCallModel sa hsep hz hout

/-- **The shipped `ed25519_invert` inverts in `ZMod (2 ^ 255 - 19)`.** -/
theorem invertShipped_inv (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (hout : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") 128 128)
    (hnz : feO sa.mem (sa.regs "%rsi") 0 ≠ 0) :
    ((feO (segsRunA invertCallModel sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).mem (sa.regs "%rdi") 0 : Nat)
        : ZMod pM)
      * (feO sa.mem (sa.regs "%rsi") 0 : ZMod pM) = 1 :=
  invertShipped_inv_zmod invertCallees_invertCallModel sa hsep hz hout hnz

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
