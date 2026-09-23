/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof

/-!
# The memory frame of the shipped `ed25519_invert`

`Imported.Ed25519InvertShipped.ed25519InvertShippedBlock`, run over callees at the
specifications of `Ed25519InvertChain`, writes only the four field slots and the
output-pointer slot of its frame, the eighteen words its callees use below `%rsp`, and the
32 bytes at its output pointer. A caller keeps every other byte across the call.

## Main definitions

* `OutsideInvFrame`: a byte outside the thirty-five words from `%rsp - 144` to `%rsp + 128`.
* `InvertFrame`: two memories agree outside those words and the four words at the output.

## Main results

* `frameCS_outside`, `stepFrame`, `chainRunFrame`: a call writing one field slot, one step
  of the chain, and a list of steps leave every byte outside the frame.
* `invertShipped_frame`: the frame of the whole block.
* `read64_invertFrame`: a word outside the frame and the output reads back unchanged.
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

/-- `x` lies outside the thirty-five words from `sp - 144` to `sp + 128`: the field slots
    and the output-pointer slot of the inversion frame, and the eighteen words its callees
    use below `sp`. -/
def OutsideInvFrame (sp x : BitVec 64) : Prop :=
  ∀ k, k < 35 → ¬ InRange8 (redBase sp + BitVec.ofInt 64 (8 * k : Nat)) x

/-- `m'` differs from `m` only in the thirty-five words from `sp - 144` to `sp + 128` and
    the four words at `op`. -/
def InvertFrame (m m' : AMem) (sp op : BitVec 64) : Prop :=
  ∀ x, OutsideInvFrame sp x →
    (∀ k, k < 4 → ¬ InRange8 (op + BitVec.ofInt 64 (8 * k : Nat)) x) → m' x = m x

theorem outsideInvFrame_word {sp x : BitVec 64} (hx : OutsideInvFrame sp x) (o : Int)
    (k : Nat) (hk : 8 * k = o + 144) (hk' : k < 35) :
    ¬ InRange8 (sp + BitVec.ofInt 64 o) x := by
  have h := hx k hk'
  rwa [redBase, addI, show (-144 : Int) + ((8 * k : Nat) : Int) = o from by omega] at h

/-- A call writing one field slot leaves every byte outside the inversion frame. -/
theorem frameCS_outside {m m' : AMem} {sp x : BitVec 64} {d : Buf}
    (hf : FrameCS m m' (sp + BitVec.ofInt 64 (bufOff d)) 4 sp) (hx : OutsideInvFrame sp x) :
    m' x = m x := by
  refine hf x (fun k hk => ?_) (fun k hk => hx k (by omega))
  rw [addI]
  rcases bufOff_mem d with h | h | h | h <;> rw [h] <;>
    exact outsideInvFrame_word hx _ (((bufOff d + 144) / 8).toNat + k)
      (by rw [h]; omega) (by rw [h]; omega)

/-- One step of the chain leaves every byte outside the inversion frame. -/
theorem stepFrame {C : ACallModel} (hC : InvertCallees C) {SP IP OP : BitVec 64} {z : Nat}
    (hsep : ChainSep SP IP) {E : Env} {sa : AState} (hinv : ChainInv SP IP OP z E sa)
    (s : Step) (x : BitVec 64) (hx : OutsideInvFrame SP x) :
    (segsRunA C sa [segOfStep s]).mem x = sa.mem x := by
  cases s with
  | sqr d a =>
    obtain ⟨hm, hrsp, -, hrdi, -⟩ := runSqrBody sa d a
    set sb := runBlockA sa (segOfStep (Step.sqr d a)).body with hsb
    obtain ⟨-, hfr, -, -⟩ := hC.sqr sb
    rw [hinv.rsp] at hrsp hrdi
    rw [hrdi, hrsp, hm] at hfr
    exact frameCS_outside hfr hx
  | mul d a b =>
    obtain ⟨hm, hrsp, hrbx, hrdi, hrsi, hrdx⟩ := runMulBody sa d a b
    set sb := runBlockA sa (segOfStep (Step.mul d a b)).body with hsb
    rw [hinv.rsp] at hrsp hrdi
    rw [hinv.rsp, hinv.rbx] at hrsi hrdx
    have hargs : ArgsBelowSep sb := ⟨by rw [hrsi, hrsp]; exact srcBelowSep hsep a,
      by rw [hrdx, hrsp]; exact srcBelowSep hsep b⟩
    obtain ⟨-, hfr, -, -⟩ := hC.mul sb hargs
    rw [hrdi, hrsp, hm] at hfr
    exact frameCS_outside hfr hx

/-- A list of steps of the chain leaves every byte outside the inversion frame. -/
theorem chainRunFrame {C : ACallModel} (hC : InvertCallees C) {SP IP OP : BitVec 64}
    {z : Nat} (hz : z < pM) (hsep : ChainSep SP IP) (x : BitVec 64)
    (hx : OutsideInvFrame SP x) :
    ∀ (steps : List Step) (E : Env) (sa : AState), ChainInv SP IP OP z E sa →
      (segsRunA C sa (steps.map segOfStep)).mem x = sa.mem x := by
  intro steps
  induction steps with
  | nil => intro E sa _; rfl
  | cons s rest ih =>
    intro E sa h
    rw [List.map_cons, show (segOfStep s :: rest.map segOfStep)
      = [segOfStep s] ++ rest.map segOfStep from rfl, segsRunA_append,
      ih (stepEnv E s) _ (chainStep hC hz hsep h s), stepFrame hC hsep h s x hx]

/-- **The frame of the shipped `ed25519_invert`.** Over callees at their specifications,
    for a state whose input buffer is disjoint from the inversion frame and whose input is
    below `2 ^ 255 - 19`, the block changes no byte outside the thirty-five words from
    `%rsp - 144` to `%rsp + 128` and the four words at the output pointer. -/
theorem invertShipped_frame {C : ACallModel} (hC : InvertCallees C) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM) :
    InvertFrame sa.mem (segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedBlock).mem
      (sa.regs "%rsp") (sa.regs "%rdi") := by
  intro x hx hop
  rw [invertBlock_eq]
  simp only [segsRunA_append]
  have h1 := invertEntry hC sa hsep
  have h2 := chainRun hC hz hsep invertSteps invertEnv1 _ h1
  set s1 := segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedSeg001 with hs1
  set s2 := segsRunA C s1 (invertSteps.map segOfStep) with hs2
  -- the last segment
  obtain ⟨hm, hrsp, hrdi, -, -⟩ := runExitBody s2
  set sb := runBlockA s2 [JInstr.loadMem "%rdi" "%rsp" 128,
    JInstr.lea "%rsi" "%rsp" "%rsp" 0 32, JInstr.lea "%rdx" "%rsp" "%rsp" 0 0] with hsb
  rw [h2.rsp] at hrsp hrdi
  rw [h2.outp] at hrdi
  have hargs : ArgsBelowSep sb := by
    obtain ⟨-, -, -, hrsi, hrdx⟩ := runExitBody s2
    rw [h2.rsp] at hrsi hrdx
    refine ⟨?_, ?_⟩
    · rw [hrsi, hrsp]
      exact srcBelowSep hsep (.buf .b1)
    · rw [hrdx, hrsp]
      exact srcBelowSep hsep (.buf .b0)
  obtain ⟨-, hfr, hcsp, -⟩ := hC.mul sb hargs
  rw [hrdi, hrsp, hm] at hfr
  rw [segsRunA_exit, ← hsb, segsRunA_clear]
  simp only [runBlockA, evalInstrA, writeAddr]
  rw [write64_of_not_inRange _ _ _ _ (by
      rw [hcsp, hrsp]; exact outsideInvFrame_word hx 128 34 (by omega) (by omega)),
    hfr x hop (fun k hk => hx k (by omega)),
    hs2, chainRunFrame hC hz hsep x hx invertSteps invertEnv1 s1 h1]
  -- the first segment
  obtain ⟨hm1, hrsp1, -, hrdi1, -⟩ := runEntryBody sa
  set sc := runBlockA sa
    [JInstr.mov "%rbx" (.reg "%rsi"), JInstr.storeMem "%rsp" 128 (.reg "%rdi"),
     JInstr.lea "%rdi" "%rsp" "%rsp" 0 0, JInstr.mov "%rsi" (.reg "%rbx")] with hsc
  obtain ⟨-, hfr1, -, -⟩ := hC.sqr sc
  rw [hrdi1, hrsp1] at hfr1
  show (C sqrSym sc).mem x = sa.mem x
  rw [frameCS_outside (d := Buf.b0) hfr1 hx, hm1]
  exact write64_of_not_inRange _ _ _ _ (outsideInvFrame_word hx 128 34 (by omega) (by omega))

/-- A word disjoint from the inversion frame and from the output reads back unchanged. -/
theorem read64_invertFrame {m m' : AMem} {sp op : BitVec 64} (hf : InvertFrame m m' sp op)
    (b : BitVec 64)
    (hd : ∀ k, k < 35 → Disjoint8 (redBase sp + BitVec.ofInt 64 (8 * k : Nat)) b)
    (ho : ∀ k, k < 4 → Disjoint8 (op + BitVec.ofInt 64 (8 * k : Nat)) b) :
    read64 m' b = read64 m b := by
  have key : ∀ i : Nat, i < 8 → m' (b + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) :=
    fun i hi => hf _ (fun k hk => not_inRange_of_disjoint _ _ i (hd k hk) hi)
      (fun k hk => not_inRange_of_disjoint _ _ i (ho k hk) hi)
  have h0 : m' b = m b := by simpa using key 0 (by decide)
  simp only [read64, h0, key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide)]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
