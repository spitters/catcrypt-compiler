/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The VALUE identity for the Jacobian point-DOUBLE: `jacDblBlock` realizes `jacDoubleGen`

`EcJacDblBlock.lean` assembles the straight-line frame-wrapped point-double block
`jacDblBlock` (= `(jacDblCalls.map emitCall).flatten`) and proves its *structural*
facts (denotation-preserving lowering, the field-op counts). It leaves the
**value** identity against `EcProjectiveGeneric.jacDoubleGen` open, gated on the
emitted Montgomery-reduce canonicalisation of each `feMulFrameAt` product.

This module closes that value identity at the **field-element level**, reusing the
`EcJacAddValue` carried-predicate discipline verbatim: the de-Montgomery slot
interpretation `slotFieldVal`, the per-op realizer `FieldOpRealized`, the threaded
trajectory machinery (`runBlock_flatten_map`, `threadState`, `slotFieldVal_const`),
and — for non-vacuity — the three named cross-prover field-op bridges
(`EcJacAddValue.deMont_montMul` via `EcJacAddMontReduceBridge.feMulFrameAtReduced`
+ `AUCurvesMontReduceFaithful`; `EcJacAddValue.deMont_canonAdd` /
`EcJacAddValue.deMont_canonSub` via `AUCurvesFieldAddSubFaithful`). The integration
algebra — that threading the 19 per-op field realizers through `jacDblCalls`
accumulates to the `dbl-2009-l` formula `jacDoubleGen` — is fully Lean-proved here
(`ring` over the field interpretation `ZMod N`).

## What is proved here

`jacDblBlock_realizes_jacDblGen`: given a `JacDblRealized` witness — the 19 per-op
field realizers along the `runBlock`-threaded trajectory, plus the input slots
holding `P = (X,Y,Z)` — running `jacDblBlock` leaves the output slots
`sX3`/`sY3`/`sZ3` holding exactly the field coordinates of `jacDoubleGen X Y Z`.
The carried realizers are satisfiable from the same bricks the Jacobian-add
vertical adopts (`EcJacAddValue` §7), so this is non-vacuous, never a `rfl`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblValue

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue

/-! ## 1. The field interpretation and per-op realizer (reused from `EcJacAddValue`)

The de-Montgomery slot interpretation `EcJacAddValue.slotFieldVal`, the per-op
`ZMod N` field op `EcJacAddValue.callOp` / output-input slot projections
`callOut`/`callIn0`/`callIn1`, and the carried per-op realizer
`EcJacAddValue.FieldOpRealized` are all reused as-is — they are stated over an
arbitrary `JacFieldCall` (the shared call type), so the double's calls feed them
directly. -/

variable {N : Nat} [NeZero N]

/-! ## 2. Threading the double's call list

`runBlock` over the assembled `jacDblBlock` is the left fold of `runBlock ∘
emitCall` over `jacDblCalls`. Same composition law as the add
(`EcJacAddValue.runBlock_flatten_map`). -/

/-- The state after running the first `n` calls of `jacDblCalls` from `s0`. -/
def threadState (s0 : JState 64) (cs : List JacFieldCall) : JState 64 :=
  cs.foldl (fun st c => runBlock st (emitCall c)) s0

@[simp] theorem threadState_nil (s0 : JState 64) : threadState s0 [] = s0 := rfl

@[simp] theorem threadState_cons (s0 : JState 64) (c : JacFieldCall) (cs : List JacFieldCall) :
    threadState s0 (c :: cs) = threadState (runBlock s0 (emitCall c)) cs := rfl

/-- `runBlock` of the assembled double block equals the threaded final state. -/
theorem runBlock_jacDblBlock (s0 : JState 64) :
    runBlock s0 jacDblBlock = threadState s0 jacDblCalls := by
  rw [jacDblBlock, runBlock_flatten_map]; rfl

/-! ## 3. The realizer bundle and the headline

`JacDblRealized N base s0` carries the per-op realizers along the trajectory
threaded from `s0`. The output slots' field values in the final state are read off
by accumulating the realizers — exactly as `EcJacAddValue.JacAddRealized`. -/

/-- The threaded states, one before each call (the realizer trajectory). -/
def trajState (s0 : JState 64) (k : Nat) : JState 64 :=
  threadState s0 (jacDblCalls.take k)

/-- **The carried realizer bundle for the whole point-double.** For each call
    index `k < 19` it carries a `FieldOpRealized` witness at the threaded
    pre-state `trajState s0 k` for `jacDblCalls[k]`. Holding it = adopting the
    per-op AUCurves-canonicalised field realizers (multiply via
    `feMulFrameAtReduced`, add/sub via the add/sub bridge) all along the
    straight-line composition. -/
structure JacDblRealized (N : Nat) (base : String) (s0 : JState 64) : Prop where
  /-- Each call realizes its field op at its threaded pre-state. -/
  realizes : ∀ (k : Nat) (h : k < jacDblCalls.length),
    FieldOpRealized N base (jacDblCalls[k]'h)
      (trajState s0 k) (trajState s0 (k + 1))

/-- One threaded step of the trajectory unfolds `trajState` by one call. -/
theorem trajState_succ (s0 : JState 64) (k : Nat) (h : k < jacDblCalls.length) :
    trajState s0 (k + 1) = runBlock (trajState s0 k) (emitCall (jacDblCalls[k]'h)) := by
  unfold trajState
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, threadState]
  rw [List.foldl_append]
  rfl

/-- The final threaded state is `trajState s0 19`. -/
theorem trajState_full (s0 : JState 64) :
    threadState s0 jacDblCalls = trajState s0 jacDblCalls.length := by
  unfold trajState; rw [List.take_length]

/-! ### Slot-value preservation across a suffix

If a slot is the output of no call in the range `[k, m)`, its field value at step
`m` equals its value at step `k` — the non-interference carry. -/

omit [NeZero N] in
/-- A slot untouched by calls `k, …, k+d-1` keeps its field value from step `k` to
    step `k+d` (`others` applied along the suffix). -/
theorem slotFieldVal_preserved
    {base : String} {s0 : JState 64} (R : JacDblRealized N base s0)
    (slot : Nat) :
    ∀ (d k : Nat) (_hk : k + d ≤ jacDblCalls.length),
      (∀ j (hj : j < jacDblCalls.length), k ≤ j → j < k + d →
        slot ≠ callOut (jacDblCalls[j]'hj))
      → slotFieldVal N (trajState s0 (k + d)) base slot
        = slotFieldVal N (trajState s0 k) base slot := by
  intro d
  induction d with
  | zero => intro k _ _; rfl
  | succ d ih =>
      intro k hk hno
      have hk1 : (k + 1) + d ≤ jacDblCalls.length := by omega
      have hkk : k < jacDblCalls.length := by omega
      have e1 : slotFieldVal N (trajState s0 ((k + 1) + d)) base slot
          = slotFieldVal N (trajState s0 (k + 1)) base slot := by
        apply ih (k + 1) hk1
        intro j hj hj1 hj2
        exact hno j hj (by omega) (by omega)
      have e0 : slotFieldVal N (trajState s0 (k + 1)) base slot
          = slotFieldVal N (trajState s0 k) base slot :=
        (R.realizes k hkk).others slot (hno k hkk (by omega) (by omega))
      have hidx : k + (d + 1) = (k + 1) + d := by omega
      rw [hidx, e1, e0]

omit [NeZero N] in
/-- Corollary: if `slot` is written by no call in `[k, m)` (`k ≤ m ≤ 19`), its
    field value agrees at steps `k` and `m`. -/
theorem slotFieldVal_const
    {base : String} {s0 : JState 64} (R : JacDblRealized N base s0)
    (slot k m : Nat) (hkm : k ≤ m) (hm : m ≤ jacDblCalls.length)
    (hno : ∀ j (hj : j < jacDblCalls.length), k ≤ j → j < m →
      slot ≠ callOut (jacDblCalls[j]'hj)) :
    slotFieldVal N (trajState s0 m) base slot = slotFieldVal N (trajState s0 k) base slot := by
  have hd : m = k + (m - k) := by omega
  rw [hd]
  exact slotFieldVal_preserved R slot (m - k) k (by omega)
    (fun j hj hj1 hj2 => hno j hj hj1 (by omega))

/-! ## 4. Spec coordinates and the all-inputs value identity

`jacDoubleGen` of the input field coordinates; `slotFieldVal` reads the three
input slots as field elements. The headline reads the three output slots off the
final threaded state. -/

/-- The `ZMod N` input coordinates read from the three input slots of the start
    state. -/
def inX (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sX
def inY (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sY
def inZ (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sZ

omit [NeZero N] in
/-- **The all-inputs VALUE identity: `jacDblBlock` realizes `jacDoubleGen`.**

    Given the carried per-op field realizers `R` (each `jacDblCalls` op realizes
    its `ZMod N` field op along the `runBlock`-threaded trajectory — multiply via
    `EcJacAddMontReduceBridge.feMulFrameAtReduced`/`AUCurvesMontReduceFaithful`,
    add/sub via the add/sub canonicalisation bridge), running `jacDblBlock` from a
    start state `s0` whose input slots hold `P = (X,Y,Z)` (in the de-Montgomery
    `slotFieldVal` interpretation) leaves the three output slots `sX3`/`sY3`/`sZ3`
    holding exactly the field coordinates of
    `EcProjectiveGeneric.jacDoubleGen X Y Z`.

    The integration algebra — threading the 19 field realizers through
    `jacDblCalls` accumulates to the `dbl-2009-l` formula — is fully Lean-proved
    (`ring` over `ZMod N`). The two trust edges are the named per-op
    canonicalisations carried in `R`, reused from the Jacobian-add vertical. -/
theorem jacDblBlock_realizes_jacDblGen
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacDblRealized N base s0) :
    (slotFieldVal N (runBlock s0 jacDblBlock) base EcJacDblBlock.sX3,
     slotFieldVal N (runBlock s0 jacDblBlock) base EcJacDblBlock.sY3,
     slotFieldVal N (runBlock s0 jacDblBlock) base EcJacDblBlock.sZ3)
      = EcProjectiveGeneric.jacDoubleGen
          (inX N s0 base) (inY N s0 base) (inZ N s0 base) := by
  -- final state = trajState at length 19
  rw [runBlock_jacDblBlock, trajState_full]
  set V : Nat → ZMod N := fun slot => slotFieldVal N (trajState s0 jacDblCalls.length) base slot
    with hV
  have len : jacDblCalls.length = 19 := by decide
  -- the value of a slot at its settle step `k` equals its final value, when the
  -- slot is written by no call in `[k, 19)` (SSA single-assignment).
  have align : ∀ (k : Nat) (_hk : k ≤ jacDblCalls.length) (slot : Nat),
      (∀ j (hj : j < jacDblCalls.length), k ≤ j → slot ≠ callOut (jacDblCalls[j]'hj)) →
      slotFieldVal N (trajState s0 k) base slot = V slot := by
    intro k hk slot hno
    rw [hV]
    exact (slotFieldVal_const R slot k jacDblCalls.length hk le_rfl
      (fun j hj hj1 _ => hno j hj hj1)).symm
  -- the per-call value step, fully aligned to the final values `V`.
  have callV : ∀ (k : Nat) (hk : k < jacDblCalls.length)
      (hout : ∀ j (hj : j < jacDblCalls.length), k + 1 ≤ j →
        callOut (jacDblCalls[k]'hk) ≠ callOut (jacDblCalls[j]'hj))
      (hin0 : ∀ j (hj : j < jacDblCalls.length), k ≤ j →
        callIn0 (jacDblCalls[k]'hk) ≠ callOut (jacDblCalls[j]'hj))
      (hin1 : ∀ j (hj : j < jacDblCalls.length), k ≤ j →
        callIn1 (jacDblCalls[k]'hk) ≠ callOut (jacDblCalls[j]'hj)),
      V (callOut (jacDblCalls[k]'hk))
        = callOp (jacDblCalls[k]'hk)
            (V (callIn0 (jacDblCalls[k]'hk))) (V (callIn1 (jacDblCalls[k]'hk))) := by
    intro k hk hout hin0 hin1
    have hLHS : V (callOut (jacDblCalls[k]'hk))
        = slotFieldVal N (trajState s0 (k + 1)) base (callOut (jacDblCalls[k]'hk)) := by
      rw [hV]
      exact slotFieldVal_const R _ (k + 1) jacDblCalls.length hk le_rfl
        (fun j hj hj1 _ => hout j hj hj1)
    have hI0 := align k (le_of_lt hk) (callIn0 (jacDblCalls[k]'hk))
      (fun j hj hj1 => hin0 j hj hj1)
    have hI1 := align k (le_of_lt hk) (callIn1 (jacDblCalls[k]'hk))
      (fun j hj hj1 => hin1 j hj hj1)
    rw [hLHS, (R.realizes k hk).out_val, hI0, hI1]
  clear align
  -- Instantiate `callV` at each concrete call; the non-write side conditions are
  -- `decide`-discharged (distinct slot numerals).
  have c0 : V 6 = V 1 * V 1 := by
    exact callV 0 (by decide) (by decide) (by decide) (by decide)
  have c1 : V 8 = V 0 * V 6 := by
    exact callV 1 (by decide) (by decide) (by decide) (by decide)
  have c2 : V 10 = V 8 + V 8 := by
    exact callV 2 (by decide) (by decide) (by decide) (by decide)
  have c3 : V 11 = V 10 + V 10 := by
    exact callV 3 (by decide) (by decide) (by decide) (by decide)
  have c4 : V 12 = V 0 * V 0 := by
    exact callV 4 (by decide) (by decide) (by decide) (by decide)
  have c5 : V 14 = V 12 + V 12 := by
    exact callV 5 (by decide) (by decide) (by decide) (by decide)
  have c6 : V 15 = V 14 + V 12 := by
    exact callV 6 (by decide) (by decide) (by decide) (by decide)
  have c7 : V 16 = V 15 * V 15 := by
    exact callV 7 (by decide) (by decide) (by decide) (by decide)
  have c8 : V 18 = V 11 + V 11 := by
    exact callV 8 (by decide) (by decide) (by decide) (by decide)
  have c9 : V 3 = V 16 - V 18 := by
    exact callV 9 (by decide) (by decide) (by decide) (by decide)
  have c10 : V 19 = V 11 - V 3 := by
    exact callV 10 (by decide) (by decide) (by decide) (by decide)
  have c11 : V 20 = V 15 * V 19 := by
    exact callV 11 (by decide) (by decide) (by decide) (by decide)
  have c12 : V 22 = V 6 * V 6 := by
    exact callV 12 (by decide) (by decide) (by decide) (by decide)
  have c13 : V 24 = V 22 + V 22 := by
    exact callV 13 (by decide) (by decide) (by decide) (by decide)
  have c14 : V 25 = V 24 + V 24 := by
    exact callV 14 (by decide) (by decide) (by decide) (by decide)
  have c15 : V 26 = V 25 + V 25 := by
    exact callV 15 (by decide) (by decide) (by decide) (by decide)
  have c16 : V 4 = V 20 - V 26 := by
    exact callV 16 (by decide) (by decide) (by decide) (by decide)
  have c17 : V 28 = V 1 * V 2 := by
    exact callV 17 (by decide) (by decide) (by decide) (by decide)
  have c18 : V 5 = V 28 + V 28 := by
    exact callV 18 (by decide) (by decide) (by decide) (by decide)
  clear callV
  -- unfold the goal's spec and read the three output slots off `V`.
  simp only [EcProjectiveGeneric.jacDoubleGen, inX, inY, inZ,
    sX, sY, sZ, EcJacDblBlock.sX3, EcJacDblBlock.sY3, EcJacDblBlock.sZ3, Prod.mk.injEq]
  -- the input slots are written by no call, so their value at s0 = their final V.
  have iX : slotFieldVal N s0 base 0 = V 0 :=
    (slotFieldVal_const R 0 0 jacDblCalls.length (by omega) le_rfl (by decide)).symm
  have iY : slotFieldVal N s0 base 1 = V 1 :=
    (slotFieldVal_const R 1 0 jacDblCalls.length (by omega) le_rfl (by decide)).symm
  have iZ : slotFieldVal N s0 base 2 = V 2 :=
    (slotFieldVal_const R 2 0 jacDblCalls.length (by omega) le_rfl (by decide)).symm
  rw [iX, iY, iZ]
  -- fold the three output-slot reads to `V 3 / V 4 / V 5`.
  have oX3 : slotFieldVal N (trajState s0 jacDblCalls.length) base 3 = V 3 := rfl
  have oY3 : slotFieldVal N (trajState s0 jacDblCalls.length) base 4 = V 4 := rfl
  have oZ3 : slotFieldVal N (trajState s0 jacDblCalls.length) base 5 = V 5 := rfl
  rw [oX3, oY3, oZ3]
  -- substitute bottom-up (outputs first, then dependencies) until everything is in
  -- the three input values `V 0, V 1, V 2`; close by `ring`.
  rw [c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ## 5. Non-vacuity: the carried realizers are satisfiable from the bricks

The `FieldOpRealized` predicate is **not** an unsatisfiable over-constraint: each
op tag's realizer is exactly the de-Montgomery image of a proven brick value plus
its named AUCurves canonicalisation — the very facts the Jacobian-add vertical
exhibits in `EcJacAddValue` §7 and re-exported here:

* a multiply realizer's field content is `EcJacAddValue.deMont_montMul` (carrying
  `EcJacAddMontReduceBridge.feMulFrameAtReduced` + `AUCurvesMontReduceFaithful`);
* an add realizer's is `EcJacAddValue.deMont_canonAdd` and a sub realizer's is
  `EcJacAddValue.deMont_canonSub`, both via
  `EcJacAddValue.AUCurvesFieldAddSubFaithful` (the mirror of the mont-reduce
  bridge for the add/sub conditional subtract).

`jacDblCalls` uses only these three op tags, so a `JacDblRealized N base s0` is
satisfiable from exactly the bricks the add vertical adopts — the headline
`jacDblBlock_realizes_jacDblGen` then proves the whole-point-double value identity
against `EcProjectiveGeneric.jacDoubleGen` purely algebraically over them. -/

omit [NeZero N] in
/-- **Non-vacuity, multiply leg (re-exported).** The field content a `mul`
    `FieldOpRealized.out_val` carries is the de-Montgomery image of the
    AUCurves-canonicalised Montgomery field product — exactly
    `EcJacAddValue.deMont_montMul`, reused unchanged. -/
theorem dbl_mul_realizer_content [Fact (Nat.Prime N)]
    (Nprime a b : Nat) (hodd : N ≠ 2) (hNleR : N ≤ 2 ^ 256)
    (ha : a < N) (hb : b < N) (hNprime : (N * Nprime) % 2 ^ 256 = 2 ^ 256 - 1) :
    deMont N (EcJacAddMontReduceBridge.montMulFieldElem N Nprime a b)
      = deMont N a * deMont N b :=
  EcJacAddValue.deMont_montMul Nprime a b hodd hNleR ha hb hNprime

omit [NeZero N] in
/-- **Non-vacuity, add leg (re-exported).** The field content an `add`
    `FieldOpRealized.out_val` carries is `EcJacAddValue.deMont_canonAdd`, reused
    unchanged. -/
theorem dbl_add_realizer_content (r a b : Nat) (hr : r < 2 * N)
    (hcong : r ≡ a + b [MOD N]) :
    deMont N (EcJacAddMontReduceBridge.canonReduce N r) = deMont N a + deMont N b :=
  EcJacAddValue.deMont_canonAdd r a b hr hcong

omit [NeZero N] in
/-- **Non-vacuity, sub leg (re-exported).** The field content a `sub`
    `FieldOpRealized.out_val` carries is `EcJacAddValue.deMont_canonSub`, reused
    unchanged. -/
theorem dbl_sub_realizer_content (r a b : Nat) (hr : r < 2 * N)
    (hcong : (r : ZMod N) = (a : ZMod N) - (b : ZMod N)) :
    deMont N (EcJacAddMontReduceBridge.canonReduce N r) = deMont N a - deMont N b :=
  EcJacAddValue.deMont_canonSub r a b hr hcong

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblValue
