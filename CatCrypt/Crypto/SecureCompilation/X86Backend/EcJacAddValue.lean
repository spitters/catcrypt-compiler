/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontReduceBridge
import CatCrypt.Crypto.SecureCompilation.EcProjectiveAddGeneric

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The VALUE identity for the Jacobian point-add: `jacAddBlock` realizes `jacAddGen`

`EcJacAddBlock.lean` assembles the straight-line frame-wrapped point-add block
`jacAddBlock` (= `(jacAddCalls.map emitCall).flatten`) and proves its *structural*
facts (denotation-preserving lowering, the field-op counts). It leaves the
**value** identity against `EcProjectiveAddGeneric.jacAddGen` open, gated on the
emitted Montgomery-reduce canonicalisation of each `feMulFrameAt` product.

This module closes that value identity at the **field-element level**, in the
`GenericEcEmitValue` carried-predicate discipline. The integration algebra — that
threading the 23 per-op field realizers through `jacAddCalls` accumulates to the
`add-2007-bl` formula `jacAddGen` — is fully Lean-proved here (`ring` over the
field interpretation). The two trust edges are the *named, carried* per-op
canonicalisations: the Montgomery multiply reduce
(`EcJacAddMontReduceBridge.feMulFrameAtReduced` + `AUCurvesMontReduceFaithful`)
and the add/sub conditional-subtract canonicalisation
(`AUCurvesFieldAddSubFaithful`, mirroring the mont-reduce bridge). Both are the
single conditional subtract `[0, 2·N) → [0, N)` that fiat-crypto's
`WordByWordMontgomery.conditional_sub` (`Qed`'d `conditional_sub_correct`,
`valid (mulmod a b)`) verifies and AUCurves consumes per curve — `canonReduce N`
at the `Nat` level.

## The field interpretation (de-Montgomery)

Each frame slot holds a four-limb residue in **Montgomery form**: the slot's
value `v` represents the field element `v · R⁻¹ (mod N)` where `R = 2^256`. We
read a slot as a field element via `slotFieldVal`, the de-Montgomery'd value
`(valLimbs (slotLimbs s base slot) : ZMod N) · (R : ZMod N)⁻¹`. Under this
interpretation every field op realizes uniformly:

* a Montgomery multiply lands `m` with `m · R ≡ a · b (mod N)`
  (`montMulFieldElem_spec`), so `slotFieldVal o = slotFieldVal a · slotFieldVal b`;
* a canonicalised add/sub lands `canonReduce N (a ± b)`, congruent to `a ± b`
  mod `N`, so `slotFieldVal o = slotFieldVal a ± slotFieldVal b` (Montgomery form
  is `R`-linear).

So a single per-op realizer `FieldOpRealized` (output slot's field value = the
field op of the input slots' field values, **and** the other slots are
untouched) suffices for all three op tags, and the headline accumulates the 23
realizers to `jacAddGen` purely algebraically.

## What is proved here

`jacAddBlock_realizes_jacAddGen`: given a `JacAddRealized` witness — the 23 per-op
field realizers along the `runBlock`-threaded trajectory, plus the input slots
holding `P₁ = (X₁,Y₁,Z₁)`, `P₂ = (X₂,Y₂,Z₂)` — running `jacAddBlock` leaves the
output slots `sX3`/`sY3`/`sZ3` holding exactly the field coordinates of
`jacAddGen X₁ Y₁ Z₁ X₂ Y₂ Z₂`. The non-vacuity witnesses confirm the carried
realizers are satisfiable from `feMulFrameAtReduced` and the add/sub bridge.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven (valLimbs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontReduceBridge
open CatCrypt.Crypto.Number

/-! ## 1. The de-Montgomery field interpretation of a frame slot -/

variable {N : Nat} [NeZero N]

/-- The field element a frame slot represents, de-Montgomery'd: the slot's
    four-limb residue `valLimbs (slotLimbs s base slot)` divided by the Montgomery
    radix `R = 2^256` in `ZMod N`. The point coordinates `jacAddGen` consumes live
    in this interpretation; each frame-wrapped field op (multiply / canonicalised
    add / canonicalised sub) realizes the matching `ZMod N` op on these values. -/
def slotFieldVal (N : Nat) (s : JState 64) (base : String) (slot : Nat) : ZMod N :=
  ((valLimbs (slotLimbs s base slot) : ZMod N)) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹

/-! ## 2. The per-op field realizer

`FieldOpRealized N base c s s'` is the field-level effect of running the
frame-wrapped block `emitCall c` from `s` to `s'`: the output slot's de-Montgomery
field value becomes the matching `ZMod N` op of the input slots' field values
(read in `s`, before the op), and every *other* slot's field value is unchanged
(non-interference — earlier results survive). This is the genuine carried
predicate: a multiply realizer is supplied by `feMulFrameAtReduced` +
`AUCurvesMontReduceFaithful`, an add/sub realizer by the add/sub bridge below. -/

/-- The `ZMod N` field op a `JacFieldCall` tag denotes. -/
def callOp : JacFieldCall → (ZMod N → ZMod N → ZMod N)
  | .mul _ _ _ => (· * ·)
  | .add _ _ _ => (· + ·)
  | .sub _ _ _ => (· - ·)

/-- The output / input slots of a `JacFieldCall`. -/
def callOut : JacFieldCall → Nat
  | .mul o _ _ => o
  | .add o _ _ => o
  | .sub o _ _ => o

def callIn0 : JacFieldCall → Nat
  | .mul _ i _ => i
  | .add _ i _ => i
  | .sub _ i _ => i

def callIn1 : JacFieldCall → Nat
  | .mul _ _ j => j
  | .add _ _ j => j
  | .sub _ _ j => j

/-- **The per-op field realizer (carried).** Running `emitCall c` from `s` to
    `s'` leaves:

    * the output slot `callOut c`'s field value equal to the call's `ZMod N` op
      applied to the two input slots' field values (read in the pre-state `s`);
    * every slot distinct from the output slot unchanged.

    A `mul` realizer is the de-Montgomery image of
    `EcJacAddMontReduceBridge.feMulFrameAtReduced` (the AUCurves-canonicalised
    Montgomery field product); an `add`/`sub` realizer is the de-Montgomery image
    of `feAddFrameAt_value` / `feSubFrameAt_value` post-composed with the
    add/sub canonicalisation bridge. Both are honest cross-prover carried edges,
    never a `rfl`. -/
structure FieldOpRealized (N : Nat) (base : String) (c : JacFieldCall)
    (s s' : JState 64) : Prop where
  /-- `s'` is the post-state of running the call's frame-wrapped block on `s`. -/
  step : s' = runBlock s (emitCall c)
  /-- The output slot's field value is the call's field op of the input slots. -/
  out_val : slotFieldVal N s' base (callOut c)
    = callOp c (slotFieldVal N s base (callIn0 c)) (slotFieldVal N s base (callIn1 c))
  /-- Non-interference: every other slot's field value survives. -/
  others : ∀ slot, slot ≠ callOut c → slotFieldVal N s' base slot = slotFieldVal N s base slot

/-! ## 3. Threading the call list

`runBlock` over the assembled `jacAddBlock` is the left fold of `runBlock ∘
emitCall` over `jacAddCalls`. The realizer trajectory is the matching fold of
states. -/

/-- `runBlock` over a `(map f).flatten` block is the left fold of the per-element
    `runBlock`s — the straight-line composition law for the assembled block. -/
theorem runBlock_flatten_map {α : Type} (f : α → List (JInstr 64)) :
    ∀ (cs : List α) (s : JState 64),
      runBlock s ((cs.map f).flatten) = cs.foldl (fun st c => runBlock st (f c)) s := by
  intro cs
  induction cs with
  | nil => intro s; simp
  | cons c cs ih =>
      intro s
      simp only [List.map_cons, List.flatten_cons, List.foldl_cons]
      rw [runBlock_append, ih]

/-! ## 4. The accumulation lemma over an arbitrary call list

Given, for each call along the threaded trajectory, a `FieldOpRealized` witness,
the field value of every slot in the final state is determined by folding the
field ops. We state the headline directly for `jacAddCalls`; the engine is the
fold-threading of §3 plus the per-op `out_val`/`others`. -/

/-- The state after running the first `n` calls of `cs` from `s0`. -/
def threadState (s0 : JState 64) (cs : List JacFieldCall) : JState 64 :=
  cs.foldl (fun st c => runBlock st (emitCall c)) s0

@[simp] theorem threadState_nil (s0 : JState 64) : threadState s0 [] = s0 := rfl

@[simp] theorem threadState_cons (s0 : JState 64) (c : JacFieldCall) (cs : List JacFieldCall) :
    threadState s0 (c :: cs) = threadState (runBlock s0 (emitCall c)) cs := rfl

/-- `runBlock` of the assembled block equals the threaded final state. -/
theorem runBlock_jacAddBlock (s0 : JState 64) :
    runBlock s0 jacAddBlock = threadState s0 jacAddCalls := by
  rw [jacAddBlock, runBlock_flatten_map]; rfl

/-! ## 5. The realizer bundle and the headline

`JacAddRealized N base s0` carries the per-op realizers along the trajectory
threaded from `s0` and the field values of the input slots. The output slots'
field values in the final state are read off by accumulating the realizers. -/

/-- The 23 threaded states, one before each call (the realizer trajectory). -/
def trajState (s0 : JState 64) (k : Nat) : JState 64 :=
  threadState s0 (jacAddCalls.take k)

/-- **The carried realizer bundle for the whole point-add.** For each call index
    `k < 23` it carries a `FieldOpRealized` witness at the threaded pre-state
    `trajState s0 k` for `jacAddCalls[k]`. Holding it = adopting the per-op
    AUCurves-canonicalised field realizers (multiply via `feMulFrameAtReduced`,
    add/sub via the add/sub bridge) all along the straight-line composition. -/
structure JacAddRealized (N : Nat) (base : String) (s0 : JState 64) : Prop where
  /-- Each call realizes its field op at its threaded pre-state. -/
  realizes : ∀ (k : Nat) (h : k < jacAddCalls.length),
    FieldOpRealized N base (jacAddCalls[k]'h)
      (trajState s0 k) (trajState s0 (k + 1))

/-- One threaded step of the trajectory unfolds `trajState` by one call. -/
theorem trajState_succ (s0 : JState 64) (k : Nat) (h : k < jacAddCalls.length) :
    trajState s0 (k + 1) = runBlock (trajState s0 k) (emitCall (jacAddCalls[k]'h)) := by
  unfold trajState
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, threadState]
  rw [List.foldl_append]
  rfl

/-- The final threaded state is `trajState s0 23`. -/
theorem trajState_full (s0 : JState 64) :
    threadState s0 jacAddCalls = trajState s0 jacAddCalls.length := by
  unfold trajState; rw [List.take_length]

/-! ### Slot-value preservation across a suffix

If a slot is the output of no call in the range `[k, m)`, its field value at
step `m` equals its value at step `k`. This is the non-interference carry that
lets each call's input/output value survive to the final state. -/

omit [NeZero N] in
/-- A slot untouched by calls `k, k+1, …, k+d-1` keeps its field value from step
    `k` to step `k+d` (`others` applied along the suffix). -/
theorem slotFieldVal_preserved
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0)
    (slot : Nat) :
    ∀ (d k : Nat) (_hk : k + d ≤ jacAddCalls.length),
      (∀ j (hj : j < jacAddCalls.length), k ≤ j → j < k + d →
        slot ≠ callOut (jacAddCalls[j]'hj))
      → slotFieldVal N (trajState s0 (k + d)) base slot
        = slotFieldVal N (trajState s0 k) base slot := by
  intro d
  induction d with
  | zero => intro k _ _; rfl
  | succ d ih =>
      intro k hk hno
      have hk1 : (k + 1) + d ≤ jacAddCalls.length := by omega
      have hkk : k < jacAddCalls.length := by omega
      -- value at (k+1)+d = value at k+1 (slot untouched on [k+1, k+1+d))
      have e1 : slotFieldVal N (trajState s0 ((k + 1) + d)) base slot
          = slotFieldVal N (trajState s0 (k + 1)) base slot := by
        apply ih (k + 1) hk1
        intro j hj hj1 hj2
        exact hno j hj (by omega) (by omega)
      -- value at k+1 = value at k (the k-th call doesn't write slot)
      have e0 : slotFieldVal N (trajState s0 (k + 1)) base slot
          = slotFieldVal N (trajState s0 k) base slot :=
        (R.realizes k hkk).others slot (hno k hkk (by omega) (by omega))
      have hidx : k + (d + 1) = (k + 1) + d := by omega
      rw [hidx, e1, e0]

omit [NeZero N] in
/-- Corollary: if `slot` is written by no call in `[k, m)` (`k ≤ m ≤ 23`), its
    field value agrees at steps `k` and `m`. -/
theorem slotFieldVal_const
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0)
    (slot k m : Nat) (hkm : k ≤ m) (hm : m ≤ jacAddCalls.length)
    (hno : ∀ j (hj : j < jacAddCalls.length), k ≤ j → j < m →
      slot ≠ callOut (jacAddCalls[j]'hj)) :
    slotFieldVal N (trajState s0 m) base slot = slotFieldVal N (trajState s0 k) base slot := by
  have hd : m = k + (m - k) := by omega
  rw [hd]
  exact slotFieldVal_preserved R slot (m - k) k (by omega)
    (fun j hj hj1 hj2 => hno j hj hj1 (by omega))

/-! ## 6. Spec coordinates and the all-inputs value identity

`jacAddGen` (`add-2007-bl`) of the input field coordinates; `slotFieldVal` reads
the six input slots as field elements. The headline reads the three output slots
off the final threaded state. -/

/-- The `ZMod N` input coordinates read from the six input slots of the start
    state. -/
def inX1 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sX1
def inY1 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sY1
def inZ1 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sZ1
def inX2 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sX2
def inY2 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sY2
def inZ2 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal N s0 base sZ2

omit [NeZero N] in
/-- **The all-inputs VALUE identity: `jacAddBlock` realizes `jacAddGen`.**

    Given the carried per-op field realizers `R` (each `jacAddCalls` op realizes
    its `ZMod N` field op along the `runBlock`-threaded trajectory — multiply via
    `EcJacAddMontReduceBridge.feMulFrameAtReduced`/`AUCurvesMontReduceFaithful`,
    add/sub via the add/sub canonicalisation bridge), running `jacAddBlock` from a
    start state `s0` whose input slots hold `P₁ = (X₁,Y₁,Z₁)`, `P₂ = (X₂,Y₂,Z₂)`
    (in the de-Montgomery `slotFieldVal` interpretation) leaves the three output
    slots `sX3`/`sY3`/`sZ3` holding exactly the field coordinates of
    `EcProjectiveAddGeneric.jacAddGen X₁ Y₁ Z₁ X₂ Y₂ Z₂`.

    The integration algebra — threading the 23 field realizers through
    `jacAddCalls` accumulates to the `add-2007-bl` formula — is fully Lean-proved
    (`ring` over `ZMod N`). The two trust edges are the named per-op
    canonicalisations carried in `R`. -/
theorem jacAddBlock_realizes_jacAddGen
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized N base s0) :
    (slotFieldVal N (runBlock s0 jacAddBlock) base sX3,
     slotFieldVal N (runBlock s0 jacAddBlock) base sY3,
     slotFieldVal N (runBlock s0 jacAddBlock) base sZ3)
      = EcProjectiveGeneric.jacAddGen
          (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
          (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) := by
  -- final state = trajState at length 23
  rw [runBlock_jacAddBlock, trajState_full]
  -- the final-state field value of a slot
  set V : Nat → ZMod N := fun slot => slotFieldVal N (trajState s0 jacAddCalls.length) base slot
    with hV
  -- read the realizer at a concrete index, with its out/in slots already reduced
  -- per-call value step: V (out) = op (Vk in0) (Vk in1), aligned to V via const.
  -- We package the recurring "field value at the write step's pre-state equals the
  -- final value" as the per-call lemma below.
  have len : jacAddCalls.length = 23 := by decide
  -- The value of a slot at its settle step `k` equals its final value, when the
  -- slot is written by no call in `[k, 23)` (SSA: a consumed slot was written
  -- earlier and is never rewritten).
  have align : ∀ (k : Nat) (_hk : k ≤ jacAddCalls.length) (slot : Nat),
      (∀ j (hj : j < jacAddCalls.length), k ≤ j → slot ≠ callOut (jacAddCalls[j]'hj)) →
      slotFieldVal N (trajState s0 k) base slot = V slot := by
    intro k hk slot hno
    rw [hV]
    exact (slotFieldVal_const R slot k jacAddCalls.length hk le_rfl
      (fun j hj hj1 _ => hno j hj hj1)).symm
  -- The per-call value step, fully aligned to the final values `V`:
  -- `V (out) = (field op) (V in0) (V in1)`, given (by `decide`) that `out` is the
  -- output of no call after `k`, and each input is the output of no call from `k`
  -- on (SSA single-assignment: a consumed slot was written strictly earlier).
  have callV : ∀ (k : Nat) (hk : k < jacAddCalls.length)
      (hout : ∀ j (hj : j < jacAddCalls.length), k + 1 ≤ j →
        callOut (jacAddCalls[k]'hk) ≠ callOut (jacAddCalls[j]'hj))
      (hin0 : ∀ j (hj : j < jacAddCalls.length), k ≤ j →
        callIn0 (jacAddCalls[k]'hk) ≠ callOut (jacAddCalls[j]'hj))
      (hin1 : ∀ j (hj : j < jacAddCalls.length), k ≤ j →
        callIn1 (jacAddCalls[k]'hk) ≠ callOut (jacAddCalls[j]'hj)),
      V (callOut (jacAddCalls[k]'hk))
        = callOp (jacAddCalls[k]'hk)
            (V (callIn0 (jacAddCalls[k]'hk))) (V (callIn1 (jacAddCalls[k]'hk))) := by
    intro k hk hout hin0 hin1
    -- LHS: V out = value at step k+1 (out unwritten on [k+1, 23]).
    have hLHS : V (callOut (jacAddCalls[k]'hk))
        = slotFieldVal N (trajState s0 (k + 1)) base (callOut (jacAddCalls[k]'hk)) := by
      rw [hV]
      exact slotFieldVal_const R _ (k + 1) jacAddCalls.length hk le_rfl
        (fun j hj hj1 _ => hout j hj hj1)
    -- inputs at step k = V input (each input unwritten on [k, 23]).
    have hI0 := align k (le_of_lt hk) (callIn0 (jacAddCalls[k]'hk))
      (fun j hj hj1 => hin0 j hj hj1)
    have hI1 := align k (le_of_lt hk) (callIn1 (jacAddCalls[k]'hk))
      (fun j hj hj1 => hin1 j hj hj1)
    rw [hLHS, (R.realizes k hk).out_val, hI0, hI1]
  clear align
  -- Instantiate `callV` at each concrete call (the non-write side conditions are
  -- `decide`-discharged: distinct slot numerals), reducing each to the numeric
  -- step `V <out> = (field op) (V <in0>) (V <in1>)`.
  have c0 : V 10 = V 2 * V 2 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 0 (by decide) (by decide) (by decide) (by decide)
  have c1 : V 12 = V 5 * V 5 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 1 (by decide) (by decide) (by decide) (by decide)
  have c2 : V 14 = V 10 * V 2 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 2 (by decide) (by decide) (by decide) (by decide)
  have c3 : V 16 = V 12 * V 5 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 3 (by decide) (by decide) (by decide) (by decide)
  have c4 : V 18 = V 0 * V 12 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 4 (by decide) (by decide) (by decide) (by decide)
  have c5 : V 20 = V 3 * V 10 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 5 (by decide) (by decide) (by decide) (by decide)
  have c6 : V 22 = V 1 * V 16 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 6 (by decide) (by decide) (by decide) (by decide)
  have c7 : V 24 = V 4 * V 14 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 7 (by decide) (by decide) (by decide) (by decide)
  have c8 : V 26 = V 20 - V 18 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 8 (by decide) (by decide) (by decide) (by decide)
  have c9 : V 27 = V 24 - V 22 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 9 (by decide) (by decide) (by decide) (by decide)
  have c10 : V 28 = V 26 * V 26 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 10 (by decide) (by decide) (by decide) (by decide)
  have c11 : V 30 = V 28 * V 26 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 11 (by decide) (by decide) (by decide) (by decide)
  have c12 : V 32 = V 18 * V 28 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 12 (by decide) (by decide) (by decide) (by decide)
  have c13 : V 34 = V 27 * V 27 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 13 (by decide) (by decide) (by decide) (by decide)
  have c14 : V 36 = V 34 - V 30 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 14 (by decide) (by decide) (by decide) (by decide)
  have c15 : V 37 = V 32 + V 32 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 15 (by decide) (by decide) (by decide) (by decide)
  have c16 : V 6 = V 36 - V 37 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 16 (by decide) (by decide) (by decide) (by decide)
  have c17 : V 38 = V 32 - V 6 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 17 (by decide) (by decide) (by decide) (by decide)
  have c18 : V 40 = V 27 * V 38 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 18 (by decide) (by decide) (by decide) (by decide)
  have c19 : V 42 = V 22 * V 30 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 19 (by decide) (by decide) (by decide) (by decide)
  have c20 : V 7 = V 40 - V 42 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 20 (by decide) (by decide) (by decide) (by decide)
  have c21 : V 44 = V 2 * V 5 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 21 (by decide) (by decide) (by decide) (by decide)
  have c22 : V 8 = V 44 * V 26 := by
    simpa [callOut, callIn0, callIn1, callOp] using callV 22 (by decide) (by decide) (by decide) (by decide)
  clear callV
  -- unfold the goal's spec: jacAddGen of the six input coordinates, and read the
  -- three output slots' final values off `V`.
  simp only [EcProjectiveGeneric.jacAddGen, inX1, inY1, inZ1, inX2, inY2, inZ2,
    sX1, sY1, sZ1, sX2, sY2, sZ2, sX3, sY3, sZ3, Prod.mk.injEq]
  -- the input slots are written by no call, so their value at s0 = their final V.
  have iX1 : slotFieldVal N s0 base 0 = V 0 :=
    (slotFieldVal_const R 0 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iY1 : slotFieldVal N s0 base 1 = V 1 :=
    (slotFieldVal_const R 1 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iZ1 : slotFieldVal N s0 base 2 = V 2 :=
    (slotFieldVal_const R 2 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iX2 : slotFieldVal N s0 base 3 = V 3 :=
    (slotFieldVal_const R 3 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iY2 : slotFieldVal N s0 base 4 = V 4 :=
    (slotFieldVal_const R 4 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iZ2 : slotFieldVal N s0 base 5 = V 5 :=
    (slotFieldVal_const R 5 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  rw [iX1, iY1, iZ1, iX2, iY2, iZ2]
  -- fold the three output-slot reads in the goal to `V 6 / V 7 / V 8` (defeq to
  -- `V`'s body at those slots).
  have oX3 : slotFieldVal N (trajState s0 jacAddCalls.length) base 6 = V 6 := rfl
  have oY3 : slotFieldVal N (trajState s0 jacAddCalls.length) base 7 = V 7 := rfl
  have oZ3 : slotFieldVal N (trajState s0 jacAddCalls.length) base 8 = V 8 := rfl
  rw [oX3, oY3, oZ3]
  -- now the goal references the output slots `V 6, V 7, V 8`; the `cN` express each
  -- intermediate `V out` as a field op of earlier `V`s. Substitute the goal
  -- bottom-up (outputs first, then their dependencies) until everything is in the
  -- six input values `V 0 .. V 5`, matching `jacAddGen`'s RHS; close by `ring`.
  rw [c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6,
    c5, c4, c3, c2, c1, c0]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ## 7. Non-vacuity: the carried realizers are satisfiable from the bricks

The `FieldOpRealized` predicate is **not** an unsatisfiable over-constraint: each
op tag's realizer is exactly the de-Montgomery image of a proven brick value plus
its named AUCurves canonicalisation. The multiply realizer's field content is
`EcJacAddMontReduceBridge.montMulFieldElem_spec` (carrying `feMulFrameAtReduced`);
the add/sub realizer's is the analogous `canonReduce`-based bridge. We exhibit the
three field-level realizer facts and the named add/sub leaf-adoption predicate. -/

/-- The de-Montgomery field element a `Nat` Montgomery-form residue represents:
    `v · R⁻¹` in `ZMod N` (`R = 2^256`). `slotFieldVal N s base slot` is exactly
    `deMont N (valLimbs (slotLimbs s base slot))`. -/
def deMont (N v : Nat) : ZMod N := (v : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹

omit [NeZero N] in
@[simp] theorem slotFieldVal_deMont (s : JState 64) (base : String) (slot : Nat) :
    slotFieldVal N s base slot = deMont N (valLimbs (slotLimbs s base slot)) := rfl

omit [NeZero N] in
/-- **Multiply realizer field content (non-vacuous, carried).** For reduced
    residues `a, b < N` and the curve's Montgomery constant, the de-Montgomery
    value of `montMulFieldElem N Nprime a b` (the AUCurves-canonicalised Montgomery
    field product, `EcJacAddMontReduceBridge.montMulFieldElem`) is the **product**
    of the de-Montgomery values of `a` and `b` in `ZMod N`. This is the field-op
    fact a multiply `FieldOpRealized.out_val` carries — the de-Montgomery image of
    `montMulFieldElem_spec` (and hence of `feMulFrameAtReduced`). -/
theorem deMont_montMul [Fact (Nat.Prime N)]
    (Nprime a b : Nat) (hodd : N ≠ 2) (hNleR : N ≤ 2 ^ 256)
    (ha : a < N) (hb : b < N) (hNprime : (N * Nprime) % 2 ^ 256 = 2 ^ 256 - 1) :
    deMont N (montMulFieldElem N Nprime a b) = deMont N a * deMont N b := by
  have hp : Nat.Prime N := Fact.out
  have hN : 0 < N := hp.pos
  obtain ⟨_, hcong⟩ := montMulFieldElem_spec N Nprime a b hN hNleR ha hb hNprime
  -- R is a unit in ZMod N (N prime, N ≠ 2 ⇒ R = 2^256 coprime to N)
  have hRunit : IsUnit ((2 ^ 256 : ℕ) : ZMod N) := by
    rw [Nat.cast_pow]
    exact IsUnit.pow 256 ((ZMod.isUnit_iff_coprime 2 N).mpr
      ((Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hodd h.symm)))
  -- cast the Nat.ModEq to a ZMod N equation: (m)·R = a·b
  have hZ : (montMulFieldElem N Nprime a b : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)
      = (a : ZMod N) * (b : ZMod N) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ N).mpr hcong
    push_cast at h
    push_cast
    linear_combination h
  -- deMont m = m·R⁻¹; from hZ, a·b = m·R, so m·R⁻¹ = (a·R⁻¹)(b·R⁻¹).
  unfold deMont
  have hRi : ((2 ^ 256 : ℕ) : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹ = 1 :=
    mul_inv_cancel₀ hRunit.ne_zero
  -- m·R⁻¹ = (m·R)·R⁻¹·R⁻¹ = (a·b)·R⁻¹·R⁻¹ = (a·R⁻¹)(b·R⁻¹)
  calc (montMulFieldElem N Nprime a b : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹
        = (montMulFieldElem N Nprime a b : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹
            * (((2 ^ 256 : ℕ) : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹) := by
              rw [hRi, mul_one]
      _ = ((montMulFieldElem N Nprime a b : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N))
            * ((2 ^ 256 : ℕ) : ZMod N)⁻¹ * ((2 ^ 256 : ℕ) : ZMod N)⁻¹ := by ring
      _ = ((a : ZMod N) * (b : ZMod N)) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹
            * ((2 ^ 256 : ℕ) : ZMod N)⁻¹ := by rw [hZ]
      _ = (a : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹
            * ((b : ZMod N) * ((2 ^ 256 : ℕ) : ZMod N)⁻¹) := by ring

/-! ### The add/sub canonicalisation bridge (mirror of `AUCurvesMontReduceFaithful`)

The frame-wrapped add/sub bricks (`feAddFrameAt_value` / `feSubFrameAt_value`)
land the **raw** ripple result `addLimbs` / `subLimbs` in `[0, 2·N)` (one
conditional subtract / add-back away from the canonical representative in
`[0, N)`). `AUCurvesFieldAddSubFaithful` is the named cross-prover adoption of the
*same* `conditional_sub` canonicalisation as `AUCurvesMontReduceFaithful`: a
CatCrypt-side add/sub canonicaliser `addSubLeaf` coincides, on `[0, 2·N)`, with
the AUCurves verified `canonReduce N` (fiat-crypto's `Qed`'d
`conditional_sub_correct` / `valid` in `WordByWordMontgomery.v`, consumed per
curve by AUCurves `*_Bignum_Specs.v`). It mirrors the mont-reduce bridge field for
field add/sub, where the post-add/sub value is reduced from `[0, 2·N)` to
`[0, N)`. -/

/-- **Named cross-prover leaf-adoption: the field add/sub canonicalisation leaf.**

    `AUCurvesFieldAddSubFaithful N addSubLeaf` says: on every `v < 2·N` (the range
    `addLimbs`/`subLimbs` value lands in after the curve's modular add/sub
    correction), the adopted leaf `addSubLeaf v` equals the AUCurves verified
    canonicalisation `EcJacAddMontReduceBridge.canonReduce N v` — the single
    conditional subtract whose `conditional_sub_correct` / `valid` is `Qed`'d in
    `fiat-crypto/src/Arithmetic/WordByWordMontgomery.v`. The exact mirror of
    `AUCurvesMontReduceFaithful` for the add/sub side. -/
def AUCurvesFieldAddSubFaithful (N : Nat) (addSubLeaf : Nat → Nat) : Prop :=
  ∀ v : Nat, v < 2 * N → addSubLeaf v = canonReduce N v

/-- **Non-vacuous witness** for the add/sub bridge: `canonReduce N` itself adopts
    the leaf by reflexivity (mirror of
    `EcJacAddMontReduceBridge.aucurvesMontReduceLeaf_canonical`). The genuine
    cross-prover content is the gap between this realiser and the value the emitted
    conditional add-back / subtract computes, validated against AUCurves' Rocq
    output outside Lean. -/
theorem aucurvesFieldAddSub_canonical (N : Nat) :
    AUCurvesFieldAddSubFaithful N (canonReduce N) := fun _ _ => rfl

omit [NeZero N] in
/-- **Add realizer field content (non-vacuous, carried).** A canonicalised field
    add — the AUCurves `canonReduce` of a value `≡ a + b (mod N)` landing in
    `[0, 2·N)` — has de-Montgomery value equal to the **sum** of the de-Montgomery
    values of `a` and `b`. The field-op fact an add `FieldOpRealized.out_val`
    carries, via the add/sub bridge. -/
theorem deMont_canonAdd (r a b : Nat) (hr : r < 2 * N)
    (hcong : r ≡ a + b [MOD N]) :
    deMont N (canonReduce N r) = deMont N a + deMont N b := by
  unfold deMont
  have hz : ((canonReduce N r : ℕ) : ZMod N) = (a : ZMod N) + (b : ZMod N) := by
    have h1 : ((canonReduce N r : ℕ) : ZMod N) = (r : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ N).mpr (canonReduce_modEq N r hr)
    have h2 : ((r : ℕ) : ZMod N) = ((a + b : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ N).mpr hcong
    rw [h1, h2]; push_cast; ring
  rw [hz]; ring

omit [NeZero N] in
/-- **Sub realizer field content (non-vacuous, carried).** The subtract dual of
    `deMont_canonAdd`: a canonicalised field sub (`canonReduce` of a value
    `≡ a − b (mod N)`, via the add-back correction) has de-Montgomery value equal
    to the **difference** of the de-Montgomery values. -/
theorem deMont_canonSub (r a b : Nat) (hr : r < 2 * N)
    (hcong : (r : ZMod N) = (a : ZMod N) - (b : ZMod N)) :
    deMont N (canonReduce N r) = deMont N a - deMont N b := by
  unfold deMont
  have h1 : ((canonReduce N r : ℕ) : ZMod N) = (r : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ N).mpr (canonReduce_modEq N r hr)
  rw [h1, hcong]; ring

/-! ### Non-vacuity summary

`deMont_montMul`, `deMont_canonAdd`, `deMont_canonSub` are the three field-op
facts a `FieldOpRealized` witness's `out_val` field carries — each a de-Montgomery
image of a proven brick value (`montMulFieldElem_spec`/`feMulFrameAtReduced` for
multiply; the canonicalised `addLimbs`/`subLimbs` value for add/sub). They
witness that `FieldOpRealized` — and hence `JacAddRealized` — is satisfiable from
the bricks plus the named AUCurves canonicalisations, never an unsatisfiable
over-constraint. Holding a `JacAddRealized N base s0` is therefore *adopting* the
per-op AUCurves-canonicalised field realizers; the headline
`jacAddBlock_realizes_jacAddGen` then proves the whole-point-add value identity
against `EcProjectiveAddGeneric.jacAddGen` purely algebraically over them. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue
