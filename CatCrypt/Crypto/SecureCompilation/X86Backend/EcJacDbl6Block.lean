/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6Block
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblBlock
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The six-limb (P-384) Jacobian point-DOUBLE BLOCK and its VALUE identity

`EcJacAdd6Block.lean` builds the **six-limb** Jacobian point-ADD: the curve-agnostic
`add-2007-bl` call schedule `EcJacAddBlock.jacAddCalls`, the six-limb call dispatch
`emitCall6`, the assembled block `jacAddBlock6`, and the value identity
`jacAddBlock6_realizes_jacAddGen` (the 23 per-op six-limb field realizers thread to
`EcProjectiveAddGeneric.jacAddGen`). This module is the **six-limb point-DOUBLE**
mirror: the same `emitCall6` dispatch over the curve-agnostic `dbl-2009-l` schedule
`EcJacDblBlock.jacDblCalls`, the assembled block `jacDblBlock6`, and the value
identity `jacDblBlock6_realizes_jacDblGen` against `EcProjectiveGeneric.jacDoubleGen`.

## What is reused (curve-, limb-, and op-independent)

* `EcJacAdd6Block.emitCall6` / `feMulFrameAt6Full` / `feAddFrameAt6Store` /
  `feSubFrameAt6Store` — the six-limb field-op dispatch (`R = 2^384`);
* `EcJacAdd6Block.slotFieldVal6` / `deMont6` — the six-limb de-Montgomery field
  interpretation;
* `EcJacAdd6Block.FieldOpRealized6` — the per-op six-limb realizer
  (output-slot field op + non-interference), stated over an arbitrary
  `JacFieldCall`, so the double's calls feed it directly;
* `EcJacAdd6Block.runBlock_flatten_map` — the `(map f).flatten` left-fold law;
* `EcJacAddValue.callOut` / `callIn0` / `callIn1` / `callOp` — the field-op
  interpretation of a call;
* `EcJacDblBlock.jacDblCalls` — the 19-call `dbl-2009-l` dataflow schedule
  (pure dataflow over abstract slots, identical at any radix);
* `EcProjectiveGeneric.jacDoubleGen` — the curve-generic `dbl-2009-l` formula;
* `EcJacAdd6Block.opResidue6_mul_full_of_runBlock` / `opResidue6_add_of_runBlock`
  / `opResidue6_sub_of_runBlock` — the six-limb residue derivations feeding the
  per-op realizers (reused unchanged for the double's three op tags).

## What is built here (six-limb double)

* `jacDblBlock6 := (jacDblCalls.map emitCall6).flatten` — the assembled six-limb
  point-double block, reusing the curve-agnostic `jacDblCalls` schedule.
* `trajStateDbl6` / `JacDblRealized6` — the threaded realizer trajectory for the
  double (mirror of `EcJacAdd6Block.trajState6` / `JacAddRealized6`).
* `jacDblBlock6_realizes_jacDblGen` — the all-inputs value identity: the 19 per-op
  six-limb realizers thread to `jacDoubleGen`. The integration algebra is the SAME
  `ring`-based dataflow proof as the four-limb double
  `EcJacDblValue.jacDblBlock_realizes_jacDblGen`, over `slotFieldVal6`.

The value identity is a dataflow proof with the same structure as the
four-limb double — with `jacDoubleGen` reused curve-generic. No `rfl`/`True` fill.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDbl6Block

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6Block
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblBlock (jacDblCalls)

variable {N : Nat} [NeZero N]

/-! ## 1. The assembled six-limb point-double block

`jacDblBlock6` concatenates the six-limb frame-wrapped field-op blocks
(`emitCall6`) in the curve-agnostic `dbl-2009-l` `jacDblCalls` order — the
straight-line realisation of `jacDoubleGen`'s dataflow over the six-limb frame. -/

/-- **The six-limb structural Jacobian point-double block** `P' := 2·P`
    (`dbl-2009-l`, `a = 0`), the assembled composition of the proven frame-wrapped
    six-limb field bricks over the single frame `"f"` in the curve-agnostic
    `jacDblCalls` order. The six-limb analogue of `EcJacDblBlock.jacDblBlock`. -/
def jacDblBlock6 : List (JInstr 64) :=
  (jacDblCalls.map emitCall6).flatten

/-! ## 2. Threading the double's call list (six-limb)

`runBlock` over the assembled `jacDblBlock6` is the left fold of `runBlock ∘
emitCall6` over `jacDblCalls`. Same composition law as the six-limb add
(`EcJacAdd6Block.runBlock_flatten_map`). -/

/-- The state after running the first calls of `cs` from `s0` over `emitCall6`. -/
def threadStateDbl6 (s0 : JState 64) (cs : List JacFieldCall) : JState 64 :=
  cs.foldl (fun st c => runBlock st (emitCall6 c)) s0

@[simp] theorem threadStateDbl6_nil (s0 : JState 64) : threadStateDbl6 s0 [] = s0 := rfl

@[simp] theorem threadStateDbl6_cons (s0 : JState 64) (c : JacFieldCall) (cs : List JacFieldCall) :
    threadStateDbl6 s0 (c :: cs) = threadStateDbl6 (runBlock s0 (emitCall6 c)) cs := rfl

/-- `runBlock` of the assembled six-limb double block equals the threaded final
    state. -/
theorem runBlock_jacDblBlock6 (s0 : JState 64) :
    runBlock s0 jacDblBlock6 = threadStateDbl6 s0 jacDblCalls := by
  rw [jacDblBlock6, runBlock_flatten_map]; rfl

/-! ## 3. The realizer bundle and the trajectory (six-limb double)

`JacDblRealized6 N base s0` carries the per-op six-limb realizers along the
trajectory threaded from `s0`. Mirror of `EcJacAdd6Block.JacAddRealized6`. -/

/-- The threaded states, one before each call (the realizer trajectory). -/
def trajStateDbl6 (s0 : JState 64) (k : Nat) : JState 64 :=
  threadStateDbl6 s0 (jacDblCalls.take k)

/-- **The carried six-limb realizer bundle for the whole point-double.** For each
    call index `k < 19` it carries a `FieldOpRealized6` witness at the threaded
    pre-state `trajStateDbl6 s0 k`. Six-limb analogue of
    `EcJacDblValue.JacDblRealized`. -/
structure JacDblRealized6 (N : Nat) (base : String) (s0 : JState 64) : Prop where
  /-- Each call realizes its field op at its threaded pre-state. -/
  realizes : ∀ (k : Nat) (h : k < jacDblCalls.length),
    FieldOpRealized6 N base (jacDblCalls[k]'h)
      (trajStateDbl6 s0 k) (trajStateDbl6 s0 (k + 1))

/-- One threaded step of the trajectory unfolds `trajStateDbl6` by one call. -/
theorem trajStateDbl6_succ (s0 : JState 64) (k : Nat) (h : k < jacDblCalls.length) :
    trajStateDbl6 s0 (k + 1) = runBlock (trajStateDbl6 s0 k) (emitCall6 (jacDblCalls[k]'h)) := by
  unfold trajStateDbl6
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, threadStateDbl6]
  rw [List.foldl_append]
  rfl

/-- The final threaded state is `trajStateDbl6 s0 19`. -/
theorem trajStateDbl6_full (s0 : JState 64) :
    threadStateDbl6 s0 jacDblCalls = trajStateDbl6 s0 jacDblCalls.length := by
  unfold trajStateDbl6; rw [List.take_length]

omit [NeZero N] in
/-- A slot untouched by calls `k, …, k+d-1` keeps its field value from step `k` to
    step `k+d` (`others` applied along the suffix). Six-limb double analogue of
    `EcJacDblValue.slotFieldVal_preserved`. -/
theorem slotFieldVal6_preservedDbl
    {base : String} {s0 : JState 64} (R : JacDblRealized6 N base s0)
    (slot : Nat) :
    ∀ (d k : Nat) (_hk : k + d ≤ jacDblCalls.length),
      (∀ j (hj : j < jacDblCalls.length), k ≤ j → j < k + d →
        slot ≠ EcJacAddValue.callOut (jacDblCalls[j]'hj))
      → slotFieldVal6 N (trajStateDbl6 s0 (k + d)) base slot
        = slotFieldVal6 N (trajStateDbl6 s0 k) base slot := by
  intro d
  induction d with
  | zero => intro k _ _; rfl
  | succ d ih =>
      intro k hk hno
      have hk1 : (k + 1) + d ≤ jacDblCalls.length := by omega
      have hkk : k < jacDblCalls.length := by omega
      have e1 : slotFieldVal6 N (trajStateDbl6 s0 ((k + 1) + d)) base slot
          = slotFieldVal6 N (trajStateDbl6 s0 (k + 1)) base slot := by
        apply ih (k + 1) hk1
        intro j hj hj1 hj2
        exact hno j hj (by omega) (by omega)
      have e0 : slotFieldVal6 N (trajStateDbl6 s0 (k + 1)) base slot
          = slotFieldVal6 N (trajStateDbl6 s0 k) base slot :=
        (R.realizes k hkk).others slot (hno k hkk (by omega) (by omega))
      have hidx : k + (d + 1) = (k + 1) + d := by omega
      rw [hidx, e1, e0]

omit [NeZero N] in
/-- If `slot` is written by no call in `[k, m)` (`k ≤ m ≤ 19`), its field value
    agrees at steps `k` and `m`. Six-limb double analogue of
    `EcJacDblValue.slotFieldVal_const`. -/
theorem slotFieldVal6_constDbl
    {base : String} {s0 : JState 64} (R : JacDblRealized6 N base s0)
    (slot k m : Nat) (hkm : k ≤ m) (hm : m ≤ jacDblCalls.length)
    (hno : ∀ j (hj : j < jacDblCalls.length), k ≤ j → j < m →
      slot ≠ EcJacAddValue.callOut (jacDblCalls[j]'hj)) :
    slotFieldVal6 N (trajStateDbl6 s0 m) base slot = slotFieldVal6 N (trajStateDbl6 s0 k) base slot := by
  have hd : m = k + (m - k) := by omega
  rw [hd]
  exact slotFieldVal6_preservedDbl R slot (m - k) k (by omega)
    (fun j hj hj1 hj2 => hno j hj hj1 (by omega))

/-! ## 4. The input coordinates and the all-inputs VALUE identity -/

/-- The `ZMod N` input coordinates read from the three input slots of the start
    state (six-limb interpretation). -/
def inX (N : Nat) (s0 : JState 64) (base : String) : ZMod N :=
  slotFieldVal6 N s0 base EcJacDblBlock.sX
def inY (N : Nat) (s0 : JState 64) (base : String) : ZMod N :=
  slotFieldVal6 N s0 base EcJacDblBlock.sY
def inZ (N : Nat) (s0 : JState 64) (base : String) : ZMod N :=
  slotFieldVal6 N s0 base EcJacDblBlock.sZ

omit [NeZero N] in
/-- **The all-inputs VALUE identity: `jacDblBlock6` realizes `jacDoubleGen`.**

    Given the carried per-op six-limb field realizers `R` (each `jacDblCalls` op
    realizes its `ZMod N` field op along the `runBlock`-threaded trajectory over
    `emitCall6` — multiply via `feMulFrameAt6Full_value`, add/sub via the six-limb
    add/sub bricks with the add/sub canonicalisation), running `jacDblBlock6` from a
    start state `s0` whose input slots hold `P = (X,Y,Z)` (in the de-Montgomery
    `slotFieldVal6` interpretation, `R = 2^384`) leaves the three output slots
    `sX3`/`sY3`/`sZ3` holding exactly the field coordinates of
    `EcProjectiveGeneric.jacDoubleGen X Y Z`.

    The integration algebra — threading the 19 six-limb field realizers through
    `jacDblCalls` accumulates to the `dbl-2009-l` formula — is the SAME `ring`-based
    dataflow proof as the four-limb `EcJacDblValue.jacDblBlock_realizes_jacDblGen`,
    over `slotFieldVal6`. `jacDoubleGen` is reused curve-generic. -/
theorem jacDblBlock6_realizes_jacDblGen
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacDblRealized6 N base s0) :
    (slotFieldVal6 N (runBlock s0 jacDblBlock6) base EcJacDblBlock.sX3,
     slotFieldVal6 N (runBlock s0 jacDblBlock6) base EcJacDblBlock.sY3,
     slotFieldVal6 N (runBlock s0 jacDblBlock6) base EcJacDblBlock.sZ3)
      = EcProjectiveGeneric.jacDoubleGen
          (inX N s0 base) (inY N s0 base) (inZ N s0 base) := by
  rw [runBlock_jacDblBlock6, trajStateDbl6_full]
  set V : Nat → ZMod N := fun slot => slotFieldVal6 N (trajStateDbl6 s0 jacDblCalls.length) base slot
    with hV
  have len : jacDblCalls.length = 19 := by decide
  have align : ∀ (k : Nat) (_hk : k ≤ jacDblCalls.length) (slot : Nat),
      (∀ j (hj : j < jacDblCalls.length), k ≤ j →
        slot ≠ EcJacAddValue.callOut (jacDblCalls[j]'hj)) →
      slotFieldVal6 N (trajStateDbl6 s0 k) base slot = V slot := by
    intro k hk slot hno
    rw [hV]
    exact (slotFieldVal6_constDbl R slot k jacDblCalls.length hk le_rfl
      (fun j hj hj1 _ => hno j hj hj1)).symm
  have callV : ∀ (k : Nat) (hk : k < jacDblCalls.length)
      (hout : ∀ j (hj : j < jacDblCalls.length), k + 1 ≤ j →
        EcJacAddValue.callOut (jacDblCalls[k]'hk) ≠ EcJacAddValue.callOut (jacDblCalls[j]'hj))
      (hin0 : ∀ j (hj : j < jacDblCalls.length), k ≤ j →
        EcJacAddValue.callIn0 (jacDblCalls[k]'hk) ≠ EcJacAddValue.callOut (jacDblCalls[j]'hj))
      (hin1 : ∀ j (hj : j < jacDblCalls.length), k ≤ j →
        EcJacAddValue.callIn1 (jacDblCalls[k]'hk) ≠ EcJacAddValue.callOut (jacDblCalls[j]'hj)),
      V (EcJacAddValue.callOut (jacDblCalls[k]'hk))
        = EcJacAddValue.callOp (jacDblCalls[k]'hk)
            (V (EcJacAddValue.callIn0 (jacDblCalls[k]'hk)))
            (V (EcJacAddValue.callIn1 (jacDblCalls[k]'hk))) := by
    intro k hk hout hin0 hin1
    have hLHS : V (EcJacAddValue.callOut (jacDblCalls[k]'hk))
        = slotFieldVal6 N (trajStateDbl6 s0 (k + 1)) base (EcJacAddValue.callOut (jacDblCalls[k]'hk)) := by
      rw [hV]
      exact slotFieldVal6_constDbl R _ (k + 1) jacDblCalls.length hk le_rfl
        (fun j hj hj1 _ => hout j hj hj1)
    have hI0 := align k (le_of_lt hk) (EcJacAddValue.callIn0 (jacDblCalls[k]'hk))
      (fun j hj hj1 => hin0 j hj hj1)
    have hI1 := align k (le_of_lt hk) (EcJacAddValue.callIn1 (jacDblCalls[k]'hk))
      (fun j hj hj1 => hin1 j hj hj1)
    rw [hLHS, (R.realizes k hk).out_val, hI0, hI1]
  clear align
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
  simp only [EcProjectiveGeneric.jacDoubleGen, inX, inY, inZ,
    EcJacDblBlock.sX, EcJacDblBlock.sY, EcJacDblBlock.sZ,
    EcJacDblBlock.sX3, EcJacDblBlock.sY3, EcJacDblBlock.sZ3, Prod.mk.injEq]
  have iX : slotFieldVal6 N s0 base 0 = V 0 :=
    (slotFieldVal6_constDbl R 0 0 jacDblCalls.length (by omega) le_rfl (by decide)).symm
  have iY : slotFieldVal6 N s0 base 1 = V 1 :=
    (slotFieldVal6_constDbl R 1 0 jacDblCalls.length (by omega) le_rfl (by decide)).symm
  have iZ : slotFieldVal6 N s0 base 2 = V 2 :=
    (slotFieldVal6_constDbl R 2 0 jacDblCalls.length (by omega) le_rfl (by decide)).symm
  rw [iX, iY, iZ]
  have oX3 : slotFieldVal6 N (trajStateDbl6 s0 jacDblCalls.length) base 3 = V 3 := rfl
  have oY3 : slotFieldVal6 N (trajStateDbl6 s0 jacDblCalls.length) base 4 = V 4 := rfl
  have oZ3 : slotFieldVal6 N (trajStateDbl6 s0 jacDblCalls.length) base 5 = V 5 := rfl
  rw [oX3, oY3, oZ3]
  rw [c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ## 5. Non-vacuity: the carried realizers are satisfiable from the bricks

The `FieldOpRealized6` predicate is not an unsatisfiable over-constraint: each op
tag's six-limb realizer is the de-Montgomery image (`R = 2^384`) of a proven brick
value plus its named canonicalisation. `jacDblCalls` uses only the three op tags
`mul`/`add`/`sub`, whose six-limb realizers are derived in `EcJacAdd6Block`
(`opResidue6_mul_full_of_runBlock` / `opResidue6_add_of_runBlock` /
`opResidue6_sub_of_runBlock`) over the proven six-limb bricks; their field content
is `EcJacAdd6Block.deMont6_montMul` / `deMont6_canonAdd` / `deMont6_canonSub`. So a
`JacDblRealized6 N base s0` is satisfiable from exactly the bricks the six-limb add
adopts — re-exported here for the double. -/

omit [NeZero N] in
/-- **Non-vacuity, multiply leg (re-exported).** The field content a `mul`
    `FieldOpRealized6.out_val` carries is the de-Montgomery image of the
    canonicalised six-limb Montgomery field product — exactly
    `EcJacAdd6Block.deMont6_montMul`, reused unchanged. -/
theorem dbl6_mul_realizer_content [Fact (Nat.Prime N)]
    (Nprime a b : Nat) (hodd : N ≠ 2) (hNleR : N ≤ 2 ^ 384)
    (ha : a < N) (hb : b < N) (hNprime : (N * Nprime) % 2 ^ 384 = 2 ^ 384 - 1) :
    deMont6 N (montMulFieldElem6 N Nprime a b) = deMont6 N a * deMont6 N b :=
  deMont6_montMul Nprime a b hodd hNleR ha hb hNprime

omit [NeZero N] in
/-- **Non-vacuity, add leg (re-exported).** `EcJacAdd6Block.deMont6_canonAdd`. -/
theorem dbl6_add_realizer_content (r a b : Nat) (hr : r < 2 * N)
    (hcong : r ≡ a + b [MOD N]) :
    deMont6 N (EcJacAddMontReduceBridge.canonReduce N r) = deMont6 N a + deMont6 N b :=
  deMont6_canonAdd r a b hr hcong

omit [NeZero N] in
/-- **Non-vacuity, sub leg (re-exported).** `EcJacAdd6Block.deMont6_canonSub`. -/
theorem dbl6_sub_realizer_content (r a b : Nat) (hr : r < 2 * N)
    (hcong : (r : ZMod N) = (a : ZMod N) - (b : ZMod N)) :
    deMont6 N (EcJacAddMontReduceBridge.canonReduce N r) = deMont6 N a - deMont6 N b :=
  deMont6_canonSub r a b hr hcong

-- The full six-limb double chain: the assembled block, the value identity against
-- `jacDoubleGen`, and the three re-exported non-vacuity legs.
#check @jacDblBlock6
#check @jacDblBlock6_realizes_jacDblGen

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDbl6Block
