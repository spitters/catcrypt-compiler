/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDbl6Block
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblABlock

@[expose] public section

set_option autoImplicit false

/-!
# The six-limb Jacobian point-double for `a = −3` and its value identity

`EcJacDblABlock` realises the `a = −3` Jacobian point-double `dbl-2001-b`
(`EcProjectiveGenericA.jacDoubleGenM3`) over the four-limb frame. This module is the
six-limb (`R = 2^384`) realisation of the same schedule, assembled the way
`EcJacDbl6Block` assembles the `a = 0` double from `EcJacDblBlock`:

* the call schedule is `EcJacDblABlock.jacDblCallsA` (22 calls: 8 `mul`, 10 `add`,
  4 `sub`) with its slot layout, reused unchanged;
* each call is emitted with the six-limb dispatch `EcJacAdd6Block.emitCall6`, and the
  calls are threaded with `EcJacDbl6Block.threadStateDbl6`, which is stated over an
  arbitrary call list;
* slots are read with the six-limb de-Montgomery interpretation
  `EcJacAdd6Block.slotFieldVal6`, and the input coordinates with
  `EcJacDbl6Block.inX` / `inY` / `inZ` (slots 0, 1, 2);
* each call's realizer is `EcJacAdd6Block.FieldOpRealized6`.

## Main results

* `jacDblBlock6A` — the six-limb block `(jacDblCallsA.map emitCall6).flatten`.
* `runBlock_jacDblBlock6A`, `trajStateDbl6A_succ`, `trajStateDbl6A_full` — the threading
  and trajectory lemmas.
* `JacDblRealized6A` — one `FieldOpRealized6` witness per call of `jacDblCallsA` along
  the `runBlock` trajectory.
* `jacDblBlock6A_realizes_jacDoubleGenA` — under `JacDblRealized6A`, the output slots
  `sX3` / `sY3` / `sZ3` of the final state hold `EcProjectiveGenericA.jacDoubleGenA (−3)`
  of the input slots.
* `jacDblBlock6A_realizes_jacDoubleGenM3` — the same identity against the `dbl-2001-b`
  form `jacDoubleGenM3`.

The statements are value identities of the field-op dataflow; no timing or security
property is stated.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDbl6ABlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6Block
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDbl6Block (threadStateDbl6 inX inY inZ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblABlock (jacDblCallsA)

variable {N : Nat} [NeZero N]

/-! ## 1. The assembled block -/

/-- The six-limb Jacobian point-double block `P' := 2·P` for `a = −3` (`dbl-2001-b`):
    the six-limb frame-wrapped field-op blocks of `jacDblCallsA` concatenated over the
    frame `"f"`. -/
def jacDblBlock6A : List (JInstr 64) :=
  (jacDblCallsA.map emitCall6).flatten

/-! ## 2. Threading and the trajectory -/

/-- `runBlock` of `jacDblBlock6A` is the left fold of `runBlock ∘ emitCall6` over
    `jacDblCallsA`. -/
theorem runBlock_jacDblBlock6A (s0 : JState 64) :
    runBlock s0 jacDblBlock6A = threadStateDbl6 s0 jacDblCallsA := by
  rw [jacDblBlock6A, runBlock_flatten_map]; rfl

/-- The state before call `k` of `jacDblCallsA`, threaded from `s0` over `emitCall6`. -/
def trajStateDbl6A (s0 : JState 64) (k : Nat) : JState 64 :=
  threadStateDbl6 s0 (jacDblCallsA.take k)

/-- The six-limb realizer bundle for the `a = −3` point-double: for each call index
    `k < 22`, a `FieldOpRealized6` witness for `jacDblCallsA[k]` between the threaded
    states `k` and `k + 1`. -/
structure JacDblRealized6A (N : Nat) (base : String) (s0 : JState 64) : Prop where
  /-- Each call realizes its field op at its threaded pre-state. -/
  realizes : ∀ (k : Nat) (h : k < jacDblCallsA.length),
    FieldOpRealized6 N base (jacDblCallsA[k]'h)
      (trajStateDbl6A s0 k) (trajStateDbl6A s0 (k + 1))

/-- One step of the trajectory runs one call. -/
theorem trajStateDbl6A_succ (s0 : JState 64) (k : Nat) (h : k < jacDblCallsA.length) :
    trajStateDbl6A s0 (k + 1)
      = runBlock (trajStateDbl6A s0 k) (emitCall6 (jacDblCallsA[k]'h)) := by
  unfold trajStateDbl6A
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, threadStateDbl6]
  rw [List.foldl_append]
  rfl

/-- The final threaded state is `trajStateDbl6A s0 22`. -/
theorem trajStateDbl6A_full (s0 : JState 64) :
    threadStateDbl6 s0 jacDblCallsA = trajStateDbl6A s0 jacDblCallsA.length := by
  unfold trajStateDbl6A; rw [List.take_length]

omit [NeZero N] in
/-- A slot written by none of the calls `k, …, k+d-1` keeps its six-limb field value
    from step `k` to step `k+d`. -/
theorem slotFieldVal6_preservedDblA
    {base : String} {s0 : JState 64} (R : JacDblRealized6A N base s0)
    (slot : Nat) :
    ∀ (d k : Nat) (_hk : k + d ≤ jacDblCallsA.length),
      (∀ j (hj : j < jacDblCallsA.length), k ≤ j → j < k + d →
        slot ≠ EcJacAddValue.callOut (jacDblCallsA[j]'hj))
      → slotFieldVal6 N (trajStateDbl6A s0 (k + d)) base slot
        = slotFieldVal6 N (trajStateDbl6A s0 k) base slot := by
  intro d
  induction d with
  | zero => intro k _ _; rfl
  | succ d ih =>
      intro k hk hno
      have hk1 : (k + 1) + d ≤ jacDblCallsA.length := by omega
      have hkk : k < jacDblCallsA.length := by omega
      have e1 : slotFieldVal6 N (trajStateDbl6A s0 ((k + 1) + d)) base slot
          = slotFieldVal6 N (trajStateDbl6A s0 (k + 1)) base slot := by
        apply ih (k + 1) hk1
        intro j hj hj1 hj2
        exact hno j hj (by omega) (by omega)
      have e0 : slotFieldVal6 N (trajStateDbl6A s0 (k + 1)) base slot
          = slotFieldVal6 N (trajStateDbl6A s0 k) base slot :=
        (R.realizes k hkk).others slot (hno k hkk (by omega) (by omega))
      have hidx : k + (d + 1) = (k + 1) + d := by omega
      rw [hidx, e1, e0]

omit [NeZero N] in
/-- A slot written by no call in `[k, m)` has the same six-limb field value at steps
    `k` and `m`. -/
theorem slotFieldVal6_constDblA
    {base : String} {s0 : JState 64} (R : JacDblRealized6A N base s0)
    (slot k m : Nat) (hkm : k ≤ m) (hm : m ≤ jacDblCallsA.length)
    (hno : ∀ j (hj : j < jacDblCallsA.length), k ≤ j → j < m →
      slot ≠ EcJacAddValue.callOut (jacDblCallsA[j]'hj)) :
    slotFieldVal6 N (trajStateDbl6A s0 m) base slot
      = slotFieldVal6 N (trajStateDbl6A s0 k) base slot := by
  have hd : m = k + (m - k) := by omega
  rw [hd]
  exact slotFieldVal6_preservedDblA R slot (m - k) k (by omega)
    (fun j hj hj1 hj2 => hno j hj hj1 (by omega))

/-! ## 3. The value identity against `jacDoubleGenA (−3)` -/

omit [NeZero N] in
/-- The six-limb value identity for the `a = −3` point-double. Given the realizer bundle
    `R`, running `jacDblBlock6A` from `s0` leaves the output slots `sX3` / `sY3` / `sZ3`,
    read through `slotFieldVal6`, holding `EcProjectiveGenericA.jacDoubleGenA (−3) X Y Z`,
    where `X`, `Y`, `Z` are the six-limb de-Montgomery field values of the input slots
    of `s0` (`EcJacDbl6Block.inX` / `inY` / `inZ`). -/
theorem jacDblBlock6A_realizes_jacDoubleGenA
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacDblRealized6A N base s0) :
    (slotFieldVal6 N (runBlock s0 jacDblBlock6A) base EcJacDblABlock.sX3,
     slotFieldVal6 N (runBlock s0 jacDblBlock6A) base EcJacDblABlock.sY3,
     slotFieldVal6 N (runBlock s0 jacDblBlock6A) base EcJacDblABlock.sZ3)
      = EcProjectiveGenericA.jacDoubleGenA (-3)
          (inX N s0 base) (inY N s0 base) (inZ N s0 base) := by
  rw [runBlock_jacDblBlock6A, trajStateDbl6A_full]
  set V : Nat → ZMod N :=
    fun slot => slotFieldVal6 N (trajStateDbl6A s0 jacDblCallsA.length) base slot
    with hV
  have align : ∀ (k : Nat) (_hk : k ≤ jacDblCallsA.length) (slot : Nat),
      (∀ j (hj : j < jacDblCallsA.length), k ≤ j →
        slot ≠ EcJacAddValue.callOut (jacDblCallsA[j]'hj)) →
      slotFieldVal6 N (trajStateDbl6A s0 k) base slot = V slot := by
    intro k hk slot hno
    rw [hV]
    exact (slotFieldVal6_constDblA R slot k jacDblCallsA.length hk le_rfl
      (fun j hj hj1 _ => hno j hj hj1)).symm
  have callV : ∀ (k : Nat) (hk : k < jacDblCallsA.length)
      (hout : ∀ j (hj : j < jacDblCallsA.length), k + 1 ≤ j →
        EcJacAddValue.callOut (jacDblCallsA[k]'hk)
          ≠ EcJacAddValue.callOut (jacDblCallsA[j]'hj))
      (hin0 : ∀ j (hj : j < jacDblCallsA.length), k ≤ j →
        EcJacAddValue.callIn0 (jacDblCallsA[k]'hk)
          ≠ EcJacAddValue.callOut (jacDblCallsA[j]'hj))
      (hin1 : ∀ j (hj : j < jacDblCallsA.length), k ≤ j →
        EcJacAddValue.callIn1 (jacDblCallsA[k]'hk)
          ≠ EcJacAddValue.callOut (jacDblCallsA[j]'hj)),
      V (EcJacAddValue.callOut (jacDblCallsA[k]'hk))
        = EcJacAddValue.callOp (jacDblCallsA[k]'hk)
            (V (EcJacAddValue.callIn0 (jacDblCallsA[k]'hk)))
            (V (EcJacAddValue.callIn1 (jacDblCallsA[k]'hk))) := by
    intro k hk hout hin0 hin1
    have hLHS : V (EcJacAddValue.callOut (jacDblCallsA[k]'hk))
        = slotFieldVal6 N (trajStateDbl6A s0 (k + 1)) base
            (EcJacAddValue.callOut (jacDblCallsA[k]'hk)) := by
      rw [hV]
      exact slotFieldVal6_constDblA R _ (k + 1) jacDblCallsA.length hk le_rfl
        (fun j hj hj1 _ => hout j hj hj1)
    have hI0 := align k (le_of_lt hk) (EcJacAddValue.callIn0 (jacDblCallsA[k]'hk))
      (fun j hj hj1 => hin0 j hj hj1)
    have hI1 := align k (le_of_lt hk) (EcJacAddValue.callIn1 (jacDblCallsA[k]'hk))
      (fun j hj hj1 => hin1 j hj hj1)
    rw [hLHS, (R.realizes k hk).out_val, hI0, hI1]
  clear align
  have c0 : V 6 = V 2 * V 2 := callV 0 (by decide) (by decide) (by decide) (by decide)
  have c1 : V 8 = V 0 - V 6 := callV 1 (by decide) (by decide) (by decide) (by decide)
  have c2 : V 9 = V 0 + V 6 := callV 2 (by decide) (by decide) (by decide) (by decide)
  have c3 : V 10 = V 8 * V 9 := callV 3 (by decide) (by decide) (by decide) (by decide)
  have c4 : V 12 = V 10 + V 10 := callV 4 (by decide) (by decide) (by decide) (by decide)
  have c5 : V 13 = V 12 + V 10 := callV 5 (by decide) (by decide) (by decide) (by decide)
  have c6 : V 14 = V 1 * V 1 := callV 6 (by decide) (by decide) (by decide) (by decide)
  have c7 : V 16 = V 0 * V 14 := callV 7 (by decide) (by decide) (by decide) (by decide)
  have c8 : V 18 = V 16 + V 16 := callV 8 (by decide) (by decide) (by decide) (by decide)
  have c9 : V 19 = V 18 + V 18 := callV 9 (by decide) (by decide) (by decide) (by decide)
  have c10 : V 20 = V 13 * V 13 := callV 10 (by decide) (by decide) (by decide) (by decide)
  have c11 : V 22 = V 19 + V 19 := callV 11 (by decide) (by decide) (by decide) (by decide)
  have c12 : V 3 = V 20 - V 22 := callV 12 (by decide) (by decide) (by decide) (by decide)
  have c13 : V 23 = V 19 - V 3 := callV 13 (by decide) (by decide) (by decide) (by decide)
  have c14 : V 24 = V 13 * V 23 := callV 14 (by decide) (by decide) (by decide) (by decide)
  have c15 : V 26 = V 14 * V 14 := callV 15 (by decide) (by decide) (by decide) (by decide)
  have c16 : V 28 = V 26 + V 26 := callV 16 (by decide) (by decide) (by decide) (by decide)
  have c17 : V 29 = V 28 + V 28 := callV 17 (by decide) (by decide) (by decide) (by decide)
  have c18 : V 30 = V 29 + V 29 := callV 18 (by decide) (by decide) (by decide) (by decide)
  have c19 : V 4 = V 24 - V 30 := callV 19 (by decide) (by decide) (by decide) (by decide)
  have c20 : V 32 = V 1 * V 2 := callV 20 (by decide) (by decide) (by decide) (by decide)
  have c21 : V 5 = V 32 + V 32 := callV 21 (by decide) (by decide) (by decide) (by decide)
  clear callV
  simp only [EcProjectiveGenericA.jacDoubleGenA, inX, inY, inZ,
    EcJacDblBlock.sX, EcJacDblBlock.sY, EcJacDblBlock.sZ, EcJacDblABlock.sX3, EcJacDblABlock.sY3, EcJacDblABlock.sZ3,
    Prod.mk.injEq]
  have iX : slotFieldVal6 N s0 base 0 = V 0 :=
    (slotFieldVal6_constDblA R 0 0 jacDblCallsA.length (by omega) le_rfl (by decide)).symm
  have iY : slotFieldVal6 N s0 base 1 = V 1 :=
    (slotFieldVal6_constDblA R 1 0 jacDblCallsA.length (by omega) le_rfl (by decide)).symm
  have iZ : slotFieldVal6 N s0 base 2 = V 2 :=
    (slotFieldVal6_constDblA R 2 0 jacDblCallsA.length (by omega) le_rfl (by decide)).symm
  rw [iX, iY, iZ]
  have oX3 : slotFieldVal6 N (trajStateDbl6A s0 jacDblCallsA.length) base 3 = V 3 := rfl
  have oY3 : slotFieldVal6 N (trajStateDbl6A s0 jacDblCallsA.length) base 4 = V 4 := rfl
  have oZ3 : slotFieldVal6 N (trajStateDbl6A s0 jacDblCallsA.length) base 5 = V 5 := rfl
  rw [oX3, oY3, oZ3]
  rw [c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4,
    c3, c2, c1, c0]
  refine ⟨?_, ?_, ?_⟩ <;> ring

omit [NeZero N] in
/-- The six-limb value identity for the `a = −3` point-double in the `dbl-2001-b` form
    `EcProjectiveGenericA.jacDoubleGenM3`. -/
theorem jacDblBlock6A_realizes_jacDoubleGenM3
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacDblRealized6A N base s0) :
    (slotFieldVal6 N (runBlock s0 jacDblBlock6A) base EcJacDblABlock.sX3,
     slotFieldVal6 N (runBlock s0 jacDblBlock6A) base EcJacDblABlock.sY3,
     slotFieldVal6 N (runBlock s0 jacDblBlock6A) base EcJacDblABlock.sZ3)
      = EcProjectiveGenericA.jacDoubleGenM3
          (inX N s0 base) (inY N s0 base) (inZ N s0 base) := by
  rw [EcProjectiveGenericA.jacDoubleGenM3_eq]
  exact jacDblBlock6A_realizes_jacDoubleGenA R

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDbl6ABlock
