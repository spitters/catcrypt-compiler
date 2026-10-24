/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
public import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# An emitted multi-limb conditional subtract proven against the multi-limb stack

> **`@kat-target`.** Hand-authored leaf block + direct `runBlock` proof — a KAT oracle /
> prototype for the bridge technique, NOT the canonical artifact. New field ops go via the
> golden path (`FieldEmitGoldenPath`); do not extend by hand.

The Barrett reduction's final step: reduce a value `x ∈ [0, 2p)` to `x mod p` with a
data-oblivious conditional subtract — `x − p` via an SBB borrow chain, then a `CMOVcc`
select keeping `x` when the subtract borrowed (`x < p`) and `x − p` otherwise. Over the
`JInstr`/`JState` x86 machine, two limbs:

```
mov d0,x0 ; mov d1,x1     -- d := x
sub d0,p0 ; sbb d1,p1     -- d := x - p, CF := borrow (= x < p)
cmovb d0,x0 ; cmovb d1,x1 -- if x < p, d := x
```

`condSub2_value` proves `valLimbs[d] = valLimbs[x] mod valLimbs[p]` for
`valLimbs[x] < 2·valLimbs[p]`, and `condSub2_bignumVal` reads it through
`valLimbs_eq_bignumVal` — the same value `MultiLimbKernel.condSubLimbs_val` proves. With
the add, subtract, and now conditional subtract emitted-and-bridged (the multiply is
`emitProductBlock4`, the limb-drop a reindexing via `bignumVal_drop`), every arithmetic
step of the Barrett reduce connects the emitted x86 machine to the proven stack.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-! ## Readout lemmas for `mov` and `cmovb` -/

theorem get_mov (s : JState 64) (dst src r : String) :
    (evalInstr s (.mov dst (.reg src))).get r
      = if r = dst then s.get src else s.get r := by
  simp only [evalInstr, x86_MOV, JState.setReg, JState.get, JOperand.eval]

theorem flagB_mov (s : JState 64) (dst src : String) :
    (evalInstr s (.mov dst (.reg src))).flagB (·.cf) = s.flagB (·.cf) := by
  simp [evalInstr, JState.setReg, JState.flagB]

theorem get_cmovb (s : JState 64) (dst src r : String) :
    (evalInstr s (.cmovb dst (.reg src))).get r
      = if r = dst then (if s.flagB (·.cf) then s.get src else s.get dst) else s.get r := by
  simp only [evalInstr, x86_CMOVcc, JState.setReg, JState.get, JOperand.eval]

theorem flagB_cmovb (s : JState 64) (dst src : String) :
    (evalInstr s (.cmovb dst (.reg src))).flagB (·.cf) = s.flagB (·.cf) := by
  simp [evalInstr, x86_CMOVcc, JState.setReg, JState.flagB]

/-! ## The conditional subtract -/

/-- The two-limb conditional-subtract kernel body over `JInstr 64`. -/
def condSub2Block : List (JInstr 64) :=
  [ .mov "d0" (.reg "x0"), .mov "d1" (.reg "x1"),
    .sub "d0" (.reg "p0"), .sbb "d1" (.reg "p1"),
    .cmovb "d0" (.reg "x0"), .cmovb "d1" (.reg "x1") ]

/-- **The emitted block reduces `x` modulo `p`.** For `valLimbs[x] < 2·valLimbs[p]`, the
    output two limbs are `valLimbs[x] mod valLimbs[p]` — for all inputs, over the
    validated x86 machine. -/
theorem condSub2_value (s : JState 64)
    (hx : valLimbs [s.get "x0", s.get "x1"] < 2 * valLimbs [s.get "p0", s.get "p1"]) :
    valLimbs [(runBlock s condSub2Block).get "d0", (runBlock s condSub2Block).get "d1"]
      = valLimbs [s.get "x0", s.get "x1"] % valLimbs [s.get "p0", s.get "p1"] := by
  -- compute the two final output limbs of the 6-instruction block.  The `cmovb`s keep
  -- `x` when the SBB chain borrowed (`x < p`) and the difference `x - p` otherwise.
  have hd0 : (runBlock s condSub2Block).get "d0"
      = if (s.get "x1").toNat < (s.get "p1").toNat
            + (if (s.get "x0").toNat < (s.get "p0").toNat then 1 else 0)
          then s.get "x0" else s.get "x0" - s.get "p0" := by
    simp only [condSub2Block, runBlock_cons, runBlock_nil, get_cmovb, get_mov, emit_sub_word,
      emit_sub_cf, emit_sub_other, emit_sbb_word, emit_sbb_cf, emit_sbb_other,
      flagB_cmovb, ne_eq, String.reduceEq, not_false_eq_true, reduceIte, decide_eq_true_eq]
  have hd1 : (runBlock s condSub2Block).get "d1"
      = if (s.get "x1").toNat < (s.get "p1").toNat
            + (if (s.get "x0").toNat < (s.get "p0").toNat then 1 else 0)
          then s.get "x1"
          else subBorrowWord (s.get "x1") (s.get "p1")
                (BitVec.ofNat 1 (if (s.get "x0").toNat < (s.get "p0").toNat then 1 else 0)) := by
    simp only [condSub2Block, runBlock_cons, runBlock_nil, get_cmovb, get_mov, emit_sub_word,
      emit_sub_cf, emit_sub_other, emit_sbb_word, emit_sbb_cf, emit_sbb_other,
      flagB_cmovb, ne_eq, String.reduceEq, not_false_eq_true, reduceIte, decide_eq_true_eq]
  -- the borrow bits and their reconstructions
  set c0 : Nat := if (s.get "x0").toNat < (s.get "p0").toNat then 1 else 0 with hc0
  have hbo0 : (borrowOutBit (s.get "x0") (s.get "p0") (BitVec.ofNat 1 0)).toNat = c0 := by
    rw [hc0, borrowOutBit]
    simp only [show (BitVec.ofNat 1 0).toNat = 0 from rfl, Nat.add_zero, apply_ite BitVec.toNat]
    rfl
  have hbinc : (BitVec.ofNat 1 c0).toNat = c0 := by rw [hc0]; split_ifs <;> decide
  have hbo1 : (borrowOutBit (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0)).toNat
      = (if (s.get "x1").toNat < (s.get "p1").toNat + c0 then 1 else 0) := by
    rw [borrowOutBit, hbinc]; split_ifs <;> decide
  have hr0 := subb_recon (s.get "x0") (s.get "p0") (BitVec.ofNat 1 0)
  have hr1 := subb_recon (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0)
  rw [hbo0] at hr0
  rw [hbinc, hbo1] at hr1
  have hsub0 : (subBorrowWord (s.get "x0") (s.get "p0") (BitVec.ofNat 1 0)) = s.get "x0" - s.get "p0" := by
    simp [subBorrowWord]
  rw [hsub0] at hr0
  -- bounds
  have hz : (BitVec.ofNat 1 0).toNat = 0 := rfl
  have hd0lt := (s.get "x0" - s.get "p0").isLt
  have hd1lt := (subBorrowWord (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0)).isLt
  have hc0le : c0 ≤ 1 := by rw [hc0]; split_ifs <;> omega
  rw [hz] at hr0
  simp only [valLimbs, mul_zero, add_zero] at hx ⊢
  rw [hd0, hd1]
  by_cases hb1 : (s.get "x1").toNat < (s.get "p1").toNat + c0
  · -- borrow ⇒ x < p ⇒ keep x
    simp only [ite_eq_left hb1] at hr1 ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
  · -- no borrow ⇒ x ≥ p ⇒ take x − p
    simp only [ite_eq_right hb1] at hr1 ⊢
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The emitted conditional subtract reduces modulo `p` in `bignumVal` terms** — the
    same value `MultiLimbKernel.condSubLimbs_val` proves for the verified List kernel. -/
theorem condSub2_bignumVal (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1"] < 2 * bignumVal [s.get "p0", s.get "p1"]) :
    bignumVal [(runBlock s condSub2Block).get "d0", (runBlock s condSub2Block).get "d1"]
      = bignumVal [s.get "x0", s.get "x1"] % bignumVal [s.get "p0", s.get "p1"] := by
  rw [← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal]
  exact condSub2_value s (by rw [valLimbs_eq_bignumVal, valLimbs_eq_bignumVal]; exact hx)

end CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit
