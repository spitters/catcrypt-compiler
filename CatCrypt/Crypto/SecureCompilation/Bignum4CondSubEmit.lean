/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit

/-!
# Curve-width (4-limb) emitted conditional subtract = x mod p

> **`@kat-target`.** Hand-authored leaf block + direct `runBlock` proof — a KAT oracle /
> prototype for the bridge technique, NOT the canonical artifact. New field ops go via the
> golden path (`FieldEmitGoldenPath`; see `EMIT_PROVENANCE.md`); do not extend by hand.

The 4-limb (P256-width) generalization of `BignumCondSubEmit.condSub2_value`: a
data-oblivious conditional subtract reducing a 256-bit value `x ∈ [0, 2p)` to `x mod p`
over the `JInstr`/`JState` x86 machine — `x − p` via a 4-limb SBB borrow chain, then a
per-limb `CMOVcc` keeping `x` when the subtract borrowed (`x < p`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Bignum4CondSubEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge
open CatCrypt.Crypto.SecureCompilation.BignumCondSubEmit

/-- The four-limb conditional-subtract kernel body over `JInstr 64`. -/
def condSub4Block : List (JInstr 64) :=
  [ .mov "d0" (.reg "x0"), .mov "d1" (.reg "x1"), .mov "d2" (.reg "x2"), .mov "d3" (.reg "x3"),
    .sub "d0" (.reg "p0"), .sbb "d1" (.reg "p1"), .sbb "d2" (.reg "p2"), .sbb "d3" (.reg "p3"),
    .cmovb "d0" (.reg "x0"), .cmovb "d1" (.reg "x1"), .cmovb "d2" (.reg "x2"),
    .cmovb "d3" (.reg "x3") ]

/-- **The emitted 4-limb conditional subtract reduces `x` modulo `p`.** For a 256-bit
    value `x` with `valLimbs[x] < 2·valLimbs[p]`, the output four limbs are
    `valLimbs[x] mod valLimbs[p]` — the P256-width emitted Barrett final step. -/
theorem condSub4_value (s : JState 64)
    (hx : valLimbs [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        < 2 * valLimbs [s.get "p0", s.get "p1", s.get "p2", s.get "p3"]) :
    valLimbs [(runBlock s condSub4Block).get "d0", (runBlock s condSub4Block).get "d1",
        (runBlock s condSub4Block).get "d2", (runBlock s condSub4Block).get "d3"]
      = valLimbs [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        % valLimbs [s.get "p0", s.get "p1", s.get "p2", s.get "p3"] := by
  -- the final-borrow condition of the 4-limb SBB chain (nested borrow-ins)
  set c0 : Nat := if (s.get "x0").toNat < (s.get "p0").toNat then 1 else 0 with hc0
  set c1 : Nat := if (s.get "x1").toNat < (s.get "p1").toNat + c0 then 1 else 0 with hc1
  set c2 : Nat := if (s.get "x2").toNat < (s.get "p2").toNat + c1 then 1 else 0 with hc2
  have hz : (BitVec.ofNat 1 0).toNat = 0 := rfl
  -- output readouts (each: keep x_i on borrow, else the difference limb)
  have hd0 : (runBlock s condSub4Block).get "d0"
      = if (s.get "x3").toNat < (s.get "p3").toNat + c2 then s.get "x0"
        else s.get "x0" - s.get "p0" := by
    simp only [condSub4Block, runBlock_cons, runBlock_nil, BignumCondSubEmit.get_cmovb, BignumCondSubEmit.get_mov, emit_sub_word,
      emit_sub_cf, emit_sub_other, emit_sbb_word, emit_sbb_cf, emit_sbb_other, flagB_cmovb,
      ne_eq, String.reduceEq, not_false_eq_true, reduceIte, decide_eq_true_eq, hc0, hc1, hc2]
  have hd1 : (runBlock s condSub4Block).get "d1"
      = if (s.get "x3").toNat < (s.get "p3").toNat + c2 then s.get "x1"
        else subBorrowWord (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0) := by
    simp only [condSub4Block, runBlock_cons, runBlock_nil, BignumCondSubEmit.get_cmovb, BignumCondSubEmit.get_mov, emit_sub_word,
      emit_sub_cf, emit_sub_other, emit_sbb_word, emit_sbb_cf, emit_sbb_other, flagB_cmovb,
      ne_eq, String.reduceEq, not_false_eq_true, reduceIte, decide_eq_true_eq, hc0, hc1, hc2]
  have hd2 : (runBlock s condSub4Block).get "d2"
      = if (s.get "x3").toNat < (s.get "p3").toNat + c2 then s.get "x2"
        else subBorrowWord (s.get "x2") (s.get "p2") (BitVec.ofNat 1 c1) := by
    simp only [condSub4Block, runBlock_cons, runBlock_nil, BignumCondSubEmit.get_cmovb, BignumCondSubEmit.get_mov, emit_sub_word,
      emit_sub_cf, emit_sub_other, emit_sbb_word, emit_sbb_cf, emit_sbb_other, flagB_cmovb,
      ne_eq, String.reduceEq, not_false_eq_true, reduceIte, decide_eq_true_eq, hc0, hc1, hc2]
  have hd3 : (runBlock s condSub4Block).get "d3"
      = if (s.get "x3").toNat < (s.get "p3").toNat + c2 then s.get "x3"
        else subBorrowWord (s.get "x3") (s.get "p3") (BitVec.ofNat 1 c2) := by
    simp only [condSub4Block, runBlock_cons, runBlock_nil, BignumCondSubEmit.get_cmovb, BignumCondSubEmit.get_mov, emit_sub_word,
      emit_sub_cf, emit_sub_other, emit_sbb_word, emit_sbb_cf, emit_sbb_other, flagB_cmovb,
      ne_eq, String.reduceEq, not_false_eq_true, reduceIte, decide_eq_true_eq, hc0, hc1, hc2]
  -- the carry-in `BitVec 1`s reduce to the c_i and the borrow-outs chain
  have hbinc0 : (BitVec.ofNat 1 c0).toNat = c0 := by rw [hc0]; split_ifs <;> decide
  have hbinc1 : (BitVec.ofNat 1 c1).toNat = c1 := by rw [hc1]; split_ifs <;> decide
  have hbinc2 : (BitVec.ofNat 1 c2).toNat = c2 := by rw [hc2]; split_ifs <;> decide
  have hbo0 : (borrowOutBit (s.get "x0") (s.get "p0") (BitVec.ofNat 1 0)).toNat = c0 := by
    rw [hc0, borrowOutBit]
    simp only [show (BitVec.ofNat 1 0).toNat = 0 from rfl, Nat.add_zero, apply_ite BitVec.toNat]
    rfl
  have hbo1 : (borrowOutBit (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0)).toNat = c1 := by
    rw [hc1, borrowOutBit, hbinc0]; split_ifs <;> decide
  have hbo2 : (borrowOutBit (s.get "x2") (s.get "p2") (BitVec.ofNat 1 c1)).toNat = c2 := by
    rw [hc2, borrowOutBit, hbinc1]; split_ifs <;> decide
  have hbo3 : (borrowOutBit (s.get "x3") (s.get "p3") (BitVec.ofNat 1 c2)).toNat
      = if (s.get "x3").toNat < (s.get "p3").toNat + c2 then 1 else 0 := by
    rw [borrowOutBit, hbinc2]; split_ifs <;> decide
  -- the four SBB reconstructions
  have hr0 := subb_recon (s.get "x0") (s.get "p0") (BitVec.ofNat 1 0)
  have hr1 := subb_recon (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0)
  have hr2 := subb_recon (s.get "x2") (s.get "p2") (BitVec.ofNat 1 c1)
  have hr3 := subb_recon (s.get "x3") (s.get "p3") (BitVec.ofNat 1 c2)
  have hsub0 : subBorrowWord (s.get "x0") (s.get "p0") (BitVec.ofNat 1 0) = s.get "x0" - s.get "p0" := by
    simp [subBorrowWord]
  rw [hbo0, hsub0, hz] at hr0
  rw [hbinc0, hbo1] at hr1
  rw [hbinc1, hbo2] at hr2
  rw [hbinc2, hbo3] at hr3
  -- bounds
  have hd0lt := (s.get "x0" - s.get "p0").isLt
  have hd1lt := (subBorrowWord (s.get "x1") (s.get "p1") (BitVec.ofNat 1 c0)).isLt
  have hd2lt := (subBorrowWord (s.get "x2") (s.get "p2") (BitVec.ofNat 1 c1)).isLt
  have hd3lt := (subBorrowWord (s.get "x3") (s.get "p3") (BitVec.ofNat 1 c2)).isLt
  have hc0le : c0 ≤ 1 := by rw [hc0]; split_ifs <;> omega
  have hc1le : c1 ≤ 1 := by rw [hc1]; split_ifs <;> omega
  have hc2le : c2 ≤ 1 := by rw [hc2]; split_ifs <;> omega
  simp only [valLimbs, mul_zero, add_zero] at hx ⊢
  rw [hd0, hd1, hd2, hd3]
  by_cases hb3 : (s.get "x3").toNat < (s.get "p3").toNat + c2
  · -- borrow ⇒ x < p ⇒ keep x
    simp only [if_pos hb3] at hr3 ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
  · -- no borrow ⇒ x ≥ p ⇒ take x − p
    simp only [if_neg hb3] at hr3 ⊢
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The `bignumVal` corollary — the same value `MultiLimbKernel.condSubLimbs_val` proves. -/
theorem condSub4_bignumVal (s : JState 64)
    (hx : bignumVal [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        < 2 * bignumVal [s.get "p0", s.get "p1", s.get "p2", s.get "p3"]) :
    bignumVal [(runBlock s condSub4Block).get "d0", (runBlock s condSub4Block).get "d1",
        (runBlock s condSub4Block).get "d2", (runBlock s condSub4Block).get "d3"]
      = bignumVal [s.get "x0", s.get "x1", s.get "x2", s.get "x3"]
        % bignumVal [s.get "p0", s.get "p1", s.get "p2", s.get "p3"] := by
  rw [← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal]
  exact condSub4_value s (by rw [valLimbs_eq_bignumVal, valLimbs_eq_bignumVal]; exact hx)

end CatCrypt.Crypto.SecureCompilation.Bignum4CondSubEmit
