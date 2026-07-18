/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# An emitted multi-limb subtract proven against the multi-limb proof stack

> **`@kat-target`.** Hand-authored leaf block + direct `runBlock` proof — a KAT oracle /
> prototype for the bridge technique, NOT the canonical artifact. New field ops go via the
> golden path (`FieldEmitGoldenPath`; see `EMIT_PROVENANCE.md`); do not extend by hand.

The `SBB` borrow-chain analogue of `BignumAddEmit`: a two-limb subtract-with-borrow
over the `JInstr`/`JState` x86 machine, whose `runBlock` value is proven — symbolically,
for all inputs — to satisfy the multi-limb subtract identity in `bignumVal` terms.

```
sbb a0, b0    -- a0 := a0 - b0 - CF,  CF := borrow
sbb a1, b1    -- a1 := a1 - b1 - CF,  CF := borrow
```

`sub2sbb_value` proves `valLimbs[out] + valLimbs[b] = valLimbs[a] + borrow·2^128`
(the borrow dual of the add's carry identity), and `sub2sbb_bignumVal` reads it through
`valLimbs_eq_bignumVal` into the `bignumVal` world — the same identity
`MultiLimbKernel.subLimbs_val` proves for the verified two's-complement subtract. With
the add (`BignumAddEmit`) and now the subtract emitted-and-bridged, the additive Barrett
steps (`x − q·p`) connect the emitted x86 machine to the List-bignum stack.
-/

namespace CatCrypt.Crypto.SecureCompilation.BignumSubEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-- The two-limb subtract-with-borrow kernel body over `JInstr 64`. -/
def sub2sbbBlock : List (JInstr 64) :=
  [ .sbb "a0" (.reg "b0"), .sbb "a1" (.reg "b1") ]

/-- **Symbolic value-correctness of the emitted subtract block.** With `CF` cleared on
    entry, the two output limbs plus the subtrahend equal the minuend plus the
    borrow-out scaled into the top — for all inputs, over the validated x86 machine. -/
theorem sub2sbb_value (s : JState 64) (hcf : s.flagB (·.cf) = false) :
    valLimbs [(runBlock s sub2sbbBlock).get "a0", (runBlock s sub2sbbBlock).get "a1"]
        + valLimbs [s.get "b0", s.get "b1"]
      = valLimbs [s.get "a0", s.get "a1"]
        + (if (runBlock s sub2sbbBlock).flagB (·.cf) then 1 else 0) * 2 ^ 128 := by
  have hrun : runBlock s sub2sbbBlock
      = evalInstr (evalInstr s (.sbb "a0" (.reg "b0"))) (.sbb "a1" (.reg "b1")) := rfl
  -- inner step readouts (CF cleared ⇒ borrow-in 0)
  have h1cf : (evalInstr s (.sbb "a0" (.reg "b0"))).flagB (·.cf)
      = decide ((s.get "a0").toNat < (s.get "b0").toNat + (BitVec.ofNat 1 0).toNat) := by
    rw [emit_sbb_cf, hcf]; simp
  have h1a1 : (evalInstr s (.sbb "a0" (.reg "b0"))).get "a1" = s.get "a1" :=
    emit_sbb_other s "a0" "b0" "a1" (by decide)
  have h1b1 : (evalInstr s (.sbb "a0" (.reg "b0"))).get "b1" = s.get "b1" :=
    emit_sbb_other s "a0" "b0" "b1" (by decide)
  set bo0 := borrowOutBit (s.get "a0") (s.get "b0") (BitVec.ofNat 1 0) with hbo0
  have hcond0 : (BitVec.ofNat 1 0).toNat = 0 := rfl
  -- the inner borrow-out is the carry-in of the outer step (BitVec and Nat forms)
  have hbin1 : (BitVec.ofNat 1 (if (evalInstr s (.sbb "a0" (.reg "b0"))).flagB (·.cf) then 1 else 0))
      = bo0 := by
    rw [h1cf, hbo0, borrowOutBit]; simp only [decide_eq_true_eq]; split_ifs <;> rfl
  have hbin1n : (if (evalInstr s (.sbb "a0" (.reg "b0"))).flagB (·.cf) then (1 : Nat) else 0)
      = bo0.toNat := by
    rw [h1cf, hbo0, borrowOutBit]; simp only [decide_eq_true_eq]; split_ifs <;> simp
  -- outer step readouts
  have ha0 : (runBlock s sub2sbbBlock).get "a0"
      = subBorrowWord (s.get "a0") (s.get "b0") (BitVec.ofNat 1 0) := by
    rw [hrun, emit_sbb_other _ "a1" "b1" "a0" (by decide), emit_sbb_word, hcf]; simp
  have ha1 : (runBlock s sub2sbbBlock).get "a1"
      = subBorrowWord (s.get "a1") (s.get "b1") bo0 := by
    rw [hrun, emit_sbb_word, h1a1, h1b1, hbin1]
  have hcfout : (runBlock s sub2sbbBlock).flagB (·.cf)
      = decide ((s.get "a1").toNat < (s.get "b1").toNat + bo0.toNat) := by
    rw [hrun, emit_sbb_cf, h1a1, h1b1, hbin1n]
  -- reconstruct each limb (low word + borrow reassemble the true difference)
  have hd0 := subb_recon (s.get "a0") (s.get "b0") (BitVec.ofNat 1 0)
  have hd1 := subb_recon (s.get "a1") (s.get "b1") bo0
  rw [← hbo0] at hd0
  have hbo1 : (if (runBlock s sub2sbbBlock).flagB (·.cf) then (1 : Nat) else 0)
      = (borrowOutBit (s.get "a1") (s.get "b1") bo0).toNat := by
    rw [hcfout, borrowOutBit]; simp only [decide_eq_true_eq]; split_ifs <;> simp
  simp only [valLimbs, mul_zero, add_zero, ha0, ha1]
  rw [hbo1]
  omega

/-- **The emitted block satisfies the multi-limb subtract identity in `bignumVal`.**
    `bignumVal[out] + bignumVal[b] = bignumVal[a] + borrow·2^128` — the same identity
    `MultiLimbKernel.subLimbs_val` proves for the verified two's-complement subtract. -/
theorem sub2sbb_bignumVal (s : JState 64) (hcf : s.flagB (·.cf) = false) :
    bignumVal [(runBlock s sub2sbbBlock).get "a0", (runBlock s sub2sbbBlock).get "a1"]
        + bignumVal [s.get "b0", s.get "b1"]
      = bignumVal [s.get "a0", s.get "a1"]
        + (if (runBlock s sub2sbbBlock).flagB (·.cf) then 1 else 0) * 2 ^ 128 := by
  rw [← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal]
  exact sub2sbb_value s hcf

end CatCrypt.Crypto.SecureCompilation.BignumSubEmit
