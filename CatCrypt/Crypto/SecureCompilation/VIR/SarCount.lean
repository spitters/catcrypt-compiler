/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# The count of an emitted arithmetic right shift

An arithmetic right shift of a width-`w` word by `n` is emitted with the count
`sarCount w n = min n (w - 1)`. Every count from `w - 1` on fills the word with the sign
bit, so the clamped shift equals the requested one (`sshiftRight_sarCount`), and the
clamped count is below `w`, so the hardware's count mask `shiftMask` leaves it unchanged
(`shiftMask_sarCount`). Together: an interpreter that masks the count of a `SAR` computes
`BitVec.sshiftRight a n` on the emitted count (`sshiftRight_shiftMask_sarCount`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

/-- The count an arithmetic right shift of a width-`w` word by `n` is emitted with:
    `min n (w - 1)`. -/
def sarCount (w n : Nat) : Nat := min n (w - 1)

/-- At a positive width the emitted arithmetic-shift count is below the width. -/
theorem sarCount_lt {w : Nat} (hw : 0 < w) (n : Nat) : sarCount w n < w := by
  unfold sarCount; omega

/-- The count mask leaves the emitted arithmetic-shift count unchanged, at every width. -/
theorem shiftMask_sarCount (w n : Nat) : shiftMask w (sarCount w n) = sarCount w n := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [sarCount, shiftMask]
  · exact shiftMask_of_lt (sarCount_lt hw n)

/-- An arithmetic right shift by `n` is the shift by the emitted count `sarCount w n`:
    every amount from `w - 1` on fills the word with the sign bit. -/
theorem sshiftRight_sarCount {w : Nat} (a : BitVec w) (n : Nat) :
    a.sshiftRight (sarCount w n) = a.sshiftRight n := by
  unfold sarCount
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight]
  by_cases hn : n ≤ w - 1
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (Nat.le_of_not_le hn)]
    have h1 : ¬ w ≤ i := Nat.not_le.2 hi
    simp only [h1, decide_false, Bool.not_false, Bool.true_and]
    have h2 : ¬ n + i < w := by omega
    simp only [h2, ↓reduceIte]
    by_cases h3 : w - 1 + i < w
    · have : w - 1 + i = w - 1 := by omega
      simp only [this, BitVec.msb_eq_getLsbD_last, ite_self]
    · simp only [h3, ↓reduceIte]

/-- An interpreter that masks the count of an arithmetic right shift computes the
    requested shift by `n` on the emitted count `sarCount w n`. -/
theorem sshiftRight_shiftMask_sarCount {w : Nat} (a : BitVec w) (n : Nat) :
    a.sshiftRight (shiftMask w (sarCount w n)) = a.sshiftRight n := by
  rw [shiftMask_sarCount]; exact sshiftRight_sarCount a n

end CatCrypt.Crypto.SecureCompilation.VIR
