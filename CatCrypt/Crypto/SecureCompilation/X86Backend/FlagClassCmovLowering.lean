/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# A self-contained `JInstr` block for the three-source conditional move

`JasminLsem.applyOpn` denotes `CMOV` as one fused op on three source words — a
condition word whose low bit selects, and the two data words — over an `Lstate`
that carries no flags. A machine conditional move reads a flag an earlier
instruction set, so a single `JInstr.cmov<cc>` denotes a value only relative to
that flag. `lowerCmovSelfContained` is the block that carries its own flag: a
`test` of the condition register against the immediate `1`, followed by a
conditional move at the matching sense.

The condition is the low bit, as `applyOpn` reads it, so the block tests
`c &&& 1` rather than `c` itself and the tie holds for an arbitrary condition
word.

## Main results

* `lowerCmovSelfContained` — the block for `CMOV [c, a, b]` into `d`.
* `zf_test_one` — the zero flag of `test c $1` is the complement of the low bit
  of `c`.
* `flagClass_cmov_value_tie` — running the block from a `JState` whose registers
  agree with an `Lstate` leaves the destination holding the word `applyOpn` gives
  the fused op on the same three source registers.
* `flagClass_cmov_other_reg` — the block writes no register but the destination.
* `zf_test_self` — the zero flag of `test c, c` is the whole-word zero test of
  `c`, the condition the printer and the Lprog byte encoder read.
* `flagClass_cmovSelect_value_tie` — the same value tie for
  `LoweringCoverageCmovSar.lowerCmovJ`, the whole-word-test block
  `GatherFullBody.encJCmovSelect_eq_lopn` byte-matches, on a condition word
  holding `0` or `1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FlagClassCmovLowering

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar (lowerCmovJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim
  (selectW_setWidth_of_lt_two)

/-! ## 1. The block -/

/-- The `JInstr` block of a three-source conditional move `CMOV [c, a, b]` into
    `d`: the data word `a` when the low bit of the condition register `c` is one,
    the data word `b` when it is zero.

    The flag comes from `test c $1`, whose zero flag is set exactly when the low
    bit of `c` is zero. Which conditional move follows depends on which data
    register the destination already names, so that no instruction of the block
    overwrites a source it still has to read:

    * `d = b`: the destination already holds the zero-bit word, and `cmovne d a`
      overwrites it with `a` on a set low bit;
    * `d = a` (and `d ≠ b`): the destination already holds the one-bit word, and
      `cmove d b` overwrites it with `b` on a clear low bit;
    * otherwise `mov d b` materialises the zero-bit word — `mov` writes no flag
      and `d` names neither source — and `cmovne d a` overwrites it on a set low
      bit. -/
def lowerCmovSelfContained (d c a b : String) : List (JInstr 64) :=
  if d == b then
    [JInstr.test c (JOperand.imm 1), JInstr.cmovne d (JOperand.reg a)]
  else if d == a then
    [JInstr.test c (JOperand.imm 1), JInstr.cmove d (JOperand.reg b)]
  else
    [JInstr.test c (JOperand.imm 1), JInstr.mov d (JOperand.reg b),
     JInstr.cmovne d (JOperand.reg a)]

/-! ## 2. The flag of the low-bit test -/

/-- Masking a word with the immediate `1` keeps its low bit: the value of the
    mask as a natural number is the word's residue modulo two. -/
theorem toNat_and_one {w : Nat} (x : BitVec w) :
    (x &&& BitVec.ofNat w 1).toNat = x.toNat % 2 := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    have h0 : x = BitVec.ofNat 0 0 := by
      apply BitVec.eq_of_toNat_eq
      have := x.isLt
      simp only [Nat.pow_zero] at this
      simp only [BitVec.toNat_ofNat]
      omega
    simp [h0]
  · have h2 : 2 ≤ 2 ^ w := by
      calc (2 : Nat) = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
    have h1 : (BitVec.ofNat w 1).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    simp [BitVec.toNat_and, h1, Nat.and_one_is_mod]

/-- The zero field of the flag tuple of `TEST x, $1` is the complement of the low
    bit of `x` — the condition bit the fused `CMOV` op reads. -/
theorem zf_x86_TEST_one {w : Nat} (x : BitVec w) :
    (x86_TEST x (BitVec.ofNat w 1)).zf
      = some (!decide (BitVec.setWidth 1 x = 1#1)) := by
  have hmod : (BitVec.setWidth 1 x = 1#1) = (x.toNat % 2 = 1) := by
    simp [BitVec.toNat_eq, BitVec.toNat_setWidth]
  simp only [x86_TEST, rflags_of_bwop, ZF_of_word, toNat_and_one, hmod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> simp [h]

/-- The zero flag of `test c $1` is the complement of the low bit of `c`: the
    condition bit `applyOpn` reads is set exactly when the flag is clear. -/
theorem zf_test_one {w : Nat} (s : JState w) (c : String) :
    (evalInstr s (JInstr.test c (JOperand.imm 1))).flagB (·.zf)
      = !decide (BitVec.setWidth 1 (s.get c) = 1#1) := by
  simp only [evalInstr, JState.flagB, JState.writeB5, JOperand.eval, JState.get,
    zf_x86_TEST_one, Option.getD_some]
  rfl

/-! ## 3. The value tie -/

/-- The block leaves the destination holding `selectW` of the condition bit on
    the two data words — the value the fused `CMOV` op writes. -/
theorem lowerCmovSelfContained_dest (s : JState 64) (d c a b : String) :
    (runBlock s (lowerCmovSelfContained d c a b)).regs d
      = selectW (BitVec.setWidth 1 (s.get c)) (s.get a) (s.get b) := by
  unfold lowerCmovSelfContained
  by_cases hb : d = b
  · subst hb
    by_cases hc : BitVec.setWidth 1 (s.regs c) = 1#1 <;>
      simp [runBlock, evalInstr, JState.setReg, JState.flagB, JState.writeB5,
        x86_CMOVcc, zf_x86_TEST_one, selectW, hc]
  · rw [ite_eq_right (by simpa using hb)]
    by_cases ha : d = a
    · subst ha
      by_cases hc : BitVec.setWidth 1 (s.regs c) = 1#1 <;>
        simp [runBlock, evalInstr, JState.setReg, JState.flagB, JState.writeB5,
          x86_CMOVcc, zf_x86_TEST_one, selectW, hc]
    · rw [ite_eq_right (by simpa using ha)]
      by_cases hc : BitVec.setWidth 1 (s.regs c) = 1#1 <;>
        simp [runBlock, evalInstr, JState.setReg, JState.flagB, JState.writeB5,
          x86_CMOVcc, x86_MOV, zf_x86_TEST_one, selectW, hc, Ne.symm ha]

/-- The block writes no register but its destination. -/
theorem lowerCmovSelfContained_other (s : JState 64) (d c a b r : String)
    (hr : r ≠ d) :
    (runBlock s (lowerCmovSelfContained d c a b)).regs r = s.regs r := by
  unfold lowerCmovSelfContained
  by_cases hb : d == b
  · simp [hb, runBlock_cons, runBlock_nil, evalInstr, JState.setReg, JState.writeB5, hr]
  · by_cases ha : d == a <;>
      simp [hb, ha, runBlock_cons, runBlock_nil, evalInstr, JState.setReg,
        JState.writeB5, hr]

/-- The `CMOV` value tie: run the block from a `JState` whose registers agree with
    an `Lstate`, and the destination register holds the word the fused `applyOpn`
    arm gives on the same three source registers. The claim is about registers
    only — the `JInstr` side also writes the five flags of the test, and `Lstate`
    has no flag component. -/
theorem flagClass_cmov_value_tie {d c a b : String} {s : Lstate 64} {j : JState 64}
    (hreg : ∀ r, j.regs r = s.lvm r) :
    applyOpn "CMOV" [s.lvm c, s.lvm a, s.lvm b]
      = some ((runBlock j (lowerCmovSelfContained d c a b)).regs d) := by
  rw [applyOpn_select, lowerCmovSelfContained_dest j d c a b]
  simp only [JState.get, hreg]

/-- The `JInstr` block of a three-source `CMOV` writes no register but the
    destination. -/
theorem flagClass_cmov_other_reg {d c a b r : String} {j : JState 64} (hr : r ≠ d) :
    (runBlock j (lowerCmovSelfContained d c a b)).regs r = j.regs r :=
  lowerCmovSelfContained_other j d c a b r hr

/-! ## 4. The whole-word test: the block the byte encoder agrees with

`LprogBytes.encCmovSelect` and `LprogAsmPrinter.renderLopn` materialise the
condition with `test c, c`, whose zero flag is set when the whole condition word
is zero. `LoweringCoverageCmovSar.lowerCmovJ` is that form, so it is the one
`GatherFullBody.encJCmovSelect_eq_lopn` byte-matches. Its value agrees with
`applyOpn`'s low-bit reading on a condition word holding `0` or `1` — the range
the dialect's `reg 1` condition operand occupies — which is the scope condition
`selectW_setWidth_of_lt_two` states. -/

/-- The zero field of the flag tuple of `TEST x, x` is set exactly when the whole
    word `x` is zero. -/
theorem zf_x86_TEST_self {w : Nat} (x : BitVec w) :
    (x86_TEST x x).zf = some (decide (x = 0)) := by
  simp [x86_TEST, rflags_of_bwop, ZF_of_word, BitVec.toNat_eq]

/-- The zero flag of `test c, c` is the whole-word zero test of `c`. -/
theorem zf_test_self {w : Nat} (s : JState w) (c : String) :
    (evalInstr s (JInstr.test c (JOperand.reg c))).flagB (·.zf)
      = decide (s.get c = 0) := by
  simp only [evalInstr, JState.flagB, JState.writeB5, JOperand.eval, JState.get,
    zf_x86_TEST_self, Option.getD_some]
  rfl

/-- The whole-word-test block leaves the destination holding the true value on a
    non-zero condition and the false value on a zero one. The condition register
    is distinct from the destination, since on three distinct names the block
    defaults the false value into the destination before the `test`. -/
theorem lowerCmovJ_dest (s : JState 64) (d c a b : String) (hcd : c ≠ d) :
    (runBlock s (lowerCmovJ d c a b)).regs d
      = if s.get c = 0 then s.get b else s.get a := by
  unfold lowerCmovJ
  by_cases ha : a = d
  · subst ha
    simp [runBlock, evalInstr, JState.setReg, JState.flagB, JState.writeB5,
      JState.get, x86_CMOVcc, zf_x86_TEST_self]
    rfl
  · rw [ite_eq_right (by simpa using ha)]
    by_cases hb : b = d
    · subst hb
      simp [runBlock, evalInstr, JState.setReg, JState.flagB, JState.writeB5,
        JState.get, x86_CMOVcc, zf_x86_TEST_self]
      rfl
    · rw [ite_eq_right (by simpa using hb)]
      simp [runBlock, evalInstr, JState.setReg, JState.flagB, JState.writeB5,
        JState.get, x86_CMOVcc, x86_MOV, zf_x86_TEST_self, hcd, ha]
      rfl

/-- **The byte-matched `CMOV` value tie.** On a condition word holding `0` or
    `1`, the whole-word-test block leaves the destination holding the word the
    fused `applyOpn` arm gives on the same three source registers. The claim is
    about registers only — the `JInstr` side also writes the five flags of the
    test, and `Lstate` has no flag component.

    `hc2` is the scope of the tie rather than an assumption about the machine.
    The block tests the condition register against itself, so its zero flag is
    the whole word's, while `applyOpn "CMOV"` selects on
    `selectW (BitVec.setWidth 1 c)`, which is bit zero. The two agree on `0` and
    `1` and disagree at a condition word of `2`. For a program the front
    produces, the dialect types the condition `reg 1` in
    `select w : [reg 1, reg w, reg w] → reg w`, so a wider word cannot arise and
    `hc2` is discharged by the typing. An `Lopn` written by hand or introduced by
    a post-pass carries no such guarantee.

    The block that agrees at every condition word is `lowerCmovSelfContained`,
    which tests against the immediate `1`. It needs no scope condition and does
    not byte-match `encodeLopn`: `test r, $1` encodes as `REX.W F7 /0 id`,
    against `REX.W 85 /r` for the self-test. -/
theorem flagClass_cmovSelect_value_tie {d c a b : String} {s : Lstate 64}
    {j : JState 64} (hreg : ∀ r, j.regs r = s.lvm r) (hcd : c ≠ d)
    (hc2 : (s.lvm c).toNat < 2) :
    applyOpn "CMOV" [s.lvm c, s.lvm a, s.lvm b]
      = some ((runBlock j (lowerCmovJ d c a b)).regs d) := by
  rw [applyOpn_select, lowerCmovJ_dest j d c a b hcd,
    selectW_setWidth_of_lt_two _ _ _ hc2]
  simp only [JState.get, hreg]

/-- The whole-word-test block writes no register but its destination. -/
theorem lowerCmovJ_other (s : JState 64) (d c a b r : String) (hr : r ≠ d) :
    (runBlock s (lowerCmovJ d c a b)).regs r = s.regs r := by
  unfold lowerCmovJ
  by_cases ha : a == d
  · simp [ha, runBlock_cons, runBlock_nil, evalInstr, JState.setReg,
      JState.writeB5, hr]
  · by_cases hb : b == d <;>
      simp [ha, hb, runBlock_cons, runBlock_nil, evalInstr, JState.setReg,
        JState.writeB5, hr]

end CatCrypt.Crypto.SecureCompilation.X86Backend.FlagClassCmovLowering
