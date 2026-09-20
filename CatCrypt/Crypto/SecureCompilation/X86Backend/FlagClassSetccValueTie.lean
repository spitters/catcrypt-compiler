/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# Value agreement between the fused `SET<cc>` op and the gathered `JInstr` triple

`JasminLsem.applyOpn` denotes `SET<cc>` as one fused op: the compare and the
materialisation of its result are a single `Lstate` step, and `Lstate` carries no
flags. `GatherFullBody.lowerFlagClassJ` lowers the same `Lopn` to the three
`JInstr`s `cmp a s1`, `mov d 0`, `setcc c d`, over a `JState` that does carry
flags.

The agreement is about registers only. The `JInstr` side writes the five flags of
the compare; the `Lstate` side has no flag component, so the conclusion states
nothing about flags.

## Main results

* `cf_sub_eq_ult`, `zf_sub_eq_beq` — the carry and zero flag of `x86_CMP x y` as
  the unsigned-below and equality predicates on the two words.
* `condB_cmp` — after `evalInstr (.cmp a b)`, the condition code of a
  `JasminCmp` relation reads as that relation on the compared words.
* `setcc_triple_dest` — the gathered triple leaves the destination holding
  `cmpBit` of the compared words at the register width.
* `flagClass_setcc_value_tie` — running the triple `lowerFlagClassJ` produces
  from a `JState` whose registers agree with an `Lstate` leaves the destination
  holding the word `applyOpn` gives the fused op.
* `flagClass_setcc_other_reg` — the triple writes no register but the
  destination.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FlagClassSetccValueTie

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended (lowerJOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody

/-! ## 1. The condition code of a comparison mnemonic -/

/-- The x86 condition code of a `JasminCmp` relation: the code `setccCondOf`
    returns for that relation's `SET<cc>:64` mnemonic. -/
def setccCondt : JasminCmp → Condt
  | .eq => .e
  | .ne => .ne
  | .ult => .b
  | .ule => .be
  | .ugt => .nbe
  | .uge => .nb

/-- `setccCondOf` reads the condition code of a width-tagged comparison mnemonic
    as `setccCondt` of its relation. -/
theorem setccCondOf_cmpName (c : JasminCmp) :
    setccCondOf (withWidthTag 64 (cmpName c)) = some (setccCondt c) := by
  cases c <;> rfl

/-- Every mnemonic `setccCondOf` accepts is the width-tagged comparison mnemonic
    of a `JasminCmp` relation, at the matching condition code. -/
theorem exists_cmp_of_setccCondOf {opn : String} {c : Condt}
    (h : setccCondOf opn = some c) :
    ∃ jc : JasminCmp, opn = withWidthTag 64 (cmpName jc) ∧ c = setccCondt jc := by
  unfold setccCondOf at h
  split at h
  · exact ⟨.eq, by simp_all; decide +kernel, (Option.some.inj h).symm⟩
  · exact ⟨.ne, by simp_all; decide +kernel, (Option.some.inj h).symm⟩
  · exact ⟨.ult, by simp_all; decide +kernel, (Option.some.inj h).symm⟩
  · exact ⟨.ule, by simp_all; decide +kernel, (Option.some.inj h).symm⟩
  · exact ⟨.ugt, by simp_all; decide +kernel, (Option.some.inj h).symm⟩
  · exact ⟨.uge, by simp_all; decide +kernel, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-! ## 2. The flags of a compare -/

/-- The carry flag of `x86_SUB x y` — the `CF` of `x86_CMP x y`, which is the
    same five-flag tuple — is the unsigned-below predicate on the two words. -/
theorem cf_sub_eq_ult {w : Nat} (x y : BitVec w) :
    decide (((x - y).toNat : Int) ≠ (x.toNat : Int) - (y.toNat : Int))
      = decide (x.toNat < y.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  have hsub : (x - y).toNat = (2 ^ w - y.toNat + x.toNat) % 2 ^ w := BitVec.toNat_sub x y
  refine decide_eq_decide.mpr ?_
  by_cases h : x.toNat < y.toNat
  · have he : (2 ^ w - y.toNat + x.toNat) % 2 ^ w = 2 ^ w - y.toNat + x.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hsub, he]
    exact ⟨fun _ => h, fun _ => by omega⟩
  · have he : (2 ^ w - y.toNat + x.toNat) % 2 ^ w = x.toNat - y.toNat := by
      rw [show 2 ^ w - y.toNat + x.toNat = 2 ^ w + (x.toNat - y.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, he]
    exact ⟨fun hne => absurd (by omega : ((x.toNat - y.toNat : Nat) : Int)
        = (x.toNat : Int) - (y.toNat : Int)) hne, fun hlt => by omega⟩

/-- The zero flag of `x86_SUB x y` — the `ZF` of `x86_CMP x y` — is the equality
    predicate on the two words. -/
theorem zf_sub_eq_beq {w : Nat} (x y : BitVec w) :
    ZF_of_word (x - y) = (x == y) := by
  simp only [ZF_of_word]
  refine decide_eq_decide.mpr ?_
  constructor
  · intro h
    have h0 : x - y = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    have := congrArg (· + y) h0
    simpa using this
  · intro h
    subst h
    simp

/-! ## 3. The condition read after a compare -/

/-- After the compare `cmp a b`, the condition code of a `JasminCmp` relation
    reads as that relation on the compared words. This is the step from the
    `JState` flag component to the flag-free `Lstate` comparison. -/
theorem condB_cmp {w : Nat} (s : JState w) (a : String) (b : JOperand) (c : JasminCmp) :
    (evalInstr s (.cmp a b)).condB (setccCondt c) = c.holds (s.get a) (b.eval s) := by
  have hcf : (evalInstr s (.cmp a b)).flagB (·.cf)
      = decide ((s.get a).toNat < (b.eval s).toNat) := by
    simp only [evalInstr, JState.flagB, JState.writeB5, x86_CMP, x86_SUB, Option.getD_some,
      wunsigned]
    exact cf_sub_eq_ult _ _
  have hzf : (evalInstr s (.cmp a b)).flagB (·.zf) = (s.get a == b.eval s) := by
    simp only [evalInstr, JState.flagB, JState.writeB5, x86_CMP, x86_SUB, Option.getD_some]
    exact zf_sub_eq_beq _ _
  have hbeq : (s.get a == b.eval s) = decide ((s.get a).toNat = (b.eval s).toNat) := by
    simp only [← BitVec.toNat_eq]; rfl
  have hbne : (s.get a != b.eval s) = !decide ((s.get a).toNat = (b.eval s).toNat) := by
    rw [← hbeq]; rfl
  cases c <;>
    simp only [setccCondt, JState.condB, x86_eval_cond, Id.run, JasminCmp.holds,
      hcf, hzf, hbeq, hbne, BitVec.ult, BitVec.ule]
  all_goals
    first
      | rfl
      | (refine Bool.eq_iff_iff.mpr ?_
         simp only [bind, pure, Bool.or_eq_true, Bool.and_eq_true,
           Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
         omega)

/-! ## 4. The destination word of the gathered triple -/

/-- Merging a `SETcc` byte into a zeroed destination gives the `0`/`1` word at
    the register width. -/
theorem wordExtendMerge_zero_setcc {w : Nat} (bl : Bool) :
    wordExtendMerge (BitVec.ofNat w 0) (x86_SETcc bl)
      = BitVec.setWidth w (if bl then 1#1 else 0#1) := by
  have hz : (BitVec.ofNat w 0) = (0 : BitVec w) := rfl
  simp only [wordExtendMerge, hz]
  cases bl <;> apply BitVec.eq_of_toNat_eq <;> simp [x86_SETcc]

/-- The destination of a `setcc` holds the `MSB_MERGE` write of the condition
    byte over its previous value. -/
theorem regs_setcc {w : Nat} (s : JState w) (c : Condt) (d : String) :
    (evalInstr s (.setcc c d)).regs d = wordExtendMerge (s.get d) (x86_SETcc (s.condB c)) := by
  simp [evalInstr, JState.setRegMerge, JState.setReg]

/-- The gathered triple `cmp a b ; mov d 0 ; setcc c d` leaves the destination
    holding `cmpBit` of the compared words at the register width — the value the
    fused `SET<cc>` op writes. -/
theorem setcc_triple_dest {w : Nat} (s : JState w) (d a : String) (b : JOperand)
    (c : JasminCmp) :
    (runBlock s [JInstr.cmp a b, JInstr.mov d (JOperand.imm 0),
        JInstr.setcc (setccCondt c) d]).regs d
      = BitVec.setWidth w (cmpBit c (s.get a) (b.eval s)) := by
  have hflags : (evalInstr (evalInstr s (JInstr.cmp a b))
      (JInstr.mov d (JOperand.imm 0))).flags = (evalInstr s (JInstr.cmp a b)).flags := rfl
  have hcond : (evalInstr (evalInstr s (JInstr.cmp a b))
        (JInstr.mov d (JOperand.imm 0))).condB (setccCondt c)
      = c.holds (s.get a) (b.eval s) := by
    rw [show (evalInstr (evalInstr s (JInstr.cmp a b))
          (JInstr.mov d (JOperand.imm 0))).condB (setccCondt c)
        = (evalInstr s (JInstr.cmp a b)).condB (setccCondt c) from by
      simp only [JState.condB, JState.flagB, hflags]]
    exact condB_cmp s a b c
  have hd : (evalInstr (evalInstr s (JInstr.cmp a b))
      (JInstr.mov d (JOperand.imm 0))).get d = BitVec.ofNat w 0 := by
    simp [evalInstr, JState.setReg, JState.get, x86_MOV]
  rw [runBlock_cons, runBlock_cons, runBlock_cons, runBlock_nil, regs_setcc, hd, hcond,
    wordExtendMerge_zero_setcc]
  rfl

/-- The gathered triple writes no register but its destination. -/
theorem setcc_triple_other {w : Nat} (s : JState w) (d a r : String) (b : JOperand)
    (c : Condt) (hr : r ≠ d) :
    (runBlock s [JInstr.cmp a b, JInstr.mov d (JOperand.imm 0),
        JInstr.setcc c d]).regs r = s.regs r := by
  simp [runBlock_cons, runBlock_nil, evalInstr, JState.setRegMerge, JState.setReg,
    JState.writeB5, hr]

/-! ## 5. The value tie -/

/-- The shape of the block `lowerFlagClassJ` produces for a `SET<cc>:64`
    mnemonic, together with the operand restriction its guard enforces. -/
theorem lowerFlagClassJ_setcc {d opn a : String} {c : Condt} {s1 : LOperand}
    {g : List (JInstr 64)} (hcc : setccCondOf opn = some c)
    (hlow : lowerFlagClassJ d opn (.reg a) s1 = some g) :
    g = [JInstr.cmp a (lowerJOperand s1), JInstr.mov d (JOperand.imm 0),
         JInstr.setcc c d] ∧ cmpSrcOk s1 = true := by
  unfold lowerFlagClassJ at hlow
  simp only [hcc] at hlow
  split at hlow
  · exact absurd hlow (by simp)
  · split at hlow
    · rename_i hguard
      exact ⟨(Option.some.inj hlow).symm, by simpa using (by simpa using hguard : _ ∧ _).2⟩
    · exact absurd hlow (by simp)

/-- A compare source the guard admits evaluates to the same word on both sides,
    given register agreement. -/
theorem eval_lowerJOperand_eq {s : Lstate 64} {j : JState 64}
    (hreg : ∀ r, j.regs r = s.lvm r) {o : LOperand} (ho : cmpSrcOk o = true) :
    (lowerJOperand o).eval j = evalOperand s o := by
  cases o with
  | reg n => simpa [lowerJOperand, evalOperand] using hreg n
  | imm v => rfl
  | arr base idx => exact absurd ho (by simp [cmpSrcOk])
  | arrIdx base idx scale => exact absurd ho (by simp [cmpSrcOk])

/-- The `SET<cc>` value tie: run the `JInstr` triple `lowerFlagClassJ` produces
    for a `SET<cc>:64` op from a `JState` whose registers agree with an `Lstate`,
    and the destination register holds the word the fused `applyOpn` arm gives on
    the same operands. The claim is about registers only — the `JInstr` side also
    writes the compare's five flags, and `Lstate` has no flag component. -/
theorem flagClass_setcc_value_tie {d opn a : String} {c : Condt} {s1 : LOperand}
    {g : List (JInstr 64)} {s : Lstate 64} {j : JState 64}
    (hreg : ∀ r, j.regs r = s.lvm r)
    (hcc : setccCondOf opn = some c)
    (hlow : lowerFlagClassJ d opn (.reg a) s1 = some g) :
    applyOpn (stripWidthTag opn) [s.lvm a, evalOperand s s1]
      = some ((runBlock j g).regs d) := by
  obtain ⟨hg, hsrc⟩ := lowerFlagClassJ_setcc hcc hlow
  obtain ⟨jc, hopn, hc⟩ := exists_cmp_of_setccCondOf hcc
  subst hg
  subst hc
  subst hopn
  rw [setcc_triple_dest j d a (lowerJOperand s1) jc,
    stripWidthTag_withWidthTag_cmpName, applyOpn_cmp]
  simp only [JState.get, hreg a, eval_lowerJOperand_eq hreg hsrc]

/-- The `JInstr` triple of a `SET<cc>:64` op writes no register but the
    destination. -/
theorem flagClass_setcc_other_reg {d opn a r : String} {c : Condt} {s1 : LOperand}
    {g : List (JInstr 64)} {j : JState 64}
    (hcc : setccCondOf opn = some c)
    (hlow : lowerFlagClassJ d opn (.reg a) s1 = some g) (hr : r ≠ d) :
    (runBlock j g).regs r = j.regs r := by
  obtain ⟨hg, _⟩ := lowerFlagClassJ_setcc hcc hlow
  subst hg
  exact setcc_triple_other j d a r (lowerJOperand s1) c hr

end CatCrypt.Crypto.SecureCompilation.X86Backend.FlagClassSetccValueTie
