/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

@[expose] public section

set_option autoImplicit false

/-!
# The checked encoder accepts no compare on a spilled first operand

`CmpSpillReload.spillCmp?` matches `Lopn [.reg d] opn [.reg d, s]` with mnemonic base `CMP`
(the mnemonics `CMP` and `CMP:64`), `d` a spill slot and `s` any operand other than the
reload scratch. The encoder `LprogBytes.encodeLopn` gives such an instruction no bytes at
every second operand: at an immediate, `encImmOp` returns no bytes for a spill destination;
at a register or a spill slot, the `CMP` arm requires a general-purpose first operand; at an
indexed operand the arm has no case. The instruction is not among the forms of
`carriesNoBytes`, so `encodableLinstrR` is `false` on it.

## Main results

* `encodableLinstrR_spillCmp`: `encodableLinstrR` is `false` on a compare whose first
  operand is a spill slot.
* `spillCmp?_of_encodableLinstrR`, `spillCmp?_of_encodableLcmd`, `spillCmp?_of_checked`: an
  instruction the checked encoder accepts is no such compare, and a body it accepts
  contains none.
* `cmpReload_of_encodableLcmd`, `cmpReload_of_checked`: the pass `cmpReload` is the identity
  on such a body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-- A mnemonic whose base is `CMP` is `CMP` or `CMP:64`. -/
theorem eq_cmp_of_stripWidthTag {opn : String} (h : stripWidthTag opn = "CMP") :
    opn = "CMP" ∨ opn = "CMP:64" := by
  unfold stripWidthTag at h
  split at h
  · rename_i hs
    right
    obtain ⟨t, ht⟩ := List.isSuffixOf_iff_suffix.mp hs
    have h2 : opn.toList = t ++ [':', '6', '4'] := ht.symm
    rw [h2] at h
    have h3 : t = "CMP".toList := by
      have := congrArg String.toList h
      simpa [List.dropLast_append_cons] using this
    rw [← String.ofList_toList (s := opn), h2, h3]
    rfl
  · exact Or.inl h

/-- The name of a spill slot is none of the sixteen general-purpose register names. -/
theorem isGpName_of_spill {d : String} (hk : hasPrefix d "k." = true) : isGpName d = false := by
  unfold isGpName
  split <;> first | rfl | (exfalso; revert hk; decide)

/-- The name of a spill-slot operand has the prefix `k.` on its character list. -/
theorem hasPrefix_of_isSpill {d : String} (h : (LOperand.reg d).isSpill = true) :
    hasPrefix d "k." = true := by
  have he : d.startsWith "k." = "k.".toList.isPrefixOf d.toList := by
    rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]
  have h' : d.startsWith "k." = true := h
  rw [he] at h'
  exact h'

/-- **The encoder has no bytes for a compare whose first operand is a spill slot**, at each
    second operand: `encImmOp` returns no bytes at a spill destination, and the register
    arm of `CMP` requires a general-purpose first operand. -/
theorem encodableLinstrR_spillCmp (frame spillW qsaveB : Nat) {opn d : String} (s : LOperand)
    (ho : stripWidthTag opn = "CMP") (hk : hasPrefix d "k." = true) :
    encodableLinstrR frame spillW (.Lopn [.reg d] opn [.reg d, s]) qsaveB = false := by
  have hg := isGpName_of_spill hk
  have hq : isSpillOrQsave d = true := by simp [isSpillOrQsave, hk]
  have h1 : (isCarryOutBinding opn || isMulHiBinding opn) = false := by
    rcases eq_cmp_of_stripWidthTag ho with rfl | rfl <;> decide +kernel
  have h3 : (opn == "KEEP") = false := by
    rcases eq_cmp_of_stripWidthTag ho with rfl | rfl <;> decide +kernel
  have hm : isMulHiBinding opn = false := by simp at h1; simp [h1]
  have hc : carriesNoBytes (.Lopn [.reg d] opn [.reg d, s]) = false := by
    simp [carriesNoBytes, hm, h3]
  have he : encodeLopn frame spillW (.Lopn [.reg d] opn [.reg d, s]) qsaveB = [] := by
    simp only [encodeLopn, h1, ho,
      show ("CMP" == "MULX") = false from by decide +kernel,
      show ("CMP" == "MULXMEM") = false from by decide +kernel,
      show adxPrefix "CMP" = none from by decide +kernel,
      show tagShiftExt "CMP" = none from by decide +kernel,
      show aluOpcode "CMP" = none from by decide +kernel,
      show twoByteOpcode "CMP" = none from by decide +kernel,
      show ("CMP" == "STOREIDX") = false from by decide +kernel,
      show ("CMP" == "CMP") = true from by decide +kernel,
      Bool.false_eq_true, if_false, if_true]
    cases s <;> simp [encImmOp, hq, hg]
  simp [encodableLinstrR, hc, encodeLinstrR, he]

/-- **An instruction the checked encoder accepts is no compare on a spilled first
    operand.** -/
theorem spillCmp?_of_encodableLinstrR {frame spillW qsaveB : Nat} {i : LinstrR}
    (h : encodableLinstrR frame spillW i qsaveB = true) : spillCmp? i = none := by
  unfold spillCmp?
  split
  · rename_i d opn a s
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨ho, rfl⟩, hsp⟩, -⟩ := hc
      rw [encodableLinstrR_spillCmp frame spillW qsaveB s ho (hasPrefix_of_isSpill hsp)] at h
      cases h
    · rfl
  · rfl

/-- **A body the checked encoder accepts has no compare on a spilled first operand.** -/
theorem spillCmp?_of_encodableLcmd {body : Lcmd} (h : encodableLcmd body = true) :
    ∀ i ∈ body, spillCmp? i.li_i = none := fun i hi =>
  spillCmp?_of_encodableLinstrR (List.all_eq_true.mp h i hi)

/-- The pass `cmpReload` is the identity on a body the checked encoder accepts. -/
theorem cmpReload_of_encodableLcmd {body : Lcmd} (h : encodableLcmd body = true) :
    cmpReload body = body :=
  cmpReload_of_forall (spillCmp?_of_encodableLcmd h)

/-- A body with bytes from `encodeLfundefBytesChecked` has no compare on a spilled first
    operand. -/
theorem spillCmp?_of_checked {body : Lcmd} {bs : List (BitVec 8)}
    (h : encodeLfundefBytesChecked body = some bs) :
    ∀ i ∈ body, spillCmp? i.li_i = none := by
  refine spillCmp?_of_encodableLcmd ?_
  unfold encodeLfundefBytesChecked at h
  split at h
  · assumption
  · cases h

/-- The pass `cmpReload` is the identity on a body with bytes from
    `encodeLfundefBytesChecked`. -/
theorem cmpReload_of_checked {body : Lcmd} {bs : List (BitVec 8)}
    (h : encodeLfundefBytesChecked body = some bs) : cmpReload body = body :=
  cmpReload_of_forall (spillCmp?_of_checked h)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
