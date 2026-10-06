/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs

@[expose] public section

set_option autoImplicit false

/-!
# Reload of a spilled first operand of a compare

The loop exporter prints the guards of a counted loop as `CMP ctr, 0` and its invariant touch
as `CMP ctr, r`, and the spill step of the allocator (`legalizeSpillDst`) keeps a compare
whose counter is in a spill slot as one instruction. The checked encoder
`LprogBytes.encodeLfundefBytesChecked` has no form for a compare whose first operand is a
spill slot. The pass `cmpReload` of this module rewrites such a compare into a copy of the
slot to the reload scratch `reloadScratch` followed by the compare on the scratch, which
sets the same flags; the second operand, an immediate, a register or a spill slot, is kept.

The pass carries no semantic theorem of its own: a route that uses it validates the
rewritten body against the source program (the gate `CellFoldLReg.routeBW` of the wide loop
route), so a body in which the scratch is live at a rewritten compare is refused there.

## Main definitions

* `spillCmp?`: the mnemonic, the slot and the second operand of a compare whose first
  operand is a spill slot.
* `cmpReloadI`, `cmpReload`: the rewrite of an instruction and of a body.

## Main results

* `cmpReload_of_forall`: the pass is the identity on a body without such a compare.
* `spillCmp?_of_mem_cmpReload`, `cmpReload_idem`: the result has no such compare, and the
  pass is idempotent.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- **A compare whose first operand is a spill slot**: for `Lopn [d] opn [d, s]` with
    mnemonic base `CMP`, `d` a spill slot and `s` other than the reload scratch, the
    mnemonic, the slot name and the second operand; `none` for every other instruction. -/
def spillCmp? : LinstrR → Option (String × String × LOperand)
  | .Lopn [.reg d] opn [.reg a, s] =>
      if stripWidthTag opn == "CMP" && d == a && (LOperand.reg d).isSpill
          && s != .reg reloadScratch then some (opn, d, s)
      else none
  | _ => none

/-- The copy mnemonic at the width of the compare `opn`. -/
def movOf (opn : String) : String := if hasSuffix opn ":64" then "MOV:64" else "MOV"

/-- **The rewrite of an instruction**: a compare on a spilled first operand becomes the copy
    of the slot to the reload scratch and the compare on the scratch; every other
    instruction is kept. -/
def cmpReloadI (i : Linstr) : Lcmd :=
  match spillCmp? i.li_i with
  | some (opn, d, s) =>
      [⟨i.li_ii, .Lopn [.reg reloadScratch] (movOf opn) [.reg d]⟩,
       ⟨i.li_ii, .Lopn [.reg reloadScratch] opn [.reg reloadScratch, s]⟩]
  | none => [i]

/-- **The reload of spilled compare operands** on a body. -/
def cmpReload (body : Lcmd) : Lcmd := body.flatMap cmpReloadI

theorem cmpReload_nil : cmpReload [] = [] := rfl

theorem cmpReload_append (a b : Lcmd) : cmpReload (a ++ b) = cmpReload a ++ cmpReload b :=
  List.flatMap_append

/-- An instruction that is no compare on a spilled first operand is kept. -/
theorem cmpReloadI_of_none {i : Linstr} (h : spillCmp? i.li_i = none) : cmpReloadI i = [i] := by
  simp [cmpReloadI, h]

/-- **The pass is the identity on a body without a compare on a spilled first operand.** -/
theorem cmpReload_of_forall {body : Lcmd} (h : ∀ i ∈ body, spillCmp? i.li_i = none) :
    cmpReload body = body := by
  induction body with
  | nil => rfl
  | cons i rest ih =>
      have hi := cmpReloadI_of_none (h i List.mem_cons_self)
      have hr := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
      simp only [cmpReload] at hr ⊢
      rw [List.flatMap_cons, hi, hr]
      rfl

/-- A copy at the mnemonic `movOf opn` is no compare on a spilled first operand. -/
theorem spillCmp?_mov (opn : String) (d s : LOperand) :
    spillCmp? (.Lopn [d] (movOf opn) [s]) = none := by
  simp [spillCmp?]

/-- A compare on the reload scratch is no compare on a spilled first operand. -/
theorem spillCmp?_scratch (opn : String) (s : LOperand) :
    spillCmp? (.Lopn [.reg reloadScratch] opn [.reg reloadScratch, s]) = none := by
  simp [spillCmp?, reloadScratch_not_spill]

/-- No instruction of a rewritten instruction is a compare on a spilled first operand. -/
theorem spillCmp?_of_mem_cmpReloadI {i j : Linstr} (hj : j ∈ cmpReloadI i) :
    spillCmp? j.li_i = none := by
  unfold cmpReloadI at hj
  split at hj
  · rename_i opn d s _
    rcases List.mem_cons.mp hj with rfl | hj
    · exact spillCmp?_mov opn _ _
    · rcases List.mem_singleton.mp hj with rfl
      exact spillCmp?_scratch opn s
  · rename_i hn
    rcases List.mem_singleton.mp hj with rfl
    exact hn

/-- **The result of the pass has no compare on a spilled first operand.** -/
theorem spillCmp?_of_mem_cmpReload {body : Lcmd} {j : Linstr} (hj : j ∈ cmpReload body) :
    spillCmp? j.li_i = none := by
  obtain ⟨i, -, hji⟩ := List.mem_flatMap.mp hj
  exact spillCmp?_of_mem_cmpReloadI hji

/-- The pass is idempotent. -/
theorem cmpReload_idem (body : Lcmd) : cmpReload (cmpReload body) = cmpReload body :=
  cmpReload_of_forall fun _ hj => spillCmp?_of_mem_cmpReload hj

end CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
