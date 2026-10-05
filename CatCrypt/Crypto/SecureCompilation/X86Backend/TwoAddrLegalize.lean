/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# Two-address legalisation of the owned `Lprog` before printing

`LprogAsmPrinter.renderLopn` prints a two-source instruction `Lopn [d] opn [a, b]`
whose mnemonic satisfies `needsTie` as the x86 two-address
`op b, d`, which denotes `d := d op b`. The linear semantics
`JasminLsem.lsemStep` gives the instruction the meaning `d := a op b` for every
choice of names, so the printed instruction and the model agree exactly when
`a = d` (`tiedOk`). `legalizeInstr` rewrites an instruction with
`a ≠ d` into instructions that satisfy the precondition:

* `mov d, a; op d, [d, b]` when `b` does not read `d` and `d`, `a` are not both
  memory operands;
* `op d, [d, a]` when `b = d` and the base of `op` is one of `commBases`;
* `mov qsave.R15, R15; mov R15, a; op R15, [R15, b]; mov d, R15; mov R15, qsave.R15`
  (`scratchRoute`) through the exporter's reserved scratch register `reloadScratch`,
  saved in and restored from the frame slot `scratchSave`, when no operand of the body
  names the register or the slot, with `mov R15, d; op R15, [R15, a]` in the middle when
  moreover `b = d` and the base of `op` is one of `commBases` (both `d` and `a` are then
  memory operands);
* for the flag-only `CMP` and `TEST`, which write no register on the machine,
  the destination becomes the first source.

An instruction none of these applies to (a narrow width tag, a first source that
is neither a register nor an immediate, a body that names the scratch register)
is kept, `bodyTiedOk` reports it, and the printer refuses it.

## Main results

* `tiedOk`, `bodyTiedOk`: the precondition on one instruction and on a body.
* `legalizeInstr_of_tiedOk`, `twoAddrBody_of_bodyTiedOk`: legalisation is the
  identity on an instruction and on a body that satisfy the precondition.
* `legalizeInstr_tiedOk`: every instruction `legalizeInstr` emits satisfies the
  precondition or is the input instruction.
* `scratchRoute_lsem`: the scratch route computes the operation and restores the
  scratch register.
* `legalizeInstr_lsem`: one instruction and its legalisation, run from states that
  agree on memory and on every name other than the save slot `scratchSave` (on every
  name when the scratch route is off), end in states that agree in the same way.
* `twoAddrBody_lsemStraight`: a straight-line body and its legalisation, run from
  one state, end with equal memory and equal values at every name other than
  `scratchSave`, and at every name when the body names the scratch register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (isMemOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
  (opNames readNames lsemStep_agreeOn evalOperand_agreeOn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (lsemStep_reg_nonmem)

/-! ## 1. The printer's precondition

The mnemonic data `tieBase`, `tiedBases`, `needsTie`, `commBases`, `movFor` and the x86
instruction-set data `x86Data` are defined in `VIR.X86IsaData`. -/

/-- The precondition of the two-address arm of `renderLopn` on one instruction: an
    instruction `Lopn [d] opn [a, b]` printed as `op b, d` has `a = d`. -/
def tiedOk : LinstrR → Bool
  | .Lopn [.reg d] opn [a, b] => !needsTie opn b || a == .reg d
  | _ => true

/-! ## 2. The rewrite -/

/-- A register or an immediate operand. -/
def isRegOrImm : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- Whether a name mentions the scratch register `x86Data.tieScratch` (`R15`): it is the
    register or its save slot `qsave.R15`, or holds it as a substring (a `mem.<base>.<off>`
    name with base `R15`). -/
def mentionsScratch (n : String) : Bool :=
  n == x86Data.tieScratch || n == "qsave." ++ x86Data.tieScratch ||
    (n.splitOn x86Data.tieScratch).length != 1

/-- An operand none of whose names mentions the scratch register. -/
def opAvoids : LOperand → Bool
  | .reg n => !mentionsScratch n
  | .arr b _ => !mentionsScratch b
  | .arrIdx b x _ => !mentionsScratch b && !mentionsScratch x
  | .imm _ => true

/-- An instruction none of whose operand names mentions the scratch register. -/
def instrAvoids : LinstrR → Bool
  | .Lopn ds _ ss => ds.all opAvoids && ss.all opAvoids
  | .Lcond c _ => opAvoids c
  | .Ligoto t => opAvoids t
  | .LstoreLabel d _ => !mentionsScratch d
  | .Lcall (some r) _ => !mentionsScratch r
  | _ => true

/-- A body none of whose instructions names the scratch register. -/
def bodyAvoids (body : Lcmd) : Bool := body.all (fun i => instrAvoids i.li_i)

/-- The body satisfies the printer's two-address precondition. -/
def bodyTiedOk (body : Lcmd) : Bool := body.all (fun i => tiedOk i.li_i)

/-- The save slot of the scratch register: the frame cell `qsave.R15`. A body that does not
    name the scratch register does not name this slot (`mentionsScratch_scratchSave`). -/
def scratchSave : String := "qsave." ++ x86Data.tieScratch

/-- The scratch route of `opn d, [a, b]`: save the scratch register, compute
    `opn R15, [a, b]` on it by a copy and the tied operation, move the result into `d`, and
    restore the scratch register. -/
def scratchRoute (ii : Nat) (opn m d : String) (a b : LOperand) : List Linstr :=
  [⟨ii, .Lopn [.reg scratchSave] "MOV:64" [.reg x86Data.tieScratch]⟩,
   ⟨ii, .Lopn [.reg x86Data.tieScratch] m [a]⟩,
   ⟨ii, .Lopn [.reg x86Data.tieScratch] opn [.reg x86Data.tieScratch, b]⟩,
   ⟨ii, .Lopn [.reg d] m [.reg x86Data.tieScratch]⟩,
   ⟨ii, .Lopn [.reg x86Data.tieScratch] "MOV:64" [.reg scratchSave]⟩]

/-- Legalise one instruction; `ok` enables the route through `reloadScratch`. -/
def legalizeInstr (ok : Bool) (i : Linstr) : List Linstr :=
  match i.li_i with
  | .Lopn [.reg d] opn [a, b] =>
      if x86Data.tied opn b && a != .reg d then
        match x86Data.copyMnemonic opn with
        | none => [i]
        | some m =>
          if tieBase opn == "CMP" || tieBase opn == "TEST" then
            match a with
            | .reg x => [⟨i.li_ii, .Lopn [.reg x] opn [.reg x, b]⟩]
            | _ => [i]
          else if !isRegOrImm a then [i]
          else if !(opNames b).contains d && !(isMemOperand (.reg d) && isMemOperand a) then
            [⟨i.li_ii, .Lopn [.reg d] m [a]⟩, ⟨i.li_ii, .Lopn [.reg d] opn [.reg d, b]⟩]
          else if x86Data.commutes (tieBase opn) && b == .reg d
              && !(isMemOperand (.reg d) && isMemOperand a) then
            [⟨i.li_ii, .Lopn [.reg d] opn [.reg d, a]⟩]
          else if ok then
            if x86Data.commutes (tieBase opn) && b == .reg d then
              scratchRoute i.li_ii opn m d (.reg d) a
            else
              scratchRoute i.li_ii opn m d a b
          else [i]
      else [i]
  | _ => [i]

/-- Legalise a body, with the scratch route on when no instruction names the scratch
    register. -/
def twoAddrBody (body : Lcmd) : Lcmd :=
  LegalizeShiftImm.legalizeBody (legalizeInstr (bodyAvoids body)) body

/-! ## 3. Legalised instructions satisfy the precondition -/

/-- Legalisation is the identity on an instruction that satisfies the precondition. -/
theorem legalizeInstr_of_tiedOk (ok : Bool) (i : Linstr) (h : tiedOk i.li_i = true) :
    legalizeInstr ok i = [i] := by
  unfold legalizeInstr
  split
  · rename_i d opn a b hi
    rw [hi] at h
    simp only [tiedOk, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · simp [h]
    · have ha : a = .reg d := by simpa using h
      simp [ha]
  · rfl

/-- Legalisation is the identity on a body that satisfies the precondition. -/
theorem twoAddrBody_of_bodyTiedOk (body : Lcmd) (h : bodyTiedOk body = true) :
    twoAddrBody body = body := by
  unfold twoAddrBody LegalizeShiftImm.legalizeBody
  simp only [bodyTiedOk, List.all_eq_true] at h
  rw [List.flatMap_congr (fun i hi => legalizeInstr_of_tiedOk _ i (h i hi))]
  simp

/-- Every instruction `legalizeInstr` emits satisfies the printer's precondition or
    is the input instruction. -/
theorem legalizeInstr_tiedOk (ok : Bool) (i : Linstr) :
    ∀ j ∈ legalizeInstr ok i, tiedOk j.li_i = true ∨ j = i := by
  intro j hj
  unfold legalizeInstr at hj
  split at hj
  · split at hj
    · split at hj
      · simp at hj; exact Or.inr hj
      · split at hj
        · split at hj
          · simp at hj; subst hj; left; simp [tiedOk]
          · simp at hj; exact Or.inr hj
        · split at hj
          · simp at hj; exact Or.inr hj
          · split at hj
            · simp at hj; rcases hj with rfl | rfl <;> left <;> simp [tiedOk]
            · split at hj
              · simp at hj; subst hj; left; simp [tiedOk]
              · split at hj
                · split at hj <;>
                    (simp only [scratchRoute, List.mem_cons, List.not_mem_nil, or_false] at hj
                     rcases hj with rfl | rfl | rfl | rfl | rfl <;> left <;> simp [tiedOk])
                · simp at hj; exact Or.inr hj
    · simp at hj; exact Or.inr hj
  · simp at hj; exact Or.inr hj

open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (isIndexed linstrRDirect lcmdDirect lcmdDirect_iff) in
/-- Legalisation keeps an instruction free of register-indexed operands. -/
theorem legalizeInstr_direct (ok : Bool) (i : Linstr) (h : linstrRDirect i.li_i = true) :
    ∀ j ∈ legalizeInstr ok i, linstrRDirect j.li_i = true := by
  intro j hj
  have h0 := h
  unfold legalizeInstr at hj
  split at hj
  · rename_i d opn a b hi
    rw [hi] at h
    simp only [linstrRDirect, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
    repeat' split at hj
    all_goals
      simp only [scratchRoute, List.mem_cons, List.mem_nil_iff, or_false] at hj
      repeat' (rcases hj with rfl | hj)
    all_goals first
      | exact h0
      | simp_all [linstrRDirect, isIndexed]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    subst hj
    exact h

open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (linstrRDirect lcmdDirect lcmdDirect_iff) in
/-- Legalisation keeps a body free of register-indexed operands. -/
theorem twoAddrBody_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (twoAddrBody body) = true := by
  rw [lcmdDirect_iff] at h ⊢
  intro j hj
  simp only [twoAddrBody, LegalizeShiftImm.legalizeBody, List.mem_flatMap] at hj
  obtain ⟨i, hi, hj⟩ := hj
  exact legalizeInstr_direct _ i (h i hi) j hj

/-! ## 4. Semantics -/

variable {w : Nat}

/-- The names at which a legalised run agrees with its source: every name other than
    `scratchSave` when the scratch route is on, every name otherwise. -/
def Kept (ok : Bool) (x : String) : Prop := ok = true → x ≠ scratchSave

/-- The names of an operand that avoids the scratch register do not mention it. -/
theorem not_mentionsScratch_of_opAvoids {o : LOperand} (h : opAvoids o = true) :
    ∀ x ∈ opNames o, mentionsScratch x = false := by
  intro x hx
  cases o <;> simp_all [opNames, opAvoids]

theorem mentionsScratch_reloadScratch : mentionsScratch reloadScratch = true := by
  simp [mentionsScratch]

theorem mentionsScratch_scratchSave : mentionsScratch scratchSave = true := by
  simp [mentionsScratch, scratchSave]

theorem ne_of_opAvoids {o : LOperand} (h : opAvoids o = true) :
    ∀ x ∈ opNames o, x ≠ reloadScratch := by
  intro x hx hxe
  have := not_mentionsScratch_of_opAvoids h x hx
  rw [hxe, mentionsScratch_reloadScratch] at this
  cases this

theorem ne_scratchSave_of_opAvoids {o : LOperand} (h : opAvoids o = true) :
    ∀ x ∈ opNames o, x ≠ scratchSave := by
  intro x hx hxe
  have := not_mentionsScratch_of_opAvoids h x hx
  rw [hxe, mentionsScratch_scratchSave] at this
  cases this

theorem scratchSave_ne_reloadScratch : scratchSave ≠ reloadScratch := by
  decide +kernel

/-- The names an instruction reads are kept when it avoids the scratch register. -/
theorem readNames_kept (ok : Bool) (i : LinstrR) (hav : ok = true → instrAvoids i = true) :
    ∀ x ∈ readNames i, Kept ok x := by
  intro x hx hok
  have ha := hav hok
  cases i with
  | Lopn ds opn ss =>
      simp only [readNames, List.mem_flatMap, List.mem_append] at hx
      obtain ⟨o, ho, hxo⟩ := hx
      simp only [instrAvoids, Bool.and_eq_true, List.all_eq_true] at ha
      rcases ho with ho | ho
      · exact ne_scratchSave_of_opAvoids (ha.1 o ho) x hxo
      · exact ne_scratchSave_of_opAvoids (ha.2 o ho) x hxo
  | Lcond c _ => exact ne_scratchSave_of_opAvoids ha x hx
  | _ => simp [readNames] at hx

theorem movFor_some {opn m : String} (h : movFor opn = some m) :
    (opn = tieBase opn ∧ m = "MOV") ∨ (opn = tieBase opn ++ ":64" ∧ m = "MOV:64") := by
  unfold movFor at h
  split at h
  · rename_i h1
    exact Or.inl ⟨by simpa using h1, (Option.some.inj h).symm⟩
  · split at h
    · rename_i _ h2
      exact Or.inr ⟨by simpa using h2, (Option.some.inj h).symm⟩
    · cases h

/-- A mnemonic with a copy at its width is its base with the `:64` tag stripped. -/
theorem stripWidthTag_of_movFor {opn m : String} (h : movFor opn = some m) :
    stripWidthTag opn = tieBase opn := by
  have hc : ':' ∉ (tieBase opn).toList := by
    simp only [tieBase, String.toList_ofList]
    intro hm
    have h2 := List.all_eq_true.mp (List.all_takeWhile (p := (· != ':')) (l := opn.toList)) _ hm
    simp at h2
  have hs := movFor_some h
  generalize tieBase opn = t at hc hs ⊢
  rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · unfold stripWidthTag hasSuffix
    rw [if_neg]
    intro hs
    obtain ⟨l, hl⟩ := List.isSuffixOf_iff_suffix.mp hs
    exact hc (hl ▸ List.mem_append_right l (by decide))
  · unfold stripWidthTag hasSuffix
    have e : (t ++ ":64").toList = t.toList ++ [':', '6', '4'] := by
      rw [String.toList_append]; rfl
    have hsuf : (":64".toList).isSuffixOf (t.toList ++ [':', '6', '4']) = true :=
      List.isSuffixOf_iff_suffix.mpr (List.suffix_append _ _)
    rw [e, if_pos hsuf]
    simp

theorem stripWidthTag_movFor {opn m : String} (h : movFor opn = some m) :
    stripWidthTag m = "MOV" := by
  rcases movFor_some h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide +kernel

theorem applyOpn_movFor {opn m : String} (h : movFor opn = some m) (v : BitVec w) :
    applyOpn (stripWidthTag m) [v] = some v := by
  rw [stripWidthTag_movFor h]
  rfl

theorem movFor_ne {opn m : String} (h : movFor opn = some m) :
    m ≠ "LOADIDX" ∧ m ≠ "STOREIDX" := by
  rcases movFor_some h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

theorem needsTie_ne {opn : String} {b : LOperand} (h : needsTie opn b = true) :
    opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" := by
  have h1 : tieBase "LOADIDX" = "LOADIDX" := by decide +kernel
  have h2 : tieBase "STOREIDX" = "STOREIDX" := by decide +kernel
  constructor <;> rintro rfl <;> cases b <;> simp_all [needsTie, tiedBases]

/-- A commutative base at an untagged or `:64`-tagged mnemonic applies to swapped
    sources with the same result. -/
theorem applyOpn_comm {opn m : String} (hm : movFor opn = some m)
    (hc : commBases.contains (tieBase opn) = true) (x y : BitVec w) :
    applyOpn (stripWidthTag opn) [x, y] = applyOpn (stripWidthTag opn) [y, x] := by
  simp only [commBases, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff,
    or_false] at hc
  rcases movFor_some hm with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases hc with hc | hc | hc | hc | hc <;> rw [hc] at h1 <;> subst h1 <;>
    · first
        | rw [show stripWidthTag "ADD" = "ADD" by decide +kernel]
        | rw [show stripWidthTag "MUL" = "MUL" by decide +kernel]
        | rw [show stripWidthTag "AND" = "AND" by decide +kernel]
        | rw [show stripWidthTag "OR" = "OR" by decide +kernel]
        | rw [show stripWidthTag "XOR" = "XOR" by decide +kernel]
        | rw [show stripWidthTag ("ADD" ++ ":64") = "ADD" by decide +kernel]
        | rw [show stripWidthTag ("MUL" ++ ":64") = "MUL" by decide +kernel]
        | rw [show stripWidthTag ("AND" ++ ":64") = "AND" by decide +kernel]
        | rw [show stripWidthTag ("OR" ++ ":64") = "OR" by decide +kernel]
        | rw [show stripWidthTag ("XOR" ++ ":64") = "XOR" by decide +kernel]
      simp only [applyOpn, BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm,
        BitVec.or_comm, BitVec.xor_comm]

/-- The flag-only compares are outside the word-op fragment of `applyOpn`. -/
theorem applyOpn_cmp_none {opn m : String} (hm : movFor opn = some m)
    (hc : (tieBase opn == "CMP" || tieBase opn == "TEST") = true) (x y : BitVec w) :
    applyOpn (stripWidthTag opn) [x, y] = none := by
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  rcases movFor_some hm with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases hc with hc | hc <;> rw [hc] at h1 <;> subst h1
  · rw [show stripWidthTag "CMP" = "CMP" by decide +kernel]; rfl
  · rw [show stripWidthTag "TEST" = "TEST" by decide +kernel]; rfl
  · rw [show stripWidthTag ("CMP" ++ ":64") = "CMP" by decide +kernel]; rfl
  · rw [show stripWidthTag ("TEST" ++ ":64") = "TEST" by decide +kernel]; rfl

theorem step_reg {d opn : String} {srcs : List LOperand} {s : Lstate w} {v : BitVec w}
    (hne : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX")
    (hv : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) = some v) :
    lsemStep (.Lopn [.reg d] opn srcs) s = some ((s.setReg d v).nextPc) := by
  rw [lsemStep_reg_nonmem d opn srcs s hne, hv]

theorem step_reg_inv {d opn : String} {srcs : List LOperand} {s t : Lstate w}
    (hne : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX")
    (h : lsemStep (.Lopn [.reg d] opn srcs) s = some t) :
    ∃ v, applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) = some v ∧
      t = (s.setReg d v).nextPc := by
  rw [lsemStep_reg_nonmem d opn srcs s hne] at h
  cases hv : applyOpn (w := w) (stripWidthTag opn) (srcs.map (evalOperand s)) with
  | none => rw [hv] at h; cases h
  | some v => rw [hv] at h; exact ⟨v, rfl, (Option.some.inj h).symm⟩

/-- Writing a name no operand name of `o` equals leaves the value of `o`. -/
theorem evalOperand_setReg_nextPc {s : Lstate w} {d : String} {v : BitVec w} {o : LOperand}
    (h : d ∉ opNames o) : evalOperand ((s.setReg d v).nextPc) o = evalOperand s o :=
  evalOperand_agreeOn (s := (s.setReg d v).nextPc) (t := s) rfl o (fun x hx => by
    have hxd : x ≠ d := fun hxd => h (hxd ▸ hx)
    simp [Lstate.setReg, Lstate.nextPc, hxd])

theorem applyOpn_mov64 (v : BitVec w) : applyOpn (stripWidthTag "MOV:64") [v] = some v := by
  rw [show stripWidthTag "MOV:64" = "MOV" by decide +kernel]
  rfl

/-- **The scratch route against the operation.** When `opn d, [a, b]` steps to the value `v`
    at `d`, its scratch route runs to a state with the same memory and the same value at every
    name other than `scratchSave`; the scratch register is restored. -/
theorem scratchRoute_lsem {opn m d : String} {a b : LOperand} (ii : Nat)
    (hm : movFor opn = some m) (hne : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX")
    (hdR : d ≠ reloadScratch) (hdS : d ≠ scratchSave)
    (haS : scratchSave ∉ opNames a) (hbR : reloadScratch ∉ opNames b)
    (hbS : scratchSave ∉ opNames b) (s : Lstate w) {v : BitVec w}
    (hv : applyOpn (stripWidthTag opn) [evalOperand s a, evalOperand s b] = some v) :
    ∃ t', lsemStraight ((scratchRoute ii opn m d a b).map Linstr.li_i) s = some t' ∧
      ((s.setReg d v).nextPc).lmem = t'.lmem ∧
      ∀ x, x ≠ scratchSave → ((s.setReg d v).nextPc).lvm x = t'.lvm x := by
  have hmne := movFor_ne hm
  have h64 : "MOV:64" ≠ "LOADIDX" ∧ "MOV:64" ≠ "STOREIDX" := by decide
  have hSR := scratchSave_ne_reloadScratch
  let s1 := (s.setReg scratchSave (evalOperand s (.reg reloadScratch))).nextPc
  let s2 := (s1.setReg reloadScratch (evalOperand s a)).nextPc
  let s3 := (s2.setReg reloadScratch v).nextPc
  let s4 := (s3.setReg d v).nextPc
  let s5 := (s4.setReg reloadScratch (evalOperand s (.reg reloadScratch))).nextPc
  have e1 : lsemStep (.Lopn [.reg scratchSave] "MOV:64" [.reg reloadScratch]) s = some s1 :=
    step_reg h64 (by simpa using applyOpn_mov64 (evalOperand s (.reg reloadScratch)))
  have e2 : lsemStep (.Lopn [.reg reloadScratch] m [a]) s1 = some s2 :=
    step_reg hmne (by
      simpa [s1, evalOperand_setReg_nextPc haS] using applyOpn_movFor hm (evalOperand s a))
  have e3 : lsemStep (.Lopn [.reg reloadScratch] opn [.reg reloadScratch, b]) s2 = some s3 := by
    refine step_reg hne ?_
    simp only [s2, s1, List.map_cons, List.map_nil, evalOperand_setReg_nextPc hbR,
      evalOperand_setReg_nextPc hbS]
    simpa [evalOperand, Lstate.setReg, Lstate.nextPc] using hv
  have e4 : lsemStep (.Lopn [.reg d] m [.reg reloadScratch]) s3 = some s4 :=
    step_reg hmne (by
      simpa [s3, evalOperand, Lstate.setReg, Lstate.nextPc] using applyOpn_movFor hm v)
  have e5 : lsemStep (.Lopn [.reg reloadScratch] "MOV:64" [.reg scratchSave]) s4 = some s5 :=
    step_reg h64 (by
      simpa [s4, s3, s2, s1, evalOperand, Lstate.setReg, Lstate.nextPc, hdS.symm, hSR] using
        applyOpn_mov64 (evalOperand s (.reg reloadScratch)))
  refine ⟨s5, by simp only [scratchRoute, List.map_cons, List.map_nil, lsemStraight_cons, e1,
    e2, e3, e4, e5, lsemStraight_nil], rfl, fun x hx => ?_⟩
  simp only [s5, s4, s3, s2, s1, Lstate.nextPc, Lstate.lvm_setReg, evalOperand, if_neg hx]
  by_cases hxR : x = reloadScratch
  · subst hxR; simp [hdR.symm]
  · simp [hxR]

/-- **One instruction against its legalisation, from one state.** When the source
    instruction steps, its legalisation runs to a state with the same memory and the
    same value at every kept name. -/
theorem legalizeInstr_lsem_local (ok : Bool) (i : Linstr)
    (hav : ok = true → instrAvoids i.li_i = true) (s t : Lstate w)
    (h : lsemStep i.li_i s = some t) :
    ∃ t', lsemStraight ((legalizeInstr ok i).map Linstr.li_i) s = some t' ∧
      t.lmem = t'.lmem ∧ ∀ x, Kept ok x → t.lvm x = t'.lvm x := by
  have refl : ∃ t', lsemStraight ([i].map Linstr.li_i) s = some t' ∧
      t.lmem = t'.lmem ∧ ∀ x, Kept ok x → t.lvm x = t'.lvm x :=
    ⟨t, by simp [h], rfl, fun _ _ => rfl⟩
  unfold legalizeInstr
  split
  · rename_i d opn a b hi
    rw [hi] at h
    split
    · rename_i hnt
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hnt
      obtain ⟨hnt, had⟩ := hnt
      have hne := needsTie_ne hnt
      obtain ⟨v, hv, rfl⟩ := step_reg_inv hne h
      simp only [List.map_cons, List.map_nil] at hv
      split
      · exact refl
      · rename_i m hm
        have hmne := movFor_ne hm
        split
        · rename_i hc
          rw [applyOpn_cmp_none hm hc] at hv
          cases hv
        · split
          · exact refl
          · rename_i hri
            split
            · -- `mov d, a; op d, [d, b]`
              rename_i hb
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
                decide_eq_false_iff_not] at hb
              have e1 : lsemStep (.Lopn [.reg d] m [a]) s
                  = some ((s.setReg d (evalOperand s a)).nextPc) :=
                step_reg hmne (by simpa using applyOpn_movFor hm (evalOperand s a))
              have e2 : lsemStep (.Lopn [.reg d] opn [.reg d, b])
                  ((s.setReg d (evalOperand s a)).nextPc)
                  = some ((((s.setReg d (evalOperand s a)).nextPc).setReg d v).nextPc) := by
                refine step_reg hne ?_
                simp only [List.map_cons, List.map_nil, evalOperand_setReg_nextPc hb.1]
                simpa [evalOperand, Lstate.setReg, Lstate.nextPc] using hv
              refine ⟨(((s.setReg d (evalOperand s a)).nextPc).setReg d v).nextPc,
                by simp only [List.map_cons, List.map_nil, lsemStraight_cons, e1, e2,
                  lsemStraight_nil], rfl, fun x _ => ?_⟩
              simp only [Lstate.nextPc, Lstate.lvm_setReg]
              split <;> rfl
            · split
              · -- `op d, [d, a]`
                rename_i hcm
                simp only [Bool.and_eq_true, beq_iff_eq] at hcm
                obtain ⟨⟨hcm, rfl⟩, -⟩ := hcm
                have e1 : lsemStep (.Lopn [.reg d] opn [.reg d, a]) s
                    = some ((s.setReg d v).nextPc) := by
                  refine step_reg hne ?_
                  simp only [List.map_cons, List.map_nil]
                  rw [applyOpn_comm hm hcm]
                  exact hv
                exact ⟨_, by simp only [List.map_cons, List.map_nil, lsemStraight_cons, e1,
                  lsemStraight_nil], rfl, fun _ _ => rfl⟩
              · split
                · -- through the scratch register
                  rename_i hok
                  have ha := hav hok
                  rw [hi] at ha
                  simp only [instrAvoids, List.all_cons, List.all_nil, Bool.and_true,
                    Bool.and_eq_true] at ha
                  obtain ⟨hd, ha', hb'⟩ := ha
                  have hdR : d ≠ reloadScratch := ne_of_opAvoids hd d (by simp [opNames])
                  have hdS : d ≠ scratchSave :=
                    ne_scratchSave_of_opAvoids hd d (by simp [opNames])
                  have hbR : reloadScratch ∉ opNames b := fun hm' =>
                    ne_of_opAvoids hb' _ hm' rfl
                  have hbS : scratchSave ∉ opNames b := fun hm' =>
                    ne_scratchSave_of_opAvoids hb' _ hm' rfl
                  have haR : reloadScratch ∉ opNames a := fun hm' =>
                    ne_of_opAvoids ha' _ hm' rfl
                  have haS : scratchSave ∉ opNames a := fun hm' =>
                    ne_scratchSave_of_opAvoids ha' _ hm' rfl
                  split
                  · -- commuted, through the scratch register
                    rename_i hcm
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcm
                    obtain ⟨hcm, rfl⟩ := hcm
                    obtain ⟨t', ht', hm', hv'⟩ :=
                      scratchRoute_lsem (a := .reg d) (b := a) i.li_ii hm hne hdR hdS
                      (by simpa [opNames] using hdS.symm) haR haS s
                      (by rw [applyOpn_comm hm hcm]; exact hv)
                    exact ⟨t', ht', hm', fun x hx => hv' x (hx hok)⟩
                  obtain ⟨t', ht', hm', hv'⟩ :=
                    scratchRoute_lsem i.li_ii hm hne hdR hdS haS hbR hbS s hv
                  exact ⟨t', ht', hm', fun x hx => hv' x (hx hok)⟩
                · exact refl
    · exact refl
  · exact refl

/-- **One instruction against its legalisation, from related states.** -/
theorem legalizeInstr_lsem (ok : Bool) (i : Linstr)
    (hav : ok = true → instrAvoids i.li_i = true) {s s' t : Lstate w}
    (hm : s.lmem = s'.lmem) (hv : ∀ x, Kept ok x → s.lvm x = s'.lvm x)
    (h : lsemStep i.li_i s = some t) :
    ∃ t', lsemStraight ((legalizeInstr ok i).map Linstr.li_i) s' = some t' ∧
      t.lmem = t'.lmem ∧ ∀ x, Kept ok x → t.lvm x = t'.lvm x := by
  have hr : ∀ x ∈ readNames i.li_i, s.lvm x = s'.lvm x :=
    fun x hx => hv x (readNames_kept ok i.li_i hav x hx)
  obtain ⟨hsome, hag⟩ := lsemStep_agreeOn (Kept ok) i.li_i hm hr hv
  rw [h] at hsome
  obtain ⟨t0, ht0⟩ : ∃ t0, lsemStep i.li_i s' = some t0 :=
    Option.isSome_iff_exists.1 hsome.symm
  obtain ⟨hm0, hv0⟩ := hag t t0 h ht0
  obtain ⟨t', ht', hm1, hv1⟩ := legalizeInstr_lsem_local ok i hav s' t0 ht0
  exact ⟨t', ht', hm0.trans hm1, fun x hx => (hv0 x hx).trans (hv1 x hx)⟩

/-- A body against its legalisation with the scratch route set by `ok`, from related
    states. -/
theorem legalizeList_lsem (ok : Bool) (body : Lcmd)
    (hav : ok = true → ∀ i ∈ body, instrAvoids i.li_i = true) {s s' t : Lstate w}
    (hm : s.lmem = s'.lmem) (hv : ∀ x, Kept ok x → s.lvm x = s'.lvm x)
    (h : lsemStraight (body.map Linstr.li_i) s = some t) :
    ∃ t', lsemStraight ((body.flatMap (legalizeInstr ok)).map Linstr.li_i) s' = some t' ∧
      t.lmem = t'.lmem ∧ ∀ x, Kept ok x → t.lvm x = t'.lvm x := by
  induction body generalizing s s' with
  | nil =>
      simp only [List.map_nil, lsemStraight_nil, Option.some.injEq] at h
      subst h
      exact ⟨s', by simp, hm, hv⟩
  | cons i is ih =>
      simp only [List.map_cons, lsemStraight_cons] at h
      cases hs : lsemStep i.li_i s with
      | none => rw [hs] at h; cases h
      | some s1 =>
          rw [hs] at h
          obtain ⟨s1', hs1', hm1, hv1⟩ :=
            legalizeInstr_lsem ok i (fun hok => hav hok i (by simp)) hm hv hs
          obtain ⟨t', ht', hm2, hv2⟩ :=
            ih (fun hok j hj => hav hok j (by simp [hj])) hm1 hv1 h
          refine ⟨t', ?_, hm2, hv2⟩
          rw [List.flatMap_cons, List.map_append, lsemStraight_append, hs1']
          exact ht'

/-- **Two-address legalisation preserves the straight-line semantics.** A body and
    `twoAddrBody` of it, run from one state, end with equal memory and equal values
    at every name other than the save slot `scratchSave`, and at every name when the body
    names the scratch register. -/
theorem twoAddrBody_lsemStraight (body : Lcmd) (s t : Lstate w)
    (h : lsemStraight (body.map Linstr.li_i) s = some t) :
    ∃ t', lsemStraight ((twoAddrBody body).map Linstr.li_i) s = some t' ∧
      t.lmem = t'.lmem ∧ ∀ x, Kept (bodyAvoids body) x → t.lvm x = t'.lvm x :=
  legalizeList_lsem (bodyAvoids body) body
    (fun hok i hi => by
      simp only [bodyAvoids, List.all_eq_true] at hok
      exact hok i hi)
    rfl (fun _ _ => rfl) h

/-- `twoAddrBody_lsemStraight` at every name other than the save slot `scratchSave`. -/
theorem twoAddrBody_lsemStraight_ne (body : Lcmd) (s t : Lstate w)
    (h : lsemStraight (body.map Linstr.li_i) s = some t) :
    ∃ t', lsemStraight ((twoAddrBody body).map Linstr.li_i) s = some t' ∧
      t.lmem = t'.lmem ∧ ∀ x, x ≠ scratchSave → t.lvm x = t'.lvm x := by
  obtain ⟨t', ht', hm, hv⟩ := twoAddrBody_lsemStraight body s t h
  exact ⟨t', ht', hm, fun x hx => hv x (fun _ => hx)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
