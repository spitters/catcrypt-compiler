/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Types
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# The deletion of dead flag-only compares

A flag-only compare `CMP:64 [c] [c, x]`, over a register `c` and a register or immediate `x`,
writes the five arithmetic flags and no register or memory cell. When the next instruction is
again such a compare, the first one has no observable effect. `dropDeadFlagOpsBody` deletes
every flag-only compare that is directly followed by another one; it deletes no label, jump or
other instruction. The owned back end `LprogOptPipeline.ownedLprog` applies it as its last
stage.

## Main definitions

* `flagSrcJ`, `flagOnlyJ`: the machine image of a flag-only instruction (`cmp` or `test`).
* `isFlagCmp`, `isDeadFlagPair`: the recogniser of a flag-only compare and of a deleted pair.
* `dropDeadFlagOpsBody`, `dropDeadFlagOpsFundef`, `dropDeadFlagOpsLprog`: the pass.
* `dropDeadFlagMarks`: the body with each instruction marked by whether the pass deletes it.

## Main results

* `dropDeadFlagOpsBody_sublist`: the output is a sublist of the input.
* `isFlagCmp_flagOnlyJ`: the machine image of a flag-only compare is a `cmp`.
* `isFlagCmp_shape`: a flag-only compare is `Lopn [.reg d] "CMP:64" [.reg d, b]` with a
  register or immediate `b`.
* `dropDeadFlagOpsBody_append_ret`: the pass keeps a trailing `Lret`.
* `dropDeadFlagMarks_fst`, `dropDeadFlagMarks_kept`, `dropDeadFlagMarks_deleted`: the marks
  list the body, the unmarked instructions are the output, and every marked instruction is a
  flag-only compare.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLoopPasses

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The recogniser -/

/-- The machine operand of a register or immediate `Lprog` source; `none` for an
    array operand. -/
def flagSrcJ : LOperand → Option JOperand
  | .reg r => some (.reg r)
  | .imm v => some (.imm v)
  | _ => none

/-- The machine image of a flag-only instruction: `Lopn [c] CMP:64 [c, x]` is
    `cmp c x` and `Lopn [c] TEST:64 [c, x]` is `test c x`, for a register or
    immediate `x`. `none` for every other instruction. -/
def flagOnlyJ (i : Linstr) : Option (JInstr 64) :=
  match i.li_i with
  | .Lopn [.reg d] opn [.reg a, b] =>
      if a = d then
        match flagSrcJ b with
        | some jb =>
            if opn = "CMP:64" then some (.cmp a jb)
            else if opn = "TEST:64" then some (.test a jb)
            else none
        | none => none
      else none
  | _ => none

/-- A flag-only compare: an instruction whose `flagOnlyJ` image is a `cmp`. -/
def isFlagCmp (i : Linstr) : Bool :=
  match flagOnlyJ i with
  | some (.cmp _ _) => true
  | _ => false

/-- A pair of adjacent instructions whose first one is dead: both are flag-only
    compares. -/
def isDeadFlagPair (i j : Linstr) : Bool :=
  isFlagCmp i && isFlagCmp j

/-- The machine image of a flag-only compare is a `cmp`. -/
theorem isFlagCmp_flagOnlyJ {i : Linstr} (h : isFlagCmp i = true) :
    ∃ a b, flagOnlyJ i = some (.cmp a b) := by
  unfold isFlagCmp at h
  split at h
  · exact ⟨_, _, by assumption⟩
  · simp at h

/-- A flag-only compare is `Lopn [.reg d] "CMP:64" [.reg d, b]` with a register or immediate
    second operand `b`. -/
theorem isFlagCmp_shape {i : Linstr} (h : isFlagCmp i = true) :
    ∃ d b, i.li_i = .Lopn [.reg d] "CMP:64" [.reg d, b] ∧ (flagSrcJ b).isSome = true := by
  unfold isFlagCmp at h
  split at h
  · rename_i a0 jb0 hcmp
    unfold flagOnlyJ at hcmp
    split at hcmp
    · rename_i d opn a b hli
      split at hcmp
      · rename_i had
        split at hcmp
        · rename_i jb hjb
          split at hcmp
          · rename_i ho
            exact ⟨d, b, by rw [hli, ho, had], by rw [hjb]; rfl⟩
          · split at hcmp <;> simp at hcmp
        · simp at hcmp
      · simp at hcmp
    · simp at hcmp
  · simp at h

/-- A flag-only compare is not `Lret`. -/
theorem isFlagCmp_ret (ii : Nat) : isFlagCmp ⟨ii, .Lret⟩ = false := rfl

/-! ## 2. The pass -/

/-- Delete every flag-only compare that is directly followed by a flag-only compare. -/
def dropDeadFlagOpsBody : Lcmd → Lcmd
  | i :: j :: rest =>
      if isDeadFlagPair i j then dropDeadFlagOpsBody (j :: rest)
      else i :: dropDeadFlagOpsBody (j :: rest)
  | l => l

/-- The pass on one function: its body rewritten by `dropDeadFlagOpsBody`. -/
def dropDeadFlagOpsFundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := dropDeadFlagOpsBody f.lfd_body }

/-- The pass on every function body of an `Lprog`. -/
def dropDeadFlagOpsLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, dropDeadFlagOpsFundef f)) }

/-- The output of the pass is a sublist of its input: the pass only deletes. -/
theorem dropDeadFlagOpsBody_sublist : ∀ b : Lcmd, (dropDeadFlagOpsBody b).Sublist b
  | [] => by simp [dropDeadFlagOpsBody]
  | [i] => by simp [dropDeadFlagOpsBody]
  | i :: j :: rest => by
      have ih := dropDeadFlagOpsBody_sublist (j :: rest)
      unfold dropDeadFlagOpsBody
      split
      · exact ih.cons i
      · exact ih.cons_cons i

/-- The pass maps a body followed by `Lret` to its output followed by the same `Lret`. -/
theorem dropDeadFlagOpsBody_append_ret (ii : Nat) :
    ∀ b : Lcmd, dropDeadFlagOpsBody (b ++ [⟨ii, .Lret⟩]) = dropDeadFlagOpsBody b ++ [⟨ii, .Lret⟩]
  | [] => by simp [dropDeadFlagOpsBody]
  | [i] => by simp [dropDeadFlagOpsBody, isDeadFlagPair, isFlagCmp_ret]
  | i :: j :: rest => by
      have ih := dropDeadFlagOpsBody_append_ret ii (j :: rest)
      simp only [List.cons_append] at ih ⊢
      unfold dropDeadFlagOpsBody
      split <;> simp [ih]

/-! ## 3. The pass as a deletion of marked instructions -/

/-- The body with each instruction marked `true` when the pass deletes it. -/
def dropDeadFlagMarks : Lcmd → List (Linstr × Bool)
  | i :: j :: rest => (i, isDeadFlagPair i j) :: dropDeadFlagMarks (j :: rest)
  | [i] => [(i, false)]
  | [] => []

/-- The marked instructions are the body. -/
theorem dropDeadFlagMarks_fst : ∀ b : Lcmd, (dropDeadFlagMarks b).map Prod.fst = b
  | [] => rfl
  | [_] => rfl
  | i :: j :: rest => by
      simp [dropDeadFlagMarks, dropDeadFlagMarks_fst (j :: rest)]

/-- The unmarked instructions are the output of the pass. -/
theorem dropDeadFlagMarks_kept : ∀ b : Lcmd,
    ((dropDeadFlagMarks b).filter (fun p => !p.2)).map Prod.fst = dropDeadFlagOpsBody b
  | [] => rfl
  | [_] => rfl
  | i :: j :: rest => by
      have ih := dropDeadFlagMarks_kept (j :: rest)
      unfold dropDeadFlagOpsBody
      split <;> simp_all [dropDeadFlagMarks]

/-- Every marked instruction is a flag-only compare. -/
theorem dropDeadFlagMarks_deleted : ∀ (b : Lcmd) (j : Linstr),
    (j, true) ∈ dropDeadFlagMarks b → isFlagCmp j = true
  | [], _, h => by simp [dropDeadFlagMarks] at h
  | [_], _, h => by simp [dropDeadFlagMarks] at h
  | i :: k :: rest, j, h => by
      simp only [dropDeadFlagMarks, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hp⟩ | h
      · have hp' := hp.symm
        simp only [isDeadFlagPair, Bool.and_eq_true] at hp'
        exact hp'.1
      · exact dropDeadFlagMarks_deleted (k :: rest) j h

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLoopPasses
