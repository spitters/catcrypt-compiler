/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCallX86

/-!
# A body with its return as a callee, from the correspondence of the body

A correspondence `CorresIsa isa (singletonProgM fn B) SR Pre fa fuel` of a body `B` without
calls states that the run of `B` from a state related to `a` halts in a state related to
`fa a`. The function a compiler exports is `B` followed by a return. This module derives,
from the correspondence of `B`, the two statements about `B ++ [Lret]` at the instruction
set with calls `isa.withCalls`.

The correspondence relates the end state to the abstract state only. The return reads the
stack pointer and the memory cell it addresses, and is fetched at the counter after the last
instruction of `B`. These facts about the run of `B` are the exit contract `ExitFrame`: the
end state is at the counter `B.length`, and the entry and end states satisfy a frame relation
`Frame` and the return address contract `IsaCall.RetFrame`.

## Main results

* `RetAddrAt`: the stack pointer holds `v - 8` and the memory cell it addresses holds the
  word of the counter `r`; the state of a callee entered by a call from the counter `r - 1`
  with the stack pointer at `v`.
* `ExitFrame`: the exit contract of the run of a body.
* `steps_snoc_ret_of_corresIsa`: from a state related by `SR` that holds a return address
  `r`, the body followed by its return makes a segment that ends at the counter `r`, with the
  stack pointer holding `v`, in the return state of a state related to `fa a`.
* `procSpec_snoc_ret_of_corresIsa`: the procedure specification `IsaCall.ProcSpec` of the
  body followed by its return, at every label, with the return at the counter `B.length`.
* `x86_steps_snoc_ret_of_corresIsa`, `x86_procSpec_snoc_ret_of_corresIsa`: the two
  statements at `x86Isa`, where the step agreement holds for every body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCall

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel LinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

variable {A : Type}

/-- **A return address on the stack.** The stack pointer register `sp` of `m` holds
    `v - 8`, and the memory cell of `sp` at `v - 8` holds the word of the counter `r`. -/
def RetAddrAt (sp : String) (v : BitVec 64) (r : Nat) (m : LstateMF) : Prop :=
  m.prog.base.reg.getW sp 64 = some (v - 8) ∧
    m.prog.base.lmem sp (v - 8).toInt = BitVec.ofNat 64 r

/-- The state after a call step holds the return address of the call. -/
theorem retAddrAt_callEntry (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) :
    RetAddrAt sp v (m.prog.base.lpc + 1) (callEntry sp v q m) :=
  ⟨callEntry_getW_sp sp v q m, callEntry_lmem_sp sp v q m⟩

/-- **The exit contract of the run of a body.** Every run of `B` at fuel `fuel` from a
    state related by `SR` to an abstract state satisfying `Pre` halts at the counter
    `B.length`, and its entry and end states satisfy `Frame` and the return address contract
    `RetFrame` at the stack pointer of `isa`. -/
def ExitFrame (isa : Isa) (fn : String) (B : List LinstrRM) (SR : LstateMF → A → Prop)
    (Pre : A → Prop) (Frame : LstateMF → LstateMF → Prop) (fuel : Nat) : Prop :=
  ∀ m a m', SR m a → Pre a → isa.lsemFuelMemF (singletonProgM fn B) fuel m = some m' →
    atPc (singletonProgM fn B) B.length m' ∧ Frame m m' ∧ RetFrame isa.sp m m'

/-- **The body followed by its return, from the correspondence of the body.** Let `B`
    contain no call and no return, let the step of `isa` on every instruction of `B` be the
    same on `B ++ [Lret]` and on `B`, let `B` correspond to `fa` at fuel `fuel`, and let its
    run satisfy the exit contract `ExitFrame`. From a state `m` related by `SR` to `a` under
    `Pre` that holds the return address `r` below `2 ^ 64` under the stack pointer value
    `v`, the instruction set with calls makes on `B ++ [Lret]` a segment of `n + 1` steps
    with `n ≤ fuel` to the state `retState isa.sp v r m'`, which is at the counter `r` with
    the stack pointer holding `v`; the state `m'` is related to `fa a` and framed against
    `m`. -/
theorem steps_snoc_ret_of_corresIsa (isa : Isa) {fn : String} {B : List LinstrRM}
    (tag : MemTag) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (hstep : ∀ i ∈ B, ∀ s, isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      isa.step (singletonProgM fn B) i s)
    (h : CorresIsa isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame isa fn B SR Pre Frame fuel)
    {m : LstateMF} {a : A} {v : BitVec 64} {r : Nat} (hSR : SR m a) (hPre : Pre a)
    (hra : RetAddrAt isa.sp v r m) (hr : r < 2 ^ 64) :
    ∃ n m', n ≤ fuel ∧
      Steps isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) (n + 1) m
        (retState isa.sp v r m') ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) r (retState isa.sp v r m') ∧
      SR m' (fa a) ∧ Frame m m' := by
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hPre
  obtain ⟨hend, hF, hRF⟩ := hexit m a m' hSR hPre hrun
  obtain ⟨hsp', hmem'⟩ := hRF (v - 8) hra.1
  obtain ⟨n, hn, hsteps, hat⟩ :=
    steps_snoc_ret isa (tag := tag) hB hstep hrun hend hsp' (hmem'.trans hra.2) hr
  exact ⟨n, m', hn, hsteps, hat, hSR', hF⟩

/-- **The procedure specification of a body followed by its return.** Let `B` contain no
    call and no return, let the step of `isa` on every instruction of `B` be the same on
    `B ++ [Lret]` and on `B`, let `B` correspond to `fa` at fuel `fuel`, and let its run
    satisfy the exit contract `ExitFrame`. For every label `l`, the program `B ++ [Lret]`
    satisfies at `isa.withCalls` the specification of a procedure at `l` that returns at the
    counter `B.length`, with the relation, the precondition, the abstraction and the frame
    of the body and the step bound `fuel`. The specification constrains the states at the
    label `l` that `SR` relates. -/
theorem procSpec_snoc_ret_of_corresIsa (isa : Isa) {fn : String} {B : List LinstrRM}
    (tag : MemTag) (l : LLabel) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (hstep : ∀ i ∈ B, ∀ s, isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      isa.step (singletonProgM fn B) i s)
    (h : CorresIsa isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame isa fn B SR Pre Frame fuel) :
    ProcSpec isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) l B.length SR Pre fa
      Frame fuel := by
  intro m a _ hSR hPre
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hPre
  obtain ⟨hend, hF, hRF⟩ := hexit m a m' hSR hPre hrun
  obtain ⟨n, hn, hsteps, hat⟩ := steps_snoc_ret_prefix isa (tag := tag) hB hstep hrun hend
  exact ⟨n, m', hn, hsteps, hat, hSR', hF, hRF⟩

/-- **The body followed by its return at x86**: `steps_snoc_ret_of_corresIsa` at `x86Isa`
    with the step agreement proved. -/
theorem x86_steps_snoc_ret_of_corresIsa {fn : String} {B : List LinstrRM} (tag : MemTag)
    {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame x86Isa fn B SR Pre Frame fuel)
    {m : LstateMF} {a : A} {v : BitVec 64} {r : Nat} (hSR : SR m a) (hPre : Pre a)
    (hra : RetAddrAt x86Isa.sp v r m) (hr : r < 2 ^ 64) :
    ∃ n m', n ≤ fuel ∧
      Steps x86Isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) (n + 1) m
        (retState x86Isa.sp v r m') ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) r (retState x86Isa.sp v r m') ∧
      SR m' (fa a) ∧ Frame m m' :=
  steps_snoc_ret_of_corresIsa x86Isa tag hB
    (fun i _ s => x86Isa_step_snoc_ret fn B tag i s) h hexit hSR hPre hra hr

/-- **The procedure specification of a body followed by its return at x86**:
    `procSpec_snoc_ret_of_corresIsa` at `x86Isa` with the step agreement proved. -/
theorem x86_procSpec_snoc_ret_of_corresIsa {fn : String} {B : List LinstrRM} (tag : MemTag)
    (l : LLabel) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame x86Isa fn B SR Pre Frame fuel) :
    ProcSpec x86Isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) l B.length SR Pre fa
      Frame fuel :=
  procSpec_snoc_ret_of_corresIsa x86Isa tag l hB
    (fun i _ s => x86Isa_step_snoc_ret fn B tag i s) h hexit

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
