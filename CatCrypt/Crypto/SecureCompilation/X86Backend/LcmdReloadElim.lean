/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
import CatCrypt.Crypto.SecureCompilation.X86Backend.RedundantReloadElim
import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# Redundant spill-reload elimination on the owned-RA `Lcmd`, and the optimized render

`RedundantReloadElim.dropReloads` deletes the reload of an adjacent store/reload
pair on `List (JInstr 64)`. The per-kernel emit drivers do not run on
`List (JInstr 64)`: they render a `JasminLprogExport.Lprog` to AT&T `.s` through
`LprogAsmPrinter.renderLprogAtt`, and the `Lcmd → List (JInstr 64)` gather
`OptimizedComToElf.gatherJBlock` returns `none` on every body carrying a spill
slot, a frame, or control flow. This module carries the deletion to the `Lcmd`
the printer consumes and adds the optimized render entry point.

## The deletion

At the `Lcmd` level a spill store and its reload are two `MOV`s over a
memory-class operand name (`k.N` spill slot, `qsave.X` ABI save slot,
`mem.<base>.<off>` frame reference):

```
Lopn [.reg "k.5"] "MOV:64" [.reg "R15"]     -- movq %r15, 16(%rsp)
Lopn [.reg "R15"] "MOV:64" [.reg "k.5"]     -- movq 16(%rsp), %r15   (deleted)
```

`dropReloadsLcmd` is one right-to-left sweep deleting the reload of each such
adjacent pair (`consDropL`), mirroring `RedundantReloadElim.dropReloads`. Both
instructions must carry the same 64-bit move mnemonic (`MOV:64` or `MOVQ`), the
slot operand must be a memory-class name, and the register operand must be a
name outside that class (one the printer resolves to a bare register).

## Contents

* `isRedundantReloadL` / `consDropL` / `dropReloadsLcmd` — the recognizer and the sweep.
* `reloadElimBody` — the sweep behind a frame-layout guard: it is applied only when
  the printer's frame size and width class are unchanged, so every rendered slot
  offset is fixed (`frameSize_reloadElimBody`).
* `dropReloadsLcmd_lsem` / `reloadElimBody_lsem` — the semantics tie against
  `JasminLsem.lsemStraight`: the swept body reaches a state agreeing with the
  original's on the register map and on memory. The program counter is one lower
  per deleted instruction, which is what `ArchAgree` quotients out.
* `linstrJ` / `isRedundantReloadL_jimage` — the transfer to the verified `JInstr`
  pass: a pair the `Lcmd` recognizer accepts maps to a pair
  `RedundantReloadElim.isRedundantReload` accepts, whose deletion is a `runBlock`
  identity.
* `renderLcmd_reloadElim_sublist` — the rendered text of the swept body is a
  sublist of the rendered text of the original.
* `renderLprogAttOpt` — the optimized render, `renderLprogAtt ∘ reloadElimLprog`.
  `renderLprogAtt` itself is untouched.
* `gatherRenderBody` — the `gatherJBlock` / validated-pipeline route with a total
  explicit fallback to `renderLcmd`.

## Scope of the `lsem` tie

`JasminLsem.lsemStep` models the straight-line word fragment; it returns `none`
on `Lgoto` / `Lcond` / `Lcall` / `Lret` / `Lsyscall`. `dropReloadsLcmd_lsem` holds
for every body, and carries information up to the first control-flow instruction.
Pairing is adjacency-based, so a deleted reload is always in the same
straight-line segment as its store and is never a jump target (a jump target is
preceded by an `Llabel`, not by a spill store).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLcmd renderLprogAtt frameSize bodyIsU64)

/-! ## 1. The spill-move shapes -/

/-- A memory-class operand name: a spill slot `k.N`, an ABI save slot `qsave.X`,
    or a frame reference `mem.<base>.<off>`. These are the names
    `LprogAsmPrinter.resolveOperand` renders as `off(%rsp)` rather than as a bare
    register. -/
def isSlotName (n : String) : Bool :=
  "k.".isPrefixOf n || "qsave.".isPrefixOf n || "mem.".isPrefixOf n

/-- An operand name the printer resolves to a bare register: any name outside the
    memory class. -/
def isRegName (n : String) : Bool := !isSlotName n

/-- The two 64-bit move mnemonics the owned exporter emits. Restricting to these
    keeps the deletion out of the untagged 32-bit `MOV`, which renders as a
    zero-extending `movl`. -/
def isMov64 (mn : String) : Bool := mn == "MOV:64" || mn == "MOVQ"

/-- Both 64-bit move mnemonics copy their single source word under
    `JasminLsem.applyOpn`. -/
theorem applyOpn_mov64 {w : Nat} {mn : String} (h : isMov64 mn = true) (a : BitVec w) :
    applyOpn (w := w) (stripWidthTag mn) [a] = some a := by
  simp only [isMov64, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · rw [show stripWidthTag "MOV:64" = "MOV" from by decide +kernel]; rfl
  · rw [stripWidthTag_MOVQ]; rfl

/-- `(slot, reg, mnemonic)` of a register-to-slot spill store
    `Lopn [.reg slot] mn [.reg r]`. -/
def spillStoreKey (i : Linstr) : Option (String × String × String) :=
  match i.li_i with
  | .Lopn [.reg slot] mn [.reg r] =>
      if isSlotName slot && isRegName r && isMov64 mn then some (slot, r, mn) else none
  | _ => none

/-- `(slot, reg, mnemonic)` of a slot-to-register reload
    `Lopn [.reg r] mn [.reg slot]`. -/
def spillLoadKey (i : Linstr) : Option (String × String × String) :=
  match i.li_i with
  | .Lopn [.reg r] mn [.reg slot] =>
      if isSlotName slot && isRegName r && isMov64 mn then some (slot, r, mn) else none
  | _ => none

theorem spillStoreKey_eq {i : Linstr} {slot r mn : String}
    (h : spillStoreKey i = some (slot, r, mn)) :
    i.li_i = .Lopn [.reg slot] mn [.reg r] ∧ isSlotName slot = true ∧
      isRegName r = true ∧ isMov64 mn = true := by
  unfold spillStoreKey at h
  split at h
  · rename_i slot' mn' r' hi
    split at h
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hcond
      exact ⟨hi, hcond.1.1, hcond.1.2, hcond.2⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem spillLoadKey_eq {i : Linstr} {slot r mn : String}
    (h : spillLoadKey i = some (slot, r, mn)) :
    i.li_i = .Lopn [.reg r] mn [.reg slot] ∧ isSlotName slot = true ∧
      isRegName r = true ∧ isMov64 mn = true := by
  unfold spillLoadKey at h
  split at h
  · rename_i r' mn' slot' hi
    split at h
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hcond
      exact ⟨hi, hcond.1.1, hcond.1.2, hcond.2⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem not_isSlotName_of_isRegName {r : String} (h : isRegName r = true) :
    isSlotName r = false := by
  simpa [isRegName] using h

/-- A slot name and a register name are distinct. -/
theorem slot_ne_reg {slot r : String} (hs : isSlotName slot = true)
    (hr : isRegName r = true) : r ≠ slot := by
  intro hrs
  rw [hrs] at hr
  rw [not_isSlotName_of_isRegName hr] at hs
  exact Bool.noConfusion hs

/-! ## 2. The recognizer and the sweep -/

/-- `isRedundantReloadL i j`: `i` spills register `r` into slot `slot`, and `j`
    reloads that same slot back into that same `r` under the same 64-bit move
    mnemonic. -/
def isRedundantReloadL (i j : Linstr) : Bool :=
  match spillStoreKey i, spillLoadKey j with
  | some (slot, r, mn), some (slot', r', mn') => slot == slot' && r == r' && mn == mn'
  | _, _ => false

/-- The keys of a recognized pair coincide. -/
theorem keys_of_isRedundantReloadL {i j : Linstr} (h : isRedundantReloadL i j = true) :
    ∃ slot r mn, spillStoreKey i = some (slot, r, mn) ∧
      spillLoadKey j = some (slot, r, mn) := by
  unfold isRedundantReloadL at h
  split at h
  · rename_i slot r mn slot' r' mn' hsi hlj
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hslot, hr⟩, hmn⟩ := h
    subst hslot; subst hr; subst hmn
    exact ⟨slot, r, mn, hsi, hlj⟩
  · exact absurd h (by simp)

/-- The instruction shape of a recognized pair. -/
theorem eq_of_isRedundantReloadL {i j : Linstr} (h : isRedundantReloadL i j = true) :
    ∃ slot r mn, i.li_i = .Lopn [.reg slot] mn [.reg r] ∧
      j.li_i = .Lopn [.reg r] mn [.reg slot] ∧
      isSlotName slot = true ∧ isRegName r = true ∧ isMov64 mn = true := by
  obtain ⟨slot, r, mn, hsi, hlj⟩ := keys_of_isRedundantReloadL h
  obtain ⟨hi, hs, hrp, hm⟩ := spillStoreKey_eq hsi
  obtain ⟨hj, _, _, _⟩ := spillLoadKey_eq hlj
  exact ⟨slot, r, mn, hi, hj, hs, hrp, hm⟩

/-- Prepend `i` to an already-swept tail, deleting the tail's head when it is the
    redundant reload of `i`. -/
def consDropL (i : Linstr) : Lcmd → Lcmd
  | [] => [i]
  | j :: rest => if isRedundantReloadL i j then i :: rest else i :: j :: rest

/-- **Redundant spill-reload elimination on an owned-RA body.** A right-to-left
    sweep deleting the reload of every adjacent spill store/reload pair. -/
def dropReloadsLcmd : Lcmd → Lcmd
  | [] => []
  | i :: rest => consDropL i (dropReloadsLcmd rest)

@[simp] theorem dropReloadsLcmd_nil : dropReloadsLcmd [] = [] := rfl

@[simp] theorem dropReloadsLcmd_cons (i : Linstr) (rest : Lcmd) :
    dropReloadsLcmd (i :: rest) = consDropL i (dropReloadsLcmd rest) := rfl

/-! ## 3. The sweep only deletes -/

theorem consDropL_sublist (i : Linstr) (k : Lcmd) : (consDropL i k).Sublist (i :: k) := by
  cases k with
  | nil => exact List.Sublist.refl _
  | cons j rest =>
    rw [consDropL]
    split
    · exact ((List.Sublist.refl rest).cons j).cons_cons i
    · exact List.Sublist.refl _

theorem dropReloadsLcmd_sublist (b : Lcmd) : (dropReloadsLcmd b).Sublist b := by
  induction b with
  | nil => exact List.nil_sublist _
  | cons i rest ih =>
    rw [dropReloadsLcmd_cons]
    exact (consDropL_sublist i (dropReloadsLcmd rest)).trans (ih.cons_cons i)

/-! ## 4. Semantics: the deletion preserves the register map and memory

`JasminLsem.lsemStep` writes the destination register and bumps the program
counter, so deleting an instruction leaves every later state one program counter
lower. `ArchAgree` is the state relation the deletion preserves: equality of the
register map `lvm` and of memory `lmem`. -/

export CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
  (ArchAgree ArchAgree.refl ArchAgree.symm ArchAgree.trans
   ArchAgreeOpt ArchAgreeOpt.refl ArchAgreeOpt.trans
   archAgreeOpt_none_none archAgreeOpt_some_some
   archAgreeOpt_none_some archAgreeOpt_some_none
   lsemStep_archAgree)

/-! `lsemStraight` peeling, as equations rather than a `match` — the form the
deletion proofs rewrite with. -/

theorem lsemStraight_cons_some {w : Nat} (i : LinstrR) (is : List LinstrR)
    {s s' : Lstate w} (h : lsemStep i s = some s') :
    lsemStraight (i :: is) s = lsemStraight is s' := by
  rw [lsemStraight_cons, h]

theorem lsemStraight_cons_none {w : Nat} (i : LinstrR) (is : List LinstrR)
    {s : Lstate w} (h : lsemStep i s = none) : lsemStraight (i :: is) s = none := by
  rw [lsemStraight_cons, h]

/-- Writing a register with the value it already holds is the identity on the
    register map. -/
theorem lvm_setReg_self {w : Nat} (s : Lstate w) (r : String) :
    (s.setReg r (s.lvm r)).lvm = s.lvm := by
  funext r'
  by_cases h : r' = r <;> simp [Lstate.setReg, h]

/-- `lsemStraight` maps `ArchAgree` start states to `ArchAgree` results. -/
theorem lsemStraight_archAgree {w : Nat} (b : List LinstrR) {s t : Lstate w}
    (h : ArchAgree s t) : ArchAgreeOpt (lsemStraight b s) (lsemStraight b t) := by
  induction b generalizing s t with
  | nil => exact h
  | cons i rest ih =>
    have hstep := lsemStep_archAgree (w := w) i h
    cases hs : lsemStep i s with
    | none =>
      rw [hs] at hstep
      cases ht : lsemStep i t with
      | none =>
        rw [lsemStraight_cons_none i rest hs, lsemStraight_cons_none i rest ht]
        trivial
      | some t' => rw [ht] at hstep; exact (hstep : False).elim
    | some s' =>
      rw [hs] at hstep
      cases ht : lsemStep i t with
      | none => rw [ht] at hstep; exact (hstep : False).elim
      | some t' =>
        rw [ht] at hstep
        rw [lsemStraight_cons_some i rest hs, lsemStraight_cons_some i rest ht]
        exact ih hstep

/-- **The store step.** A spill store always steps, writing the register's word
    into the slot cell. -/
theorem lsemStep_spill_store {w : Nat} {slot r mn : String} (hm : isMov64 mn = true)
    (s : Lstate w) :
    lsemStep (.Lopn [.reg slot] mn [.reg r]) s = some ((s.setReg slot (s.lvm r)).nextPc) := by
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, applyOpn_mov64 hm]

/-- **The reload of a just-spilled register is a no-op on the architectural
    state.** After `MOV slot, r` the slot holds `r`'s word, so `MOV r, slot`
    rewrites `r` with the value it already holds. -/
theorem lsemStep_reload_archAgree {w : Nat} {slot r mn : String}
    (hs : isSlotName slot = true) (hr : isRegName r = true) (hm : isMov64 mn = true)
    {s s₁ : Lstate w} (h₁ : lsemStep (.Lopn [.reg slot] mn [.reg r]) s = some s₁) :
    ∃ s₂, lsemStep (.Lopn [.reg r] mn [.reg slot]) s₁ = some s₂ ∧ ArchAgree s₂ s₁ := by
  rw [lsemStep_spill_store hm] at h₁
  have hs₁ : s₁ = (s.setReg slot (s.lvm r)).nextPc := (Option.some.inj h₁).symm
  have hslot : s₁.lvm slot = s₁.lvm r := by
    subst hs₁
    simp [Lstate.nextPc, Lstate.setReg, slot_ne_reg hs hr]
  refine ⟨(s₁.setReg r (s₁.lvm slot)).nextPc, ?_, ?_, ?_⟩
  · simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, applyOpn_mov64 hm]
  · rw [hslot]
    simp only [Lstate.nextPc, lvm_setReg_self]
  · rfl

/-- The deletion inside `consDropL` preserves the architectural state. -/
theorem consDropL_lsem {w : Nat} (i : Linstr) (k : Lcmd) (s : Lstate w) :
    ArchAgreeOpt (lsemStraight ((consDropL i k).map Linstr.li_i) s)
      (lsemStraight ((i :: k).map Linstr.li_i) s) := by
  cases k with
  | nil => exact ArchAgreeOpt.refl _
  | cons j rest =>
    rw [consDropL]
    split
    · rename_i h
      obtain ⟨slot, r, mn, hi, hj, hslot, hreg, hmn⟩ := eq_of_isRedundantReloadL h
      simp only [List.map_cons, hi, hj]
      cases h₁ : lsemStep (w := w) (LinstrR.Lopn [.reg slot] mn [.reg r]) s with
      | none =>
        rw [lsemStraight_cons_none _ _ h₁, lsemStraight_cons_none _ _ h₁]
        trivial
      | some s₁ =>
        obtain ⟨s₂, h₂, hagree⟩ := lsemStep_reload_archAgree hslot hreg hmn h₁
        rw [lsemStraight_cons_some _ _ h₁, lsemStraight_cons_some _ _ h₁,
          lsemStraight_cons_some _ _ h₂]
        exact lsemStraight_archAgree _ hagree.symm
    · exact ArchAgreeOpt.refl _

/-- **The sweep preserves the register map and memory.** On every body and every
    start state, the swept body's `lsemStraight` result agrees with the
    original's on `lvm` and `lmem`. -/
theorem dropReloadsLcmd_lsem {w : Nat} (b : Lcmd) (s : Lstate w) :
    ArchAgreeOpt (lsemStraight ((dropReloadsLcmd b).map Linstr.li_i) s)
      (lsemStraight (b.map Linstr.li_i) s) := by
  induction b generalizing s with
  | nil => exact ArchAgreeOpt.refl _
  | cons i rest ih =>
    rw [dropReloadsLcmd_cons]
    refine ArchAgreeOpt.trans (consDropL_lsem i (dropReloadsLcmd rest) s) ?_
    simp only [List.map_cons]
    cases h₁ : lsemStep (w := w) i.li_i s with
    | none =>
      rw [lsemStraight_cons_none _ _ h₁, lsemStraight_cons_none _ _ h₁]
      trivial
    | some s₁ =>
      rw [lsemStraight_cons_some _ _ h₁, lsemStraight_cons_some _ _ h₁]
      exact ih s₁

/-! ## 5. Transfer to the verified `JInstr` pass

The `Lcmd` recognizer accepts exactly the pairs whose `JInstr` image the verified
recognizer `RedundantReloadElim.isRedundantReload` accepts. The image keys the
memory cell by the slot NAME (`storeMem slot 0` / `loadMem _ slot 0`): the printer
resolves a memory-class operand from its name alone within a body, so equal names
are the same cell. -/

/-- The `JInstr` image of a spill move: a store into the slot cell, or a reload
    out of it. `none` for every other instruction. -/
def linstrJ (i : Linstr) : Option (JInstr 64) :=
  match spillStoreKey i with
  | some (slot, r, _) => some (.storeMem slot 0 (.reg r))
  | none =>
    match spillLoadKey i with
    | some (slot, r, _) => some (.loadMem r slot 0)
    | none => none

/-- The two keys are mutually exclusive: a store writes a slot name, a reload
    writes a physical GP, and no physical GP is a slot name. -/
theorem spillLoadKey_eq_none_of_store {i : Linstr} {slot r mn : String}
    (h : spillStoreKey i = some (slot, r, mn)) : spillLoadKey i = none := by
  obtain ⟨hi, _, hr, _⟩ := spillStoreKey_eq h
  unfold spillLoadKey
  rw [hi]
  simp [not_isSlotName_of_isRegName hr]

theorem spillStoreKey_eq_none_of_load {i : Linstr} {slot r mn : String}
    (h : spillLoadKey i = some (slot, r, mn)) : spillStoreKey i = none := by
  obtain ⟨hi, _, hr, _⟩ := spillLoadKey_eq h
  unfold spillStoreKey
  rw [hi]
  simp [not_isSlotName_of_isRegName hr]

/-- **The transfer.** A pair the `Lcmd` recognizer accepts has `JInstr` images
    that the verified `RedundantReloadElim` recognizer accepts, and deleting the
    reload of that image pair is a `runBlock` identity. -/
theorem isRedundantReloadL_jimage {i j : Linstr} (h : isRedundantReloadL i j = true) :
    ∃ slot r,
      linstrJ i = some (.storeMem slot 0 (.reg r)) ∧
      linstrJ j = some (.loadMem r slot 0) ∧
      RedundantReloadElim.isRedundantReload [slot]
        (.storeMem slot 0 (.reg r)) (.loadMem r slot 0) = true ∧
      RedundantReloadElim.dropReloads [slot]
        [.storeMem slot 0 (.reg r), .loadMem r slot 0] = [.storeMem slot 0 (.reg r)] ∧
      ∀ s : JState 64,
        runBlock s [JInstr.storeMem slot 0 (.reg r), JInstr.loadMem r slot 0]
          = runBlock s [JInstr.storeMem slot 0 (.reg r)] := by
  obtain ⟨slot, r, mn, hsi, hlj⟩ := keys_of_isRedundantReloadL h
  have hrec : RedundantReloadElim.isRedundantReload [slot]
      (.storeMem slot 0 (.reg r)) (.loadMem r slot 0) = true := by
    simp [RedundantReloadElim.isRedundantReload, RedundantReloadElim.storeKey,
      RedundantReloadElim.loadKey]
  refine ⟨slot, r, ?_, ?_, hrec, ?_, ?_⟩
  · simp [linstrJ, hsi]
  · simp [linstrJ, spillStoreKey_eq_none_of_load hlj, hlj]
  · rw [RedundantReloadElim.dropReloads, RedundantReloadElim.dropReloads,
      RedundantReloadElim.dropReloads, RedundantReloadElim.consDrop,
      RedundantReloadElim.consDrop, if_pos hrec]
  · intro s
    rw [runBlock_cons, runBlock_cons, runBlock_cons,
      RedundantReloadElim.evalInstr_loadMem_storeMem]

/-! ## 6. The frame-layout guard

`LprogAsmPrinter.renderLfundef` sizes the frame from the body (`frameSize`) and
picks the spill stride from its width class (`bodyIsU64`). `reloadElimBody`
applies the sweep only when both are unchanged, so every rendered slot offset in
the optimized body is the offset it had in the original. -/

/-- The sweep behind the frame-layout guard: `dropReloadsLcmd` when it leaves the
    printer's frame size and width class fixed, the identity otherwise. -/
def reloadElimBody (b : Lcmd) : Lcmd :=
  if frameSize (dropReloadsLcmd b) == frameSize b
      && bodyIsU64 (dropReloadsLcmd b) == bodyIsU64 b then dropReloadsLcmd b else b

/-- **The optimized body keeps the frame layout.** -/
theorem frameSize_reloadElimBody (b : Lcmd) : frameSize (reloadElimBody b) = frameSize b := by
  unfold reloadElimBody
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1
  · rfl

/-- **The optimized body keeps the spill-stride width class.** -/
theorem bodyIsU64_reloadElimBody (b : Lcmd) : bodyIsU64 (reloadElimBody b) = bodyIsU64 b := by
  unfold reloadElimBody
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.2
  · rfl

theorem reloadElimBody_sublist (b : Lcmd) : (reloadElimBody b).Sublist b := by
  unfold reloadElimBody
  split
  · exact dropReloadsLcmd_sublist b
  · exact List.Sublist.refl b

/-- **The guarded sweep preserves the register map and memory.** -/
theorem reloadElimBody_lsem {w : Nat} (b : Lcmd) (s : Lstate w) :
    ArchAgreeOpt (lsemStraight ((reloadElimBody b).map Linstr.li_i) s)
      (lsemStraight (b.map Linstr.li_i) s) := by
  unfold reloadElimBody
  split
  · exact dropReloadsLcmd_lsem b s
  · exact ArchAgreeOpt.refl _

/-! ## 7. The optimized render -/

/-- Sublists are preserved by `flatMap`. -/
theorem sublist_flatMap {α β : Type} {a b : List α} (h : a.Sublist b) (f : α → List β) :
    (a.flatMap f).Sublist (b.flatMap f) := by
  induction h with
  | slnil => exact List.Sublist.refl _
  | cons x _ ih =>
      simp only [List.flatMap_cons]
      exact ih.trans (List.sublist_append_right _ _)
  | cons_cons x _ ih =>
      simp only [List.flatMap_cons]
      exact ih.append_left _

/-- **The optimized render deletes lines and adds none.** At the frame the
    optimized body itself determines (`frameSize_reloadElimBody`: the original's),
    the rendered text of the swept body is a sublist of the rendered text of the
    original. -/
theorem renderLcmd_reloadElim_sublist (frame spillW : Nat) (b : Lcmd) (lblPfx : String) :
    (renderLcmd frame spillW (reloadElimBody b) lblPfx).Sublist
      (renderLcmd frame spillW b lblPfx) :=
  sublist_flatMap (reloadElimBody_sublist b) _

/-- The pass on one `Lfundef` (body only; ABI metadata untouched). -/
def reloadElimFundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := reloadElimBody f.lfd_body }

/-- The pass on a whole `Lprog` (every function body). -/
def reloadElimLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, reloadElimFundef f) }

/-- **The optimized AT&T render.** `renderLprogAtt` after the guarded sweep. The
    unoptimized entry point `renderLprogAtt` is unchanged; an emitter opts in by
    calling this instead. -/
def renderLprogAttOpt (p : Lprog) : String := renderLprogAtt (reloadElimLprog p)

/-- The optimized render keeps the function list and its symbol names. -/
theorem reloadElimLprog_names (p : Lprog) :
    (reloadElimLprog p).lp_funcs.map Prod.fst = p.lp_funcs.map Prod.fst := by
  simp [reloadElimLprog, List.map_map, Function.comp_def]

/-! ## 8. The `gatherJBlock` route, with a total fallback

`OptimizedComToElf.optimizedJBlock` runs the validated `JInstr` pipeline
(`X86OptPipelineComposed.composeValidated`, whose soundness is
`OptimizedComToElf.optimizedJBlock_sound`) on the gathered body, and is `none`
whenever any instruction is outside `LoweringExtended.lowerLinstrExtL`'s
fragment. `gatherRenderBody` renders through that route when it succeeds and
through `renderLcmd` otherwise, so no body is dropped.

The `JInstr` printer resolves register names through a `GpAlloc`; the allocation
is derived from the gathered block by `AsmPrinter.allocGp`. -/

/-- AT&T lines for a body: the gathered-and-optimized `JInstr` render when the
    body is inside the `lowerLinstrExtL` fragment, the `Lcmd` render otherwise. -/
def gatherRenderBody (frame spillW : Nat) (body : Lcmd) (lblPfx : String := "") : List String :=
  match OptimizedComToElf.optimizedJBlock body with
  | some opt =>
      AsmPrinter.renderBlockBody
        (AsmPrinter.allocGp ([] : AsmPrinter.GpAlloc) opt) opt
  | none => renderLcmd frame spillW body lblPfx

/-- **The fallback is exactly the unoptimized render.** -/
theorem gatherRenderBody_fallback (frame spillW : Nat) (body : Lcmd) (lblPfx : String)
    (h : OptimizedComToElf.optimizedJBlock body = none) :
    gatherRenderBody frame spillW body lblPfx = renderLcmd frame spillW body lblPfx := by
  unfold gatherRenderBody
  rw [h]

/-- **The gathered route runs the validated pipeline.** When the gather succeeds,
    the block `gatherRenderBody` renders is `runBlock`-equal to the gathered
    block on every state — `OptimizedComToElf.optimizedJBlock_sound`. -/
theorem gatherRenderBody_sound (body : Lcmd) (g opt : List (JInstr 64))
    (hg : OptimizedComToElf.gatherJBlock body = some g)
    (ho : OptimizedComToElf.optimizedJBlock body = some opt) :
    ∀ s : JState 64, runBlock s opt = runBlock s g :=
  OptimizedComToElf.optimizedJBlock_sound body g opt hg ho

/-! ## 9. Firing / non-firing demos (`#guard`, evaluated at elaboration)

The recognizer goes through `String.isPrefixOf`, which does not reduce in the
kernel, so these are `#guard`s (elaborator-evaluated, no axiom cost) rather than
`by decide` — the `LcmdCopyPropagate` precedent. Each fails the build on a
regression. `Linstr`'s `DecidableEq` instance comes from `LcmdCopyPropagate`. -/

/-- A spill store followed by its reload. -/
def demoPair : Lcmd :=
  [ ⟨0, .Lopn [.reg "k.5"] "MOV:64" [.reg "R15"]⟩,
    ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.5"]⟩ ]

-- The recognizer fires and the sweep deletes the reload.
#guard dropReloadsLcmd demoPair = [(⟨0, .Lopn [.reg "k.5"] "MOV:64" [.reg "R15"]⟩ : Linstr)]

/-- A store whose reload targets a different slot. -/
def demoNoPair : Lcmd :=
  [ ⟨0, .Lopn [.reg "k.5"] "MOV:64" [.reg "R15"]⟩,
    ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.6"]⟩ ]

-- A different slot is not a redundant reload.
#guard dropReloadsLcmd demoNoPair = demoNoPair

/-- A 32-bit `MOV` pair, outside the recognizer (the rendered `movl` zero-extends). -/
def demoNarrow : Lcmd :=
  [ ⟨0, .Lopn [.reg "k.5"] "MOV" [.reg "R15"]⟩,
    ⟨0, .Lopn [.reg "R15"] "MOV" [.reg "k.5"]⟩ ]

-- The narrow move is left alone.
#guard dropReloadsLcmd demoNarrow = demoNarrow

/-- A reload separated from its store by another instruction. -/
def demoNotAdjacent : Lcmd :=
  [ ⟨0, .Lopn [.reg "k.5"] "MOV:64" [.reg "R15"]⟩,
    ⟨0, .Lopn [.reg "R14"] "ADD:64" [.reg "R14", .reg "R13"]⟩,
    ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.5"]⟩ ]

-- Only adjacent pairs are recognized.
#guard dropReloadsLcmd demoNotAdjacent = demoNotAdjacent

end CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
