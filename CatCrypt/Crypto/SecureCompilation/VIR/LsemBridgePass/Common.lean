/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad

/-!
# Shared lemmas for pass soundness over the uniform-width run with flags

The deletion and rewriting passes of the basic-block optimiser act on single-source
register moves. This module collects the facts about `LsemBridge.lsemStepFlag` that their
soundness proofs over `LsemBridge.lsemStraightFlag` share.

## Main definitions

* `SameF` — two states with the same register map, word memory and flags; the program
  counters are unrelated.

## Main results

* `lsemStepFlag_sameF`, `lsemStraightFlag_sameF` — the step and the run with flags map
  `SameF` states to `SameF` states.
* `lsemStraightFlag_tag` — the run with flags does not read the memory tags.
* `lsemStepFlag_one_src` — on a single-destination, single-source `Lopn` the step with
  flags is `lsemStep`: it neither reads nor writes a flag.
* `lsemStepFlag_lvm_of_not_written` — the frame lemma: a step with flags changes only the
  registers `LprogStoreToLoad.writtenNames` lists.
* `fragFB_ne_mov1` — the fragment with flags contains no single-source register move.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Common

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (writtenNames lsemStep_lvm_of_not_written)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp

/-! ## 1. States equal up to the program counter -/

/-- Two states with the same register map, word memory and flags. -/
def SameF (s t : Lstate 64) : Prop :=
  s.lvm = t.lvm ∧ s.lmem = t.lmem ∧ s.cf = t.cf ∧ s.of = t.of

theorem SameF.refl (s : Lstate 64) : SameF s s := ⟨rfl, rfl, rfl, rfl⟩

theorem SameF.symm {s t : Lstate 64} (h : SameF s t) : SameF t s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem SameF.trans {s t u : Lstate 64} (h : SameF s t) (h' : SameF t u) : SameF s u :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩

/-- From `SameF` states every instruction steps under `lsemStepFlag` to `SameF` states. -/
theorem lsemStepFlag_sameF (i : LinstrRM) {s t : Lstate 64} (h : SameF s t) {s₁ : Lstate 64}
    (hst : lsemStepFlag i s = some s₁) : ∃ t₁, lsemStepFlag i t = some t₁ ∧ SameF s₁ t₁ :=
  lsemStepFlag_congr_full i h.1 h.2.1 h.2.2.1 h.2.2.2 hst

/-- From `SameF` states a body that runs to completion under `lsemStraightFlag` runs to
    completion from the other state, to a `SameF` state. -/
theorem lsemStraightFlag_sameF : ∀ (body : List LinstrRM) (s t : Lstate 64), SameF s t →
    ∀ s₂, lsemStraightFlag body s = some s₂ →
      ∃ t₂, lsemStraightFlag body t = some t₂ ∧ SameF s₂ t₂ := by
  intro body
  induction body with
  | nil =>
    intro s t h s₂ hrun
    simp only [lsemStraightFlag_nil, Option.some.injEq] at hrun
    subst hrun
    exact ⟨t, rfl, h⟩
  | cons i is ih =>
    intro s t h s₂ hrun
    rw [lsemStraightFlag_cons] at hrun
    cases hst : lsemStepFlag i s with
    | none => rw [hst] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      rw [hst, Option.bind_some] at hrun
      obtain ⟨t₁, ht₁, h₁⟩ := lsemStepFlag_sameF i h hst
      rw [lsemStraightFlag_cons, ht₁, Option.bind_some]
      exact ih s₁ t₁ h₁ s₂ hrun

/-- The run with flags does not read the memory tags. -/
theorem lsemStraightFlag_tag (tag tag' : LinstrR → MemTag) (body : List Linstr)
    (s : Lstate 64) :
    lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s
      = lsemStraightFlag (body.map fun i => (i.li_i, tag' i.li_i)) s := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, lsemStraightFlag_cons]
    rw [lsemStepFlag_tag i.li_i (tag i.li_i) (tag' i.li_i)]
    cases lsemStepFlag (i.li_i, tag' i.li_i) s with
    | none => rfl
    | some s₁ => exact ih s₁

/-! ## 2. Single-source instructions and the frame lemma -/

/-- On a single-destination, single-source `Lopn` the step with flags is `lsemStep`: none
    of the three recognizers of the flag layer accepts the instruction. -/
theorem lsemStepFlag_one_src (d opn : String) (a : LOperand) (tg : MemTag) (s : Lstate 64) :
    lsemStepFlag (.Lopn [.reg d] opn [a], tg) s = lsemStep (.Lopn [.reg d] opn [a]) s := by
  unfold lsemStepFlag
  cases lsemStep (.Lopn [.reg d] opn [a]) s with
  | some b => rfl
  | none => rfl

/-- **Frame lemma.** A step with flags changes only the registers `writtenNames` lists. -/
theorem lsemStepFlag_lvm_of_not_written {i : LinstrR} {tg : MemTag} {s s' : Lstate 64}
    (hstep : lsemStepFlag (i, tg) s = some s') {n : String} (hn : n ∉ writtenNames i) :
    s'.lvm n = s.lvm n := by
  cases hst : lsemStep i s with
  | some b =>
    rw [lsemStepFlag_of_lsemStep (i := (i, tg)) hst, Option.some.injEq] at hstep
    subst hstep
    rw [withALUFlagsL_lvm]
    exact lsemStep_lvm_of_not_written hst hn
  | none =>
    rcases lsemStepFlag_none_inv i tg hst hstep with
      ⟨d, opn, a, b, v, rfl, hv, -⟩ | ⟨lo, hi, opn, b, v, v', rfl, hv, -⟩
    · have hnd : n ≠ d := by simpa [writtenNames] using hn
      rw [hv]
      simp [Lstate.lvm_setReg, hnd]
    · have hnd : n ≠ lo ∧ n ≠ hi := by simpa [writtenNames] using hn
      rw [hv]
      simp [Lstate.lvm_setReg, hnd.1, hnd.2]

/-! ## 3. The fragment with flags has no single-source register move -/

/-- No instruction of the fragment with flags is a single-source register move. The
    reload-elimination and load-CSE passes rewrite and delete only such moves, so they are
    the identity on a body of the fragment. -/
theorem fragFB_ne_mov1 {A : String → Option Nat} {w : LinstrR} {tg : MemTag}
    (h : fragFB A (w, tg) = true) (d opn k : String) : w ≠ .Lopn [.reg d] opn [.reg k] := by
  obtain ⟨sh, hsh, -⟩ := fragFB_shape h
  rintro rfl
  cases sh with
  | plain sh => cases sh <;> simp [ShapeF.toInstr, Shape.toInstr] at hsh
  | carry op d' a b => simp [ShapeF.toInstr] at hsh
  | mov2 d' x b => simp [ShapeF.toInstr] at hsh
  | mulx lo hi b => simp [ShapeF.toInstr] at hsh

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Common
