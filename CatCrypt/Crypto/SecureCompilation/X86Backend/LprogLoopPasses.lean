/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogDeadFlag
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak

/-!
# Dead flag-only compares in `Lprog` loop bodies

The runtime-trip loop export closes a loop body with a run of flag-only compares
`CMP:64 [c] [c, x]` before the conditional back-edge; only the last of them sets
the flags the branch reads. A flag-only compare writes the five arithmetic flags and
no register or memory cell, so when the next instruction is again a flag-only
compare, the first one has no observable effect.

The pass `dropDeadFlagOpsBody` and its recogniser `isDeadFlagPair` are defined in
`LprogDeadFlag`. Their machine image is the `JasminModel` instruction `cmp`
(`flagOnlyJ`), the form the gather of `GatherFullBody.lowerFlagClassJ` gives a
two-address `CMP:64`. This module states the pass on the machine model.

## Main results

* `isDeadFlagPair_jimage`: the machine images of an accepted pair `i, j` satisfy
  `runBlock s [ji, jj] = runBlock s [jj]` on every machine state.
* `dropDeadFlagOpsBody_runBlock`: for every per-instruction image that sends a
  flag-only instruction to its `flagOnlyJ` image, the gathered block of the output
  exists when the input's does, is a sublist of it, and has the same `runBlock` on
  every machine state.
* `dropDeadFlagOpsBody_allDirect`: the gathered output block stays in the
  constant-time class `MachineConstantTime.IsDirect`.
* `flagOnly_leak_nil`: a deleted instruction emits no event under every leakage
  model `LprogLeak.LeakFn`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLoopPasses

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (IsDirect)

/-! ## 1. Machine semantics of one deletion -/

/-- The image of a flag-only instruction is a `cmp` or a `test`. -/
theorem flagOnlyJ_cases {i : Linstr} {ji : JInstr 64} (h : flagOnlyJ i = some ji) :
    ∃ a b, ji = .cmp a b ∨ ji = .test a b := by
  unfold flagOnlyJ at h
  split at h
  · split at h
    · split at h
      · split at h
        · exact ⟨_, _, Or.inl (Option.some.inj h).symm⟩
        · split at h
          · exact ⟨_, _, Or.inr (Option.some.inj h).symm⟩
          · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A `cmp` or `test` followed by a `cmp` or `test` evaluates as the second one
    alone: the first writes only the five flags, which the second overwrites
    without reading. -/
theorem evalInstr_flagOnly_flagOnly (s : JState 64) {ji jj : JInstr 64}
    (hi : ∃ a b, ji = .cmp a b ∨ ji = .test a b)
    (hj : ∃ a b, jj = .cmp a b ∨ jj = .test a b) :
    evalInstr (evalInstr s ji) jj = evalInstr s jj := by
  obtain ⟨a, b, rfl | rfl⟩ := hi <;> obtain ⟨c, d, rfl | rfl⟩ := hj <;> cases d <;> rfl

/-- **The transfer.** A pair the recogniser accepts has machine images `ji`, `jj`
    with `runBlock s [ji, jj] = runBlock s [jj]` on every machine state. -/
theorem isDeadFlagPair_jimage {i j : Linstr} (h : isDeadFlagPair i j = true) :
    ∃ ji jj, flagOnlyJ i = some ji ∧ flagOnlyJ j = some jj ∧
      ∀ s : JState 64, runBlock s [ji, jj] = runBlock s [jj] := by
  simp only [isDeadFlagPair, Bool.and_eq_true] at h
  obtain ⟨a, b, hji⟩ := isFlagCmp_flagOnlyJ h.1
  obtain ⟨c, d, hjj⟩ := isFlagCmp_flagOnlyJ h.2
  refine ⟨_, _, hji, hjj, fun s => ?_⟩
  simp only [runBlock_cons, runBlock_nil]
  exact evalInstr_flagOnly_flagOnly s (flagOnlyJ_cases hji) (flagOnlyJ_cases hjj)

/-! ## 2. The pass on a gathered block -/

/-- The block of a body under a per-instruction image: the concatenation of the
    images, `none` when an instruction has none. -/
def gatherWith (img : Linstr → Option (List (JInstr 64))) : Lcmd → Option (List (JInstr 64))
  | [] => some []
  | i :: is =>
      match img i, gatherWith img is with
      | some a, some b => some (a ++ b)
      | _, _ => none

/-- An image agrees with the recogniser when it sends every flag-only instruction
    to its one-instruction `flagOnlyJ` image. -/
def ImgAgrees (img : Linstr → Option (List (JInstr 64))) : Prop :=
  ∀ i ji, flagOnlyJ i = some ji → img i = some [ji]

/-- The gathered block of a cons is the image of its head followed by the block of
    its tail. -/
theorem gatherWith_cons_iff (img : Linstr → Option (List (JInstr 64))) (i : Linstr)
    (is : Lcmd) (blk : List (JInstr 64)) :
    gatherWith img (i :: is) = some blk ↔
      ∃ a g, img i = some a ∧ gatherWith img is = some g ∧ blk = a ++ g := by
  simp only [gatherWith]
  split <;> grind

/-- **Block-level correctness.** For an image that agrees with the recogniser, the
    gathered block of the output exists whenever the input's does, is a sublist of
    it, and runs to the same machine state from every start state. -/
theorem dropDeadFlagOpsBody_runBlock (img : Linstr → Option (List (JInstr 64)))
    (himg : ImgAgrees img) :
    ∀ (b : Lcmd) (blk : List (JInstr 64)), gatherWith img b = some blk →
      ∃ blk', gatherWith img (dropDeadFlagOpsBody b) = some blk' ∧ blk'.Sublist blk ∧
        ∀ s : JState 64, runBlock s blk' = runBlock s blk
  | [], blk, h => ⟨blk, by simpa [dropDeadFlagOpsBody] using h, .refl _, fun _ => rfl⟩
  | [i], blk, h => ⟨blk, by simpa [dropDeadFlagOpsBody] using h, .refl _, fun _ => rfl⟩
  | i :: j :: rest, blk, h => by
      obtain ⟨a, g, ha, hg, rfl⟩ := (gatherWith_cons_iff img i (j :: rest) blk).mp h
      obtain ⟨g', hg', hsub, hrun⟩ := dropDeadFlagOpsBody_runBlock img himg (j :: rest) g hg
      unfold dropDeadFlagOpsBody
      split
      · rename_i hp
        obtain ⟨ji, jj, hji, hjj, hrb⟩ := isDeadFlagPair_jimage hp
        obtain ⟨a2, g2, ha2, hg2, rfl⟩ := (gatherWith_cons_iff img j rest g).mp hg
        rw [himg i ji hji] at ha
        rw [himg j jj hjj] at ha2
        cases ha
        cases ha2
        refine ⟨g', hg', hsub.cons ji, fun s => ?_⟩
        grind [Optimizer.SpillingRegAlloc.runBlock_append]
      · refine ⟨a ++ g', (gatherWith_cons_iff img i _ _).mpr ⟨a, g', ha, hg', rfl⟩,
          hsub.append_left a, fun s => ?_⟩
        rw [Optimizer.SpillingRegAlloc.runBlock_append,
          Optimizer.SpillingRegAlloc.runBlock_append, hrun]

/-- **Constant-time class.** When every instruction of the input's gathered block
    is `IsDirect`, so is every instruction of the output's. -/
theorem dropDeadFlagOpsBody_allDirect (img : Linstr → Option (List (JInstr 64)))
    (himg : ImgAgrees img) (b : Lcmd) (blk : List (JInstr 64))
    (hb : gatherWith img b = some blk) (hd : ∀ x ∈ blk, IsDirect x) :
    ∃ blk', gatherWith img (dropDeadFlagOpsBody b) = some blk' ∧ ∀ x ∈ blk', IsDirect x := by
  obtain ⟨blk', h1, h2, -⟩ := dropDeadFlagOpsBody_runBlock img himg b blk hb
  exact ⟨blk', h1, fun x hx => hd x (h2.subset hx)⟩

/-- **Leakage.** A flag-only instruction, the only kind the pass deletes, emits no
    event under every leakage model of the labeled semantics. -/
theorem flagOnly_leak_nil {w : Nat} {ε : Type} (L : LprogLeak.LeakFn w ε) {i : Linstr}
    {ji : JInstr 64} (h : flagOnlyJ i = some ji) (s : VIR.JasminLsem.Lstate w) :
    L.ev s i.li_i = [] := by
  unfold flagOnlyJ at h
  split at h
  · rename_i d opn a b hli
    rw [hli]
    apply L.frag
    cases b <;> simp_all [flagSrcJ, LprogGpRealloc.regOrImm]
  · simp at h

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLoopPasses
