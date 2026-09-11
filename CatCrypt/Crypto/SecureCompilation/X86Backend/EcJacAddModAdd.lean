/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA

@[expose] public section

set_option autoImplicit false

/-!
# Frame-wrapped modular add over the Jacobian point-add frame

The Jacobian point-add composition (`EcJacAddRunBlock`) rests on a frame
load/store layer wrapping the register-based proven field bricks. That module
supplies the frame layer (`slotOff`, `loadSlot4`, `storeSlot4`, `slotLimbs`) and
the frame-wrapped modular **subtract** (`feSubFrameAt` / `feSubFrameAt_value`)
over the proven SBB borrow chain.

This module is the add-side mirror: `feAddFrameAt` is the frame-wrapped modular
**add** — read input slots `a` and `b` into two register windows
`dregs`/`sregs`, run the proven ADC carry chain on the windows
(`FieldAddSubTierA.emitAdcChain`), and store the sum window back to output slot
`o`. `feAddFrameAt_value` composes `loadSlot4_get` (inputs land in the windows) +
`FieldAddSubTierA.emitAdcChain_runBlock` (the destination window then holds the
abstract `addLimbs` sum) + `storeSlot4_load` (the sum window lands in slot `o`),
entered with `CF = 0`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven (addLimbs)

/-- Frame-wrapped modular add: load slot `a` into the destination window `dregs`,
    slot `b` into the source window `sregs`, run the emitted ADC carry chain over
    the two windows, and store the sum window back to slot `o`. The add-side
    mirror of `feSubFrameAt`. -/
def feAddFrameAt (dregs sregs : List String) (base : String) (o a b : Nat) :
    List (JInstr 64) :=
  match dregs, sregs with
  | [d0, d1, d2, d3], [e0, e1, e2, e3] =>
      loadSlot4 d0 d1 d2 d3 base a
        ++ loadSlot4 e0 e1 e2 e3 base b
        ++ emitAdcChain dregs sregs
        ++ storeSlot4 d0 d1 d2 d3 base o
  | _, _ => []

/-- **Frame-wrapped modular add value.** Running `feAddFrameAt` over a frame whose
    slots `a` and `b` hold four-limb field elements leaves output slot `o`'s four
    limbs equal to the abstract ADC ripple-add sum limbs
    `(addLimbs (slotLimbs s base a) (slotLimbs s base b) 0).1`. Composes
    `loadSlot4_get` (each input slot lands in its window), the proven
    `FieldAddSubTierA.emitAdcChain_runBlock` (the destination window then holds the
    `addLimbs` sum), and `storeSlot4_load` (the sum window lands in slot `o`).
    Entered with `CF = 0`, the carry-chain-entry condition. -/
theorem feAddFrameAt_value
    (d0 d1 d2 d3 e0 e1 e2 e3 base : String) (o a b : Nat) (s : JState 64)
    (hd10 : d1 ≠ d0) (hd20 : d2 ≠ d0) (hd21 : d2 ≠ d1)
    (hd30 : d3 ≠ d0) (hd31 : d3 ≠ d1) (hd32 : d3 ≠ d2)
    (he10 : e1 ≠ e0) (he20 : e2 ≠ e0) (he21 : e2 ≠ e1)
    (he30 : e3 ≠ e0) (he31 : e3 ≠ e1) (he32 : e3 ≠ e2)
    (hde : ∀ d ∈ [d0, d1, d2, d3], ∀ e ∈ [e0, e1, e2, e3], d ≠ e)
    (hcf0 : s.flagB (·.cf) = false) :
    slotLimbs (runBlock s (feAddFrameAt [d0, d1, d2, d3] [e0, e1, e2, e3] base o a b)) base o
      = (addLimbs (slotLimbs s base a) (slotLimbs s base b) 0).1 := by
  simp only [feAddFrameAt, runBlock_append]
  -- the three intermediate states
  set s1 := runBlock s (loadSlot4 d0 d1 d2 d3 base a) with hs1def
  set s2 := runBlock s1 (loadSlot4 e0 e1 e2 e3 base b) with hs2def
  set s3 := runBlock s2 (emitAdcChain [d0, d1, d2, d3] [e0, e1, e2, e3]) with hs3def
  -- disjointness of the two windows (each d distinct from each e)
  have hd0e : ∀ e ∈ [e0, e1, e2, e3], d0 ≠ e := hde d0 (by simp)
  have hd1e : ∀ e ∈ [e0, e1, e2, e3], d1 ≠ e := hde d1 (by simp)
  have hd2e : ∀ e ∈ [e0, e1, e2, e3], d2 ≠ e := hde d2 (by simp)
  have hd3e : ∀ e ∈ [e0, e1, e2, e3], d3 ≠ e := hde d3 (by simp)
  -- s1: the destination window holds slot-a's limbs.
  obtain ⟨hs1d0, hs1d1, hs1d2, hs1d3⟩ :=
    loadSlot4_get d0 d1 d2 d3 base a s hd10 hd20 hd21 hd30 hd31 hd32
  -- s2: the source window holds slot-b's limbs (load on s1)...
  obtain ⟨hs2e0, hs2e1, hs2e2, hs2e3⟩ :=
    loadSlot4_get e0 e1 e2 e3 base b s1 he10 he20 he21 he30 he31 he32
  -- ...and the destination window is untouched by the b-load (windows disjoint).
  have hs2d0 : s2.get d0 = s.load base (slotOff a 0) := by
    rw [hs2def, loadSlot4_other e0 e1 e2 e3 base b s1 d0
      (hd0e e0 (by simp)) (hd0e e1 (by simp)) (hd0e e2 (by simp)) (hd0e e3 (by simp)), hs1d0]
  have hs2d1 : s2.get d1 = s.load base (slotOff a 1) := by
    rw [hs2def, loadSlot4_other e0 e1 e2 e3 base b s1 d1
      (hd1e e0 (by simp)) (hd1e e1 (by simp)) (hd1e e2 (by simp)) (hd1e e3 (by simp)), hs1d1]
  have hs2d2 : s2.get d2 = s.load base (slotOff a 2) := by
    rw [hs2def, loadSlot4_other e0 e1 e2 e3 base b s1 d2
      (hd2e e0 (by simp)) (hd2e e1 (by simp)) (hd2e e2 (by simp)) (hd2e e3 (by simp)), hs1d2]
  have hs2d3 : s2.get d3 = s.load base (slotOff a 3) := by
    rw [hs2def, loadSlot4_other e0 e1 e2 e3 base b s1 d3
      (hd3e e0 (by simp)) (hd3e e1 (by simp)) (hd3e e2 (by simp)) (hd3e e3 (by simp)), hs1d3]
  -- the flag is still 0 at the ADC entry (loads touch no flag).
  have hs2cf : (s2.flagB fun x ↦ x.cf) = false := by
    rw [hs2def, loadSlot4_flagB, hs1def, loadSlot4_flagB, hcf0]
  -- ChainFresh for the two windows
  have hfresh : FieldAddSubTierA.ChainFresh [d0, d1, d2, d3] [e0, e1, e2, e3] :=
    { ds_nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          and_true, not_or, or_false, not_false_iff]
        refine ⟨⟨Ne.symm hd10, Ne.symm hd20, ?_⟩, ⟨Ne.symm hd21, ?_⟩, ?_⟩ <;>
          simp_all [Ne.symm hd30, Ne.symm hd31, Ne.symm hd32]
      ds_ss := hde }
  -- the destination window's get-map is slot-a's limbs; source window's is slot-b's.
  have hdmap : [d0, d1, d2, d3].map s2.get = slotLimbs s base a := by
    simp only [List.map_cons, List.map_nil, slotLimbs, hs2d0, hs2d1, hs2d2, hs2d3]
  have hsmap : [e0, e1, e2, e3].map s2.get = slotLimbs s base b := by
    rw [← hs2def] at hs2e0 hs2e1 hs2e2 hs2e3
    simp only [List.map_cons, List.map_nil, slotLimbs, hs2e0, hs2e1, hs2e2, hs2e3,
      hs1def, loadSlot4_load]
  -- the proven ADC chain leaves the sum limbs in the destination window of s3.
  obtain ⟨hsum, _⟩ := emitAdcChain_runBlock [d0, d1, d2, d3] [e0, e1, e2, e3]
    (slotLimbs s base a) (slotLimbs s base b) 0 s2
    rfl rfl rfl hfresh hdmap hsmap (by simp [hs2cf])
  -- store the sum window back to slot o, then read slot o's four limbs.
  obtain ⟨ho0, ho1, ho2, ho3⟩ := storeSlot4_load d0 d1 d2 d3 base o s3
  rw [← hs3def] at hsum
  simp only [List.map_cons, List.map_nil] at hsum
  simp only [slotLimbs, ho0, ho1, ho2, ho3]
  exact hsum

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
