/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

set_option autoImplicit false

/-!
# Emitted Jacobian point-add over `runBlock`, composed from the proven field bricks

The EC point-add value residual is, after `EcEmitRealizesFromGroupLaw`, the
byte-level fact "the emitted curve kernel's bytes realize the inversion-free
`add-2007-bl` Jacobian-add field formula `jacAddGen`"
(`EcProjectiveAddGeneric.jacAddGen`); everything above it — the projective→affine
inverse and the affine group law — is the proved `ec_jacAdd_realizes_affineAdd`.

The field operations `jacAddGen` is built from are each a proven emitted `runBlock`
block: full Montgomery multiply (`SchoolbookProductRunBlock.emitProductBlock` +
`MontReduceRunBlock.emitMontRedc4`), modular add (`FieldAddSubTierA.modAdd_runBlock`)
and modular sub (`FieldSubRunBlock.modSub_runBlock`). This module composes those
bricks over a single stack **frame** (each field element one 4-limb slot) so that a
straight-line `runBlock` of the composed block computes `jacAddGen` of the input
coordinates in Montgomery form — discharging the `ecJacKernelRealizes` residual that
`EcEmitRealizesFromGroupLaw` localizes.

## Frame geometry

Each field element is one slot of four 64-bit limbs; slot `i` limb `k` lives at byte
offset `slotOff i k = 32·i + 8·k` in the frame buffer (the `Ed25519PointKernel` frame
convention). A field op reads its input slots into a register window, runs the proven
field brick on that window, and stores the result window back to its output slot.

## This file

The composition rests on a frame load/store layer wrapping the register-based proven
bricks. `loadSlot4` is the input prologue (slot → register window); `loadSlot4_get` is
its reconstruction (the window holds the slot's limbs). The wrapped field ops and the
`jacAddGen` composition build on this layer.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Byte offset of slot `i`'s limb `k` in a frame buffer (one slot = four 64-bit
    limbs = 32 bytes), the `Ed25519PointKernel` frame convention. -/
def slotOff (i k : Nat) : Int := 32 * (i : Int) + 8 * (k : Int)

/-- Load slot `slot`'s four limbs from frame `base` into the register window
    `r0..r3` — the input prologue of a frame-wrapped field op. -/
def loadSlot4 (r0 r1 r2 r3 base : String) (slot : Nat) : List (JInstr 64) :=
  [ .loadMem r0 base (slotOff slot 0)
  , .loadMem r1 base (slotOff slot 1)
  , .loadMem r2 base (slotOff slot 2)
  , .loadMem r3 base (slotOff slot 3) ]

/-- **Frame-load reconstruction.** After `loadSlot4`, each window register holds the
    corresponding limb of `slot` (the loads read memory, which the register writes
    leave untouched, so the four reads see the original frame). -/
theorem loadSlot4_get (r0 r1 r2 r3 base : String) (slot : Nat) (s : JState 64)
    (h10 : r1 ≠ r0) (h20 : r2 ≠ r0) (h21 : r2 ≠ r1)
    (h30 : r3 ≠ r0) (h31 : r3 ≠ r1) (h32 : r3 ≠ r2) :
    (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).get r0 = s.load base (slotOff slot 0)
      ∧ (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).get r1 = s.load base (slotOff slot 1)
      ∧ (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).get r2 = s.load base (slotOff slot 2)
      ∧ (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).get r3 = s.load base (slotOff slot 3) := by
  simp only [loadSlot4, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.load,
    JState.setReg, JState.get]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [if_neg (Ne.symm h30), if_neg (Ne.symm h20), if_neg (Ne.symm h10),
      if_neg (Ne.symm h31), if_neg (Ne.symm h21), if_neg (Ne.symm h32), if_true]

/-- The four limb offsets of a single slot are pairwise distinct: `slotOff slot k`
    differs in `k` (they are `32·slot + 8·k`, an injective function of `k` for the
    fixed slot). Discharges the store-disjointness side conditions of
    `storeSlot4_load`. -/
theorem slotOff_inj (slot k k' : Nat) (h : k ≠ k') : slotOff slot k ≠ slotOff slot k' := by
  simp only [slotOff]
  omega

/-- Store the register window `r0..r3` back to slot `slot`'s four limbs in frame
    `base` — the output epilogue of a frame-wrapped field op (the mirror of
    `loadSlot4`). -/
def storeSlot4 (r0 r1 r2 r3 base : String) (slot : Nat) : List (JInstr 64) :=
  [ .storeMem base (slotOff slot 0) (.reg r0)
  , .storeMem base (slotOff slot 1) (.reg r1)
  , .storeMem base (slotOff slot 2) (.reg r2)
  , .storeMem base (slotOff slot 3) (.reg r3) ]

/-- **Frame-store reconstruction.** After `storeSlot4`, slot `slot`'s four limbs in
    frame `base` hold the four window-register values (the stores write the slot's
    four offsets, which are pairwise distinct, so each load reads its own store).
    Mirror of `loadSlot4_get` for stores. -/
theorem storeSlot4_load (r0 r1 r2 r3 base : String) (slot : Nat) (s : JState 64) :
    (runBlock s (storeSlot4 r0 r1 r2 r3 base slot)).load base (slotOff slot 0) = s.get r0
      ∧ (runBlock s (storeSlot4 r0 r1 r2 r3 base slot)).load base (slotOff slot 1) = s.get r1
      ∧ (runBlock s (storeSlot4 r0 r1 r2 r3 base slot)).load base (slotOff slot 2) = s.get r2
      ∧ (runBlock s (storeSlot4 r0 r1 r2 r3 base slot)).load base (slotOff slot 3) = s.get r3 := by
  simp only [storeSlot4, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval,
    JState.regs_store, JState.get]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [JState.load_store_other (h := fun h => slotOff_inj slot 0 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj slot 0 2 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj slot 0 1 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj slot 1 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj slot 1 2 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj slot 2 3 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_same]

/-- **Frame load/store round-trip.** Loading slot `slot` into a fresh distinct
    window `r0..r3` and immediately storing that window back to the same slot
    leaves the slot's four limbs unchanged: the load fills the window with the
    slot limbs (`loadSlot4_get`), and the store writes them straight back
    (`storeSlot4_load`). -/
theorem loadStoreSlot4_roundtrip (r0 r1 r2 r3 base : String) (slot : Nat) (s : JState 64)
    (h10 : r1 ≠ r0) (h20 : r2 ≠ r0) (h21 : r2 ≠ r1)
    (h30 : r3 ≠ r0) (h31 : r3 ≠ r1) (h32 : r3 ≠ r2) :
    (runBlock s (loadSlot4 r0 r1 r2 r3 base slot ++ storeSlot4 r0 r1 r2 r3 base slot)).load
        base (slotOff slot 0) = s.load base (slotOff slot 0)
      ∧ (runBlock s (loadSlot4 r0 r1 r2 r3 base slot ++ storeSlot4 r0 r1 r2 r3 base slot)).load
          base (slotOff slot 1) = s.load base (slotOff slot 1)
      ∧ (runBlock s (loadSlot4 r0 r1 r2 r3 base slot ++ storeSlot4 r0 r1 r2 r3 base slot)).load
          base (slotOff slot 2) = s.load base (slotOff slot 2)
      ∧ (runBlock s (loadSlot4 r0 r1 r2 r3 base slot ++ storeSlot4 r0 r1 r2 r3 base slot)).load
          base (slotOff slot 3) = s.load base (slotOff slot 3) := by
  rw [runBlock_append]
  set s1 := runBlock s (loadSlot4 r0 r1 r2 r3 base slot) with hs1
  obtain ⟨hl0, hl1, hl2, hl3⟩ := loadSlot4_get r0 r1 r2 r3 base slot s h10 h20 h21 h30 h31 h32
  obtain ⟨hs0, hs1', hs2, hs3⟩ := storeSlot4_load r0 r1 r2 r3 base slot s1
  rw [← hs1] at hl0 hl1 hl2 hl3
  exact ⟨by rw [hs0, hl0], by rw [hs1', hl1], by rw [hs2, hl2], by rw [hs3, hl3]⟩

/-! ## Frame-wrapped modular subtract

`feSubFrameAt` is the first frame-wrapped field op: read input slots `a` and `b`
into two register windows `dregs`/`sregs`, run the proven SBB borrow chain on the
windows (`FieldSubRunBlock.emitSbbChain`), and store the difference window back to
output slot `o`. `feSubFrameAt_value` composes `loadSlot4_get` (inputs land in the
windows) + `FieldSubRunBlock.emitSbbChain_runBlock` (the windows hold the abstract
`subLimbs` difference) + `storeSlot4_load` (the difference lands in slot `o`). -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

/-- The four-limb little-endian value vector held in slot `slot` of frame `base`. -/
def slotLimbs (s : JState 64) (base : String) (slot : Nat) : List (BitVec 64) :=
  [ s.load base (slotOff slot 0), s.load base (slotOff slot 1)
  , s.load base (slotOff slot 2), s.load base (slotOff slot 3) ]

/-- `loadSlot4` touches no flag: each step is a `loadMem`, i.e. a `setReg`, which
    preserves the flag map. -/
theorem loadSlot4_flagB (r0 r1 r2 r3 base : String) (slot : Nat) (s : JState 64)
    (f : RFlags → JFlag) :
    (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).flagB f = s.flagB f := by
  simp only [loadSlot4, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg,
    JState.flagB]

/-- `loadSlot4` writes no memory: each step is a `loadMem`/`setReg`, which leaves
    the memory unchanged, so any frame cell reads the same as before. -/
theorem loadSlot4_load (r0 r1 r2 r3 base : String) (slot : Nat) (s : JState 64)
    (b' : String) (o' : Int) :
    (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).load b' o' = s.load b' o' := by
  simp only [loadSlot4, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg,
    JState.load]

/-- `loadSlot4` writes only its window `r0..r3`: any register distinct from all four
    is preserved. -/
theorem loadSlot4_other (r0 r1 r2 r3 base : String) (slot : Nat) (s : JState 64)
    (r : String) (h0 : r ≠ r0) (h1 : r ≠ r1) (h2 : r ≠ r2) (h3 : r ≠ r3) :
    (runBlock s (loadSlot4 r0 r1 r2 r3 base slot)).get r = s.get r := by
  simp only [loadSlot4, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg,
    JState.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3]

/-- Frame-wrapped modular subtract: load slot `a` into the destination window
    `dregs`, slot `b` into the source window `sregs`, run the emitted SBB borrow
    chain over the two windows, and store the difference window back to slot `o`. -/
def feSubFrameAt (dregs sregs : List String) (base : String) (o a b : Nat) :
    List (JInstr 64) :=
  match dregs, sregs with
  | [d0, d1, d2, d3], [e0, e1, e2, e3] =>
      loadSlot4 d0 d1 d2 d3 base a
        ++ loadSlot4 e0 e1 e2 e3 base b
        ++ emitSbbChain dregs sregs
        ++ storeSlot4 d0 d1 d2 d3 base o
  | _, _ => []

/-- **Frame-wrapped modular subtract value.** Running `feSubFrameAt` over a frame
    whose slots `a` and `b` hold four-limb field elements leaves output slot `o`'s
    four limbs equal to the abstract SBB ripple-subtract difference limbs
    `(subLimbs (slotLimbs s base a) (slotLimbs s base b) 0).1`. Composes
    `loadSlot4_get` (each input slot lands in its window), the proven
    `FieldSubRunBlock.emitSbbChain_runBlock` (the destination window then holds the
    `subLimbs` difference), and `storeSlot4_load` (the difference window lands in
    slot `o`). Entered with `CF = 0`, the borrow-chain-entry condition. -/
theorem feSubFrameAt_value
    (d0 d1 d2 d3 e0 e1 e2 e3 base : String) (o a b : Nat) (s : JState 64)
    (hd10 : d1 ≠ d0) (hd20 : d2 ≠ d0) (hd21 : d2 ≠ d1)
    (hd30 : d3 ≠ d0) (hd31 : d3 ≠ d1) (hd32 : d3 ≠ d2)
    (he10 : e1 ≠ e0) (he20 : e2 ≠ e0) (he21 : e2 ≠ e1)
    (he30 : e3 ≠ e0) (he31 : e3 ≠ e1) (he32 : e3 ≠ e2)
    (hde : ∀ d ∈ [d0, d1, d2, d3], ∀ e ∈ [e0, e1, e2, e3], d ≠ e)
    (hcf0 : s.flagB (·.cf) = false) :
    slotLimbs (runBlock s (feSubFrameAt [d0, d1, d2, d3] [e0, e1, e2, e3] base o a b)) base o
      = (subLimbs (slotLimbs s base a) (slotLimbs s base b) 0).1 := by
  simp only [feSubFrameAt, runBlock_append]
  -- the three intermediate states
  set s1 := runBlock s (loadSlot4 d0 d1 d2 d3 base a) with hs1def
  set s2 := runBlock s1 (loadSlot4 e0 e1 e2 e3 base b) with hs2def
  set s3 := runBlock s2 (emitSbbChain [d0, d1, d2, d3] [e0, e1, e2, e3]) with hs3def
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
  -- the flag is still 0 at the SBB entry (loads touch no flag).
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
  -- the proven SBB chain leaves the difference limbs in the destination window of s3.
  obtain ⟨hdiff, _⟩ := emitSbbChain_runBlock [d0, d1, d2, d3] [e0, e1, e2, e3]
    (slotLimbs s base a) (slotLimbs s base b) 0 s2
    rfl rfl rfl hfresh hdmap hsmap (by simp [hs2cf])
  -- store the difference window back to slot o, then read slot o's four limbs.
  obtain ⟨ho0, ho1, ho2, ho3⟩ := storeSlot4_load d0 d1 d2 d3 base o s3
  rw [← hs3def] at hdiff
  simp only [List.map_cons, List.map_nil] at hdiff
  simp only [slotLimbs, ho0, ho1, ho2, ho3]
  exact hdiff

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
