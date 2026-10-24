/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

@[expose] public section

set_option autoImplicit false

/-!
# Six-limb (384-bit) Jacobian point-add frame layer over `runBlock`

`EcJacAddRunBlock.lean` builds the four-limb frame load/store layer (32-byte
slots, four 64-bit windows) over which the secp256k1 / P-256 / BN254 Jacobian
point-add composes its proven field bricks. This module is its **six-limb**
mirror, the frame geometry the P-384 / BLS12-381 Jacobian point-add composes
over: each field element is one slot of six 64-bit limbs (48 bytes), and the
512-bit-style product of two field elements (here 768 bits = twelve words)
occupies two consecutive six-limb slots.

## Frame geometry

Each field element is one slot of six 64-bit limbs; slot `i` limb `k` lives at
byte offset `slotOff6 i k = 48·i + 8·k` in the frame buffer. A field op reads its
input slots into register windows, runs the proven six-limb field brick on those
windows, and stores the result window back to its output slot. The twelve-word
product occupies the two consecutive slots `o` (limbs `0..5`) and `o+1` (limbs
`0..5`), equivalently the twelve offsets `slotOff6 o 0 .. slotOff6 o 11`
(`= 48·o + 8·k`, `k = 0..11`), since `slotOff6 o (6 + j) = slotOff6 (o+1) j`.

## This file

* `slotOff6` / `slotOff6_inj` — the 48-byte slot geometry and its limb-offset
  injectivity (the store-disjointness discharger);
* `loadSlot6` / `loadSlot6_get` (+ `loadSlot6_flagB`, `loadSlot6_load`,
  `loadSlot6_other`) — the six-limb input prologue and its reconstruction /
  non-interference lemmas;
* `storeSlot6` / `storeSlot6_load` (+ `storeSlot6_load_other`) — the six-limb
  output epilogue and its reconstruction / disjoint-cell non-interference;
* `slotLimbs6` — the six-limb little-endian value vector held in a slot;
* `storeSlot12` / `slotLimbs12` / `storeSlot12_load` — the twelve-word product
  store into the two-slot output region and its reconstruction.

These mirror the four-limb `EcJacAddRunBlock` (`slotOff`, `loadSlot4`,
`storeSlot4`, `slotLimbs`) and `EcJacAddMontMul` (`storeSlot8`, `slotLimbs8`) at
six limbs / twelve product words, feeding `EcJacAdd6FieldOps` (the frame-wrapped
six-limb field ops) above.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6RunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The six-limb slot geometry -/

/-- Byte offset of slot `i`'s limb `k` in a frame buffer (one slot = six 64-bit
    limbs = 48 bytes), the six-limb analogue of `EcJacAddRunBlock.slotOff`. -/
def slotOff6 (i k : Nat) : Int := 48 * (i : Int) + 8 * (k : Int)

/-- The limb offsets of a single slot are pairwise distinct in `k`: `slotOff6 i k`
    is `48·i + 8·k`, an injective function of `k` for the fixed slot. Discharges
    the store-disjointness side conditions of `storeSlot6_load` / `storeSlot12_load`.
    (Stated for any two slots `i i'` with equal value forcing `k = k'` only when
    `i = i'`; the curve uses the same-slot specialisation, but the general form is
    no harder and serves the cross-slot product geometry `slotOff6 o (6+j) =
    slotOff6 (o+1) j`.) -/
theorem slotOff6_inj (slot k k' : Nat) (h : k ≠ k') : slotOff6 slot k ≠ slotOff6 slot k' := by
  simp only [slotOff6]
  omega

/-- Cross-slot offset identity: the twelve product words rooted at slot `o` reach
    into slot `o+1`, with `slotOff6 o (6 + j) = slotOff6 (o+1) j`. -/
theorem slotOff6_hi (o j : Nat) : slotOff6 o (6 + j) = slotOff6 (o + 1) j := by
  simp only [slotOff6]; push_cast; ring

/-! ## 2. The six-limb load window -/

/-- Load slot `slot`'s six limbs from frame `base` into the register window
    `r0..r5` — the input prologue of a frame-wrapped six-limb field op. -/
def loadSlot6 (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) : List (JInstr 64) :=
  [ .loadMem r0 base (slotOff6 slot 0)
  , .loadMem r1 base (slotOff6 slot 1)
  , .loadMem r2 base (slotOff6 slot 2)
  , .loadMem r3 base (slotOff6 slot 3)
  , .loadMem r4 base (slotOff6 slot 4)
  , .loadMem r5 base (slotOff6 slot 5) ]

/-- **Frame-load reconstruction.** After `loadSlot6`, each window register holds
    the corresponding limb of `slot` (the loads read memory, which the register
    writes leave untouched, so the six reads see the original frame). The six-limb
    analogue of `EcJacAddRunBlock.loadSlot4_get`. -/
theorem loadSlot6_get (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) (s : JState 64)
    (h10 : r1 ≠ r0) (h20 : r2 ≠ r0) (h21 : r2 ≠ r1)
    (h30 : r3 ≠ r0) (h31 : r3 ≠ r1) (h32 : r3 ≠ r2)
    (h40 : r4 ≠ r0) (h41 : r4 ≠ r1) (h42 : r4 ≠ r2) (h43 : r4 ≠ r3)
    (h50 : r5 ≠ r0) (h51 : r5 ≠ r1) (h52 : r5 ≠ r2) (h53 : r5 ≠ r3) (h54 : r5 ≠ r4) :
    (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r0 = s.load base (slotOff6 slot 0)
      ∧ (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r1 = s.load base (slotOff6 slot 1)
      ∧ (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r2 = s.load base (slotOff6 slot 2)
      ∧ (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r3 = s.load base (slotOff6 slot 3)
      ∧ (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r4 = s.load base (slotOff6 slot 4)
      ∧ (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r5
          = s.load base (slotOff6 slot 5) := by
  simp only [loadSlot6, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.load,
    JState.setReg, JState.get]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ite_eq_right (Ne.symm h50), ite_eq_right (Ne.symm h40), ite_eq_right (Ne.symm h30),
      ite_eq_right (Ne.symm h20), ite_eq_right (Ne.symm h10), ite_eq_right (Ne.symm h51), ite_eq_right (Ne.symm h41),
      ite_eq_right (Ne.symm h31), ite_eq_right (Ne.symm h21), ite_eq_right (Ne.symm h52), ite_eq_right (Ne.symm h42),
      ite_eq_right (Ne.symm h32), ite_eq_right (Ne.symm h53), ite_eq_right (Ne.symm h43), ite_eq_right (Ne.symm h54),
      ite_true]

/-- `loadSlot6` touches no flag: each step is a `loadMem`, i.e. a `setReg`, which
    preserves the flag map. -/
theorem loadSlot6_flagB (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) (s : JState 64)
    (f : RFlags → JFlag) :
    (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).flagB f = s.flagB f := by
  simp only [loadSlot6, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg,
    JState.flagB]

/-- `loadSlot6` writes no memory: each step is a `loadMem`/`setReg`, which leaves
    the memory unchanged, so any frame cell reads the same as before. -/
theorem loadSlot6_load (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) (s : JState 64)
    (b' : String) (o' : Int) :
    (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).load b' o' = s.load b' o' := by
  simp only [loadSlot6, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg,
    JState.load]

/-- `loadSlot6` writes only its window `r0..r5`: any register distinct from all six
    is preserved. -/
theorem loadSlot6_other (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) (s : JState 64)
    (r : String) (h0 : r ≠ r0) (h1 : r ≠ r1) (h2 : r ≠ r2) (h3 : r ≠ r3)
    (h4 : r ≠ r4) (h5 : r ≠ r5) :
    (runBlock s (loadSlot6 r0 r1 r2 r3 r4 r5 base slot)).get r = s.get r := by
  simp only [loadSlot6, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg,
    JState.get, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]

/-! ## 3. The six-limb store window -/

/-- Store the register window `r0..r5` back to slot `slot`'s six limbs in frame
    `base` — the output epilogue of a frame-wrapped six-limb field op (the mirror
    of `loadSlot6`). -/
def storeSlot6 (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) : List (JInstr 64) :=
  [ .storeMem base (slotOff6 slot 0) (.reg r0)
  , .storeMem base (slotOff6 slot 1) (.reg r1)
  , .storeMem base (slotOff6 slot 2) (.reg r2)
  , .storeMem base (slotOff6 slot 3) (.reg r3)
  , .storeMem base (slotOff6 slot 4) (.reg r4)
  , .storeMem base (slotOff6 slot 5) (.reg r5) ]

/-- **Frame-store reconstruction.** After `storeSlot6`, slot `slot`'s six limbs in
    frame `base` hold the six window-register values (the stores write the slot's
    six offsets, which are pairwise distinct, so each load reads its own store).
    The six-limb analogue of `EcJacAddRunBlock.storeSlot4_load`. -/
theorem storeSlot6_load (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) (s : JState 64) :
    (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base (slotOff6 slot 0) = s.get r0
      ∧ (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base (slotOff6 slot 1) = s.get r1
      ∧ (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base (slotOff6 slot 2) = s.get r2
      ∧ (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base (slotOff6 slot 3) = s.get r3
      ∧ (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base (slotOff6 slot 4) = s.get r4
      ∧ (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base (slotOff6 slot 5)
          = s.get r5 := by
  simp only [storeSlot6, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval,
    JState.regs_store, JState.get]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [JState.load_store_other (h := fun h => slotOff6_inj slot 0 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 0 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 0 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 0 2 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 0 1 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj slot 1 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 1 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 1 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 1 2 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj slot 2 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 2 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 2 3 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj slot 3 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj slot 3 4 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj slot 4 5 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_same]

/-- **Frame-store non-interference.** A frame cell `(base, off)` distinct from all
    six store offsets of slot `slot` is untouched by `storeSlot6` — the
    disjoint-slot reconstruction (a store to one slot leaves any other slot's limbs
    unchanged), via `JState.load_store_other`. -/
theorem storeSlot6_load_other (r0 r1 r2 r3 r4 r5 base : String) (slot : Nat) (s : JState 64)
    (off : Int)
    (h0 : off ≠ slotOff6 slot 0) (h1 : off ≠ slotOff6 slot 1) (h2 : off ≠ slotOff6 slot 2)
    (h3 : off ≠ slotOff6 slot 3) (h4 : off ≠ slotOff6 slot 4) (h5 : off ≠ slotOff6 slot 5) :
    (runBlock s (storeSlot6 r0 r1 r2 r3 r4 r5 base slot)).load base off = s.load base off := by
  simp only [storeSlot6, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval]
  rw [JState.load_store_other (h := fun h => h5 h.2),
    JState.load_store_other (h := fun h => h4 h.2),
    JState.load_store_other (h := fun h => h3 h.2),
    JState.load_store_other (h := fun h => h2 h.2),
    JState.load_store_other (h := fun h => h1 h.2),
    JState.load_store_other (h := fun h => h0 h.2)]

/-- The six-limb little-endian value vector held in slot `slot` of frame `base`. -/
def slotLimbs6 (s : JState 64) (base : String) (slot : Nat) : List (BitVec 64) :=
  [ s.load base (slotOff6 slot 0), s.load base (slotOff6 slot 1)
  , s.load base (slotOff6 slot 2), s.load base (slotOff6 slot 3)
  , s.load base (slotOff6 slot 4), s.load base (slotOff6 slot 5) ]

/-! ## 4. The twelve-word product store (two consecutive slots)

The 384×384 product is 768 bits — twelve 64-bit words. Reusing the slot byte
geometry (`slotOff6 i k = 48·i + 8·k`), the twelve product words occupy the two
consecutive slots `o` (limbs `0..5`) and `o+1` (limbs `0..5`); equivalently the
twelve offsets `slotOff6 o 0 .. slotOff6 o 11` (`slotOff6 o (6 + j) =
slotOff6 (o+1) j`). `storeSlot12` writes a twelve-register window to those
offsets and `storeSlot12_load` reconstructs them. -/

/-- Store the twelve-register window `r0..r11` (the 768-bit product) into the
    twelve contiguous frame words at offsets `slotOff6 o 0 .. slotOff6 o 11` (the
    two-slot output region `o`, `o+1`). Mirror of `EcJacAddMontMul.storeSlot8` at
    width twelve. -/
def storeSlot12 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 base : String) (o : Nat) :
    List (JInstr 64) :=
  [ .storeMem base (slotOff6 o 0) (.reg r0)
  , .storeMem base (slotOff6 o 1) (.reg r1)
  , .storeMem base (slotOff6 o 2) (.reg r2)
  , .storeMem base (slotOff6 o 3) (.reg r3)
  , .storeMem base (slotOff6 o 4) (.reg r4)
  , .storeMem base (slotOff6 o 5) (.reg r5)
  , .storeMem base (slotOff6 o 6) (.reg r6)
  , .storeMem base (slotOff6 o 7) (.reg r7)
  , .storeMem base (slotOff6 o 8) (.reg r8)
  , .storeMem base (slotOff6 o 9) (.reg r9)
  , .storeMem base (slotOff6 o 10) (.reg r10)
  , .storeMem base (slotOff6 o 11) (.reg r11) ]

/-- The twelve-word little-endian value vector held in the output region of frame
    `base` rooted at slot `o` (offsets `slotOff6 o 0 .. slotOff6 o 11`). -/
def slotLimbs12 (s : JState 64) (base : String) (o : Nat) : List (BitVec 64) :=
  [ s.load base (slotOff6 o 0), s.load base (slotOff6 o 1)
  , s.load base (slotOff6 o 2), s.load base (slotOff6 o 3)
  , s.load base (slotOff6 o 4), s.load base (slotOff6 o 5)
  , s.load base (slotOff6 o 6), s.load base (slotOff6 o 7)
  , s.load base (slotOff6 o 8), s.load base (slotOff6 o 9)
  , s.load base (slotOff6 o 10), s.load base (slotOff6 o 11) ]

/-- **Frame-store reconstruction (twelve words).** After `storeSlot12 r0..r11
    base o`, each of the twelve output words holds its register value: the twelve
    stored offsets `slotOff6 o 0 .. slotOff6 o 11` are pairwise distinct
    (`slotOff6_inj`), so each load reads its own store. The twelve-word analogue of
    `EcJacAddMontMul.storeSlot8_load`. -/
theorem storeSlot12_load (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 base : String) (o : Nat)
    (s : JState 64) :
    slotLimbs12 (runBlock s (storeSlot12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 base o)) base o
      = [ s.get r0, s.get r1, s.get r2, s.get r3, s.get r4, s.get r5
        , s.get r6, s.get r7, s.get r8, s.get r9, s.get r10, s.get r11 ] := by
  simp only [storeSlot12, slotLimbs12, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
    JOperand.eval, JState.regs_store, JState.get, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 0 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 2 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 0 1 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 1 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 1 2 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 2 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 2 3 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 3 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 3 4 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 4 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 4 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 4 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 4 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 4 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 4 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 4 5 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 5 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 5 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 5 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 5 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 5 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 5 6 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 6 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 6 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 6 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 6 8 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 6 7 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 7 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 7 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 7 9 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 7 8 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 8 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 8 10 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 8 9 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 9 11 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff6_inj o 9 10 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff6_inj o 10 11 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_same]

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6RunBlock
