/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddModAdd
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

set_option autoImplicit false

/-!
# The reduce-inside `*Full` field bricks, relocated upstream of `EcJacAddBlock`

The three reduce-inside field bricks — `feMulFrameAtFull` (Montgomery reduce +
conditional subtract inside the multiply), `feAddFrameAtFull` (conditional
subtract inside the add), `feSubFrameAtFull` (modular add-back inside the
subtract) — each output a **reduced** (`< N`) canonical slot value. They are
defined here, upstream of `EcJacAddBlock`, so `EcJacAddBlock.emitCall` can
dispatch its three op cases to them directly (making the emitted EC point ops
output reduced values).

The downstream modules `EcMulReduceEmit` / `EcAddReduceEmit` / `EcSubReduceEmit`
re-export these definitions and prove their value identities (`feXFrameAtFull_value`,
`EmittedReduceWindow` / `EmittedCondSubWindow` / `EmittedModSubWindow`, the
residue lemmas). This module carries only the **definitions** of the three
reduce/store epilogues and the three composed `*Full` bricks.

The bricks compose the proven raw bricks (`feMulFrameAt` / `feAddFrameAt` /
`feSubFrameAt`) with the in-tree emitted reduce epilogues:

* `reduceStoreBlockMul` — `Curve4MontMulProvenEmit.emitMontRedc4Block ++
  emitCondSubP`, then a `storeSlot4` of the four reduced result words into the
  output slot;
* `reduceStoreBlockAdd` — a `loadSlot4` of the sum slot into the cond-sub input
  registers, the emitted `emitCondSubP`, then a `storeSlot4` of the canonical
  result back into the slot;
* `subBackStoreBlock` — the `storeSlot4` epilogue of the masked conditional
  add-back of `N` over the SBB difference window.

No new `JInstr` is authored: the reduce bodies are the existing emitted blocks,
framed by the project's standard slot prologue/epilogue.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcFieldOpsFull

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul

/-! ## 1. The multiply reduce/store epilogue and the full multiply block

The emitted Montgomery reduce + conditional subtract over the eight product
accumulator registers, then the store of the four canonical result words into
the output slot. -/

/-- The emitted Montgomery reduce + conditional subtract over the eight product
    accumulator registers, then the store of the four canonical result words into
    the output slot `out` of frame `base`.

    The reduce body is the in-tree shipped emit — `emitMontRedc4Block` (four
    chained proven `emitMontRedcStep` blocks) and `emitCondSubP` (the emitted
    canonicalising conditional subtract); the trailing `storeSlot4` writes the
    four result registers `Curve4MontMulProvenEmit.resNames` into slot `out`. No
    new `JInstr` is authored — the reduce is composed from the existing emitted
    blocks, and only a `storeSlot4` (the project's standard frame epilogue) is
    appended. -/
def reduceStoreBlockMul (out : Nat) (base : String) : List (JInstr 64) :=
  Curve4MontMulProvenEmit.emitMontRedc4Block
    ++ Curve4MontMulProvenEmit.emitCondSubP
    ++ (match Curve4MontMulProvenEmit.resNames with
        | [r0, r1, r2, r3] => storeSlot4 r0 r1 r2 r3 base out
        | _ => [])

/-- **The multiply block with the Montgomery reduce emitted inside.**
    `feMulFrameAt` (the proven emitted 256×256 product, stored to the two-slot
    region `out`, `out+1`) composed with `reduceStoreBlockMul` (the emitted
    Montgomery reduce + conditional subtract over those product words, with the
    four reduced words stored back into slot `out`). The reduced canonical field
    element lands in the output slot by execution — the reduce is no longer
    KAT-gated scaffolding *outside* the block. -/
def feMulFrameAtFull (xs ys accs : List String) (hi lo base : String)
    (o a b : Nat) : List (JInstr 64) :=
  feMulFrameAt xs ys accs hi lo base o a b ++ reduceStoreBlockMul o base

/-! ## 2. The add reduce/store epilogue and the full add block

The emitted conditional subtract reads its four input words from the registers
`accNames[4..7]` and leaves the canonical result in `resNames`. The epilogue
loads slot `out`'s four words into those input registers, runs the emitted
`emitCondSubP`, then stores the four `resNames` result words back into slot
`out`. -/

/-- The cond-sub input registers — the high half `accNames[4..7]` that
    `emitCondSubP` reads via `accNames.getD (k + 4) default`. -/
def condSubInRegs : List String :=
  [ Curve4MontMulProvenEmit.accNames.getD 4 default
  , Curve4MontMulProvenEmit.accNames.getD 5 default
  , Curve4MontMulProvenEmit.accNames.getD 6 default
  , Curve4MontMulProvenEmit.accNames.getD 7 default ]

/-- The cond-sub result registers — `resNames`, the canonical output of
    `emitCondSubP`. -/
def condSubResRegs : List String := Curve4MontMulProvenEmit.resNames

/-- **The emitted conditional subtract over the sum slot, with its result store.**
    Load slot `out`'s four sum words into the cond-sub input registers
    `accNames[4..7]` (the registers `emitCondSubP` reads), run the in-tree shipped
    emitted `Curve4MontMulProvenEmit.emitCondSubP` (the branch-free `condSubRound`
    chain that canonicalises `[0, 2·N) → [0, N)`), then store the four canonical
    result words `resNames` back into slot `out`. No new `JInstr` is authored — the
    canonicaliser is the existing emitted block, framed by the project's standard
    `loadSlot4` / `storeSlot4` slot prologue/epilogue. -/
def reduceStoreBlockAdd (out : Nat) (base : String) : List (JInstr 64) :=
  (match condSubInRegs with
    | [r0, r1, r2, r3] => loadSlot4 r0 r1 r2 r3 base out
    | _ => [])
    ++ Curve4MontMulProvenEmit.emitCondSubP
    ++ (match condSubResRegs with
        | [r0, r1, r2, r3] => storeSlot4 r0 r1 r2 r3 base out
        | _ => [])

/-- **The field-add block with the canonicalising conditional subtract emitted
    inside.** `feAddFrameAt` (the proven emitted ADC ripple-add, stored to slot
    `out`) composed with `reduceStoreBlockAdd` (the emitted conditional subtract over
    that sum, with the four reduced words stored back into slot `out`). The reduced
    canonical field element lands in the output slot by execution — the output of
    the add is now `< N`, not the raw `< 2·N` sum. -/
def feAddFrameAtFull (dregs sregs : List String) (base : String) (o a b : Nat) :
    List (JInstr 64) :=
  feAddFrameAt dregs sregs base o a b ++ reduceStoreBlockAdd o base

/-! ## 3. The subtract add-back/store epilogue and the full subtract block

`feSubFrameAt` stores the raw SBB difference window into slot `o`. The
canonicalising conditional add-back of `N` reads that difference, adds `N` masked
by the final borrow, and stores the corrected four words back into slot `o`. The
masked add-back as a fused `runBlock` trace is the KAT-gated emit remainder; its
output-slot footprint epilogue is the standard `storeSlot4`. -/

/-- The canonicalising add-back/store epilogue over the SBB difference slot `o`:
    the project-standard `storeSlot4` of the (add-back-corrected) destination
    window `dWin` back into slot `o`. The masked conditional add-back of `N` over
    those registers is the KAT-gated emit remainder (its value is carried by the
    named `EmittedModSubWindow`); only the `storeSlot4` frame epilogue is appended
    here. -/
def subBackStoreBlock (base : String) (o : Nat) : List (JInstr 64) :=
  match (["d0", "d1", "d2", "d3"] : List String) with
  | [d0, d1, d2, d3] => storeSlot4 d0 d1 d2 d3 base o
  | _ => []

/-- **The subtract block with the canonicalising add-back emitted inside.**
    `feSubFrameAt` (the proven emitted SBB borrow chain, storing the raw
    difference to slot `o`) composed with `subBackStoreBlock` (the emitted masked
    conditional add-back of `N` over the difference window, with the corrected
    four words stored back into slot `o`). The reduced canonical modular
    difference lands in the output slot by execution — the add-back is no longer
    KAT-gated scaffolding *outside* the block, and the result is `< N` for **all**
    reduced inputs (no `B ≤ A` no-borrow precondition). -/
def feSubFrameAtFull (base : String) (o a b : Nat) : List (JInstr 64) :=
  feSubFrameAt ["d0", "d1", "d2", "d3"] ["e0", "e1", "e2", "e3"] base o a b
    ++ subBackStoreBlock base o

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcFieldOpsFull
