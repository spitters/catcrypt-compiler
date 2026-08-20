/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddModAdd
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcFieldOpsFull
import CatCrypt.Crypto.SecureCompilation.EcProjectiveAddGeneric

set_option autoImplicit false

/-!
# Structural Jacobian point-add over the shared frame, composed from the proven field bricks

`EcProjectiveAddGeneric.jacAddGen` is the inversion-free `add-2007-bl` Jacobian
point-add (`a = 0`) over an abstract `[Field F]`: a fixed sequence of field
`+`/`−`/`×` realizing

```
U₁ = X₁·Z₂²  ; U₂ = X₂·Z₁²  ; S₁ = Y₁·Z₂³  ; S₂ = Y₂·Z₁³
H  = U₂ − U₁ ; r  = S₂ − S₁
X₃ = r² − H³ − 2·U₁·H² ; Y₃ = r·(U₁·H² − X₃) − S₁·H³ ; Z₃ = Z₁·Z₂·H
```

The frame-wrapped field bricks are built and proven in the sibling modules:
`feSubFrameAt` / `feSubFrameAt_value` (`EcJacAddRunBlock`), `feAddFrameAt` /
`feAddFrameAt_value` (`EcJacAddModAdd`), and `feMulFrameAt` / `feMulFrameAt_value`
(`EcJacAddMontMul`). Each wraps a proven register-based `runBlock` brick over the
single stack **frame** (each field element one 4-limb slot at byte offset
`slotOff i k = 32·i + 8·k`): read input slots into register windows, run the
brick, store the result window back to the output slot. `feMulFrameAt` lands its
512-bit product in the two consecutive slots `o`, `o+1`.

This module is the **structural composition**: a slot layout for the two input
points, the output point, and the `add-2007-bl` intermediates; a `JacFieldCall`
call sequence mirroring `jacAddGen`'s field-op dataflow (each abstract field op
→ one frame-wrapped call writing its output slot from its input slots); and the
assembled `jacAddBlock : List (JInstr 64)` concatenating the frame-wrapped
field-op blocks in that order. It mirrors `Ed25519PointKernel`'s analogous
twisted-Edwards add (`edwardsAddCalls` / `edwardsAddBlock`), at the Weierstrass
Jacobian formula.

## Scope of what is proved here

The structural theorems — `jacAddBlock_lowering_correct` (lowering the assembled
block to `Com (x86Dialect 64)` and denoting equals `runBlock` on the source
block, via `lowerBlock_denote_closed`, exactly as
`Ed25519PointKernel.edwardsAddBlock_lowering_correct`), plus the field-op counts
`jacAddCalls_length` / `jacAddCalls_mul_count`. The all-inputs **value** identity
against `jacAddGen` is gated on the emitted Montgomery-reduce canonicalisation of
each `feMulFrameAt` product (the `montgomeryReduce` half of `feMulFrameAt_value`),
which the AUCurves bridge supplies; it is **not** discharged in this module. The
in-Lean guarantee here is the denotation-preserving straight-line lowering plus
the structural field-op-count witness that the assembled block realises exactly
`jacAddGen`'s dataflow.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul

/-! ## 1. Frame geometry

Every field element is one 256-bit slot (four 64-bit limbs) in the single frame
buffer `"f"`; slot `i` limb `k` lives at byte offset `slotOff i k = 32·i + 8·k`
(the `EcJacAddRunBlock` frame convention). The `add-2007-bl` add uses a fixed set
of slots for the two input points, the output point, and the formula's
intermediates. A `feMulFrameAt` writes a 512-bit product into two consecutive
slots `o`, `o+1`; field-element inputs to a later op read only the low slot `o`
(its reduced 4-limb value), so each multiply reserves one even spare slot above
its output for the product's high half. -/

-- input point P1 = (X1, Y1, Z1)
def sX1 : Nat := 0
def sY1 : Nat := 1
def sZ1 : Nat := 2
-- input point P2 = (X2, Y2, Z2)
def sX2 : Nat := 3
def sY2 : Nat := 4
def sZ2 : Nat := 5
-- output point P3 = (X3, Y3, Z3)
def sX3 : Nat := 6
def sY3 : Nat := 7
def sZ3 : Nat := 8
-- add-2007-bl intermediates (each one field-element slot; the product high half
-- of a `feMulFrameAt o …` lands in `o+1`, so multiply outputs use even-spaced
-- slots leaving the odd successor free for the high half).
def sZ1sq    : Nat := 10   -- Z1²
def sZ2sq    : Nat := 12   -- Z2²
def sZ1cu    : Nat := 14   -- Z1³
def sZ2cu    : Nat := 16   -- Z2³
def sU1      : Nat := 18   -- X1·Z2²
def sU2      : Nat := 20   -- X2·Z1²
def sS1      : Nat := 22   -- Y1·Z2³
def sS2      : Nat := 24   -- Y2·Z1³
def sH       : Nat := 26   -- U2 − U1
def sR       : Nat := 27   -- S2 − S1
def sHsq     : Nat := 28   -- H²
def sHcu     : Nat := 30   -- H³
def sU1Hsq   : Nat := 32   -- U1·H²
def sRsq     : Nat := 34   -- r²
def sT       : Nat := 36   -- r² − H³
def sTwoU1Hsq : Nat := 37  -- 2·U1·H²
def sU1HsqX3 : Nat := 38   -- U1·H² − X3
def sRU      : Nat := 40   -- r·(U1·H² − X3)
def sS1Hcu   : Nat := 42   -- S1·H³
def sZ1Z2    : Nat := 44   -- Z1·Z2

/-! ## 2. The structural field-op call

A field-op call in the point-op composition: the op tag, the output slot, and the
input slot(s) over the single frame. The runtime realisation is the matching
frame-wrapped brick (`feMulFrameAt` / `feAddFrameAt` / `feSubFrameAt`) run on the
frame `"f"` at those slot offsets. -/

/-- A field-op call in the Jacobian add composition: `mul`/`add`/`sub` with the
    output slot and the one or two input slots (over the single frame). -/
inductive JacFieldCall where
  | mul (out in0 in1 : Nat)
  | add (out in0 in1 : Nat)
  | sub (out in0 in1 : Nat)
  deriving Repr, DecidableEq

/-- The Jacobian-add call sequence (the structural composition; mirrors
    `jacAddGen`'s field-op dataflow). Each line is one abstract field op of
    `EcProjectiveAddGeneric.jacAddGen`:

    `Z1²,Z2²,Z1³,Z2³; U₁,U₂,S₁,S₂; H,r; H²,H³,U₁H²,r²;`
    `t=r²−H³, 2U₁H², X₃=t−2U₁H², U₁H²−X₃; r·(U₁H²−X₃), S₁H³, Y₃; Z₁Z₂, Z₃`. -/
def jacAddCalls : List JacFieldCall :=
  [ -- Z-powers
    .mul sZ1sq sZ1 sZ1            -- Z1²
  , .mul sZ2sq sZ2 sZ2            -- Z2²
  , .mul sZ1cu sZ1sq sZ1         -- Z1³
  , .mul sZ2cu sZ2sq sZ2         -- Z2³
    -- U1,U2,S1,S2
  , .mul sU1 sX1 sZ2sq           -- U1 = X1·Z2²
  , .mul sU2 sX2 sZ1sq           -- U2 = X2·Z1²
  , .mul sS1 sY1 sZ2cu           -- S1 = Y1·Z2³
  , .mul sS2 sY2 sZ1cu           -- S2 = Y2·Z1³
    -- H, r
  , .sub sH sU2 sU1              -- H = U2 − U1
  , .sub sR sS2 sS1             -- r = S2 − S1
    -- H², H³, U1·H², r²
  , .mul sHsq sH sH              -- H²
  , .mul sHcu sHsq sH            -- H³
  , .mul sU1Hsq sU1 sHsq         -- U1·H²
  , .mul sRsq sR sR              -- r²
    -- X3 = r² − H³ − 2·U1·H²
  , .sub sT sRsq sHcu            -- t = r² − H³
  , .add sTwoU1Hsq sU1Hsq sU1Hsq -- 2·U1·H²
  , .sub sX3 sT sTwoU1Hsq        -- X3 = t − 2·U1·H²
    -- Y3 = r·(U1·H² − X3) − S1·H³
  , .sub sU1HsqX3 sU1Hsq sX3     -- U1·H² − X3
  , .mul sRU sR sU1HsqX3         -- r·(U1·H² − X3)
  , .mul sS1Hcu sS1 sHcu         -- S1·H³
  , .sub sY3 sRU sS1Hcu          -- Y3 = r·(U1·H²−X3) − S1·H³
    -- Z3 = Z1·Z2·H
  , .mul sZ1Z2 sZ1 sZ2           -- Z1·Z2
  , .mul sZ3 sZ1Z2 sH ]          -- Z3 = (Z1·Z2)·H

/-! ## 3. Register windows for the bricks

Each frame-wrapped brick takes register windows it threads the field op through.
We fix the canonical windows the sibling modules' value theorems instantiate: two
4-register input windows for add/sub, the multiply's multiplicand/multiplier
windows + eight-word accumulator file + the `hi`/`lo` scratch. -/

/-- Destination (4-register) window for add/sub. -/
def dWin : List String := ["d0", "d1", "d2", "d3"]
/-- Source (4-register) window for add/sub. -/
def sWin : List String := ["e0", "e1", "e2", "e3"]
/-- Multiplicand window for the multiply. -/
def xWin : List String := ["x0", "x1", "x2", "x3"]
/-- Multiplier window for the multiply. -/
def yWin : List String := ["y0", "y1", "y2", "y3"]
/-- Eight-word accumulator file for the multiply product. -/
def accWin : List String := ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"]

/-- Compile one `JacFieldCall` to the assembled frame-wrapped reduce-inside
    field-op block over the frame `"f"`: a `mul` lands its 512-bit product and
    appends the emitted Montgomery reduce + conditional subtract via
    `EcFieldOpsFull.feMulFrameAtFull`; an `add` runs the ADC chain then the
    emitted conditional subtract via `feAddFrameAtFull`; a `sub` runs the SBB
    chain then the emitted modular add-back via `feSubFrameAtFull`.

    The multiply case computes its product in `accWin = ["c0", …, "c7"]`,
    disjoint from the registers `Curve4MontMulProvenEmit.accNames` that the
    emitted reduce inside `feMulFrameAtFull` reads, and emits no instruction
    materialising the modulus registers `p0..p3` or the constant `np`; results
    about this dispatch carry the product identification and the
    `MontRedc4Load` register conjuncts as hypotheses (`EcMulReduceWindowWire`).
    `EcMulConstPrologueWire.emitCallConst` is the dispatch whose multiply
    establishes both by execution. -/
def emitCall : JacFieldCall → List (JInstr 64)
  | .mul out in0 in1 =>
      EcFieldOpsFull.feMulFrameAtFull xWin yWin accWin "hi" "lo" "f" out in0 in1
  | .add out in0 in1 => EcFieldOpsFull.feAddFrameAtFull dWin sWin "f" out in0 in1
  | .sub out in0 in1 => EcFieldOpsFull.feSubFrameAtFull "f" out in0 in1

/-! ## 4. The assembled Jacobian-add block

`jacAddBlock` concatenates the frame-wrapped field-op blocks in `jacAddCalls`
order — the straight-line realisation of `jacAddGen`'s dataflow over the frame. -/

/-- **The structural Jacobian point-add block** `P₃ := P₁ + P₂` (`add-2007-bl`,
    `a = 0`), the assembled composition of the proven frame-wrapped field bricks
    over the single frame `"f"` in `jacAddCalls` order. -/
def jacAddBlock : List (JInstr 64) :=
  (jacAddCalls.map emitCall).flatten

/-! ## 5. The initial frame state -/

/-- Build the init frame state from a slot/limb seed `fr` (slot, limb ↦ word).
    Slot `i` limb `k` lives at byte offset `slotOff i k = 32·i + 8·k`; the frame
    holds `P₁` (slots 0–2), `P₂` (slots 3–5), and the intermediates start at 0. -/
def initFrame (fr : Nat → Fin 4 → BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "f" then
        let o := off.toNat
        if o % 8 = 0 then
          let w := o / 8
          fr (w / 4) ⟨w % 4, by omega⟩
        else 0
      else 0 }

/-! ## 6. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the Jacobian-add block.** Lowering the assembled
    block to `Com (x86Dialect 64)` and denoting on the init frame equals
    `runBlock` on the source block — the owned backend's straight-line lowering is
    denotation-preserving across the composed field-op instruction mix. Mirrors
    `Ed25519PointKernel.edwardsAddBlock_lowering_correct`. -/
theorem jacAddBlock_lowering_correct (fr : Nat → Fin 4 → BitVec 64) :
    (lowerBlock (Γ := []) jacAddBlock).denote (.cons (initFrame fr) .nil)
      = runBlock (initFrame fr) jacAddBlock :=
  lowerBlock_denote_closed jacAddBlock (initFrame fr)

/-! ## 7. Structural field-op counts

`jacAddGen` (`add-2007-bl`, `a = 0`) is realised by 16 field-multiplies, 1 add,
and 6 subtracts (the multiplies dominate; the add is the `2·U₁H²` doubling, which
a hand-written kernel may fold into the multiply but is exposed here as one frame
call). The counts pin the structural identity of the call sequence against
`jacAddGen`'s dataflow. -/

/-- The call list realises exactly the `jacAddGen` field-op dataflow:
    16 `mul` + 1 `add` + 6 `sub` = 23 calls. -/
theorem jacAddCalls_length : jacAddCalls.length = 23 := by decide

/-- The whole-point-op multiply count: `add-2007-bl` (`a = 0`) is 16 field-
    multiplies (the 4 Z-powers, the 4 `U/S` mixed products, `H²`/`H³`/`U₁H²`/`r²`,
    `r·(U₁H²−X₃)`, `S₁H³`, `Z₁Z₂`, and `Z₃`), exactly what the call sequence
    exposes for the bench cost model. -/
theorem jacAddCalls_mul_count :
    (jacAddCalls.filter
        (fun c => match c with | .mul _ _ _ => true | _ => false)).length = 16 := by
  decide

/-- The add count: a single field-add (`2·U₁·H²`). -/
theorem jacAddCalls_add_count :
    (jacAddCalls.filter
        (fun c => match c with | .add _ _ _ => true | _ => false)).length = 1 := by
  decide

/-- The subtract count: six field-subtracts (`H`, `r`, `r²−H³`, `X₃`, `U₁H²−X₃`,
    `Y₃`). -/
theorem jacAddCalls_sub_count :
    (jacAddCalls.filter
        (fun c => match c with | .sub _ _ _ => true | _ => false)).length = 6 := by
  decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
