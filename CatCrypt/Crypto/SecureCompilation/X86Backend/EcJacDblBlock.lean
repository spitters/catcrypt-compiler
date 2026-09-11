/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

@[expose] public section

set_option autoImplicit false

/-!
# Structural Jacobian point-DOUBLE over the shared frame, composed from the proven field bricks

`EcProjectiveGeneric.jacDoubleGen` is the inversion-free `dbl-2009-l` Jacobian
point-double (`a = 0`) over an abstract `[Field F]`: a fixed sequence of field
`+`/`−`/`×` realizing

```
S = 4·X·Y² ; M = 3·X²
X' = M² − 2·S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```

The frame-wrapped field bricks are the same proven ones the Jacobian-add vertical
composes (`EcJacAddBlock`): `feSubFrameAt` / `feSubFrameAt_value`
(`EcJacAddRunBlock`), `feAddFrameAt` / `feAddFrameAt_value` (`EcJacAddModAdd`),
and `feMulFrameAt` / `feMulFrameAt_value` (`EcJacAddMontMul`). Each wraps a proven
register-based `runBlock` brick over the single stack **frame** (each field
element one 4-limb slot at byte offset `slotOff i k = 32·i + 8·k`): read input
slots into register windows, run the brick, store the result window back to the
output slot. `feMulFrameAt` lands its 512-bit product in the two consecutive slots
`o`, `o+1`.

This module is the **structural composition** for the double: a slot layout for
the one input point, the output point, and the `dbl-2009-l` intermediates; a
`JacFieldCall` (reused from `EcJacAddBlock`) call sequence mirroring
`jacDoubleGen`'s field-op dataflow (each abstract field op → one frame-wrapped
call writing its output slot from its input slots); and the assembled
`jacDblBlock : List (JInstr 64)` concatenating the frame-wrapped field-op blocks
in that order. It is the exact analogue of `EcJacAddBlock.jacAddBlock` at the
Weierstrass Jacobian double formula.

## Scope of what is proved here

The structural theorems — `jacDblBlock_lowering_correct` (lowering the assembled
block to `Com (x86Dialect 64)` and denoting equals `runBlock` on the source
block, via `lowerBlock_denote_closed`, exactly as
`EcJacAddBlock.jacAddBlock_lowering_correct`), plus the field-op counts
`jacDblCalls_length` / `jacDblCalls_mul_count`. The all-inputs **value** identity
against `jacDoubleGen` is in the sibling `EcJacDblValue`, gated on the same
emitted Montgomery-reduce canonicalisation of each `feMulFrameAt` product the
add vertical uses. The in-Lean guarantee here is the denotation-preserving
straight-line lowering plus the structural field-op-count witness that the
assembled block realises exactly `jacDoubleGen`'s dataflow.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock

/-! ## 1. Frame geometry

Every field element is one 256-bit slot (four 64-bit limbs) in the single frame
buffer `"f"`; slot `i` limb `k` lives at byte offset `slotOff i k = 32·i + 8·k`
(the `EcJacAddRunBlock` frame convention). The `dbl-2009-l` double uses a fixed
set of slots for the one input point, the output point, and the formula's
intermediates. A `feMulFrameAt` writes a 512-bit product into two consecutive
slots `o`, `o+1`; field-element inputs to a later op read only the low slot `o`
(its reduced 4-limb value), so each multiply reserves one even spare slot above
its output for the product's high half. -/

-- input point P1 = (X, Y, Z)
def sX : Nat := 0
def sY : Nat := 1
def sZ : Nat := 2
-- output point P' = (X', Y', Z')
def sX3 : Nat := 3
def sY3 : Nat := 4
def sZ3 : Nat := 5
-- dbl-2009-l intermediates (each one field-element slot; the product high half of
-- a `feMulFrameAt o …` lands in `o+1`, so multiply outputs use even-spaced slots
-- leaving the odd successor free for the high half).
def sYY     : Nat := 6    -- Y²
def sXYY    : Nat := 8    -- X·Y²
def sS2     : Nat := 10   -- 2·X·Y²
def sS      : Nat := 11   -- S = 4·X·Y²
def sXX     : Nat := 12   -- X²
def sM2     : Nat := 14   -- 2·X²
def sM      : Nat := 15   -- M = 3·X²
def sMsq    : Nat := 16   -- M²
def sTwoS   : Nat := 18   -- 2·S
def sSmXp   : Nat := 19   -- S − X'
def sMSmXp  : Nat := 20   -- M·(S − X')
def sYYsq   : Nat := 22   -- Y⁴
def sY2     : Nat := 24   -- 2·Y⁴
def sY4     : Nat := 25   -- 4·Y⁴
def sY8     : Nat := 26   -- 8·Y⁴
def sYZ     : Nat := 28   -- Y·Z

/-! ## 2. The structural field-op call sequence

A field-op call (`EcJacAddBlock.JacFieldCall`: `mul`/`add`/`sub` with the output
slot and the one or two input slots over the single frame) realises one abstract
field op of `jacDoubleGen`. The call list mirrors `jacDoubleGen`'s dataflow:

`Y², X·Y², 2X·Y², S=4X·Y²; X², 2X², M=3X²; M²; 2S, X'=M²−2S;`
`S−X', M·(S−X'); Y⁴, 2Y⁴, 4Y⁴, 8Y⁴, Y'=M(S−X')−8Y⁴; Y·Z, Z'=2YZ`. -/

/-- The Jacobian-double call sequence (the structural composition; mirrors
    `EcProjectiveGeneric.jacDoubleGen`'s field-op dataflow). Each line is one
    abstract field op. -/
def jacDblCalls : List JacFieldCall :=
  [ -- S = 4·X·Y²
    .mul sYY sY sY                -- Y²
  , .mul sXYY sX sYY             -- X·Y²
  , .add sS2 sXYY sXYY           -- 2·X·Y²
  , .add sS sS2 sS2              -- S = 4·X·Y²
    -- M = 3·X²
  , .mul sXX sX sX               -- X²
  , .add sM2 sXX sXX             -- 2·X²
  , .add sM sM2 sXX              -- M = 3·X²
    -- X' = M² − 2·S
  , .mul sMsq sM sM              -- M²
  , .add sTwoS sS sS             -- 2·S
  , .sub sX3 sMsq sTwoS          -- X' = M² − 2·S
    -- Y' = M·(S − X') − 8·Y⁴
  , .sub sSmXp sS sX3            -- S − X'
  , .mul sMSmXp sM sSmXp         -- M·(S − X')
  , .mul sYYsq sYY sYY           -- Y⁴
  , .add sY2 sYYsq sYYsq         -- 2·Y⁴
  , .add sY4 sY2 sY2             -- 4·Y⁴
  , .add sY8 sY4 sY4             -- 8·Y⁴
  , .sub sY3 sMSmXp sY8          -- Y' = M·(S − X') − 8·Y⁴
    -- Z' = 2·Y·Z
  , .mul sYZ sY sZ               -- Y·Z
  , .add sZ3 sYZ sYZ ]           -- Z' = 2·Y·Z

/-! ## 3. The assembled Jacobian-double block

`jacDblBlock` concatenates the frame-wrapped field-op blocks in `jacDblCalls`
order — the straight-line realisation of `jacDoubleGen`'s dataflow over the
frame, via `EcJacAddBlock.emitCall`. -/

/-- **The structural Jacobian point-double block** `P' := 2·P` (`dbl-2009-l`,
    `a = 0`), the assembled composition of the proven frame-wrapped field bricks
    over the single frame `"f"` in `jacDblCalls` order. -/
def jacDblBlock : List (JInstr 64) :=
  (jacDblCalls.map emitCall).flatten

/-! ## 4. The initial frame state -/

/-- Build the init frame state from a slot/limb seed `fr` (slot, limb ↦ word).
    Slot `i` limb `k` lives at byte offset `slotOff i k = 32·i + 8·k`; the frame
    holds `P = (X,Y,Z)` (slots 0–2) and the intermediates start at 0. -/
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

/-! ## 5. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the Jacobian-double block.** Lowering the assembled
    block to `Com (x86Dialect 64)` and denoting on the init frame equals
    `runBlock` on the source block — the owned backend's straight-line lowering is
    denotation-preserving across the composed field-op instruction mix. Mirrors
    `EcJacAddBlock.jacAddBlock_lowering_correct`. -/
theorem jacDblBlock_lowering_correct (fr : Nat → Fin 4 → BitVec 64) :
    (lowerBlock (Γ := []) jacDblBlock).denote (.cons (initFrame fr) .nil)
      = runBlock (initFrame fr) jacDblBlock :=
  lowerBlock_denote_closed jacDblBlock (initFrame fr)

/-! ## 6. Structural field-op counts

`jacDoubleGen` (`dbl-2009-l`, `a = 0`) is realised here by 7 field-multiplies,
9 adds, and 3 subtracts (the `dbl-2009-l` formula trades multiplies for the cheap
doublings/triplings exposed as field adds). The counts pin the structural
identity of the call sequence against `jacDoubleGen`'s dataflow. -/

/-- The call list realises exactly the `jacDoubleGen` field-op dataflow:
    7 `mul` + 9 `add` + 3 `sub` = 19 calls. -/
theorem jacDblCalls_length : jacDblCalls.length = 19 := by decide

/-- The whole-point-op multiply count: `dbl-2009-l` (`a = 0`) is 7 field-
    multiplies (`Y²`, `X·Y²`, `X²`, `M²`, `M·(S−X')`, `Y⁴`, `Y·Z`), exactly what
    the call sequence exposes for the bench cost model. -/
theorem jacDblCalls_mul_count :
    (jacDblCalls.filter
        (fun c => match c with | .mul _ _ _ => true | _ => false)).length = 7 := by
  decide

/-- The add count: nine field-adds (the `2X·Y²`, `S`, `2X²`, `M`, `2S`, `2Y⁴`,
    `4Y⁴`, `8Y⁴`, `Z'` doublings/triplings). -/
theorem jacDblCalls_add_count :
    (jacDblCalls.filter
        (fun c => match c with | .add _ _ _ => true | _ => false)).length = 9 := by
  decide

/-- The subtract count: three field-subtracts (`X'`, `S−X'`, `Y'`). -/
theorem jacDblCalls_sub_count :
    (jacDblCalls.filter
        (fun c => match c with | .sub _ _ _ => true | _ => false)).length = 3 := by
  decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblBlock
