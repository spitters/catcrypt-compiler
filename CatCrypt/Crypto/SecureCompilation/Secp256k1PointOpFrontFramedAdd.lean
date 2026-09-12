/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue

/-!
# secp256k1 Jacobian addition, FRAME-RELATIVE front tiling

A frame-relative re-tiling of the `add-2007-bl` addition body of
`Secp256k1PointOpFront`, the addition analogue of
`Secp256k1PointOpFrontFramed.jacDblBodyFramed`. Every intermediate field element
lives in a slot of a single memref frame `F` (slot `s` occupies cells
`4·s .. 4·s+3`). Each field-op brick loads its two operands from their frame
slots into brick-local half-limbs, runs the same operand-scanning brick body
(`feMulHalves` / `feAddHalves` / `feSubHalves` from `Secp256k1PointOpFront`), and
stores its eight result half-limbs back to the output frame slot. The next brick
loads from the frame rather than from a live SSA name, so the only value threaded
across bricks is the frame base `F`.

The brick generator `emitFOpFramed` is reused unchanged from
`Secp256k1PointOpFrontFramed`; it is op-generic and schedule-generic. Only the
schedule (`jacAddSchedule`) and slot map (`slotOfAdd`) differ from the doubling
tiling.

## Frame provenance (provisional)

The frame `F` is a single `116`-cell (`928`-byte) memref that is the sole context
parameter. The six input coordinates are assumed pre-placed in slots `0..5`
(`X1,Y1,Z1,X2,Y2,Z2`); the three output coordinates end in the frame slots their
schedule outputs occupy. As in the doubling module this isolates the lowering
cost of the framed tiling; the deployable kernel's ABI is a later decision.

## Main results

* `jacAddBodyFramed` — the full 23-brick frame-relative addition body as a
  `LowCT`, built only from existing `Secp256k1PointOpFront` /
  `Secp256k1PointOpFrontFramed` combinators.
* `jacAddBodyFramed_runs` — the whole frame-relative addition body runs to a
  defined exit environment from any input environment, unconditionally.
* `jacAddFrontComFramed` — `jacAddBodyFramed` pushed through
  `translateDialectControl` and capped with `ret F`, as a `Com catCryptDialect`.

## Framed ladder step (remaining work)

A frame-relative ladder step over a single frame `F` composes, in place:

1. `jacDblBodyFramed` on the accumulator slots (the frame threads across the
   trip because every value lives in `F`);
2. a framed conditional swap ("cswap"/select) of the accumulator and base slots,
   keyed on the current scalar bit — the one new brick, which needs a
   frame-relative select over the two point slot-ranges;
3. `jacAddBodyFramed` reading the (post-swap) accumulator and base slots.

The straight-line totality of a two-body composition over one frame is immediate
from `Secp256k1PointOpFramedValue.mapIdxFlatten_runs` on each body and
`semScalar_seqAll_append`; the missing pieces are (a) a unified slot layout that
places the doubling outputs `Xp,Yp,Zp` and the addition inputs `X1,Y1,Z1` in the
same slot range so the accumulator persists across the trip without a copy, and
(b) the framed select brick of step 2. Neither is expressible by reusing
`emitFOpFramed` alone (a select is not an `FOp`), so a ladder step is not built
here; this module delivers the framed addition body it composes.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedAdd

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront (FOp jacAddSchedule)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed (emitFOpFramed)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue
  (mapIdxFlatten_runs emitFOpFramed_runs)

/-! ## 1. Slot map and the full framed addition body -/

/-- Field-element names in first-appearance order: the six inputs, then each
    addition-schedule output. Slot `i` holds the `i`-th name (cells `4i .. 4i+3`). -/
def addNames : List String :=
  ["X1", "Y1", "Z1", "X2", "Y2", "Z2"] ++ jacAddSchedule.map (fun op => match op with
    | .mul o _ _ => o | .add o _ _ => o | .sub o _ _ => o)

/-- Frame slot index of a field-element name in the addition tiling. -/
def slotOfAdd (s : String) : Nat := addNames.idxOf s

/-- The 116-cell (928-byte) frame holds `addNames.length = 29` field elements. -/
def addFrameCells : Nat := 116

/-- The full 23-brick frame-relative addition body over the single frame `F`. -/
def jacAddBodyFramed : LowCT :=
  seqAll ((jacAddSchedule.mapIdx
    (fun i op => emitFOpFramed (8 * addFrameCells) "F" slotOfAdd i op)).flatten)

/-! ## 2. Termination of the framed addition body -/

/-- **The frame-relative `jacAdd` body runs to completion from any environment.**
    Each of the twenty-three frame-relative bricks binds every word it reads and
    the frame load and store never decline, so the whole body's waist semantics is
    defined on every input environment. The array arms never decline, so no frame
    precondition is needed. -/
theorem jacAddBodyFramed_runs (env : SEnvScalar) :
    ∃ env', semScalar jacAddBodyFramed env = some env' :=
  mapIdxFlatten_runs jacAddSchedule
    (fun i op => emitFOpFramed (8 * addFrameCells) "F" slotOfAdd i op)
    (fun i op e => emitFOpFramed_runs (8 * addFrameCells) slotOfAdd i op e) env

/-! ## 3. Front-compile -/

/-- Single-frame context: one 116-cell memref. -/
def inΓFAdd : Ctx := [.memref addFrameCells]

/-- Single-frame `VarMap`: the sole memref bound as `F`. -/
def inVMFAdd : VarMap inΓFAdd := VarMap.empty.bind (t := .memref addFrameCells) "F"

/-- Push `jacAddBodyFramed` through the direct control front, cap with `ret F`. -/
def jacAddFrontComFramed : Option (Com catCryptDialect inΓFAdd (.memref addFrameCells)) :=
  match translateDialectControl inVMFAdd jacAddBodyFramed with
  | some r =>
      match r.vm.lookup "F" with
      | some ⟨.memref 116, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedAdd
