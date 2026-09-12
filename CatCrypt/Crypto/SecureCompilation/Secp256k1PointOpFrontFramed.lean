/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront

@[expose] public section

set_option autoImplicit false

/-!
# secp256k1 Jacobian doubling, FRAME-RELATIVE front tiling (lowering-cost prototype)

A frame-relative re-tiling of the `dbl-2009-l` doubling body of
`Secp256k1PointOpFront`. Every intermediate field element lives in a slot of a
single memref frame `F` (slot `s` occupies cells `4·s .. 4·s+3`). Each field-op
brick loads its two operands from their frame slots into brick-local half-limbs,
runs the same operand-scanning brick body (`feMulHalves` / `feAddHalves` /
`feSubHalves` from `Secp256k1PointOpFront`), and stores its eight result
half-limbs back to the output frame slot. The next brick loads from the frame
rather than from a live SSA name, so every operand, constant and index reference
is to a recently bound variable; the only value threaded across bricks is the
frame base `F`.

This is the front-level analogue of `X86Backend.EcJacAddMontMul.feMulFrameAt`
(`loadSlot4` operands → product → `storeSlot8` result) and of
`X86Backend.Ed25519PointKernel.feMulAt` (`slotOff`-based load/store around the
unchanged arithmetic). It reuses the doubling schedule and bricks of
`Secp256k1PointOpFront` unchanged; only the composition tiling differs.

## Frame provenance (provisional)

The frame `F` is a single `88`-cell (`704`-byte) memref that is the sole context
parameter. The three input coordinates are assumed pre-placed in slots `0` (`X`),
`1` (`Y`), `2` (`Z`); the three output coordinates end in the frame slots their
schedule outputs occupy. This isolates the lowering cost of the framed tiling —
the deployable kernel's ABI (separate `out` / `P` pointers plus either a scratch
argument or a stack-allocated local frame) is a later decision and does not
affect the lowering cost this module measures.

## Main results

* `jacDblBodyFramed` — the full 19-brick frame-relative doubling body as a
  `LowCT`, built only from existing `Secp256k1PointOpFront` combinators.
* `jacDblFrontComFramed` — `jacDblBodyFramed` pushed through
  `translateDialectControl` and capped with `ret F`, as a `Com catCryptDialect`.
* `jacDblLoweredFramed` — `jacDblFrontComFramed` lowered to `Com jasminDialect`
  via `cryptoDialectToJasminCom`; its `isSome` is the lowering-cost measurement.
-/

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront

/-! ## 1. Frame store and per-brick index binding -/

/-- Recombine field element `fe`'s eight 32-bit half-limbs into four `u64` and
    store them into the `fw`-byte pointer `arr` at cell offset `o .. o+3`. The
    array-name-general form of `Secp256k1PointOpFront.storeField` (which fixes
    the array name to `out`). -/
def storeFieldTo (fw : Nat) (arr : String) (o : Nat) (fe : String) : List LowCT :=
  (List.range 4).flatMap (fun j =>
    [ (.RScalarSetExpr s!"{fe}o{j}"
        (.SAdd (sv s!"{fe}h{2*j}") (.SShl (sv s!"{fe}h{2*j+1}") (.SLit 32))) : LowCT),
      (.RArrStore ⟨arr, .TBytes fw⟩ s!"ix{o + j}" ⟨s!"{fe}o{j}", .TU64⟩ : LowCT) ])

/-- Bind the constant cell-index scalars `ix{c}` for each `c` in `cells`. -/
def idxCells (cells : List Nat) : List LowCT :=
  cells.map (fun i => (.RScalarSetExpr s!"ix{i}" (.SLit i) : LowCT))

/-- The brick generator plus operand/output field-element names for a field op. -/
def brickFn :
    FOp → (String → List String → List String → List LowCT × List String)
        × String × String × String
  | .mul o a b => (feMulHalves, o, a, b)
  | .add o a b => (feAddHalves, o, a, b)
  | .sub o a b => (feSubHalves, o, a, b)

/-! ## 2. The frame-relative brick tiling -/

/-- Emit one field-op call `fop{idx}` frame-relative over frame `frame`
    (`fw` bytes wide, slots assigned by `slotOf`): rebind the constants and the
    twelve touched index scalars locally, `loadField` both operands from their
    frame slots into brick-local half-limbs, run the matching brick body, wire
    the eight results, and `storeFieldTo` them into the output slot. -/
def emitFOpFramed (fw : Nat) (frame : String) (slotOf : String → Nat)
    (idx : Nat) (op : FOp) : List LowCT :=
  let pfx := s!"fop{idx}"
  let (bf, o, a, b) := brickFn op
  let ca := (List.range 4).map (4 * slotOf a + ·)
  let cb := (List.range 4).map (4 * slotOf b + ·)
  let co := (List.range 4).map (4 * slotOf o + ·)
  let (bc, br) := bf (pfx ++ "C") (feH (pfx ++ "A")) (feH (pfx ++ "B"))
  idxCells (ca ++ cb ++ co) ++ constInit
    ++ loadField fw frame (4 * slotOf a) (pfx ++ "A")
    ++ loadField fw frame (4 * slotOf b) (pfx ++ "B")
    ++ bc
    ++ (List.range 8).map (fun k => (.RScalarSetExpr s!"{pfx}Oh{k}" (sv (br[k]!)) : LowCT))
    ++ storeFieldTo fw frame (4 * slotOf o) (pfx ++ "O")

/-! ## 3. Slot map and the full framed doubling body -/

/-- Field-element names in first-appearance order: the three inputs, then each
    doubling-schedule output. Slot `i` holds the `i`-th name (cells `4i .. 4i+3`). -/
def dblNames : List String :=
  ["X", "Y", "Z"] ++ jacDblSchedule.map (fun op => match op with
    | .mul o _ _ => o | .add o _ _ => o | .sub o _ _ => o)

/-- Frame slot index of a field-element name. -/
def slotOfDbl (s : String) : Nat := dblNames.idxOf s

/-- The 88-cell (704-byte) frame holds `dblNames.length = 22` field elements. -/
def frameCells : Nat := 88

/-- The full 19-brick frame-relative doubling body over the single frame `F`. -/
def jacDblBodyFramed : LowCT :=
  seqAll ((jacDblSchedule.mapIdx
    (fun i op => emitFOpFramed (8 * frameCells) "F" slotOfDbl i op)).flatten)

/-! ## 4. Front-compile and lower -/

/-- Single-frame context: one 88-cell memref. -/
def inΓF : Ctx := [.memref frameCells]

/-- Single-frame `VarMap`: the sole memref bound as `F`. -/
def inVMF : VarMap inΓF := VarMap.empty.bind (t := .memref frameCells) "F"

/-- Push `jacDblBodyFramed` through the direct control front, cap with `ret F`. -/
def jacDblFrontComFramed : Option (Com catCryptDialect inΓF (.memref frameCells)) :=
  match translateDialectControl inVMF jacDblBodyFramed with
  | some r =>
      match r.vm.lookup "F" with
      | some ⟨.memref 88, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- Lower the framed front dialect body to a `Com jasminDialect`. -/
def toJasminF (com : Option (Com catCryptDialect inΓF (.memref frameCells))) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match com with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- `jacDblBodyFramed` lowered to `Com jasminDialect`. The lowering-cost
    measurement is `jacDblLoweredFramed.isSome`. -/
def jacDblLoweredFramed := toJasminF jacDblFrontComFramed

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
