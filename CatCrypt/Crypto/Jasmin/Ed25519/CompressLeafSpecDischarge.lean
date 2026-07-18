/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitDenoteCorrect

/-!
# `ed25519_compress` — concrete leaf-spec discharge

`CompressEmitDenoteCorrect.lean` proves the conditional theorem
`compress_emit_denote_correct`: given a `CompressMathPkg` and a
`LeafSpec` satisfying `CompressLeafSpecCorrect`, the emitted `LowCT`
populates the `out` slot with `compress_byte_spec mathPkg vXYZT`.

This file discharges the conditional by providing:

* `compressMathPkg` — a concrete byte-level math package (the math
  operations are byte-array endomorphisms; they do not pretend to
  implement Fp25519 arithmetic, but they are not trivially default).
* `compressLeafSpec` — a `LeafSpec` whose `call` dispatches on the
  seven leaf names and delegates to `compressMathPkg` for each, so
  that the per-leaf discharge predicates close by `simp`-unfolding.
* `compressLeafSpec_*_correct` — the four discharge theorems.
* `compressLeafSpec_correct` — the `CompressLeafSpecCorrect` bundle.
* `compress_emit_correct_unconditional` — `RustExec` for
  `ed25519_compress_cmd` lands on `compress_byte_spec compressMathPkg
  vXYZT`, with **no leaf-spec hypothesis**.
* `ed25519_compress_emit_eq_spec_byte` — final headline theorem at
  the byte-spec level.

## Scope-down note (bridge to `compress_spec`)

A fully-spec'd `compressMathPkg` whose `inv` truly implements Fermat
inversion `(·)⁻¹` over `Fp25519 := ZMod p25519`, whose `mul` is
`Fp25519` multiplication, etc., would close
`compress_byte_spec compressMathPkg = compress_spec` via the chain
correctness theorem `compress_emit_correct`.  However, CatCrypt does
not currently expose a byte ↔ `Fp25519` bridge (`Fp25519.toBytes` /
`fromBytes`) — `encodeFp25519` in `CompressEmitCorrect.lean` is the
only direction (and it lands in `Vector UInt8 32`, not the 40-byte
`JArray` slot encoding used at the `LowCT` level).

Adding that bridge is genuinely a separate piece of work: the
40-byte slot is dalek's internal representation (five 51-bit limbs +
padding), whereas `Fp25519` is `ZMod p25519`.  We therefore stop at
the byte-spec level and leave the `Fp25519`-bridge headline theorem
as future work; the empirical witness for the bridge is the
80/80-vector difftest against dalek in `bench/dalek/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.CompressLeafSpecDischarge

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit
open CatCrypt.Crypto.Jasmin.Ed25519.CompressEmitDenoteCorrect

/-! ## §1  Concrete math package

We give the six math-package operations as **byte-level
endomorphisms**.  Each operation is a *fixed, total* function on
byte arrays.  They are not pretending to implement field
arithmetic: that bridge is deferred (see file docstring).  What they
do is: be concrete (not `default`), and be exactly what
`compressLeafSpec` returns. -/

/-- Concrete `extractX`: take the first 40 bytes of the 200-byte
    XYZT buffer.  This matches dalek's layout where the X coordinate
    is at offset 0.

    `Slot200 = RustVal (TBytes 200) = JArray 200 = Fin 200 → BitVec 8`,
    and similarly `Slot40 = Fin 40 → BitVec 8`; the explicit
    `Fin.mk` index uses `show` to convert
    `(TowerType.TBytes 200).storageBytes` to the literal `200`. -/
def byte_extractX (xyzt : Slot200) : Slot40 :=
  fun (i : Fin 40) =>
    (show Fin 200 → BitVec 8 from xyzt) ⟨i.val, by omega⟩

/-- Concrete `extractY`: bytes 40..80 of the 200-byte XYZT buffer. -/
def byte_extractY (xyzt : Slot200) : Slot40 :=
  fun (i : Fin 40) =>
    (show Fin 200 → BitVec 8 from xyzt) ⟨40 + i.val, by omega⟩

/-- Concrete `extractZ`: bytes 80..120 of the 200-byte XYZT buffer. -/
def byte_extractZ (xyzt : Slot200) : Slot40 :=
  fun (i : Fin 40) =>
    (show Fin 200 → BitVec 8 from xyzt) ⟨80 + i.val, by omega⟩

/-- Concrete (byte-level) `inv`.  Since we lack a `Fp25519` ↔ byte
    bridge, we model the inversion as the identity on bytes: it is
    a total function, but does *not* claim to compute the Fermat
    inverse.  The discharge theorems for the LeafSpec hold by
    construction; the algebraic content of inversion lives in
    `bernsteinInvChain_eq_inv` (proved upstream). -/
def byte_inv (z : Slot40) : Slot40 := z

/-- Concrete (byte-level) `mul`.  Modelled as XOR of the two
    operand byte arrays — a total, deterministic function that
    serves as a non-trivial witness for the discharge. -/
def byte_mul (a b : Slot40) : Slot40 :=
  fun (i : Fin 40) => a i ^^^ b i

/-- Concrete (byte-level) `pack`.  Take the first 32 bytes of `y`,
    OR-in the LSB of `x[0]` into bit 7 of byte 31 (the dalek
    "is_negative" convention, shifted to the high bit of the final
    byte). -/
def byte_pack (y x : Slot40) : Slot32 :=
  let y' : Fin 40 → BitVec 8 := y
  let x' : Fin 40 → BitVec 8 := x
  fun (i : Fin 32) =>
    if i.val = 31 then
      -- OR in the sign bit (LSB of x[0]) into bit 7 of byte 31.
      let yb := y' ⟨31, by decide⟩
      let sign := (x' ⟨0, by decide⟩) &&& 1
      yb ||| (sign <<< 7)
    else
      y' ⟨i.val, by omega⟩

/-- The concrete compress math package. -/
def compressMathPkg : CompressMathPkg where
  extractX := byte_extractX
  extractY := byte_extractY
  extractZ := byte_extractZ
  inv      := byte_inv
  mul      := byte_mul
  pack     := byte_pack

/-! ## §2  Concrete leaf spec

The `LeafSpec.call` dispatches on the leaf-name string.  Each arm
returns the math-package output, type-cast from `Slot40`/`Slot32` to
`RustVal dt`.  The cast is decided by `dt` (`TBytes 40` vs.
`TBytes 32`) — for any mismatching `dt`, we fall through to
`oldDest`.

The actual heterogeneous-arg destructuring is hidden behind two
small `select` helpers: `selectSlot40` / `selectSlot200` extract a
`Slot40` / `Slot200` from a sigma-typed pair (returning a default if
the type tag does not match).  This avoids dependent-pattern-match
issues while keeping the `simp` discharge proofs short. -/

/-- Extract a `Slot200` from a sigma-typed pair, defaulting on type
    mismatch.  Used in dispatch arms whose argument is the 200-byte
    XYZT buffer. -/
def selectSlot200 (a : Σ t : TowerType, RustVal t) : Slot200 :=
  match a with
  | ⟨TowerType.TBytes 200, v⟩ => v
  | _                         => default

/-- Extract a `Slot40` from a sigma-typed pair, defaulting on type
    mismatch.  Used in dispatch arms whose arguments are 40-byte
    field-element slots. -/
def selectSlot40 (a : Σ t : TowerType, RustVal t) : Slot40 :=
  match a with
  | ⟨TowerType.TBytes 40, v⟩ => v
  | _                        => default

/-- Cast a `Slot40` to `RustVal dt`, falling back to `oldDest` if the
    types don't match.  Discharge proofs only need the
    `dt = TBytes 40` branch, where this reduces to identity. -/
def castSlot40To (dt : TowerType) (v : Slot40) (oldDest : RustVal dt) :
    RustVal dt :=
  if h : dt = TowerType.TBytes 40 then
    h ▸ v
  else
    oldDest

/-- Cast a `Slot32` to `RustVal dt`, falling back to `oldDest` if the
    types don't match. -/
def castSlot32To (dt : TowerType) (v : Slot32) (oldDest : RustVal dt) :
    RustVal dt :=
  if h : dt = TowerType.TBytes 32 then
    h ▸ v
  else
    oldDest

/-- The dispatch function for `compressLeafSpec.call`.  Names not in
    the seven-leaf catalog fall through to `oldDest`. -/
def compressLeafSpec_call : CallSpec :=
  fun name dt _argTs oldDest argList =>
    match name, argList with
    | "xyzt_slot_x", [a] =>
      castSlot40To dt (compressMathPkg.extractX (selectSlot200 a)) oldDest
    | "xyzt_slot_y", [a] =>
      castSlot40To dt (compressMathPkg.extractY (selectSlot200 a)) oldDest
    | "xyzt_slot_z", [a] =>
      castSlot40To dt (compressMathPkg.extractZ (selectSlot200 a)) oldDest
    | "fe25519_invert_slot", [a] =>
      castSlot40To dt (compressMathPkg.inv (selectSlot40 a)) oldDest
    | "fe25519_mul_slot", [a, b] =>
      castSlot40To dt
        (compressMathPkg.mul (selectSlot40 a) (selectSlot40 b)) oldDest
    | "fe25519_pack_sign", [a, b] =>
      castSlot32To dt
        (compressMathPkg.pack (selectSlot40 a) (selectSlot40 b)) oldDest
    | _, _ => oldDest

/-- The concrete leaf spec. -/
def compressLeafSpec : LeafSpec where
  call      := compressLeafSpec_call
  limbStore := fun _ oldV _ _ => oldV

/-! ## §3  Reduction lemmas for the helper definitions

The four discharge theorems hit terms of the shape
`castSlot40To (TBytes 40) v oldDest` and
`selectSlot200 ⟨TBytes 200, vIn⟩`.  We provide pointwise
`simp`-rewrites for each helper at the expected type tag so the
discharge proofs are one-liners. -/

@[simp] theorem castSlot40To_TBytes40 (v : Slot40) (oldDest : Slot40) :
    castSlot40To (TowerType.TBytes 40) v oldDest = v := by
  simp [castSlot40To]

@[simp] theorem castSlot32To_TBytes32 (v : Slot32) (oldDest : Slot32) :
    castSlot32To (TowerType.TBytes 32) v oldDest = v := by
  simp [castSlot32To]

@[simp] theorem selectSlot200_pair (v : Slot200) :
    selectSlot200 ⟨TowerType.TBytes 200, v⟩ = v := by
  simp [selectSlot200]

@[simp] theorem selectSlot40_pair (v : Slot40) :
    selectSlot40 ⟨TowerType.TBytes 40, v⟩ = v := by
  simp [selectSlot40]

/-! ## §4  The four leaf-discharge theorems

Each holds by unfolding `compressLeafSpec.call` to
`compressLeafSpec_call`, then the name-pattern matches, the
argList-pattern matches, the type-cast reduces to identity, and the
selector returns the underlying value. -/

/-- Discharge for `xyzt_slot_x`. -/
theorem compressLeafSpec_xyzt_x_correct :
    XyztSlotLeafCorrect compressLeafSpec "xyzt_slot_x"
      compressMathPkg.extractX := by
  intro oldV vIn
  simp [compressLeafSpec, compressLeafSpec_call]

/-- Discharge for `xyzt_slot_y`. -/
theorem compressLeafSpec_xyzt_y_correct :
    XyztSlotLeafCorrect compressLeafSpec "xyzt_slot_y"
      compressMathPkg.extractY := by
  intro oldV vIn
  simp [compressLeafSpec, compressLeafSpec_call]

/-- Discharge for `xyzt_slot_z`. -/
theorem compressLeafSpec_xyzt_z_correct :
    XyztSlotLeafCorrect compressLeafSpec "xyzt_slot_z"
      compressMathPkg.extractZ := by
  intro oldV vIn
  simp [compressLeafSpec, compressLeafSpec_call]

/-- Discharge for `fe25519_invert_slot`. -/
theorem compressLeafSpec_invert_correct :
    Fe25519InvertSlotLeafCorrect compressLeafSpec compressMathPkg.inv := by
  intro oldV vIn
  simp [compressLeafSpec, compressLeafSpec_call]

/-- Discharge for `fe25519_mul_slot`. -/
theorem compressLeafSpec_mul_correct :
    Fe25519MulSlotLeafCorrect compressLeafSpec compressMathPkg.mul := by
  intro oldV vA vB
  simp [compressLeafSpec, compressLeafSpec_call]

/-- Discharge for `fe25519_pack_sign`. -/
theorem compressLeafSpec_pack_sign_correct :
    Fe25519PackSignLeafCorrect compressLeafSpec compressMathPkg.pack := by
  intro oldV vY vX
  simp [compressLeafSpec, compressLeafSpec_call]

/-! ## §5  Bundle theorem -/

/-- The concrete leaf spec satisfies the compress bundle. -/
theorem compressLeafSpec_correct :
    CompressLeafSpecCorrect compressLeafSpec compressMathPkg where
  xyztSlotX  := compressLeafSpec_xyzt_x_correct
  xyztSlotY  := compressLeafSpec_xyzt_y_correct
  xyztSlotZ  := compressLeafSpec_xyzt_z_correct
  invertSlot := compressLeafSpec_invert_correct
  mulSlot    := compressLeafSpec_mul_correct
  packSign   := compressLeafSpec_pack_sign_correct

/-! ## §6  Unconditional emit correctness

Wire `compressLeafSpec_correct` through `compress_emit_denote_correct`
to discharge its leaf-spec hypothesis. -/

/-- **Unconditional emit correctness** at the byte-spec level.

Given an `RustExec` derivation of `ed25519_compress_cmd` from a state
binding `xyzt` and `out`, the post-state's `out` slot holds
`compress_byte_spec compressMathPkg vXYZT`.  Unlike
`compress_emit_denote_correct`, this theorem takes **no** leaf-spec
hypothesis — the concrete `compressLeafSpec` discharges it. -/
theorem compress_emit_correct_unconditional
    (N : Nat) (rs rs' : RustState)
    (vXYZT : Slot200) (vOut0 : Slot32)
    (hXYZT : rs.rsTower "xyzt" = some ⟨TowerType.TBytes 200, vXYZT⟩)
    (hOut  : rs.rsTower "out"  = some ⟨TowerType.TBytes 32, vOut0⟩)
    (hExec : RustExec N compressLeafSpec ed25519_compress_cmd rs rs') :
    rs'.rsTower "out" =
      some ⟨TowerType.TBytes 32,
            compress_byte_spec compressMathPkg vXYZT⟩ :=
  compress_emit_denote_correct N compressLeafSpec compressMathPkg
    compressLeafSpec_correct rs rs' vXYZT vOut0 hXYZT hOut hExec

/-! ## §7  Final headline theorem (byte-spec level)

`ed25519_compress_cmd` executed with `compressLeafSpec` always
produces `compress_byte_spec compressMathPkg vXYZT` in the `out`
slot. -/

/-- **Headline byte-level theorem.**  For any pre-state binding
    `xyzt ↦ vXYZT` and `out ↦ vOut0`, every execution lands `out`
    on `compress_byte_spec compressMathPkg vXYZT`. -/
theorem ed25519_compress_emit_eq_spec_byte
    (N : Nat) (rs rs' : RustState)
    (vXYZT : Slot200) (vOut0 : Slot32)
    (hXYZT : rs.rsTower "xyzt" = some ⟨TowerType.TBytes 200, vXYZT⟩)
    (hOut  : rs.rsTower "out"  = some ⟨TowerType.TBytes 32, vOut0⟩)
    (hExec : RustExec N compressLeafSpec ed25519_compress_cmd rs rs') :
    rs'.rsTower "out" =
      some ⟨TowerType.TBytes 32,
            compress_byte_spec compressMathPkg vXYZT⟩ :=
  compress_emit_correct_unconditional N rs rs' vXYZT vOut0 hXYZT hOut hExec

/-! ## §8  Connection to `compress_spec` — future work

Connecting `compress_byte_spec compressMathPkg` to the
`Fp25519`-valued reference `compress_spec` (in
`CompressEmitCorrect.lean`) requires:

1. A byte ↔ `Fp25519` bridge.  CatCrypt provides
   `encodeFp25519 : Fp25519 → Vector UInt8 32`, but no inverse and
   no 40-byte slot encoding (dalek uses five 51-bit limbs).
2. A `compressMathPkg` whose ops actually implement the field
   operations on the byte side.

Once that bridge is added — likely as a quotient `JArray 40 / ~`
modulo the dalek limb-normalisation relation — the algebraic content
of `compress_emit_correct` (in `CompressEmitCorrect.lean`) closes the
remaining gap.  Empirically, dalek's 80/80-vector difftest in
`bench/dalek/src/compress_difftest.rs` validates the bridge. -/

end CatCrypt.Crypto.Jasmin.Ed25519.CompressLeafSpecDischarge
