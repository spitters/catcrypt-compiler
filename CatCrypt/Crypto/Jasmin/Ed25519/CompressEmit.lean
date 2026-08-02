/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# `ed25519_compress` — VIR-extracted curve leaf

`ed25519_compress` (the operation `Edwards XYZT → 32-byte compressed`) is
currently a single `extern "C"` leaf primitive in the bedrock2/LowCT
pipeline (`BedrockEd25519Sign.lean` exposes it as
`ed25519_compress_call_correct`).  This module decomposes that leaf into
its arithmetic steps and emits the result as standalone MLIR (`func`
dialect, out-pointer C ABI) suitable for the
`mlir-opt → mlir-translate → clang` toolchain in `bench/dalek/`.

## Decomposition

Matches `compress_xyz` in
`ed25519_rustcmd/fe25519_portable.rs` (curve25519-jasmin-rs crate):

```
ed25519_compress(out, xyzt):
  X = xyzt[0..40]                          -- 40-byte slot
  Y = xyzt[40..80]
  Z = xyzt[80..120]
  Z⁻¹ = fe25519_invert(Z)                  -- Bernstein 254S + 11M chain
  Y_aff = Y * Z⁻¹                          -- fe25519_mul
  X_aff = X * Z⁻¹                          -- fe25519_mul
  out  = fe25519_pack_sign(Y_aff, X_aff)   -- to_bytes(Y_aff); bit 255 := LSB(X_aff)
```

We emit MLIR `func.call`s to **6 leaf primitives**:
* `xyzt_slot_x`, `xyzt_slot_y`, `xyzt_slot_z` — unpack 40-byte slots from
  the 200-byte XYZT buffer.
* `fe25519_invert_slot` — field inversion on the 40-byte slot encoding.
* `fe25519_mul_slot` — field multiply on 40-byte slot.
* `fe25519_pack_sign` — pack `Y_aff` to 32 bytes, OR'ing in the sign bit
  from `X_aff` (LSB of byte 0) into bit 255 of the output (MSB of byte 31).

These 6 leaves are implemented in a small Rust shim in `bench/dalek/`
(`src/compress_leaves.rs`) that delegates to dalek's verified field-element
code path.  In a future track, the VIR pipeline emits `fe25519_invert_slot`
itself as a 254-squaring + 11-multiply addition chain
(`FieldExpChain.bernsteinInvChain`); here it is a single leaf
so the **shape of the decomposition** is the artifact under test.

## Test plan

`bench/dalek/src/compress_difftest.rs` builds random `EdwardsPoint`s via
dalek, writes their 200-byte XYZT representation, and calls both
`dalek_compress` (reference) and `ed25519_compress` (this emitter).
Byte-for-byte equality is the correctness witness.

## Output

The emitter writes `bench/dalek/extracted/ed25519_compress.mlir`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Type printer and helpers (inlined, decoupled from MLIRExtract) -/

/-- Render a `TowerType` as an MLIR type name (out-pointer C ABI:
    every byte buffer becomes `memref<n x i8>`). -/
def renderTowerType : TowerType → String
  | .TBytes n => "memref<" ++ toString n ++ "xi8>"
  | _ => "!catcrypt.unsupported"

/-- Indent every line of `s` by `n` spaces. -/
def indentLines (n : Nat) (s : String) : String :=
  let pfx := String.replicate n ' '
  pfx ++ s.replace "\n" ("\n" ++ pfx)

/-! ## §2  Leaf-primitive table

Each leaf is `(name, [out_type, arg_types...])`.  Return type is always
`()` (void); out-pointer C ABI. -/

def compressLeafPrimitives : List (String × List TowerType) :=
  [ ("xyzt_slot_x",         [.TBytes 40, .TBytes 200])
  , ("xyzt_slot_y",         [.TBytes 40, .TBytes 200])
  , ("xyzt_slot_z",         [.TBytes 40, .TBytes 200])
  , ("fe25519_invert_slot", [.TBytes 40, .TBytes 40])
  , ("fe25519_mul_slot",    [.TBytes 40, .TBytes 40, .TBytes 40])
  , ("fe25519_pack_sign",   [.TBytes 32, .TBytes 40, .TBytes 40]) ]

/-! ## §3  Compress body as a `LowCT`

  Variable slots:
  * `xyzt` — 200-byte input (function argument)
  * `out`  — 32-byte output (function argument)
  * `x_slot`, `y_slot`, `z_slot` — 40-byte unpacked field elements
  * `z_inv`, `y_aff`, `x_aff` — 40-byte intermediates

  Call sequence (out-pointer ABI):
  ```
  xyzt_slot_x         (x_slot, xyzt)
  xyzt_slot_y         (y_slot, xyzt)
  xyzt_slot_z         (z_slot, xyzt)
  fe25519_invert_slot (z_inv,  z_slot)
  fe25519_mul_slot    (y_aff,  y_slot, z_inv)
  fe25519_mul_slot    (x_aff,  x_slot, z_inv)
  fe25519_pack_sign   (out,    y_aff,  x_aff)
  ```
-/

private def ξ_xyzt : String := "xyzt"
private def ξ_out  : String := "out"
private def ξ_xs   : String := "x_slot"
private def ξ_ys   : String := "y_slot"
private def ξ_zs   : String := "z_slot"
private def ξ_zinv : String := "z_inv"
private def ξ_yaff : String := "y_aff"
private def ξ_xaff : String := "x_aff"

/-- Helper: build a `Located` from slot name + tower type. -/
private def L (name : String) (t : TowerType) : Located := ⟨name, t⟩

/-- The `LowCT` body for `ed25519_compress`.  Mirrors `compress_xyz`'s
    7-call sequence verbatim. -/
def ed25519_compress_cmd : LowCT :=
  -- Allocate 6 intermediate 40-byte slots.
  .RLetZero ξ_xs (.TBytes 40) <|
  .RLetZero ξ_ys (.TBytes 40) <|
  .RLetZero ξ_zs (.TBytes 40) <|
  .RLetZero ξ_zinv (.TBytes 40) <|
  .RLetZero ξ_yaff (.TBytes 40) <|
  .RLetZero ξ_xaff (.TBytes 40) <|
  -- Unpack X, Y, Z slots.
  .RSeq (.RCall "xyzt_slot_x" (L ξ_xs (.TBytes 40))
            [L ξ_xyzt (.TBytes 200)]) <|
  .RSeq (.RCall "xyzt_slot_y" (L ξ_ys (.TBytes 40))
            [L ξ_xyzt (.TBytes 200)]) <|
  .RSeq (.RCall "xyzt_slot_z" (L ξ_zs (.TBytes 40))
            [L ξ_xyzt (.TBytes 200)]) <|
  -- Z⁻¹.
  .RSeq (.RCall "fe25519_invert_slot" (L ξ_zinv (.TBytes 40))
            [L ξ_zs (.TBytes 40)]) <|
  -- Y_aff = Y * Z⁻¹, X_aff = X * Z⁻¹.
  .RSeq (.RCall "fe25519_mul_slot" (L ξ_yaff (.TBytes 40))
            [L ξ_ys (.TBytes 40), L ξ_zinv (.TBytes 40)]) <|
  .RSeq (.RCall "fe25519_mul_slot" (L ξ_xaff (.TBytes 40))
            [L ξ_xs (.TBytes 40), L ξ_zinv (.TBytes 40)]) <|
  -- Pack Y_aff into out, OR-in sign of X_aff into bit 255.
  .RCall "fe25519_pack_sign" (L ξ_out (.TBytes 32))
    [L ξ_yaff (.TBytes 40), L ξ_xaff (.TBytes 40)]

/-! ## §4  String emitter (out-pointer C ABI)

Locally defined so this file does NOT depend on `MLIRExtract.lean` —
which has unrelated build breaks during the ongoing LowCT refactor. -/

private def emitCall (name : String) (dest : Located) (args : List Located) : String :=
  let argRefs := args.map (fun a => "%" ++ a.locVar)
  let argTys  := args.map (fun a => renderTowerType a.locDst)
  let allRefs := ("%" ++ dest.locVar) :: argRefs
  let allTys  := renderTowerType dest.locDst :: argTys
  let refStr := String.intercalate ", " allRefs
  let tyStr  := String.intercalate ", " allTys
  s!"func.call @{name}({refStr}) : ({tyStr}) -> ()"

private partial def emitBody : LowCT → List String
  | .RSkip        => []
  | .RSeq c1 c2   => emitBody c1 ++ emitBody c2
  | .RBlock body  => emitBody body
  | .RLetZero x t body =>
      ("%" ++ x ++ " = memref.alloca() : " ++ renderTowerType t) :: emitBody body
  | .RCall name dest args => [emitCall name dest args]
  | _ => ["// unsupported"]

/-- Render an extern declaration `func.func private @name(args)`. -/
private def externLine (name : String) (params : List TowerType) : String :=
  let paramStr := String.intercalate ", " (params.map renderTowerType)
  s!"  func.func private @{name}({paramStr})"

/-- Render the `ed25519_compress` MLIR module (func dialect,
    out-pointer C ABI). -/
def emitEd25519Compress : String :=
  let externs := String.intercalate "\n"
    (compressLeafPrimitives.map fun (n, ps) => externLine n ps)
  let bodyLines := emitBody ed25519_compress_cmd
  let bodyStr := indentLines 4 (String.intercalate "\n" bodyLines)
  "module {\n" ++
  externs ++ "\n" ++
  "  func.func @ed25519_compress(%out: memref<32xi8>, %xyzt: memref<200xi8>) {\n" ++
  bodyStr ++ "\n" ++
  "    func.return\n" ++
  "  }\n" ++
  "}\n"

end CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit

/-- `lake env lean --run` entrypoint.  Emits the MLIR module to stdout. -/
private def main (_args : List String) : IO Unit := do
  IO.println CatCrypt.Crypto.Jasmin.Ed25519.CompressEmit.emitEd25519Compress
