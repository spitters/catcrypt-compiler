/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

/-!
# `Com → Tile → NVIDIA Tile IR`: the emit (Phase 3 of the spike)

This emits a `TileModel` tile program as **NVIDIA `cuda_tile` MLIR dialect** text
(`github.com/NVIDIA/cuda-tile`, `Dialect/CudaTile/IR/Ops.td`/`Types.td`). It
completes the spike: `TileModel` fixes the *semantics* (`bbMulTile_denote`); this
file *emits* the same tile program into the real dialect, so the same field
arithmetic that the semantics proves correct is written in the IR NVIDIA's
`cuda-tile` compiler lowers to PTX/SASS.

## The dialect mapping (from `Ops.td` / `Types.td`)

| `TileModel.TileOp` | `cuda_tile` op (mnemonic) | assembly |
|---|---|---|
| `add` | `cuda_tile.addi` | `%r = cuda_tile.addi %a, %b : !cuda_tile.tile<8xi64>` |
| `sub` | `cuda_tile.subi` | `%r = cuda_tile.subi %a, %b : …` |
| `mul` | `cuda_tile.muli` | `%r = cuda_tile.muli %a, %b : …` |
| `and` | `cuda_tile.andi` | `%r = cuda_tile.andi %a, %b : …` |
| `shr` | `cuda_tile.shri`  | `%s = cuda_tile.constant …; %r = cuda_tile.shri %a, %s : …` |
| `const` | `cuda_tile.constant` | `%r = cuda_tile.constant dense<N> : …` |
| `permxv` | `cuda_tile.permute` | `%r = cuda_tile.permute %a, %idx : …` (index operand second) |
| `bcast` | `cuda_tile.broadcast` | `%r = cuda_tile.broadcast %a {lane = N} : …` |
| `hadd` | `cuda_tile.reduce` | `%r = cuda_tile.reduce %a {op = "add"} : …` |

The cross-tile (lane-moving) ops `permute`/`broadcast`/`reduce` are the
`cuda_tile` mnemonics an NTT butterfly / Poseidon2 MDS shuffle lowers to (named
in `Ops.td` alongside the elementwise arithmetic).

The tile type is `!cuda_tile.tile<8xi64>` (`Types.td`: shape × element, power-of-two
dims; our 8 BabyBear lanes as `i64` for the Barrett intermediates).

## Scope (honest)

* **Emits** the `bbMul` tile as `cuda_tile` MLIR, grounded in the real dialect's
  op mnemonics + assembly format (`addi` = `$lhs `,` $rhs attr-dict `:` type`).
* **Structural pins** (`native_decide`) that the emitted text carries the
  `cuda_tile` ops + tile type.
* **Not tool-validated here:** validating the text through NVIDIA's `cuda-tile`
  `mlir-opt` (and lowering to PTX) needs that C++/MLIR toolchain, which is not on
  this box — the analogue of "no GPU to execute on." The emit + the `TileModel`
  denotation are what this increment delivers; toolchain round-trip is the next
  step once `cuda-tile` is built.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

set_option autoImplicit false

/-- The `cuda_tile` tile type for the spike kernels: 8 `i64` lanes. -/
def tileTy : String := "!cuda_tile.tile<8xi64>"

/-! ## 1. SSA-renaming emit state

`cuda_tile` MLIR is SSA; the tile program reuses names (`x`/`q`/`o`/`m`). Thread a
name → current `%vNN` map + a fresh counter (the `ComToMLIR`/`ComToNvptx` pattern). -/

structure St where
  map : List (String × String)
  ctr : Nat
  lines : List String

def St.opnd (s : St) (nm : String) : String := (s.map.lookup nm).getD "%undef"
def St.bind (s : St) (nm v : String) : St := { s with map := (nm, v) :: s.map }
def St.fresh (s : St) : String × St := ("%v" ++ toString s.ctr, { s with ctr := s.ctr + 1 })
def St.emit (s : St) (line : String) : St := { s with lines := line :: s.lines }

/-- Emit one `TileOp` as `cuda_tile` MLIR, threading SSA state. -/
def emitTileOp (s : St) : TileOp → St
  | .const dst n =>
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = cuda_tile.constant dense<" ++ toString n
                        ++ "> : " ++ tileTy)
      s.bind dst v
  | .add dst a b => binOp s "addi" dst a b
  | .sub dst a b => binOp s "subi" dst a b
  | .mul dst a b => binOp s "muli" dst a b
  | .and dst a b => binOp s "andi" dst a b
  | .orr dst a b => binOp s "ori" dst a b
  | .xorr dst a b => binOp s "xori" dst a b
  | .shll dst a b => binOp s "shli" dst a b
  | .shrr dst a b => binOp s "shrui" dst a b
  | .andn dst a b =>
      -- no direct `andn`: emit (~a) via `xori` with the all-ones tile, then `andi`
      let (ones, s) := s.fresh
      let s := s.emit ("  " ++ ones ++ " = cuda_tile.constant dense<-1> : " ++ tileTy)
      let (na, s) := s.fresh
      let s := s.emit ("  " ++ na ++ " = cuda_tile.xori " ++ s.opnd a ++ ", " ++ ones
                        ++ " : " ++ tileTy)
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = cuda_tile.andi " ++ na ++ ", " ++ s.opnd b
                        ++ " : " ++ tileTy)
      s.bind dst v
  | .shr dst a imm =>
      -- the shift amount is a tile operand: materialise it as a constant tile
      let (sh, s) := s.fresh
      let s := s.emit ("  " ++ sh ++ " = cuda_tile.constant dense<" ++ toString imm
                        ++ "> : " ++ tileTy)
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = cuda_tile.shri " ++ s.opnd a ++ ", " ++ sh
                        ++ " : " ++ tileTy)
      s.bind dst v
  | .mulhs dst a b => binOp s "mulhi" dst a b
  | .permxv dst idx a =>
      -- data-dependent gather: `cuda_tile.permute %a, %idx` (index operand second)
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = cuda_tile.permute " ++ s.opnd a ++ ", "
                        ++ s.opnd idx ++ " : " ++ tileTy)
      s.bind dst v
  | .bcast dst a lane =>
      -- splat one lane across the tile: `cuda_tile.broadcast %a {lane = N}`
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = cuda_tile.broadcast " ++ s.opnd a
                        ++ " {lane = " ++ toString lane ++ "} : " ++ tileTy)
      s.bind dst v
  | .hadd dst a =>
      -- horizontal add-reduce broadcast: `cuda_tile.reduce %a {op = "add"}`
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = cuda_tile.reduce " ++ s.opnd a
                        ++ " {op = \"add\"} : " ++ tileTy)
      s.bind dst v
where
  binOp (s : St) (mn dst a b : String) : St :=
    let (v, s) := s.fresh
    let s := s.emit ("  " ++ v ++ " = cuda_tile." ++ mn ++ " " ++ s.opnd a ++ ", "
                      ++ s.opnd b ++ " : " ++ tileTy)
    s.bind dst v

/-- Emit a 2-input / 1-output tile program (`resName` the result tile) as a
    `cuda_tile` MLIR function. -/
def emitTileFunc (name : String) (body : List TileOp) (resName : String) : String :=
  let header :=
    [ "func.func @" ++ name ++ "(%a: " ++ tileTy ++ ", %b: " ++ tileTy
        ++ ") -> " ++ tileTy ++ " {" ]
  let s0 : St := { map := [("a", "%a"), ("b", "%b")], ctr := 0, lines := [] }
  let s := body.foldl emitTileOp s0
  let footer := [ "  return " ++ s.opnd resName ++ " : " ++ tileTy, "}" ]
  String.intercalate "\n" (header ++ s.lines.reverse ++ footer) ++ "\n"

/-- The BabyBear `bbMul` tile emitted as `cuda_tile` MLIR (the emitted artifact). -/
def bbMulTileIR : String := emitTileFunc "bb_mul_tile" bbMulTile "o"

/-! ## 2. Structural pins (the emitted dialect text) -/

/-- A substring test. -/
def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The emit carries the `cuda_tile` tile type and the entry function. -/
theorem ir_has_func_and_type :
    contains bbMulTileIR "func.func @bb_mul_tile" = true
      ∧ contains bbMulTileIR "!cuda_tile.tile<8xi64>" = true := by
  native_decide

/-- The Barrett field arithmetic is present as `cuda_tile` ops. -/
theorem ir_has_field_ops :
    contains bbMulTileIR "cuda_tile.muli" = true
      ∧ contains bbMulTileIR "cuda_tile.shri" = true
      ∧ contains bbMulTileIR "cuda_tile.subi" = true
      ∧ contains bbMulTileIR "cuda_tile.constant dense<2290649223>" = true := by
  native_decide

/-! ## 3. Emit driver -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/gpu_compare/gen"
  IO.FS.writeFile "bench/gpu_compare/gen/bb_mul_tile.cuda_tile.mlir" bbMulTileIR
  IO.println "wrote bench/gpu_compare/gen/bb_mul_tile.cuda_tile.mlir (BabyBear bbMul, cuda_tile dialect)"
  IO.println s!"  {bbMulTile.length} tile ops -> cuda_tile MLIR (tile<8xi64>)"

-- #eval main

end CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR
