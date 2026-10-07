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
# `Com → Tile → NVIDIA Tile IR`: the emit

This emits a `TileModel` tile program as text of the NVIDIA CUDA Tile IR
(`cuda_tile` MLIR dialect; specification
https://docs.nvidia.com/cuda/tile-ir/latest/sections/operations.html, textual
syntax from `Dialect/CudaTile/IR/Ops.td` and the tests of
`github.com/NVIDIA/cuda-tile`). `CudaTileSemantics` gives the emitted fragment an
AST, a parser and a semantics, and proves that the text computes what
`TileModel.runTileBlock` computes.

## The kernel

`emitTileFuncAt n w name body res` prints a module `@name` holding one
`cuda_tile.entry @name` kernel. Entry arguments are scalars, so the input and
output tiles are passed as pointers `%pa`, `%pb`, `%pr` of type
`!cuda_tile.tile<ptr<i w>>`: the kernel builds the pointer tiles `p + i` for
`i < n` (`iota`, `reshape`, `broadcast`, `offset`), loads the tiles `%a`, `%b`
(`load_ptr_tko weak`), runs the body at tile type `!cuda_tile.tile<n x i w>`, and
stores the result register (`store_ptr_tko weak`) before `cuda_tile.return`.

## The op mapping

| `TileModel.TileOp` | `cuda_tile` text |
|---|---|
| `const k` | `constant <i w: k>` |
| `add`, `sub`, `mul` | `addi`, `subi`, `muli` |
| `and`, `orr`, `xorr` | `andi`, `ori`, `xori` |
| `shll` | `shli` |
| `shrr` | `shri … unsigned` |
| `shr k` | `constant <i w: k>`, then `shri … unsigned` |
| `andn` | `constant <i w: -1>`, `xori`, `andi` |
| `mulhs` | `mulhii` on the unsigned values, corrected by `shri … signed` by `w - 1`, `andi` and two `subi` |
| `permxv`, `bcast`, `hadd` | none |

The lane-moving ops `permxv`, `bcast`, `hadd` have no `cuda_tile` form here:
`emitTileOp` prints no line for them and binds the destination to `%undef`, and
`emitTileFunc?` returns `none` for a block that contains one.

The emitted text is not checked by the `cuda-tile` toolchain in this package.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

set_option autoImplicit false

/-! ## 1. Types and line forms -/

/-- The tile type `!cuda_tile.tile<n x i w>`. -/
def tileTyAt (n w : Nat) : String := "!cuda_tile.tile<" ++ toString n ++ "xi" ++ toString w ++ ">"

/-- The tile type of the BabyBear kernels, `!cuda_tile.tile<8xi64>`. -/
def tileTy : String := tileTyAt 8 64

/-- The scalar pointer type `!cuda_tile.tile<ptr<i w>>` of a kernel argument. -/
def ptrTyAt (w : Nat) : String := "!cuda_tile.tile<ptr<i" ++ toString w ++ ">>"

/-- The pointer tile type `!cuda_tile.tile<m x ptr<i w>>`. -/
def ptrTileTyAt (m w : Nat) : String :=
  "!cuda_tile.tile<" ++ toString m ++ "xptr<i" ++ toString w ++ ">>"

/-- The index tile type `!cuda_tile.tile<n x i32>` of the `iota` result. -/
def idxTyAt (n : Nat) : String := "!cuda_tile.tile<" ++ toString n ++ "xi32>"

/-- The line `r = cuda_tile.constant <i w: k> : ty`. -/
def constLine (n w : Nat) (r : String) (k : Int) : String :=
  "    " ++ r ++ " = cuda_tile." ++ "constant" ++ " <i" ++ toString w ++ ": " ++ toString k
    ++ "> : " ++ tileTyAt n w

/-- The line `r = cuda_tile.<mn> x, y : ty`. -/
def binLine (n w : Nat) (mn r x y : String) : String :=
  "    " ++ r ++ " = cuda_tile." ++ mn ++ " " ++ x ++ ", " ++ y ++ " : " ++ tileTyAt n w

/-- The line `r = cuda_tile.shri x, y <sgn> : ty`, with `sgn` one of `signed`,
    `unsigned`. -/
def shriLine (n w : Nat) (sgn r x y : String) : String :=
  "    " ++ r ++ " = cuda_tile." ++ "shri" ++ " " ++ x ++ ", " ++ y ++ " " ++ sgn ++ " : "
    ++ tileTyAt n w

/-! ## 2. SSA-renaming emit state

`cuda_tile` MLIR is SSA; the tile program reuses register names. The state threads
a name → current `%vNN` map and a fresh counter. -/

structure St where
  map : List (String × String)
  ctr : Nat
  lines : List String

def St.opnd (s : St) (nm : String) : String := (s.map.lookup nm).getD "%undef"
def St.bind (s : St) (nm v : String) : St := { s with map := (nm, v) :: s.map }
def St.fresh (s : St) : String × St := ("%v" ++ toString s.ctr, { s with ctr := s.ctr + 1 })
def St.emit (s : St) (line : String) : St := { s with lines := line :: s.lines }

/-- Emit one `TileOp` at tile type `tileTyAt n w`, threading SSA state. The
    lane-moving ops, the immediate `shl`/`sar`/`rotl`/`rotr` and `mulhu` print
    nothing and bind their destination to `%undef`. -/
def emitTileOp (n w : Nat) (s : St) : TileOp → St
  | .const dst k =>
      let (v, s) := s.fresh
      (s.emit (constLine n w v k)).bind dst v
  | .add dst a b => binOp s "addi" dst a b
  | .sub dst a b => binOp s "subi" dst a b
  | .mul dst a b => binOp s "muli" dst a b
  | .and dst a b => binOp s "andi" dst a b
  | .orr dst a b => binOp s "ori" dst a b
  | .xorr dst a b => binOp s "xori" dst a b
  | .shll dst a b => binOp s "shli" dst a b
  | .shrr dst a b =>
      let (v, s) := s.fresh
      (s.emit (shriLine n w "unsigned" v (s.opnd a) (s.opnd b))).bind dst v
  | .andn dst a b =>
      let (ones, s) := s.fresh
      let s := s.emit (constLine n w ones (-1))
      let (na, s) := s.fresh
      let s := s.emit (binLine n w "xori" na (s.opnd a) ones)
      let (v, s) := s.fresh
      (s.emit (binLine n w "andi" v na (s.opnd b))).bind dst v
  | .shr dst a imm =>
      let (sh, s) := s.fresh
      let s := s.emit (constLine n w sh imm)
      let (v, s) := s.fresh
      (s.emit (shriLine n w "unsigned" v (s.opnd a) sh)).bind dst v
  | .mulhs dst a b =>
      -- signed high half = unsigned high half - (a < 0 ? b : 0) - (b < 0 ? a : 0)
      let (c, s) := s.fresh
      let s := s.emit (constLine n w c (w - 1 : Nat))
      let (sa, s) := s.fresh
      let s := s.emit (shriLine n w "signed" sa (s.opnd a) c)
      let (sb, s) := s.fresh
      let s := s.emit (shriLine n w "signed" sb (s.opnd b) c)
      let (h, s) := s.fresh
      let s := s.emit (binLine n w "mulhii" h (s.opnd a) (s.opnd b))
      let (ca, s) := s.fresh
      let s := s.emit (binLine n w "andi" ca sa (s.opnd b))
      let (cb, s) := s.fresh
      let s := s.emit (binLine n w "andi" cb sb (s.opnd a))
      let (u, s) := s.fresh
      let s := s.emit (binLine n w "subi" u h ca)
      let (v, s) := s.fresh
      (s.emit (binLine n w "subi" v u cb)).bind dst v
  | .permxv dst _ _ => s.bind dst "%undef"
  | .bcast dst _ _ => s.bind dst "%undef"
  | .hadd dst _ => s.bind dst "%undef"
  | .shl dst _ _ => s.bind dst "%undef"
  | .sar dst _ _ => s.bind dst "%undef"
  | .rotl dst _ _ => s.bind dst "%undef"
  | .rotr dst _ _ => s.bind dst "%undef"
  | .mulhu dst _ _ => s.bind dst "%undef"
  | .shuffle dst _ _ _ => s.bind dst "%undef"
  | .blend dst _ _ _ => s.bind dst "%undef"
where
  binOp (s : St) (mn dst a b : String) : St :=
    let (v, s) := s.fresh
    (s.emit (binLine n w mn v (s.opnd a) (s.opnd b))).bind dst v

/-! ## 3. The kernel -/

/-- The three lines that turn the pointer argument `%p<x>` into the tile of
    pointers `%p<x>3` to `n` consecutive elements. -/
def ptrLines (n w : Nat) (x : String) : String :=
  "    %p" ++ x ++ "1 = cuda_tile.reshape %p" ++ x ++ " : " ++ ptrTyAt w ++ " -> "
      ++ ptrTileTyAt 1 w ++ "\n"
    ++ "    %p" ++ x ++ "2 = cuda_tile.broadcast %p" ++ x ++ "1 : " ++ ptrTileTyAt 1 w ++ " -> "
      ++ ptrTileTyAt n w ++ "\n"
    ++ "    %p" ++ x ++ "3 = cuda_tile.offset %p" ++ x ++ "2, %iota : " ++ ptrTileTyAt n w ++ ", "
      ++ idxTyAt n ++ " -> " ++ ptrTileTyAt n w ++ "\n"

/-- The line loading the tile `%<x>` through `%p<x>3`. -/
def loadLine (n w : Nat) (x : String) : String :=
  "    %" ++ x ++ ", %t" ++ x ++ " = cuda_tile.load_ptr_tko weak %p" ++ x ++ "3 : "
    ++ ptrTileTyAt n w ++ " -> " ++ tileTyAt n w ++ ", token\n"

/-- The lines after the `iota` type: the pointer tiles of `%pa`, `%pb`, `%pr` and the
    loads of `%a`, `%b`. -/
def loadPrologue (n w : Nat) : String :=
  "\n" ++ ptrLines n w "a" ++ loadLine n w "a" ++ ptrLines n w "b" ++ loadLine n w "b"
    ++ ptrLines n w "r"

/-- The kernel text up to the first body line: the module, the entry with pointer
    arguments `%pa`, `%pb`, `%pr`, and the loads. -/
def kernelOpen (n w : Nat) (name : String) : String :=
  "cuda_tile.module @" ++ name ++ " {\n  cuda_tile.entry @" ++ name ++ "(%pa: " ++ ptrTyAt w
    ++ ", %pb: " ++ ptrTyAt w ++ ", %pr: " ++ ptrTyAt w ++ ") {\n    %iota = cuda_tile.iota : "
    ++ idxTyAt n ++ loadPrologue n w

/-- The start of the store line, before the stored operand. -/
def storeHead : String := "    %tr = cuda_tile.store_ptr_tko weak %pr3, "

/-- The rest of the store line, the `return` and the closing braces. -/
def storeTail (n w : Nat) : String :=
  " : " ++ ptrTileTyAt n w ++ ", " ++ tileTyAt n w ++ " -> token\n    cuda_tile.return\n  }\n}\n"

/-- The initial emit state: registers `a`, `b` are the loaded tiles `%a`, `%b`. -/
def St.init : St := { map := [("a", "%a"), ("b", "%b")], ctr := 0, lines := [] }

/-- Emit a tile block at tile type `tileTyAt n w` as a `cuda_tile` kernel `name`
    that loads registers `a`, `b` and stores register `res`. -/
def emitTileFuncAt (n w : Nat) (name : String) (body : List TileOp) (res : String) : String :=
  let s := body.foldl (emitTileOp n w) St.init
  kernelOpen n w name ++ String.join (s.lines.reverse.map (· ++ "\n")) ++ storeHead
    ++ s.opnd res ++ storeTail n w

/-- `emitTileFuncAt` at tile type `8xi64`. -/
def emitTileFunc (name : String) (body : List TileOp) (res : String) : String :=
  emitTileFuncAt 8 64 name body res

/-- The ops the emitter has no `cuda_tile` form for. -/
def laneMoving : TileOp → Bool
  | .permxv .. | .bcast .. | .hadd .. | .shl .. | .sar .. | .rotl .. | .rotr .. | .mulhu ..
  | .shuffle .. | .blend .. => true
  | _ => false

/-- The kernel text, or `none` when the block contains a lane-moving op. -/
def emitTileFunc? (n w : Nat) (name : String) (body : List TileOp) (res : String) :
    Option String :=
  if body.any laneMoving then none else some (emitTileFuncAt n w name body res)

/-- The BabyBear `bbMul` tile emitted as a `cuda_tile` kernel. -/
def bbMulTileIR : String := emitTileFunc "bb_mul_tile" bbMulTile "o"

/-! ## 4. Emit driver -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/gpu_compare/gen"
  IO.FS.writeFile "bench/gpu_compare/gen/bb_mul_tile.cuda_tile.mlir" bbMulTileIR
  IO.println "wrote bench/gpu_compare/gen/bb_mul_tile.cuda_tile.mlir (BabyBear bbMul, cuda_tile dialect)"
  IO.println s!"  {bbMulTile.length} tile ops -> cuda_tile MLIR (tile<8xi64>)"

end CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR
