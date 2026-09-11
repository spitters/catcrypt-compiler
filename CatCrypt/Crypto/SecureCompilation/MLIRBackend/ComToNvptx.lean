/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# `Com → Tile → NVVM/PTX`: a GPU emit path (first increment / PoC)

This is the first increment of a GPU backend for the verified CatCrypt compiler.
It lowers a field kernel's straight-line op sequence — the **same `regArith`
alphabet** a `Com jasminDialect` field leaf is built from (`add`/`sub`/`mul`/`and`/
`shr`, plus materialised constants; cf. `Plonky3NttLayerEmit`, the owned ARM
`BOp` blocks) — to an **NVPTX CUDA kernel** in LLVM IR, which `clang`'s NVPTX
back-end lowers to **PTX**.

## The tile model

A *tile* is a block of `N` BabyBear lanes laid out in global memory. The kernel
is the per-lane program run by **one GPU thread per lane**: thread
`gid = ctaid.x · ntid.x + tid.x` loads lane `gid` of each input, runs the field
op sequence (its scalar `Com` body), and stores lane `gid` of the output. So the
straight-line field `Com` *is* a single thread's program; the tile is the SIMT
fan-out over lanes. This is the GPU analogue of the SIMD lane-parallel maps the
x86/ARM backends emit (`LaneMap.laneMap`), but expressed at the thread level.

## What this increment IS / IS NOT (honest scope)

* **IS — a validated emission path.** `Com`-shaped field op sequence → NVPTX
  LLVM IR → (clang `--target=nvptx64-nvidia-cuda -S`) → **PTX**. `clang`'s NVPTX
  back-end is the structural validator: it accepts the emitted IR and produces a
  `.visible .entry` PTX kernel (`bench/gpu_compare`). The emitted kernel is the
  BabyBear Barrett `bbMul` (the load-bearing field multiply: `(a·b) mod p` via the
  shift/multiply/shift reduce + branchless conditional subtract).
* **IS NOT — executed.** There is no GPU / `ptxas` available; the PTX is emitted
  and structurally validated, **not run**. No execution KAT is claimed.
* **IS NOT — verified.** There is **no** `Com → PTX` denotation-preservation
  theorem here and **no** GPU/SIMT semantics — that (a tile/GPU semantics + a
  lowering-correctness keystone) is the open research part. There is also **no
  SAIL anchor for GPU** (unlike the x86/ARM `decode(encode)=i` verified-to-bytes
  story); SAIL has no authoritative PTX/SASS model.

The point of this increment is to prove the *emission path* end-to-end and to
size the verification obligation, not to be a verified GPU prover.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.MLIRBackend.ComToNvptx

set_option autoImplicit false

/-! ## 1. The tile op alphabet

The elementwise BabyBear field ops over a tile lane — the `regArith` subset a
field `Com jasminDialect` leaf uses. `shr` carries an immediate count; `const`
materialises a 64-bit field constant (a lane-uniform value). -/

/-- One straight-line field op over named lane-local SSA values. -/
inductive TileOp where
  /-- `dst := a + b` (wrapping u64). -/
  | add (dst a b : String)
  /-- `dst := a - b` (wrapping u64). -/
  | sub (dst a b : String)
  /-- `dst := a * b` (low 64 of the product — the Barrett `bbMul` step). -/
  | mul (dst a b : String)
  /-- `dst := a & b`. -/
  | and (dst a b : String)
  /-- `dst := a >>> imm` (logical shift right by an immediate). -/
  | shr (dst a : String) (imm : Nat)
  /-- `dst := n` (a lane-uniform 64-bit constant). -/
  | const (dst : String) (n : Nat)
  deriving Repr, DecidableEq

/-! ## 2. BabyBear Barrett `bbMul` as a tile body

`bbMul a b = (a·b) mod p` over BabyBear (`p = 2013265921`, Barrett `MU =
2290649223`), branchless: the shift-multiply-shift reduce then one conditional
subtract — byte-identical to the x86/ARM field leaves' `bbMul`. Inputs are the
loaded lane values `a`, `b`; the result is `o`. -/
def bbMulTile : List TileOp :=
  [ .const "MU" 2290649223, .const "P" 2013265921, .const "zero" 0
  -- Barrett reduce of x = a*b:
  , .mul "x" "a" "b", .shr "q" "x" 30, .mul "q" "q" "MU", .shr "q" "q" 32
  , .mul "q" "q" "P", .sub "x" "x" "q"
  -- conditional subtract: o = x - p; m = (o>>63); m = 0-m; m = m & p; o = o + m
  , .sub "o" "x" "P", .shr "m" "o" 63, .sub "m" "zero" "m", .and "m" "m" "P"
  , .add "o" "o" "m" ]

/-! ## 3. SSA renaming + the per-op LLVM-IR line

LLVM IR is SSA (each `%name` assigned once), but the tile body reuses names
(`q`, `x`, `m`, `o`). We thread a name → current-`%ssa` map and a fresh counter:
each write mints a fresh `%vNN`, reads resolve to the latest binding. `const`
binds a name to an inline literal (no instruction). -/

/-- Emit state: the value-resolution map, fresh counter, and emitted IR lines. -/
structure St where
  /-- name → current LLVM operand (a `%vNN` or an integer literal). -/
  map : List (String × String)
  /-- fresh `%vNN` counter. -/
  ctr : Nat
  /-- emitted IR body lines (reversed). -/
  lines : List String

/-- Resolve a tile value name to its current LLVM operand (literal `0` if unbound,
    which cannot happen for a well-formed body — every read is written first). -/
def St.opnd (s : St) (nm : String) : String := (s.map.lookup nm).getD "0"

/-- Bind `nm` to operand `v`. -/
def St.bind (s : St) (nm v : String) : St := { s with map := (nm, v) :: s.map }

/-- Mint a fresh `%vNN`, returning it and the bumped state. -/
def St.fresh (s : St) : String × St :=
  let v := "%v" ++ toString s.ctr
  (v, { s with ctr := s.ctr + 1 })

/-- Emit one IR body line. -/
def St.emit (s : St) (line : String) : St := { s with lines := line :: s.lines }

/-- Translate one `TileOp` into LLVM IR, threading the SSA state. The binary ops
    map to the obvious `i64` LLVM instruction; `shr` is `lshr i64`; `const` binds
    the name to an inline literal with no instruction. -/
def emitTileOp (s : St) : TileOp → St
  | .const dst n => s.bind dst (toString n)
  | .add dst a b => binOp s "add"  dst a b
  | .sub dst a b => binOp s "sub"  dst a b
  | .mul dst a b => binOp s "mul"  dst a b
  | .and dst a b => binOp s "and"  dst a b
  | .shr dst a imm =>
      let (v, s) := s.fresh
      let s := s.emit ("  " ++ v ++ " = lshr i64 " ++ s.opnd a ++ ", " ++ toString imm)
      s.bind dst v
where
  binOp (s : St) (mn dst a b : String) : St :=
    let (v, s) := s.fresh
    let s := s.emit ("  " ++ v ++ " = " ++ mn ++ " i64 " ++ s.opnd a ++ ", " ++ s.opnd b)
    s.bind dst v

/-- Fold the body through `emitTileOp`. -/
def emitBody (s0 : St) (body : List TileOp) : St := body.foldl emitTileOp s0

/-! ## 4. The NVPTX kernel wrapper

`define void @<name>(i64* %out, i64* %a, i64* %b)`: thread `gid = ctaid·ntid +
tid` loads `a[gid]`, `b[gid]` (bound to the tile names `a`, `b`), runs the body,
stores the result name `o` to `out[gid]`. The module carries the
`nvptx64-nvidia-cuda` triple and the `!nvvm.annotations` entry marking the
function as a `kernel` (so `ptxas`/the driver expose it as a launchable entry). -/

/-- The NVPTX module preamble: triple + the SReg intrinsics used for the lane id. -/
def preamble : List String :=
  [ "target triple = \"nvptx64-nvidia-cuda\""
  , ""
  , "declare i32 @llvm.nvvm.read.ptx.sreg.tid.x()"
  , "declare i32 @llvm.nvvm.read.ptx.sreg.ctaid.x()"
  , "declare i32 @llvm.nvvm.read.ptx.sreg.ntid.x()" ]

/-- Emit the full NVPTX kernel module for a 2-input / 1-output tile body whose
    result lives in the name `resName`. -/
def emitKernel (name : String) (body : List TileOp) (resName : String) : String :=
  let prologue : List String :=
    [ "define void @" ++ name ++ "(i64* %out, i64* %a, i64* %b) {"
    , "entry:"
    , "  %tid = call i32 @llvm.nvvm.read.ptx.sreg.tid.x()"
    , "  %ctaid = call i32 @llvm.nvvm.read.ptx.sreg.ctaid.x()"
    , "  %ntid = call i32 @llvm.nvvm.read.ptx.sreg.ntid.x()"
    , "  %blk = mul i32 %ctaid, %ntid"
    , "  %gid32 = add i32 %blk, %tid"
    , "  %gid = sext i32 %gid32 to i64"
    , "  %pa = getelementptr i64, i64* %a, i64 %gid"
    , "  %va = load i64, i64* %pa"
    , "  %pb = getelementptr i64, i64* %b, i64 %gid"
    , "  %vb = load i64, i64* %pb" ]
  -- seed the tile inputs `a`, `b` to the loaded lane values
  let s0 : St := { map := [("a", "%va"), ("b", "%vb")], ctr := 0, lines := [] }
  let s := emitBody s0 body
  let epilogue : List String :=
    [ "  %pout = getelementptr i64, i64* %out, i64 %gid"
    , "  store i64 " ++ s.opnd resName ++ ", i64* %pout"
    , "  ret void"
    , "}"
    , ""
    , "!nvvm.annotations = !{!0}"
    , "!0 = !{ptr @" ++ name ++ ", !\"kernel\", i32 1}" ]
  String.intercalate "\n"
    (preamble ++ [""] ++ prologue ++ s.lines.reverse ++ epilogue) ++ "\n"

/-- The BabyBear `bbMul` NVPTX kernel module (the emitted artifact). -/
def bbMulKernel : String := emitKernel "bb_mul_tile" bbMulTile "o"

/-! ## 5. Structural pins (the emitted IR shape) -/

/-- A substring test. -/
def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The kernel carries the NVPTX triple. -/
theorem kernel_has_triple :
    contains bbMulKernel "target triple = \"nvptx64-nvidia-cuda\"" = true := by
  native_decide

/-- The kernel defines the `bb_mul_tile` entry and reads the lane id. -/
theorem kernel_has_entry :
    contains bbMulKernel "define void @bb_mul_tile" = true
      ∧ contains bbMulKernel "@llvm.nvvm.read.ptx.sreg.tid.x" = true := by
  native_decide

/-- The Barrett reduce is present (the `mul`/`lshr` field arithmetic) and the
    `nvvm` kernel annotation marks it launchable. -/
theorem kernel_has_field_ops_and_annotation :
    contains bbMulKernel "lshr i64" = true
      ∧ contains bbMulKernel "mul i64" = true
      ∧ contains bbMulKernel "!\"kernel\"" = true := by
  native_decide

/-! ## 6. Emit driver

Writes the kernel module to `bench/gpu_compare/gen/bb_mul_tile.ll`. The bench
target `gpu-nvptx-emit` then runs
`clang --target=nvptx64-nvidia-cuda -S bb_mul_tile.ll -o bb_mul_tile.ptx`
and checks the PTX carries `.visible .entry bb_mul_tile`. -/
def main : IO Unit := do
  IO.FS.createDirAll "bench/gpu_compare/gen"
  IO.FS.writeFile "bench/gpu_compare/gen/bb_mul_tile.ll" bbMulKernel
  IO.println "wrote bench/gpu_compare/gen/bb_mul_tile.ll (BabyBear bbMul NVPTX tile kernel)"
  IO.println s!"  {bbMulTile.length} tile ops -> NVPTX LLVM IR (one thread per lane)"

-- #eval main

end CatCrypt.Crypto.SecureCompilation.MLIRBackend.ComToNvptx
