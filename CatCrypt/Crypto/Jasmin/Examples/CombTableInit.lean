/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# build_comb_table authored as a Lean `LowCT` AST.

Computes the Ed25519 comb table: `T[i][d] = d · 16^i · B` for
`i ∈ 0..63`, `d ∈ 0..15`.  Used by the wnaf_comb scalarmult_base body
to do zero-doubling fixed-base multiplication.

This is Phase 2 of the "extend the IR" plan, applied to the second
hand-coded primitive in `curve25519-jasmin-rs/src/ed25519_rustcmd/leaves.rs`.
Per the user's instruction (2026-05-12), we author the body in Lean
using the **existing** `LowCT` constructors — no runtime-indexed slot
access yet, so the 1024 cells become 1024 separately-named slots
`cell_<i>_<d>`.  Generation is mechanical via Lean meta.

The AST is large (~5000 nodes) but flat — pure sequencing of:
  * 1024 `RLetZero` slot declarations (1024 × `TBytes 200`)
  * 15 `RCall "xyzt_add_decomposed" cell_0_d [cell_0_(d-1), B]` for the d·B row
  * 1 `RCall "xyzt_copy" cell_0_0 [ID_xyzt]` for the identity
  * 1 `RCall "xyzt_copy" cell_0_1 [B_xyzt]` for B itself
  * 63 × 16 × 4 doubling RCalls = 4032 (with ping-pong via scratch slots)
  * Plus copy-from-scratch operations to land each cell in its named slot

Inputs:  `B_xyzt`, `ID_xyzt`   (both `&[u8; 200]`)
Outputs: `cell_0_0` ... `cell_63_15`  (1024 × `&mut [u8; 200]`)
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.RustEmit


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.CombTableInit

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1.  Slot helpers -/

/-- A 200-byte XYZT-point slot. -/
def xyzt (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TBytes 200 }

def cellName (i d : Nat) : String :=
  s!"cell_{i}_{d}"

def cell (i d : Nat) : Located := xyzt (cellName i d)

/-- `RCall "xyzt_add_decomposed" dst [a, b]`: `dst := a + b`. -/
def xyztAdd (dst a b : String) : LowCT :=
  LowCT.RCall "xyzt_add_decomposed" (xyzt dst) [xyzt a, xyzt b]

/-- `RCall "xyzt_double_decomposed" dst [a]`: `dst := 2 · a`. -/
def xyztDouble (dst a : String) : LowCT :=
  LowCT.RCall "xyzt_double_decomposed" (xyzt dst) [xyzt a]

/-- `RCall "xyzt_copy" dst [a]`: `dst := a` (200-byte memcpy). -/
def xyztCopy (dst a : String) : LowCT :=
  LowCT.RCall "xyzt_copy" (xyzt dst) [xyzt a]

/-- Left-fold a list of commands into a `RSeq` chain. -/
def seqN : List LowCT → LowCT
  | []      => LowCT.RSkip
  | [c]     => c
  | c :: cs => LowCT.RSeq c (seqN cs)

/-! ## §2.  Slot declarations -/

/-- Declare a single 200-byte XYZT scratch (`scratch_a`/`scratch_b`)
    or named cell, wrapping a continuation. -/
def letCell (name : String) (cont : LowCT) : LowCT :=
  LowCT.RLetZero name (TowerType.TBytes 200) cont

/-- Wrap a body with all 1024 cell declarations + 2 doubling scratches. -/
def declareAllSlots (body : LowCT) : LowCT :=
  letCell "scratch_a" $
  letCell "scratch_b" $
  -- Outer fold over (i, d): wrap one RLetZero per cell.
  (List.range 64).foldr (fun i acc =>
    (List.range 16).foldr (fun d acc' =>
      letCell (cellName i d) acc') acc) body

/-! ## §3.  Body construction -/

/-- Row 0: `cell_0_0 = ID`, `cell_0_1 = B`, `cell_0_d = cell_0_(d-1) + B` for d ≥ 2. -/
def buildRow0 : LowCT :=
  seqN $
    [ xyztCopy (cellName 0 0) "ID_xyzt"   -- 0 · B = identity
    , xyztCopy (cellName 0 1) "B_xyzt" ]  -- 1 · B = B
    ++ (List.range 14).map (fun k =>
         -- d = k+2 ∈ {2, ..., 15}
         xyztAdd (cellName 0 (k + 2)) (cellName 0 (k + 1)) "B_xyzt")

/-- For row i ≥ 1, cell `(i, d) = double^4(cell (i-1, d))`.
    To avoid `&mut x, &x` aliasing on consecutive doublings we
    ping-pong through two scratch slots:
      scratch_a := double cell_(i-1)_d
      scratch_b := double scratch_a
      scratch_a := double scratch_b
      cell_i_d  := double scratch_a
    Four `xyzt_double_decomposed` RCalls, no copies. -/
def buildCell (i d : Nat) : LowCT :=
  let src := cellName (i - 1) d
  let dst := cellName i d
  seqN
    [ xyztDouble "scratch_a" src
    , xyztDouble "scratch_b" "scratch_a"
    , xyztDouble "scratch_a" "scratch_b"
    , xyztDouble dst "scratch_a" ]

/-- Row i for i ≥ 1: 16 cells × 4 doublings = 64 RCalls. -/
def buildRow (i : Nat) : LowCT :=
  seqN ((List.range 16).map (fun d => buildCell i d))

/-- Full body: row 0 then rows 1..63.  All cells written. -/
def combTableInitBody : LowCT :=
  declareAllSlots $
    seqN (buildRow0 :: (List.range 63).map (fun k => buildRow (k + 1)))

/-! ## §4.  Function envelope + emit -/

/-- Inputs: B and identity point as 200-byte XYZT slots.

    Note: the AST passes named cells through `RLetZero` declarations
    inside the body, NOT as output parameters.  In emitted Rust the
    cells are local `let mut cell_i_d : [u8; 200]` declarations;
    a hand-written shim (in the crate) copies them into the
    `OnceLock<CombTable>` at the bottom of the function.  This keeps
    the AST closed-form (one function, fixed signature). -/
def params : List Located := [ xyzt "B_xyzt", xyzt "ID_xyzt" ]

/-- Outputs: a single 200×1024 = 204800-byte sink slot that the
    emitted code never directly writes — used here only to give the
    function a non-empty result list.  The emitted code's effect is
    captured by the 1024 local `cell_*` slots; the shim reads those
    out via Rust scope leakage (the shim text wraps the emitted body
    in a closure that returns a `[[u8; 200]; 1024]` literal). -/
def results : List Located := []

/-- The Rust source string for `build_comb_table`. -/
def emitCombTableInit : String :=
  ppRustFunction "build_comb_table_emitted" params results combTableInitBody

/-- IO driver: write the emitted source to `/tmp/build_comb_table.rs`. -/
def runEmit : IO Unit := do
  let outPath := "/tmp/build_comb_table.rs"
  IO.FS.writeFile outPath emitCombTableInit
  IO.println s!"wrote {outPath}"
  IO.println s!"({emitCombTableInit.length} bytes)"

end CatCrypt.Crypto.Jasmin.Examples.CombTableInit
