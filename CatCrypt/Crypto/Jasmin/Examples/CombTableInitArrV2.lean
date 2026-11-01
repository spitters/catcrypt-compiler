/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# `build_comb_table` v2 — full TArr + SExpr compression.

This is the rewrite of `CombTableInitArr.lean` using BOTH new IR
features:
  * `TArr 1024 (TBytes 200)` for the cell array
  * `RScalarSetExpr` + `SExpr` for runtime index arithmetic

With BOTH features, the algorithm collapses to ~10 IR nodes:
  * Row 0 init: `RFor d in 0..14 { k = d+2; load cells[k-1]; add B; store cells[k] }`
  * Doubling rows: `RFor i in 1..64 { RFor d in 0..16 { k = i*16+d; load; double⁴; store } }`

Compare to:
  * Named-slot version (CombTableInit.lean):       277 KB / 5075 lines / 5000 nodes
  * TArr-without-SExpr (CombTableInitArr.lean):    331 KB / 8145 lines / similar nodes
  * TArr + SExpr (THIS FILE):                       ~3 KB / ~30 lines / ~10 nodes
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.Jasmin.RustEmit


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2

open CatCrypt.Crypto.Jasmin.LowCT

def cellsLoc : Located :=
  { locVar := "cells", locSrc := TowerType.TArr 1024 (TowerType.TBytes 200) }

def cellLoc (name : String) : Located :=
  { locVar := name, locSrc := TowerType.TBytes 200 }

def xyztAdd (dst a b : String) : LowCT :=
  LowCT.RCall "xyzt_add_decomposed" (cellLoc dst) [cellLoc a, cellLoc b]

def xyztDouble (dst a : String) : LowCT :=
  LowCT.RCall "xyzt_double_decomposed" (cellLoc dst) [cellLoc a]

def arrStore (idxVar src : String) : LowCT :=
  LowCT.RArrStore cellsLoc idxVar (cellLoc src)

def arrLoad (dst idxVar : String) : LowCT :=
  LowCT.RArrLoad (cellLoc dst) cellsLoc idxVar

/-- Set scalar `x` to an SExpr value (Phase Ext shorthand). -/
def scExpr (x : String) (e : SExpr) : LowCT :=
  LowCT.RScalarSetExpr x e

def seqN : List LowCT → LowCT
  | []      => LowCT.RSkip
  | [c]     => c
  | c :: cs => LowCT.RSeq c (seqN cs)

/-! ## §1.  Row 0 — d·B for d=0..15

  cells[0] = ID;
  cells[1] = B;
  for d in 0..14 {       // d' = d+2 ∈ 2..15, k = d', k-1 = d+1
    k := d + 1;
    prev := cells[k];
    sum := prev + B;
    k := d + 2;
    cells[k] := sum;
  }
-/

def buildRow0 : LowCT := seqN
  [ scExpr "k" (.SLit 0)
  , arrStore "k" "ID_xyzt"
  , scExpr "k" (.SLit 1)
  , arrStore "k" "B_xyzt"
  , LowCT.RFor "d" 14 (seqN
      [ scExpr "k" (.SAdd (.SVar "d") (.SLit 1))         -- k := d + 1
      , arrLoad "prev" "k"
      , xyztAdd "sum" "prev" "B_xyzt"
      , scExpr "k" (.SAdd (.SVar "d") (.SLit 2))         -- k := d + 2
      , arrStore "k" "sum"
      ])
  ]

/-! ## §2.  Rows 1..63 — cells[i*16+d] = double⁴(cells[(i-1)*16+d])

  for i in 0..63 {           // outer counts 0..63, so row = i+1 ∈ 1..64
    for d in 0..16 {
      k := i*16 + d;         // index of cells[(i-1)*16+d] ... wait, RFor x in 0..63 → x = 0,1,..,62
                             // Actually RFor x n iterates x = 0..n-1, n iters
      // Use the SAME row-source convention: read from row i, write to row i+1
      k := i*16 + d;
      a := cells[k];
      b := double(a);
      a := double(b);
      b := double(a);
      a := double(b);
      k := (i+1)*16 + d;
      cells[k] := a;
    }
  }
-/

def buildLaterRows : LowCT :=
  LowCT.RFor "i" 63 (
    LowCT.RFor "d" 16 (seqN
      [ -- k := i*16 + d   (source row index, i in 0..63 means row = i)
        scExpr "k" (.SAdd (.SMul (.SVar "i") (.SLit 16)) (.SVar "d"))
      , arrLoad "scratch_a" "k"
      , xyztDouble "scratch_b" "scratch_a"
      , xyztDouble "scratch_a" "scratch_b"
      , xyztDouble "scratch_b" "scratch_a"
      , xyztDouble "scratch_a" "scratch_b"
        -- k := (i+1)*16 + d   (dest row index = i+1)
      , scExpr "k" (.SAdd (.SMul (.SAdd (.SVar "i") (.SLit 1)) (.SLit 16)) (.SVar "d"))
      , arrStore "k" "scratch_a"
      ]))

def combTableInitArrV2Body : LowCT :=
  LowCT.RLetZero "cells" (TowerType.TArr 1024 (TowerType.TBytes 200)) $
  LowCT.RLetZero "scratch_a" (TowerType.TBytes 200) $
  LowCT.RLetZero "scratch_b" (TowerType.TBytes 200) $
  LowCT.RLetZero "prev" (TowerType.TBytes 200) $
  LowCT.RLetZero "sum" (TowerType.TBytes 200) $
  LowCT.RLetU64Zero "k" $
  LowCT.RSeq buildRow0 buildLaterRows

def params : List Located := [ cellLoc "B_xyzt", cellLoc "ID_xyzt" ]
def results : List Located := []

def emitCombTableInitArrV2 (_ : Unit) : String :=
  ppRustFunction "build_comb_table_arr_v2" params results combTableInitArrV2Body

def runEmit : IO Unit := do
  let outPath := "/tmp/build_comb_table_arr_v2.rs"
  let s := emitCombTableInitArrV2 ()
  IO.FS.writeFile outPath s
  IO.println s!"wrote {outPath}"
  IO.println s!"({s.length} bytes)"
  IO.println "---"
  IO.println s

end CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2
