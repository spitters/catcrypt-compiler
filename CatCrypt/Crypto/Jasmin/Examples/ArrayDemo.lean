/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# `TArr` array-of-slots IR demo.

Demonstrates the `TArr n t` TowerType + `RArrLoad` / `RArrStore`
constructors.  Same body shape as the build_comb_table
inner loop, but using runtime-indexed array access instead of 1024
separately named slots.

For a single 4-element doubling pipeline this saves: 4 named `cell_i`
slots collapse to one `cells : TArr 4 (TBytes 200)` slot, accessed by a
loop variable `i : u64`.  Scaled to the full comb table (1024 cells),
this would shrink the AST from ~5000 nodes to ~10 nodes (a `RFor`
loop body of 4-5 `RArrStore`/`RArrLoad` calls).

This file just emits a smoke-test function to validate the new IR
compiles + prints to syntactically valid Rust.  Semantic KAT against a
hand-coded equivalent is out of scope here (the comb-table KAT in the
curve25519-jasmin-rs crate covers the leaves; the IR extension is
syntactic).
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTSyntax
public import CatCrypt.Crypto.Jasmin.RustEmit
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.ArrayDemo

open CatCrypt.Crypto.Jasmin.LowCT

/-- The array slot: 4 cells of 200 bytes each = TArr 4 (TBytes 200). -/
def arrLoc : Located :=
  { locVar := "cells", locSrc := TowerType.TArr 4 (TowerType.TBytes 200) }

/-- A single 200-byte cell scratch. -/
def scratchLoc : Located :=
  { locVar := "scratch", locSrc := TowerType.TBytes 200 }

/-- Body: for i in 0..4 { cells[i] = scratch }.  Demonstrates
    `RArrStore` with a runtime index bound by `RFor`. -/
def demoStoreLoop : LowCT :=
  LowCT.RLetZero "cells" (TowerType.TArr 4 (TowerType.TBytes 200)) $
  LowCT.RLetZero "scratch" (TowerType.TBytes 200) $
  LowCT.RFor "i" 4
    (LowCT.RArrStore arrLoc "i" scratchLoc)

/-- Body: for i in 0..4 { cells[i] = scratch; tmp = cells[i]; }.
    Demonstrates both store and load with a runtime index. -/
def demoLoadStoreLoop : LowCT :=
  let tmpLoc : Located := { locVar := "tmp", locSrc := TowerType.TBytes 200 }
  LowCT.RLetZero "cells" (TowerType.TArr 4 (TowerType.TBytes 200)) $
  LowCT.RLetZero "scratch" (TowerType.TBytes 200) $
  LowCT.RLetZero "tmp" (TowerType.TBytes 200) $
  LowCT.RFor "i" 4
    (LowCT.RSeq
      (LowCT.RArrStore arrLoc "i" scratchLoc)
      (LowCT.RArrLoad tmpLoc arrLoc "i"))

/-! ## Constant-time guarantee (dynamic-index array support)

With the runtime-indexed array ops wired through the secure-compiler
front-end, the security question is whether a runtime-indexed array loop is
constant-time.  It is — **when the index is public**.  The loop counter `"i"`
is public (it ranges over `0..4`, independent of any secret), so the array-map
loop passes `cmdCT`; by `cmdCT_sound` this is noninterference (no
secret leaks via the address trace).  The *same* `cmdCT` rejects a loop whose
index reads secret data (the AES-S-box class). -/

/-- The store loop is constant-time by construction on a public index. -/
theorem demoStoreLoop_isCT (leafCT : LeafCTTable) :
    cmdCT demoStoreLoop (fun _ => SecretLevel.Public) leafCT = true := by
  simp only [demoStoreLoop, arrLoc, scratchLoc, cmdCT_RLetZero, cmdCT_RFor,
    cmdCT_RArrStore]
  decide

/-- The load+store loop (both runtime-indexed accesses) is constant-time by
    construction on a public index. -/
theorem demoLoadStoreLoop_isCT (leafCT : LeafCTTable) :
    cmdCT demoLoadStoreLoop (fun _ => SecretLevel.Public) leafCT = true := by
  simp only [demoLoadStoreLoop, arrLoc, scratchLoc, cmdCT_RLetZero, cmdCT_RFor,
    cmdCT_RSeq, cmdCT_RArrStore, cmdCT_RArrLoad]
  decide

/-- The emit. -/
def emitDemo : String :=
  ppRustFunction "array_demo" [] [] demoLoadStoreLoop

def runEmit : IO Unit := do
  let outPath := "/tmp/array_demo.rs"
  IO.FS.writeFile outPath emitDemo
  IO.println s!"wrote {outPath}"
  IO.println s!"({emitDemo.length} bytes)"
  IO.println "---"
  IO.println emitDemo

end CatCrypt.Crypto.Jasmin.Examples.ArrayDemo
