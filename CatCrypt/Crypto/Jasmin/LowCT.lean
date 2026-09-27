/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTTypes
public import CatCrypt.Crypto.Jasmin.LowCTSExpr
public import CatCrypt.Crypto.Jasmin.LowCTSyntax
public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# `LowCT`: Typed Tower-Field Low-level Constant-Time Command Language

Port of `AUCurves/src/Bedrock/SafeRustSimulation.v`.

`LowCT` is a typed DSL for low-level
constant-time crypto programs over tower field elements (Fp, Fp2, Fp6, Fp12,
U64) — *not* Rust.  It exposes branchless-select, kernel-call ABIs, machine
intrinsics, widening multiply, and limb stores, the scheduling/codegen layer
Rust deliberately hides.  The borrow checker (`LowCTBorrowCheck.lean`)
certifies memory safety statically; the simulation semantics (`RustExec`)
gives the big-step meaning used for frame proofs.

This module re-exports the four parts of the language, all in the namespace
`CatCrypt.Crypto.Jasmin.LowCT`:

* `LowCTTypes` — `encodeStringNat`, `TowerType`, `RustVal`, `SecretLevel`,
  `LevelTable`, `Located`, `callAliases`;
* `LowCTSExpr` — `SExpr` with `SExpr.eval`, `SExpr.evalBV`, `SExpr.inRange`
  and the printers `SExpr.ppRust`, `SExpr.ppJazz`;
* `LowCTSyntax` — the command type `LowCT`, `LowCT.RVsimdSetExpr`,
  `LowCT.fold`, `LowCT.foldNode`, `LowCT.isRecursive`;
* `LowCTExec` — `LeafSpec`, `RustState`, `SExpr.evalState`,
  `SExpr.evalStateBV`, `locatedLookup`, `locatedUpdate`, `callNUpdate` and the
  big-step relation `RustExec`.

## Tower type encoding

Tower elements are modelled as fixed-size byte arrays (`JArray`), using the
BLS12-381 sizes as concrete defaults.  The `byteSize` function can be
overridden by downstream files for other curves.

## References

* AUCurves `SafeRustSimulation.v` — original Rocq DSL
* AUCurves `SafeRustBorrowCheck.v` — borrow checker and frame theorems
-/
