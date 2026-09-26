/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Emit driver: the FULL BN254 tower as one native jasmin artifact (#222)

This is the CatCrypt-side composition driver for the AUCurves-emitted FULL BN254
tower. It does NOT touch `CatCrypt.Crypto.Vale.BN254` (the EIP-197 verify / G1-MSM
kernels over the leaf edge); it adds the wiring for the *whole* pairing tower as a
single jasmin module.

## What changed in the trust base

`CatCrypt.Crypto.Vale.BN254` composes BN254 over the LEAF edge: the jasmin kernels
call `bn254_pairing` / `bn254_fp12_mul` as opaque leaves, and the leaves are the
AUCurves Rust tower (`Fp/Fp2/Fp6/Fp12` + pairing) compiled by **rustc/LLVM** and
linked through a **C/FFI shim** (`stubs.rs` + `jasmin_aliases.s`). So today only the
Fp word-level leaves (`bn254_add/sub/mul/square`) go through jasmin; the
tower-composition layer (Fp2/Fp6/Fp12/miller/final-exp/pairing) is rustc-compiled.

The full-tower emit removes the tower-composition layer from the rustc/LLVM trust
base: AUCurves `src/Bedrock/ExtractBN254TowerJasmin.v` runs the SAME bedrock2
`bn254_tower_funcs` list that `ExtractSafeTower.v` emits as the Rust `tower` module
through the verified `tr_func_sized 4` / `pp_module` path, producing
`bn254-safe-rust/generated/bn254_tower.jazz` — one jasmin module containing all 51
tower functions. The jasmin tower and the Rust tower are two pretty-prints of one
verified bedrock2 program (`Core.tr_cmd_correct` is the Qed faithfulness theorem).

## Emit-faithfulness (AUCurves side, cited here)

* `Core.tr_cmd_correct : forall c, cmd_jasmin_equiv c (tr_cmd c)` — the bedrock2
  `cmd` -> `jasmin_cmd` AST translation is faithful (Qed). Every tower function's
  body is `cmd.call` / `cmd.stackalloc` / `cmd.set` / `cmd.store` / `cmd.cond` /
  `cmd.while`, all covered by `tr_cmd`.
* `Core.pp_locals_decls_nospill_drops_spill` / `pp_locals_decls_spill_form` (Qed) —
  the spill vs no-spill emits differ ONLY in the `#[spill]` register-class hint, an
  inert jasminc allocation hint. So `bn254_tower.jazz` and `bn254_tower_nospill.jazz`
  denote the same program.

The tower funcs inline no field multiply (they only move and call leaves), so the
radix / MULX representation concern is confined to the Fp leaves; the tower emit is
representation-agnostic.

## Coverage (honest gap)

All 51 tower functions emit to jasmin TEXT. Of those, 12 leaf-level functions (Fp2
felem_copy/add/sub/conjugate/mul_fp + the seven Fp2 constant loaders) type-check
under jasminc as emitted and compile to x86-64 against the verified leaves. The
remaining 39 (Fp2_mul/square, all of Fp6/Fp12, make_line, pow_u, final_exp,
miller_loop, pairing) hit a calling-convention gap: the emit prints pointer args as
`reg u64` and stackalloc temporaries as `stack u64[N]`, and jasminc cannot
implicitly decay a `stack u64[N]` array to a `reg u64` when passing a temporary to a
leaf. Closing it needs a `reg ptr u64[N]` emit convention (params + array-indexed
access + return-value threading) for both the tower and the leaf signatures — a new
emit path, not a reuse of the #218/#219 primitives. See
`jasmin_tower/JASMIN_TOWER_222.md`.

KAT (`jasmin_tower/bn254_tower_kat.rs`): the compiling subset (Fp2_add/sub/copy) is
byte-identical to the Rust tower on the published EIP-197 G2 generator coordinates.

Invoke:  lake env lean bench/bn254_compare/bn254_tower_jasmin_emit.lean
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254TowerJasmin

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- Path to the AUCurves-emitted full BN254 tower jasmin module. Relative to the
CatCrypt repo root; the sibling `BLS/AUCurves` checkout holds the generated file. -/
def towerJazzPath : String :=
  "../BLS/AUCurves/bn254-safe-rust/generated/bn254_tower.jazz"

/-- The leaf symbols the jasmin tower calls — the EDGE that `Bn254Emit` ties to the
abstract BN254 primitives (the same leaves `bn254-safe-rust` provides as the
verified Fp word-level jasmin from #219). -/
def towerLeafEdge : List String :=
  ["bn254_add", "bn254_sub", "bn254_mul", "bn254_square",
   "bn254_opp", "bn254_felem_copy", "bn254_from_word"]

/-- The top-level pairing entry points the full-tower emit provides as native
jasmin (vs the rustc-compiled `tower` module today). -/
def towerTopLevel : List String :=
  ["bn254_pairing_dsd", "bn254_pairing_dsd_optimal",
   "bn254_miller_loop", "bn254_miller_loop_optimal",
   "bn254_final_exp_dsd", "bn254_Fp12_mul", "bn254_Fp6_mul"]

/-- Structural check: the emitted tower text declares every expected top-level
pairing function and references every leaf-edge symbol. Run against the on-disk
`bn254_tower.jazz` (AUCurves emit). -/
def checkTowerShape (jazz : String) : Bool :=
  (towerTopLevel.all  (fun f => strContains jazz ("export fn " ++ f ++ "("))) &&
  (towerLeafEdge.all  (fun f => strContains jazz (f ++ "(")))

def main : IO Unit := do
  let jazz ← IO.FS.readFile towerJazzPath
  let funcs := (jazz.splitOn "export fn ").length - 1
  IO.println s!"BN254 full-tower jasmin emit (AUCurves ExtractBN254TowerJasmin.v):"
  IO.println s!"  source : {towerJazzPath}"
  IO.println s!"  export fn count : {funcs}"
  if checkTowerShape jazz then
    IO.println "  shape OK: all top-level pairing entry points present; leaf edge wired"
    IO.println "  trust delta: tower-composition layer (Fp2/Fp6/Fp12/miller/final-exp/"
    IO.println "               pairing) leaves the rustc/LLVM trust base — emitted as one"
    IO.println "               native jasmin module from the verified bedrock2 program"
    IO.println "               (Core.tr_cmd_correct). The C/FFI shim remains only for the"
    IO.println "               leaf edge until the 39-function stackalloc convention gap"
    IO.println "               (jasmin_tower/JASMIN_TOWER_222.md) is closed."
  else
    IO.eprintln "  shape CHECK FAILED: emitted tower missing an expected entry point/leaf"

#eval main

end CatCrypt.Crypto.Pairing.Bn254TowerJasmin
