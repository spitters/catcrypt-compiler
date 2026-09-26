/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

/-!
Emit driver for the FULL BN254 base-field Montgomery multiply assembled from
PROVEN blocks (`emitProductBlock4` product + `emitMontRedcStep` Montgomery
reduce, `n' = 0x87d20782e4866389`, separate digit/row carry). Writes the `.s` for
`bench/bn254_compare/gen/bn254_montmul_proven.s` (symbol `bn254_montmul_proven`,
System-V `void bn254_montmul_proven(uint64_t *z, const uint64_t *x, const uint64_t *y)`).

Invoke (from repo root):
  lake env lean bench/bn254_compare/bn254_montmul_proven_emit.lean
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

def main : IO Unit := emitMainBn254

#eval main
