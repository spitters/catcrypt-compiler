/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

/-!
Emit driver for the FULL Pallas base-field Montgomery multiply assembled from
PROVEN blocks (`emitProductBlock4` product + `emitMontRedcStep` Montgomery
reduce, `n' = 0x992d30ecffffffff`, separate digit/row carry). Writes the `.s` for
`bench/pallas_compare/gen/pallas_montmul_proven.s` (symbol `pallas_montmul_proven`,
System-V `void pallas_montmul_proven(uint64_t *z, const uint64_t *x, const uint64_t *y)`).

Invoke (from repo root):
  lake env lean bench/pallas_compare/pallas_montmul_proven_emit.lean
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

def main : IO Unit := emitMainPallas

#eval main
