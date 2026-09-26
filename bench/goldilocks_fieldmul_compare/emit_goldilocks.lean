module

public meta import CatCrypt.Crypto.Optimizer.ModReduceSelect

@[expose] public section
open CatCrypt.Crypto.Optimizer.ModReduceSelect

-- Re-emit `gen_com/goldilocks_mul_x86_from_lean.s` from the verified AST.
-- Run from the repo root:
--   lake env lean bench/goldilocks_fieldmul_compare/emit_goldilocks.lean
#eval emitGoldilocks
