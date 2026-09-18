import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

/-!
Emit driver for `bench/ed25519_comb_select_compare/gen_com_folded`: the
front-generated Ed25519 comb-window selects after the constant-index fold
(`ConstIndexFold.constIndexFold`) and copy coalescing
(`LprogCopyCoalesce.coalesceRounds`), under the shipped symbol names, so the same
harness checks them. Run from the compiler repository root with
`lake env lean --run`.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

def main : IO Unit := emitFoldedTo "bench/ed25519_comb_select_compare/gen_com_folded"
