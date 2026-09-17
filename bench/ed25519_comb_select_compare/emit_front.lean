import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

/-!
Emit driver for `bench/ed25519_comb_select_compare/gen_com_front`: the front-generated
Ed25519 comb-window select kernels (`CombSelectFront`), under the same symbol names
as the shipped ones, so the same harness checks them. Run from the compiler
repository root with `lake env lean --run`.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

def main : IO Unit := emitFrontTo "bench/ed25519_comb_select_compare/gen_com_front"
