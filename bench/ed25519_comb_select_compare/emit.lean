import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

/-!
Emit driver for `bench/ed25519_comb_select_compare/gen_com`: the 4-, 5- and 6-bit
Ed25519 comb-window select kernels rendered by the owned x86 backend. Run from the
compiler repository root with `lake env lean --run`.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

def main : IO Unit := emitTo "bench/ed25519_comb_select_compare/gen_com"
