module

public import CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit

@[expose] public section

/-
`lake env lean --run` entry point: emit the FRONT-COMPILED Mersenne-31 field
kernels `m31_mul_owned` / `m31_add_owned` / `m31_reduce_owned` as one owned
`.s` (no jasminc, no hand `Com`/`Lcmd`).

The kernels are plain covered straight-line LowCT (RArrLoad / RScalarSetExpr /
RArrStore) front-compiled by `translateDialectControl` and lowered through
`cryptoDialectToJasminCom` + `Com.toLprogPhysAbi` (SysV pointer ABI, one u64
cell per pointer). The Mersenne `2³¹ ≡ 1` field math (double fold + branch-free
conditional subtract) is all immediate-shift `SExpr` — the covered alphabet.

KAT: bench/m31_compare/m31_field_kat.c (small-exhaustive + boundary + random
vs a direct `__int128 % p` C reference).
-/
open CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit in
def main : IO Unit := do
  IO.FS.createDirAll "bench/m31_compare/gen_com"
  emit "bench/m31_compare/gen_com/m31_field_owned.s"
  IO.println "wrote bench/m31_compare/gen_com/m31_field_owned.s (front-compiled, no hand Com/Lcmd, no jasminc)"
