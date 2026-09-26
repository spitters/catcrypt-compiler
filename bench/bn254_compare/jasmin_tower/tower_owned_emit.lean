module

public import CatCrypt.Crypto.SecureCompilation.Bn254TowerFrontEmit

@[expose] public section

/-
`lake env lean --run` entry point: emit the FRONT-COMPILED BN254 `Fp2` tower
leaves `j_bn254_Fp2_add` / `j_bn254_Fp2_sub` / `j_bn254_Fp2_felem_copy` as one
owned `.s` (no jasminc, no hand `Com`/`Lcmd`).

The kernels are covered straight-line LowCT (RArrLoad / RScalarSetExpr /
RArrStore) front-compiled by `translateDialectCarrySelect` (the C6 carry-chain
instruction-selection front: the `bSltu` carry/borrow windows lower to
`bvAddCarryLo`/`bvAddCarryHi` ADC-class chains, constant array indices are
re-materialised per access; everything else falls through to
`translateDialectControl`) and lowered through `cryptoDialectToJasminCom` +
`Com.toLprogPhysAbi` (SysV pointer ABI, eight u64 cells per pointer).

KAT: bench/bn254_compare/jasmin_tower/bn254_tower_kat.rs (byte-identical vs
the AUCurves verified-bedrock2 Rust tower on the published EIP-197 G2
generator coordinates).
-/
open CatCrypt.Crypto.SecureCompilation.Bn254TowerFrontEmit in
def main : IO Unit := do
  IO.FS.createDirAll "bench/bn254_compare/jasmin_tower/gen_com"
  emit "bench/bn254_compare/jasmin_tower/gen_com/tower_owned.s"
  IO.println "wrote bench/bn254_compare/jasmin_tower/gen_com/tower_owned.s (front-compiled, no hand Com/Lcmd, no jasminc)"
