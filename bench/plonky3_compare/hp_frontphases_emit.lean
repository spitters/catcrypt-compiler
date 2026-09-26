module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HonestProveFrontEmit

@[expose] public section

/-
`lake env lean --run` entry point: emit the FRONT-COMPILED `honest_prove` FRI
fold-chain phase as owned `.s` (no jasminc, no hand `Com`/`Lcmd`).  Writes
`bench/plonky3_compare/gen_com/honest_prove_frontphases.s`.

  lake env lean --run bench/plonky3_compare/hp_frontphases_emit.lean

KAT: `make -C bench/plonky3_compare plonky3-hp-frontphases-kat` (the REAL
jasminc whole-prover artifact linked as the oracle).
-/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HonestProveFrontEmit.emit
