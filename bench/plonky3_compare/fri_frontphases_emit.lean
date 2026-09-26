module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit

@[expose] public section

/-
`lake env lean --run` entry point: emit the FRONT-COMPILED `fri_proof` spine
phases (FRI fold chain at runtime AND compile-time counts + flat Merkle build
+ layer-0 query/auth-path walk) as owned `.s` (no jasminc, no hand
`Com`/`Lcmd`).  Writes `bench/plonky3_compare/gen_com/fri_proof_frontphases.s`.

  lake env lean --run bench/plonky3_compare/fri_frontphases_emit.lean

KAT: `make -C bench/plonky3_compare plonky3-fri-frontphases-kat` (independent
C-reference fold + Merkle oracle).
-/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit.emit
