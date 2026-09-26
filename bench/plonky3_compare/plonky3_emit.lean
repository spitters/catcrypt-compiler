/-
Emit the full Plonky3 STARK prover chain as `.jazz` exports, directly from
CatCrypt's verified front. Four layers, each with its denotation-preservation
theorem and a KAT against the plonky3-hax reference:

  * `merkle_build_root.jazz` — layer 1: binary Merkle-tree commitment over Baby
    Bear leaves. Every tree level is a lane-parallel MAP (one two-to-one
    compress per lane); denotation via `merkleLevel_denotation_preserves`.
    KAT: root / leaf / compress byte-identical to plonky3-hax merkle.rs.
  * `lde_coset_fft.jazz` — layer 2: coset-FFT low-degree extension. Radix-2
    butterfly reusing the lattice NTT structure over Baby Bear; denotation via
    `ldeStage_denotation_preserves`. KAT: Horner / domain-element / field ops.
  * `fri.jazz` — layer 3: FRI commit (per-coset fold, lane-parallel) + query
    (Merkle openings reusing layer 1). Denotation via
    `friFoldLayer_denotation_preserves`. KAT: fri_fold / fold_polynomial.
  * `air_eval_fib.jazz` — layer 4: AIR constraint evaluator (Fibonacci AIR).
    Per-step transition sweep is a lane-parallel MAP; denotation via
    `airTransition_denotation_preserves`. KAT: fib_trace / max-degree.

All four field-arithmetic kernels are regArith-only (NO opaque leaf), the same
discipline as the Poseidon2-BabyBear emit. KAT references live in
plonky3-hax/tests/kat_vectors.rs; see README.md for the per-layer mapping.

Invoke:  lake env lean bench/plonky3_compare/plonky3_emit.lean
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit


@[expose] public section
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit

def main : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen"
  -- Layer 1: Merkle-tree commitment.
  IO.FS.writeFile "bench/plonky3_compare/gen/merkle_build_root.jazz"
    (merkleJazz ++ "\n")
  IO.println "wrote bench/plonky3_compare/gen/merkle_build_root.jazz (layer 1: Merkle)"
  -- Layer 2: coset-FFT LDE.
  IO.FS.writeFile "bench/plonky3_compare/gen/lde_coset_fft.jazz"
    (ldeJazz ++ "\n")
  IO.println "wrote bench/plonky3_compare/gen/lde_coset_fft.jazz (layer 2: LDE)"
  -- Layer 3: FRI commit + query.
  IO.FS.writeFile "bench/plonky3_compare/gen/fri.jazz"
    (friJazz ++ "\n")
  IO.println "wrote bench/plonky3_compare/gen/fri.jazz (layer 3: FRI)"
  -- Layer 4: AIR constraint evaluator.
  IO.FS.writeFile "bench/plonky3_compare/gen/air_eval_fib.jazz"
    (airJazz ++ "\n")
  IO.println "wrote bench/plonky3_compare/gen/air_eval_fib.jazz (layer 4: AIR)"

#eval main
