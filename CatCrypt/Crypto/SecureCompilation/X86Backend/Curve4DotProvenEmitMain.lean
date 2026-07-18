/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4DotProvenEmit

/-!
Compiled producer entry point for the secp256k1 base-field COMPOSITION
`dot(a,b,c,d) = a·b + c·d` over 𝔽ₚ, emitted as a composition of PROVEN blocks
(`Curve4DotProvenEmit.emitMainSecp256k1Dot` → `gen_com/secp256k1_dot_proven.s`).

`lake exe secp256k1dot` — the proven montmul leaf's spilling-allocated block
renders too slowly through the `lean --run` interpreter, so the emit is run as
native code, exactly as the Poseidon2 field-pipeline keystone
(`poseidon2fieldpipeline`).
-/

def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4DotProvenEmit.emitMainSecp256k1Dot
