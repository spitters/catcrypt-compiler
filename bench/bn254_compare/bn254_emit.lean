/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.Pairing.Bn254Emit

/-!
# Emission of the production BN254 (alt-bn128) kernels: G1 MSM + EIP-197 verify

**TEST/BENCH-ONLY — STRING-TEMPLATED, not verified-compiler output.** The
emitted `gen/bn254_*.jazz` files are assembled as text (`"export fn …"` bodies
with `for`-loop and leaf-call lines built by string builders, joined with
`++`/`String.intercalate`), with no single verified-printer descent for the
whole file. The `g1MsmFold_eq_msm` / `eip197VerifyCom_denote` /
`pairingCom_denote` denotation theorems hold over the `Com` model, not over the
assembled `.jazz` text. The `#guard`/`strContains`/`splitOn` checks are
substring assertions on that text. It is a bench/interop reference. The verified
emit path is the FRONT-SOURCED descent; see
`../SSProve-lean/bench/framework/AUDIT_EMIT_BYPASS.md` and `EMIT_PROVENANCE.md`
§"Which emit is verified?".

Emits fixed-size jazz kernels over the production
BN254 leaves declared in `CatCrypt.Crypto.Pairing.Bn254Emit`:

* `bn254_g1_msm` — the G1 MSM `Σ_i k_i · P_i`, the `scalarFold` reduction over the
  production BN254 G1 `AddCommMonoid` (`Bn254Emit.g1MsmFold_eq_msm`), a real
  single-level `for` loop calling `bn254_g1_scalar_mul` / `bn254_g1_add`;
* `bn254_eip197_verify` — the EIP-197 2-pair product `e(P₁,Q₁) · e(P₂,Q₂)`, two
  `bn254_pairing` leaves accumulated by one `bn254_fp12_mul` leaf
  (`Bn254Emit.eip197VerifyCom_denote`);
* `bn254_pairing_one` — a single `bn254_pairing` leaf (`Bn254Emit.pairingCom_denote`).

The leaves are the AUCurves verified-bedrock2 BN254 tower (`bn254-safe-rust`:
the extracted `Fp/Fp2/Fp6/Fp12` tower + `pairing_optimal` + `fp12_mul`). The KAT
(`bench/bn254_compare/bn254_kat.rs`) cross-checks the emitted-equation denotation
against that reference on the published EIP-196 / EIP-197 vectors.

Invoke:  lake env lean bench/bn254_compare/bn254_emit.lean
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254Emit.Emit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.Pairing.Bn254Emit

/-- The MSM length the bench uses (`L = 4` terms). -/
def L : Nat := 4

/-! ## 1. The G1 MSM kernel (scalarFold over the production BN254 G1 group) -/

/-- Single-level G1 MSM `for` loop body — the `scalarFold` step
    `acc ↦ acc + k_i·P_i`. One iteration; the `for` is NOT unrolled.
    (Fp = 32 bytes, G1 point = 64 bytes.) -/
def g1MsmLoopBody : String :=
  "  for i = 0 to " ++ toString L ++ " {\n" ++
  "    for j = 0 to 32 { ksi[j] = ks[32 * i + j]; }\n" ++
  "    for j = 0 to 64 { psi[j] = ps[64 * i + j]; }\n" ++
  "    psi = bn254_g1_scalar_mul(ksi, psi);\n" ++
  "    acc = bn254_g1_add(acc, psi);\n" ++
  "  }"

/-- The fixed-size BN254 G1 MSM kernel `Σ_{i=0}^{L-1} k_i · P_i`. ABI: `out :
    u8[64]`, `ks : u8[32L]`, `ps : u8[64L]`. Real single-level `for i = 0 to L`
    loop. Denotation: `out = Σ_i k_i·P_i` (`Bn254Emit.g1MsmFold_eq_msm` +
    `g1MsmTermCom_denote`). -/
def g1MsmJazz : String :=
  "export fn bn254_g1_msm(reg ptr u8[64] out, reg const ptr u8[" ++ toString (32 * L) ++
    "] ks, reg const ptr u8[" ++ toString (64 * L) ++ "] ps) -> reg ptr u8[64] {\n" ++
  "  stack u8[64] acc;\n" ++
  "  stack u8[64] psi;\n" ++
  "  stack u8[32] ksi;\n" ++
  "  inline int i;\n" ++
  "  inline int j;\n" ++
  "  for j = 0 to 64 { acc[j] = 0; }\n" ++
  g1MsmLoopBody ++ "\n" ++
  "  for j = 0 to 64 { out[j] = acc[j]; }\n" ++
  "  return out;\n}"

/-! ## 2. The pairing verifiers -/

/-- Single BN254 pairing leaf `e(P, Q)`. ABI: `out : u8[384]` (GT = Fp12), `p :
    u8[64]` (G1), `q : u8[128]` (G2). Denotes to `prims.pairing p q`
    (`Bn254Emit.pairingCom_denote`). -/
def pairingOneJazz : String :=
  "export fn bn254_pairing_one(reg ptr u8[384] out, reg const ptr u8[64] p, " ++
    "reg const ptr u8[128] q) -> reg ptr u8[384] {\n" ++
  "  out = bn254_pairing(out, p, q);\n" ++
  "  return out;\n}"

/-- EIP-197 2-pair product `e(P₁,Q₁) · e(P₂,Q₂)`: two `bn254_pairing` leaves
    accumulated by one `bn254_fp12_mul` leaf. ABI: `out : u8[384]` (GT), inputs
    bundled in `inp` of two (G1,G2) pairs = 2·(64+128) = 384 bytes. Denotes to
    `fp12Mul (e P₁ Q₁) (e P₂ Q₂)` (`Bn254Emit.eip197VerifyCom_denote`); the
    precompile accepts iff this `= 1` in GT. -/
def eip197VerifyJazz : String :=
  "export fn bn254_eip197_verify(reg ptr u8[384] out, reg const ptr u8[384] inp) " ++
    "-> reg ptr u8[384] {\n" ++
  "  stack u8[64] p1; stack u8[128] q1;\n" ++
  "  stack u8[64] p2; stack u8[128] q2;\n" ++
  "  stack u8[384] e1;\n" ++
  "  stack u8[384] e2;\n" ++
  "  inline int j;\n" ++
  "  reg u8 t;\n" ++
  "  for j = 0 to 64  { t = inp[j];        p1[j] = t; }\n" ++
  "  for j = 0 to 128 { t = inp[64 + j];   q1[j] = t; }\n" ++
  "  for j = 0 to 64  { t = inp[192 + j];  p2[j] = t; }\n" ++
  "  for j = 0 to 128 { t = inp[256 + j];  q2[j] = t; }\n" ++
  "  e1 = bn254_pairing(e1, p1, q1);\n" ++
  "  e2 = bn254_pairing(e2, p2, q2);\n" ++
  "  e1 = bn254_fp12_mul(e1, e2);\n" ++
  "  for j = 0 to 384 { t = e1[j]; out[j] = t; }\n" ++
  "  return out;\n}"

/-! ## 3. Structural checks on the emitted text -/

/-- The G1 MSM kernel emits a real single-level `for i = 0 to 4` loop, not unrolled. -/
theorem g1msm_has_for : strContains g1MsmJazz "for i = 0 to 4" = true := by native_decide

/-- The G1 MSM body calls the G1 scalar-multiply leaf on the term. -/
theorem g1msm_scalar_mul_leaf :
    strContains g1MsmJazz "psi = bn254_g1_scalar_mul(ksi, psi);" = true := by native_decide

/-- The G1 MSM body accumulates via the G1 point-add leaf. -/
theorem g1msm_point_add_leaf :
    strContains g1MsmJazz "acc = bn254_g1_add(acc, psi);" = true := by native_decide

/-- The G1 scalar-multiply leaf appears exactly ONCE (the `for` is not unrolled). -/
theorem g1msm_not_unrolled :
    (g1MsmJazz.splitOn "psi = bn254_g1_scalar_mul(ksi, psi);").length = 2 := by native_decide

/-- The EIP-197 verifier emits exactly two `bn254_pairing` leaf calls. -/
theorem eip197_two_pairings :
    (eip197VerifyJazz.splitOn "bn254_pairing(").length = 3 := by native_decide

/-- The EIP-197 verifier accumulates via exactly one `bn254_fp12_mul` leaf. -/
theorem eip197_one_fp12_mul :
    (eip197VerifyJazz.splitOn "bn254_fp12_mul(").length = 2 := by native_decide

/-- The single-pairing kernel emits exactly one `bn254_pairing` leaf. -/
theorem pairing_one_leaf :
    (pairingOneJazz.splitOn "bn254_pairing(").length = 2 := by native_decide

def main : IO Unit := do
  IO.FS.createDirAll "bench/bn254_compare/gen"
  IO.FS.writeFile "bench/bn254_compare/gen/bn254_g1_msm.jazz" (g1MsmJazz ++ "\n")
  IO.FS.writeFile "bench/bn254_compare/gen/bn254_pairing_one.jazz" (pairingOneJazz ++ "\n")
  IO.FS.writeFile "bench/bn254_compare/gen/bn254_eip197_verify.jazz" (eip197VerifyJazz ++ "\n")
  IO.println "wrote bench/bn254_compare/gen/*.jazz (BN254 leaves)"

#eval main

end CatCrypt.Crypto.Pairing.Bn254Emit.Emit
