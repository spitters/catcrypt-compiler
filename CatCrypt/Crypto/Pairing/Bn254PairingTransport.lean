/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Pairing.Eip197Denote

/-!
# BN254 pairing transport: AUCurves-anchored deployed primitives

`Eip197Denote.lean` seals the deployed EIP-197 pairing leaf edge as an
**abstract self-seal**: `opaque deployedPrims : Bn254Primitives` (uninterpreted)
plus `axiom eip197LeafOracle_agrees`.  That axiom is content-free — it relates an
opaque leaf oracle to an opaque primitive, with no reference to the mathematical
pairing spec or to any external proof.

This module provides, in place of that self-seal, an **AUCurves-anchored cross-prover
transport**, in the exact discipline of the curve25519 bedrock transport
(`KeyAgreement/X25519/BedrockX25519.lean`) and the trust registry
(`TrustAxioms.lean` §4): a Rocq-`Qed`'d spec is carried into Lean as a *named*
axiom with a provenance citation, and the deployed primitives are the concrete
byte functions the axiom talks about — so the trust edge is a NAMED transport
citing a real Rocq theorem, not an opaque agreement.

## The transport

* `bn254PairingLeaf` / `bn254Fp12MulLeaf` — the deployed byte-level pairing and
  `Fp12`-multiply functions (the Lean images of the compiled AUCurves
  `pairing_optimal` / `fp12_mul` byte kernels), opaque.
* `decodeG1` / `decodeG2` / `decodeGT` — byte→field decoders, the CatCrypt images
  of AUCurves' abstract `feval`-style decoders (`bn254_fp12_to_Z`, the G1/G2
  coordinate readers), opaque.
* `bn254_optimal_ate_spec` / `bn254_fp12_mul_spec` — the mathematical field-level
  specs (Lean images of the AUCurves Rocq spec functions), opaque.
* `bn254_pairing_correct_rocq` / `bn254_fp12mul_correct_rocq` — the **transport
  axioms**: the deployed byte leaf, decoded to a field value, equals the
  mathematical spec applied to the decoded arguments.

## Provenance citation

`bn254_pairing_correct_rocq` transports the AUCurves Rocq theorem

    bn254_pairing_dsd_optimal_correct   (BN254_PairingCorrect.v, `Qed`)

whose bedrock2 WP spec is `bn254_fp12_to_Z out = bn254_optimal_ate_spec …`
(given the strong callee hypotheses `strong_loader_spec` / `strong_miller_spec`
/ `strong_final_exp_spec`); see the §0 catalog in
`SecureCompilation/AUCurvesImport/FieldLeafBridge.lean:63`.  The companion
`pairing_spec_compose` (`Qed`, same file) proves
`final_exp ∘ (corrections ∘ miller) = bn254_optimal_ate_spec`.
`bn254_fp12mul_correct_rocq` transports the AUCurves `fp12_mul` byte kernel's
field-multiply spec (the `Curve/BN254Curve_G1_BignumSpecs.v` Montgomery-mul
leaf, consumed by `BN254_PairingCorrect.v`).

## Scope (what this file does and does not claim)

The transport axioms are **cross-prover edges** (Rocq→Lean): each carries an
AUCurves Rocq-`Qed`'d spec into Lean as a named hypothesis, exactly the status
of the four curve25519 bedrock axioms.  They are NOT machine-checked in Lean.

The KAT (`bench/bn254_compare/`, published EIP-196/EIP-197 vectors) SEPARATELY
checks the *computed* byte result against the reference; it does **not** discharge
the transport axioms (value validation ≠ syntactic/spec transport — the two are
independent legs of the trust triangle, per `TrustAxioms.lean` §4).

Named residual (same status as the curve25519 bedrock axioms):
1. the byte↔field decode round-trip (`decodeG1`/`decodeG2`/`decodeGT` are the
   faithful images of the AUCurves layout readers), and
2. identifying the deployed byte leaves `bn254PairingLeaf` / `bn254Fp12MulLeaf`
   with the AUCurves `pairing_optimal` / `fp12_mul` Rust symbols the emit
   targets.
Both live outside Lean — the residual the transport axiom encapsulates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254PairingTransport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bn254Emit
open CatCrypt.Crypto.Pairing.Eip197Denote

/-! ## 1. The BN254 base field + on-wire field-value representations

The BN254 (alt-bn128) base field is `F p` for the 254-bit prime
`p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
(`y² = x³ + 3`, generator `G1 = (1,2)`).  We model the decoded field values with
`ZMod p`: a G1 point as an affine `(x, y)`; a G2 point as an affine pair over
`Fp2 = Fp × Fp`; and a GT (`Fp12`) element as a 12-tuple of base-field
coordinates — the Lean image of AUCurves' `bn254_fp12_to_Z` output. -/

/-- The BN254 base-field prime `p` (see `Bn254Emit.lean` header). -/
def bn254BaseFieldPrime : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The BN254 base field `F p`. -/
abbrev Fp : Type := ZMod bn254BaseFieldPrime

/-- A decoded G1 point: affine `(x, y)` over `Fp`. -/
abbrev G1Repr : Type := Fp × Fp

/-- A decoded G2 point: affine `(x, y)` over `Fp2 = Fp × Fp`. -/
abbrev G2Repr : Type := (Fp × Fp) × (Fp × Fp)

/-- A decoded GT (`Fp12`) element: 12 base-field coordinates (the image of
    AUCurves' `bn254_fp12_to_Z`). -/
abbrev Fp12Repr : Type := Fin 12 → Fp

/-! ## 2. Deployed byte leaves + byte→field decoders + math specs (opaque)

Each `opaque` below is the Lean image of a concrete AUCurves object.  They are
kept uninterpreted: the transport axioms (§3) are the only facts asserted about
them, mirroring `BedrockX25519`'s `bytesToWord` / `Fp25519OfBedrock` opaque
adapters and its `montladder_math_spec`. -/

/-- The deployed BN254 pairing byte kernel `e(P, Q)` — the Lean image of the
    compiled AUCurves `pairing_optimal` (Miller loop + final exponentiation).
    Opaque; its only spec is the transport axiom `bn254_pairing_correct_rocq`. -/
noncomputable opaque bn254PairingLeaf :
    (Fin G1SZ → BitVec 8) → (Fin G2SZ → BitVec 8) → (Fin GTSZ → BitVec 8)

/-- The deployed BN254 GT (`Fp12`) multiply byte kernel — the Lean image of the
    compiled AUCurves `fp12_mul`.  Opaque; spec'd by `bn254_fp12mul_correct_rocq`. -/
noncomputable opaque bn254Fp12MulLeaf :
    (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)

/-- Byte→field decoder for a G1 point (image of the AUCurves coordinate reader). -/
noncomputable opaque decodeG1 : (Fin G1SZ → BitVec 8) → G1Repr

/-- Byte→field decoder for a G2 point (image of the AUCurves coordinate reader). -/
noncomputable opaque decodeG2 : (Fin G2SZ → BitVec 8) → G2Repr

/-- Byte→field decoder for a GT (`Fp12`) element — the Lean image of AUCurves'
    `bn254_fp12_to_Z`. -/
noncomputable opaque decodeGT : (Fin GTSZ → BitVec 8) → Fp12Repr

/-- The mathematical BN254 optimal-ate pairing spec `G1 × G2 → Fp12` — the Lean
    image of AUCurves' `bn254_optimal_ate_spec`. -/
noncomputable opaque bn254_optimal_ate_spec : G1Repr → G2Repr → Fp12Repr

/-- The mathematical GT (`Fp12`) product spec — the Lean image of AUCurves'
    `fp12_mul` field-level specification. -/
noncomputable opaque bn254_fp12_mul_spec : Fp12Repr → Fp12Repr → Fp12Repr

/-! ## 3. The transport axioms (named cross-prover edges, Rocq→Lean) -/

/-- **Transport axiom (BN254 optimal-ate pairing).**  The deployed pairing byte
    kernel, decoded to `Fp12`, equals the mathematical optimal-ate spec on the
    decoded G1/G2 arguments.

    AUCurves Rocq citation: `bn254_pairing_dsd_optimal_correct`
    (`AUCurves/.../BN254_PairingCorrect.v`, `Qed`) — bedrock2 WP spec
    `bn254_fp12_to_Z out = bn254_optimal_ate_spec …` (given the strong callee
    hypotheses); see `FieldLeafBridge.lean:63`.  This is a cross-prover edge, not
    a Lean theorem: the fact that the deployed byte kernel realises the
    Rocq-proved spec spans two proof assistants and is named here, not proved. -/
axiom bn254_pairing_correct_rocq
    (P : Fin G1SZ → BitVec 8) (Q : Fin G2SZ → BitVec 8) :
    decodeGT (bn254PairingLeaf P Q)
      = bn254_optimal_ate_spec (decodeG1 P) (decodeG2 Q)

/-- **Transport axiom (BN254 `Fp12` multiply).**  The deployed GT-multiply byte
    kernel, decoded to `Fp12`, equals the mathematical `Fp12` product on the
    decoded arguments.

    AUCurves Rocq citation: the `fp12_mul` byte kernel's field-multiply spec
    (`Curve/BN254Curve_G1_BignumSpecs.v` Montgomery-mul leaf, consumed by
    `BN254_PairingCorrect.v`; §0 catalog, `FieldLeafBridge.lean:57,63`).  Same
    cross-prover status as `bn254_pairing_correct_rocq`. -/
axiom bn254_fp12mul_correct_rocq
    (a b : Fin GTSZ → BitVec 8) :
    decodeGT (bn254Fp12MulLeaf a b)
      = bn254_fp12_mul_spec (decodeGT a) (decodeGT b)

/-! ## 4. The AUCurves-anchored deployed primitives -/

/-- **The deployed BN254 primitives, anchored to the AUCurves transport.**  The
    pairing / `Fp12`-multiply fields are the deployed byte kernels
    `bn254PairingLeaf` / `bn254Fp12MulLeaf` the transport axioms (§3) spec; the
    group fields are inert (not exercised by the EIP-197 verifier).  This is the
    transport-anchored replacement for `Eip197Denote.deployedPrims` (an opaque
    self-seal). -/
noncomputable def deployedBn254Prims : Bn254Primitives where
  g1Add := fun _ _ _ => 0
  g1Mul := fun _ _ _ => 0
  g2Add := fun _ _ _ => 0
  g2Mul := fun _ _ _ => 0
  pairing := bn254PairingLeaf
  fp12Mul := bn254Fp12MulLeaf

@[simp] theorem deployedBn254Prims_pairing :
    deployedBn254Prims.pairing = bn254PairingLeaf := rfl

@[simp] theorem deployedBn254Prims_fp12Mul :
    deployedBn254Prims.fp12Mul = bn254Fp12MulLeaf := rfl

/-- **The deployed leaves realise the deployed primitives.**  A *theorem* (via
    `pairingOracle_agrees`), not an axiom: `pairingOracle deployedBn254Prims`
    satisfies `PairingLeavesAgree deployedBn254Prims` by construction — the
    orchestration is Lean-proven and the trust is pushed entirely onto the two
    named transport axioms. -/
theorem deployedBn254Prims_leavesAgree :
    PairingLeavesAgree deployedBn254Prims (pairingOracle deployedBn254Prims) :=
  pairingOracle_agrees deployedBn254Prims

/-! ## 5. The EIP-197 verifier at the transport-anchored primitives -/

/-- **The deployed EIP-197 verifier at the transport-anchored oracle (byte
    value).**  `Bn254Emit.eip197VerifyCom`, denoted through
    `jasminDenoteWith (pairingOracle deployedBn254Prims)`, computes the deployed
    byte product `fp12Mul (pairing P₁ Q₁) (pairing P₂ Q₂)`.  Instantiation of
    the leaf-parametric `Bn254Emit.eip197VerifyCom_denote` at the leaf model
    `pairingOracle deployedBn254Prims` and the Lean-proven agreement — no
    `eip197LeafOracle_agrees` self-seal. -/
theorem eip197VerifyCom_denote_deployed
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _
        (JasminDialect.jasminDenoteWith (pairingOracle deployedBn254Prims)) _ _
        Bn254Emit.eip197VerifyCom
        (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil))))
      = bn254Fp12MulLeaf (bn254PairingLeaf p1 q1) (bn254PairingLeaf p2 q2) :=
  Bn254Emit.eip197VerifyCom_denote (pairingOracle deployedBn254Prims) deployedBn254Prims
    deployedBn254Prims_leavesAgree p1 q1 p2 q2

/-- **The deployed EIP-197 verifier at the transport-anchored oracle (field
    value).**  The deployed `eip197VerifyCom`, denoted through the deployed
    oracle and read back as an `Fp12` via `decodeGT`, computes the mathematical
    pairing product

        e(P₁,Q₁) · e(P₂,Q₂) = fp12_mul (ate P₁ Q₁) (ate P₂ Q₂)

    where `ate = bn254_optimal_ate_spec`.  The precompile accepts iff this equals
    `1` in GT.

    The orchestration is Lean-proven; the *only* trust edges are the two NAMED
    transport axioms `bn254_pairing_correct_rocq` / `bn254_fp12mul_correct_rocq`
    (each citing a real AUCurves Rocq `Qed`), NOT an opaque self-seal.  Run
    `#print axioms eip197VerifyCom_denote_transport` to confirm the footprint. -/
theorem eip197VerifyCom_denote_transport
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    decodeGT (@Com.denote _ _ _
        (JasminDialect.jasminDenoteWith (pairingOracle deployedBn254Prims)) _ _
        Bn254Emit.eip197VerifyCom
        (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil)))))
      = bn254_fp12_mul_spec
          (bn254_optimal_ate_spec (decodeG1 p1) (decodeG2 q1))
          (bn254_optimal_ate_spec (decodeG1 p2) (decodeG2 q2)) := by
  rw [eip197VerifyCom_denote_deployed, bn254_fp12mul_correct_rocq,
      bn254_pairing_correct_rocq, bn254_pairing_correct_rocq]

end CatCrypt.Crypto.Pairing.Bn254PairingTransport
