/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Pairing.Eip197Denote

/-!
# BN254 pairing transport: the EIP-197 verifier under the AUCurves specs

`Eip197Denote.lean` denotes the deployed EIP-197 verifier against the leaf oracle
`pairingOracle prims` for any `prims : Bn254Primitives`
(`Eip197Denote.pairingOracle_agrees`). This module states, as a hypothesis on
`prims`, the facts that the AUCurves Rocq development proves about the deployed
pairing and `fp12_mul` byte kernels, and derives the field value the verifier
computes from them.

## Main results

* `bn254PairingLeaf` / `bn254Fp12MulLeaf` — the deployed byte-level pairing and
  `Fp12`-multiply functions (the Lean images of the compiled AUCurves
  `pairing_optimal` / `fp12_mul` byte kernels), opaque.
* `decodeG1` / `decodeG2` / `decodeGT` — byte→field decoders, the CatCrypt images
  of AUCurves' `feval`-style decoders (`bn254_fp12_to_Z`, the G1/G2 coordinate
  readers), opaque.
* `bn254_optimal_ate_spec` / `bn254_fp12_mul_spec` — the field-level specs (Lean
  images of the AUCurves Rocq spec functions), opaque.
* `RocqTransport prims` — the proposition that `prims.pairing` and
  `prims.fp12Mul`, decoded to `Fp12`, equal the field-level specs on the decoded
  arguments.
* `eip197VerifyCom_denote_deployed` — the verifier at
  `pairingOracle deployedBn254Prims` computes the deployed byte product.
* `eip197VerifyCom_denote_of_rocqTransport` — under `RocqTransport prims`, the
  verifier at `pairingOracle prims`, decoded, is the product of the two
  optimal-ate pairings.

## Provenance of the transport hypothesis

`RocqTransport.pairing_correct` is the Lean statement of the AUCurves Rocq
theorem

    bn254_pairing_dsd_optimal_correct   (BN254_PairingCorrect.v, `Qed`)

whose bedrock2 WP spec is `bn254_fp12_to_Z out = bn254_optimal_ate_spec …`
(given the callee hypotheses `strong_loader_spec` / `strong_miller_spec` /
`strong_final_exp_spec`); see the §0 catalog in
`SecureCompilation/AUCurvesImport/FieldLeafBridge.lean:63`. The companion
`pairing_spec_compose` (`Qed`, same file) proves
`final_exp ∘ (corrections ∘ miller) = bn254_optimal_ate_spec`.
`RocqTransport.fp12Mul_correct` is the field-multiply spec of the AUCurves
`fp12_mul` byte kernel (the `Curve/BN254Curve_G1_BignumSpecs.v` Montgomery-mul
leaf, consumed by `BN254_PairingCorrect.v`).

Discharging `RocqTransport deployedBn254Prims` takes the Rocq proofs together
with two facts outside Lean: the decoders are the AUCurves layout readers, and
`bn254PairingLeaf` / `bn254Fp12MulLeaf` are the AUCurves `pairing_optimal` /
`fp12_mul` symbols the emit targets. The KAT (`bench/bn254_compare/`, published
EIP-196/EIP-197 vectors) checks computed byte results against the reference and
is independent of this hypothesis.
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

Each `opaque` below is the Lean image of a concrete AUCurves object. They are
uninterpreted; the only facts about them are the hypotheses of
`RocqTransport` (§3). -/

/-- The deployed BN254 pairing byte kernel `e(P, Q)` — the Lean image of the
    compiled AUCurves `pairing_optimal` (Miller loop + final exponentiation).
    Opaque. -/
noncomputable opaque bn254PairingLeaf :
    (Fin G1SZ → BitVec 8) → (Fin G2SZ → BitVec 8) → (Fin GTSZ → BitVec 8)

/-- The deployed BN254 GT (`Fp12`) multiply byte kernel — the Lean image of the
    compiled AUCurves `fp12_mul`. Opaque. -/
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

/-! ## 3. The transport hypothesis -/

/-- The AUCurves specs hold for the primitives `prims`: the pairing and the
    `Fp12` multiply, decoded to `Fp12`, equal the field-level specs on the
    decoded arguments. A theorem that needs these facts takes this proposition
    as a hypothesis. -/
structure RocqTransport (prims : Bn254Primitives) : Prop where
  /-- The pairing, decoded, is the optimal-ate spec on the decoded G1/G2
      arguments. AUCurves Rocq citation: `bn254_pairing_dsd_optimal_correct`
      (`BN254_PairingCorrect.v`, `Qed`); see `FieldLeafBridge.lean:63`. -/
  pairing_correct : ∀ (P : Fin G1SZ → BitVec 8) (Q : Fin G2SZ → BitVec 8),
    decodeGT (prims.pairing P Q) = bn254_optimal_ate_spec (decodeG1 P) (decodeG2 Q)
  /-- The `Fp12` multiply, decoded, is the `Fp12` product of the decoded
      arguments. AUCurves Rocq citation: the `fp12_mul` byte kernel's
      field-multiply spec (`Curve/BN254Curve_G1_BignumSpecs.v`, consumed by
      `BN254_PairingCorrect.v`; `FieldLeafBridge.lean:57,63`). -/
  fp12Mul_correct : ∀ (a b : Fin GTSZ → BitVec 8),
    decodeGT (prims.fp12Mul a b) = bn254_fp12_mul_spec (decodeGT a) (decodeGT b)

/-! ## 4. The deployed primitives -/

/-- The deployed BN254 primitives: the pairing / `Fp12`-multiply fields are the
    deployed byte kernels `bn254PairingLeaf` / `bn254Fp12MulLeaf`; the group
    fields are constant (the EIP-197 verifier does not call them). -/
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

/-- `pairingOracle deployedBn254Prims` realises the deployed primitives, by
    `pairingOracle_agrees`. -/
theorem deployedBn254Prims_leavesAgree :
    PairingLeavesAgree deployedBn254Prims (pairingOracle deployedBn254Prims) :=
  pairingOracle_agrees deployedBn254Prims

/-! ## 5. The EIP-197 verifier -/

/-- The deployed EIP-197 verifier at `pairingOracle deployedBn254Prims` computes
    the deployed byte product `fp12Mul (pairing P₁ Q₁) (pairing P₂ Q₂)`: the
    instance of `Bn254Emit.eip197VerifyCom_denote` at that oracle. -/
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

/-- Under `RocqTransport prims`, the EIP-197 verifier at `pairingOracle prims`,
    read back as an `Fp12` via `decodeGT`, computes the pairing product

        e(P₁,Q₁) · e(P₂,Q₂) = fp12_mul (ate P₁ Q₁) (ate P₂ Q₂)

    where `ate = bn254_optimal_ate_spec`. The precompile accepts iff this
    equals `1` in GT. -/
theorem eip197VerifyCom_denote_of_rocqTransport
    (prims : Bn254Primitives) (hT : RocqTransport prims)
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    decodeGT (@Com.denote _ _ _
        (JasminDialect.jasminDenoteWith (pairingOracle prims)) _ _
        Bn254Emit.eip197VerifyCom
        (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil)))))
      = bn254_fp12_mul_spec
          (bn254_optimal_ate_spec (decodeG1 p1) (decodeG2 q1))
          (bn254_optimal_ate_spec (decodeG1 p2) (decodeG2 q2)) := by
  rw [Bn254Emit.eip197VerifyCom_denote _ prims (pairingOracle_agrees prims),
    hT.fp12Mul_correct, hT.pairing_correct, hT.pairing_correct]

end CatCrypt.Crypto.Pairing.Bn254PairingTransport
