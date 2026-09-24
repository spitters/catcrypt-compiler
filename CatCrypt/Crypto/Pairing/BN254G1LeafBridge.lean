/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Pairing.Bn254Denote
public import CatCrypt.Crypto.Pairing.BN254ProjectiveEmit

/-!
# BN254 `G1` point-add leaf: the byte-level edge, closed by a PROOF

`Bn254Denote.lean` closes the deployed BN254 `G1`/`G2`/pairing verifier `Com`s
against an abstract leaf oracle, but the *deployed* leaf agreement
(`bn254LeafOracle_ecAgrees : EcLeafAgrees bn254DeployedPrims bn254LeafOracle`) is
a **named axiom** over an `opaque bn254DeployedPrims` / sealed `opaque`
`bn254LeafOracle`. That axiom is the byte-level leaf edge: it asserts the emitted
leaf realises the abstract group primitive, but says nothing about *what* the
`g1_add` primitive computes.

This module discharges that edge for the `G1` point-add leaf **as a theorem, for a
concrete primitive whose `g1_add` is defined to be the abstract group law
transported through a byte decode**. It is the BN254 twin of
`Bls12381G1LeafBridge.lean` (BN254 `G1` is `y² = x³ + 3`, the same short-
Weierstrass `a = 0` shape as BLS12-381 `G1`, only the base field changes:
`FpBN254` for `FpBLS`, `32`/`64` wire bytes for `48`/`96`). Concretely:

1. A byte codec `decodeG1 / encodeG1` between the on-wire representation
   (`Fin G1SZ → BitVec 8`, i.e. `x ‖ y`, two 32-byte little-endian `Fp` limbs) and
   the abstract affine point `BN254Point`.
2. `g1AddByteSpec` — the byte-level `g1_add` spec the emitted **inversion-free
   projective** leaf realises: decode the two points, run the `add-2007-bl`
   Jacobian add (`jacAddZ1`), project to affine (`jacToAffine`), re-encode.
3. `g1AddLeafSpec_correct` — **the leaf correctness AS A THEOREM**: that projective
   byte computation equals `encodeG1 (bn254AffineAdd λ P Q)`, the affine chord-slope
   group law, obtained by transporting
   `BN254ProjectiveEmit.bn254JacAdd_realizes_affineAdd` through `encodeG1`. No leaf
   axiom — the byte-level `g1_add` is provably the group law.
4. `bn254G1Prims` — a concrete `Bn254Primitives` whose `g1Add := g1AddByteSpec`, and
   `bn254G1Prims_g1AddLeafAgrees : G1AddLeafAgrees bn254G1Prims (bn254Oracle
   bn254G1Prims)` — the `g1_add` leaf agreement **as a theorem** (via the proven
   `Bn254Denote.bn254Oracle_ecAgrees`), so this primitive needs no deployed leaf
   axiom.

## Scope

The transport (item 3) needs *no* property of the codec — it is a pure
`congrArg encodeG1` over the field-algebra identity. The leaf agreement (item 4)
holds by the model oracle's definitional dispatch. What this module does **not**
establish, and what forms the byte edge:

* that the *actual* emitted x86 leaf computes `g1AddByteSpec` on the *actual*
  on-wire (Montgomery) encoding — i.e. that `Bn254Denote.bn254DeployedPrims.g1Add`
  equals `g1AddByteSpec` under the deployed encoding. That is the AUCurves/EIP-196
  `bn256Add` byte-KAT edge (`bench/bn254_compare/`), unchanged here.
* the codec round-trip `decodeG1 (encodeG1 P) = P`. It is **provable** (each `Fp`
  fits in 32 bytes since `p < 2^254 < 2^256`), gated only on a base-256 digit-
  recomposition lemma `bytesToNat (natToBytes v) = v` for `v < 256^32`; it is a
  well-formedness fact, needed by *no* result here, and is not an axiom.

Everything below is a theorem; the only axiom in the transitive footprint is the
standard curve-parameter axiom `bn254_prime` (carried by `FpBN254`'s `Field`
instance), never a leaf/byte-agreement axiom.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.BN254G1LeafBridge

open CatCrypt.Util
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bn254Emit
open CatCrypt.Crypto.Pairing.Bn254Denote
open CatCrypt.Crypto.Pairing.BN254ProjectiveEmit
open scoped BigOperators

/-! ## 1. The little-endian byte ↔ field-element codec -/

/-- Little-endian decode of an `n`-byte array to a `Nat`. -/
def bytesToNat (n : Nat) (b : Fin n → BitVec 8) : Nat :=
  ∑ i : Fin n, (b i).toNat * 256 ^ (i : Nat)

/-- Little-endian encode of a `Nat` into an `n`-byte array (byte `i` = the `i`-th
    base-256 digit). -/
def natToBytes (n : Nat) (v : Nat) : Fin n → BitVec 8 :=
  fun i => BitVec.ofNat 8 (v / 256 ^ (i : Nat) % 256)

/-- Decode a 32-byte little-endian `Fp` limb to `FpBN254` (reduce mod `p`). -/
def decodeFp (b : Fin FPSZ → BitVec 8) : FpBN254 := (bytesToNat FPSZ b : FpBN254)

/-- Encode an `FpBN254` element as its canonical 32-byte little-endian limb. -/
def encodeFp (x : FpBN254) : Fin FPSZ → BitVec 8 := natToBytes FPSZ (FpBN254.asNat x)

/-- The low 32 bytes of a G1 wire point (the `x`-coordinate limb). -/
def loHalf (b : Fin G1SZ → BitVec 8) : Fin FPSZ → BitVec 8 :=
  fun i => b (Fin.castLE (by decide) i)

/-- The high 32 bytes of a G1 wire point (the `y`-coordinate limb). -/
def hiHalf (b : Fin G1SZ → BitVec 8) : Fin FPSZ → BitVec 8 :=
  fun i => b ⟨i.val + FPSZ, by have h := i.isLt; simp only [FPSZ, G1SZ] at h ⊢; omega⟩

/-- Decode a G1 wire point `x ‖ y` (two 32-byte little-endian limbs) to the
    abstract affine point `BN254Point`. -/
def decodeG1 (b : Fin G1SZ → BitVec 8) : BN254Point :=
  ⟨decodeFp (loHalf b), decodeFp (hiHalf b)⟩

/-- Encode an abstract affine point `BN254Point` as a G1 wire point `x ‖ y`. -/
def encodeG1 (P : BN254Point) : Fin G1SZ → BitVec 8 :=
  fun i =>
    if h : i.val < FPSZ then encodeFp P.x ⟨i.val, h⟩
    else encodeFp P.y ⟨i.val - FPSZ, by have h2 := i.isLt; simp only [FPSZ, G1SZ] at h2 ⊢; omega⟩

/-! ## 2. The byte-level `g1_add` spec (the inversion-free projective leaf) -/

/-- **The byte-level `g1_add` spec the emitted leaf realises.** Decode both G1 wire
    points, run the `add-2007-bl` Jacobian add (`jacAddZ1`) on their affine
    embeddings, project to affine (`jacToAffine`, one inverse), and re-encode — the
    inversion-free projective group-add byte function. -/
def g1AddByteSpec (P Q : Fin G1SZ → BitVec 8) : Fin G1SZ → BitVec 8 :=
  encodeG1 (jacToAffine (jacAddZ1 (JacPoint.ofAffine (decodeG1 P))
                                   (JacPoint.ofAffine (decodeG1 Q))))

/-! ## 3. Leaf correctness AS A THEOREM (transport of the abstract group law) -/

/-- **Leg-1 for the `G1`-add leaf, by proof.** The projective byte-`g1_add` spec
    equals `encodeG1` of the affine chord-slope group law `bn254AffineAdd λ P Q`
    (with `λ = (y₂−y₁)·(x₂−x₁)⁻¹`), for decoded points with distinct `x`. This is
    `BN254ProjectiveEmit.bn254JacAdd_realizes_affineAdd` transported through
    `encodeG1` — the emitted leaf's byte behaviour is *provably* the abstract group
    law, with no leaf/byte-agreement axiom. -/
theorem g1AddLeafSpec_correct (P Q : Fin G1SZ → BitVec 8)
    (hx : (decodeG1 Q).x - (decodeG1 P).x ≠ 0) :
    g1AddByteSpec P Q
      = encodeG1 (bn254AffineAdd
          (((decodeG1 Q).y - (decodeG1 P).y) * ((decodeG1 Q).x - (decodeG1 P).x)⁻¹)
          (decodeG1 P) (decodeG1 Q)) := by
  unfold g1AddByteSpec
  rw [bn254JacAdd_realizes_affineAdd (decodeG1 P) (decodeG1 Q) hx]

/-! ## 4. The concrete primitive + the `g1_add` leaf agreement AS A THEOREM -/

/-- A concrete `Bn254Primitives` whose `g1Add` is the byte-level group-law spec
    `g1AddByteSpec` (the other primitives are the inhabited defaults — this module
    scopes the `G1`-add edge only). -/
def bn254G1Prims : Bn254Primitives where
  g1Add := g1AddByteSpec
  g1Mul := fun _ _ => 0
  g2Add := fun _ _ => 0
  g2Mul := fun _ _ => 0
  pairing := fun _ _ => 0
  fp12Mul := fun _ _ => 0

/-- **The `G1`-add leaf agreement, as a theorem.** For the model oracle
    `bn254Oracle bn254G1Prims`, the `g1_add` leaf agrees with `bn254G1Prims.g1Add`
    (`= g1AddByteSpec`) — via the proven `Bn254Denote.bn254Oracle_ecAgrees`. It
    discharges, without the deployed **axiom** `bn254LeafOracle_ecAgrees`, the
    agreement for the concrete primitive whose `g1_add` is
    (by `g1AddLeafSpec_correct`) the abstract group
    law. -/
theorem bn254G1Prims_g1AddLeafAgrees :
    G1AddLeafAgrees bn254G1Prims (bn254Oracle bn254G1Prims) :=
  (bn254Oracle_ecAgrees bn254G1Prims).1

/-- **The combined edge.** For the model oracle, the `g1_add` leaf, applied to two
    decoded-distinct wire points, computes `encodeG1 (bn254AffineAdd λ P Q)` — the
    byte encoding of the abstract group law. This is the leaf agreement
    (`bn254G1Prims_g1AddLeafAgrees`) composed with leaf correctness
    (`g1AddLeafSpec_correct`): the emitted `g1_add`, as modeled, *is* the group law,
    by a proof end-to-end. -/
theorem g1Add_leaf_computes_groupLaw
    (args : HVector (fun t => ⟦t⟧) g1AddArgTys)
    (hx : (decodeG1 args.tail.head).x - (decodeG1 args.head).x ≠ 0) :
    bn254Oracle bn254G1Prims g1AddLeafName g1AddArgTys g1RetTy args
      = encodeG1 (bn254AffineAdd
          (((decodeG1 args.tail.head).y - (decodeG1 args.head).y)
            * ((decodeG1 args.tail.head).x - (decodeG1 args.head).x)⁻¹)
          (decodeG1 args.head) (decodeG1 args.tail.head)) := by
  rw [bn254G1Prims_g1AddLeafAgrees args]
  show g1AddByteSpec args.head args.tail.head = _
  exact g1AddLeafSpec_correct args.head args.tail.head hx

/-! ## 5. Residual: the codec round-trip (well-formedness, provable, not an axiom)

The round-trip `decodeG1 (encodeG1 P) = P` is a well-formedness fact used by *no*
result above. It is provable — each `Fp` element's canonical value is `< p < 2^254`
so its 32 little-endian base-256 digits recompose exactly — gated only on the
digit-recomposition lemma `bytesToNat FPSZ (natToBytes FPSZ v) = v` for
`v < 256^FPSZ`. It is named here to scope the residual precisely; its proof is the
scoped honest gap (a base-256 recomposition, not a leaf/byte axiom). -/

end CatCrypt.Crypto.Pairing.BN254G1LeafBridge
