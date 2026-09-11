/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.CrossProverBridge

@[expose] public section

set_option autoImplicit false

/-!
# AUCurves → CatCrypt cross-prover **field-mul** leaf bridge

This file extends the AUCurves retarget's cross-prover edge
(`CrossProverBridge.lean`, the skip/seq/letZero/call/limbStore semantics
bridge) **down to the field-multiply leaves**.  Where `CrossProverBridge`
localizes the residual that AUCurves' Rocq big-step relation `rust_exec_ed`
agrees with CatCrypt's `RustExec` *structurally*, this file localizes the
residual that AUCurves' Rocq-proved **functional correctness of a field-mul
leaf** — that the leaf computes the field product `x · y` in `F p` (for
fe25519, the radix-2^51 schoolbook; for the Montgomery curves, the
word-by-word Montgomery product `x · y · R⁻¹ mod p`) — agrees with the
CatCrypt-side `LeafSpec` value the leaf-call oracle produces.

It follows the *exact* discipline of `CrossProverBridge` (`#368`): the
cross-prover statement is **not** a Lean theorem (it crosses Rocq↔Lean), so it
is a named, inhabited predicate (`§2`), bundled as a Catalog-style assumption
`structure` (`§3`), with a non-vacuous witness (`§3`) and a worked consumable
theorem (`§4`) showing it is usable as a hypothesis — the analogue of
`CrossProverCallBridge` / `cross_call_of_residual`.

## §0  The verified AUCurves field/curve catalog (cited Rocq theorems)

Every entry below was confirmed by reading the AUCurves `.v` source.  Where a
file records its `Print Assumptions` status, that is noted; where the result is
**axiomatized** in Rocq (with independent external validation), that is stated
explicitly so the catalog is honest about which leaves are kernel-`Qed`'d.

### Field-multiply / field-op leaves (curve25519 / Ed25519)

| Rocq theorem                  | File                                          | Computes / status |
|-------------------------------|-----------------------------------------------|-------------------|
| `fe25519_mul_body_correct`    | `End2End/Ed25519/Fe25519MulCorrect.v`         | `Fp25519_holds rs2 dest (F.mul xa xb)` — `Qed`. Section-parametric over the abstract decoder `feval`, the slot predicate `Fp25519_holds`, and the algebraic hypothesis `feval_limbwise_mul_mask64` (the radix-2^51 mask64 schoolbook decodes to `F.mul`); no new GLOBAL axioms (the file ends `Print Assumptions fe25519_mul_body_correct`). |
| `fe25519_square_body_correct` | `End2End/Ed25519/Fe25519SquareCorrect.v`      | `F.mul xa xa` — `Qed`, same section-parametric shape (companion to the mul file). |
| `fe25519_add_body_correct` / `fe25519_sub_body_correct` | `End2End/Ed25519/Fe25519AddSubCorrect.v` | `F.add` / `F.sub` — `Qed` (the A31 base the mul file mirrors). |
| `fe25519_carry_body_correct`  | `End2End/Ed25519/Fe25519CarryCorrect.v`       | carry-reduction to canonical limbs — `Qed`. |

### Montgomery field-multiply leaves (secp256k1 / P256 / BN254 / BLS12)

These wrap **fiat-crypto's** WP-proven word-by-word-Montgomery field
multiply.  AUCurves *consumes* (does not re-prove) the fiat-crypto theorem and
re-states it in its `Bignum`/`valid` style:

| fiat-crypto theorem (consumed) | AUCurves bridge file                       | Computes |
|--------------------------------|--------------------------------------------|----------|
| `secp256k1_mul_correct`        | `Curve/Secp256k1_Bignum_Specs.v` (imports `Crypto.Bedrock.Secp256k1.Field256k1`) | `x · y · R⁻¹ mod (2^256−2^32−977)` (WBW-Montgomery) |
| (P256 WBW mul)                 | `Curve/P256_Bignum_Specs.v`                | `x · y · R⁻¹ mod p256` |
| (BN254 `bn254_mul`)            | `Curve/BN254Curve_G1_BignumSpecs.v`, used by `BN254_PairingCorrect.v` | `x · y · R⁻¹ mod bn254_p` |

### Pairing / MSM end-to-end leaves (citable, NOT field-mul shaped)

| Rocq theorem                          | File                          | Status |
|---------------------------------------|-------------------------------|--------|
| `bn254_pairing_dsd_optimal_correct`   | `BN254_PairingCorrect.v`      | `Qed`. bedrock2 WP spec: `bn254_fp12_to_Z out = bn254_optimal_ate_spec …` given strong callee hypotheses (`strong_loader_spec` / `strong_miller_spec` / `strong_final_exp_spec`). |
| `pairing_spec_compose`                | `BN254_PairingCorrect.v`      | `Qed`. `final_exp ∘ (corrections ∘ miller) = bn254_optimal_ate_spec`. |
| BLS12 pairing/MSM closures            | `BLS12_PairingRustConcrete.v`, `BLS12_MSM*.v`, `SafeRustBLS12Concrete.v` | bedrock2/Rust-concrete closures (cited as available; not transcribed here). |

### Half-safegcd divstep certificates (the safegcd-perf story) — **AXIOMATIZED**

The half-divstep convergence certificates are the proven half-divstep variants
relevant to the safegcd modular-inverse performance story (10 outer × 59
divsteps, matching libsecp256k1's `modinv64`).  **They are recorded in Rocq as
`Axiom`s, not `Qed`'d** (the `N.iter 590 …` term is too large to kernel-check;
the same certificate is independently validated in OCaml via
`Arithmetic/safegcd/multi_curve_driver`).  This is stated here so the catalog is
honest about kernel status:

| Rocq object (verified by reading the file)       | File                                      | Status |
|--------------------------------------------------|-------------------------------------------|--------|
| `Axiom p256_half_certificate` (N = 590)          | `Arithmetic/safegcd/divsteps_p256_half.v` | **Axiom** (OCaml-cert-validated) |
| `Axiom secp256k1_half_certificate` (N = 590)     | `Arithmetic/safegcd/divsteps_secp256k1_half.v` | **Axiom** (OCaml-cert-validated) |
| `Axiom p256_certificate` (N = 741, full)         | `Arithmetic/safegcd/divsteps_p256.v`      | **Axiom** (OCaml-cert-validated) |
| `Axiom secp256k1_certificate` (N = 741, full)    | `Arithmetic/safegcd/divsteps_secp256k1.v` | **Axiom** (OCaml-cert-validated) |

### SM2 is NOT in AUCurves

There is **no** SM2 field/curve in AUCurves: no `sm2_*` source, no SM2 prime,
no SM2 field-mul correctness.  Any SM2 leaf on the CatCrypt side has *no*
AUCurves cross-prover anchor and must not claim one.
-/

namespace CatCrypt.Crypto.SecureCompilation.AUCurvesImport

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The field-mul leaf parameters

A field-mul leaf is identified by:

* `fname` — the leaf's function name (e.g. `"fe25519_mul"`, `"secp256k1_mul"`);
* `dt`    — the destination `TowerType` (the field-element representation, e.g.
  `TFp25519`, or a `TBytes`-backed Montgomery limb tuple);
* the CatCrypt `LeafSpec` whose `call` oracle gives the leaf's post-value.

To state "computes `x · y` in `F p`" we also need a *decoder* — the CatCrypt
image of AUCurves' abstract `feval : list Z → F p` — projecting a `RustVal dt`
slot to a residue in `ZMod modulus` (`modulus = p` for the schoolbook leaf, or
`p` with the values already in Montgomery domain for the WBW leaf).  We keep the
decoder abstract (a parameter), exactly as AUCurves keeps `feval` a section
`Variable`: the bridge says the two decoders *agree on the leaf's output*, it
does not fix a particular `feval`. -/

/-- A curve-specific field-mul leaf bundle: the leaf name, its destination
    `TowerType`, the modulus `p` of the field, and the abstract decoder
    `decode : RustVal dt → ZMod modulus` (the CatCrypt image of AUCurves'
    `feval`). -/
structure FieldMulLeaf where
  /-- The leaf-function name, e.g. `"fe25519_mul"`. -/
  fname   : String
  /-- The destination field-element `TowerType`. -/
  dt      : TowerType
  /-- The field modulus `p` (e.g. `2^255 - 19`, `2^256 - 2^32 - 977`). -/
  modulus : Nat
  /-- The abstract field decoder, the CatCrypt image of AUCurves' `feval`. -/
  decode  : RustVal dt → ZMod modulus

/-! ## §2  The named cross-prover field-mul bridge predicate

`FieldMulSpecAgrees leaf leafSpec` is the precise statement of the cross-prover
edge.  It mirrors `CrossProverBridge.CallBridge`'s shape: a `Prop` over the
opaque CatCrypt `leafSpec.call` value of the leaf, asserting it decodes to the
AUCurves-Rocq-proved field product.

In words (for the curve25519 instance): for any two field-element argument
slots `xa`, `xb` whose decoded residues are `da`, `db`, the value the CatCrypt
leaf-call oracle produces for `leaf.fname` decodes via `leaf.decode` to the
field product `da · db` — which is exactly the post-value AUCurves'
`fe25519_mul_body_correct` proves (`F.mul xa xb`, transcribed to `ZMod`
multiplication).  The `oldDest`/arg-type plumbing matches `CallSpec`'s shape so
the predicate composes with `RustExec.call` / `cross_call`. -/

/-- **Named cross-prover field-mul bridge (analogue of `CallBridge`).**

    `FieldMulSpecAgrees leaf leafSpec` says: the CatCrypt `leafSpec.call`
    oracle, applied at the leaf `leaf.fname` to two field-element arguments
    `xa`, `xb` (in slots typed `leaf.dt`), produces a destination value whose
    decoded residue equals the field product `leaf.decode xa * leaf.decode xb`
    in `ZMod leaf.modulus`.

    This is the CatCrypt-side image of AUCurves' Rocq-proved field-mul
    correctness (`fe25519_mul_body_correct` for curve25519, the consumed
    `secp256k1_mul_correct` for secp256k1).  It is **not** a Lean theorem: the
    fact that `leafSpec.call`'s opaque value coincides with AUCurves' proved
    output is a cross-prover claim, named here rather than asserted. -/
def FieldMulSpecAgrees (leaf : FieldMulLeaf) (leafSpec : LeafSpec) : Prop :=
  ∀ (xa xb : RustVal leaf.dt) (oldDest : RustVal leaf.dt),
    leaf.decode
        (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
          [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩])
      = leaf.decode xa * leaf.decode xb

/-! ## §3  The Catalog-style named assumption + non-vacuous witness

As in `CrossProverBridge.§5`, we promote the predicate to a `structure … :
Prop` carrying it as its single field, so a downstream theorem that takes a
`AUCurvesFieldMulBridge leaf leafSpec` value genuinely *assumes* the edge, in
the `CrossProverCallBridge` / ZKSoundness discipline. -/

/-- **Named assumption: the AUCurves cross-prover field-mul bridge.**

    Bundles `FieldMulSpecAgrees leaf leafSpec` (the CatCrypt leaf-call value
    decodes to the AUCurves-Rocq-proved field product) as a Catalog-style
    assumption object, mirroring `CrossProverCallBridge`.

    Holding a value of this structure is *assuming* that AUCurves' Qed'd
    field-mul correctness (`fe25519_mul_body_correct`, …) is faithfully
    realized by the CatCrypt `leafSpec.call` oracle for this leaf — the honest,
    named cross-prover edge, never a bare `axiom` bolted onto a different
    hand-written kernel. -/
structure AUCurvesFieldMulBridge (leaf : FieldMulLeaf) (leafSpec : LeafSpec) :
    Prop where
  /-- The field-mul spec agreement holds for this leaf (see
      `FieldMulSpecAgrees`). -/
  specAgrees : FieldMulSpecAgrees leaf leafSpec

/-- The canonical `LeafSpec.call` oracle realizing a given field-mul leaf: at
    the target `fname`/`dt` it ignores `oldDest`, decodes the *two* positional
    arguments (when they are present and typed `dt`), multiplies their residues
    in `ZMod modulus`, and re-encodes via a supplied section `encode` back into
    a `RustVal dt` slot.  Off-target it is the identity (returns `oldDest`).

    This is the trivial-but-typed instantiation confirming `FieldMulSpecAgrees`
    is satisfiable — the analogue of `canonicalLimbWrite` for
    `limbWriteBridge`. -/
def fieldMulCallSpec (leaf : FieldMulLeaf)
    (encode : ZMod leaf.modulus → RustVal leaf.dt) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if _hf : fname = leaf.fname then
      -- read the two positional arguments; recover a `RustVal leaf.dt` from
      -- each dependent pair when the stored type matches `leaf.dt`.
      let pick : (Σ t : TowerType, RustVal t) → ZMod leaf.modulus := fun a =>
        if ht : a.1 = leaf.dt then leaf.decode (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          -- the destination slot type is `oldDest`'s type; the canonical
          -- witness is only consulted at the target leaf where it is `leaf.dt`
          -- by construction (see `fieldMulSpecAgrees_canonical`).
          if hd : _dt = leaf.dt then
            hd ▸ encode (pick a * pick b)
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuous witness for `FieldMulSpecAgrees`.**  For the canonical
    `LeafSpec` built from `fieldMulCallSpec leaf encode` with a decoder section
    `encode` (`leaf.decode ∘ encode = id`), the field-mul spec agreement holds —
    confirming the predicate is the *right* shape (an inhabited cross-prover
    claim), not an unsatisfiable over-constraint.  The genuine cross-prover
    content is precisely the gap between this canonical realizer and AUCurves'
    actual Rocq-proved oracle, which lives outside Lean. -/
theorem fieldMulSpecAgrees_canonical (leaf : FieldMulLeaf)
    (encode : ZMod leaf.modulus → RustVal leaf.dt)
    (hsection : ∀ z : ZMod leaf.modulus, leaf.decode (encode z) = z)
    (limbStore : LimbStoreSpec) :
    FieldMulSpecAgrees leaf
      { call := fieldMulCallSpec leaf encode, limbStore := limbStore } := by
  intro xa xb oldDest
  simp only [fieldMulCallSpec, dif_pos, hsection]

/-- **Non-vacuous witness for the bundled assumption.**  Packages the canonical
    realizer as an inhabitant of `AUCurvesFieldMulBridge`, the analogue of
    `crossProverResidual_canonical` confirming the named assumption is genuine,
    not vacuous. -/
theorem aucurvesFieldMulBridge_canonical (leaf : FieldMulLeaf)
    (encode : ZMod leaf.modulus → RustVal leaf.dt)
    (hsection : ∀ z : ZMod leaf.modulus, leaf.decode (encode z) = z)
    (limbStore : LimbStoreSpec) :
    AUCurvesFieldMulBridge leaf
      { call := fieldMulCallSpec leaf encode, limbStore := limbStore } where
  specAgrees := fieldMulSpecAgrees_canonical leaf encode hsection limbStore

/-! ## §4  The bridge is consumable (worked theorem)

To show `AUCurvesFieldMulBridge` is *usable as an explicit hypothesis* — not
just a label — we record the canonical conclusion it supports, in the
`cross_call_of_residual` discipline: given the named field-mul assumption, the
CatCrypt leaf-call value *provably decodes to the field product*.  This is the
consumable cross-prover edge: a downstream theorem can now assume
`AUCurvesFieldMulBridge curve25519Fe25519Mul leafSpec` and conclude the
`fe25519_mul` leaf computes `x · y` in `ZMod (2^255 − 19)`. -/

/-- **The field-mul bridge is consumable.**  Given the named assumption
    `AUCurvesFieldMulBridge leaf leafSpec`, the CatCrypt leaf-call value for
    `leaf.fname` on field-element arguments `xa`, `xb` decodes to the field
    product `leaf.decode xa * leaf.decode xb` — AUCurves' Rocq-proved spec,
    consumed as a CatCrypt fact. -/
theorem fieldMul_value_of_bridge
    {leaf : FieldMulLeaf} {leafSpec : LeafSpec}
    (h : AUCurvesFieldMulBridge leaf leafSpec)
    (xa xb oldDest : RustVal leaf.dt) :
    leaf.decode
        (leafSpec.call leaf.fname leaf.dt [leaf.dt, leaf.dt] oldDest
          [⟨leaf.dt, xa⟩, ⟨leaf.dt, xb⟩])
      = leaf.decode xa * leaf.decode xb :=
  h.specAgrees xa xb oldDest

/-! ## §5  Curve instances

We instantiate `FieldMulLeaf` for the curves AUCurves actually proves, citing
the verified Rocq theorem for each (see the §0 catalog).  The decoder is left
abstract (a parameter), exactly as AUCurves keeps `feval` a section variable —
the bridge says the two decoders agree on the leaf output, it does not pin a
particular `feval`. -/

/-- **curve25519 / Ed25519 `fe25519_mul` leaf.**  Cites
    `fe25519_mul_body_correct` (`AUCurves/src/Bedrock/End2End/Ed25519/`
    `Fe25519MulCorrect.v`, `Qed`): the body computes `F.mul xa xb` in
    `F (2^255 − 19)`.  Destination slot type `TFp25519` (the radix-2^51
    5-limb representation); `decode` is the CatCrypt image of the file's
    abstract `feval : list Z → F p`. -/
def curve25519Fe25519Mul (decode : RustVal .TFp25519 → ZMod (2 ^ 255 - 19)) :
    FieldMulLeaf where
  fname   := "fe25519_mul"
  dt      := .TFp25519
  modulus := 2 ^ 255 - 19
  decode  := decode

/-- **secp256k1 `secp256k1_mul` leaf.**  Cites `secp256k1_mul_correct` (the
    fiat-crypto WP-proved word-by-word-Montgomery field multiply, consumed by
    `AUCurves/src/Bedrock/Curve/Secp256k1_Bignum_Specs.v` via
    `Crypto.Bedrock.Secp256k1.Field256k1`): the leaf computes
    `x · y · R⁻¹ mod (2^256 − 2^32 − 977)` in the Montgomery domain.  The
    destination slot is the 4-limb / 256-bit field element (`TBytes 32`);
    `decode` is the CatCrypt image of AUCurves' `feval = F.of_Z (eval (from_mont
    …))`. -/
def secp256k1Mul (decode : RustVal (.TBytes 32) → ZMod (2 ^ 256 - 2 ^ 32 - 977)) :
    FieldMulLeaf where
  fname   := "secp256k1_mul"
  dt      := .TBytes 32
  modulus := 2 ^ 256 - 2 ^ 32 - 977
  decode  := decode

/-- The two instances are well-formed leaves carrying their cited moduli (a
    sanity check that the instantiations type-check against `FieldMulLeaf`). -/
theorem curve25519Fe25519Mul_modulus
    (decode : RustVal .TFp25519 → ZMod (2 ^ 255 - 19)) :
    (curve25519Fe25519Mul decode).modulus = 2 ^ 255 - 19 := rfl

theorem secp256k1Mul_modulus
    (decode : RustVal (.TBytes 32) → ZMod (2 ^ 256 - 2 ^ 32 - 977)) :
    (secp256k1Mul decode).modulus = 2 ^ 256 - 2 ^ 32 - 977 := rfl

end CatCrypt.Crypto.SecureCompilation.AUCurvesImport
