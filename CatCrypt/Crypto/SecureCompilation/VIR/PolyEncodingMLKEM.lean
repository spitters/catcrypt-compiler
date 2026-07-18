/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSound
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete `PolyEncoding 3329 256` for ML-KEM-768 (Stage F instance)

Stage F (`Optimizer/Lattice/NTTPolyMul_CompPolyConcrete.lean`) and the lattice
NTT-soundness file (`LatticeNTTSound.lean`) both carry the byte-layout decision
as a *parameter* — an abstract `enc : PolyEncoding q n R` plus a `Domain R`. This
file discharges the byte-layout half for ML-KEM-768 parameters
`(q, n) = (3329, 256)` over `R = ZMod 3329`, producing a **concrete**
`PolyEncoding 3329 256 (ZMod 3329)` with no remaining layout freedom, and then
instantiates the parametric agreement theorems at it.

## The byte layout (`mlkem768Encoding`)

`RustVal (.TPolyMod 3329 256)` is `Fin 512 → BitVec 8` (256 coefficients × 2
little-endian bytes; `⌈(Nat.log2 3329 + 1)/8⌉ = 2`). The encoding is:

* `decode v` : read the 512 bytes as 256 little-endian `u16` coefficients,
  reduce each into `ZMod 3329`, build a `CPolynomial.Raw` array, and `.trim` it
  to canonical form. Canonicality is `Raw.isCanonical_trim`.
* `encode p` : **negacyclic fold** of `p` mod `X^256 + 1` (see below), then
  write each of the 256 folded coefficients as two little-endian bytes.

`PolyEncoding` requires only that `encode`/`decode` *exist* (the round-trip
discipline is the consumer's, per the Stage-F structure docstring), so the
layout above fully determines a concrete instance.

## The negacyclic fold

ML-KEM works in `R[X]/(X^256 + 1)` (negacyclic), while CompPoly's cyclic
`Domain` / `fastMulImpl` computes the convolution in `R[X]` (truncated, i.e.
`X^N - 1` style). The Stage-F recipe folds the high half into the low half via
`X^256 ≡ -1`. We realise that fold inside `encode`:

  `foldedCoeff p i  =  Σ_{m < 2} (-1)^m · p.coeff (i + 256·m)`   (i < 256)

For the convolution of two degree-`<256` operands (degree `< 511`) the `m ∈
{0,1}` window is exact — coefficients of index `≥ 512` cannot appear. So
`encode` of any such product is the genuine `X^256 + 1` reduction.

## CompPoly friction: the radix-2 root-of-unity obstruction (honest scope)

Stage F's recipe also asks for a `Domain (ZMod 3329)` of cyclic size `≥ 2·256 =
512` so `Domain.fits` holds for the convolution. **No such domain exists.**
CompPoly's `Domain` is a *radix-2* NTT domain: `Domain.mk` demands
`IsPrimitiveRoot omega (2 ^ logN)`. The multiplicative group of `ZMod 3329` has
order `3328 = 2^8 · 13`, so its 2-adicity is `8`: primitive `2^logN`-th roots
exist only for `logN ≤ 8`, i.e. `Domain.n ≤ 256`. A full cyclic convolution of
two degree-`<256` polynomials needs length up to `511`, hence `Domain.n ≥ 512 =
2^9` — unattainable over `ZMod 3329`.

This is exactly why ML-KEM uses the **negacyclic incomplete NTT** mod
`X^256 + 1` with a 256th root of unity, *not* a 512-point cyclic NTT. CompPoly's
`fastMulImpl` delivers the cyclic product (mod `X^N - 1`), which is both the
wrong ring *and* unavailable at the required size over `ZMod 3329`.

Consequently the `Domain` parameter `D` and its `Domain.fits` witness **cannot
be eliminated** at these parameters: there is no closed `Domain (ZMod 3329)` to
plug in. We therefore keep `D` (and `hfits`) as hypotheses in the concrete
agreement theorem below; what is now concrete — and the genuinely-deferred work
this file closes — is the **byte layout** `mlkem768Encoding`. The agreement is
otherwise a one-line instantiation of the Stage-F transport through
`fastMulImpl_eq_mul`.

This obstruction is a property of the parameters, not a defect of either side;
it is the standard reason ML-KEM's reference NTT is the negacyclic incomplete
transform rather than a power-of-two cyclic one.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

set_option maxRecDepth 4000

open CompPoly (CPolynomial)
open CompPoly.CPolynomial.NTT (Domain)
open CatCrypt.Crypto.Jasmin.LowCT (RustVal TowerType)
open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul (PolyEncoding polyMul_leaf_agreement)

/-! ## 1. ML-KEM-768 parameters -/

/-- ML-KEM-768 modulus. -/
abbrev mlkemQ : Nat := 3329

/-- ML-KEM-768 polynomial degree bound (coefficient count). -/
abbrev mlkemN : Nat := 256

/-- `3329` is prime, so `ZMod 3329` is a field — required for `CPolynomial`'s
    `Field` instance and for `Domain`. -/
instance instFactPrime3329 : Fact (Nat.Prime 3329) := ⟨by native_decide⟩

/-- The concrete coefficient type. `ZMod 3329` is a finite field via Mathlib's
    `Field (ZMod p)` instance, synthesised from `instFactPrime3329`. -/
abbrev MLKEMField : Type := ZMod 3329

/-- Re-expose the `Field (ZMod 3329)` instance at the `MLKEMField` abbreviation
    head so that `[Field R]`-parameterised structures (`PolyEncoding`, `Domain`)
    resolve their instance argument when applied at `MLKEMField`. -/
instance instFieldMLKEMField : Field MLKEMField := inferInstanceAs (Field (ZMod 3329))

/-! ## 2. Byte ↔ coefficient conversion (little-endian, 2 bytes) -/

/-- Low byte of a coefficient (`val mod 256`). -/
def loByte (c : MLKEMField) : BitVec 8 := BitVec.ofNat 8 (c.val % 256)

/-- High byte of a coefficient (`val / 256`). Since `c.val < 3329 < 2^16`, the
    high byte is `< 14`, so it fits in 8 bits. -/
def hiByte (c : MLKEMField) : BitVec 8 := BitVec.ofNat 8 (c.val / 256)

/-- Reassemble a coefficient from two little-endian bytes, reducing mod `3329`. -/
def bytesToCoeff (lo hi : BitVec 8) : MLKEMField :=
  (((hi.toNat * 256 + lo.toNat : Nat) : MLKEMField))

/-! ## 3. The concrete encoding -/

/-- Read the `i`-th coefficient (`i < 256`) from a 512-byte `RustVal`, as a
    little-endian `u16` reduced into `ZMod 3329`. -/
def readCoeff (v : RustVal (.TPolyMod mlkemQ mlkemN)) (i : Nat) : MLKEMField :=
  if h : 2 * i + 1 < (TowerType.TPolyMod mlkemQ mlkemN).storageBytes then
    bytesToCoeff (v ⟨2 * i, Nat.lt_of_le_of_lt (Nat.le_succ _) h⟩) (v ⟨2 * i + 1, h⟩)
  else 0

/-- **Decode**: build the canonical `CPolynomial` whose `i`-th coefficient is the
    little-endian `u16` stored at bytes `2i, 2i+1` of `v`. -/
noncomputable def mlkemDecode (v : RustVal (.TPolyMod mlkemQ mlkemN)) :
    CPolynomial MLKEMField :=
  ⟨(CPolynomial.Raw.mk (Array.ofFn (fun i : Fin mlkemN => readCoeff v i.val))).trim,
    CompPoly.CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- The negacyclic fold of `p` mod `X^256 + 1`, evaluated at index `i < 256`:
    `Σ_{m < 2} (-1)^m · p.coeff (i + 256·m)`. The two-term window is exact for
    products of two degree-`<256` operands (degree `< 511`). -/
def foldedCoeff (p : CPolynomial MLKEMField) (i : Nat) : MLKEMField :=
  CompPoly.CPolynomial.coeff p i - CompPoly.CPolynomial.coeff p (i + mlkemN)

/-- Write the 512 bytes of a `RustVal` from the 256 negacyclically-folded
    coefficients of `p`, little-endian. Even bytes hold low halves, odd bytes
    high halves. Out-of-range indices (none, for `Fin 512`) map to `0`. -/
def mlkemEncode (p : CPolynomial MLKEMField) :
    RustVal (.TPolyMod mlkemQ mlkemN) :=
  fun b =>
    let i := b.val / 2
    if b.val % 2 = 0 then loByte (foldedCoeff p i) else hiByte (foldedCoeff p i)

/-- **The concrete ML-KEM-768 polynomial encoding.** Little-endian 2-byte
    coefficient packing on `decode`; negacyclic fold mod `X^256 + 1` followed by
    the same packing on `encode`. No remaining byte-layout freedom. -/
noncomputable def mlkem768Encoding : PolyEncoding mlkemQ mlkemN MLKEMField where
  encode := mlkemEncode
  decode := mlkemDecode

/-! ## 4. Concrete agreement theorem

We instantiate the Stage-F / `LatticeNTTSound` parametric agreement at
`mlkem768Encoding`. The `Domain` `D` and its `Domain.fits` witness remain
hypotheses: as the module docstring explains, no closed `Domain (ZMod 3329)` of
the required cyclic size exists (the radix-2 two-adicity of `ZMod 3329` is `8`,
capping `Domain.n` at `256 < 511`). The *byte layout* is what this file makes
concrete; the agreement is then a one-line transport through
`fastMulImpl_eq_mul`. -/

/-- **Concrete ML-KEM-768 leaf agreement** (byte-layout discharged). For any
    radix-2 NTT `Domain D` over `ZMod 3329` large enough for the decoded
    operands (`Domain.fits`), the *concrete* encoded NTT-backed product equals
    the *concrete* encoded canonical product, under the concrete
    `mlkem768Encoding` byte layout. This is `polyMul_leaf_agreement`
    instantiated at the concrete encoding — no longer parametric in the
    encoding.

    `D` and `hfits` stay as hypotheses because no closed `Domain (ZMod 3329)` of
    cyclic size `≥ 512` exists (see module docstring): the genuinely-deferred
    *byte-layout* step is what is closed here. -/
theorem mlkem768_polyMul_leaf_agreement
    (D : Domain MLKEMField)
    (a b : RustVal (.TPolyMod mlkemQ mlkemN))
    (hfits : Domain.fits D (mlkem768Encoding.decode a).val
      (mlkem768Encoding.decode b).val) :
    mlkem768Encoding.encode
        (CompPoly.CPolynomial.NTT.FastMul.fastMulImpl D
          (mlkem768Encoding.decode a) (mlkem768Encoding.decode b)) =
      mlkem768Encoding.encode
        (mlkem768Encoding.decode a * mlkem768Encoding.decode b) :=
  polyMul_leaf_agreement D mlkem768Encoding a b hfits

/-- **Concrete ML-KEM-768 NTT-multiply soundness** (byte-layout discharged).
    `LatticeNTTSound.polyEncoded_agrees_schoolbook` instantiated at
    `mlkem768Encoding`: under `Domain.fits`, the concrete encoded *real* NTT
    round-trip (`realNttMul` on the decoded operands) equals the concrete
    encoded schoolbook product. The lattice-dialect rewrite's soundness
    obligation, read at ML-KEM-768's concrete byte layout, reduces to CompPoly's
    convolution theorem `fastMulImpl_eq_mul`. -/
theorem mlkem768_polyEncoded_agrees_schoolbook
    (D : Domain MLKEMField)
    (a b : RustVal (.TPolyMod mlkemQ mlkemN))
    (hfits : Domain.fits D (mlkem768Encoding.decode a).val
      (mlkem768Encoding.decode b).val) :
    mlkem768Encoding.encode
        (realNttMul D (mlkem768Encoding.decode a) (mlkem768Encoding.decode b)) =
      mlkem768Encoding.encode
        (mlkem768Encoding.decode a * mlkem768Encoding.decode b) :=
  polyEncoded_agrees_schoolbook D mlkem768Encoding a b hfits

end CatCrypt.Crypto.SecureCompilation.VIR
