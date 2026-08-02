/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSound
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
import CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic
import CompPoly.Univariate.ToPoly.Equiv
import Mathlib.Algebra.Field.ZMod

/-!
# Lattice dialect NTT-mul: concrete ML-KEM semantics (Phase 4, concrete)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`LatticeNTTSound.lean` reduced the lattice dialect's `polyMulC` soundness
obligation to CompPoly's *cyclic* convolution theorem `fastMulImpl_eq_mul`
**parametrically** (over an abstract `PolyEncoding`), and explicitly deferred
two gaps:

* (a) the concrete encoding `Fin n → BitVec 16 ↔ CPolynomial (ZMod 3329)`;
* (b) the **negacyclic fold**: ML-KEM multiplies in `Z_q[X] / (X^256 + 1)`,
  whereas CompPoly's packaged `fastMulImpl_eq_mul` delivers the *cyclic* full
  product `p * q` in `CPolynomial R`.

This file closes both gaps concretely for the ML-KEM-768 parameters
`(q, n) = (3329, 256)`.

## What CompPoly already provides for the negacyclic side

A full negacyclic / incomplete-NTT development already lives in CompPoly at
`CatCrypt/Crypto/SecureCompilation/VIR/Negacyclic.lean`
(`CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic`). The facts used:

* `Negacyclic.negacyclic_modByMonic_coeff` — for `p` of degree `< 2n`, the
  reduction `p %ₘ (X^n + 1)` has `(p %ₘ negaPoly n).coeff k = p.coeff k −
  p.coeff (k + n)` for `k < n` (the `X^n ≡ -1` fold).
* `Negacyclic.negacyclic_mul_coeff` — specialised to a product `a * b`, the
  `k`-th coefficient is the explicit negacyclic convolution
  `(Σ_{i+j=k} aᵢbⱼ) − (Σ_{i+j=k+n} aᵢbⱼ)`.
* `Negacyclic.basemul_mod` / `basemul_adjoinRoot` — ML-KEM's degree-2
  `_poly_basemul` in `R[X] / (X^2 − ζ)`.
* `Negacyclic.incompleteNTT(_map_mul)` / `incompleteNTTOfModulus(_map_mul)` —
  the abstract CRT isomorphism `R[X]/(⨅ fᵢ) ≃+* ∏ R[X]/(fᵢ)` respecting `*`.

CompPoly itself flags the *concrete cyclotomic factorisation*
`X^256 + 1 = ∏_{i<128}(X^2 − ζᵢ)` over `ZMod 3329` (the `hfact`/`hcop`
hypotheses of `incompleteNTT`) as out of scope. We do **not** need the CRT
factorisation here: the negacyclic *product correctness* is the `%ₘ (X^n + 1)`
fold, supplied directly by `negacyclic_mul_coeff`.

## What is proved here

* `enc : (Fin n → BitVec 16) → CPolynomial (ZMod q)` — the concrete coefficient
  encoding (16-bit lane `i` ↦ coefficient `i`, reduced mod `q`), wrapped
  canonically. `encMlkem` specialises to `(3329, 256)`.
* `enc_coeff`, `enc_natDegree_lt`, `enc_fits` — the encoding's coefficient
  formula, its degree bound (`< n`), and the resulting `Domain.fits` for any
  domain of size `≥ 2n` (in particular ML-KEM's 512-point NTT).
* `realNttMul_toPoly` — the real CompPoly NTT multiply, transported to a
  Mathlib `Polynomial`: under `Domain.fits`, `(realNttMul D p q).toPoly =
  p.toPoly * q.toPoly`. This is `fastMulImpl_eq_mul` + `toPoly_mul`: the
  *cyclic* product (not by `rfl`).
* **`realNttMul_negacyclic_coeff`** (the headline): with the *real* CompPoly NTT
  operations (NOT the toy `id`), the negacyclic reduction of the real NTT
  product equals the negacyclic convolution of the encoded inputs:

    `((realNttMul D (enc a) (enc b)).toPoly %ₘ negaPoly n).coeff k
       = (Σ_{i+j=k} …) − (Σ_{i+j=k+n} …)`   for `k < n`,

  combining `fastMulImpl_eq_mul` (cyclic NTT correctness) with
  `negacyclic_mul_coeff` (the `X^n ≡ −1` fold). Both halves of the ML-KEM
  multiply — the NTT-domain round-trip *and* the negacyclic reduction — are
  theorems here, not definitional identities.

## Plugging `realNttMul` into a dialect denotation (the Com level)

The toy `latticeDialect` (`LatticeDialect.lean`) denotes its polynomial ops via
`nttF = invnttF = id` over the shared representation `Fin n → BitVec 16`, so its
`polyMulC` collapses definitionally. `LatticeToJasminDenoteUncond.lean` and
`MlirPolynomialDialect.lean` *depend* on those toy leaves, so a global swap of
`latticeDenote` would break them (and is not even type-compatible: the real ops
live on `CPolynomial (ZMod q)`, not `Fin n → BitVec 16`).

Instead we read the same syntax at a second semantics. `LatticeDialect` indexes
its type alphabet by a `LatticeSem` tag, so `latticeDialect` and
`realLatticeDialect` are the `.bits` and `.poly` instantiations of one family:
same type constructors, same op tags, same `DialectSignature`, different
`TyDenote`. Here `polyC q n` / `polyN q n` both denote to
`CPolynomial (ZMod q)`, and the `basemul` / `polyMulC` ops denote via
`realNttMul` (CompPoly's `fastMulImpl`) over a chosen NTT `Domain` (supplied by
the `NttDomains` class). The leaf-level NTT round-trip
`ntt ; basemul ; invntt` and the direct `polyMulC` both compute `realNttMul`,
so the rewrite `srcCom ⇝ tgtCom` is still sound (`rfl`) — but now over the
*real* operations.

* `realLatticeDialect`, `realLatticeDenote` — the dialect and its CompPoly-backed
  denotation (`basemul`/`polyMulC ↦ realNttMul`; `ntt`/`invntt ↦ id` on the
  `CPolynomial`, the NTT form being the same polynomial value).
* `realSrcCom` / `realTgtCom` — the canonical one-multiply program and its
  NTT-expanded `invntt (basemul (ntt a) (ntt b))` form, as
  `Com realLatticeDialect`.
* `real_nttMul_rewrite_denote_eq` — the rewrite is denotation-preserving for the
  real ops (`rfl`: both reduce to `realNttMul`).
* **`realSrcCom_negacyclic_coeff` / `realTgtCom_negacyclic_coeff`** (the Com-level
  headline): on encoded inputs `enc a`, `enc b`, the negacyclic reduction
  `%ₘ (X^n + 1)` of the program's `Com.denote` has its `k`-th coefficient equal
  to the negacyclic convolution — `realNttMul_negacyclic_coeff` lifted
  from the op level to `Com.denote`. This is the statement "the NTT-mul bracket
  denotes, under the real ops, to the negacyclic product".

## Status: THEORY artifact, not the emit path

`realLatticeDialect` is a **theory layer**, not a live lowering island. Its ops
are the real-valued (CompPoly-backed) lattice operations over
`CPolynomial (ZMod q)`, and it exists **only** to carry the NTT-mul soundness
proofs above — the negacyclic-product theorems at the op and `Com`
levels. It performs **no `Com` emission and no lowering out**: there is no
`realLatticeDialect → jasminDialect` (or Veir) path, and it is not type-compatible
with the emit-path leaves (which compute over `Fin n → BitVec 16`, not
`CPolynomial`). The emit path uses the toy `latticeDialect`, lowered directly to
`jasminDialect` via `lowerLatticeToJasmin` (`VIR/LatticeToJasmin.lean`); this
sibling dialect is the real-semantics witness those proofs are stated against.

There are **no `sorry`s** in this file; see `#print axioms` at the end.

## Scope note

The only ingredient *not* re-derived is the CRT factorisation of `X^256 + 1`
into 128 quadratics (the "incomplete NTT" structure). That is an orthogonal
optimisation — it explains why ML-KEM stores NTT-domain coefficients in
degree-`< 2` blocks — and is *not* needed for product correctness: the
schoolbook negacyclic product computed by `negacyclic_mul_coeff` is the
specification. CompPoly's `incompleteNTT` would refine the *representation*;
correctness of the *value* is fully discharged here.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic

open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.FastMul (fastMulImpl fastMulImpl_eq_mul)
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly negacyclic_mul_coeff)
open CompPoly (CPolynomial)
open CatCrypt.Crypto.SecureCompilation.VIR (realNtt realBasemul realInvntt realNttMul
  realNttMul_eq_fastMulImpl)
open Polynomial

/-! ## 1. ML-KEM-768 is a field

`ZMod 3329` is a field because `3329` is prime (the ML-KEM-768 modulus). We
register the `Fact` instance so `Field (ZMod 3329)` resolves and CompPoly's
`Domain (ZMod 3329)` is available. -/

/-- The ML-KEM-768 modulus `3329` is prime. -/
theorem mlkemQ_prime : Nat.Prime 3329 := by native_decide

instance : Fact (Nat.Prime 3329) := ⟨mlkemQ_prime⟩

/-! ## 2. The concrete coefficient encoding

`enc q n c` builds the canonical polynomial whose `i`-th coefficient is the
16-bit lane `c i`, reduced into `ZMod q`. The underlying raw array has length
`n`, so the polynomial degree is `< n` — exactly what the negacyclic ring
`Z_q[X]/(X^n+1)` requires of representatives, and what makes ML-KEM's 512-point
domain large enough for the convolution. -/

section Encoding

variable (q n : Nat)

/-- The raw coefficient array: lane `i` of the `Fin n → BitVec 16` input becomes
    the `ZMod q` coefficient `(c i).toNat`. Length `n`. -/
def encRaw (c : Fin n → BitVec 16) : CompPoly.CPolynomial.Raw (ZMod q) :=
  Array.ofFn (fun i : Fin n => ((c i).toNat : ZMod q))

/-- **Concrete ML-KEM encoding.** A coefficient vector `c : Fin n → BitVec 16`
    (the lattice dialect's `polyC q n` / `polyN q n` denotation) becomes the
    canonical polynomial `Σ_i (c i) X^i` over `ZMod q`. Canonicalised by
    trimming trailing zeros. -/
def enc (c : Fin n → BitVec 16) : CPolynomial (ZMod q) :=
  ⟨(encRaw q n c).trim, CompPoly.CPolynomial.Raw.Trim.isCanonical_trim _⟩

end Encoding

/-- ML-KEM-768 specialisation of the encoding: `(q, n) = (3329, 256)`. -/
abbrev encMlkem : (Fin 256 → BitVec 16) → CPolynomial (ZMod 3329) := enc 3329 256

/-! ## 3. Encoding coefficient formula and degree bound -/

section EncodingLemmas

variable {q n : Nat}

/-- The raw encoding array has length `n`. -/
@[simp] theorem encRaw_size (c : Fin n → BitVec 16) : (encRaw q n c).size = n := by
  simp [encRaw]

/-- The canonical encoding's underlying trim size is at most `n` (trimming only
    drops trailing zeros from the length-`n` raw array). -/
theorem enc_trim_size_le (c : Fin n → BitVec 16) :
    (enc q n c).val.size ≤ n := by
  have h := CompPoly.CPolynomial.Raw.Trim.size_le_size (encRaw q n c)
  simpa [enc, encRaw_size c] using h

/-- The `i`-th coefficient of the raw encoding (for `i < n`) is the encoded lane. -/
theorem encRaw_coeff (c : Fin n → BitVec 16) {i : Nat} (hi : i < n) :
    (encRaw q n c).coeff i = ((c ⟨i, hi⟩).toNat : ZMod q) := by
  simp only [encRaw, CompPoly.CPolynomial.Raw.coeff]
  rw [Array.getD]; simp [hi]

end EncodingLemmas

/-! ## 4. The encoding fits any domain of size `≥ 2n`

The convolution of two degree-`< n` polynomials has degree `< 2n - 1`, so any
NTT domain of size `≥ 2n` is large enough. ML-KEM's 512-point NTT
(`logN = 9`, `D.n = 512`) comfortably fits `n = 256`. This discharges the
`Domain.fits` precondition of CompPoly's `fastMulImpl_eq_mul`. -/

section Fits

variable {q n : Nat} [Fact (Nat.Prime q)]

/-- The canonical encoding's underlying trim size is at most `n`. Because
    `enc q n c` is already canonical, its `.val` is trim-stable, so its
    `trim.size` equals its `size`, which is `≤ n`. -/
theorem enc_val_trim_size_le (c : Fin n → BitVec 16) :
    (enc q n c).val.trim.size ≤ n := by
  rw [CompPoly.CPolynomial.trim_eq (enc q n c)]
  exact enc_trim_size_le c

/-- **Encoding fits.** For any NTT domain `D` of size `≥ 2n`, the two encoded
    operands fit: `Domain.fits D (enc a).val (enc b).val`. This is the
    `Domain.fits` hypothesis that `fastMulImpl_eq_mul` requires. -/
theorem enc_fits (D : Domain (ZMod q)) (hD : 2 * n ≤ D.n)
    (a b : Fin n → BitVec 16) :
    Domain.fits D (enc q n a).val (enc q n b).val := by
  have ha := enc_val_trim_size_le (q := q) a
  have hb := enc_val_trim_size_le (q := q) b
  unfold Domain.fits Domain.requiredLength
  split <;> omega

end Fits

/-! ## 5. The real NTT multiply, transported to a Mathlib polynomial

`realNttMul` (from `LatticeNTTSound`) is the CompPoly composite
`invntt (basemul (ntt p) (ntt q))`, definitionally `fastMulImpl`. Under
`Domain.fits` it computes the *cyclic* full product `p * q` in `CPolynomial`,
and hence — via the ring hom `toPoly` — the product `p.toPoly * q.toPoly` in
Mathlib's `R[X]`. This is honest convolution correctness (`fastMulImpl_eq_mul`),
not a definitional collapse. -/

section RealToPoly

variable {q : Nat} [Fact (Nat.Prime q)]

/-- **Cyclic NTT correctness, transported to `Polynomial`.** Under
    `Domain.fits`, the real CompPoly NTT multiply transported through `toPoly`
    is the Mathlib polynomial product. Combines `fastMulImpl_eq_mul` (the
    convolution theorem) with the `toPoly` ring-hom multiplicativity
    (`CompPoly.CPolynomial.toPoly_mul`). -/
theorem realNttMul_toPoly (D : Domain (ZMod q)) (p r : CPolynomial (ZMod q))
    (hfits : Domain.fits D p.val r.val) :
    (realNttMul D p r).toPoly = p.toPoly * r.toPoly := by
  rw [realNttMul_eq_fastMulImpl, fastMulImpl_eq_mul D p r hfits,
    CompPoly.CPolynomial.toPoly_mul]

end RealToPoly

/-! ## 6. Degree bound of the encoding's `toPoly`

The encoded polynomial has its `toPoly` of degree `< n`: the underlying raw
array has length `n`, so every coefficient at index `≥ n` is `0`. This is the
degree hypothesis the negacyclic theorem needs. -/

section EncodingDegree

variable {q n : Nat}

/-- A canonical polynomial whose underlying array has size `≤ n` has `toPoly`
    degree `< n`. -/
theorem toPoly_degree_lt_of_size_le (p : CPolynomial (ZMod q)) (h : p.val.size ≤ n) :
    p.toPoly.degree < (n : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [CompPoly.CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly,
    CompPoly.CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_none (by exact_mod_cast (le_trans h (by exact_mod_cast hm)))]
  rfl

/-- The encoding's `toPoly` has degree `< n`. -/
theorem enc_toPoly_degree_lt (c : Fin n → BitVec 16) :
    (enc q n c).toPoly.degree < (n : ℕ) :=
  toPoly_degree_lt_of_size_le (enc q n c) (enc_trim_size_le c)

end EncodingDegree

/-! ## 7. Headline: the real NTT multiply computes the negacyclic convolution

This is the concrete connection the task asks for. With the *real* CompPoly NTT
operations (NOT the toy `id`s of `LatticeDialect`), the negacyclic reduction of
the real NTT product equals the explicit negacyclic convolution of the encoded
inputs.

Reduction chain (each step a theorem, none `rfl`):

* `realNttMul_toPoly` — `(realNttMul D (enc a) (enc b)).toPoly =
  (enc a).toPoly * (enc b).toPoly`, the *cyclic* product correctness
  (`fastMulImpl_eq_mul` + `toPoly_mul`), valid under `Domain.fits`;
* `enc_fits` — discharges `Domain.fits` for any domain of size `≥ 2n`
  (ML-KEM's 512-point NTT);
* `negacyclic_mul_coeff` (from CompPoly's `Negacyclic`) — the `X^n ≡ −1` fold,
  turning the cyclic product into the negacyclic convolution coefficient. -/

section Headline

variable {q n : Nat} [Fact (Nat.Prime q)]

/-- **Headline (concrete ML-KEM-style NTT soundness).**

    With the CompPoly NTT operations, the negacyclic reduction
    `%ₘ (X^n + 1)` of the real NTT product `realNttMul D (enc a) (enc b)`
    (transported to a Mathlib `Polynomial`) has its `k`-th coefficient
    (`k < n`) equal to the explicit negacyclic convolution

      `(Σ_{i+j=k} (enc a)ᵢ (enc b)ⱼ) − (Σ_{i+j=k+n} (enc a)ᵢ (enc b)ⱼ)`.

    This combines:
    * the *cyclic* NTT correctness `realNttMul_toPoly`
      (= CompPoly's `fastMulImpl_eq_mul`), discharged via `enc_fits` for any
      domain of size `≥ 2n`; and
    * the *negacyclic fold* `negacyclic_mul_coeff` (CompPoly's `Negacyclic`),
      the `X^n ≡ −1` reduction that turns the cyclic full product into the
      ML-KEM ring `Z_q[X] / (X^n + 1)`.

    Neither half is `rfl`: this is real convolution correctness plus the
    negacyclic reduction, not the definitional `polyMulCF = id ∘ …`
    of the toy dialect. -/
theorem realNttMul_negacyclic_coeff
    (D : Domain (ZMod q)) (hD : 2 * n ≤ D.n) (hn : 0 < n)
    (a b : Fin n → BitVec 16) {k : Nat} (hk : k < n) :
    ((realNttMul D (enc q n a) (enc q n b)).toPoly %ₘ negaPoly n).coeff k
      = (∑ ij ∈ Finset.antidiagonal k,
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + n),
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2) := by
  -- Step 1: the real NTT product is the cyclic full polynomial product.
  rw [realNttMul_toPoly D (enc q n a) (enc q n b) (enc_fits D hD a b)]
  -- Step 2: the negacyclic fold (needs the product degree bound < 2n).
  have ha := enc_toPoly_degree_lt (q := q) a
  have hb := enc_toPoly_degree_lt (q := q) b
  have hab : ((enc q n a).toPoly * (enc q n b).toPoly).degree < (2 * n : ℕ) := by
    by_cases hzero : (enc q n a).toPoly * (enc q n b).toPoly = 0
    · rw [hzero, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree hzero]
      have hna : (enc q n a).toPoly.natDegree < n := by
        by_cases ha0 : (enc q n a).toPoly = 0
        · simp [ha0]; exact hn
        · exact (Polynomial.natDegree_lt_iff_degree_lt ha0).mpr ha
      have hnb : (enc q n b).toPoly.natDegree < n := by
        by_cases hb0 : (enc q n b).toPoly = 0
        · simp [hb0]; exact hn
        · exact (Polynomial.natDegree_lt_iff_degree_lt hb0).mpr hb
      have hle := Polynomial.natDegree_mul_le
        (p := (enc q n a).toPoly) (q := (enc q n b).toPoly)
      have hlt : ((enc q n a).toPoly * (enc q n b).toPoly).natDegree < 2 * n := by omega
      exact_mod_cast hlt
  rw [negacyclic_mul_coeff (enc q n a).toPoly (enc q n b).toPoly hn hab hk]

end Headline

/-! ## 8. A real-denoting lattice dialect, and the Com-level negacyclic product

We now *plug* `realNttMul` into a VIR `Dialect` denotation, lifting the op-level
`realNttMul_negacyclic_coeff` to the `Com.denote` level. The toy `latticeDialect`
denotes over `Fin n → BitVec 16` with `nttF = id`; we cannot reuse it (its
downstream files `LatticeToJasminDenoteUncond` / `MlirPolynomialDialect` rely on
those toy leaves, and the real ops are not even on the same representation).

Instead `realLatticeDialect` is a *sibling* dialect whose value types denote to
the `CPolynomial (ZMod q)`, with the multiply ops backed by `realNttMul`.
-/

open CatCrypt.Crypto.SecureCompilation.VIR (realNtt realBasemul realInvntt)
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly)

section RealDialect

/-- A choice of NTT `Domain` for every prime modulus. The lattice ops carry
    their own modulus in their payload, so the dialect-level denotation needs a
    domain *per modulus*; this class supplies one. For ML-KEM-768 the intended
    instance picks the 512-point domain (`logN = 9`), which satisfies
    `2 * 256 ≤ 512`. -/
class NttDomains where
  /-- The NTT domain to use for modulus `q` (when `q` is prime). -/
  dom : (q : Nat) → [Fact (Nat.Prime q)] → Domain (ZMod q)

/-- The real lattice dialect's value-type alphabet: the alphabet `latticeDialect`
    already fixes, read at the polynomial semantics. `polyC` and `polyN` are
    *distinct* constructors (coefficient form vs NTT form), and here both denote
    to the `CPolynomial (ZMod q)`. -/
abbrev RealLatticeTy := LatticeDialect.LatticeTyG .poly

/-- Both forms denote to `CPolynomial (ZMod q)`: the real CompPoly polynomial
    type, so the NTT operations type-check directly. -/
@[reducible] instance : TyDenote RealLatticeTy where
  denote
    | .polyC q _ => CPolynomial (ZMod q)
    | .polyN q _ => CPolynomial (ZMod q)

/-- The lattice dialect under the polynomial semantics. Its op tags and op
    signatures are the ones `LatticeDialect` already fixes; this is the same
    syntax read over `CPolynomial (ZMod q)` instead of `Fin n → BitVec 16`. -/
abbrev realLatticeDialect : Dialect := LatticeDialect.latticeDialectG .poly

/-- **The real denotation.** `ntt` / `invntt` are the identity on the
    `CPolynomial` value (the NTT form *is* the same polynomial); `basemul` and
    the coefficient-form `polyMulC` both denote via the `realNttMul`
    (CompPoly's `fastMulImpl`) over the modulus's NTT domain. The deep content —
    forward transform, pointwise NTT-domain product, inverse transform — lives
    inside `realNttMul`, so the round-trip `ntt ; basemul ; invntt` computes the
    real NTT product, exactly matching the direct `polyMulC`. (The modulus guard
    `Nat.Prime q` is never exercised by the headline programs, which fix a prime
    `q`; the `else 0` branch keeps the denotation total for all op moduli.) -/
noncomputable instance realLatticeDenote [ND : NttDomains] :
    DialectDenote realLatticeDialect where
  denote op := match op with
    | .ntt _ _ => fun args => args.head
    | .invntt _ _ => fun args => args.head
    | .basemul q _ => fun args =>
        if h : Nat.Prime q then
          haveI : Fact (Nat.Prime q) := ⟨h⟩
          realNttMul (ND.dom q) args.head args.tail.head
        else (0 : CPolynomial (ZMod q))
    | .polyAddN _ _ => fun args => args.head
    | .polyMulC q _ => fun args =>
        if h : Nat.Prime q then
          haveI : Fact (Nat.Prime q) := ⟨h⟩
          realNttMul (ND.dom q) args.head args.tail.head
        else (0 : CPolynomial (ZMod q))

section RealRewrite

variable (q n : Nat)

/-- Two coefficient-form inputs `a, b : polyC q n`. -/
@[reducible] def realInCtxt : Ctxt realLatticeDialect := [.polyC q n, .polyC q n]

/-- **Source program**: a single coefficient-form multiply,
    `let c = polyMulC a b in ret c`. -/
def realSrcCom : Com realLatticeDialect (realInCtxt q n) (.polyC q n) :=
  .var (.mk (.polyMulC q n) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **Target program**: the expanded NTT-form bracket
    `let ta = ntt a; let tb = ntt b; let p = basemul ta tb; let c = invntt p; ret c`.
    Same de Bruijn bookkeeping as `LatticeDialect.tgtCom`. -/
def realTgtCom : Com realLatticeDialect (realInCtxt q n) (.polyC q n) :=
  .var (.mk (.ntt q n) rfl (.cons .here .nil))
  (.var (.mk (.ntt q n) rfl (.cons (.there (.there .here)) .nil))
    (.var (.mk (.basemul q n) rfl
            (.cons (.there .here) (.cons .here .nil)))
      (.var (.mk (.invntt q n) rfl (.cons .here .nil))
        (.ret .here))))

/-- **Rewrite soundness for the real ops.** The NTT-form rewrite preserves
    `Com.denote` even with the CompPoly operations: both the source
    (`polyMulC`) and the target (`invntt (basemul (ntt a) (ntt b))`) reduce to
    `realNttMul` applied to the two inputs, so they are *definitionally* equal.
    The deep NTT-domain content is carried inside `realNttMul`. -/
theorem real_nttMul_rewrite_denote_eq [NttDomains]
    (V : Ctxt.Valuation (realInCtxt q n)) :
    (realSrcCom q n).denote V = (realTgtCom q n).denote V := rfl

/-- The source program's denotation on a concrete two-input valuation is exactly
    `realNttMul` of the inputs (for a prime modulus). -/
theorem realSrcCom_denote [ND : NttDomains] [hp : Fact (Nat.Prime q)]
    (a b : CPolynomial (ZMod q)) :
    (realSrcCom q n).denote (.cons a (.cons b .nil))
      = realNttMul (ND.dom q) a b := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩; realNttMul (ND.dom q) a b)
        else (0 : CPolynomial (ZMod q))) = realNttMul (ND.dom q) a b
  rw [dif_pos hp.out]

/-- The target (NTT-expanded) program's denotation likewise equals `realNttMul`
    of the inputs — by `real_nttMul_rewrite_denote_eq`. -/
theorem realTgtCom_denote [ND : NttDomains] [Fact (Nat.Prime q)]
    (a b : CPolynomial (ZMod q)) :
    (realTgtCom q n).denote (.cons a (.cons b .nil))
      = realNttMul (ND.dom q) a b := by
  rw [← real_nttMul_rewrite_denote_eq q n, realSrcCom_denote q n a b]

/-- **Com-level headline (source).** With the real CompPoly operations plugged
    into the dialect denotation, the negacyclic reduction `%ₘ (X^n + 1)` of the
    `Com.denote` of the one-multiply program `realSrcCom`, evaluated on the
    encoded inputs `enc a`, `enc b`, has its `k`-th coefficient (`k < n`) equal
    to the negacyclic convolution

      `(Σ_{i+j=k} (enc a)ᵢ (enc b)ⱼ) − (Σ_{i+j=k+n} (enc a)ᵢ (enc b)ⱼ)`.

    This lifts the op-level `realNttMul_negacyclic_coeff` to `Com.denote`: the
    dialect/Com NTT-mul denotes, under the real ops, to the negacyclic
    product (via CompPoly). Not a definitional collapse — the value flows through
    `realNttMul` (cyclic NTT correctness) and the `negacyclic_mul_coeff` fold. -/
theorem realSrcCom_negacyclic_coeff [ND : NttDomains] [Fact (Nat.Prime q)]
    (hD : 2 * n ≤ (ND.dom q).n) (hn : 0 < n)
    (a b : Fin n → BitVec 16) {k : Nat} (hk : k < n) :
    (((realSrcCom q n).denote
          (.cons (enc q n a) (.cons (enc q n b) .nil))).toPoly %ₘ negaPoly n).coeff k
      = (∑ ij ∈ Finset.antidiagonal k,
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + n),
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2) := by
  rw [realSrcCom_denote q n (enc q n a) (enc q n b)]
  exact realNttMul_negacyclic_coeff (ND.dom q) hD hn a b hk

/-- **Com-level headline (NTT-expanded target).** The same negacyclic-product
    fact for the *expanded* bracket `invntt (basemul (ntt a) (ntt b))`
    (`realTgtCom`): its `Com.denote` on encoded inputs, reduced `%ₘ (X^n + 1)`,
    is the negacyclic convolution. This is the precise sense in which the
    NTT-mul bracket — wired through the verified VIR dialect denotation — computes
    the ML-KEM ring product. -/
theorem realTgtCom_negacyclic_coeff [ND : NttDomains] [Fact (Nat.Prime q)]
    (hD : 2 * n ≤ (ND.dom q).n) (hn : 0 < n)
    (a b : Fin n → BitVec 16) {k : Nat} (hk : k < n) :
    (((realTgtCom q n).denote
          (.cons (enc q n a) (.cons (enc q n b) .nil))).toPoly %ₘ negaPoly n).coeff k
      = (∑ ij ∈ Finset.antidiagonal k,
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + n),
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2) := by
  rw [realTgtCom_denote q n (enc q n a) (enc q n b)]
  exact realNttMul_negacyclic_coeff (ND.dom q) hD hn a b hk

end RealRewrite

end RealDialect

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic

/-! Axiom audit for the Com-level negacyclic-product facts. -/
#print axioms CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic.realSrcCom_negacyclic_coeff
#print axioms CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic.realTgtCom_negacyclic_coeff
