/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyEncoding
public import CompPoly.Univariate.NTT.FastMul
public import CompPoly.Univariate.NTT.Forward
public import CompPoly.Univariate.NTT.Inverse

/-!
# Lattice dialect NTT-mul: real-convolution soundness

The lattice VIR dialect (`SecureCompilation/VIR/LatticeDialect.lean`) proves the
rewrite

    polyMulC a b  ⇝  invntt (basemul (ntt a) (ntt b))

is denotation-preserving. With its *toy* denotation (`nttF = invnttF = id`,
`basemulF` pointwise, and `polyMulCF` **defined** as the composite) the
soundness obligation

    polyMulCF a b = invnttF (basemulF (nttF a) (nttF b))

is true *by definition* — `nttMul_rewrite_denote_eq` closes by `rfl`. That is
not a statement about a real NTT.

The general soundness theorem
`LatticeDialect.nttMul_rewrite_denote_eq_general` instead takes the agreement
as a hypothesis `hAgree`. **This module discharges that agreement shape against a
real NTT semantics**, where:

* `polyMulC` is canonical polynomial multiplication `(· * ·)` in
  `CPolynomial R` (the schoolbook / negacyclic-convolution product, *not*
  defined via NTT);
* `ntt` / `basemul` / `invntt` are the *actual* CompPoly NTT operations
  (`Forward.forwardImpl`, `FastMul.pointwiseMul`, `Inverse.inverseImpl`),
  composed exactly as `CompPoly.…FastMul.fastMulImpl` composes them.

The headline `realNttMul_agrees_schoolbook` shows the lattice rewrite's
soundness obligation, instantiated at the real operations, **is** CompPoly's
convolution theorem `fastMulImpl_eq_mul` (under `Domain.fits`) — not a
definitional identity. The deep content is `fastMulImpl_eq_mul`; everything
here is the plumbing that pins the lattice-dialect agreement shape onto it.

## What is proved (all goals closed; standard axioms only)

* `realNttMul` — the real NTT multiply, **literally** the composite
  `invntt (basemul (ntt p) (ntt q))` (definitionally equal to
  `FastMul.fastMulImpl`).
* `realNttMul_eq_compose` — `realNttMul D p q = realInvntt D (realBasemul D
  (realNtt D p) (realNtt D q))`. This is the lattice-shaped *right-hand side*
  for the real operations; it holds by `rfl` because the real ops are exactly
  the components of `fastMulImpl` — i.e. the *composition shape* is faithful.
* `realNttMul_agrees_schoolbook` — the agreement in the dialect's exact shape
  `schoolbook a b = invntt (basemul (ntt a) (ntt b))`, where
  `schoolbook = (· * ·)`. Under `Domain.fits`, this is **`fastMulImpl_eq_mul`**.
  The `= p * q` step is real convolution correctness, not `rfl`.
* `polyEncoded_agrees_schoolbook` — the `PolyEncoding`-parameterized plumbing
  variant, reusing
  `Optimizer.Lattice.NTTPolyMul.polyMul_leaf_agreement` (which itself is a
  one-step transport through `fastMulImpl_eq_mul`): the encoded real NTT
  multiply equals the encoded schoolbook product.

## What remains deferred (and why)

* A **concrete** `PolyEncoding 3329 256` (ML-KEM-768) / `PolyEncoding 8380417
  256` (ML-DSA-65): the byte-layout decision (little-endian packing,
  Montgomery vs. plain domain, NTT-domain caching) belongs to the protocol
  bridge, not the soundness framework, and
  `NTTPolyEncoding.lean` does not fix it either; we keep the
  encoding as a *parameter* so the theorem is statable and provable without
  inventing a layout.
* The **negacyclic fold** (ML-KEM/ML-DSA work mod `X^n + 1`, CompPoly's cyclic
  `Domain` delivers the cyclic product): handled encoding-side by choosing a
  domain of size `≥ 2·n` and folding `X^n ≡ -1` after `Domain.fits` is met.
  This is again a per-parameter encoding obligation, not a framework one.

The scope is therefore a **plumbing theorem**: it certifies that
the lattice rewrite's soundness obligation, read against real NTT operations,
*reduces to the convolution theorem* rather than to a definitional
collapse. The concrete byte-layout instance is outside this module.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.Forward (forwardImpl)
open CompPoly.CPolynomial.NTT.Inverse (inverseImpl)
open CompPoly.CPolynomial.NTT.FastMul (pointwiseMul fastMulImpl fastMulImpl_eq_mul)
open CompPoly (CPolynomial)

section RealOps

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-! ## 1. The real NTT operations (CompPoly-backed)

These are the *actual* transforms CompPoly uses inside `fastMulImpl`, not the
identity stand-ins of the toy dialect denotation. We expose them as named
operations so the lattice-rewrite agreement shape can be pinned onto them.

`realNtt` / `realBasemul` operate on raw evaluation arrays (`Array R`), exactly
the intermediate representation of the NTT pipeline; `realInvntt` returns the
canonical polynomial. Their composition is `realNttMul`, which we show equals
`fastMulImpl` definitionally. -/

/-- Real forward NTT: CompPoly's `Forward.forwardImpl`, taking a coefficient
    polynomial to its evaluation array. This is a nontrivial transform, not `id`. -/
@[reducible] def realNtt (D : Domain R) (p : CPolynomial R) : Array R :=
  forwardImpl D p.val

/-- Real NTT-domain base multiply: CompPoly's `FastMul.pointwiseMul`, the
    pointwise product of two evaluation arrays. -/
@[reducible] def realBasemul (D : Domain R) (a b : Array R) : Array R :=
  pointwiseMul D a b

/-- Real inverse NTT (+ canonicalising truncation), as composed inside
    `fastMulImpl`: `Inverse.inverseImpl` followed by `Domain.truncate` to the
    convolution length, packaged as a canonical `CPolynomial`.

    The truncation length is taken from the two *operand* polynomials, exactly
    as `FastMul.fastMulImpl` does, so that `realNttMul` below is definitionally
    `fastMulImpl`. -/
@[reducible] def realInvntt (D : Domain R) (p q : CPolynomial R) (cHat : Array R) :
    CPolynomial R :=
  ⟨(Domain.truncate (Domain.requiredLength p.val q.val) (inverseImpl D cHat)).trim,
    CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- The real NTT-based multiply, defined as the composite
    `invntt (basemul (ntt p) (ntt q))`. This is **definitionally equal** to
    `CompPoly.…FastMul.fastMulImpl D p q` — see `realNttMul_eq_fastMulImpl`. -/
@[reducible] def realNttMul (D : Domain R) (p q : CPolynomial R) : CPolynomial R :=
  realInvntt D p q (realBasemul D (realNtt D p) (realNtt D q))

/-! ## 2. The composition shape is faithful

`realNttMul` is *literally* the lattice-dialect right-hand side
`invntt (basemul (ntt a) (ntt b))` for the real operations, and it coincides
with CompPoly's `fastMulImpl`. Both facts hold by `rfl`: the real ops are the
exact internal components of `fastMulImpl`, so the *shape* of the rewrite is
honest (no reassociation, no hidden identity). -/

/-- `realNttMul` is exactly the lattice-shaped composite of the real
    operations. Holds by `rfl`: it is how `realNttMul` is defined. This is the
    *shape-faithfulness* statement — the rewrite target really is
    `invntt (basemul (ntt a) (ntt b))`. -/
theorem realNttMul_eq_compose (D : Domain R) (p q : CPolynomial R) :
    realNttMul D p q =
      realInvntt D p q (realBasemul D (realNtt D p) (realNtt D q)) := rfl

/-- `realNttMul` coincides with CompPoly's canonical `fastMulImpl`. Holds by
    `rfl` because `realNtt`/`realBasemul`/`realInvntt` are unfolded copies of
    the `forwardImpl`/`pointwiseMul`/`inverseImpl`+`truncate` pipeline that
    *defines* `fastMulImpl`. This is the bridge to the convolution theorem. -/
theorem realNttMul_eq_fastMulImpl (D : Domain R) (p q : CPolynomial R) :
    realNttMul D p q = fastMulImpl D p q := rfl

/-! ## 3. Soundness = the real convolution theorem

The lattice rewrite's soundness obligation, instantiated at the real NTT
operations and with `polyMulC` being canonical multiplication, is
*exactly* CompPoly's `fastMulImpl_eq_mul`. The agreement is **not** `rfl`: the
`schoolbook = invntt (basemul (ntt a) (ntt b))` step is the deep statement that
NTT-domain pointwise multiply, sandwiched by the transforms, computes the
convolution product. -/

/-- **Headline soundness.** Under `Domain.fits`, schoolbook polynomial
    multiplication agrees with the real NTT round-trip, in the lattice
    dialect's exact rewrite shape:

      `p * q  =  invntt (basemul (ntt p) (ntt q))`.

    This is the obligation `LatticeDialect.nttMul_rewrite_denote_eq_general`
    takes as a hypothesis — here discharged against *real* operations, where it
    is precisely `CompPoly.…FastMul.fastMulImpl_eq_mul` (the convolution
    theorem), **not** a definitional identity. -/
theorem realNttMul_agrees_schoolbook (D : Domain R) (p q : CPolynomial R)
    (hfits : Domain.fits D p.val q.val) :
    p * q = realInvntt D p q (realBasemul D (realNtt D p) (realNtt D q)) := by
  rw [← realNttMul_eq_compose, realNttMul_eq_fastMulImpl]
  exact (fastMulImpl_eq_mul D p q hfits).symm

/-- Symmetric orientation: the real NTT multiply equals schoolbook
    multiplication. Direct restatement of `fastMulImpl_eq_mul` through
    `realNttMul = fastMulImpl`. -/
theorem realNttMul_eq_schoolbook (D : Domain R) (p q : CPolynomial R)
    (hfits : Domain.fits D p.val q.val) :
    realNttMul D p q = p * q := by
  rw [realNttMul_eq_fastMulImpl]; exact fastMulImpl_eq_mul D p q hfits

end RealOps

/-! ## 4. PolyEncoding-parameterized plumbing

For a protocol bridge carrying a `PolyEncoding q n R` (encode/decode between the
`RustVal (.TPolyMod q n)` byte layout and `CPolynomial R`), the same soundness
reads at the encoded level. This reuses
`Optimizer.Lattice.NTTPolyMul.polyMul_leaf_agreement` — itself a one-step
transport through `fastMulImpl_eq_mul` — so the encoded real NTT multiply
equals the encoded schoolbook product.

The encoding is taken as a **parameter**: the concrete `PolyEncoding 3329 256`
(byte layout) is the documented deferred step (see module docstring). -/

open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul (PolyEncoding polyMul_leaf_agreement)
open CatCrypt.Crypto.Jasmin.LowCT (RustVal)

section Encoded

variable {q n : Nat} {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- **Encoded plumbing soundness.** Given a `PolyEncoding`, a `Domain` large
    enough (`Domain.fits` on the decoded operands), the encoded real NTT
    multiply (`realNttMul` on the decoded operands) equals the encoded
    schoolbook product. Reuses `polyMul_leaf_agreement`, which routes
    through `fastMulImpl_eq_mul`.

    This is the shape a concrete ML-KEM/ML-DSA bridge would discharge once it
    fixes a byte layout; here the layout is the `enc` parameter. -/
theorem polyEncoded_agrees_schoolbook
    (D : Domain R) (enc : PolyEncoding q n R)
    (a b : RustVal (.TPolyMod q n))
    (hfits : Domain.fits D (enc.decode a).val (enc.decode b).val) :
    enc.encode (realNttMul D (enc.decode a) (enc.decode b)) =
      enc.encode (enc.decode a * enc.decode b) := by
  -- `realNttMul = fastMulImpl` definitionally, then transport through `encode`
  -- using `polyMul_leaf_agreement`.
  show enc.encode (fastMulImpl D (enc.decode a) (enc.decode b)) =
    enc.encode (enc.decode a * enc.decode b)
  exact polyMul_leaf_agreement D enc a b hfits

end Encoded

end CatCrypt.Crypto.SecureCompilation.VIR
