/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.ZMod3329

/-!
# Verified ML-KEM NTT poly arithmetic over `Zq3329`

A pure-Lean reference computation of the inner ML-KEM kernel operations
(NTT butterfly, scalar poly addition, scalar poly multiplication,
matrix-vector product) over the verified prime field
`Zq3329 := ZMod 3329`.

This is the verified body that the `MlkemHaxLowCTBridge` consults so
the bridge round-trip identities reduce to proven `rfl`-style facts
over the underlying `ZMod 3329`, rather than opaque axioms on an
abstract field surface (this is the lattice analogue of
`MqEvalVerified.lean` for MAYO).

## ML-KEM parameters

* `q  = 3329` (modulus)
* `n  = 256`  (polynomial degree)
* `k  = 3`    (module rank, ML-KEM-768; other levels reuse the same
  arithmetic primitives at different `k`)

## API

* `nttButterflyVerified a b twiddle` — the Cooley–Tukey butterfly step
  `(a + twiddle * b, a - twiddle * b)` over `Zq3329`.
* `polyAddVerified`, `polyMulPointwiseVerified` — coefficient-wise
  addition and pointwise multiplication of two poly-form vectors
  (in NTT domain pointwise mul is the basemul; in coefficient form
  it is the schoolbook poly product modulo `x^n + 1`).
* `polyVecDotVerified` — `Σ a[i] · b[i]` over `k` poly slots.
* `matVecMulVerified` — `(A · s)[i] = Σ_j A[i][j] · s[j]` — the
  matrix-vector product used by ML-KEM keygen/encaps/decaps.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.NttPolyVerified

open CatCrypt.Util

/-- ML-KEM-768 polynomial degree. -/
def n : Nat := 256

/-- ML-KEM-768 module rank. -/
def k : Nat := 3

/-! ## NTT butterfly -/

/-- The Cooley–Tukey NTT butterfly: given a pair `(a, b)` and a twiddle
    factor `ω`, return `(a + ω · b, a − ω · b)`. Pointwise over
    `Zq3329`. -/
def nttButterflyVerified (a b twiddle : Zq3329) : Zq3329 × Zq3329 :=
  (a + twiddle * b, a - twiddle * b)

/-- Sanity: butterfly at twiddle = 1 reduces to `(a + b, a - b)`. -/
theorem nttButterflyVerified_at_one (a b : Zq3329) :
    nttButterflyVerified a b 1 = (a + b, a - b) := by
  simp [nttButterflyVerified]

/-- Sanity: butterfly at twiddle = 0 reduces to `(a, a)`. -/
theorem nttButterflyVerified_at_zero (a b : Zq3329) :
    nttButterflyVerified a b 0 = (a, a) := by
  simp [nttButterflyVerified]

/-! ## Pointwise poly arithmetic over `Zq3329` -/

/-- Coefficient-wise polynomial addition (length `n`). -/
def polyAddVerified (a b : Vector Zq3329 n) : Vector Zq3329 n :=
  Vector.ofFn (fun i => a.get i + b.get i)

/-- Coefficient-wise polynomial subtraction. -/
def polySubVerified (a b : Vector Zq3329 n) : Vector Zq3329 n :=
  Vector.ofFn (fun i => a.get i - b.get i)

/-- Pointwise polynomial multiplication (matches NTT-domain basemul). -/
def polyMulPointwiseVerified (a b : Vector Zq3329 n) : Vector Zq3329 n :=
  Vector.ofFn (fun i => a.get i * b.get i)

/-- Sanity: `polyAddVerified` is commutative. -/
theorem polyAddVerified_comm (a b : Vector Zq3329 n) :
    polyAddVerified a b = polyAddVerified b a := by
  unfold polyAddVerified
  apply Vector.ext
  intro i _
  simp [Vector.getElem_ofFn]
  ring

/-! ## Polyvec-dot and matrix-vector product -/

/-- Vector inner product of two polyvecs (length `k`), giving a single
    polynomial of degree `n` in the NTT domain. -/
def polyVecDotVerified
    (a b : Vector (Vector Zq3329 n) k) : Vector Zq3329 n :=
  -- Σ_{i=0}^{k-1} a[i] ⊙ b[i] (pointwise mul, then poly-add accumulate)
  -- For k = 3 we unfold the sum explicitly so the body stays computable.
  let p0 := polyMulPointwiseVerified (a.get ⟨0, by decide⟩) (b.get ⟨0, by decide⟩)
  let p1 := polyMulPointwiseVerified (a.get ⟨1, by decide⟩) (b.get ⟨1, by decide⟩)
  let p2 := polyMulPointwiseVerified (a.get ⟨2, by decide⟩) (b.get ⟨2, by decide⟩)
  polyAddVerified (polyAddVerified p0 p1) p2

/-- Matrix-vector product `(A · s)[i] = Σ_j A[i][j] ⊙ s[j]`. Output
    is a poly-vec of length `k`. -/
def matVecMulVerified
    (A : Vector (Vector (Vector Zq3329 n) k) k)
    (s : Vector (Vector Zq3329 n) k) : Vector (Vector Zq3329 n) k :=
  Vector.ofFn (fun i => polyVecDotVerified (A.get i) s)

/-- Elementwise polyvec addition (length `k`): the `u = A·r + e` vector add
    that the ML-KEM encryption backbone forms after the matrix·vector product. -/
def polyVecAddVerified (a b : Vector (Vector Zq3329 n) k) :
    Vector (Vector Zq3329 n) k :=
  Vector.ofFn (fun i => polyAddVerified (a.get i) (b.get i))

end CatCrypt.Crypto.MLKEM.NttPolyVerified
