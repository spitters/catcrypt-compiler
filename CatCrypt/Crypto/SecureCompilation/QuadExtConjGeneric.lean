/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.QuadExtGeneric
import Mathlib.Algebra.Field.Basic

/-!
# Generic conjugation, norm, and inversion of `QuadExt K = K[u]/(u² − ξ)`

`QuadExtGeneric` builds the generic quadratic extension `QuadExt K = K × K`
(written `c0 + c1·u`, `u² = ξ`) with schoolbook/Karatsuba multiply and a
`commRing ξ` instance over an abstract `CommRing K`. This module adds the next
layer — the structure that makes every quadratic field-extension level a field:

* the **Galois conjugation** `conj (a + b·u) = a − b·u`, a base-ring-fixing ring
  endomorphism (`conj_add`, `conj_mul`, `conj_conj`);
* the **field norm** `norm ξ x = (x · conj x).c0 = c0² − ξ·c1²`, which lands in
  the base ring (`mul_conj_c1_zero`, `mul_conj_eq`) and is multiplicative
  (`norm_mul`);
* over a base **field** `[Field K]`, the **conjugate-over-norm inverse**
  `inv ξ x = conj x · ⟨(norm ξ x)⁻¹, 0⟩` with the cancellation law
  `x · inv ξ x = 1` whenever `norm ξ x ≠ 0` (`mul_inv`).

This is the **generic core** that the per-tower `bls12_377` conjugation/norm/
inversion modules instantiate:

* `Fp2_377`-conj/norm/inv (`RelationalFrontBls377Fp2Conj`/`Fp2Inv`) are these at
  `K = ZMod bls377Q` (the base prime field);
* `Fp12_377`-conj/norm/inv (`RelationalFrontBls377Fp12Conj`/`Fp12Inv`) are these
  at `K = Fp6_377` (the degree-6 subfield, top step of the `2·3·2` tower).

Factoring through `QuadExt` proves the conjugation ring-hom facts, the norm's
base-ring landing, and the field cancellation law **once**, generically, instead
of re-deriving them per tower level. Because the base is a genuine abstract
`CommRing`/`Field`, `ring` closes the component identities **directly** — no
opaque-multiply `show` dance, unlike the `ZMod`-specialized phrasings where the
base operations are concrete.

## Honesty boundary

This is the abstract algebra only — conjugation, norm, and the conjugate-over-
norm inverse of `K[u]/(u² − ξ)`. The cancellation law is conditioned on
`norm ξ x ≠ 0`; that holds for all `x ≠ 0` **iff** `ξ` is a non-residue
(`a² − ξ·b² = 0` forces `a = b = 0`), a number-theoretic fact about the concrete
nonresidue, recorded but not proved here. It does **not** wire conjugation/norm/
inversion down to any emitted base kernel; that lift is per-instantiation and
deliberately out of scope here, to keep the generic core focused and sorry-free.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.QuadExtGeneric

namespace QuadExt

variable {K : Type*}

/-! ## 1. The Galois conjugation `a + b·u ↦ a − b·u`

The conjugation flips the sign of the `u`-component. It is `ξ`-independent at the
definition level (it is just a componentwise negation on `c1`); its
multiplicativity interacts with `ξ`, but invariantly so (`(−b)(−d)·ξ = b·d·ξ`).
We work over the `commRing ξ` instance (so `*` is `mulSchoolbook ξ`) for the
multiplicative facts. -/

/-- The **generic Galois conjugate** `conj (a + b·u) = a − b·u` — the nontrivial
    automorphism of `QuadExt K` over the base ring `K`. -/
def conj [Neg K] (x : QuadExt K) : QuadExt K := ⟨x.c0, -x.c1⟩

@[simp] theorem conj_c0 [Neg K] (x : QuadExt K) : (conj x).c0 = x.c0 := rfl
@[simp] theorem conj_c1 [Neg K] (x : QuadExt K) : (conj x).c1 = -x.c1 := rfl

/-! ## 2. `conj` is additive, an involution, and unit-preserving -/

/-- **`conj` is additive** (`conj (x + y) = conj x + conj y`). -/
theorem conj_add [CommRing K] (x y : QuadExt K) : conj (x + y) = conj x + conj y := by
  ext <;> simp [add_comm]

/-- **`conj` is an involution** (`conj (conj x) = x`) — it is the order-2 element
    of the Galois group of `K[u]/(u² − ξ)` over `K`. -/
theorem conj_conj [CommRing K] (x : QuadExt K) : conj (conj x) = x := by
  ext <;> simp

/-- **`conj` fixes `1`** (`conj 1 = 1`). -/
theorem conj_one [CommRing K] : conj (1 : QuadExt K) = 1 := by
  ext <;> simp

/-- **`conj` fixes `0`** (`conj 0 = 0`). -/
theorem conj_zero [CommRing K] : conj (0 : QuadExt K) = 0 := by
  ext <;> simp

/-- **`conj` negates** (`conj (-x) = -conj x`). -/
theorem conj_neg [CommRing K] (x : QuadExt K) : conj (-x) = -conj x := by
  ext <;> simp

/-! ## 3. `conj` is multiplicative — the ring-homomorphism fact

The key identity: `conj` commutes with the schoolbook product. Both
`conj (x · y)` and `conj x · conj y` equal
`(c0·c0' + ξ·c1·c1') − (c0·c1' + c1·c0')·u`. The `ξ`-reduced real component is
unchanged (`(−b)(−d)·ξ = b·d·ξ`); the imaginary component flips sign. Because the
base `K` is a genuine `CommRing`, `ring` closes each component **directly**. -/

/-- **`conj` is multiplicative** (`conj (x * y) = conj x * conj y`) over the
    `commRing ξ` instance — the load-bearing ring-homomorphism fact. The sign
    flip on the `u`-component commutes with the schoolbook product because the
    `ξ`-reduction `(−b)(−d)·ξ = b·d·ξ` is invariant under conjugation. -/
theorem conj_mul [CommRing K] (ξ : K) (x y : QuadExt K) :
    letI := commRing ξ
    conj (x * y) = conj x * conj y := by
  letI := commRing ξ
  show conj (mulSchoolbook ξ x y) = mulSchoolbook ξ (conj x) (conj y)
  ext <;> simp [mulSchoolbook, add_comm]

/-! ## 4. The `QuadExt K → K` field norm `norm ξ x = (x · conj x).c0`

The norm is the product of an element with its conjugate, projected to the base
ring. Because `(a + b·u)(a − b·u) = (a² − ξ·b²) + 0·u`, the `u`-component of
`x · conj x` vanishes — the norm genuinely lands in `K`. -/

/-- The **`u`-component of `x · conj x` vanishes** — the field norm lands in the
    base ring `K`. (`(a + b·u)(a − b·u) = (a² − ξ·b²) + 0·u`.) -/
theorem mul_conj_c1_zero [CommRing K] (ξ : K) (x : QuadExt K) :
    letI := commRing ξ
    (x * conj x).c1 = 0 := by
  letI := commRing ξ
  show (mulSchoolbook ξ x (conj x)).c1 = 0
  simp [mulSchoolbook]; ring

/-- The **`QuadExt K → K` field norm** `norm ξ x = (x · conj x).c0 = c0² − ξ·c1²`.
    The product `x · conj x` lands in the base ring (`mul_conj_c1_zero`), so the
    norm is well-defined as its `c0` projection. This is the building block for
    quadratic-extension inversion. -/
def norm [CommRing K] (ξ : K) (x : QuadExt K) : K :=
  letI := commRing ξ
  (x * conj x).c0

/-- **The norm in closed form** (`norm ξ x = c0² − ξ·c1²`). -/
theorem norm_eq [CommRing K] (ξ : K) (x : QuadExt K) :
    norm ξ x = x.c0 * x.c0 - x.c1 * x.c1 * ξ := by
  letI := commRing ξ
  show (mulSchoolbook ξ x (conj x)).c0 = x.c0 * x.c0 - x.c1 * x.c1 * ξ
  simp [mulSchoolbook]; ring

/-- **`x · conj x` is the norm injected into `QuadExt K`** (`= norm ξ x + 0·u`):
    its `c0` is `norm ξ x` and its `c1` is `0`. -/
theorem mul_conj_eq [CommRing K] (ξ : K) (x : QuadExt K) :
    letI := commRing ξ
    x * conj x = ⟨norm ξ x, 0⟩ := by
  letI := commRing ξ
  ext
  · rfl
  · exact mul_conj_c1_zero ξ x

/-! ## 5. `norm` is multiplicative

The norm is a multiplicative map `QuadExt K → K`
(`norm (x·y) = norm x · norm y`), immediate from `conj`'s multiplicativity and
commutativity of the base ring. -/

/-- **The norm is multiplicative** (`norm ξ (x * y) = norm ξ x * norm ξ y`) —
    a consequence of `conj_mul` and commutativity. -/
theorem norm_mul [CommRing K] (ξ : K) (x y : QuadExt K) :
    letI := commRing ξ
    norm ξ (x * y) = norm ξ x * norm ξ y := by
  letI := commRing ξ
  have hxy : x * y * conj (x * y) = (x * conj x) * (y * conj y) := by
    rw [conj_mul]; ring
  have h0 : (x * y * conj (x * y)).c0 = ((x * conj x) * (y * conj y)).c0 := by
    rw [hxy]
  rw [mul_conj_eq ξ x, mul_conj_eq ξ y] at h0
  show (x * y * conj (x * y)).c0 = _
  rw [h0]
  show (mulSchoolbook ξ ⟨norm ξ x, 0⟩ ⟨norm ξ y, 0⟩).c0 = norm ξ x * norm ξ y
  simp [mulSchoolbook]

/-! ## 6. The base-ring embedding and the conjugate-over-norm inverse

Over a base **field** `[Field K]`, the norm (a base-ring element) is invertible
whenever nonzero, so we can invert via the classical formula `x⁻¹ = conj x /
norm x`: scale the conjugate `conj x` by the base-field inverse of the norm,
injected into `QuadExt K` on the `c0` component. Because `K` is a genuine
`Field`, `mul_inv_cancel₀` closes the cancellation directly. -/

/-- The **base-ring embedding** `K → QuadExt K`, `n ↦ n + 0·u`. The norm
    (a base-ring element) is injected back into the extension this way. -/
def ofBase [Zero K] (n : K) : QuadExt K := ⟨n, 0⟩

@[simp] theorem ofBase_c0 [Zero K] (n : K) : (ofBase n).c0 = n := rfl
@[simp] theorem ofBase_c1 [Zero K] (n : K) : (ofBase n).c1 = 0 := rfl

/-- The **product of two base-ring elements** stays in the base ring and is the
    base-ring product on `c0` (`⟨a, 0⟩ · ⟨b, 0⟩ = ⟨a·b, 0⟩`): the cross terms
    `a·0`, `0·b` and the `ξ`-reduced term `0·0·ξ` all vanish. -/
theorem ofBase_mul [CommRing K] (ξ : K) (a b : K) :
    letI := commRing ξ
    ofBase a * ofBase b = ofBase (a * b) := by
  letI := commRing ξ
  show mulSchoolbook ξ (ofBase a) (ofBase b) = ofBase (a * b)
  ext <;> simp [mulSchoolbook, ofBase]

/-- The **`QuadExt K` inverse** `inv ξ x = conj x · ⟨(norm ξ x)⁻¹, 0⟩` — the
    conjugate scaled by the base-field inverse of the norm (`x⁻¹ = conj x /
    norm x`). Requires `K` to be a field so the norm is invertible; the
    cancellation law (`mul_inv`) additionally needs `norm ξ x ≠ 0`. -/
noncomputable def inv [Field K] (ξ : K) (x : QuadExt K) : QuadExt K :=
  letI := commRing ξ
  conj x * ofBase (norm ξ x)⁻¹

/-! ## 7. The field cancellation law `x · x⁻¹ = 1` -/

/-- **`QuadExt K` field cancellation** (`x · inv ξ x = 1`) whenever the norm is
    nonzero. The conjugate-over-norm inverse cancels `x`: associating the product
    as `(x · conj x) · ⟨(norm x)⁻¹, 0⟩`, the inner factor is the base-ring-valued
    `⟨norm ξ x, 0⟩` (`mul_conj_eq`), so the whole product is the base-ring product
    `⟨norm x · (norm x)⁻¹, 0⟩ = ⟨1, 0⟩ = 1` by `mul_inv_cancel₀`. This is the
    operation that makes `QuadExt K` a genuine field over a base field `K`. -/
theorem mul_inv [Field K] (ξ : K) (x : QuadExt K) (hx : norm ξ x ≠ 0) :
    letI := commRing ξ
    x * inv ξ x = 1 := by
  letI := commRing ξ
  -- Associate: x * (conj x * ⟨(norm x)⁻¹,0⟩) = (x * conj x) * ⟨(norm x)⁻¹,0⟩.
  have hassoc : x * inv ξ x = (x * conj x) * ofBase (norm ξ x)⁻¹ := by
    show x * (conj x * ofBase (norm ξ x)⁻¹) = (x * conj x) * ofBase (norm ξ x)⁻¹
    rw [mul_assoc]
  rw [hassoc, mul_conj_eq ξ x]
  -- Now ⟨norm x, 0⟩ * ⟨(norm x)⁻¹, 0⟩ = ⟨norm x * (norm x)⁻¹, 0⟩ = ⟨1, 0⟩ = 1.
  have hbase : (⟨norm ξ x, 0⟩ : QuadExt K) = ofBase (norm ξ x) := rfl
  rw [hbase, ofBase_mul ξ (norm ξ x) (norm ξ x)⁻¹, mul_inv_cancel₀ hx]
  rfl

/-- **`QuadExt K` field cancellation, other side** (`inv ξ x · x = 1`) —
    immediate from `mul_inv` and commutativity of the `commRing ξ` multiply. -/
theorem inv_mul [Field K] (ξ : K) (x : QuadExt K) (hx : norm ξ x ≠ 0) :
    letI := commRing ξ
    inv ξ x * x = 1 := by
  letI := commRing ξ
  rw [mul_comm]
  exact mul_inv ξ x hx

/-! ## 8. Remark — when is the norm nonzero?

The cancellation law is conditioned on `norm ξ x ≠ 0`. For `QuadExt K` to be a
field (every nonzero element invertible) one needs `norm ξ x = 0 ↔ x = 0`, which
holds **iff** `ξ` is a non-residue: `norm ξ x = c0² − ξ·c1²`, so `norm ξ x = 0`
forces `c0² = ξ·c1²`; if `ξ` is a non-square this is impossible unless
`c0 = c1 = 0`. Non-squareness of the concrete nonresidue is a number-theoretic
fact about the concrete `ξ`, **not** proved here — we record the equivalence as a
statement parameterized by that non-residue hypothesis. -/

/-- **The norm vanishes only at `0`, given `ξ` is a non-residue** (stated as the
    hypothesis `hξ`). Under that number-theoretic assumption — which we do **not**
    prove, it is a fact about the concrete nonresidue — `norm ξ x = 0 ↔ x = 0`,
    so every nonzero `QuadExt K` element is invertible by `mul_inv` and
    `QuadExt K` is a field. -/
theorem norm_ne_zero_iff_of_nonresidue [Field K] (ξ : K)
    (hξ : ∀ x : QuadExt K, norm ξ x = 0 → x = 0) (x : QuadExt K) :
    norm ξ x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hn hx0
    apply hn
    subst hx0
    show norm ξ 0 = 0
    rw [norm_eq]
    simp
  · intro hx0 hn
    exact hx0 (hξ x hn)

end QuadExt

end CatCrypt.Crypto.SecureCompilation.QuadExtGeneric
