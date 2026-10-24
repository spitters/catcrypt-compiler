/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealization


@[expose] public section
set_option autoImplicit false

/-!
# DR realization, finite layer — `SPComp.sample (BitVec n)` IS the finite uniform

`RngRealization.lean` proved the *component* facts of the realization against the
real `SDistr` (`PMF ∘ Option`) semantics: the cardinality seam
`Fintype.card (BitVec n) = 2 ^ n`, surjectivity of the deterministic
entropy-read leaf (`readBv_surjective`), the per-fibre uniform weight
`SPComp.sample (BitVec n) h (some (b, h)) = (2 ^ n)⁻¹` (`sample_apply_value`),
and support agreement (image = support).  It stopped short of the headline
PMF/SDistr *equality* and flagged the gap as "infinite-product-measure theory".

The key insight that closes it on the finite layer: `readBv η n` reads only the
**first `n` bits** of the entropy stream, so the relevant uniform object is a
**finite** `PMF (BitVec n)` over `2 ^ n` outcomes — `PMF.uniformFintype
(BitVec n)` — **not** the infinite Bernoulli product measure on `Nat → Bool`.
No cylinder σ-algebra is needed.  Two `SDistr`s with equal mass at every point
are equal (`PMF.ext`), and the prior step pinned the mass everywhere:

* `some (b, h)` : `(2 ^ n)⁻¹`  (`sample_apply_value`),
* `some (b, h')`, `h' ≠ h` : `0` (the sample never changes the heap),
* `none` : `0` (the sample never fails).

So this file states and proves the headline:

`SPComp.sample (BitVec n) h = uniformBV n h`

where `uniformBV n h : SDistr (BitVec n × Heap)` is the explicit pushforward of
the finite uniform PMF on `BitVec n` onto the support point `(·, h)`.  The
deterministic-leaf realization corollary follows: the support of this finite
uniform is exactly the image of `fun η => (sampleDet η (.bv n), h)`.

**DR realization closed on the finite layer — `sample` = the finite uniform,
realized by the deterministic `n`-bit entropy read.**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Rng

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## The finite uniform sub-distribution -/

/-- The finite uniform `PMF` on the `2 ^ n` outcomes of `BitVec n`.  This — not
    any infinite-stream measure — is the uniform object the deterministic read
    `readBv · n` realizes, because `readBv η n` consumes only `η`'s first `n`
    bits. -/
noncomputable def uniformBVPMF (n : Nat) : PMF (BitVec n) :=
  PMF.uniformFintype (BitVec n)

/-- Each of the `2 ^ n` `n`-bit words carries equal mass `(2 ^ n)⁻¹` under the
    finite uniform PMF. -/
theorem uniformBVPMF_apply (n : Nat) (b : BitVec n) :
    uniformBVPMF n b = ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [uniformBVPMF, PMF.uniformFintype_apply, card_bitvec]

/-- The finite uniform sub-distribution on outcomes `(b, h)`: the pushforward of
    the finite uniform PMF on `BitVec n` onto the support point `(·, h)`, lifted
    into `SDistr` (i.e. tagged `some`).  This is the explicit realization target
    for `SPComp.sample (BitVec n) h`. -/
noncomputable def uniformBV (n : Nat) (h : Heap) : SDistr (BitVec n × Heap) :=
  (uniformBVPMF n).map (fun b => some (b, h))

/-- Mass of the finite uniform sub-distribution at the support point `some (b, h)`
    is `(2 ^ n)⁻¹` — independent of `b`. -/
theorem uniformBV_apply_some (n : Nat) (h : Heap) (b : BitVec n) :
    uniformBV n h (some (b, h)) = ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [uniformBV, PMF.map_apply]
  rw [tsum_eq_single b]
  · simp [uniformBVPMF_apply]
  · intro b' hb'
    rw [ite_eq_right (fun hc => hb' (by simp only [Option.some.injEq, Prod.mk.injEq] at hc; exact hc.1.symm))]

/-- Mass of the finite uniform sub-distribution at a heap-mismatched point
    `some (b, h')`, `h' ≠ h`, is `0` — it lives entirely on the fixed heap `h`. -/
theorem uniformBV_apply_some_ne (n : Nat) (h h' : Heap) (b : BitVec n)
    (hne : h' ≠ h) : uniformBV n h (some (b, h')) = 0 := by
  rw [uniformBV, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro b'
  rw [ite_eq_right (fun hc => hne (by simp only [Option.some.injEq, Prod.mk.injEq] at hc; exact hc.2))]

/-- The finite uniform sub-distribution never fails. -/
theorem uniformBV_apply_none (n : Nat) (h : Heap) :
    uniformBV n h none = 0 := by
  rw [uniformBV, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro b
  rw [ite_eq_right (by simp)]

/-! ## The headline: `SPComp.sample (BitVec n)` IS this finite uniform -/

/-- **The finite realization (headline).**  `SPComp.sample (BitVec n) h`, the
    probabilistic denotation of the sampling leaf, equals `uniformBV n h`, the
    pushforward of the *finite* uniform PMF on `BitVec n` onto `(·, h)`.

    The proof is `PMF.ext`: two `SDistr`s (`PMF (Option ·)`) are equal once they
    agree at every point.  The prior step (`RngRealization`) pinned the mass of
    the sample everywhere — `(2 ^ n)⁻¹` on the support, `0` off it — and that is
    exactly the mass of the finite uniform.  No infinite-product measure is
    involved: `readBv · n` reads only the first `n` bits, so the realization
    closes on the finite `BitVec n` layer. -/
theorem sample_eq_uniformBV (n : Nat) (h : Heap) :
    SPComp.sample (BitVec n) h = uniformBV n h := by
  apply PMF.ext
  rintro (_ | ⟨b, h'⟩)
  · -- `none`: neither fails.
    rw [uniformBV_apply_none]
    classical
    unfold SPComp.sample SDistr.bind
    rw [PMF.bind_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro ob
    cases ob with
    | none => simp [SDistr.uniform_apply_none]
    | some b'' => simp [SDistr.pure, PMF.pure_apply]
  · -- `some (b, h')`: split on whether the heap matches.
    by_cases hh : h' = h
    · subst hh
      rw [sample_apply_value, uniformBV_apply_some]
    · rw [uniformBV_apply_some_ne n h h' b hh]
      classical
      unfold SPComp.sample SDistr.bind
      rw [PMF.bind_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro ob
      cases ob with
      | none => simp [SDistr.uniform_apply_none]
      | some b'' =>
        simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq]
        rw [ite_eq_right (by intro hc; exact hh hc.2)]
        simp

/-! ## The deterministic-leaf realization corollary -/

/-- **Realization corollary.**  The finite uniform sub-distribution `uniformBV n h`
    that `SPComp.sample (BitVec n) h` equals has support exactly the image of the
    deterministic entropy-read leaf `fun η => (sampleDet η (.bv n), h)`.

    Combined with `sample_eq_uniformBV`, this is the closed realization: the
    probabilistic sample *is* the finite uniform, and that finite uniform is
    *realized* by running the deterministic `n`-bit read `sampleDet · (.bv n)`
    over the `2 ^ n` finite entropy prefixes. -/
theorem uniformBV_support_eq_image (n : Nat) (h : Heap) :
    (uniformBV n h).support
      = Set.range (fun η : Entropy => (sampleDet η (.bv n), h)) := by
  rw [← sample_eq_uniformBV]
  exact sample_support_eq_image n h

/-- The deterministic leaf's image is precisely the support of the finite
    uniform realization — the surjective-read direction, stated directly. -/
theorem sampleDet_mem_uniformBV_support (n : Nat) (h : Heap) (η : Entropy) :
    (sampleDet η (.bv n), h) ∈ (uniformBV n h).support := by
  rw [← sample_eq_uniformBV]
  exact sampleDet_mem_sample_support n h η

end CatCrypt.Crypto.SecureCompilation.Dialects.Rng
