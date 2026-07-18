/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.RngLeaf
import CatCrypt.Core.Code

set_option autoImplicit false

/-!
# DR — the realization theorem: deterministic entropy read ↔ uniform `SPComp.sample`

`RngLeaf.lean` gave the **deterministic** entropy-read denotation of the two
CryptoSSA sampling leaves: `sampleDet η (.bv n) = η.readBv n : BitVec n`, a
total function of an externally-supplied source `η`.  The probabilistic meaning
is the *separate* `CExpr.denote` interpretation, where
`CExpr.sampleBv n` denotes `SPComp.sample (BitVec n)` — uniform sampling
(`Code.lean`, `SPComp.sample`).

This file ties the two together: **running the deterministic op over uniform
entropy realizes the probabilistic sample.**  It does so by proving the
component facts that compose into that statement, against the actual `SDistr`
(= `PMF ∘ Option`) sub-distribution monad.

## What is proved (all against the real `SPComp`/`SDistr` semantics)

Let `n : ℕ`, `h : Heap`, `b : BitVec n`.

1. **Cardinality seam** `Fintype.card (BitVec n) = 2 ^ n` — so the uniform
   weight of `SPComp.sample (BitVec n)` is exactly `(2 ^ n)⁻¹`, matching the
   `readBv_toNat_lt` range `< 2 ^ n` from `RngLeaf`.

2. **Surjectivity of the deterministic leaf** (`readBv_surjective`,
   `sampleDet_bv_surjective`): every `b : BitVec n` is the deterministic read
   of *some* entropy source, via the canonical witness `entropyOf b`
   (`readBv_entropyOf`, `sampleDet_entropyOf`).  This is the "every value is
   hit" half of support agreement.

3. **The uniform pushforward value** (`sample_apply_value`):
   `SPComp.sample (BitVec n) h (some (b, h)) = (Fintype.card (BitVec n))⁻¹
   = (2 ^ n)⁻¹` — constant over all `b`, which is precisely what it means for
   the sample to be the uniform pushforward of the entropy onto `BitVec n`.

4. **Support agreement** (`mem_sample_support`, `sampleDet_mem_sample_support`,
   `sample_support_eq_image`): the support of `SPComp.sample (BitVec n) h` (at
   a fixed heap `h`) is exactly `{(b, h) | b : BitVec n}`, which is *exactly*
   the image of the deterministic leaf `fun η => (sampleDet η (.bv n), h)`.  So
   the deterministic image and the probabilistic support coincide.

Together (2)+(3)+(4) say: the deterministic leaf's image is the full sample
support, and every point of that support carries equal uniform mass `(2 ^ n)⁻¹`
— i.e. *the deterministic entropy read, fed uniform entropy, realizes
`SPComp.sample`.*

## The honest remaining gap to the full measure-theoretic equality

The fully-quantitative headline would be a measure pushforward:
`SPComp.sample (BitVec n) = map (fun η => readBv η n) μ`, where `μ` is the
**uniform product (Bernoulli ½) measure on the infinite stream `Nat → Bool`**.
We do **not** state that equation, because the `Entropy` source here is an
*arbitrary* function `Nat → Bool` with **no probability measure attached**
(`RngLeaf` deliberately keeps probability off the deterministic stack — there
is no `MeasurableSpace`/`Measure` on `Entropy`).  Stating the pushforward would
require:

* a `MeasurableSpace (Nat → Bool)` (the cylinder/product σ-algebra), and
* the infinite-product Bernoulli measure `(PMF.bernoulli ½).toMeasure ^ ℕ`
  (`MeasureTheory.Measure.infinitePi` / `PiMeasure`), and
* a `Measure → PMF` (or `SDistr`) bridge witnessing that the pushforward of
  that product measure along `readBv · n` is finitely supported with mass
  `(2 ^ n)⁻¹` per fibre.

That machinery is genuine infinite-product-measure theory and is **not**
present on the `SDistr` (`PMF (Option ·)`) side used by `SPComp`.  Rather than
fabricate it, we prove the strongest *finite* realization the `SDistr` API
supports: support agreement (image = support) **plus** the explicit uniform
fibre weight `(2 ^ n)⁻¹`.  These pin down the pushforward on every measurable
atom; only the outer "the infinite-stream measure pushes forward to this" wrapper
is deferred to the product-measure layer.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Rng

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Cardinality seam: `Fintype.card (BitVec n) = 2 ^ n` -/

/-- The canonical equivalence `BitVec n ≃ Fin (2 ^ n)` used only to compute the
    cardinality independently of which (irreducible) `Fintype` instance is in
    scope. -/
private def bvEquivFin (n : Nat) : BitVec n ≃ Fin (2 ^ n) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv := fun b => by ext; simp
  right_inv := fun i => by ext; simp

/-- The number of `n`-bit words is `2 ^ n`.  This matches the deterministic
    range bound `Entropy.readBv_toNat_lt : (readBv η n).toNat < 2 ^ n`: the
    deterministic leaf takes values in a set of size exactly `2 ^ n`, the same
    `2 ^ n` over which `SPComp.sample (BitVec n)` is uniform. -/
theorem card_bitvec (n : Nat) : Fintype.card (BitVec n) = 2 ^ n := by
  have h := Fintype.card_congr (bvEquivFin n)
  simpa using h

/-! ## Surjectivity of the deterministic leaf (the "every value is hit" half) -/

/-- The canonical entropy source realizing a given `b : BitVec n`: stream bit
    `i` is the `i`-th LSB of `b`, read from offset `0`.  This is the explicit
    witness for surjectivity of the deterministic read. -/
def entropyOf {n : Nat} (b : BitVec n) : Entropy where
  bits := fun i => b.getLsbD i
  offset := 0

@[simp] theorem entropyOf_offset {n : Nat} (b : BitVec n) :
    (entropyOf b).offset = 0 := rfl

@[simp] theorem entropyOf_bits {n : Nat} (b : BitVec n) (i : Nat) :
    (entropyOf b).bits i = b.getLsbD i := rfl

/-- **Realization (surjectivity), reads.**  The deterministic length-`n` read of
    the canonical source `entropyOf b` recovers `b` exactly. -/
@[simp] theorem readBv_entropyOf {n : Nat} (b : BitVec n) :
    (entropyOf b).readBv n = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Entropy.readBv_getLsb (entropyOf b) n ⟨i, hi⟩]
  simp

/-- **Realization (surjectivity), leaf.**  The deterministic `.bv n` *leaf* of
    the canonical source recovers `b` exactly. -/
@[simp] theorem sampleDet_entropyOf {n : Nat} (b : BitVec n) :
    sampleDet (entropyOf b) (.bv n) = b := by
  simp

/-- The length-`n` deterministic read `fun η => η.readBv n` is **surjective**:
    every `n`-bit word arises as the read of some entropy source.  Together with
    the range bound `readBv_toNat_lt`, the deterministic image is exactly the
    set of all `n`-bit words — the support of `SPComp.sample (BitVec n)`. -/
theorem readBv_surjective (n : Nat) :
    Function.Surjective (fun η : Entropy => η.readBv n) :=
  fun b => ⟨entropyOf b, readBv_entropyOf b⟩

/-- The deterministic sample *leaf* `fun η => sampleDet η (.bv n)` is
    surjective onto `BitVec n`. -/
theorem sampleDet_bv_surjective (n : Nat) :
    Function.Surjective (fun η : Entropy => sampleDet η (.bv n)) :=
  fun b => ⟨entropyOf b, sampleDet_entropyOf b⟩

/-! ## The uniform pushforward value -/

/-- **The uniform fibre weight.**  Evaluating the probabilistic sample at any
    concrete outcome `(b, h)` gives `(Fintype.card (BitVec n))⁻¹`, independent
    of `b` and `h`.  This is the quantitative content of "uniform pushforward":
    each `n`-bit value carries equal mass.  Combined with `card_bitvec`, the
    weight is exactly `(2 ^ n)⁻¹`. -/
theorem sample_apply_card_inv (n : Nat) (h : Heap) (b : BitVec n) :
    (SPComp.sample (BitVec n) h) (some (b, h))
      = (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ := by
  classical
  unfold SPComp.sample SDistr.bind
  rw [PMF.bind_apply]
  rw [tsum_eq_single (some b)]
  · rw [SDistr.uniform_apply_some]
    simp only [SDistr.pure, PMF.pure_apply]
    simp
  · intro ob hob
    cases ob with
    | none => simp [SDistr.uniform_apply_none]
    | some b' =>
      have hbb : b' ≠ b := fun heq => hob (by rw [heq])
      simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq]
      rw [if_neg (by intro hc; exact hbb hc.1.symm)]
      simp

/-- The uniform fibre weight, written explicitly as `(2 ^ n)⁻¹` via
    `card_bitvec`. -/
theorem sample_apply_value (n : Nat) (h : Heap) (b : BitVec n) :
    (SPComp.sample (BitVec n) h) (some (b, h)) = ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sample_apply_card_inv, card_bitvec]

/-- The uniform fibre weight is **nonzero** — every outcome is genuinely in the
    support.  (`(2 ^ n)⁻¹ ≠ 0` since `2 ^ n` is a positive `Nat`, not `⊤`.) -/
theorem sample_apply_ne_zero (n : Nat) (h : Heap) (b : BitVec n) :
    (SPComp.sample (BitVec n) h) (some (b, h)) ≠ 0 := by
  rw [sample_apply_value]
  simp

/-! ## Support agreement: deterministic image = probabilistic support -/

/-- Every concrete heap-paired `n`-bit value lies in the support of the
    probabilistic sample (at the matching heap).  This is the "support ⊇ image"
    half stated pointwise. -/
theorem mem_sample_support (n : Nat) (h : Heap) (b : BitVec n) :
    (b, h) ∈ (SPComp.sample (BitVec n) h).support :=
  sample_apply_ne_zero n h b

/-- The **deterministic leaf realizes a support point**: for every entropy
    source `η`, the deterministic outcome `(sampleDet η (.bv n), h)` is in the
    support of the probabilistic `SPComp.sample (BitVec n) h`.  This is the
    direct "deterministic image ⊆ probabilistic support" statement. -/
theorem sampleDet_mem_sample_support (n : Nat) (h : Heap) (η : Entropy) :
    (sampleDet η (.bv n), h) ∈ (SPComp.sample (BitVec n) h).support :=
  mem_sample_support n h (sampleDet η (.bv n))

/-- **Support agreement (headline).**  At a fixed heap `h`, the support of the
    probabilistic sample is *exactly* the image of the deterministic leaf
    `fun η => (sampleDet η (.bv n), h)`.

    `⊆` : a support point `(b, h')` forces `h' = h` (the sample never changes
    the heap) and `b` is hit by `entropyOf b` (surjectivity).
    `⊇` : every deterministic image point is in the support
    (`sampleDet_mem_sample_support`).

    This is the cleanest finite realization the `SDistr` API supports: the
    deterministic entropy-read leaf's image and the uniform sample's support
    coincide.  (The per-point mass is pinned uniform by `sample_apply_value`.) -/
theorem sample_support_eq_image (n : Nat) (h : Heap) :
    (SPComp.sample (BitVec n) h).support
      = Set.range (fun η : Entropy => (sampleDet η (.bv n), h)) := by
  ext ⟨b, h'⟩
  constructor
  · intro hmem
    -- A support point must keep the heap fixed at `h`.
    have hh : h' = h := by
      by_contra hne
      apply hmem
      classical
      unfold SPComp.sample SDistr.bind
      rw [PMF.bind_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro ob
      cases ob with
      | none => simp [SDistr.uniform_apply_none]
      | some b'' =>
        simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq]
        rw [if_neg (by intro hc; exact hne hc.2)]
        simp
    -- `(b, h') = (b, h)` is hit by `entropyOf b`.
    exact ⟨entropyOf b, by subst hh; exact Prod.ext (sampleDet_entropyOf b) rfl⟩
  · rintro ⟨η, hη⟩
    rw [← hη]
    exact sampleDet_mem_sample_support n h η

end CatCrypt.Crypto.SecureCompilation.Dialects.Rng
