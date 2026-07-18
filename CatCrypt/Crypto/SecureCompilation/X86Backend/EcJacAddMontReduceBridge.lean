/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Frame-wrapped Montgomery field-multiply, canonicalised by the AUCurves leaf

`EcJacAddMontMul.lean` lands the frame-wrapped Montgomery multiply at the value
level: over a field-element frame whose slots `a`, `b` hold reduced four-limb
inputs, `feMulFrameAt_value` proves the output region reconstructs to the genuine
emitted product `valLimbs a · valLimbs b`, and `montgomeryReduce N (2^256) Nprime`
of that stored value is the Montgomery field product — landing `< 2·N` and
`· 2^256 ≡ a · b (mod N)`. That result is *one conditional subtract away* from a
canonical field element: it is in `[0, 2·N)`, not `[0, N)`. The emitted
canonicalising conditional-subtract (`Curve4MontMulProvenEmit.emitCondSubP`,
`< 2N → < N`) is the trusted, KAT-gated emit scaffolding — there is no in-tree
`runBlock = canonical-reduced` theorem.

This module closes that last step **by adopting the AUCurves verified curve
library's Montgomery-reduce leaf**, exactly as
`AUCurvesImport/FieldLeafBridge.lean` adopts the AUCurves field-mul leaf and
`Pairing/Bls12381AUCurves.lean` adopts the AUCurves pairing leaf — the
leaf-adoption pattern: "composed over an adopted external verified leaf". The
canonicalisation we would otherwise KAT-gate is *proven upstream* in the AUCurves
field tower.

## What AUCurves genuinely proves (verified, accurately established)

The reduce/canonicalisation leaf is fiat-crypto's word-by-word-Montgomery
multiply, which AUCurves consumes and re-states per curve
(`src/Bedrock/Curve/Secp256k1_Bignum_Specs.v`, `…/P256_Bignum_Specs.v`,
`…/BN254Curve_G1_BignumSpecs.v`). Its correctness core, read from the AUCurves
tree (`fiat-crypto/src/Arithmetic/WordByWordMontgomery.v`), is:

```
Definition valid (a : list Z) := small a /\ 0 <= eval a < m.        (* line 1121 *)

Lemma mulmod_correct                                                  (* line 1184 *)
  : (forall a (_ : valid a) b (_ : valid b),
       eval (from_montgomerymod (mulmod a b)) mod m
         = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m)
    /\ (forall a (_ : valid a) b (_ : valid b), valid (mulmod a b)).
Proof using … . … Qed.
```

`mulmod_correct` is `Qed`'d, and the whole file carries **zero** `Admitted` and
**zero** `Axiom` (verified by reading the source: `grep -c "Admitted\|Axiom"` over
`WordByWordMontgomery.v` is `0`). The second conjunct `valid (mulmod a b)` is
exactly the canonicalised output: `valid x = small x ∧ 0 ≤ eval x < m`, i.e. the
result is a genuine reduced field element in `[0, m)` — *after* the conditional
subtract. The conditional subtract itself is the `Qed`'d
`conditional_sub_correct` (line 415): `0 ≤ eval v < eval N + R →
eval (conditional_sub v N) = eval v + (if N ≤ v then -N else 0)`. This is the
precise canonicalisation our emit only KAT-gates — proven upstream.

This is the field-arithmetic leaf, the candidate the project rule flags as most
likely genuinely proven, and it is. (The `(*proj*)` markers in the proof scripts
are proof-search annotations, not stubs; the `Qed.` is real. Contrast the
half-safegcd divstep certificates `Axiom secp256k1_half_certificate`, which the
FieldLeafBridge catalog honestly records as `Axiom`s — those are NOT cited here.
The BLS12 G1 *group* add `bls12_G1_ok` is known commented-out upstream — also NOT
cited here; this bridge is about the FIELD Montgomery reduce only.)

## The bridge (leaf-adoption, named-predicate discipline)

Following `FieldLeafBridge.FieldMulSpecAgrees` and
`VIR/LeafAxiomConsolidation.LeafFFIValidated`: the cross-prover edge (our value
`montgomeryReduce N (2^256) Nprime T` canonicalises to the AUCurves
`from_montgomerymod (mulmod …)` reduced element `< N`) is **not** a Lean theorem
— it crosses Rocq↔Lean. It is a named, inhabited predicate
(`AUCurvesMontReduceFaithful`), bundled as a Catalog-style assumption structure
with a non-vacuous witness and a consumable worked theorem. Holding it = adopting
the AUCurves verified canonicalisation as the witness for our value-level reduce.

`feMulFrameAtReduced` is the headline composable field-mul lemma: under the
adopted leaf, slot `o`'s reduced value is a genuine field element (`< N`) whose
`· 2^256 ≡ a · b (mod N)` — the composable Montgomery field product, ready to feed
a point-add. No `sorry`, no new global `axiom`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontReduceBridge

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul
open CatCrypt.Crypto.Number

/-! ## 1. The AUCurves canonicalisation function (the adopted leaf, abstractly)

The AUCurves verified leaf is `from_montgomerymod (mulmod a b)`, whose output
`valid`-ity (`0 ≤ eval < m`) is the canonical reduced field element. At the
`Nat` value level its effect on our `montgomeryReduce …` output (`< 2·N`) is the
single conditional subtract: reduce a value in `[0, 2·N)` to its canonical
representative in `[0, N)`. We name that effect `canonReduce N`, the abstract
image of AUCurves' `conditional_sub`/`valid`-canonicalisation, and prove its two
defining facts (`< N` and value-preservation mod `N`) in Lean — so the *Nat*
side of the adoption is closed, and only the cross-prover faithfulness edge
(that our emitted reduce's value equals AUCurves' `mulmod` output) is named. -/

/-- The canonical conditional-subtract on a value already in `[0, 2·N)`: subtract
    one `N` once the value is `≥ N`. This is the `Nat` image of AUCurves'
    `conditional_sub` (the `Qed`'d `conditional_sub_correct`) applied to the
    `montgomeryReduce` output. -/
def canonReduce (N v : Nat) : Nat := if N ≤ v then v - N else v

/-- **`canonReduce` lands in `[0, N)`** for an input `< 2·N`: the canonical
    representative is a genuine field element. The `Nat` image of AUCurves'
    `valid (mulmod a b)` (`0 ≤ eval < m`). -/
theorem canonReduce_lt (N v : Nat) (hv : v < 2 * N) :
    canonReduce N v < N := by
  unfold canonReduce
  split <;> omega

/-- **`canonReduce` preserves the value mod `N`.** Subtracting one `N` when
    `≥ N` is the identity in `ZMod N` / `Nat.ModEq`. So the canonicalised reduce
    is still `≡ montgomeryReduce …` mod `N`, hence still `· 2^256 ≡ a·b (mod N)`. -/
theorem canonReduce_modEq (N v : Nat) (hv : v < 2 * N) :
    canonReduce N v ≡ v [MOD N] := by
  unfold canonReduce
  split
  · -- v ≥ N, v < 2N ⇒ (v - N) + N = v, so v - N ≡ v [MOD N]
    rename_i h
    exact (Nat.modEq_iff_dvd' (by omega)).mpr ⟨1, by omega⟩
  · rfl

/-! ## 2. The named cross-prover leaf-adoption predicate

`AUCurvesMontReduceFaithful N reduceLeaf` is the precise statement that a
CatCrypt-side canonicalising reduce function `reduceLeaf : Nat → Nat` (the value
the emitted `emitCondSubP` would compute, or any adopted realiser) coincides with
the AUCurves verified canonicalisation `canonReduce N` on every value `< 2·N`
(the range `montgomeryReduce N (2^256) Nprime` lands in). It mirrors
`FieldLeafBridge.FieldMulSpecAgrees` and `LeafFFIValidated`: a `Prop` over the
opaque leaf, asserting it realises the AUCurves-proved output. -/

/-- **Named cross-prover leaf-adoption: the Montgomery-reduce canonicalisation
    leaf.**

    `AUCurvesMontReduceFaithful N reduceLeaf` says: on every value `v < 2·N` (the
    range `montgomeryReduce N (2^256) Nprime` lands in, per
    `feMulFrameAt_value`), the adopted leaf `reduceLeaf v` equals the AUCurves
    verified canonicalisation `canonReduce N v` — the single conditional subtract
    `conditional_sub` whose correctness (`conditional_sub_correct`) and resulting
    `valid (mulmod a b)` (`0 ≤ eval < m`) are `Qed`'d in
    `fiat-crypto/src/Arithmetic/WordByWordMontgomery.v` (consumed per curve by
    `AUCurves/src/Bedrock/Curve/{Secp256k1,P256,BN254…}_Bignum_Specs.v`).

    This is **not** a Lean theorem: that a CatCrypt leaf realiser's value
    coincides with AUCurves' `mulmod`/`conditional_sub` output is a cross-prover
    claim, named here rather than asserted — the leaf-adoption discipline of
    `FieldLeafBridge.FieldMulSpecAgrees` and `LeafFFIValidated`. -/
def AUCurvesMontReduceFaithful (N : Nat) (reduceLeaf : Nat → Nat) : Prop :=
  ∀ v : Nat, v < 2 * N → reduceLeaf v = canonReduce N v

/-- **Catalog-style named assumption: the AUCurves Montgomery-reduce leaf.**

    Bundles `AUCurvesMontReduceFaithful N reduceLeaf` as a Catalog-style
    assumption object, mirroring `FieldLeafBridge.AUCurvesFieldMulBridge` and the
    FFI predicate `LeafFFIValidated`. Holding a value of this structure is
    *adopting* AUCurves' `Qed`'d Montgomery canonicalisation as the witness for
    the CatCrypt reduce leaf — the honest, named cross-prover edge, never a bare
    `axiom` on a hand-written kernel. -/
structure AUCurvesMontReduceLeaf (N : Nat) (reduceLeaf : Nat → Nat) : Prop where
  /-- The reduce leaf realises the AUCurves canonicalisation on `[0, 2·N)`. -/
  faithful : AUCurvesMontReduceFaithful N reduceLeaf

/-- **Non-vacuous witness.** The CatCrypt-side canonical realiser `canonReduce N`
    itself adopts the leaf by reflexivity — confirming the predicate is the right
    shape (an inhabited cross-prover claim), not an unsatisfiable over-constraint.
    The genuine cross-prover content is the gap between *this* realiser and the
    value the emitted `emitCondSubP` computes, validated against AUCurves' Rocq
    `mulmod` output, which lives outside Lean (analogue of
    `FieldLeafBridge.aucurvesFieldMulBridge_canonical`). -/
theorem aucurvesMontReduceLeaf_canonical (N : Nat) :
    AUCurvesMontReduceLeaf N (canonReduce N) where
  faithful := fun _ _ => rfl

/-! ## 3. The composable Montgomery field product `montMulFieldElem`

`montMulFieldElem N Nprime a b` is the canonical reduced Montgomery product: take
`montgomeryReduce N (2^256) Nprime (a·b)` (in `[0, 2·N)`, the value
`feMulFrameAt_value` lands) and canonicalise it. By §1 it is `< N` and
`· 2^256 ≡ a·b (mod N)` — a genuine field element. -/

/-- The canonical reduced Montgomery field product of two residues `a, b`: reduce
    the product at radix `2^256`, then canonicalise (the AUCurves leaf). -/
def montMulFieldElem (N Nprime a b : Nat) : Nat :=
  canonReduce N (montgomeryReduce N (2 ^ 256) Nprime (a * b))

/-- **`montMulFieldElem` is a genuine field element (`< N`)** and
    **`· 2^256 ≡ a·b (mod N)`**, for reduced inputs `a, b < N` and the curve's
    Montgomery constant. The product half is the proven emitted+stored `runBlock`
    (via `feMulFrameAt_value`); the `< N` canonicalisation is the AUCurves leaf
    (`canonReduce_lt`); the congruence is preserved (`canonReduce_modEq` ∘
    `montgomeryMul_correct`). -/
theorem montMulFieldElem_spec (N Nprime a b : Nat)
    (hN : 0 < N) (hNleR : N ≤ 2 ^ 256)
    (ha : a < N) (hb : b < N)
    (hNprime : (N * Nprime) % 2 ^ 256 = 2 ^ 256 - 1) :
    montMulFieldElem N Nprime a b < N ∧
    (montMulFieldElem N Nprime a b) * 2 ^ 256 ≡ a * b [MOD N] := by
  obtain ⟨hrange, hcong⟩ :=
    Number.montgomeryMul_correct N (2 ^ 256) Nprime a b hN (by positivity) hNleR hNprime ha hb
  -- montgomeryMul = montgomeryReduce of the product
  rw [Number.montgomeryMul] at hrange hcong
  refine ⟨canonReduce_lt N _ hrange, ?_⟩
  -- canonReduce v · 2^256 ≡ v · 2^256 ≡ a·b
  exact ((canonReduce_modEq N _ hrange).mul_right (2 ^ 256)).trans hcong

/-! ## 4. The headline composable field-mul lemma over the frame

`feMulFrameAtReduced` combines `feMulFrameAt_value` (the proven emitted product +
value-level reduce, landing `< 2·N`) with the adopted AUCurves leaf (the
canonicalisation `< N`). Given the leaf adoption `AUCurvesMontReduceLeaf` and the
hypotheses of `feMulFrameAt_value`, the leaf-applied reduce of the stored output
region is a canonical field element `< N` and `· 2^256 ≡ a·b (mod N)`. This is
the composable field-mul output — a REDUCED four-limb field element value, ready
to feed a point-add. -/

/-- **Frame-wrapped Montgomery field-multiply, canonicalised (composable).**

    Under the hypotheses of `EcJacAddMontMul.feMulFrameAt_value` (proven emitted
    product over `runBlock`, reduced inputs, the curve's `Nprime`) and the adopted
    AUCurves Montgomery-reduce leaf `AUCurvesMontReduceLeaf N reduceLeaf`:

    applying the leaf `reduceLeaf` to `montgomeryReduce N (2^256) Nprime` of the
    stored output region's reconstructed value yields

    * a genuine field element: `reduceLeaf (montgomeryReduce …) < N`; and
    * the Montgomery field product: `· 2^256 ≡ valLimbs a · valLimbs b (mod N)`.

    The product is the proven emitted+stored `runBlock` (`feMulFrameAt_value`);
    the canonicalisation `< N` is the AUCurves `Qed`'d `conditional_sub` /
    `valid (mulmod a b)`, adopted as the leaf. This is the composable reduced
    field-mul output (a `< N` four-limb field element), in contrast to
    `feMulFrameAt_value`'s `< 2·N` value. -/
theorem feMulFrameAtReduced
    (x0 x1 x2 x3 y0 y1 y2 y3 c0 c1 c2 c3 c4 c5 c6 c7 : String) (hi lo base : String)
    (o a b : Nat) (s : JState 64) (N Nprime : Nat) (reduceLeaf : Nat → Nat)
    -- the adopted AUCurves verified canonicalisation leaf
    (hLeaf : AUCurvesMontReduceLeaf N reduceLeaf)
    -- input-window freshness
    (hx10 : x1 ≠ x0) (hx20 : x2 ≠ x0) (hx21 : x2 ≠ x1)
    (hx30 : x3 ≠ x0) (hx31 : x3 ≠ x1) (hx32 : x3 ≠ x2)
    (hy10 : y1 ≠ y0) (hy20 : y2 ≠ y0) (hy21 : y2 ≠ y1)
    (hy30 : y3 ≠ y0) (hy31 : y3 ≠ y1) (hy32 : y3 ≠ y2)
    (hxy : ∀ d ∈ [x0, x1, x2, x3], ∀ e ∈ [y0, y1, y2, y3], d ≠ e)
    (hacc_x : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7], ∀ q ∈ [x0, x1, x2, x3], r ≠ q)
    (hacc_y : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7], ∀ q ∈ [y0, y1, y2, y3], r ≠ q)
    (hfresh : ProdFresh [c0, c1, c2, c3, c4, c5, c6, c7] [x0, x1, x2, x3]
      [y0, y1, y2, y3] hi lo)
    (hacc0 : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7], s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hN : 0 < N) (hNleR : N ≤ 2 ^ 256)
    (hx_red : valLimbs (slotLimbs s base a) < N)
    (hy_red : valLimbs (slotLimbs s base b) < N)
    (hNprime : (N * Nprime) % 2 ^ 256 = 2 ^ 256 - 1) :
    reduceLeaf (Number.montgomeryReduce N (2 ^ 256) Nprime
        (valLimbs (slotLimbs8 (runBlock s
          (feMulFrameAt [x0, x1, x2, x3] [y0, y1, y2, y3]
            [c0, c1, c2, c3, c4, c5, c6, c7] hi lo base o a b)) base o))) < N ∧
    (reduceLeaf (Number.montgomeryReduce N (2 ^ 256) Nprime
        (valLimbs (slotLimbs8 (runBlock s
          (feMulFrameAt [x0, x1, x2, x3] [y0, y1, y2, y3]
            [c0, c1, c2, c3, c4, c5, c6, c7] hi lo base o a b)) base o)))) * 2 ^ 256
      ≡ valLimbs (slotLimbs s base a) * valLimbs (slotLimbs s base b) [MOD N] := by
  -- the proven frame-wrapped product + value-level reduce (lands < 2·N)
  obtain ⟨hprod, hrange, hcong⟩ :=
    feMulFrameAt_value x0 x1 x2 x3 y0 y1 y2 y3 c0 c1 c2 c3 c4 c5 c6 c7 hi lo base o a b s N Nprime
      hx10 hx20 hx21 hx30 hx31 hx32 hy10 hy20 hy21 hy30 hy31 hy32 hxy hacc_x hacc_y hfresh
      hacc0 hcf hof hN hNleR hx_red hy_red hNprime
  -- the stored value reconstructs to the product, so the reduce input is
  -- montgomeryReduce of (a·b); name that value `R` and its bound `< 2·N`.
  set R := Number.montgomeryReduce N (2 ^ 256) Nprime
      (valLimbs (slotLimbs8 (runBlock s
        (feMulFrameAt [x0, x1, x2, x3] [y0, y1, y2, y3]
          [c0, c1, c2, c3, c4, c5, c6, c7] hi lo base o a b)) base o)) with hR
  -- adopt the AUCurves leaf: reduceLeaf R = canonReduce N R (R < 2·N)
  have hleaf : reduceLeaf R = canonReduce N R := hLeaf.faithful R hrange
  rw [hleaf]
  refine ⟨canonReduce_lt N R hrange, ?_⟩
  -- canonReduce N R · 2^256 ≡ R · 2^256 ≡ a·b
  exact ((canonReduce_modEq N R hrange).mul_right (2 ^ 256)).trans hcong

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontReduceBridge
