/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit
public import Mathlib.Algebra.BigOperators.Fin

/-!
# HAWK 4-way: the negacyclic ring multiply and a non-vacuous lane tie

This module gives a non-vacuous per-lane block for the HAWK 4-way batched emit
(`HawkMul4WayEmit.lean`). The emit file carries a deliberately constant-zero
block (`hawkRingMulSpec := fun _ _ => fun _ => 0`) so that its
*lane-independence* corollary (`hawk_mul_4way_lane_map`) can be instantiated;
that corollary is parametric over the block and proves nothing about the ring
multiply. Here we build the per-lane negacyclic schoolbook product
over `Z/1024[x]/(x^N + 1)` (`N = 16`, HAWK-256's ring) as a clean
`HawkLane → HawkLane → HawkLane` function, and prove a lane-map equality at that
spec together with a *non-vacuous* ring-multiply property.

## Lane semantics: INDEPENDENT (verified)

The HAWK 4-way batches **four independent** negacyclic products — it is NOT a
4-quarter split of one product (contrast the NTT-mixing case). Evidence:

* `HawkMul4WayEmit`'s module header: "lane `b ∈ Fin 4` carries an independent
  `Z/q[x]/(x^n + 1)` instance" and the SoA layout "each `__m128i` holds the 4
  lanes' coefficient at one of the 16 positions".
* The external KAT `bench/hawk_compare/hawk_mul_4way_kat.c` computes the expected
  output by calling a per-lane scalar reference (`ref_hawk_lane_mul`)
  **independently for each of the 4 lanes** (its `expected[l]` loop), then
  unpacking the packed output lane-by-lane. There is no cross-lane term.

So the per-lane `LaneMap` frame is the correct one: the block is one
complete negacyclic product applied identically to each lane, and the lane-map
equality at the negacyclic spec is a true and non-vacuous statement.

## The negacyclic multiply

In `Z/q[x]/(x^N + 1)` the fold is `x^N ≡ -1`, so the wrapped half of the
schoolbook convolution is **subtracted**:

  `out[k] = Σ_{i ≤ k} a[i]·b[k-i]  −  Σ_{i > k} a[i]·b[(k-i+N)]   (mod q)`

Over `Zq1024 = ZMod 1024` subtraction is the ring negation, so the negacyclic
sign is exactly the `if i ≤ k then (+) else (−)` branch. `hawkNegacyclicMul`
realizes this as a `Finset.sum` over the term index `i : Fin N`, with partner
`j = (k - i) mod N`. This matches `HawkMulEmit.hawkMulCom` (the
`Com jasminDialect` straight-line kernel: positive terms for `i ≤ k`, the `sub`
op for `i > k`) and the KAT's `ref_hawk_lane_mul` term-for-term.

## Scope (read this)

What is proved **in Lean** here:

* `hawkNegacyclicMul` — the per-lane negacyclic product over `ZMod 1024`.
* `hawk_negacyclic_mul_one` — `1 · b = b` (the multiplicative unit acts trivially;
  a real ring identity, *false* for the constant-zero block).
* `hawk_negacyclic_shift` — multiplying by `X` (`a[1] = 1`, else `0`) performs the
  **negacyclic** rotation: `(X · b)[0] = −b[N-1]` and `(X · b)[k] = b[k-1]` for
  `k ≥ 1`. This is the headline non-vacuous statement: it uses the negacyclic
  *subtraction* (the `out[0] = −b[N-1]` sign is the `x^N = -1` fold), the one
  feature that distinguishes negacyclic from cyclic convolution. It is **false**
  for the constant-zero block and false for a cyclic (`+`) convolution.
* `hawk_mul_4way_lane_map_genuine` — the 4-way lane-map equality at the negacyclic
  block: batching the negacyclic multiply over the 4 lanes equals running it
  per-lane. Non-vacuous as a *ring-multiply* statement because the block is the
  real negacyclic product (combine with `hawk_negacyclic_shift` to see the lanes
  carry a non-trivial multiply).

What stays **KAT-gated** (NOT proved in Lean): the byte identity between the
emitted SIMD `.jazz` (`bench/hawk_compare/gen/hawk_mul_4way.jazz`, with its
packed `#VPMULL_4u32`/`#VPADD_4u32`/`#VPSUB_4u32` and `& 1023`) and this
per-lane reference is carried by the external `hawk_mul_4way_kat.c`. We do **not**
claim the emitted SIMD kernel is proven to compute `hawkNegacyclicMul` — that is
the external KAT's job. This module gives the negacyclic spec, the
in-Lean negacyclic-multiply correctness (unit + shift) and the lane tie.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayRealization

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit (Zq1024 N HawkLane Hawk4Way Hawk4WayInputs)

/-! ## 1. The negacyclic ring multiply -/

/-- The negacyclic-convolution **sign-and-term** at output coefficient `k` and
    term index `i`: the product `a[i] · b[(k - i) mod N]`, taken **positive**
    when `i ≤ k` (no wrap, `i + j = k`) and **negative** when `i > k` (the
    wrapped half, `i + j = k + N`, carrying the `x^N = -1` sign). Over
    `ZMod 1024` the sign is the ring negation. -/
def negaTerm (a b : HawkLane) (k i : Fin N) : Zq1024 :=
  let j : Fin N := ⟨(k.val + N - i.val) % N, Nat.mod_lt _ (by decide)⟩
  if i.val ≤ k.val then a i * b j else -(a i * b j)

/-- The per-lane HAWK negacyclic schoolbook product over
    `Z/1024[x]/(x^N + 1)`:

      `out[k] = Σ_{i : Fin N} negaTerm a b k i
              = Σ_{i ≤ k} a[i]·b[k-i] − Σ_{i > k} a[i]·b[(k-i+N) mod N]`.

    This is the block the 4-way emit batches over 4 independent lanes;
    it mirrors `HawkMulEmit.hawkMulCom` and the KAT's `ref_hawk_lane_mul`
    term-for-term. **Not** the constant-zero block of
    `HawkMul4WayEmit.hawkRingMulSpec`. -/
def hawkNegacyclicMul (a b : HawkLane) : HawkLane :=
  fun k => ∑ i : Fin N, negaTerm a b k i

/-! ## 2. Non-vacuous ring-multiply properties

These are algebraic facts about `hawkNegacyclicMul` — each is *false*
for the constant-zero block, so they certify the spec is the real
negacyclic product, not a vacuous stand-in. -/

/-- The multiplicative unit `1` (the constant polynomial `1`, i.e. `1[0] = 1`,
    `1[k] = 0` for `k ≠ 0`) acts trivially: `1 · b = b`. A ring identity
    — for `1`, the only surviving term in `out[k]` is `i = 0`
    (`a[0]·b[k] = b[k]`, positive since `0 ≤ k`); all `i > 0` terms vanish. This
    is **false** for the constant-zero block. -/
theorem hawk_negacyclic_mul_one (b : HawkLane) :
    hawkNegacyclicMul (fun k => if k.val = 0 then 1 else 0) b = b := by
  funext k
  have hk : k.val < 16 := k.isLt
  unfold hawkNegacyclicMul negaTerm
  rw [Finset.sum_eq_single (⟨0, by decide⟩ : Fin N)]
  · -- the i = 0 term: a[0] = 1, j = (k - 0) mod N = k, 0 ≤ k ⇒ + a[0]·b[k] = b[k]
    have hle : (⟨0, by decide⟩ : Fin N).val ≤ k.val := Nat.zero_le _
    have hjk : (⟨(k.val + N - (⟨0, by decide⟩ : Fin N).val) % N,
        Nat.mod_lt _ (by decide)⟩ : Fin N) = k := by
      apply Fin.ext
      show (k.val + 16 - 0) % 16 = k.val
      omega
    simp only [ite_eq_left hle, hjk]
    norm_num
  · -- i ≠ 0 ⇒ a[i] = 0 ⇒ term = 0
    intro i _ hi
    have hi0 : i.val ≠ 0 := fun h => hi (by apply Fin.ext; simp [h])
    simp only [hi0, ite_false]
    by_cases hle : i.val ≤ k.val <;> simp [hle]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The negacyclic shift (headline non-vacuous property).** Multiplying by the
    monomial `X` (`a[1] = 1`, all other coefficients `0`) is the **negacyclic
    rotation**: every coefficient shifts up by one position, and the top
    coefficient wraps into position `0` with a **minus sign** (the `x^N = -1`
    fold):

      `(X · b)[0]     = − b[N-1]`     (the wrapped, *subtracted* term)
      `(X · b)[k]     =   b[k-1]`     for `k ≥ 1`.

    This is the property that distinguishes the **negacyclic** product
    from a cyclic one: the wrap at position `0` is negated. It uses the `i > k`
    branch (`negaTerm`'s subtraction) at `k = 0`, `i = 1`. It is **false** for
    the constant-zero block and **false** for the cyclic (`+`) convolution.

    Stated as the single equation `(X · b)[k] = (if k = 0 then −b[N-1] else
    b[k-1])`. -/
theorem hawk_negacyclic_shift (b : HawkLane) (k : Fin N) :
    hawkNegacyclicMul (fun i => if i.val = 1 then 1 else 0) b k
      = (if k.val = 0 then -(b ⟨N - 1, by decide⟩) else b ⟨k.val - 1, by omega⟩) := by
  have hk : k.val < 16 := k.isLt
  unfold hawkNegacyclicMul negaTerm
  -- Only the i = 1 term survives (a[i] = 0 for i ≠ 1).
  rw [Finset.sum_eq_single (⟨1, by decide⟩ : Fin N)]
  · -- the i = 1 term: a[1] = 1, so the surviving term is ± b[(k - 1 + N) mod N]
    have hidx1 : (⟨1, by decide⟩ : Fin N).val = 1 := rfl
    by_cases hk0 : k.val = 0
    · -- k = 0: 1 ≤ 0 is false ⇒ negative term, j = (0 + N - 1) % N = N - 1
      have hle : ¬ ((⟨1, by decide⟩ : Fin N).val ≤ k.val) := by rw [hidx1]; omega
      have hjk : (⟨(k.val + N - (⟨1, by decide⟩ : Fin N).val) % N,
          Nat.mod_lt _ (by decide)⟩ : Fin N) = (⟨N - 1, by decide⟩ : Fin N) := by
        apply Fin.ext
        show (k.val + 16 - 1) % 16 = 16 - 1
        omega
      simp only [ite_eq_right hle, ite_eq_left hk0, hjk]
      norm_num
    · -- k ≥ 1: 1 ≤ k ⇒ positive term, j = (k + N - 1) % N = k - 1
      have hle : (⟨1, by decide⟩ : Fin N).val ≤ k.val := by rw [hidx1]; omega
      have hjk : (⟨(k.val + N - (⟨1, by decide⟩ : Fin N).val) % N,
          Nat.mod_lt _ (by decide)⟩ : Fin N) = (⟨k.val - 1, by omega⟩ : Fin N) := by
        apply Fin.ext
        show (k.val + 16 - 1) % 16 = k.val - 1
        omega
      simp only [ite_eq_left hle, ite_eq_right hk0, hjk]
      norm_num
  · -- i ≠ 1 ⇒ a[i] = 0 ⇒ term = 0
    intro i _ hi
    have hi1 : i.val ≠ 1 := fun h => hi (by apply Fin.ext; simp [h])
    simp only [hi1, ite_false]
    by_cases hle : i.val ≤ k.val <;> simp [hle]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 3. The 4-way lane-map tie

The lane-map equality at the **negacyclic** block. Because the block is the
negacyclic product (not `id`/`0`), this is a non-vacuous *ring-multiply*
statement: it says the 4-way SIMD batching computes, on each of the 4 lanes,
`hawkNegacyclicMul` — combine with `hawk_negacyclic_shift` /
`hawk_negacyclic_mul_one` to see the lanes carry a non-trivial multiply. -/

/-- The negacyclic block in lane-curried form (the `f : α → β` the lane-map theorem
    is instantiated at, with `α = HawkLane × HawkLane`, `β = HawkLane`). -/
def hawkNegacyclicMulPair : HawkLane × HawkLane → HawkLane :=
  fun ab => hawkNegacyclicMul ab.1 ab.2

/-- **HAWK 4-way lane-map equality at the negacyclic multiply.** Applying
    the per-lane negacyclic product to each of the 4 lane-pairs in
    parallel equals running it sequentially on each lane-pair. Unlike
    `HawkMul4WayEmit.hawk_mul_4way_denotation_preserves` (whose block is the
    constant-zero block), the block here is the real
    `hawkNegacyclicMul`, so this is a non-vacuous ring-multiply statement: each
    lane computes the HAWK negacyclic product (cf. `hawk_negacyclic_shift`,
    `hawk_negacyclic_mul_one`). The byte identity emit↔reference stays KAT-gated
    (`hawk_mul_4way_kat.c`). -/
theorem hawk_mul_4way_lane_map_genuine (lanes : Hawk4WayInputs) :
    LaneMap.laneMap hawkNegacyclicMulPair lanes
      = (fun b => hawkNegacyclicMulPair (lanes b)) := by
  funext i
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayRealization
