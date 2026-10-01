/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttInverse
public import CatCrypt.Crypto.Optimizer.Lattice.SignedNegacyclicConv

/-!
# The negacyclic NTT turns the product of `R_q` into block products

After `L` layers on `N = 2 ^ M` lanes, `nttSpec` holds in block `c` of length
`B = 2 ^ (M - L)` the residue of the input modulo `X ^ B - γ_c`, with
`γ_c = ψ ^ (2 · BitRev_L c + 1)`.  This file proves once, for every `M`, `L ≤ M`
and `ψ` with `ψ ^ (2 ^ L) = -1`, that the transform of the negacyclic product
in `R[X]/(X ^ N + 1)` is the blockwise product modulo `X ^ B - γ_c` of the
transforms.  At `L = M` the blocks have length one and the block product is the
pointwise product; at ML-KEM's `B = 2` it is FIPS 203's `BaseCaseMultiply`.

## Main definitions

* `negaMul` — the negacyclic product of two lane functions of length `N`.
* `blockRoot` — the root `ψ ^ (2 · BitRev_L c + 1)` of block `c`.
* `blockMul` — the product in `R[X]/(X ^ B - γ_c)` within every block.
* `finLanes` — a coefficient vector on `Fin N` as a lane function.

## Main results

* `nttSpec_negaMul` — `nttSpec (negaMul a b) = blockMul (nttSpec a) (nttSpec b)`
  on the first `N` lanes.
* `blockMul_one` — with blocks of length one, `blockMul` is the pointwise product.
* `blockMul_congr` — `blockMul` reads its operands on the first `K · B` lanes only.
* `negaMul_eq_signedNegaConv` — `negaMul` is `signedNegaConv` on `Fin N`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

open Finset
open CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric (bitrev)

variable {R : Type*} [CommRing R]

/-- The negacyclic product in `R[X]/(X ^ N + 1)` of the lane functions `a` and
`b` of length `N`: the pairs with `i + j = k` count `+1`, those with
`i + j = k + N` count `-1`. -/
def negaMul (N : ℕ) (a b : ℕ → R) (k : ℕ) : R :=
  ∑ i ∈ range N, ∑ j ∈ range N,
    a i * b j * (if i + j = k then 1 else if i + j = k + N then -1 else 0)

/-- The root of block `c` after `L` layers: `ψ ^ (2 · BitRev_L c + 1)`. -/
def blockRoot (ψ : R) (L c : ℕ) : R := ψ ^ (2 * bitrev L c + 1)

/-- The product within every block of length `B` in `R[X]/(X ^ B - γ c)`: lane
`c · B + t` collects the pairs with `u + v = t` with weight `1` and those with
`u + v = t + B` with weight `γ c`. -/
def blockMul (B : ℕ) (γ : ℕ → R) (a b : ℕ → R) (i : ℕ) : R :=
  ∑ u ∈ range B, ∑ v ∈ range B, a (i / B * B + u) * b (i / B * B + v) *
    (if u + v = i % B then 1 else if u + v = i % B + B then γ (i / B) else 0)

/-! ## 1. Collapsing the indicator sums -/

theorem eq_add_mul_iff (B t s m : ℕ) (hB : 0 < B) (ht : t < B) :
    m = t + s * B ↔ (s = m / B ∧ m % B = t) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt ht, Nat.zero_add]
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · rintro ⟨rfl, rfl⟩
    exact (Nat.mod_add_div' m B).symm

theorem sum_pow_indicator (γ : R) (K B t m : ℕ) (hB : 0 < B) (ht : t < B) :
    ∑ s ∈ range K, γ ^ s * (if m = t + s * B then (1 : R) else 0)
      = if m % B = t ∧ m / B < K then γ ^ (m / B) else 0 := by
  simp only [eq_add_mul_iff B t _ m hB ht]
  by_cases hm : m % B = t
  · simp only [hm, and_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (range K) (m / B) (fun s => γ ^ s)]
    simp [Finset.mem_range]
  · simp [hm]

/-- The weight of a pair with `i + j = m`, summed over the blocks' powers of `γ`. -/
theorem sum_pow_weight (γ : R) (K B t m : ℕ) (hB : 0 < B) (ht : t < B)
    (hγ : γ ^ K = -1) (hm : m < 2 * (K * B)) :
    ∑ s ∈ range K, γ ^ s *
        (if m = t + s * B then 1 else if m = t + s * B + K * B then -1 else 0)
      = if m % B = t then γ ^ (m / B) else 0 := by
  by_cases hlt : m < K * B
  · have hrw : ∀ s, (if m = t + s * B then (1 : R) else if m = t + s * B + K * B then -1 else 0)
        = if m = t + s * B then 1 else 0 := fun s => by
      by_cases h1 : m = t + s * B
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1, if_neg (by omega)]
    simp only [hrw]
    rw [sum_pow_indicator γ K B t m hB ht]
    have hd : m / B < K := by rw [Nat.div_lt_iff_lt_mul hB]; exact hlt
    simp [hd]
  · have hrw : ∀ s, s < K → (if m = t + s * B then (1 : R) else
          if m = t + s * B + K * B then -1 else 0)
        = -(if m - K * B = t + s * B then 1 else 0) := fun s hs => by
      have hsB : s * B + B ≤ K * B := by
        have := Nat.mul_le_mul_right B (show s + 1 ≤ K by omega)
        rw [Nat.add_mul, one_mul] at this; exact this
      rw [if_neg (by omega)]
      by_cases h2 : m - K * B = t + s * B
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2, neg_zero]
    rw [Finset.sum_congr rfl (fun s hs => by rw [hrw s (Finset.mem_range.mp hs)])]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [sum_pow_indicator γ K B t (m - K * B) hB ht]
    have hmod : (m - K * B) % B = m % B := by
      conv_rhs => rw [show m = (m - K * B) + K * B from by omega]
      rw [Nat.add_mul_mod_self_right]
    have hdiv : (m - K * B) / B = m / B - K := by
      have h1 : m = (m - K * B) + K * B := by omega
      have h2 : m / B = (m - K * B) / B + K := by
        conv_lhs => rw [h1]
        rw [Nat.add_mul_div_right _ _ hB]
      rw [h2, Nat.add_sub_cancel]
    have hdK : (m - K * B) / B < K := by
      rw [Nat.div_lt_iff_lt_mul hB]
      exact Nat.sub_lt_left_of_lt_add (by omega) (by rw [two_mul] at hm; exact hm)
    have hge : K ≤ m / B := by
      rw [Nat.le_div_iff_mul_le hB]; omega
    rw [hmod, hdiv]
    by_cases ht' : m % B = t
    · have hdK' : m / B - K < K := by omega
      simp only [ht', hdK', and_self, if_true]
      rw [show m / B = (m / B - K) + K from by omega, pow_add, hγ]
      simp only [Nat.add_sub_cancel]
      ring
    · simp [ht']

/-! ## 2. Reindexing the lanes by blocks -/

theorem sum_range_mul_blocks {M : Type*} [AddCommMonoid M] (B : ℕ) (f : ℕ → M) :
    ∀ K : ℕ, ∑ i ∈ range (K * B), f i = ∑ s ∈ range K, ∑ u ∈ range B, f (u + s * B)
  | 0 => by simp
  | K + 1 => by
      rw [Nat.add_mul, one_mul, Finset.sum_range_add, sum_range_mul_blocks B f K,
        Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Nat.add_comm (K * B) u]

/-- The block weight of a pair `(u + s B, v + s' B)` is the summed weight of
their lane sum. -/
theorem block_weight (γ : R) (B t u v s s' : ℕ) (hB : 0 < B) (ht : t < B) (hu : u < B)
    (hv : v < B) :
    γ ^ s * γ ^ s' * (if u + v = t then 1 else if u + v = t + B then γ else 0)
      = if (u + s * B + (v + s' * B)) % B = t then γ ^ ((u + s * B + (v + s' * B)) / B)
        else 0 := by
  have he : u + s * B + (v + s' * B) = (u + v) + (s + s') * B := by ring
  rw [he, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hB]
  by_cases h1 : u + v = t
  · rw [if_pos h1, if_pos (by rw [h1, Nat.mod_eq_of_lt ht]), h1, Nat.div_eq_of_lt ht,
      Nat.zero_add, pow_add, mul_one]
  · by_cases h2 : u + v = t + B
    · rw [if_neg h1, if_pos h2, if_pos (by rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt ht]), h2,
        show (t + B) / B = 1 from by
          rw [Nat.add_div_right _ hB, Nat.div_eq_of_lt ht], pow_add, pow_add, pow_one]
      ring
    · rw [if_neg h1, if_neg h2, mul_zero, if_neg]
      intro hmod
      have hlt : u + v < B + B := by omega
      rcases Nat.lt_or_ge (u + v) B with h | h
      · rw [Nat.mod_eq_of_lt h] at hmod; exact h1 hmod
      · have : (u + v) % B = u + v - B := by
          rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
        omega

/-! ## 3. The product theorem -/

/-- `nttSpec` written with the block root. -/
theorem nttSpec_eq_blockRoot (ψ : R) (L M : ℕ) (f : ℕ → R) (i : ℕ) :
    nttSpec ψ L M f i = ∑ s ∈ range (2 ^ L),
      f (i % 2 ^ (M - L) + s * 2 ^ (M - L)) * blockRoot ψ L (i / 2 ^ (M - L)) ^ s := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [blockRoot, ← pow_mul]

theorem blockRoot_pow (ψ : R) (L : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (c : ℕ) :
    blockRoot ψ L c ^ (2 ^ L) = -1 := by
  rw [blockRoot, ← pow_mul, mul_comm, pow_mul, hψ, pow_succ, pow_mul, neg_one_sq, one_pow,
    one_mul]

/-- **The transform of the negacyclic product is the block product of the
transforms.** -/
theorem nttSpec_negaMul (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (hLM : L ≤ M)
    (a b : ℕ → R) (i : ℕ) :
    nttSpec ψ L M (negaMul (2 ^ M) a b) i
      = blockMul (2 ^ (M - L)) (blockRoot ψ L) (nttSpec ψ L M a) (nttSpec ψ L M b) i := by
  set B := 2 ^ (M - L) with hBdef
  set K := 2 ^ L with hKdef
  have hB : 0 < B := Nat.two_pow_pos _
  have hN : (2 : ℕ) ^ M = K * B := by rw [hKdef, hBdef, ← pow_add]; congr 1; omega
  set c := i / B with hcdef
  set t := i % B with htdef
  have ht : t < B := Nat.mod_lt _ hB
  set γ := blockRoot ψ L c with hγdef
  have hγ : γ ^ K = -1 := blockRoot_pow ψ L hψ c
  -- the left side as a weighted double sum over pairs
  have hlhs : nttSpec ψ L M (negaMul (2 ^ M) a b) i
      = ∑ i' ∈ range (K * B), ∑ j ∈ range (K * B), a i' * b j *
          (if (i' + j) % B = t then γ ^ ((i' + j) / B) else 0) := by
    rw [nttSpec_eq_blockRoot]
    simp only [negaMul, hN, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' hi' => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hm : i' + j < 2 * (K * B) := by
      have := Finset.mem_range.mp hi'; have := Finset.mem_range.mp hj; omega
    rw [← sum_pow_weight γ K B t (i' + j) hB ht hγ hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show t + s * B + K * B = t + s * B + K * B from rfl]
    ring
  -- the right side as the same weighted double sum
  have hblk : ∀ (f : ℕ → R) (u : ℕ), u < B →
      nttSpec ψ L M f (c * B + u) = ∑ s ∈ range K, f (u + s * B) * γ ^ s := by
    intro f u hu
    rw [nttSpec_eq_blockRoot]
    have hmod : (c * B + u) % B = u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    have hdiv : (c * B + u) / B = c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hu, Nat.zero_add]
    rw [hmod, hdiv]
  rw [hlhs, blockMul, sum_range_mul_blocks B _ K, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hblk a u (Finset.mem_range.mp hu)]
  have hinner : ∀ s, ∑ j ∈ range (K * B), a (u + s * B) * b j *
      (if (u + s * B + j) % B = t then γ ^ ((u + s * B + j) / B) else 0)
      = ∑ v ∈ range B, ∑ s' ∈ range K, a (u + s * B) * b (v + s' * B) *
          (if (u + s * B + (v + s' * B)) % B = t
            then γ ^ ((u + s * B + (v + s' * B)) / B) else 0) := fun s => by
    rw [sum_range_mul_blocks B _ K, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun s _ => hinner s)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hblk b v (Finset.mem_range.mp hv), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← htdef, ← hcdef, ← hγdef,
    ← block_weight γ B t u v s' s hB ht (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)]
  ring

/-- With blocks of length one, the block product is the pointwise product. -/
theorem blockMul_one (γ : ℕ → R) (a b : ℕ → R) (i : ℕ) :
    blockMul 1 γ a b i = a i * b i := by
  simp [blockMul, Nat.mod_one]

/-- On the first `K · B` lanes, `blockMul` reads its operands below `K · B` only. -/
theorem blockMul_congr (B K : ℕ) (hB : 0 < B) (γ : ℕ → R) (a a' b b' : ℕ → R)
    (ha : ∀ j, j < K * B → a j = a' j) (hb : ∀ j, j < K * B → b j = b' j) (i : ℕ)
    (hi : i < K * B) : blockMul B γ a b i = blockMul B γ a' b' i := by
  have hc : i / B < K := by rw [Nat.div_lt_iff_lt_mul hB]; exact hi
  have hle : (i / B + 1) * B ≤ K * B := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul, one_mul] at hle
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
  have hu' := Finset.mem_range.mp hu
  have hv' := Finset.mem_range.mp hv
  rw [ha _ (by omega), hb _ (by omega)]

/-- A coefficient vector on `Fin N` as a lane function, zero past `N - 1`. -/
def finLanes {N : ℕ} (x : Fin N → R) (k : ℕ) : R := if h : k < N then x ⟨k, h⟩ else 0

/-- `negaMul` is the signed negacyclic convolution `signedNegaConv` on `Fin N`. -/
theorem negaMul_eq_signedNegaConv {N : ℕ} [NeZero N] (x y : Fin N → R) (k : Fin N) :
    negaMul N (finLanes x) (finLanes y) k
      = CatCrypt.Crypto.Optimizer.Lattice.SignedNegacyclicConv.signedNegaConv x y k := by
  rw [negaMul, CatCrypt.Crypto.Optimizer.Lattice.SignedNegacyclicConv.signedNegaConv,
    Finset.sum_range (fun i => ∑ j ∈ range N, finLanes x i * finLanes y j *
      (if i + j = k.val then 1 else if i + j = k.val + N then -1 else 0))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hk := k.isLt
  have hi := i.isLt
  by_cases hle : i.val ≤ k.val
  · rw [if_pos hle, Finset.sum_eq_single (k.val - i.val)]
    · have hsub : ((k - i : Fin N) : ℕ) = k.val - i.val := Fin.coe_sub_iff_le.mpr hle
      rw [if_pos (by omega), finLanes, finLanes, dif_pos hi, dif_pos (by omega), mul_one]
      congr 2
      exact Fin.ext hsub.symm
    · intro j hjN hj
      have hjN' := Finset.mem_range.mp hjN
      generalize k.val = kv at *
      generalize i.val = iv at *
      rw [if_neg (by omega), if_neg (by omega), mul_zero]
    · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
  · have hlt' : k.val < i.val := by omega
    rw [if_neg hle, Finset.sum_eq_single (k.val + N - i.val)]
    · have hsub : ((k - i : Fin N) : ℕ) = N + k.val - i.val := Fin.coe_sub_iff_lt.mpr hlt'
      rw [if_neg (by omega), if_pos (by omega), finLanes, finLanes, dif_pos hi,
        dif_pos (by omega), mul_neg, mul_one]
      congr 3
      exact Fin.ext (by simp only [hsub]; omega)
    · intro j hjN hj
      have hjN' := Finset.mem_range.mp hjN
      generalize k.val = kv at *
      generalize i.val = iv at *
      rw [if_neg (by omega), if_neg (by omega), mul_zero]
    · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
