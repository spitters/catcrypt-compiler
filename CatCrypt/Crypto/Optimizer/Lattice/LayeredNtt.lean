/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

/-!
# The layered radix-2 NTT of `ntt.rs`, proved equal to the DFT

`Plonky3ProveEmit.bbNtt` models Plonky3's `ntt.rs::ntt`: bit-reverse the input,
then run `log n` Cooley–Tukey layers in place. Layer `m` works on blocks of size
`2^(m+1)` with half-block `h = 2^m` and twiddle base `wSize = ω^(n / 2^(m+1))`;
inside a block at offset `j < h` it writes `x[j] + wSize^j·x[j+h]` to position `j`
and `x[j] − wSize^j·x[j+h]` to position `j + h`.

This module states that transform over an arbitrary commutative ring, on
`ℕ`-indexed data (`ctLayer`, `layers`), and proves it computes the DFT
`NTTRecursionPass.dft` (`Σ_j x_j ω^{jk}`, evaluation at the powers of `ω`) on the
bit-reversed input.

## Main results

* `ctLayer` — one Cooley–Tukey layer with half-block `h` and twiddle base `w`.
* `layers e ω m` — the first `m` layers of the length-`2^e` transform with root `ω`.
* `nttIterN` — the recursive form of the same transform on contiguous halves, with
  the upper output `L − ωᵏ·U`.
* `layers_eq_nttIterN` — the layered and recursive forms agree below `2^e`, with
  no hypothesis on `ω`.
* `nttIterN_eq_nttIter` — under `ω^(2^(e-1)) = −1` the recursive form is
  `IterativeNttEqRec.nttIter`.
* `layers_bitrev_eq_dft` — for `ω^(2^e) = −1`, the `e + 1` layers applied to the
  bit-reversed input compute `dft (2^(e+1)) ω`.
* `layers_bitrev_eq_dft_of_isPrimitiveRoot` — the same for a primitive
  `2^(e+1)`-th root of unity in a domain.
* `bupd`, `layerPairs`, `nttPairs` — one in-place butterfly on a triple
  `(lo, hi, twiddle exponent)`, and the butterflies of one layer and of the first
  `m` layers in the loop order of `ntt.rs`.
* `foldl_layerPairs`, `foldl_nttPairs` — the butterflies of a layer compute
  `ctLayer`, and those of the first `m` layers compute `layers`, below `2^e`.
* `foldl_nttPairs_bitrev_eq_dft` — the butterfly sequence of all layers on the
  bit-reversed input computes the DFT.

## Bit-reversal convention

The input of the layers at position `i` is `x (bitrev (e+1) i)`, the value at the
index whose low `e + 1` bits are those of `i` reversed (`BitReversalGeneric.bitrev`),
which is `ntt.rs::bit_reverse_permute`. The output is in natural order: position
`k` holds `Σ_j x_j ω^{jk}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt

open CatCrypt.Crypto.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Lattice.BitReversalGeneric
open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

variable {R : Type*} [CommRing R]

/-! ## 1. The layered transform -/

/-- One radix-2 Cooley–Tukey layer with half-block `h` and twiddle base `w`, on
`ℕ`-indexed data. Position `idx` lies in the block starting at
`b = ⌊idx / 2h⌋·2h` at offset `o = idx mod 2h`; for `o < h` it receives
`x (b+o) + w^o · x (b+o+h)`, otherwise `x (b+o−h) − w^(o−h) · x (b+o)`. -/
def ctLayer (h : ℕ) (w : R) (x : ℕ → R) (idx : ℕ) : R :=
  if idx % (2 * h) < h then
    x (idx / (2 * h) * (2 * h) + idx % (2 * h))
      + w ^ (idx % (2 * h)) * x (idx / (2 * h) * (2 * h) + idx % (2 * h) + h)
  else
    x (idx / (2 * h) * (2 * h) + (idx % (2 * h) - h))
      - w ^ (idx % (2 * h) - h) * x (idx / (2 * h) * (2 * h) + idx % (2 * h))

/-- The first `m` layers of the length-`2^e` transform with root `ω`: layer `m`
has half-block `2^m` and twiddle base `ω^(2^e / 2^(m+1))`. -/
def layers (e : ℕ) (ω : R) : ℕ → (ℕ → R) → (ℕ → R)
  | 0, x => x
  | m + 1, x => ctLayer (2 ^ m) (ω ^ (2 ^ e / 2 ^ (m + 1))) (layers e ω m x)

/-- The recursive radix-2 transform on contiguous halves, with upper output
`L − ωᵏ·U`: the lower half is transformed at `ω²`, the upper half (shifted by
`2^e`) likewise, and the two are merged by one butterfly. -/
def nttIterN : ℕ → R → (ℕ → R) → (ℕ → R)
  | 0, _, x => x
  | e + 1, ω, x => fun k =>
    if k < 2 ^ e then
      nttIterN e (ω ^ 2) x k + ω ^ k * nttIterN e (ω ^ 2) (fun j => x (j + 2 ^ e)) k
    else
      nttIterN e (ω ^ 2) x (k - 2 ^ e)
        - ω ^ (k - 2 ^ e) * nttIterN e (ω ^ 2) (fun j => x (j + 2 ^ e)) (k - 2 ^ e)

/-! ## 2. Locality of one layer -/

/-- Shifting by a multiple of the block size commutes with a layer. -/
theorem ctLayer_shift (h N : ℕ) (w : R) (x : ℕ → R) (hN : 2 * h ∣ N) (i : ℕ) :
    ctLayer h w x (i + N) = ctLayer h w (fun j => x (j + N)) i := by
  obtain ⟨c, rfl⟩ := hN
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0; simp [ctLayer]
  have h2 : 0 < 2 * h := by omega
  have hmod : (i + 2 * h * c) % (2 * h) = i % (2 * h) := by
    rw [Nat.add_mul_mod_self_left]
  have hdiv : (i + 2 * h * c) / (2 * h) * (2 * h)
      = i / (2 * h) * (2 * h) + 2 * h * c := by
    rw [Nat.add_mul_div_left _ _ h2, Nat.add_mul]; ring
  simp only [ctLayer, hmod, hdiv]
  split_ifs <;> ring_nf

/-- On a prefix `[0, N)` that is a union of blocks, a layer reads only that prefix. -/
theorem ctLayer_congr_lt (h N : ℕ) (w : R) (x y : ℕ → R) (hpos : 0 < h)
    (hN : 2 * h ∣ N) (hxy : ∀ j, j < N → x j = y j) (i : ℕ) (hi : i < N) :
    ctLayer h w x i = ctLayer h w y i := by
  have h2 : 0 < 2 * h := by omega
  have hb : i / (2 * h) * (2 * h) + 2 * h ≤ N := by
    obtain ⟨c, rfl⟩ := hN
    have : i / (2 * h) < c := by
      rw [Nat.div_lt_iff_lt_mul h2]; linarith
    nlinarith
  have hm := Nat.mod_lt i h2
  unfold ctLayer
  split_ifs with ho
  · rw [hxy _ (by omega), hxy _ (by omega)]
  · rw [hxy _ (by omega), hxy _ (by omega)]

/-! ## 3. Layered = recursive -/

/-- The twiddle base of layer `m` at length `2^(e+1)` and root `ω` is that of layer
`m` at length `2^e` and root `ω²`, for `m < e`. -/
theorem twiddle_succ (e m : ℕ) (ω : R) (hm : m < e) :
    ω ^ (2 ^ (e + 1) / 2 ^ (m + 1)) = (ω ^ 2) ^ (2 ^ e / 2 ^ (m + 1)) := by
  rw [← pow_mul, Nat.pow_div (by omega) (by norm_num), Nat.pow_div (by omega) (by norm_num)]
  congr 1
  rw [show e + 1 - (m + 1) = (e - (m + 1)) + 1 by omega, pow_succ]; ring

/-- The first `m ≤ e` layers of the length-`2^(e+1)` transform act on the two
contiguous halves as the first `m` layers of the length-`2^e` transform at `ω²`. -/
theorem layers_split (e : ℕ) (ω : R) (x : ℕ → R) :
    ∀ m, m ≤ e →
      (∀ i, i < 2 ^ e → layers (e + 1) ω m x i = layers e (ω ^ 2) m x i) ∧
      (∀ i, layers (e + 1) ω m x (i + 2 ^ e)
        = layers e (ω ^ 2) m (fun j => x (j + 2 ^ e)) i) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | succ m ih =>
    intro hm
    obtain ⟨ihA, ihB⟩ := ih (by omega)
    have hdvd : 2 * 2 ^ m ∣ 2 ^ e := by
      rw [← pow_succ']; exact Nat.pow_dvd_pow 2 (by omega)
    have hpos : 0 < 2 ^ m := by positivity
    refine ⟨fun i hi => ?_, fun i => ?_⟩
    · simp only [layers]
      rw [twiddle_succ e m ω (by omega)]
      exact ctLayer_congr_lt _ _ _ _ _ hpos hdvd ihA i hi
    · simp only [layers]
      rw [twiddle_succ e m ω (by omega), ctLayer_shift _ _ _ _ hdvd]
      congr 1
      funext j
      exact ihB j

/-- **Layered = recursive.** Below `2^e`, the `e` layers of the length-`2^e`
transform agree with `nttIterN`, for every `ω`. -/
theorem layers_eq_nttIterN :
    ∀ (e : ℕ) (ω : R) (x : ℕ → R) (k : ℕ), k < 2 ^ e →
      layers e ω e x k = nttIterN e ω x k := by
  intro e
  induction e with
  | zero => intro _ _ _ _; rfl
  | succ e ih =>
    intro ω x k hk
    obtain ⟨hA, hB⟩ := layers_split e ω x e le_rfl
    have htw : ω ^ (2 ^ (e + 1) / 2 ^ (e + 1)) = ω := by
      rw [Nat.div_self (by positivity), pow_one]
    have hk' : k < 2 * 2 ^ e := by rw [← pow_succ']; exact hk
    have hdiv : k / (2 * 2 ^ e) = 0 := Nat.div_eq_of_lt hk'
    have hmod : k % (2 * 2 ^ e) = k := Nat.mod_eq_of_lt hk'
    simp only [layers, htw, ctLayer, hdiv, hmod, zero_mul, zero_add, nttIterN]
    split_ifs with hlt
    · rw [hA k hlt, hB k, ih _ _ _ hlt, ih _ _ _ hlt]
    · have hk2 : k - 2 ^ e < 2 ^ e := by omega
      have hkk : k = (k - 2 ^ e) + 2 ^ e := by omega
      rw [hA _ hk2, ih _ _ _ hk2]
      conv_lhs => rw [hkk, hB (k - 2 ^ e)]
      rw [ih _ _ _ hk2, Nat.add_sub_cancel]

/-! ## 4. Recursive = `nttIter` -/

/-- Under `ω^(2^(e-1)) = −1` (for `e ≥ 1`), `nttIterN` on `ℕ`-indexed data agreeing
with `y` below `2^e` is `IterativeNttEqRec.nttIter e ω y`. -/
theorem nttIterN_eq_nttIter :
    ∀ (e : ℕ) (ω : R), (e = 0 ∨ ω ^ (2 ^ (e - 1)) = -1) →
      ∀ (x : ℕ → R) (y : Fin (2 ^ e) → R), (∀ i (hi : i < 2 ^ e), x i = y ⟨i, hi⟩) →
      ∀ (k : ℕ) (hk : k < 2 ^ e), nttIterN e ω x k = nttIter e ω y ⟨k, hk⟩ := by
  intro e
  induction e with
  | zero =>
    intro ω _ x y hxy k hk
    exact hxy k hk
  | succ e ih =>
    intro ω hω x y hxy k hk
    have hω' : ω ^ (2 ^ e) = -1 := by
      rcases hω with h | h
      · omega
      · simpa using h
    have hω2 : e = 0 ∨ (ω ^ 2) ^ (2 ^ (e - 1)) = -1 := by
      rcases Nat.eq_zero_or_pos e with h0 | hpos
      · exact Or.inl h0
      · right
        rw [← pow_mul, ← hω']
        congr 1
        rw [← pow_succ']; congr 1; omega
    have hlow : ∀ i (hi : i < 2 ^ e), x i = lowerHalf e y ⟨i, hi⟩ := by
      intro i hi; simp only [lowerHalf]; exact hxy i _
    have hup : ∀ i (hi : i < 2 ^ e), x (i + 2 ^ e) = upperHalf e y ⟨i, hi⟩ := by
      intro i hi; simp only [upperHalf]; exact hxy _ _
    simp only [nttIterN, nttIter]
    split_ifs with hlt
    · rw [ih _ hω2 _ _ hlow k hlt, ih _ hω2 _ _ hup k hlt]
    · rw [ih _ hω2 _ _ hlow (k - 2 ^ e) (by omega), ih _ hω2 _ _ hup (k - 2 ^ e) (by omega),
        hω']
      ring

/-! ## 5. The layered transform computes the DFT -/

/-- The bit-reversed input of the length-`2^e` transform as `ℕ`-indexed data
(`0` outside `[0, 2^e)`): position `i` holds `x (bitrev e i)`. -/
def bitrevInput (e : ℕ) (x : Fin (2 ^ e) → R) (i : ℕ) : R :=
  if hi : i < 2 ^ e then x ((bitrevPerm e) ⟨i, hi⟩) else 0

/-- **The layered NTT computes the DFT.** For `ω` with `ω^(2^e) = −1`, running the
`e + 1` Cooley–Tukey layers of `ntt.rs` on the bit-reversed input yields, at every
`k < 2^(e+1)`, the DFT `Σ_j x_j ω^{jk}`. -/
theorem layers_bitrev_eq_dft (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1)
    (x : Fin (2 ^ (e + 1)) → R) (k : Fin (2 ^ (e + 1))) :
    layers (e + 1) ω (e + 1) (bitrevInput (e + 1) x) k.val = dft (2 ^ (e + 1)) ω x k := by
  have hone : ω ^ (2 ^ (e + 1)) = 1 := by
    rw [pow_succ, pow_mul, hω]; norm_num
  rw [layers_eq_nttIterN _ _ _ _ k.isLt,
    nttIterN_eq_nttIter (e + 1) ω (Or.inr (by simpa using hω)) _
      (fun j => x ((bitrevPerm (e + 1)) j)) (fun i hi => by simp [bitrevInput, hi]) k.val k.isLt]
  exact nttIter_comp_bitrev_eq_dft (e + 1) ω hone x k

/-- `layers_bitrev_eq_dft` for a primitive `2^(e+1)`-th root of unity in a domain. -/
theorem layers_bitrev_eq_dft_of_isPrimitiveRoot [IsDomain R] (e : ℕ) (ω : R)
    (hω : IsPrimitiveRoot ω (2 ^ (e + 1)))
    (x : Fin (2 ^ (e + 1)) → R) (k : Fin (2 ^ (e + 1))) :
    layers (e + 1) ω (e + 1) (bitrevInput (e + 1) x) k.val = dft (2 ^ (e + 1)) ω x k := by
  refine layers_bitrev_eq_dft e ω ?_ x k
  have h2 : IsPrimitiveRoot (ω ^ (2 ^ e)) 2 := by
    have := hω.pow_of_dvd (p := 2 ^ e) (by positivity) (Nat.pow_dvd_pow 2 (by omega))
    rwa [Nat.pow_div (by omega) (by norm_num), show e + 1 - e = 1 by omega, pow_one] at this
  exact h2.eq_neg_one_of_two_right

/-! ## 6. The layers as sequences of in-place butterflies -/

/-- One in-place butterfly on the triple `(lo, hi, t)`: positions `lo` and `hi`
receive `Y lo + Tw t · Y hi` and `Y lo − Tw t · Y hi`; every other position is
kept. -/
def bupd (Tw : ℕ → R) (Y : ℕ → R) (q : ℕ × ℕ × ℕ) : ℕ → R := fun i =>
  if i = q.1 then Y q.1 + Tw q.2.2 * Y q.2.1
  else if i = q.2.1 then Y q.1 - Tw q.2.2 * Y q.2.1
  else Y i

/-- The butterflies of layer `m` of the length-`2^e` transform, in the loop order of
`ntt.rs` (block `b` outer, offset `j` inner): `(b·2^(m+1) + j, b·2^(m+1) + j + 2^m,
j · 2^e / 2^(m+1))`, the last entry the exponent of `ω` in the twiddle. -/
def layerPairs (e m : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (2 ^ e / 2 ^ (m + 1)) ×ˢ List.range (2 ^ m)).map
    (fun bj => (bj.1 * 2 ^ (m + 1) + bj.2, bj.1 * 2 ^ (m + 1) + bj.2 + 2 ^ m,
      bj.2 * (2 ^ e / 2 ^ (m + 1))))

/-- The butterflies of the first `m` layers of the length-`2^e` transform. -/
def nttPairs (e : ℕ) : ℕ → List (ℕ × ℕ × ℕ)
  | 0 => []
  | m + 1 => nttPairs e m ++ layerPairs e m

/-- Two butterflies touch disjoint positions. -/
def Disj (p q : ℕ × ℕ × ℕ) : Prop :=
  p.1 ≠ q.1 ∧ p.1 ≠ q.2.1 ∧ p.2.1 ≠ q.1 ∧ p.2.1 ≠ q.2.1

theorem foldl_bupd_off (Tw : ℕ → R) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (Y : ℕ → R) (i : ℕ), (∀ q ∈ l, i ≠ q.1 ∧ i ≠ q.2.1) →
      l.foldl (bupd Tw) Y i = Y i := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons q l ih =>
    intro Y i h
    obtain ⟨h1, h2⟩ := h q (List.mem_cons_self ..)
    rw [List.foldl_cons, ih _ i (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
    simp [bupd, h1, h2]

theorem foldl_bupd_mem (Tw : ℕ → R) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (Y : ℕ → R), l.Pairwise Disj → (∀ q ∈ l, q.1 ≠ q.2.1) →
      ∀ q ∈ l, l.foldl (bupd Tw) Y q.1 = Y q.1 + Tw q.2.2 * Y q.2.1
        ∧ l.foldl (bupd Tw) Y q.2.1 = Y q.1 - Tw q.2.2 * Y q.2.1 := by
  intro l
  induction l with
  | nil => intro _ _ _ q hq; simp at hq
  | cons p l ih =>
    intro Y hpw hne q hq
    rw [List.pairwise_cons] at hpw
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl | hq
    · have hoff : ∀ i, (i = q.1 ∨ i = q.2.1) → ∀ q' ∈ l, i ≠ q'.1 ∧ i ≠ q'.2.1 := by
        intro i hi q' hq'
        obtain ⟨d1, d2, d3, d4⟩ := hpw.1 q' hq'
        rcases hi with rfl | rfl
        · exact ⟨d1, d2⟩
        · exact ⟨d3, d4⟩
      have hq12 := hne q (List.mem_cons_self ..)
      rw [foldl_bupd_off Tw l _ _ (hoff _ (Or.inl rfl)),
        foldl_bupd_off Tw l _ _ (hoff _ (Or.inr rfl))]
      simp [bupd, Ne.symm hq12]
    · obtain ⟨d1, d2, d3, d4⟩ := hpw.1 q hq
      rw [(ih _ hpw.2 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) q hq).1,
        (ih _ hpw.2 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) q hq).2]
      simp [bupd, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4]

theorem mem_layerPairs {e m : ℕ} {q : ℕ × ℕ × ℕ} :
    q ∈ layerPairs e m ↔ ∃ b j, b < 2 ^ e / 2 ^ (m + 1) ∧ j < 2 ^ m ∧
      q = (b * 2 ^ (m + 1) + j, b * 2 ^ (m + 1) + j + 2 ^ m, j * (2 ^ e / 2 ^ (m + 1))) := by
  simp only [layerPairs, List.mem_map, List.mem_product, List.mem_range, Prod.exists]
  constructor
  · rintro ⟨b, j, ⟨hb, hj⟩, rfl⟩; exact ⟨b, j, hb, hj, rfl⟩
  · rintro ⟨b, j, hb, hj, rfl⟩; exact ⟨b, j, ⟨hb, hj⟩, rfl⟩

/-- Position `b·2^(m+1) + j + s·2^m` (`j < 2^m`, `s ≤ 1`) determines `b`, `j`, `s`. -/
theorem pos_inj {m b j s b' j' s' : ℕ} (hj : j < 2 ^ m) (hj' : j' < 2 ^ m)
    (hs : s ≤ 1) (hs' : s' ≤ 1)
    (h : b * 2 ^ (m + 1) + j + s * 2 ^ m = b' * 2 ^ (m + 1) + j' + s' * 2 ^ m) :
    b = b' ∧ j = j' ∧ s = s' := by
  have hS : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  have hr : j + s * 2 ^ m < 2 ^ (m + 1) := by
    rw [hS]; interval_cases s <;> omega
  have hr' : j' + s' * 2 ^ m < 2 ^ (m + 1) := by
    rw [hS]; interval_cases s' <;> omega
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have e1 : (b * 2 ^ (m + 1) + (j + s * 2 ^ m)) / 2 ^ (m + 1) = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, zero_add]
  have e2 : (b' * 2 ^ (m + 1) + (j' + s' * 2 ^ m)) / 2 ^ (m + 1) = b' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr', zero_add]
  have hb : b = b' := by
    rw [← e1, ← e2]; congr 1; omega
  subst hb
  have hjs : j + s * 2 ^ m = j' + s' * 2 ^ m := by omega
  have hm : 0 < 2 ^ m := by positivity
  interval_cases s <;> interval_cases s' <;> omega

theorem layerPairs_pairwise (e m : ℕ) : (layerPairs e m).Pairwise Disj := by
  unfold layerPairs
  rw [List.pairwise_map]
  refine List.Nodup.pairwise_of_forall_ne
    (List.Nodup.product List.nodup_range List.nodup_range) ?_
  rintro ⟨b, j⟩ hbj ⟨b', j'⟩ hbj' hne
  simp only [List.mem_product, List.mem_range] at hbj hbj'
  have key : ∀ s s', s ≤ 1 → s' ≤ 1 →
      b * 2 ^ (m + 1) + j + s * 2 ^ m ≠ b' * 2 ^ (m + 1) + j' + s' * 2 ^ m := by
    intro s s' hs hs' h
    obtain ⟨rfl, rfl, -⟩ := pos_inj hbj.2 hbj'.2 hs hs' h
    exact hne rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using key 0 0 (by omega) (by omega)
  · simpa using key 0 1 (by omega) (by omega)
  · simpa using key 1 0 (by omega) (by omega)
  · simpa using key 1 1 (by omega) (by omega)

theorem layerPairs_ne (e m : ℕ) : ∀ q ∈ layerPairs e m, q.1 ≠ q.2.1 := by
  intro q hq
  obtain ⟨b, j, -, -, rfl⟩ := mem_layerPairs.mp hq
  have : 0 < 2 ^ m := by positivity
  simp only; omega

/-- **One layer as butterflies.** Below `2^e`, the in-place butterflies of layer
`m < e` with twiddle table `Tw k = ω^k` compute `ctLayer` with half-block `2^m` and
twiddle base `ω^(2^e / 2^(m+1))`. -/
theorem foldl_layerPairs (e m : ℕ) (hm : m < e) (ω : R) (Tw : ℕ → R)
    (hTw : ∀ k, Tw k = ω ^ k) (Y : ℕ → R) (i : ℕ) (hi : i < 2 ^ e) :
    (layerPairs e m).foldl (bupd Tw) Y i = ctLayer (2 ^ m) (ω ^ (2 ^ e / 2 ^ (m + 1))) Y i := by
  have hS : 2 * 2 ^ m = 2 ^ (m + 1) := by rw [pow_succ']
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hdvd : 2 ^ (m + 1) ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
  have hb : i / 2 ^ (m + 1) < 2 ^ e / 2 ^ (m + 1) :=
    Nat.div_lt_div_of_lt_of_dvd hdvd hi
  have hdecomp : i / 2 ^ (m + 1) * 2 ^ (m + 1) + i % 2 ^ (m + 1) = i := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod i _
  have hmod := Nat.mod_lt i hpos
  unfold ctLayer
  rw [hS]
  split_ifs with ho
  · have hq : (i / 2 ^ (m + 1) * 2 ^ (m + 1) + i % 2 ^ (m + 1),
        i / 2 ^ (m + 1) * 2 ^ (m + 1) + i % 2 ^ (m + 1) + 2 ^ m,
        i % 2 ^ (m + 1) * (2 ^ e / 2 ^ (m + 1))) ∈ layerPairs e m :=
      mem_layerPairs.mpr ⟨_, _, hb, ho, rfl⟩
    have h := (foldl_bupd_mem Tw _ Y (layerPairs_pairwise e m) (layerPairs_ne e m) _ hq).1
    simp only at h
    rw [hdecomp] at h ⊢
    rw [h, hTw, ← pow_mul, Nat.mul_comm (i % 2 ^ (m + 1))]
  · have hq : (i / 2 ^ (m + 1) * 2 ^ (m + 1) + (i % 2 ^ (m + 1) - 2 ^ m),
        i / 2 ^ (m + 1) * 2 ^ (m + 1) + (i % 2 ^ (m + 1) - 2 ^ m) + 2 ^ m,
        (i % 2 ^ (m + 1) - 2 ^ m) * (2 ^ e / 2 ^ (m + 1))) ∈ layerPairs e m :=
      mem_layerPairs.mpr ⟨_, i % 2 ^ (m + 1) - 2 ^ m, hb, by omega, rfl⟩
    have h := (foldl_bupd_mem Tw _ Y (layerPairs_pairwise e m) (layerPairs_ne e m) _ hq).2
    simp only at h
    have he : i / 2 ^ (m + 1) * 2 ^ (m + 1) + (i % 2 ^ (m + 1) - 2 ^ m) + 2 ^ m = i := by
      omega
    rw [he] at h
    rw [hdecomp, h, hTw, ← pow_mul, Nat.mul_comm (i % 2 ^ (m + 1) - 2 ^ m)]

/-- Every butterfly of the first `m ≤ e` layers stays below `2^e`, has distinct
positions, and reads a twiddle exponent below `2^e / 2`. -/
theorem mem_nttPairs_bounds {e : ℕ} : ∀ {m : ℕ} {q : ℕ × ℕ × ℕ}, m ≤ e → q ∈ nttPairs e m →
    q.1 < 2 ^ e ∧ q.2.1 < 2 ^ e ∧ q.1 ≠ q.2.1 ∧ q.2.2 < 2 ^ e / 2 := by
  intro m
  induction m with
  | zero => intro q _ hq; simp [nttPairs] at hq
  | succ m ih =>
    intro q hm hq
    rw [nttPairs, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ih (by omega) hq
    · obtain ⟨b, j, hb, hj, rfl⟩ := mem_layerPairs.mp hq
      have hS : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
      have hdvd : 2 ^ (m + 1) ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨c, hc⟩ := hdvd
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h] at hc; simp at hc
        · exact h
      have hdiv : 2 ^ e / 2 ^ (m + 1) = c := by
        rw [hc, Nat.mul_div_cancel_left _ (by positivity)]
      rw [hdiv] at hb ⊢
      have hhalf : 2 ^ e / 2 = 2 ^ m * c := by
        rw [hc, hS, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
      have hpm : 0 < 2 ^ m := by positivity
      have h1 : (b + 1) * 2 ^ (m + 1) ≤ 2 ^ e := by
        rw [hc, Nat.mul_comm (2 ^ (m + 1))]; exact Nat.mul_le_mul_right _ hb
      refine ⟨?_, ?_, by simp only; omega, ?_⟩
      · simp only; rw [Nat.add_mul] at h1; rw [hS] at h1 ⊢; omega
      · simp only; rw [Nat.add_mul] at h1; rw [hS] at h1 ⊢; omega
      · simp only; rw [hhalf]; exact Nat.mul_lt_mul_of_pos_right hj hcpos

/-- **The butterflies of the first `m ≤ e` layers compute those layers** below `2^e`,
with twiddle table `Tw k = ω^k`. -/
theorem foldl_nttPairs (e : ℕ) (ω : R) (Tw : ℕ → R) (hTw : ∀ k, Tw k = ω ^ k)
    (Y : ℕ → R) : ∀ m, m ≤ e → ∀ i, i < 2 ^ e →
      (nttPairs e m).foldl (bupd Tw) Y i = layers e ω m Y i := by
  intro m
  induction m with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro hm i hi
    rw [nttPairs, List.foldl_append, foldl_layerPairs e m (by omega) ω Tw hTw _ i hi, layers]
    have hdvd : 2 * 2 ^ m ∣ 2 ^ e := by
      rw [← pow_succ']; exact Nat.pow_dvd_pow 2 (by omega)
    exact ctLayer_congr_lt _ _ _ _ _ (by positivity) hdvd (ih (by omega)) i hi

/-- The butterflies read the twiddle table only at their own twiddle exponents. -/
theorem foldl_bupd_congr_tw {Tw Tw' : ℕ → R} :
    ∀ (l : List (ℕ × ℕ × ℕ)) (Y : ℕ → R), (∀ q ∈ l, Tw q.2.2 = Tw' q.2.2) →
      l.foldl (bupd Tw) Y = l.foldl (bupd Tw') Y := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons q l ih =>
    intro Y h
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
    congr 1
    funext i
    simp [bupd, h q (List.mem_cons_self ..)]

/-- The layers read their input only below `2^e`. -/
theorem layers_congr (e : ℕ) (ω : R) (Y Y' : ℕ → R) (h : ∀ i, i < 2 ^ e → Y i = Y' i) :
    ∀ m, m ≤ e → ∀ i, i < 2 ^ e → layers e ω m Y i = layers e ω m Y' i := by
  intro m
  induction m with
  | zero => exact fun _ => h
  | succ m ih =>
    intro hm i hi
    have hdvd : 2 * 2 ^ m ∣ 2 ^ e := by
      rw [← pow_succ']; exact Nat.pow_dvd_pow 2 (by omega)
    exact ctLayer_congr_lt _ _ _ _ _ (by positivity) hdvd (ih (by omega)) i hi

/-- **The butterfly sequence of `ntt.rs` computes the DFT.** For `ω^(2^e) = −1` and
twiddle table `Tw k = ω^k`, the in-place butterflies of all `e + 1` layers, run on
the bit-reversed input, leave `Σ_j x_j ω^{jk}` at every position `k < 2^(e+1)`. -/
theorem foldl_nttPairs_bitrev_eq_dft (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1)
    (Tw : ℕ → R) (hTw : ∀ k, Tw k = ω ^ k)
    (x : Fin (2 ^ (e + 1)) → R) (k : Fin (2 ^ (e + 1))) :
    (nttPairs (e + 1) (e + 1)).foldl (bupd Tw) (bitrevInput (e + 1) x) k.val
      = dft (2 ^ (e + 1)) ω x k := by
  rw [foldl_nttPairs (e + 1) ω Tw hTw _ (e + 1) le_rfl _ k.isLt]
  exact layers_bitrev_eq_dft e ω hω x k

end CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt
