/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral
public import CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric
public import CatCrypt.Crypto.Number.MontgomeryReduction

/-!
# The negacyclic merged-twiddle NTT as one `fieldDialect` template

The forward transforms of FIPS 203 (Algorithm 9) and FIPS 204 (Algorithm 41) are
one loop: on `N = 2 ^ M` coefficients in natural order, layer `ℓ` (for `ℓ < L`)
splits each of the `2 ^ ℓ` blocks of length `2 ^ (M - ℓ)` by the butterfly
`(x, y) ↦ (x + z·y, x − z·y)` at half-length `2 ^ (M - 1 - ℓ)`, with the twiddle
of block `c` equal to `ψ ^ BitRev_L (2 ^ ℓ + c)`.  When `ψ ^ (2 ^ L) = -1`, after
`L` layers block `c` holds the input reduced modulo
`X ^ (2 ^ (M - L)) - ψ ^ (2 · BitRev_L c + 1)`.  ML-DSA is `M = L = 8`,
`ψ = 1753` (every block a single evaluation); ML-KEM is `M = 8`, `L = 7`,
`ψ = 17` (every block a degree-one residue).

This file states that loop once, generic in the modulus `q`, the length exponent
`M`, the layer count `L` and the root `ψ`, as a `MultiReturnCom fieldDialect`
program on `N` lanes, and proves once that the program computes the reductions.

## Main definitions

* `zt`, `rho` — the twiddle of a block index, and the root of the modulus block
  `c` is reduced by after `ℓ` layers.
* `layerSum` — the reduction of an input modulo `X ^ B - r` at offset `t`, as a
  sum over the coefficients spaced `B` apart.
* `layerFn`, `run` — one layer on lane functions `ℕ → R`, and `k` layers from
  layer `ℓ`.
* `nttSpec` — lane `i` of the transform: offset `i % 2 ^ (M - L)` of the
  reduction modulo `X ^ (2 ^ (M - L)) - ψ ^ (2 · BitRev_L (i / 2 ^ (M - L)) + 1)`.
* `layerLaneProg` — the schedule of output lane `i` of layer `ℓ`.
* `chain` — `k` layers from layer `ℓ`, each emitted by `Com.foldVarN` over the
  result variables of the previous one.
* `NttParams`, `NttParams.Ok`, `nttProg` — the parameter record, its decidable
  side condition on `ℕ`, and the transform program.
* `mlkemNtt`, `mldsaNtt` — the FIPS 203 and FIPS 204 parameter records.
* `LazySched`, `SchedOk` — a lazy Montgomery schedule (radix, Montgomery
  constant, subtraction offset, reduced layers, word width) and its decidable
  side condition on `ℕ`.
* `zr`, `tmul`, `lazyLayer`, `lazyRun` — the twiddle in Montgomery form, the
  Montgomery-reduced twiddle product, and the layers on unsigned representatives.
* `bnd` — the lane bound after `ℓ` layers, a function of the schedule.
* `mlkemLazy`, `mldsaLazy` — radix `2 ^ 16` and `2 ^ 32`, offset `2 q`, no
  reduced layer.

## Main results

* `bitrev_two_mul`, `bitrev_two_mul_succ`, `bitrev_pow_add`, `bitrev_one` — the
  bit-reversal identities the layer recursion uses, at every width.
* `rho_sq`, `rho_last` — the layer twiddle squares to the block root it splits,
  and after `L` layers the root of block `i` is `ψ ^ (2 · BitRev_L i + 1)`.
* `layerInv_step`, `run_spec` — one layer advances the block invariant, and `L`
  layers compute `nttSpec`.
* `chain_denote` — `chain` denotes the lane functions of `run`.
* `nttProg_denote` — for every parameter record satisfying `NttParams.Ok`, lane
  `i` of `nttProg` is `nttSpec` at `i`.
* `mlkemNtt_ok`, `mldsaNtt_ok` — the side conditions of the two instances, by
  kernel `decide` on `ℕ`.
* `tmul_lt`, `tmul_cast` — the reduced twiddle product is below `2 q` and is the
  twiddle times the input in `ZMod q`.
* `lazyRun_lt` — the bound theorem: after `ℓ` layers every representative is
  below `bnd ℓ`.
* `lazyRun_cast`, `lazyRun_eq_nttProg` — the representatives cast to the lanes
  of `run`, and after all layers to the lanes of `nttProg P`.
* `butterfly_words` — the twiddle product, the Montgomery numerator and the
  pre-subtraction sum of every butterfly fit their words.
* `mlkemLazy_ok`, `mldsaLazy_ok` — the schedule side conditions, by kernel
  `decide` on `ℕ`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
  (hvToHom homToHV pullV_hvToHom lookupVars_homToHV)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn (F)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral
open CatCrypt.Crypto.Lattice.BitReversalGeneric
  (bitrev toBits fromBits toBits_fromBits fromBits_toBits toBits_length)

/-! ## 1. Bit reversal at every width -/

theorem toBits_succ_snoc (w i : ℕ) : toBits (w + 1) i = toBits w i ++ [i.testBit w] := by
  simp [toBits, List.range_succ]

theorem fromBits_append_single (xs : List Bool) (b : Bool) :
    fromBits (xs ++ [b]) = fromBits xs + (if b then 2 ^ xs.length else 0) := by
  induction xs with
  | nil => cases b <;> simp [fromBits]
  | cons x xs ih =>
    simp only [List.cons_append, fromBits, ih, List.length_cons, pow_succ]
    cases b <;> simp; ring

/-- Reversal at width `w + 1` from the top bit: the top bit becomes the low bit. -/
theorem bitrev_succ_low (w i : ℕ) :
    bitrev (w + 1) i = (if i.testBit w then 1 else 0) + 2 * bitrev w i := by
  simp [bitrev, toBits_succ_snoc, fromBits]

/-- Reversal at width `w + 1` from the low bit: the low bit becomes the top bit. -/
theorem bitrev_succ_high (w i : ℕ) :
    bitrev (w + 1) i = bitrev w (i / 2) + (if i % 2 = 1 then 2 ^ w else 0) := by
  rw [bitrev, CatCrypt.Crypto.Lattice.BitReversalGeneric.toBits_succ,
    List.reverse_cons, fromBits_append_single, List.length_reverse, toBits_length,
    Nat.testBit_zero]
  simp only [decide_eq_true_eq]
  rfl

/-- Reversal at width `w` reads only the low `w` bits. -/
theorem bitrev_mod (w i : ℕ) : bitrev w (i % 2 ^ w) = bitrev w i := by
  unfold bitrev
  rw [← fromBits_toBits]
  have h := toBits_fromBits (toBits w i)
  rw [toBits_length] at h
  rw [h]

/-- Reversing `2 * k` halves the reversal of `k`. -/
theorem bitrev_two_mul (m k : ℕ) (hk : k < 2 ^ m) :
    2 * bitrev (m + 1) (2 * k) = bitrev (m + 1) k := by
  rw [bitrev_succ_high, bitrev_succ_low, Nat.testBit_eq_false_of_lt hk]
  simp

/-- Setting the low bit of `2 * k` raises the reversal by `2 ^ m`. -/
theorem bitrev_two_mul_succ (m k : ℕ) :
    bitrev (m + 1) (2 * k + 1) = bitrev (m + 1) (2 * k) + 2 ^ m := by
  rw [bitrev_succ_high, bitrev_succ_high]
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : 2 * k / 2 = k := by omega
  simp [h1, h2]

/-- Setting the top bit raises the reversal by `1`. -/
theorem bitrev_pow_add (m k : ℕ) (hk : k < 2 ^ m) :
    bitrev (m + 1) (2 ^ m + k) = bitrev (m + 1) k + 1 := by
  rw [bitrev_succ_low, bitrev_succ_low, Nat.testBit_two_pow_add_eq,
    Nat.testBit_eq_false_of_lt hk, ← bitrev_mod m (2 ^ m + k),
    show (2 ^ m + k) % 2 ^ m = k from by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hk]]
  simp
  omega

theorem bitrev_zero (m : ℕ) : bitrev m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bitrev_succ_low, ih]; simp

/-- The reversal of `1` is the top bit. -/
theorem bitrev_one (m : ℕ) : bitrev (m + 1) 1 = 2 ^ m := by
  rw [bitrev_succ_high]
  simp [bitrev_zero]

/-! ## 2. The block roots

Over a commutative ring `R` with `ψ ^ (2 ^ L) = -1`, block `c` after `ℓ` layers
is reduced modulo `X ^ (2 ^ (M - ℓ)) - rho ψ L ℓ c`.  The lower half of a block
split at layer `ℓ` carries the twiddle `zt ψ L (2 ^ ℓ + c)` as its root and the
upper half its negation. -/

section Roots

variable {R : Type*} [CommRing R]

/-- The twiddle of block index `k`: `ψ ^ BitRev_L k`. -/
def zt (ψ : R) (L k : ℕ) : R := ψ ^ bitrev L k

/-- The root of the modulus block `c` is reduced by after `ℓ` layers. -/
def rho (ψ : R) (L ℓ c : ℕ) : R :=
  if ℓ = 0 then -1
  else if c % 2 = 0 then zt ψ L (2 ^ (ℓ - 1) + c / 2) else - zt ψ L (2 ^ (ℓ - 1) + c / 2)

theorem rho_even (ψ : R) (L ℓ c : ℕ) : rho ψ L (ℓ + 1) (2 * c) = zt ψ L (2 ^ ℓ + c) := by
  unfold rho
  rw [ite_eq_right (Nat.succ_ne_zero ℓ), ite_eq_left (by omega)]
  congr 2
  omega

theorem rho_odd (ψ : R) (L ℓ c : ℕ) :
    rho ψ L (ℓ + 1) (2 * c + 1) = - zt ψ L (2 ^ ℓ + c) := by
  unfold rho
  rw [ite_eq_right (Nat.succ_ne_zero ℓ), ite_eq_right (by omega)]
  congr 3
  omega

/-- The layer twiddle squares to the block root it splits. -/
theorem rho_sq (ψ : R) (L : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (ℓ c : ℕ) (hl : ℓ < L)
    (hc : c < 2 ^ ℓ) : rho ψ L ℓ c = zt ψ L (2 ^ ℓ + c) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hψ' : ψ ^ (2 * 2 ^ m) = -1 := by rw [← pow_succ']; exact hψ
  match ℓ with
  | 0 =>
    have hc0 : c = 0 := by simpa using hc
    subst hc0
    rw [show rho ψ (m + 1) 0 0 = -1 from ite_eq_left rfl, zt, ← pow_mul,
      show (2 : ℕ) ^ 0 + 0 = 1 from rfl, bitrev_one, mul_comm, hψ']
  | (l + 1) =>
    have hpow : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by ring
    have hle : (2 : ℕ) ^ (l + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.even_or_odd' c with ⟨c', hc' | hc'⟩
    · subst hc'
      have hk : 2 ^ l + c' < 2 ^ m := by omega
      rw [rho_even, show 2 ^ (l + 1) + 2 * c' = 2 * (2 ^ l + c') from by omega]
      simp only [zt, ← pow_mul]
      rw [mul_comm (bitrev (m + 1) (2 * (2 ^ l + c'))) 2, bitrev_two_mul m _ hk]
    · subst hc'
      have hk : 2 ^ l + c' < 2 ^ m := by omega
      rw [rho_odd, show 2 ^ (l + 1) + (2 * c' + 1) = 2 * (2 ^ l + c') + 1 from by omega]
      simp only [zt, ← pow_mul]
      rw [mul_comm (bitrev (m + 1) (2 * (2 ^ l + c') + 1)) 2, bitrev_two_mul_succ,
        Nat.mul_add, bitrev_two_mul m _ hk, pow_add, hψ']
      ring

/-- After `L` layers the root of block `i` is `ψ ^ (2 · BitRev_L i + 1)`. -/
theorem rho_last (ψ : R) (L : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (hL : 0 < L) (i : ℕ)
    (hi : i < 2 ^ L) : rho ψ L L i = ψ ^ (2 * bitrev L i + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hψ' : ψ ^ (2 * 2 ^ m) = -1 := by rw [← pow_succ']; exact hψ
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  rcases Nat.even_or_odd' i with ⟨j, hj | hj⟩
  · subst hj
    have hjlt : j < 2 ^ m := by omega
    rw [rho_even, zt, bitrev_pow_add m j hjlt, ← bitrev_two_mul m j hjlt]
  · subst hj
    have hjlt : j < 2 ^ m := by omega
    rw [rho_odd, zt, bitrev_pow_add m j hjlt, bitrev_two_mul_succ, Nat.mul_add,
      bitrev_two_mul m j hjlt,
      show bitrev (m + 1) j + 2 * 2 ^ m + 1 = (bitrev (m + 1) j + 1) + 2 * 2 ^ m from by
        omega, pow_add ψ (bitrev (m + 1) j + 1) (2 * 2 ^ m), hψ']
    ring

end Roots

/-! ## 3. The block invariant on lane functions -/

section Layers

variable {R : Type*} [CommRing R]

/-- The reduction of `w` modulo `X ^ B - r` at offset `t`, from the `n`
coefficients spaced `B` apart. -/
def layerSum (w : ℕ → R) (n : ℕ) (r : R) (B t : ℕ) : R :=
  ∑ s ∈ Finset.range n, w (t + s * B) * r ^ s

/-- Reducing modulo `X ^ B - r` and then modulo the two factors of
`X ^ (2 * B) - r ^ 2` is the butterfly. -/
theorem layerSum_split (w : ℕ → R) (n : ℕ) (r : R) (B t : ℕ) :
    layerSum w (2 * n) r B t
      = layerSum w n (r ^ 2) (2 * B) t + r * layerSum w n (r ^ 2) (2 * B) (t + B) := by
  have hsplit : ∀ (m : ℕ) (f : ℕ → R), ∑ s ∈ Finset.range (2 * m), f s
      = ∑ u ∈ Finset.range m, (f (2 * u) + f (2 * u + 1)) := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, add_assoc]
  unfold layerSum
  rw [hsplit, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e1 : r ^ (2 * u) = (r ^ 2) ^ u := by rw [pow_mul]
  have e2 : r ^ (2 * u + 1) = (r ^ 2) ^ u * r := by rw [pow_succ, pow_mul]
  rw [show t + 2 * u * B = t + u * (2 * B) from by ring,
    show t + (2 * u + 1) * B = t + B + u * (2 * B) from by ring, e1, e2]
  ring

/-- Layer `ℓ` of the length-`2 ^ M` transform on lane function `f`: the
half-length is `2 ^ (M - 1 - ℓ)` and block `c` uses the twiddle
`zt ψ L (2 ^ ℓ + c)`. -/
def layerFn (ψ : R) (L M ℓ : ℕ) (f : ℕ → R) (i : ℕ) : R :=
  if i % (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) < 2 ^ (M - 1 - ℓ) then
    f i + zt ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)))
      * f (i + 2 ^ (M - 1 - ℓ))
  else
    f (i - 2 ^ (M - 1 - ℓ)) - zt ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ))) * f i

/-- `k` layers starting at layer `ℓ`. -/
def run (ψ : R) (L M : ℕ) : (k ℓ : ℕ) → (ℕ → R) → ℕ → R
  | 0, _, f => f
  | k + 1, ℓ, f => run ψ L M k (ℓ + 1) (layerFn ψ L M ℓ f)

/-- After `ℓ` layers, block `c` of length `2 ^ (M - ℓ)` of `a` is the reduction
of `w` modulo `X ^ (2 ^ (M - ℓ)) - rho ψ L ℓ c`. -/
def LayerInv (ψ : R) (L M : ℕ) (w a : ℕ → R) (ℓ : ℕ) : Prop :=
  ∀ c t : ℕ, c < 2 ^ ℓ → t < 2 ^ (M - ℓ) →
    a (c * 2 ^ (M - ℓ) + t) = layerSum w (2 ^ ℓ) (rho ψ L ℓ c) (2 ^ (M - ℓ)) t

theorem layerInv_zero (ψ : R) (L M : ℕ) (w : ℕ → R) : LayerInv ψ L M w w 0 := by
  intro c t hc _
  have hc0 : c = 0 := by simpa using hc
  subst hc0
  simp [layerSum]

/-- One layer carries the block invariant from `ℓ` to `ℓ + 1`. -/
theorem layerInv_step (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (w a : ℕ → R) (ℓ : ℕ)
    (hl : ℓ < L) (hLM : L ≤ M) (h : LayerInv ψ L M w a ℓ) :
    LayerInv ψ L M w (layerFn ψ L M ℓ a) (ℓ + 1) := by
  intro c' t hc' ht
  have hlen : M - (ℓ + 1) = M - 1 - ℓ := by omega
  have hB : (2 : ℕ) ^ (M - ℓ) = 2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ) := by
    rw [show M - ℓ = M - 1 - ℓ + 1 from by omega, pow_succ]; ring
  have hP : (2 : ℕ) ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
  rw [hlen] at ht ⊢
  rw [hP] at hc'
  have hpos : 0 < (2 : ℕ) ^ (M - 1 - ℓ) := Nat.two_pow_pos _
  set len := (2 : ℕ) ^ (M - 1 - ℓ) with hlen_def
  have h' : ∀ c u, c < 2 ^ ℓ → u < len + len →
      a (c * (len + len) + u) = layerSum w (2 ^ ℓ) (rho ψ L ℓ c) (len + len) u := by
    intro c u hc hu
    have := h c u hc (by rw [hB]; exact hu)
    rwa [hB] at this
  rcases Nat.even_or_odd' c' with ⟨c, hc | hc⟩
  · subst hc
    have hcl : c < 2 ^ ℓ := by omega
    have hidx : 2 * c * len + t = t + (len + len) * c := by ring
    have hdiv : (2 * c * len + t) / (len + len) = c := by
      rw [hidx, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
    have hmod : (2 * c * len + t) % (len + len) = t := by
      rw [hidx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h1 := h' c t hcl (by omega)
    have h2 := h' c (t + len) hcl (by omega)
    rw [show c * (len + len) + t = 2 * c * len + t from by ring] at h1
    rw [show c * (len + len) + (t + len) = 2 * c * len + t + len from by ring] at h2
    simp only [layerFn, ← hlen_def, hdiv, hmod, ite_eq_left ht, h1, h2]
    rw [rho_even, hP, ← two_mul (2 ^ ℓ), layerSum_split, rho_sq ψ L hψ ℓ c hl hcl,
      two_mul len]
  · subst hc
    have hcl : c < 2 ^ ℓ := by omega
    have hidx : (2 * c + 1) * len + t = (len + t) + (len + len) * c := by ring
    have hdiv : ((2 * c + 1) * len + t) / (len + len) = c := by
      rw [hidx, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
    have hmod : ((2 * c + 1) * len + t) % (len + len) = len + t := by
      rw [hidx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h1 := h' c t hcl (by omega)
    have h2 := h' c (t + len) hcl (by omega)
    rw [show c * (len + len) + t = (2 * c + 1) * len + t - len from by
      rw [show (2 * c + 1) * len = c * (len + len) + len from by ring]; omega] at h1
    rw [show c * (len + len) + (t + len) = (2 * c + 1) * len + t from by ring] at h2
    simp only [layerFn, ← hlen_def, hdiv, hmod, ite_eq_right (show ¬ len + t < len by omega), h1, h2]
    rw [rho_odd, hP, ← two_mul (2 ^ ℓ), layerSum_split, neg_sq, rho_sq ψ L hψ ℓ c hl hcl,
      two_mul len]
    ring

/-- `k` layers from a state satisfying the invariant at `ℓ` satisfy it at
`ℓ + k`. -/
theorem run_inv (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (hLM : L ≤ M) (w : ℕ → R) :
    ∀ (k ℓ : ℕ) (a : ℕ → R), ℓ + k ≤ L → LayerInv ψ L M w a ℓ →
      LayerInv ψ L M w (run ψ L M k ℓ a) (ℓ + k)
  | 0, _, _, _, h => h
  | k + 1, ℓ, a, hk, h => by
      rw [show ℓ + (k + 1) = ℓ + 1 + k from by omega]
      exact run_inv ψ L M hψ hLM w k (ℓ + 1) _ (by omega)
        (layerInv_step ψ L M hψ w a ℓ (by omega) hLM h)

/-- Lane `i` of the transform: offset `i % 2 ^ (M - L)` of the reduction of `w`
modulo `X ^ (2 ^ (M - L)) - ψ ^ (2 · BitRev_L (i / 2 ^ (M - L)) + 1)`. -/
def nttSpec (ψ : R) (L M : ℕ) (w : ℕ → R) (i : ℕ) : R :=
  ∑ s ∈ Finset.range (2 ^ L),
    w (i % 2 ^ (M - L) + s * 2 ^ (M - L))
      * ψ ^ ((2 * bitrev L (i / 2 ^ (M - L)) + 1) * s)

/-- **The layers compute the transform.** -/
theorem run_spec (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (hL : 0 < L) (hLM : L ≤ M)
    (w : ℕ → R) (i : ℕ) (hi : i < 2 ^ M) :
    run ψ L M L 0 w i = nttSpec ψ L M w i := by
  have hinv := run_inv ψ L M hψ hLM w L 0 w (by omega) (layerInv_zero ψ L M w)
  rw [Nat.zero_add] at hinv
  have hpos : 0 < (2 : ℕ) ^ (M - L) := Nat.two_pow_pos _
  have hM : (2 : ℕ) ^ M = 2 ^ L * 2 ^ (M - L) := by
    rw [← pow_add]; congr 1; omega
  have hc : i / 2 ^ (M - L) < 2 ^ L := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← hM]; exact hi
  have h := hinv (i / 2 ^ (M - L)) (i % 2 ^ (M - L)) hc (Nat.mod_lt _ hpos)
  rw [Nat.div_add_mod'] at h
  rw [h, layerSum, nttSpec, rho_last ψ L hψ hL _ hc]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_mul]

end Layers

/-! ## 4. The `fieldDialect` program -/

/-- The valuation reading lane function `f` from index `off` into an `n`-lane
context. -/
def fnVal (q : ℕ) (f : ℕ → ZMod q) : (n off : ℕ) → Valuation (Ctxn q n)
  | 0, _ => .nil
  | n + 1, off => .cons (f off) (fnVal q f n (off + 1))

theorem fnVal_lookup (q : ℕ) (f : ℕ → ZMod q) :
    ∀ (n i off : ℕ), i ≤ n → fpv (laneVar q n i) (fnVal q f (n + 1) off) = f (off + i)
  | _, 0, off, _ => by
      simp only [fpv, laneVar, fnVal, Nat.add_zero]
      rfl
  | 0, _ + 1, _, h => absurd h (by omega)
  | n + 1, i + 1, off, h => by
      show fpv (laneVar q n i) (fnVal q f (n + 1) (off + 1)) = f (off + (i + 1))
      rw [fnVal_lookup q f n i (off + 1) (by omega)]
      congr 1
      omega

theorem hvGetD_fnVal (q : ℕ) (f : ℕ → ZMod q) :
    ∀ (n off i : ℕ), i < n → hvGetD (fnVal q f n off) i = f (off + i)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, off, 0, _ => by simp [fnVal, hvGetD]
  | n + 1, off, i + 1, h => by
      show hvGetD (fnVal q f n (off + 1)) i = f (off + (i + 1))
      rw [hvGetD_fnVal q f n (off + 1) i (by omega)]
      congr 1
      omega

/-- An `n`-lane valuation agreeing with `f` from `off` on is `fnVal q f n off`. -/
theorem eq_fnVal (q : ℕ) (f : ℕ → ZMod q) :
    ∀ (n off : ℕ) (hv : Valuation (Ctxn q n)),
      (∀ i, i < n → hvGetD hv i = f (off + i)) → hv = fnVal q f n off
  | 0, _, .nil, _ => rfl
  | n + 1, off, .cons x r, h => by
      have h0 := h 0 (by omega)
      simp only [hvGetD, Nat.add_zero] at h0
      have hr : r = fnVal q f n (off + 1) := by
        refine eq_fnVal q f n (off + 1) r fun i hi => ?_
        have := h (i + 1) (by omega)
        simp only [hvGetD] at this
        rw [this]; congr 1; omega
      rw [h0, hr]
      rfl

/-- The schedule of output lane `i` of layer `ℓ` on `n` lanes. -/
def layerLaneProg (q n M L : ℕ) (ψ : ZMod q) (ℓ i : ℕ) : Com fieldDialect (Ctxn q n) (F q) :=
  if i % (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) < 2 ^ (M - 1 - ℓ) then
    laneProg q n (zt ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ))))
      i (i + 2 ^ (M - 1 - ℓ)) true
  else
    laneProg q n (zt ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ))))
      (i - 2 ^ (M - 1 - ℓ)) i false

theorem layerLaneProg_denote (q n M L : ℕ) (ψ : ZMod q) (ℓ i : ℕ) (f : ℕ → ZMod q)
    (hi : i < n)
    (hup : i % (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) < 2 ^ (M - 1 - ℓ) →
      i + 2 ^ (M - 1 - ℓ) < n) :
    PolyToField.fpDenote (layerLaneProg q n M L ψ ℓ i) (fnVal q f n 0)
      = layerFn ψ L M ℓ f i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [layerLaneProg, layerFn]
  generalize 2 ^ (M - 1 - ℓ) = len at *
  split
  · next hlt =>
    rw [laneProg_denote, ite_eq_left rfl, fnVal_lookup q f m i 0 (by omega),
      fnVal_lookup q f m (i + len) 0 (by have := hup hlt; omega)]
    simp
  · next hlt =>
    rw [laneProg_denote, ite_eq_right (by simp), fnVal_lookup q f m (i - len) 0
      (by omega), fnVal_lookup q f m i 0 (by omega)]
    simp

/-- The partner of a lower butterfly lane is inside the `2 ^ M` lanes. -/
theorem layer_partner_lt (M ℓ i : ℕ) (hl : ℓ < M) (hi : i < 2 ^ M)
    (hr : i % (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) < 2 ^ (M - 1 - ℓ)) :
    i + 2 ^ (M - 1 - ℓ) < 2 ^ M := by
  have hpos : 0 < (2 : ℕ) ^ (M - 1 - ℓ) := Nat.two_pow_pos _
  have hM : (2 : ℕ) ^ M = 2 ^ ℓ * (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) := by
    rw [← two_mul, ← pow_succ', ← pow_add]; congr 1; omega
  set B := 2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ) with hB
  have hdm := Nat.div_add_mod i B
  have hlt : i / B < 2 ^ ℓ := by
    rw [Nat.div_lt_iff_lt_mul (by omega), ← hM]; exact hi
  have hle : B * (i / B + 1) ≤ B * 2 ^ ℓ := Nat.mul_le_mul_left _ hlt
  have hring : B * (i / B + 1) = B * (i / B) + B := by ring
  have hcomm : B * 2 ^ ℓ = 2 ^ ℓ * B := mul_comm _ _
  omega

/-- `k` layers from layer `ℓ`, each emitted over the result variables of the
previous one; with `k = 0`, the lanes `h` names. -/
def chain (q n M L : ℕ) (ψ : ZMod q) :
    (k ℓ : ℕ) → {Γ : Ctxt fieldDialect} → Ctxt.Hom (Ctxn q n) Γ →
      MultiReturnCom fieldDialect Γ (List.replicate n (F q))
  | 0, _, _, h => .ret (homToHV _ h)
  | k + 1, ℓ, _, h =>
      Com.foldVarN n (layerLaneProg q n M L ψ ℓ) h
        (fun {_} _ vs => chain q n M L ψ k (ℓ + 1) (hvToHom vs))

/-- `chain` denotes the lanes of `run`. -/
theorem chain_denote (q M L : ℕ) (ψ : ZMod q) :
    ∀ (k ℓ : ℕ) {Γ : Ctxt fieldDialect} (h : Ctxt.Hom (Ctxn q (2 ^ M)) Γ)
      (V : Valuation Γ) (f : ℕ → ZMod q), ℓ + k ≤ M →
      pullV h V = fnVal q f (2 ^ M) 0 →
      (chain q (2 ^ M) M L ψ k ℓ h).denote V = fnVal q (run ψ L M k ℓ f) (2 ^ M) 0
  | 0, _, _, h, V, f, _, hV => by
      show MultiReturnCom.lookupVars (homToHV _ h) V = _
      rw [lookupVars_homToHV, hV]
      rfl
  | k + 1, ℓ, _, h, V, f, hk, hV => by
      refine Com.foldVarN_denote (2 ^ M) _ h V _ _ ?_
      intro Γ' h' vs V' _ hvs
      refine chain_denote q M L ψ k (ℓ + 1) (hvToHom vs) V' (layerFn ψ L M ℓ f)
        (by omega) ?_
      rw [pullV_hvToHom, hvs, hV]
      refine eq_fnVal q _ (2 ^ M) 0 _ fun i hi => ?_
      rw [hvGetD_denoteN _ _ _ i hi, Nat.zero_add]
      exact layerLaneProg_denote q (2 ^ M) M L ψ ℓ i f hi
        (layer_partner_lt M ℓ i (by omega) hi)

/-! ## 5. Parameter records and the transform program -/

/-- The parameters of a merged-twiddle negacyclic NTT: modulus `q`, length
exponent `logN`, layer count `layers` and root `psi`. -/
structure NttParams where
  /-- The coefficient modulus. -/
  q : ℕ
  /-- The polynomial length is `2 ^ logN`. -/
  logN : ℕ
  /-- The number of butterfly layers. -/
  layers : ℕ
  /-- The root; its twiddles are `psi ^ BitRev_layers k`. -/
  psi : ℕ

/-- The side condition, decidable on `ℕ`: at least one layer and no more than
`logN`, `1 < q`, and `psi ^ (2 ^ layers) ≡ -1 (mod q)`. -/
def NttParams.Ok (P : NttParams) : Prop :=
  0 < P.layers ∧ P.layers ≤ P.logN ∧ 1 < P.q ∧ P.psi ^ (2 ^ P.layers) % P.q = P.q - 1

instance (P : NttParams) : Decidable P.Ok :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Under `NttParams.Ok`, the root raised to `2 ^ layers` is `-1` in `ZMod q`. -/
theorem NttParams.psi_pow (P : NttParams) (hP : P.Ok) :
    (P.psi : ZMod P.q) ^ (2 ^ P.layers) = -1 := by
  obtain ⟨_, _, hq, hpow⟩ := hP
  have h := congrArg (Nat.cast : ℕ → ZMod P.q) hpow
  rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_sub (by omega), ZMod.natCast_self,
    Nat.cast_one, zero_sub] at h
  exact h

/-- The transform program of `P` on `2 ^ logN` lanes. -/
def nttProg (P : NttParams) :
    MultiReturnCom fieldDialect (Ctxn P.q (2 ^ P.logN)) (List.replicate (2 ^ P.logN) (F P.q)) :=
  chain P.q (2 ^ P.logN) P.logN P.layers (P.psi : ZMod P.q) P.layers 0 (Ctxt.Hom.id _)

/-- **The value theorem.** For every parameter record satisfying `NttParams.Ok`,
lane `i` of `nttProg P` on the coefficients `w` is `nttSpec` at `i`. -/
theorem nttProg_denote (P : NttParams) (hP : P.Ok) (w : ℕ → ZMod P.q) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    hvGetD ((nttProg P).denote (fnVal P.q w (2 ^ P.logN) 0)) i
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN w i := by
  have hLM : P.layers ≤ P.logN := hP.2.1
  rw [nttProg, chain_denote P.q P.logN P.layers _ P.layers 0 (Ctxt.Hom.id _) _ w (by omega)
    (pullV_id _), hvGetD_fnVal _ _ _ _ _ hi, Nat.zero_add]
  exact run_spec _ P.layers P.logN (P.psi_pow hP) hP.1 hLM w i hi

/-! ## 6. Instances -/

/-- FIPS 203 (ML-KEM): `q = 3329`, 256 coefficients, seven layers, `ψ = 17`. -/
def mlkemNtt : NttParams := ⟨3329, 8, 7, 17⟩

/-- FIPS 204 (ML-DSA): `q = 8380417`, 256 coefficients, eight layers, `ψ = 1753`. -/
def mldsaNtt : NttParams := ⟨8380417, 8, 8, 1753⟩

theorem mlkemNtt_ok : mlkemNtt.Ok := by decide

theorem mldsaNtt_ok : mldsaNtt.Ok := by decide

/-- The ML-KEM transform program computes `nttSpec` at `ψ = 17`, `L = 7`. -/
theorem mlkemNtt_denote (w : ℕ → ZMod 3329) (i : ℕ) (hi : i < 256) :
    hvGetD ((nttProg mlkemNtt).denote (fnVal 3329 w 256 0)) i
      = nttSpec (17 : ZMod 3329) 7 8 w i :=
  nttProg_denote mlkemNtt mlkemNtt_ok w i hi

/-- The ML-DSA transform program computes `nttSpec` at `ψ = 1753`, `L = 8`. -/
theorem mldsaNtt_denote (w : ℕ → ZMod 8380417) (i : ℕ) (hi : i < 256) :
    hvGetD ((nttProg mldsaNtt).denote (fnVal 8380417 w 256 0)) i
      = nttSpec (1753 : ZMod 8380417) 8 8 w i :=
  nttProg_denote mldsaNtt mldsaNtt_ok w i hi

/-! ## 7. Coefficient bounds under a lazy Montgomery schedule

The layers run on unsigned representatives in `ℕ`, as word code runs them: the
twiddle product is the Montgomery reduction `Number.montgomeryReduce q R q'` of
the product with the twiddle in Montgomery form `ψ ^ BitRev_L k · R mod q`, the
lower butterfly output is the unreduced sum, the upper is `x + off · q − t`, and
after the layers the schedule marks each lane is replaced by its residue. -/

/-- A lazy Montgomery schedule: radix `R`, Montgomery constant `qinv` with
`q · qinv ≡ -1 (mod R)`, subtraction offset `off` (in multiples of `q`), the
layers `red` after which lanes are reduced, and the word width `w`. -/
structure LazySched where
  /-- The Montgomery radix. -/
  R : ℕ
  /-- The Montgomery constant. -/
  qinv : ℕ
  /-- The upper butterfly output is `x + off · q − t`. -/
  off : ℕ
  /-- Lanes are reduced after layer `ℓ` when `red ℓ`. -/
  red : ℕ → Bool
  /-- The word width. -/
  w : ℕ

section Lazy

open CatCrypt.Crypto.Number (montgomeryReduce montgomeryReduce_correct)

variable (P : NttParams) (S : LazySched)

/-- The twiddle of block `k` in Montgomery form: `ψ ^ BitRev_L k · R mod q`. -/
def zr (k : ℕ) : ℕ := P.psi ^ bitrev P.layers k * S.R % P.q

/-- The reduced twiddle product of block `k`. -/
def tmul (k x : ℕ) : ℕ := montgomeryReduce P.q S.R S.qinv (zr P S k * x)

/-- Layer `ℓ` on representatives. -/
def lazyLayer (ℓ : ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  let v :=
    if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
      f i + tmul P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))
        (f (i + 2 ^ (P.logN - 1 - ℓ)))
    else
      f (i - 2 ^ (P.logN - 1 - ℓ)) + S.off * P.q
        - tmul P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))) (f i)
  if S.red ℓ then v % P.q else v

/-- `k` layers on representatives starting at layer `ℓ`. -/
def lazyRun : (k ℓ : ℕ) → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, f => f
  | k + 1, ℓ, f => lazyRun k (ℓ + 1) (lazyLayer P S ℓ f)

/-- The bound on every lane after `ℓ` layers: `q` at the start and after a
reduced layer, `bnd ℓ + off · q` otherwise. -/
def bnd : ℕ → ℕ
  | 0 => P.q
  | ℓ + 1 => if S.red ℓ then P.q else bnd ℓ + S.off * P.q

/-- The side condition of a schedule, decidable on `ℕ`: the offset covers a
reduced twiddle product, `R` is a positive radix coprime to `q` with Montgomery
constant `qinv`, the Montgomery numerator fits two words, and for every layer
count up to `L` the bound is at most `R` and the bound plus the offset fits a
word. -/
def SchedOk : Prop :=
  2 ≤ S.off ∧ 0 < S.R ∧ Nat.Coprime S.R P.q ∧ (P.q * S.qinv) % S.R = S.R - 1 ∧
    2 * P.q * S.R ≤ 2 ^ (2 * S.w) ∧
    ∀ ℓ, ℓ < P.layers + 1 → bnd P S ℓ ≤ S.R ∧ bnd P S ℓ + S.off * P.q ≤ 2 ^ S.w

instance : Decidable (SchedOk P S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem zr_lt (hq : 0 < P.q) (k : ℕ) : zr P S k < P.q := Nat.mod_lt _ hq

theorem zr_mul_lt (hq : 0 < P.q) (hR : 0 < S.R) (k x : ℕ) (hx : x ≤ S.R) :
    zr P S k * x < S.R * P.q := by
  have h1 : zr P S k * x ≤ zr P S k * S.R := Nat.mul_le_mul_left _ hx
  have h2 : zr P S k * S.R < P.q * S.R := Nat.mul_lt_mul_of_pos_right (zr_lt P S hq k) hR
  rw [Nat.mul_comm S.R]
  omega

/-- The reduced twiddle product is below `2 q`. -/
theorem tmul_lt (hq : 0 < P.q) (hR : 0 < S.R) (hN : (P.q * S.qinv) % S.R = S.R - 1)
    (k x : ℕ) (hx : x ≤ S.R) : tmul P S k x < 2 * P.q :=
  (montgomeryReduce_correct P.q S.R S.qinv _ hq hR hN (zr_mul_lt P S hq hR k x hx)).1

/-- The reduced twiddle product is the twiddle times the input in `ZMod q`. -/
theorem tmul_cast (hq : 0 < P.q) (hR : 0 < S.R) (hcop : Nat.Coprime S.R P.q)
    (hN : (P.q * S.qinv) % S.R = S.R - 1) (k x : ℕ) (hx : x ≤ S.R) :
    ((tmul P S k x : ℕ) : ZMod P.q) = zt (P.psi : ZMod P.q) P.layers k * (x : ZMod P.q) := by
  have hmod := (montgomeryReduce_correct P.q S.R S.qinv _ hq hR hN
    (zr_mul_lt P S hq hR k x hx)).2
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [Nat.cast_mul, Nat.cast_mul, zr, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow] at hcast
  have hu : IsUnit ((S.R : ℕ) : ZMod P.q) := ⟨ZMod.unitOfCoprime S.R hcop, rfl⟩
  apply hu.mul_left_inj.mp
  rw [tmul, zr, hcast, zt]
  ring

/-- One layer on representatives casts to `layerFn`. -/
theorem lazyLayer_cast (hS : SchedOk P S) (hq : 0 < P.q) (ℓ : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f j ≤ S.R) (i : ℕ) :
    ((lazyLayer P S ℓ f i : ℕ) : ZMod P.q)
      = layerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => (f j : ZMod P.q)) i := by
  obtain ⟨hoff, hR, hcop, hN, _, _⟩ := hS
  have hpre : ((if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ)
      then f i + tmul P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))
        (f (i + 2 ^ (P.logN - 1 - ℓ)))
      else f (i - 2 ^ (P.logN - 1 - ℓ)) + S.off * P.q
        - tmul P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))) (f i) : ℕ)
        : ZMod P.q)
      = layerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => (f j : ZMod P.q)) i := by
    rw [layerFn]
    generalize 2 ^ (P.logN - 1 - ℓ) = len
    generalize 2 ^ ℓ + i / (len + len) = k
    split
    · rw [Nat.cast_add, tmul_cast P S hq hR hcop hN k _ (hf _)]
    · have ht := tmul_lt P S hq hR hN k (f i) (hf i)
      have hle : tmul P S k (f i) ≤ f (i - len) + S.off * P.q := by
        have : 2 * P.q ≤ S.off * P.q := Nat.mul_le_mul_right _ hoff
        omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        tmul_cast P S hq hR hcop hN k _ (hf _)]
      ring
  rw [lazyLayer]
  split
  · rw [ZMod.natCast_mod]; exact hpre
  · exact hpre

/-- One layer on representatives below `bnd ℓ` stays below `bnd (ℓ + 1)`. -/
theorem lazyLayer_lt (hS : SchedOk P S) (hq : 0 < P.q) (ℓ : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f j < bnd P S ℓ) (hbR : bnd P S ℓ ≤ S.R) (i : ℕ) :
    lazyLayer P S ℓ f i < bnd P S (ℓ + 1) := by
  obtain ⟨hoff, hR, _, hN, _, _⟩ := hS
  have hoffq : 2 * P.q ≤ S.off * P.q := Nat.mul_le_mul_right _ hoff
  have hpre : (if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ)
      then f i + tmul P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))
        (f (i + 2 ^ (P.logN - 1 - ℓ)))
      else f (i - 2 ^ (P.logN - 1 - ℓ)) + S.off * P.q
        - tmul P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))) (f i))
      < bnd P S ℓ + S.off * P.q := by
    generalize 2 ^ (P.logN - 1 - ℓ) = len
    generalize 2 ^ ℓ + i / (len + len) = k
    split
    · have := tmul_lt P S hq hR hN k (f (i + len)) (by have := hf (i + len); omega)
      have := hf i
      omega
    · have := hf (i - len)
      omega
  rw [lazyLayer, bnd]
  by_cases hr : S.red ℓ = true
  · rw [ite_eq_left hr, ite_eq_left hr]; exact Nat.mod_lt _ hq
  · rw [ite_eq_right hr, ite_eq_right hr]; exact hpre

theorem bnd_le_R (hS : SchedOk P S) (ℓ : ℕ) (hl : ℓ ≤ P.layers) : bnd P S ℓ ≤ S.R :=
  (hS.2.2.2.2.2 ℓ (by omega)).1

/-- **The bound theorem.** From inputs below `bnd ℓ`, after `k` more layers every
lane is below `bnd (ℓ + k)`. -/
theorem lazyRun_lt (hS : SchedOk P S) (hq : 0 < P.q) :
    ∀ (k ℓ : ℕ) (f : ℕ → ℕ), ℓ + k ≤ P.layers → (∀ j, f j < bnd P S ℓ) →
      ∀ j, lazyRun P S k ℓ f j < bnd P S (ℓ + k)
  | 0, _, _, _, hf => hf
  | k + 1, ℓ, f, hk, hf => by
      rw [show ℓ + (k + 1) = ℓ + 1 + k from by omega]
      exact lazyRun_lt hS hq k (ℓ + 1) _ (by omega)
        (lazyLayer_lt P S hS hq ℓ f hf (bnd_le_R P S hS ℓ (by omega)))

/-- **The congruence theorem.** From inputs below `bnd ℓ`, `k` layers on
representatives cast to `k` layers of `run` over `ZMod q`. -/
theorem lazyRun_cast (hS : SchedOk P S) (hq : 0 < P.q) :
    ∀ (k ℓ : ℕ) (f : ℕ → ℕ), ℓ + k ≤ P.layers → (∀ j, f j < bnd P S ℓ) →
      ∀ i, ((lazyRun P S k ℓ f i : ℕ) : ZMod P.q)
        = run (P.psi : ZMod P.q) P.layers P.logN k ℓ (fun j => (f j : ZMod P.q)) i
  | 0, _, _, _, _ => fun _ => rfl
  | k + 1, ℓ, f, hk, hf => by
      have hR := bnd_le_R P S hS ℓ (by omega)
      have hlayer : (fun j => ((lazyLayer P S ℓ f j : ℕ) : ZMod P.q))
          = layerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => (f j : ZMod P.q)) :=
        funext (lazyLayer_cast P S hS hq ℓ f (fun j => by have := hf j; omega))
      intro i
      rw [lazyRun, lazyRun_cast hS hq k (ℓ + 1) _ (by omega)
        (lazyLayer_lt P S hS hq ℓ f hf hR), hlayer]
      rfl

/-- **The lazy run computes the transform program.** From inputs below `q`, the
representatives after all layers cast to the lanes of `nttProg P`. -/
theorem lazyRun_eq_nttProg (hP : P.Ok) (hS : SchedOk P S) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    ((lazyRun P S P.layers 0 f i : ℕ) : ZMod P.q)
      = hvGetD ((nttProg P).denote (fnVal P.q (fun j => (f j : ZMod P.q)) (2 ^ P.logN) 0)) i := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  rw [lazyRun_cast P S hS hq P.layers 0 f (by omega) hf i, nttProg_denote P hP _ i hi]
  exact run_spec _ P.layers P.logN (P.psi_pow hP) hP.1 hP.2.1 _ i hi

/-- **Word fit.** For a layer `ℓ < L` and inputs `x, y` below `bnd ℓ`, the
twiddle product is below `q · R`, the Montgomery numerator below `2 ^ (2 w)`, the
pre-subtraction sum `y + off · q` below `2 ^ w`, and the next bound at most
`2 ^ w`. -/
theorem butterfly_words (hP : P.Ok) (hS : SchedOk P S) (ℓ : ℕ) (hl : ℓ < P.layers)
    (k x y : ℕ) (hx : x < bnd P S ℓ) (hy : y < bnd P S ℓ) :
    zr P S k * x < S.R * P.q ∧
    zr P S k * x + (zr P S k * x * S.qinv % S.R) * P.q < 2 ^ (2 * S.w) ∧
    y + S.off * P.q < 2 ^ S.w ∧ bnd P S (ℓ + 1) ≤ 2 ^ S.w := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  obtain ⟨_, hR, _, _, hRw, hb⟩ := hS
  have hbℓ := hb ℓ (by omega)
  have hb1 := hb (ℓ + 1) (by omega)
  have hprod := zr_mul_lt P S hq hR k x (by omega)
  have hm : zr P S k * x * S.qinv % S.R < S.R := Nat.mod_lt _ hR
  have hmq : (zr P S k * x * S.qinv % S.R) * P.q < S.R * P.q :=
    Nat.mul_lt_mul_of_pos_right hm hq
  refine ⟨hprod, ?_, by omega, by omega⟩
  have : 2 * P.q * S.R = S.R * P.q + S.R * P.q := by ring
  omega

end Lazy

/-- The ML-KEM schedule: radix `2 ^ 16`, offset `2 q`, no reduced layer,
16-bit words. -/
def mlkemLazy : LazySched := ⟨2 ^ 16, 3327, 2, fun _ => false, 16⟩

/-- The ML-DSA schedule: radix `2 ^ 32`, offset `2 q`, no reduced layer,
32-bit words. -/
def mldsaLazy : LazySched := ⟨2 ^ 32, 4236238847, 2, fun _ => false, 32⟩

theorem mlkemLazy_ok : SchedOk mlkemNtt mlkemLazy := by decide

theorem mldsaLazy_ok : SchedOk mldsaNtt mldsaLazy := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
