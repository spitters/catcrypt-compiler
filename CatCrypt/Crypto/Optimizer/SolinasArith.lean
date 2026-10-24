/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Set

/-!
# Value-level Solinas reduction modulo `p = 2^k - c`

For a modulus `p = 2^k - c` with small `c`, a double-width value
`V = high · 2^k + low` is reduced by two folds `v ↦ (v / 2^k) · c + v % 2^k`, each
preserving the residue because `2^k ≡ c (mod p)`, followed by one conditional
subtraction of `p`. Under the side condition `c · (c + 3) < 2^k` the result is the
canonical residue. The statements are over `Nat` only.

## Main definitions

* `SolinasPrime`, `SolinasPrime.modulus`: the pair `(k, c)` and `p = 2^k - c`.
* `SolinasOK`: the side condition on `(k, c)` and the two halves.
* `solinasFold`, `solinasReduce`: one fold, and two folds with a conditional subtraction.
* `solinasParams25519`, `solinasParamsSecp256k1`, `solinasParamsPoly1305`: the pairs of
  `2^255 - 19`, `2^256 - (2^32 + 977)` and `2^130 - 5`.

## Main results

* `solinasFold_mod`: a fold preserves the residue modulo `p`.
* `solinasFold_lt`: the bound of a fold.
* `solinasReduce_eq_mod`: `solinasReduce P high low = (high · 2^k + low) % p` under
  `SolinasOK`.
* `reduce25519_eq_mod`, `reduceSecp256k1_eq_mod`, `reducePoly1305_eq_mod`: the three
  instances.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ModReduceSelect

/-! ## 1. The prime shape -/

/-- A pseudo-Mersenne / Solinas modulus descriptor: the prime is `p = 2^k - c`, with
    `k` the bit position of the radix split and `c` the subtrahend. -/
structure SolinasPrime where
  /-- The radix exponent: the modulus is `2^k - c`. -/
  k : Nat
  /-- The small subtrahend `c` in `p = 2^k - c`. -/
  c : Nat

/-- The modulus `p = 2^k - c` as a `Nat`. -/
def SolinasPrime.modulus (P : SolinasPrime) : Nat := 2 ^ P.k - P.c

/-! ## 2. The side condition

Two folds leave `t' < c·(c+1) + 2^k`; one conditional subtraction gives the residue
when `t' < 2·p = 2^(k+1) − 2c`, which follows from `c·(c + 3) < 2^k`. The halves are
below `2^k`. -/

/-- The side condition under which `solinasReduce` is exact: `c ≥ 1`, the halves are
    below the radix, and `c·(c+3) < 2^k`. -/
structure SolinasOK (P : SolinasPrime) (high low : Nat) : Prop where
  /-- `c ≥ 1`, so `2^k - c < 2^k` is a proper modulus. -/
  c_pos : 1 ≤ P.c
  /-- The high limb is below the radix `2^k`. -/
  high_lt : high < 2 ^ P.k
  /-- The low limb is below the radix `2^k`. -/
  low_lt : low < 2 ^ P.k
  /-- The small-`c` regime: `c · (c + 3) < 2^k`, so two folds leave the value
      below `2·p` and one conditional subtract suffices. -/
  cc_lt : P.c * (P.c + 3) < 2 ^ P.k

/-! ## 3. The fold and the reduction -/

/-- One Solinas fold: replace `v = vh · 2^k + vl` by `vh · c + vl`. Since
    `2^k ≡ c (mod p)`, this preserves the residue mod `p`. -/
def solinasFold (P : SolinasPrime) (v : Nat) : Nat :=
  (v / 2 ^ P.k) * P.c + v % 2 ^ P.k

/-- Two folds followed by one conditional subtraction of `p`. -/
def solinasReduce (P : SolinasPrime) (high low : Nat) : Nat :=
  let t := solinasFold P (high * 2 ^ P.k + low)   -- = high·c + low
  let t' := solinasFold P t                        -- the second (quotient) fold
  if t' < P.modulus then t' else t' - P.modulus

/-! ## 4. Correctness over all `(k, c)` -/

/-- `2^k ≡ c (mod p)` for `p = 2^k - c` with `c ≤ 2^k`: the defining congruence
    the fold exploits. -/
theorem two_pow_k_mod (P : SolinasPrime) (hc : P.c ≤ 2 ^ P.k) :
    (2 ^ P.k) % P.modulus = P.c % P.modulus := by
  have heq : (2 : Nat) ^ P.k = P.modulus + P.c := by
    simp only [SolinasPrime.modulus]; omega
  rw [heq, Nat.add_mod_left]

/-- A fold preserves the residue mod `p`: `solinasFold v ≡ v (mod p)`. This is
    the core algebraic fact `(vh·2^k + vl) ≡ vh·c + vl (mod p)`. -/
theorem solinasFold_mod (P : SolinasPrime) (hc : P.c ≤ 2 ^ P.k) (v : Nat) :
    solinasFold P v % P.modulus = v % P.modulus := by
  have hsplit : v = (v / 2 ^ P.k) * 2 ^ P.k + v % 2 ^ P.k := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod v _).symm
  conv_rhs => rw [hsplit]
  simp only [solinasFold]
  -- `(q·2^k + r) % p = (q·c + r) % p` because `2^k ≡ c (mod p)`.
  conv_rhs =>
    rw [Nat.add_mod, Nat.mul_mod, two_pow_k_mod P hc, ← Nat.mul_mod, ← Nat.add_mod]

/-- After one fold of a value `v < 2^k · M`, the result is below `M · c + 2^k`
    (the high part `< M` times `c`, plus a residue `< 2^k`). -/
theorem solinasFold_lt (P : SolinasPrime) {v M : Nat} (hM : v < 2 ^ P.k * M) :
    solinasFold P v < M * P.c + 2 ^ P.k := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  simp only [solinasFold]
  have hq : v / 2 ^ P.k < M := by
    rw [Nat.div_lt_iff_lt_mul hk]; rwa [Nat.mul_comm] at hM
  have hr : v % 2 ^ P.k < 2 ^ P.k := Nat.mod_lt _ hk
  calc (v / 2 ^ P.k) * P.c + v % 2 ^ P.k
      ≤ (M - 1) * P.c + v % 2 ^ P.k := by
        have : v / 2 ^ P.k ≤ M - 1 := by omega
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _
    _ < M * P.c + 2 ^ P.k := by
        have hMc : (M - 1) * P.c ≤ M * P.c := Nat.mul_le_mul_right _ (by omega)
        omega

/-- Under `SolinasOK`, two folds and a conditional subtraction give the canonical
    residue: `solinasReduce P high low = (high · 2^k + low) mod (2^k - c)`. -/
theorem solinasReduce_eq_mod (P : SolinasPrime) {high low : Nat}
    (h : SolinasOK P high low) :
    solinasReduce P high low = (high * 2 ^ P.k + low) % P.modulus := by
  have hk : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  -- c·(c+3) < 2^k gives c < 2^k and c ≤ 2^k.
  have hc_lt : P.c < 2 ^ P.k :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) h.cc_lt
  have hc_le : P.c ≤ 2 ^ P.k := le_of_lt hc_lt
  have hp_pos : 0 < P.modulus := by
    simp only [SolinasPrime.modulus]; omega
  -- The two folds preserve the residue.
  set t := solinasFold P (high * 2 ^ P.k + low) with ht
  set t' := solinasFold P t with ht'
  have hmod : t' % P.modulus = (high * 2 ^ P.k + low) % P.modulus := by
    rw [ht', solinasFold_mod P hc_le, ht, solinasFold_mod P hc_le]
  -- Bound t': first fold of a value < 2^k·(high+1) gives t < (high+1)·c + 2^k.
  have hV : high * 2 ^ P.k + low < 2 ^ P.k * (high + 1) := by
    have : low < 2 ^ P.k := h.low_lt
    calc high * 2 ^ P.k + low < high * 2 ^ P.k + 2 ^ P.k := by omega
      _ = 2 ^ P.k * (high + 1) := by ring
  have ht_lt : t < (high + 1) * P.c + 2 ^ P.k := by
    rw [ht]; exact solinasFold_lt P hV
  -- high + 1 ≤ 2^k, so t < 2^k·(c+1).
  have htM : t < 2 ^ P.k * (P.c + 1) := by
    have hh1 : high + 1 ≤ 2 ^ P.k := by have := h.high_lt; omega
    have : (high + 1) * P.c ≤ 2 ^ P.k * P.c := Nat.mul_le_mul_right _ hh1
    calc t < (high + 1) * P.c + 2 ^ P.k := ht_lt
      _ ≤ 2 ^ P.k * P.c + 2 ^ P.k := by omega
      _ = 2 ^ P.k * (P.c + 1) := by ring
  -- the second fold of t < 2^k·(c+1) gives t' < (c+1)·c + 2^k.
  have ht'_lt : t' < (P.c + 1) * P.c + 2 ^ P.k := by
    rw [ht']; exact solinasFold_lt P htM
  -- (c+1)·c + 2^k = c·c + c + 2^k.  Need t' < 2·p = 2^(k+1) - 2c, i.e. c·c + 3c < 2^k.
  have hcc : P.c * (P.c + 3) < 2 ^ P.k := h.cc_lt
  have ht'_2p : t' < 2 * P.modulus := by
    simp only [SolinasPrime.modulus]
    have hexp : (P.c + 1) * P.c + 2 ^ P.k = P.c * (P.c + 3) + 2 ^ P.k - 2 * P.c := by
      have : P.c * (P.c + 3) = (P.c + 1) * P.c + 2 * P.c := by ring
      omega
    -- 2·(2^k - c) = 2·2^k - 2c.  From c·(c+3) < 2^k: (c+1)·c + 2^k < 2·2^k - 2c.
    have key : (P.c + 1) * P.c + 2 ^ P.k < 2 * (2 ^ P.k - P.c) := by
      have hexpand : P.c * (P.c + 3) = (P.c + 1) * P.c + 2 * P.c := by ring
      have : (P.c + 1) * P.c + 2 * P.c < 2 ^ P.k := by rw [← hexpand]; exact hcc
      omega
    omega
  -- Conclude: t' < 2p and t' ≡ V (mod p), so the conditional subtract gives V mod p.
  simp only [solinasReduce, ← ht, ← ht']
  by_cases hlt : t' < P.modulus
  · rw [ite_eq_left hlt]
    rw [← hmod, Nat.mod_eq_of_lt hlt]
  · rw [ite_eq_right hlt]
    have hlt : P.modulus ≤ t' := Nat.le_of_not_lt hlt
    have h1 : t' - P.modulus < P.modulus := by omega
    rw [← hmod]
    rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt h1]

/-! ## 5. Per-prime instantiations

Each discharges the side condition `c·(c+3) < 2^k` and specialises
`solinasReduce_eq_mod`. -/

/-- Curve25519 / Ed25519: `p = 2^255 - 19`. -/
def solinasParams25519 : SolinasPrime := { k := 255, c := 19 }

/-- secp256k1 (Bitcoin's curve base field): `p = 2^256 - (2^32 + 977)`. -/
def solinasParamsSecp256k1 : SolinasPrime := { k := 256, c := 2 ^ 32 + 977 }

/-- Poly1305: `p = 2^130 - 5`. -/
def solinasParamsPoly1305 : SolinasPrime := { k := 130, c := 5 }

/-- At `(255, 19)`: for halves below `2^255`, `solinasReduce` equals
    `(high·2^255 + low) mod (2^255 - 19)`. -/
theorem reduce25519_eq_mod {high low : Nat}
    (hh : high < 2 ^ 255) (hl : low < 2 ^ 255) :
    solinasReduce solinasParams25519 high low
      = (high * 2 ^ 255 + low) % (2 ^ 255 - 19) :=
  solinasReduce_eq_mod solinasParams25519
    { c_pos := by norm_num [solinasParams25519]
      high_lt := hh
      low_lt := hl
      cc_lt := by
        show 19 * (19 + 3) < 2 ^ 255
        have h9 : (2 : Nat) ^ 9 ≤ 2 ^ 255 :=
          Nat.pow_le_pow_right (Nat.zero_lt_two) (by omega)
        have e9 : (2 : Nat) ^ 9 = 512 := by norm_num
        omega }

/-- At secp256k1 `(256, 2^32 + 977)`: `solinasReduce` computes the secp256k1
    residue. -/
theorem reduceSecp256k1_eq_mod {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    solinasReduce solinasParamsSecp256k1 high low
      = (high * 2 ^ 256 + low) % (2 ^ 256 - (2 ^ 32 + 977)) :=
  solinasReduce_eq_mod solinasParamsSecp256k1
    { c_pos := by norm_num [solinasParamsSecp256k1]
      high_lt := hh
      low_lt := hl
      cc_lt := by
        show (2 ^ 32 + 977) * ((2 ^ 32 + 977) + 3) < 2 ^ 256
        have e32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
        have e33 : (2 : Nat) ^ 33 = 8589934592 := by norm_num
        have h1 : (2 : Nat) ^ 32 + 977 < 2 ^ 33 := by omega
        have h2 : (2 : Nat) ^ 32 + 977 + 3 < 2 ^ 33 := by omega
        calc (2 ^ 32 + 977) * ((2 ^ 32 + 977) + 3)
            < 2 ^ 33 * 2 ^ 33 := Nat.mul_lt_mul'' h1 h2
          _ = 2 ^ 66 := by ring
          _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (Nat.zero_lt_two) (by omega) }

/-- At Poly1305 `(130, 5)`: `solinasReduce` computes the Poly1305 residue. -/
theorem reducePoly1305_eq_mod {high low : Nat}
    (hh : high < 2 ^ 130) (hl : low < 2 ^ 130) :
    solinasReduce solinasParamsPoly1305 high low
      = (high * 2 ^ 130 + low) % (2 ^ 130 - 5) :=
  solinasReduce_eq_mod solinasParamsPoly1305
    { c_pos := by norm_num [solinasParamsPoly1305]
      high_lt := hh
      low_lt := hl
      cc_lt := by
        show 5 * (5 + 3) < 2 ^ 130
        have h6 : (2 : Nat) ^ 6 ≤ 2 ^ 130 :=
          Nat.pow_le_pow_right (Nat.zero_lt_two) (by omega)
        have e6 : (2 : Nat) ^ 6 = 64 := by norm_num
        omega }

end CatCrypt.Crypto.Optimizer.ModReduceSelect
