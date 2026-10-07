/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# FIPS 203 §4.2.1 Compress / Decompress for ML-KEM

Computable `Compress_d` and `Decompress_d` over `ZMod 3329` and `ZMod (2^d)`,
using integer round-half-up (no reals).

For a coefficient `x ∈ Z_q` with `q = 3329`:

* `compress_d d x = round((2^d / q) · x) mod 2^d`, implemented as
  `((2^d · x.val + ⌊q/2⌋) / q) mod 2^d`.
* `decompress_d d y = round((q / 2^d) · y)`, implemented as
  `(q · y.val + ⌊2^d/2⌋) / 2^d`.

The round trip is approximate. `roundtrip_error_int` gives the FIPS 203 error
bound: writing `c` for the (pre-reduction) compression of a coefficient `x < q`
and `x'` for its decompression, the centered error satisfies

  `|x' - x| ≤ round(q / 2^(d+1)) = (q + 2^d) / 2^(d+1)`.

This is `errorBound d`. For ML-KEM the relevant parameters are `d_u = 10`
(bound 2) and `d_v = 4` (bound 104), both instances of the general statement
with `d ≥ 1`.

## Main definitions

* `q` — the ML-KEM modulus `3329`.
* `compress_d d x` — `Compress_d` of FIPS 203 §4.2.1, as
  `((2^d · x.val + ⌊q/2⌋) / q) mod 2^d`.
* `decompress_d d y` — `Decompress_d` of FIPS 203 §4.2.1, as
  `(q · y.val + ⌊2^d/2⌋) / 2^d`.
* `errorBound d` — the bound `round(q / 2^(d+1)) = (q + 2^d) / 2^(d+1)`.

## Main results

* `roundtrip_error_int` — for `d ≥ 1` and a natural number `x < 3329`, the integer
  distance between `x` and the decompression of its compression before reduction
  modulo `2^d` is at most `(3329 + 2^d) / (2 · 2^d)`. The statement is over natural
  numbers and does not mention `compress_d` and `decompress_d`; the distance is the
  absolute value of the integer difference, not the distance modulo `q`.

## References

* NIST FIPS 203 §4.2.1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.Compress

/-- ML-KEM modulus. Reducible, so that `ZMod q` unifies with `ZMod 3329`. -/
abbrev q : ℕ := 3329

/-- FIPS 203 Compress_d: round `x ∈ Z_q` to `Z_{2^d}`.

    `Compress_d(x) = round((2^d / q) · x) mod 2^d`. -/
def compress_d (d : ℕ) (x : ZMod q) : ZMod (2 ^ d) :=
  ((2 ^ d * x.val + q / 2) / q : ℕ)

/-- FIPS 203 Decompress_d: map `y ∈ Z_{2^d}` back to `Z_q`.

    `Decompress_d(y) = round((q / 2^d) · y)`. -/
def decompress_d (d : ℕ) (y : ZMod (2 ^ d)) : ZMod q :=
  ((q * y.val + 2 ^ d / 2) / 2 ^ d : ℕ)

/-- The FIPS 203 §4.2.1 round-trip error bound `round(q / 2^(d+1))`. -/
def errorBound (d : ℕ) : ℕ := (q + 2 ^ d) / 2 ^ (d + 1)

/-- FIPS 203 §4.2.1 compression error bound.

    For a coefficient `x < q`, let `c` be the pre-reduction compression
    `round((2^d / q) · x)` and `x'` the decompression `round((q / 2^d) · c)`.
    The centered error is bounded by `round(q / 2^(d+1))`, i.e.
    `|x' - x| ≤ (q + 2^d) / (2 · 2^d)`, which is `errorBound d`.

    Stated for `d ≥ 1`, covering every ML-KEM compression parameter. -/
theorem roundtrip_error_int (d : ℕ) (hd : 1 ≤ d) (x : ℕ) (hx : x < 3329) :
    let n : ℕ := 2 ^ d
    let c : ℕ := (n * x + 1664) / 3329
    let x' : ℕ := (3329 * c + n / 2) / n
    |(x' : ℤ) - x| ≤ ((3329 : ℤ) + n) / (2 * n) := by
  intro n c x'
  -- Make the let-bound `c`, `x'` opaque locals with their defining equations, so the
  -- linear-arithmetic view never confuses `x'` with its (syntactically distinct) quotient.
  have hcdef : c = (n * x + 1664) / 3329 := rfl
  have hx'def : x' = (3329 * c + n / 2) / n := rfl
  clear_value c x'
  -- `n = 2 * k` with `k = 2^(d-1)`, so `n / 2 = k` and no floor-division atom survives.
  obtain ⟨k, hk, hkpos⟩ : ∃ k, n = 2 * k ∧ 0 < k := by
    refine ⟨2 ^ (d - 1), ?_, Nat.two_pow_pos _⟩
    show 2 ^ d = 2 * 2 ^ (d - 1)
    rw [← pow_succ']
    congr 1
    omega
  have hn : 0 < n := by omega
  have hhalf : n / 2 = k := by omega
  -- Obtain the two remainders as opaque bounded ℕ variables (no `%`/`/` survives
  -- into the linear-arithmetic view — that avoids the quotient-form desync).
  obtain ⟨rc, hrc_lt, hrc_eq⟩ : ∃ rc, rc < 3329 ∧ 3329 * c + rc = n * x + 1664 :=
    ⟨(n * x + 1664) % 3329, Nat.mod_lt _ (by norm_num), by
      have h := Nat.div_add_mod (n * x + 1664) 3329; rw [← hcdef] at h; omega⟩
  obtain ⟨rx, hrx_lt, hrx_eq⟩ : ∃ rx, rx < n ∧ n * x' + rx = 3329 * c + k :=
    ⟨(3329 * c + n / 2) % n, Nat.mod_lt _ hn, by
      have h := Nat.div_add_mod (3329 * c + n / 2) n; rw [← hx'def] at h; omega⟩
  -- cast the clean (division-free) facts to ℤ
  have hcZ : (3329 : ℤ) * c + rc = n * x + 1664 := by exact_mod_cast hrc_eq
  have hx'Z : (n : ℤ) * x' + rx = 3329 * c + k := by exact_mod_cast hrx_eq
  have hnZ : (n : ℤ) = 2 * k := by exact_mod_cast hk
  have hcmZ : (rc : ℤ) < 3329 := by exact_mod_cast hrc_lt
  have hx'mZ : (rx : ℤ) < n := by exact_mod_cast hrx_lt
  have hr1 : (0 : ℤ) ≤ (rc : ℤ) := by positivity
  have hr2 : (0 : ℤ) ≤ (rx : ℤ) := by positivity
  have pos : (0 : ℤ) < 2 * n := by positivity
  rw [Int.le_ediv_iff_mul_le pos]
  have key : |(x' : ℤ) - x| * (2 * n) = |((x' : ℤ) - x) * (2 * n)| := by
    rw [abs_mul, abs_of_pos pos]
  rw [key, abs_le]
  -- `(x'-x)·2n = 2·(n·x') - 2·(n·x)`; hx'Z, hcZ pin `n·x'`, `n·x` linearly
  have expand : ((x' : ℤ) - x) * (2 * n) = 2 * ((n : ℤ) * x') - 2 * ((n : ℤ) * x) := by ring
  rw [expand]
  constructor <;> nlinarith [hcZ, hx'Z, hcmZ, hx'mZ, hr1, hr2, hnZ]

end CatCrypt.Crypto.MLKEM.Compress
