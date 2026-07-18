/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Generic Barrett reduction — the ℕ correctness core

This file develops the **Barrett reduction** generically, over an arbitrary
modulus `q` and shift `k`, working entirely in `ℕ`.

Barrett reduction replaces the (expensive) division `x / q` by the cheap
right-shift of a product with a precomputed reciprocal.  For a modulus `q` and
a shift `k`, the precomputed reciprocal is

```
mu = 2^k / q            (truncating ℕ division)
```

and the Barrett estimate of `x` is

```
t        = (x * mu) / 2^k        (the estimated quotient `≈ x / q`)
barrett x = x - t * q            (the estimated remainder, before condsub)
```

The defining property of `mu` is the division bracketing
`q * mu ≤ 2^k < q * (mu + 1)`, i.e. `mu = ⌊2^k / q⌋`
(`q_mul_mu_le` and `two_pow_lt_q_mul_mu_succ`).  From it we prove the
**standard Barrett quotient error bound**

```
x / q - 1 ≤ t ≤ x / q          (i.e.   barrettQuot_le  and  barrettQuot_ge).
```

* `barrettQuot_le` — the estimate never *overshoots*: `t ≤ x / q`.  Hence
  `barrett x = x - t*q ≥ x % q`.
* `barrettQuot_ge` — when the input is in range (`x < 2^k`), the estimate
  *undershoots* by at most one: `x / q ≤ t + 1`.  Hence
  `barrett x < x % q + 2q`, and in fact `barrett x ≤ x % q + q`.

Assembling the two bounds (`barrett_bounds`) gives the genuine Barrett-error
statement

```
x % q ≤ barrett x ∧ barrett x ≤ x % q + q.
```

The estimate is *tight*: `barrett x` can equal `x % q + q` exactly (the
quotient error is genuinely `1`, e.g. `q = 5`, `k = 6`, `x = 5`).  Consequently
`barrett x` reduces to `x % q` after **at most one** conditional subtraction of
`q` (`barrettCondsub_eq_mod`): the corrected value `barrettCondsub x` equals
`x % q` on the nose.

The bignum Barrett kernel (`MultiLimbKernel.barrettReduce`) is the concrete
instance; this file is the abstract ℕ correctness it rests on.
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

variable (q k : ℕ)

/-- The precomputed Barrett reciprocal `mu = 2^k / q` (truncating ℕ division). -/
def mu : ℕ := 2 ^ k / q

/-- The Barrett estimated quotient `t = (x * mu) / 2^k`. -/
def barrettQuot (x : ℕ) : ℕ := (x * mu q k) / 2 ^ k

/-- The Barrett estimated remainder (before the conditional subtract):
    `barrett x = x - t * q` where `t = barrettQuot x`. -/
def barrett (x : ℕ) : ℕ := x - barrettQuot q k x * q

/-- The condsub-corrected Barrett reduction: subtract `q` once more if the
    estimate is still `≥ q`. -/
def barrettCondsub (x : ℕ) : ℕ :=
  let r := barrett q k x
  if q ≤ r then r - q else r

/-! ## §1  The defining bracketing of `mu` -/

/-- Lower half of `mu = 2^k / q`: `q * mu ≤ 2^k`. -/
theorem q_mul_mu_le : q * mu q k ≤ 2 ^ k := by
  unfold mu
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (2 ^ k) q

/-- Upper half of `mu = 2^k / q`: `2^k < q * (mu + 1)`. -/
theorem two_pow_lt_q_mul_mu_succ (hq : 0 < q) : 2 ^ k < q * (mu q k + 1) := by
  unfold mu
  have h := Nat.div_add_mod (2 ^ k) q
  have hm := Nat.mod_lt (2 ^ k) hq
  nlinarith [h, hm]

/-! ## §2  The Barrett quotient error bound -/

/-- **Barrett never overshoots**: the estimated quotient is at most the true
    quotient, `t ≤ x / q`.  Hence `barrett x = x - t*q ≥ x % q`. -/
theorem barrettQuot_le (hq : 0 < q) (hk : q ≤ 2 ^ k) (x : ℕ) :
    barrettQuot q k x ≤ x / q := by
  have hmu : 0 < mu q k := by
    have : 0 < 2 ^ k / q := Nat.div_pos hk (by positivity)
    simpa [mu] using this
  -- `t * 2^k ≤ x * mu` from the floor, and `q * mu ≤ 2^k`.
  have h1 : barrettQuot q k x * 2 ^ k ≤ x * mu q k := by
    rw [barrettQuot]; exact Nat.div_mul_le_self (x * mu q k) (2 ^ k)
  have h2 : q * mu q k ≤ 2 ^ k := q_mul_mu_le q k
  -- chain: `t * q * mu ≤ t * 2^k ≤ x * mu`, then cancel `mu`.
  have h3 : barrettQuot q k x * q * mu q k ≤ x * mu q k := by
    calc barrettQuot q k x * q * mu q k
        = barrettQuot q k x * (q * mu q k) := by ring
      _ ≤ barrettQuot q k x * 2 ^ k := Nat.mul_le_mul_left _ h2
      _ ≤ x * mu q k := h1
  exact (Nat.le_div_iff_mul_le hq).mpr (Nat.le_of_mul_le_mul_right h3 hmu)

/-- **Barrett undershoots by at most one**: when the input is in range
    (`x < 2^k`), the estimated quotient is at least `x/q - 1`, equivalently
    `x / q ≤ t + 1`.  Hence `barrett x = x - t*q < x % q + 2q`. -/
theorem barrettQuot_ge (hq : 0 < q) (x : ℕ) (hx : x < 2 ^ k) :
    x / q ≤ barrettQuot q k x + 1 := by
  have hP : 0 < (2 : ℕ) ^ k := by positivity
  -- It suffices to show `x < (t + 2) * q`; equivalently the error is `≤ 2`,
  -- which together with `x / q ≤ t + 1 ⟺ x < (t + 2) * q` is the claim.
  have key : x < (barrettQuot q k x + 2) * q := by
    -- Exact division decompositions:
    --   `2^k = q*mu + (2^k % q)`,  `x*mu = 2^k*t + (x*mu % 2^k)`.
    have hmu : q * mu q k + 2 ^ k % q = 2 ^ k := Nat.div_add_mod (2 ^ k) q
    have hr2 : 2 ^ k % q < q := Nat.mod_lt _ hq
    have ht : 2 ^ k * barrettQuot q k x + (x * mu q k) % 2 ^ k = x * mu q k := by
      simpa [barrettQuot] using Nat.div_add_mod (x * mu q k) (2 ^ k)
    have hrx : (x * mu q k) % 2 ^ k < 2 ^ k := Nat.mod_lt _ hP
    -- The two "carry" products are each `< q * 2^k`:
    have p1 : q * ((x * mu q k) % 2 ^ k) < q * 2 ^ k := (Nat.mul_lt_mul_left hq).2 hrx
    have p2 : x * (2 ^ k % q) < 2 ^ k * q := by
      have hle : x * (2 ^ k % q) ≤ (2 ^ k - 1) * (q - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith [hle, hP, hq]
    -- `x * 2^k = t*q*2^k + q*rx + x*r2 < (t + 2) * q * 2^k`.
    have hlt : x * 2 ^ k < (barrettQuot q k x + 2) * q * 2 ^ k := by
      nlinarith [hmu, ht, p1, p2]
    exact lt_of_mul_lt_mul_right hlt (Nat.zero_le (2 ^ k))
  have hdiv : x / q < barrettQuot q k x + 2 := by
    rw [Nat.div_lt_iff_lt_mul hq]
    linarith [key, mul_comm (barrettQuot q k x + 2) q]
  omega

/-! ## §3  The Barrett-error bound and the corrected reduction -/

/-- **Barrett error bound** (the genuine Barrett correctness statement): the
    pre-condsub estimate satisfies `x % q ≤ barrett x ≤ x % q + q`.  In words,
    `barrett x` is congruent to `x` modulo `q` and overshoots the true residue
    by at most one multiple of `q`.  The upper endpoint is attained, so this is
    tight. -/
theorem barrett_bounds (hq : 0 < q) (hk : q ≤ 2 ^ k) (x : ℕ) (hx : x < 2 ^ k) :
    x % q ≤ barrett q k x ∧ barrett q k x ≤ x % q + q := by
  have hle := barrettQuot_le q k hq hk x
  have hge := barrettQuot_ge q k hq x hx
  have hxq : q * (x / q) + x % q = x := Nat.div_add_mod x q
  -- bracket `t * q` between `(x/q - 1)*q` and `(x/q)*q`, normalised to `q * _`.
  have e1 : barrettQuot q k x * q ≤ (x / q) * q := Nat.mul_le_mul_right _ hle
  have e2 : (x / q) * q ≤ (barrettQuot q k x + 1) * q := Nat.mul_le_mul_right _ hge
  have c1 : (x / q) * q = q * (x / q) := by ring
  have c2 : (barrettQuot q k x + 1) * q = barrettQuot q k x * q + q := by ring
  have hbx : barrettQuot q k x * q ≤ x := by
    have := Nat.div_mul_le_self x q; omega
  simp only [barrett]
  refine ⟨by omega, by omega⟩

/-- **Corrected reduction is exact**: at most one conditional subtraction of `q`
    turns the Barrett estimate into the true residue, `barrettCondsub x = x % q`.

    The proof pins `barrett x` (which is `≡ x (mod q)` and lies in the length-`q`
    window `[x % q, x % q + q]`) to one of its two endpoints `x % q` or
    `x % q + q`; the conditional subtract collapses both to `x % q`. -/
theorem barrettCondsub_eq_mod (hq : 0 < q) (hk : q ≤ 2 ^ k) (x : ℕ)
    (hx : x < 2 ^ k) : barrettCondsub q k x = x % q := by
  obtain ⟨_hb1, hb2⟩ := barrett_bounds q k hq hk x hx
  have hmodlt : x % q < q := Nat.mod_lt _ hq
  have hbx : barrettQuot q k x * q ≤ x := by
    have hle := barrettQuot_le q k hq hk x
    calc barrettQuot q k x * q ≤ (x / q) * q := Nat.mul_le_mul_right _ hle
      _ ≤ x := Nat.div_mul_le_self x q
  -- `barrett x ≡ x (mod q)`, via `barrett x + t*q = x`.
  have hcong : barrett q k x % q = x % q := by
    have hrec : barrett q k x + barrettQuot q k x * q = x := by
      simp only [barrett]; omega
    calc barrett q k x % q
        = (barrett q k x + barrettQuot q k x * q) % q := by
            rw [Nat.add_mul_mod_self_right]
      _ = x % q := by rw [hrec]
  -- the window `[x%q, x%q+q]` meets the residue class `x % q` only at its ends.
  have hdvd : barrett q k x = x % q ∨ barrett q k x = x % q + q := by
    rcases Nat.lt_or_ge (barrett q k x) q with h | h
    · left
      have := Nat.mod_eq_of_lt h; omega
    · right
      have hbq : barrett q k x - q < q := by omega
      have h1 : (barrett q k x - q) % q = barrett q k x - q := Nat.mod_eq_of_lt hbq
      have h2 : (barrett q k x - q) % q = barrett q k x % q := by
        conv_rhs => rw [show barrett q k x = (barrett q k x - q) + q by omega]
        rw [Nat.add_mod_right]
      omega
  unfold barrettCondsub
  simp only
  rcases hdvd with h | h <;> rw [h] <;> split <;> omega

end CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric
