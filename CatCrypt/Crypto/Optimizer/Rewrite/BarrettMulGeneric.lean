/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

@[expose] public section

set_option autoImplicit false

/-!
# Barrett-based modular multiplication — the ℕ correctness core

Building on the generic Barrett reduction
(`CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric`), this file defines
**Barrett modular multiplication**

```
barrettModMul a b = barrettCondsub (a * b)
```

— the workhorse of constant-time modular exponentiation and NTT butterflies —
and proves it computes the true modular product `(a * b) % q`.

The reduction core (`barrettCondsub_eq_mod`) requires its input to lie in the
range `x < 2 ^ k`.  For the product `a * b` of two canonical residues
`a, b < q` we have `a * b < q ^ 2`, so the range hypothesis is met precisely
when the Barrett shift is sized for products, `q ^ 2 ≤ 2 ^ k`.  This is the
standard sizing condition for a Barrett **modmul** (as opposed to a single
reduction, which only needs `x < 2 ^ k`); we thread it as an explicit
hypothesis `hkk : q ^ 2 ≤ 2 ^ k`.

* `barrettModMul_eq_mod` — `barrettModMul a b = (a * b) % q`, the correctness
  statement, under `0 < q`, `q ^ 2 ≤ 2 ^ k`, `a < q`, `b < q`.
* `barrettModMul_lt` — `barrettModMul a b < q`, the canonical-representative
  bound that lets Barrett modmuls chain.
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.BarrettMulGeneric

open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

variable (q k : ℕ)

/-- Barrett modular multiplication: reduce the integer product `a * b` with the
    condsub-corrected Barrett reduction.  Correct when `a, b < q` and the shift
    is sized for products (`q ^ 2 ≤ 2 ^ k`). -/
def barrettModMul (a b : ℕ) : ℕ := barrettCondsub q k (a * b)

/-- The Barrett shift, sized for products (`q ^ 2 ≤ 2 ^ k`), also dominates a
    single modulus (`q ≤ 2 ^ k`).  Auxiliary for discharging the reduction
    core's `hk` hypothesis. -/
theorem q_le_two_pow (hq : 0 < q) (hkk : q ^ 2 ≤ 2 ^ k) : q ≤ 2 ^ k := by
  calc q ≤ q ^ 2 := by nlinarith [hq]
    _ ≤ 2 ^ k := hkk

/-- The product of two canonical residues is in Barrett range: from `a < q` and
    `b < q` and the product sizing `q ^ 2 ≤ 2 ^ k` we get `a * b < 2 ^ k`. -/
theorem mul_lt_two_pow (hkk : q ^ 2 ≤ 2 ^ k) {a b : ℕ} (ha : a < q) (hb : b < q) :
    a * b < 2 ^ k := by
  have hab : a * b < q ^ 2 := by
    have : a * b < q * q := Nat.mul_lt_mul'' ha hb
    nlinarith [this]
  exact lt_of_lt_of_le hab hkk

/-- **Barrett modmul is exact**: for canonical residues `a, b < q` and a shift
    sized for products (`q ^ 2 ≤ 2 ^ k`), Barrett modular multiplication
    computes the true modular product, `barrettModMul a b = (a * b) % q`.

    This specialises the reduction core `barrettCondsub_eq_mod` to the input
    `a * b`, discharging its range hypothesis `a * b < 2 ^ k` from `a, b < q`
    via `mul_lt_two_pow`. -/
theorem barrettModMul_eq_mod (hq : 0 < q) (hkk : q ^ 2 ≤ 2 ^ k)
    {a b : ℕ} (ha : a < q) (hb : b < q) :
    barrettModMul q k a b = (a * b) % q := by
  unfold barrettModMul
  exact barrettCondsub_eq_mod q k hq (q_le_two_pow q k hq hkk) (a * b)
    (mul_lt_two_pow q k hkk ha hb)

/-- **Barrett modmul yields a canonical residue**: `barrettModMul a b < q`.
    This is the bound that lets Barrett modmuls chain (the output is again a
    canonical input to a subsequent modmul). -/
theorem barrettModMul_lt (hq : 0 < q) (hkk : q ^ 2 ≤ 2 ^ k)
    {a b : ℕ} (ha : a < q) (hb : b < q) :
    barrettModMul q k a b < q := by
  rw [barrettModMul_eq_mod q k hq hkk ha hb]
  exact Nat.mod_lt _ hq

end CatCrypt.Crypto.Optimizer.Rewrite.BarrettMulGeneric
