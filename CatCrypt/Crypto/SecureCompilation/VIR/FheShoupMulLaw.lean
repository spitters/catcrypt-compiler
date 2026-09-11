/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Shoup precomputed-twiddle modmul law for a 60-bit FHE NTT butterfly

This is the load-bearing correctness law for OpenFHE's actual NTT butterfly
modular multiply: the **Shoup** (Barrett-with-precomputed-quotient) modmul for a
*fixed* twiddle `b`. It is faster than the generic Montgomery REDC of
`FheMontMulLaw.lean` because the per-twiddle quotient `b' = ⌊b·R/q⌋` is
precomputed once, eliminating the `qinv` multiply inside the inner loop.

We model the emittable single-word Shoup multiply at the 60-bit prime
`q = 1152921504606830593` with radix `R = 2^64`:
```
  b' := ⌊b·R / q⌋                  -- precomputed constant for the twiddle b
  q̂  := ⌊a·b' / R⌋                 -- quotient estimate (high word of a·b')
  t  := a·b − q̂·q                  -- t ∈ [0, 2q)
  shoupMul a b := if t ≥ q then t − q else t
```

All reasoning is over `Nat` (the cleanest layer), mirroring `FheMontMulLaw.lean`
and the Barrett bound of `Plonky3BarrettLaw.lean`. The estimate is bounded into
`[0, 2q)`, then a single conditional subtract canonicalises it into `[0, q)`.

## The Shoup quotient bound (`q̂·q ≤ a·b < q̂·q + 2q`)

Write `b·R = b'·q + r_b` (`r_b = b·R mod q < q`) and `a·b' = q̂·R + r₁`
(`r₁ = a·b' mod R < R`). Then
```
  q̂·q·R = (a·b' − r₁)·q = a·(b'·q) − r₁·q = a·(b·R − r_b) − r₁·q
         = a·b·R − a·r_b − r₁·q,
```
so the estimate `t = a·b − q̂·q` satisfies the exact identity
```
  t·R = a·r_b + r₁·q.                                     (†)
```
From (†): `t·R ≥ 0` so `q̂·q ≤ a·b`; and with `a < q`, `r_b < q`, `r₁ < R`,
```
  t·R = a·r_b + r₁·q < q·q + R·q = q·(q + R) < q·(2R) = 2q·R   (since q < R),
```
so `t < 2q` and one conditional subtract canonicalises. The headline result is
`shoupMul_correct : shoupMul a b = (a · b) % q` for `a, b < q`, the function a
GMP KAT checks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FheShoupMulLaw

/-- The 60-bit FHE prime `q = 1152921504606830593`. -/
def fheQ : Nat := 1152921504606830593

/-- The Shoup radix `R = 2^64`. -/
def fheR : Nat := 18446744073709551616

/-! ### Constant-verification lemmas (all `by norm_num`, no `native_decide`) -/

theorem fheR_eq : fheR = 2 ^ 64 := by norm_num [fheR]

theorem fheQ_pos : 0 < fheQ := by norm_num [fheQ]

theorem fheR_pos : 0 < fheR := by norm_num [fheR]

/-- `q < R` (the 60-bit prime fits strictly below the 64-bit radix). -/
theorem fheQ_lt_fheR : fheQ < fheR := by norm_num [fheQ, fheR]

/-! ### Shoup precomputed twiddle and the modmul -/

/-- The precomputed Shoup constant for a fixed twiddle `b`: `b' = ⌊b·R / q⌋`. -/
def fheShoupConst (b : Nat) : Nat := b * fheR / fheQ

/-- **The emitted Shoup modmul sequence** for a fixed twiddle `b` with
    precomputed `b' = fheShoupConst b`: the quotient estimate `q̂ = ⌊a·b'/R⌋`
    (high word of `a·b'`), the estimate `t = a·b − q̂·q ∈ [0, 2q)`, then one
    conditional subtract canonicalises into `[0, q)`. -/
def shoupMul (a b : Nat) : Nat :=
  let qhat := a * (fheShoupConst b) / fheR
  let t := a * b - qhat * fheQ
  if t ≥ fheQ then t - fheQ else t

/-- The Shoup quotient estimate `q̂ = ⌊a·b'/R⌋`, named for reuse. -/
def shoupQ (a b : Nat) : Nat := a * (fheShoupConst b) / fheR

/-- **The exact Shoup identity (†):** `(a·b − q̂·q)·R = a·r_b + r₁·q`, where
    `r_b = b·R mod q` and `r₁ = a·b' mod R`. Equivalently, multiplying through,
    `a·b·R = q̂·q·R + a·r_b + r₁·q`. This is the heart of the bound. -/
theorem shoup_identity (a b : Nat) :
    a * b * fheR
      = (shoupQ a b) * fheQ * fheR
        + (a * (b * fheR % fheQ) + (a * fheShoupConst b % fheR) * fheQ) := by
  -- `b·R = b'·q + r_b`
  have hb : fheShoupConst b * fheQ + b * fheR % fheQ = b * fheR := by
    rw [fheShoupConst, Nat.div_add_mod' (b * fheR) fheQ]
  -- `a·b' = q̂·R + r₁`
  have ha : (shoupQ a b) * fheR + a * fheShoupConst b % fheR = a * fheShoupConst b := by
    rw [shoupQ, Nat.div_add_mod' (a * fheShoupConst b) fheR]
  -- `a·b·R = a·(b'·q + r_b) = a·b'·q + a·r_b = (q̂·R + r₁)·q + a·r_b`
  calc a * b * fheR
      = a * (b * fheR) := by ring
    _ = a * (fheShoupConst b * fheQ + b * fheR % fheQ) := by rw [hb]
    _ = (a * fheShoupConst b) * fheQ + a * (b * fheR % fheQ) := by ring
    _ = ((shoupQ a b) * fheR + a * fheShoupConst b % fheR) * fheQ
          + a * (b * fheR % fheQ) := by rw [ha]
    _ = (shoupQ a b) * fheQ * fheR
          + (a * (b * fheR % fheQ) + (a * fheShoupConst b % fheR) * fheQ) := by ring

/-- **The Shoup quotient never overshoots:** `q̂·q ≤ a·b`, so `t = a·b − q̂·q ≥ 0`.
    Immediate from (†): the remainder term `a·r_b + r₁·q ≥ 0`. -/
theorem shoup_q_mul_q_le (a b : Nat) : (shoupQ a b) * fheQ ≤ a * b := by
  have hid := shoup_identity a b
  -- `q̂·q·R ≤ a·b·R`, then cancel `R`.
  have hR : (shoupQ a b) * fheQ * fheR ≤ a * b * fheR := by omega
  have h2 : (shoupQ a b) * fheQ * fheR ≤ (a * b) * fheR := by
    have he : a * b * fheR = (a * b) * fheR := by ring
    omega
  exact Nat.le_of_mul_le_mul_right h2 fheR_pos

/-- **The Shoup estimate undershoots by less than `2q`:** `a·b < q̂·q + 2q`.
    From (†): `t·R = a·r_b + r₁·q < q·q + R·q = q·(q + R) < q·(2R) = 2q·R`
    (using `a < q`, `r_b < q`, `r₁ < R`, `q < R`), so `t < 2q`. -/
theorem shoup_lt (a b : Nat) (ha : a < fheQ) :
    a * b < (shoupQ a b) * fheQ + 2 * fheQ := by
  have hid := shoup_identity a b
  -- bounds on the two remainder pieces
  have hrb : b * fheR % fheQ < fheQ := Nat.mod_lt _ fheQ_pos
  have hr1 : a * fheShoupConst b % fheR < fheR := Nat.mod_lt _ fheR_pos
  -- `a·r_b < q·q`
  have hpart1 : a * (b * fheR % fheQ) < fheQ * fheQ :=
    Nat.mul_lt_mul'' ha hrb
  -- `r₁·q < R·q`
  have hpart2 : (a * fheShoupConst b % fheR) * fheQ < fheR * fheQ :=
    mul_lt_mul_of_pos_right hr1 fheQ_pos
  -- remainder `< q·q + R·q = q·(q+R) < q·2R = 2q·R`
  have hsum : a * (b * fheR % fheQ) + (a * fheShoupConst b % fheR) * fheQ
      < fheQ * fheQ + fheR * fheQ := by omega
  have hbound : fheQ * fheQ + fheR * fheQ < 2 * fheQ * fheR := by
    have hqR := fheQ_lt_fheR
    -- q*q + R*q < R*q + R*q = 2*R*q = 2*q*R
    have h1 : fheQ * fheQ < fheR * fheQ := mul_lt_mul_of_pos_right hqR fheQ_pos
    have he : 2 * fheQ * fheR = fheR * fheQ + fheR * fheQ := by ring
    omega
  -- so `a·b·R < q̂·q·R + 2q·R`, cancel `R`
  have hltR : a * b * fheR < (shoupQ a b) * fheQ * fheR + 2 * fheQ * fheR := by
    omega
  -- regroup into `(… ) * R` form and cancel
  have hltR' : (a * b) * fheR < ((shoupQ a b) * fheQ + 2 * fheQ) * fheR := by
    have he1 : a * b * fheR = (a * b) * fheR := by ring
    have he2 : ((shoupQ a b) * fheQ + 2 * fheQ) * fheR
        = (shoupQ a b) * fheQ * fheR + 2 * fheQ * fheR := by ring
    rw [he2]; rw [he1] at hltR; exact hltR
  exact Nat.lt_of_mul_lt_mul_right hltR'

/-- **`shoupMul` is the field product.** For `a, b < q`,
    `shoupMul a b = (a · b) % q`.

    The quotient estimate `q̂` satisfies `q̂·q ≤ a·b < q̂·q + 2q`
    (`shoup_q_mul_q_le`, `shoup_lt`), so `t = a·b − q̂·q ∈ [0, 2q)` and the single
    conditional subtract canonicalises it into `[0, q)`. Since the canonical
    value is `< q` and congruent to `a·b` mod `q`, it equals `(a·b) % q`. -/
theorem shoupMul_correct (a b : Nat) (ha : a < fheQ) (_hb : b < fheQ) :
    shoupMul a b = (a * b) % fheQ := by
  have hle := shoup_q_mul_q_le a b
  have hlt := shoup_lt a b ha
  -- `shoupMul a b = if t ≥ q then t − q else t`, with `t = a·b − q̂·q`.
  show (if a * b - (shoupQ a b) * fheQ ≥ fheQ
        then (a * b - (shoupQ a b) * fheQ) - fheQ
        else a * b - (shoupQ a b) * fheQ) = (a * b) % fheQ
  set t := a * b - (shoupQ a b) * fheQ with htdef
  -- `t ∈ [0, 2q)` and `a·b = q̂·q + t`
  have htval : a * b = (shoupQ a b) * fheQ + t := by omega
  have ht2q : t < 2 * fheQ := by omega
  -- rewrite `a·b = q̂·q + t` on the RHS so the residue reads off the estimate.
  rw [htval]
  -- the canonical residue, branchwise; both branches `< q` and `≡ a·b (mod q)`.
  split
  · -- t ≥ q: result is `t − q`, and `(q̂·q + t) % q = t % q = t − q`.
    rename_i hge
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  · -- t < q: result is `t`, and `(q̂·q + t) % q = t`.
    rename_i hlt_q'
    have hlt_q : t < fheQ := by omega
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlt_q]

end CatCrypt.Crypto.SecureCompilation.VIR.FheShoupMulLaw
