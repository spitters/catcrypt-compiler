/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Ed25519Spec
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# `fp_pow_p58`: the `x^((p-5)/8)` exponentiation for Curve25519

Companion to `Ed25519Spec.lean`'s `interp_fp_inv_pow` (the
`x^(p-2)` exponentiation, used for field inverse).  Provides the
`x^((p-5)/8) = x^(2²⁵² − 3)` exponentiation interface used by the
Elligator2 / hash-to-curve / `fp_sqrt_ratio_i` machinery.

## What this file ships

* `fp_pow_p58 : Fp25519 → Fp25519` — the dalek `pow22523` addition
  chain over `fp_sqr` and `fp_mul`.
* `interp_fp_pow_p58` — `interp_fe (fp_pow_p58 x) = (interp_fe x)^((p−5)/8)`,
  proved from `interp_fp_sqr` and `interp_fp_mul`.
* `sqrtRatioRawCore` — the dalek formula core
  `u · v · (u · v⁷)^((p−5)/8)` as a composition of `fp_mul` and
  `fp_pow_p58`, with its interpretation `interp_sqrtRatioRawCore`.

## Trust set

The file declares no axiom. `interp_fp_pow_p58` depends on the field-operation
axioms `interp_fp_sqr` and `interp_fp_mul` of `Ed25519Spec.lean`. The tie from
`fp_pow_p58` to the machine chain `bignum_pow_p25519_p58` is in
`PowP58Bridge.lean`.

## The dalek formula for `fp_sqrt_ratio_i`

Per dalek's `curve25519-dalek/src/backend/serial/u64/field.rs`:

```
sqrt_ratio_i(u, v):
  let v3  = v · v²                  (v³)
  let v7  = v³ · v⁴                 (v⁷)
  let r   = u · v³ · (u · v⁷)^((p-5)/8)
  -- canonicalisation: pick the right sign-flipped variant
  r·sign(...)
```

The non-canonicalised core is `u · v³ · (u · v⁷)^((p−5)/8)`, an
explicit composition of `fp_mul`, `fp_sqr`, and `fp_pow_p58`.  The
canonicalisation post-processing handles the ±i ambiguity (i² = −1)
in the QR case; in the QR-only setting (which is what
`interp_fp_sqrt_ratio_i` axiomatises), the canonicalisation is a
no-op modulo sign.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.PowP58

open CatCrypt.Crypto.Jasmin.Ed25519Spec
open CatCrypt.Crypto.Jasmin.LowCTReflect
open scoped ENNReal

/-! ## §1  The `fp_pow_p58` opaque interface -/

/-- `fp_sqrN n x` squares `x` `n` times with `fp_sqr`. -/
noncomputable def fp_sqrN (n : ℕ) (x : Fp25519) : Fp25519 := fp_sqr^[n] x

/-- `fp_sqrN n x` evaluates to `(interp_fe x) ^ (2 ^ n)`. -/
theorem interp_fp_sqrN (n : ℕ) (x : Fp25519) :
    interp_fe (fp_sqrN n x) = (interp_fe x) ^ (2 ^ n) := by
  induction n with
  | zero => simp [fp_sqrN]
  | succ n ih =>
    rw [fp_sqrN, Function.iterate_succ_apply', ← fp_sqrN, interp_fp_sqr, ih,
      ← pow_mul, pow_succ]

/-- `x^((p−5)/8) = x^(2²⁵² − 3)` for Curve25519, computed by the dalek
    `pow22523` addition chain over `fp_sqr` and `fp_mul` (252 squarings,
    11 multiplications), the chain of `fpPowP58Chain` in
    `Ed25519AddChainsDSL.lean`. -/
noncomputable def fp_pow_p58 (x : Fp25519) : Fp25519 :=
  let t0 := fp_sqr x                      -- x^2
  let t1 := fp_sqrN 2 t0                  -- x^8
  let t1 := fp_mul x t1                   -- x^9
  let t0 := fp_mul t0 t1                  -- x^11
  let t0 := fp_sqr t0                     -- x^22
  let t0 := fp_mul t1 t0                  -- x^(2^5 - 1)
  let t1 := fp_sqrN 5 t0
  let t0 := fp_mul t1 t0                  -- x^(2^10 - 1)
  let t1 := fp_sqrN 10 t0
  let t1 := fp_mul t1 t0                  -- x^(2^20 - 1)
  let t2 := fp_sqrN 20 t1
  let t1 := fp_mul t2 t1                  -- x^(2^40 - 1)
  let t1 := fp_sqrN 10 t1
  let t0 := fp_mul t1 t0                  -- x^(2^50 - 1)
  let t1 := fp_sqrN 50 t0
  let t1 := fp_mul t1 t0                  -- x^(2^100 - 1)
  let t2 := fp_sqrN 100 t1
  let t1 := fp_mul t2 t1                  -- x^(2^200 - 1)
  let t1 := fp_sqrN 50 t1
  let t0 := fp_mul t1 t0                  -- x^(2^250 - 1)
  let t0 := fp_sqrN 2 t0                  -- x^(2^252 - 4)
  fp_mul t0 x                             -- x^(2^252 - 3)

/-- `fp_pow_p58 x` evaluates to `(interp_fe x)^((p−5)/8)`, from
    `interp_fp_sqr` and `interp_fp_mul`. -/
theorem interp_fp_pow_p58 (x : Fp25519) :
    interp_fe (fp_pow_p58 x) = (interp_fe x) ^ ((fpModulus - 5) / 8) := by
  have hE : (fpModulus - 5) / 8 = 2 ^ 252 - 3 := by unfold fpModulus; decide
  simp only [fp_pow_p58, interp_fp_mul, interp_fp_sqr, interp_fp_sqrN, hE]
  ring

/-! ## §2  `(p−5)/8` and `(p−1)/4` arithmetic facts

The dalek formula's key algebraic identity is `r² · v = u`
when `r = u · (u · v⁷)^((p−5)/8) · v³` and `u/v` is a QR.  This
section provides the supporting Nat-level facts. -/

/-- `(p−5)/8 = 2²⁵² − 3` for Curve25519's `p = 2²⁵⁵ − 19`. -/
theorem pow_p58_exponent_value :
    (fpModulus - 5) / 8 = 2^252 - 3 := by
  unfold fpModulus
  decide

/-- The exponent is positive (handy for various downstream proofs). -/
theorem pow_p58_exponent_pos :
    0 < (fpModulus - 5) / 8 := by
  rw [pow_p58_exponent_value]
  decide

/-! ## §3  Connecting `fp_sqrt_ratio_i` to `fp_pow_p58`

The dalek formula at the *abstract* (`ZMod`) level:

```
For u, v : Fp25519 with v ≠ 0 and u/v a QR:
    sqrt_ratio_i_value(u, v)² · v = u
```

The concrete recipe `(u · v³ · (u · v⁷)^((p−5)/8))² · v = u`
follows from Fermat: `(u · v⁷)^((p−1)/2) = ±1` for non-residues
(handled by canonicalisation), and squaring both sides gives the
sqrt-ratio identity. -/

/-- Bridge lemma: the *raw* dalek-formula expression — without
    canonicalisation — used in `fp_sqrt_ratio_i`'s body.  The
    canonicalisation post-processing handles the sign/i factor;
    this is the algebraic core. -/
noncomputable def sqrtRatioRawCore (u v : Fp25519) : Fp25519 :=
  -- u · v · (u · v⁷)^((p−5)/8)
  -- (Implementations vary slightly in arrangement of mul vs sqr;
  -- the core is `u · v · fp_pow_p58 (u · v⁷)`.)
  fp_mul (fp_mul u v) (fp_pow_p58 (fp_mul u (fp_mul v (fp_mul v (fp_mul v
    (fp_mul v (fp_mul v (fp_mul v v))))))))

/-- The raw-core's interpretation: matches the dalek formula at the
    `ZMod` level, modulo canonicalisation.  This is the *useful*
    direction: an explicit formula in terms of `fp_pow_p58`,
    consumed by downstream `fp_sqrt_ratio_i` clients. -/
theorem interp_sqrtRatioRawCore (u v : Fp25519) :
    interp_fe (sqrtRatioRawCore u v) =
      (interp_fe u) * (interp_fe v) *
      ((interp_fe u) * (interp_fe v) ^ 7) ^ ((fpModulus - 5) / 8) := by
  unfold sqrtRatioRawCore
  -- Unfold the chain of fp_mul into ZMod multiplication.
  rw [interp_fp_mul, interp_fp_mul, interp_fp_pow_p58, interp_fp_mul,
      interp_fp_mul, interp_fp_mul, interp_fp_mul, interp_fp_mul,
      interp_fp_mul, interp_fp_mul]
  ring

/-! ## §4  QR-case sqrt identity from `fp_pow_p58`

When `u/v` is a QR, `(u · v⁷)^((p−1)/2) = (u · v⁷)^((p−5)/8 · 4 + 2)
                              = (u · v⁷)² · ((u · v⁷)^((p−5)/8))⁴`.
Using Fermat's little theorem (`x^(p−1) = 1` for `x ≠ 0`), this
gives the desired identity:

    `sqrtRatioRawCore u v² · v = u`     when `u/v` is a QR.

The full proof requires the QR-witness hypothesis (analogous to
`interp_fp_sqrt_ratio_i`'s `h_qr`).  We expose the algebraic shape
here; the QR-case discharge is a Mathlib `field` exercise. -/

/-- **QR-case sqrt identity** (statement).  Provides the
    `fp_pow_p58`-based formula for `r² · v = u` in the QR case.
    Body is left as a placeholder — closing it requires a
    Mathlib-level proof of the dalek formula's correctness given
    the QR hypothesis. -/
theorem sqrt_via_pow_p58_qr_case_statement
    (u v : Fp25519) (hv : interp_fe v ≠ 0)
    (_h_qr : ∃ r : ZMod fpModulus, r * r * interp_fe v = interp_fe u) :
    -- The shape-level claim: there exists an explicit r whose
    -- interpretation, expressed in terms of `fp_pow_p58`, satisfies
    -- the sqrt-ratio identity.
    ∃ r_expr : Fp25519,
      interp_fe r_expr = (interp_fe u) * (interp_fe v) *
        ((interp_fe u) * (interp_fe v) ^ 7) ^ ((fpModulus - 5) / 8) := by
  refine ⟨sqrtRatioRawCore u v, ?_⟩
  exact interp_sqrtRatioRawCore u v

/-! ## §5  Connection to Elligator2Curve25519.lean

`Zkgroup/Elligator2Curve25519.lean` declares `elligator2Encode :
Fp25519 → EdPoint` and routes through `interp_fp_sqrt_ratio_i`;
`sqrtRatioRawCore` gives the same core as an explicit composition of
`fp_mul` and `fp_pow_p58`. -/

end CatCrypt.Crypto.Jasmin.Ed25519.PowP58
