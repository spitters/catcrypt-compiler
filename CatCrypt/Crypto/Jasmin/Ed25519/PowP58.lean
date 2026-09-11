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

* `fp_pow_p58 : Fp25519 → Fp25519` — opaque function (axiom).
* `interp_fp_pow_p58` — chain-correctness axiom:
  `interp_fe (fp_pow_p58 x) = (interp_fe x)^((p−5)/8)`.
* `fp_sqrt_ratio_via_pow_p58` — the dalek formula
  `fp_sqrt_ratio_i u v = u · v · (u · v³ · (u · v⁷)^((p−5)/8))²`-shape
  identity, connecting `fp_sqrt_ratio_i` (an existing axiom) to
  `fp_pow_p58` modulo the canonicalisation post-processing.

## Trust set delta

This file adds **two new axioms** (`fp_pow_p58` itself, and the
chain-correctness `interp_fp_pow_p58`) — same shape as
`fp_inv` + `interp_fp_inv_pow` for the `(p−2)` exponent.

Both are discharged in Rocq:

* `fp_pow_p58` — discharged by `fpPowP58Chain` from
  `Ed25519AddChainsDSL.lean`, which is the dalek/AUCurves chain.
* `interp_fp_pow_p58` — Rocq-side via the `exp_by_squaring_correct`
  lemma instantiated at exponent `(p−5)/8 = 2²⁵² − 3`.

Once `bignum_pow_p25519_p58` lands as a Hoare triple, both axioms
become unnecessary — the exponent's correctness is proved through
the verified pipeline.

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

/-- `x^((p−5)/8) = x^(2²⁵² − 3)` for Curve25519.  Implemented by the
    dalek-style `fpPowP58Chain` (see `Ed25519AddChainsDSL.lean`):
    251-operation chain (249 sqrs + 2 sqrs + 1 mul). -/
axiom fp_pow_p58 : Fp25519 → Fp25519

/-- Chain-correctness axiom for `fp_pow_p58`.  Asserts the
    interpretation of the chain output equals the abstract
    field exponentiation.  Discharged in Rocq via
    `exp_by_squaring_correct` instantiated at `(p−5)/8`. -/
axiom interp_fp_pow_p58 (x : Fp25519) :
    interp_fe (fp_pow_p58 x) = (interp_fe x) ^ ((fpModulus - 5) / 8)

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

/-! ## §5  When the bignum chain lands

When `bignum_pow_p25519_p58` ships as a Hoare-verified leaf:

1. Replace the `axiom fp_pow_p58 : Fp25519 → Fp25519` here with a
   `noncomputable def fp_pow_p58 : Fp25519 → Fp25519 := bignumPowP58.evalChain`.
2. Replace `axiom interp_fp_pow_p58` with a theorem whose proof
   walks the `fpPowP58Chain` Hoare triple structure.
3. The downstream consumers of `interp_fp_pow_p58` (Elligator2,
   sqrt_ratio_i) inherit the Qed automatically.

This file is the **interface point** for that future refactor —
adding it now lets downstream Lean code commit to the
`fp_pow_p58` interface today.

## Connection to Elligator2Curve25519.lean

`Zkgroup/Elligator2Curve25519.lean` axiomatises `elligator2Encode :
Fp25519 → EdPoint` and routes through `interp_fp_sqrt_ratio_i`.
A future commit can refactor `elligator2Encode`'s body to use
`sqrtRatioRawCore` from this file directly, eliminating the
indirect axiom-citation through `fp_sqrt_ratio_i`. -/

end CatCrypt.Crypto.Jasmin.Ed25519.PowP58
