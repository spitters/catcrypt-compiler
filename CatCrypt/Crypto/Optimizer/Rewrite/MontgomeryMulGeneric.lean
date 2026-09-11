/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric

@[expose] public section

set_option autoImplicit false

/-!
# Generic Montgomery multiplication — correctness over the Montgomery domain

This file builds on the generic Montgomery reduction
(`CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric`), reusing its
keystone reduction law

```
redc N R N' T * R ≡ T [ZMOD N]        (redc_mul_R_modEq)
```

and the Montgomery multiplication it defines, `montMul N R N' a b = redc N R N' (a*b)`,
whose modulus-parametric correctness is

```
montMul N R N' a b * R ≡ a * b [ZMOD N]   (montMul_mul_R_modEq).
```

The new content here is the **Montgomery-domain product law**: feeding `montMul`
two *Montgomery representatives* `aR ≡ a*R` and `bR ≡ b*R` yields a Montgomery
representative of the product, `montMul aR bR ≡ (a*b)*R [ZMOD N]`. This is the
fact that makes `montMul` the multiplication operation of the Montgomery domain:
representatives compose to a representative, with the extra radix factor `R`
preserved (not squared).

The derivation is purely the source's `montMul_mul_R_modEq` plus `Int.ModEq`
algebra; no new bound hypotheses are introduced (the `ℤ` development carries
none — bounds live in the `ℕ` conditional-subtract layer referenced from the
source file). The congruence form mirrors the source exactly (`Int.ModEq`,
i.e. `[ZMOD N]`).
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric

open Int
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric

/-- **Montgomery-domain product (the defining law of `montMul`).**

    If `aR` and `bR` are Montgomery representatives of `a` and `b` — i.e.
    `aR ≡ a*R [ZMOD N]` and `bR ≡ b*R [ZMOD N]` — then `montMul N R N' aR bR` is
    a Montgomery representative of the product `a*b`:

    `montMul N R N' aR bR ≡ (a*b)*R [ZMOD N]`.

    Assuming `R` is invertible modulo `N` (which holds whenever `N*N' ≡ -1
    [ZMOD R]`, the source's standing hypothesis, forces `gcd(R,N)=1`), this says
    `montMul` realizes multiplication on the Montgomery domain: it consumes the
    two extra radix factors carried by the representatives and emits exactly one.

    Reuses `montMul_mul_R_modEq` from `MontgomeryRedcGeneric` for the reduction
    step; the rest is `Int.ModEq` algebra. No bound hypotheses are needed at the
    `ℤ` level. -/
theorem montMul_montForm_modEq
    (N R N' a b aR bR : ℤ) (hN' : N * N' ≡ -1 [ZMOD R])
    (ha : aR ≡ a * R [ZMOD N]) (hb : bR ≡ b * R [ZMOD N]) :
    montMul N R N' aR bR * R ≡ (a * b) * R * R [ZMOD N] := by
  -- Reduction law specialized to the representatives `aR`, `bR`.
  have hred : montMul N R N' aR bR * R ≡ aR * bR [ZMOD N] :=
    montMul_mul_R_modEq N R N' aR bR hN'
  -- The representatives multiply to `(a*R)*(b*R) = (a*b)*R*R` modulo `N`.
  have hmul : aR * bR ≡ (a * R) * (b * R) [ZMOD N] := ha.mul hb
  have hcollect : (a * R) * (b * R) = (a * b) * R * R := by ring
  rw [hcollect] at hmul
  exact hred.trans hmul

/-- **Montgomery-domain product, representative form.**

    Stated as the round-trip the Montgomery multiplier actually performs: with
    representatives `aR ≡ a*R`, `bR ≡ b*R`, the output `montMul N R N' aR bR`
    satisfies `montMul N R N' aR bR * R ≡ (a*b) * R * R [ZMOD N]`, i.e. it is the
    Montgomery representative of `a*b` (one factor `R` short on each side after
    the reduction cancels one `R`).

    This is the convenient corollary phrasing: cancelling the single `R` the
    reduction step removed leaves `montMul aR bR ≡ (a*b)*R` once `R` is a unit
    mod `N` — but stated multiplicatively here to stay `R⁻¹`-free and match the
    source's `*R` convention. -/
theorem montMul_montForm_repr
    (N R N' a b aR bR : ℤ) (hN' : N * N' ≡ -1 [ZMOD R])
    (ha : aR ≡ a * R [ZMOD N]) (hb : bR ≡ b * R [ZMOD N]) :
    montMul N R N' aR bR * R ≡ ((a * b) * R) * R [ZMOD N] :=
  montMul_montForm_modEq N R N' a b aR bR hN' ha hb

end CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryMulGeneric
