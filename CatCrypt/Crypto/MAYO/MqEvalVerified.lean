/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.Gf16
public import CatCrypt.Crypto.Util.Gf16

/-!
# Verified MAYO `mq_eval` over GF(16) at the oil dimension N=8

A pure-Lean reference computation of the MAYO public-map component

```
    P(s) = sᵀ A s = Σ_{i,k} s[i] · A[i][k] · s[k]    over GF(16)
```

at `N = 8` (the MAYO-1 oil dimension; matches the rustcmd leaf
`mayo_quadform_n8`).

This is the verified body that the `MayoHaxLowCTBridge` consults so
the bridge round-trip identities reduce to proven `rfl`-style facts over
the underlying `Gf16 := BitVec 4`, rather than opaque axioms on an
abstract `MayoScalar`.

## API

* `mqEvalN8 : Vector Gf16 8 → Vector Gf16 64 → Gf16` — the canonical
  `P(s) = sᵀ A s` computation at `N = 8`.

The matrix is stored row-major: `A[i][k] = mat.get (i*8 + k)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MAYO.MqEvalVerified

open CatCrypt.Util
open CatCrypt.Util.Gf16

/-- One inner-product accumulation term `s[i] * (Σ_k A[i][k] * s[k])`. -/
def innerRow (s : Vector Gf16 8) (mat : Vector Gf16 64) (i : Fin 8) : Gf16 :=
  let row_sum : Gf16 :=
    (mul (mat.get ⟨i.val * 8 + 0, by have := i.isLt; omega⟩) (s.get 0)) ^^^
    (mul (mat.get ⟨i.val * 8 + 1, by have := i.isLt; omega⟩) (s.get 1)) ^^^
    (mul (mat.get ⟨i.val * 8 + 2, by have := i.isLt; omega⟩) (s.get 2)) ^^^
    (mul (mat.get ⟨i.val * 8 + 3, by have := i.isLt; omega⟩) (s.get 3)) ^^^
    (mul (mat.get ⟨i.val * 8 + 4, by have := i.isLt; omega⟩) (s.get 4)) ^^^
    (mul (mat.get ⟨i.val * 8 + 5, by have := i.isLt; omega⟩) (s.get 5)) ^^^
    (mul (mat.get ⟨i.val * 8 + 6, by have := i.isLt; omega⟩) (s.get 6)) ^^^
    (mul (mat.get ⟨i.val * 8 + 7, by have := i.isLt; omega⟩) (s.get 7))
  mul (s.get i) row_sum

/-- MAYO public-map component `P(s) = sᵀ A s` at `N = 8`, over GF(16).

    The result is `Σ_i s[i] · (Σ_k A[i][k] · s[k])` with all arithmetic
    in GF(16) (XOR for addition, `Gf16.mul` for multiplication). -/
def mqEvalN8 (s : Vector Gf16 8) (mat : Vector Gf16 64) : Gf16 :=
  (innerRow s mat 0) ^^^
  (innerRow s mat 1) ^^^
  (innerRow s mat 2) ^^^
  (innerRow s mat 3) ^^^
  (innerRow s mat 4) ^^^
  (innerRow s mat 5) ^^^
  (innerRow s mat 6) ^^^
  (innerRow s mat 7)

/-! ## Sanity check: zero in, zero out -/

theorem mqEvalN8_zero :
    mqEvalN8 (Vector.replicate 8 (0 : Gf16)) (Vector.replicate 64 (0 : Gf16)) =
      (0 : Gf16) := by
  native_decide

end CatCrypt.Crypto.MAYO.MqEvalVerified
