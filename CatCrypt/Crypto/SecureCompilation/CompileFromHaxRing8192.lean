/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# #606 fan-out: the verified compiler emits a `Z/8192Z` (NTRU-HRSS) ring multiply

This module extends the **C4** step of the verified-compiler plan to the
**power-of-two ring** coefficient multiply of **NTRU-HRSS-701**:
`q = 8192 = 2¹³`. Unlike the Mersenne/Solinas prime-field fan-outs (GF(127),
GF(251), GF(8191)), reduction `mod 2¹³` is a single **bit-mask** `& 8191`
(`2¹³ - 1`), no fold and no conditional subtract — the ring structure is
`Z/8192Z` (composite modulus, not a field), which is exactly what NTRU-HRSS's
coefficient ring-multiply kernel uses (add/sub/mul only).

## Z/8192Z coefficient multiply (mask reduce), `w = 64`

With `a, b ∈ [0, 8191]` the product `a·b ≤ 8191² = 67092481 < 2²⁷` fits in the
low word, and `mod 2¹³` is the low-13-bit mask:

```
   p := a*b                    -- p < 2²⁷
   r := p & 8191               -- mod 8192 = low-13-bit mask
```

Both steps are `*`/`&` over GPRs — the existing SHA-256/Keccak/BLAKE2
`wrapping_mul`/`BitAnd` recognizers accept them, so **no change to the verified
front is required**. This is the power-of-two **ring** sibling of the prime-field
fan-outs.

## Method (mirrors `CompileFromHaxGf8191.gf8191Mul_compiles`)

`ring8192MulSrc` is the let-normalized `ImpExpr`; `ring8192MulMask` is the closed
mask **emit form** the source denotes to; `_compiles` routes the source-spec (a
`rfl`) through `compileFromHax_meets_spec`. The abstract `(a*b) % 8192` tie is
`ring8192MulMask_eq_mod` over `a, b < 8192`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The Z/8192Z ring multiply source — `w = 64`, parameters `["a","b"]` -/

/-- The Z/8192Z coefficient multiply source as a hax `ImpExpr`, fully
    let-normalized, parameters `["a","b"]`. Integer multiply then a low-13-bit
    mask (`mod 2¹³`). Returns the residue register `r`. -/
def ring8192MulSrc : ImpExpr :=
  .letBind "c8191" (.lit (.int 8191))
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   (.letBind "r" (.app "BitAnd" [.var "p", .var "c8191"])
    (.var "r")))

/-- The explicit closed mask **emit form** the source denotes to. -/
def ring8192MulMask (a b : BitVec 64) : BitVec 64 :=
  let p := a * b
  p &&& 8191

/-- The Z/8192Z source denotes to the mask emit form. -/
theorem ring8192MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I ring8192MulSrc (fun _ => none)
      = some (ring8192MulMask (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the Z/8192Z multiply. -/
theorem ring8192Mul_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] ring8192MulSrc).isSome := by
  native_decide

/-- **Z/8192Z (NTRU-HRSS) multiply emitted by the verified compiler (mask
    form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] ring8192MulSrc = some c`, and `c`'s `BitVec 64`
    denotation (under `![a, b]`) is the closed mask emit form `ring8192MulMask`.
    A #606 fan-out to the power-of-two coefficient ring `Z/2¹³Z`. The abstract
    `(a*b) % 8192` tie is `ring8192MulMask_eq_mod`. -/
theorem ring8192Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] ring8192MulSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = ring8192MulMask a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] ring8192MulSrc).get
    ring8192Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] ring8192MulSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      ring8192MulSrc (fun _ => none) = some (ring8192MulMask a b) := by
    have h := ring8192MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] ring8192MulSrc _ hc hspec

/-! ## The abstract `(a*b) % 8192` tie (the power-of-two mask-reduce identity) -/

/-- **Z/8192Z mask = `(a*b) mod 8192`** on the residue domain `a, b < 8192`. Ties
    the emitted closed mask form `ring8192MulMask` (the `_compiles` deliverable)
    to abstract modular multiply. The product `a·b ≤ 8191² < 2²⁷` never wraps the
    `BitVec 64`, so the low-13-bit mask `& 8191` is exactly `mod 2¹³`. -/
theorem ring8192MulMask_eq_mod (a b : BitVec 64)
    (ha : a < 8192#64) (hb : b < 8192#64) :
    ring8192MulMask a b = (a * b) % 8192#64 := by
  unfold ring8192MulMask
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192
