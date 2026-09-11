/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the NTRU-HRSS ring-multiply MAC step

This module extends the **C4** step of the verified-compiler plan to the
load-bearing inner-loop body of NTRU-HRSS-701's cyclic ring multiply
(`NTRU/NtruhrssRingMulVerified.lean`). NTRU-HRSS is the power-of-two-modulus
lattice KEM; its core arithmetic is the cyclic-convolution product

```
    out[k] = Σ_{(i+j) mod N = k} a[i] · b[j]    (mod 8192)
```

over `Zq8192 := ZMod 8192 = Z/2^13`. Each output coefficient is built by
repeated **multiply-accumulate** (MAC) of the form `acc := acc + a · b`, and
because the modulus `q = 8192 = 2^13` is a power of two, the reduction `mod
2^13` is *free*: it is the single bit-mask `& 8191` (`= & (2^13 - 1)`), the low
13 bits of the running word. There is **no Barrett / Montgomery / Mersenne
fold** — the single mask `& 0x1FFF` *is* the modular reduction. This is the
direct sibling of the FrodoKEM MAC (`CompileFromHaxFrodoMac`), with the only
difference being the modulus (`2^13` instead of `2^16`, mask `8191` instead of
`65535`); sntrup761 (`q = 4591`, prime) would instead need a real mod-p reduce,
so the HRSS power-of-two variant is the cleaner tie.

## The NTRU MAC step, `w = 64`

The accumulator and the two operands are carried in `BitVec 64` (the owned-emit
convention). The body is

```
   p := a * b                 -- exact integer product of two coefficients
   acc1 := acc + p            -- accumulate
   r := acc1 & 0x1FFF         -- reduce mod 2^13 (mask = the NTRU-HRSS reduce)
```

All three steps are `*` / `+` / `&` over GPRs — exactly the
`wrapping_mul`/`wrapping_add`/`BitAnd` recognizers already accepted by the
SHA-256/Keccak/BLAKE2/GF(127)/Frodo fronts, so **no change to the verified front
is required**. This is the cyclic-ring lattice analogue of the dense-LWE Frodo
MAC fan-out (`CompileFromHaxFrodoMac`), with the only change being the mask
literal (`8191` vs `65535`) because both moduli are powers of two dividing
`2^64`.

## Method (mirrors `CompileFromHaxFrodoMac.frodoMac_compiles`)

`ntruMacSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `ntruMacForm` is the explicit closed **emit form** the
source denotes to; the `_compiles` theorem routes the form source-spec
(`ntruMacSrc_denoteScalar`, a `rfl`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the emit form.

The abstract `Zq8192` ring tie (`ntruMacForm_eq_ring`, in the companion
`...Tie.lean`) shows the emitted leaf, read back through `Zq8192.fromNat ∘
toNat`, computes exactly the `ZMod 8192` MAC `accZ + aZ · bZ` that
`NtruhrssRingMulVerified.ringMulCoeff` sums.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMul

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The NTRU MAC source — `w = 64`, parameters `["acc","a","b"]` -/

/-- The NTRU-HRSS multiply-accumulate source as a hax `ImpExpr`, fully
    let-normalized, parameters `["acc","a","b"]` (`nIn = 3`; `I 0 = acc`,
    `I 1 = a`, `I 2 = b`). Integer multiply `a·b`, accumulate into `acc`, then a
    single `& 0x1FFF` mask that *is* the `mod 2^13` reduction (NTRU-HRSS's
    modulus is the power of two `8192`). Returns the reduced accumulator
    register `r`. -/
def ntruMacSrc : ImpExpr :=
  -- pre-bind the mask literal (binary-ALU literal operands must be `let`-bound
  -- under the front's ANF discipline)
  .letBind "mask" (.lit (.int 8191))
  -- p := a * b
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   -- acc1 := acc + p
   (.letBind "acc1" (.app "wrapping_add" [.var "acc", .var "p"])
    -- r := acc1 & 0x1FFF   (mod-2^13 reduce)
    (.letBind "r" (.app "BitAnd" [.var "acc1", .var "mask"])
     (.var "r"))))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated
    as a plain `def` so the emitted form is explicit and auditable. This is the
    exact step-by-step computation `ntruMacSrc` performs: `wrapping_mul` is `*`,
    `wrapping_add` is `+`, `BitAnd` is `&&&`. -/
def ntruMacForm (acc a b : BitVec 64) : BitVec 64 :=
  let p    := a * b
  let acc1 := acc + p
  acc1 &&& 8191

/-- The NTRU MAC source denotes (under `denoteScalar`, parameters
    `["acc","a","b"]`) to the emit form `ntruMacForm`, reading `acc = inpGet I 0`,
    `a = inpGet I 1`, `b = inpGet I 2`. The closed let-normalized body reduces
    definitionally: `wrapping_mul` is `*`, `wrapping_add` is `+`, `BitAnd` is
    `&&&`. -/
theorem ntruMacSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["acc", "a", "b"] I ntruMacSrc (fun _ => none)
      = some (ntruMacForm (inpGet I 0) (inpGet I 1) (inpGet I 2)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the NTRU MAC (`w = 64`, three
    parameters). -/
theorem ntruMac_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] ntruMacSrc).isSome := by
  native_decide

/-- **NTRU-HRSS ring-multiply MAC step emitted by the verified compiler
    (mask-reduce form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["acc","a","b"] ntruMacSrc = some c`, and for every
    `(acc, a, b)`, `c`'s `BitVec 64` denotation (under the input valuation
    `![acc, a, b]`) is exactly the closed emit form `ntruMacForm`. Routed through
    the C3 per-primitive obligation `compileFromHax_meets_spec`. This is a C4
    fan-out to the **power-of-two-modulus** cyclic-ring core of NTRU-HRSS (the
    convolution inner step `acc + a·b mod 2^13`), reusing the
    SHA-256/Keccak/BLAKE2/GF(127)/Frodo `wrapping_mul`/`wrapping_add`/`BitAnd`
    recognizers with no front change. The abstract `Zq8192` ring tie is
    `ntruMacForm_eq_ring` (companion module). -/
theorem ntruMac_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] ntruMacSrc = some prog ∧
      ∀ (acc a b : BitVec 64),
        prog.denote (inputValuation 64 3 ![acc, a, b])
          = ntruMacForm acc a b := by
  set prog := (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] ntruMacSrc).get
    ntruMac_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] ntruMacSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro acc a b
  have hspec : ImpExpr.denoteScalar ["acc", "a", "b"] ![acc, a, b]
      ntruMacSrc (fun _ => none) = some (ntruMacForm acc a b) := by
    have h := ntruMacSrc_denoteScalar (nIn := 3) ![acc, a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["acc", "a", "b"]
    ![acc, a, b] ntruMacSrc _ hc hspec

/-! ## The abstract mod-`2^13` tie (the power-of-two reduce identity)

The emit form `ntruMacForm` equals the abstract `(acc + a*b) mod 2^13`. Because
the modulus is a power of two dividing `2^64`, the `& 0x1FFF` mask is exactly
`% 8192` at the `BitVec` level, so this is the genuine (and exact) NTRU-HRSS
reduce — phrased in pure `BitVec` so `bv_decide` bitblasts the mask. No domain
restriction is needed: the mask reduces *any* 64-bit accumulator into
`[0, 2^13)`, matching the coefficient-ring wraparound semantics. -/

/-- **NTRU MAC mask-form = `(acc + a*b) mod 8192`**, with no domain restriction.
    The `& 0x1FFF` mask is exactly the `mod 2^13` reduction because `8192 = 2^13`
    is a power of two; the integer multiply `a*b` and accumulate `acc + ·` may
    wrap `BitVec 64`, but only their low 13 bits survive the mask, matching the
    `Z/8192` coefficient semantics NTRU-HRSS's ring-multiply kernel reduces
    under. -/
theorem ntruMacForm_eq_mod (acc a b : BitVec 64) :
    ntruMacForm acc a b = (acc + a * b) % 8192#64 := by
  unfold ntruMacForm
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMul
