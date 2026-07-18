/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the HAWK ring-multiply MAC step

This module extends the **C4** step of the verified-compiler plan to the
load-bearing inner-loop body of HAWK's negacyclic ring multiply
(`HAWK/RingMul4WayVerified.lean`). HAWK is the Falcon-family hash-and-sign
lattice signature over the cyclotomic ring `Z/q[x]/(x^N + 1)`; its per-lane
core arithmetic is the schoolbook negacyclic convolution

```
    c[k] = Σ_{i=0..N-1} a[i] · b[(k-i) mod N] · sign    (mod 1024)
```

over `Zq1024 := ZMod 1024 = Z/2^10` (`RingMul4WayVerified.ringMulCoeff`). The
coefficient sum is built by repeated **multiply-accumulate** (MAC) of the form
`acc := acc + a · b`, and because the modulus `q = 1024 = 2^10` is a power of
two, the reduction `mod 2^10` is *free*: it is the low-10-bit truncation of the
running word, a single mask `& 0x3FF`. There is **no Barrett / Montgomery /
Mersenne fold** — the single mask `& 1023` *is* the modular reduction. This is
the power-of-two-modulus lattice fan-out, identical in shape to the FrodoKEM
(`2^16`) and NTRU-HRSS (`2^13`) MAC ties, just with the `2^10` mask.

## The HAWK MAC step, `w = 64`

The accumulator and the two operands are carried in `BitVec 64` (the owned-emit
convention). The body is

```
   p := a * b                 -- exact integer product of two coefficients
   acc1 := acc + p            -- accumulate
   r := acc1 & 0x3FF          -- reduce mod 2^10 (low-10-bit truncation = the ring reduce)
```

All three steps are `*` / `+` / `&` over GPRs — exactly the
`wrapping_mul`/`wrapping_add`/`BitAnd` recognizers already accepted by the
SHA-256/Keccak/BLAKE2/GF(127)/Frodo/NTRU fronts, so **no change to the verified
front is required**.

## Method (mirrors `CompileFromHaxFrodoMac.frodoMac_compiles`)

`hawkMacSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `hawkMacForm` is the explicit closed **emit form** the
source denotes to; the `_compiles` theorem routes the form source-spec
(`hawkMacSrc_denoteScalar`, a `rfl`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the emit form.

The abstract `Zq1024` ring tie (`hawkMacForm_eq_ring`, in the companion
`...Tie.lean`) shows the emitted leaf, read back through `Zq1024.fromNat ∘
toNat`, computes exactly the `ZMod 1024` MAC `accZ + aZ · bZ` that
`RingMul4WayVerified.ringMulCoeff` sums.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMul

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The HAWK MAC source — `w = 64`, parameters `["acc","a","b"]` -/

/-- The HAWK negacyclic ring-multiply multiply-accumulate source as a hax
    `ImpExpr`, fully let-normalized, parameters `["acc","a","b"]` (`nIn = 3`;
    `I 0 = acc`, `I 1 = a`, `I 2 = b`). Integer multiply `a·b`, accumulate into
    `acc`, then a single `& 0x3FF` mask that *is* the `mod 2^10` reduction
    (HAWK's modulus is the power of two `1024`). Returns the reduced accumulator
    register `r`. -/
def hawkMacSrc : ImpExpr :=
  -- pre-bind the mask literal (binary-ALU literal operands must be `let`-bound
  -- under the front's ANF discipline)
  .letBind "mask" (.lit (.int 1023))
  -- p := a * b
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   -- acc1 := acc + p
   (.letBind "acc1" (.app "wrapping_add" [.var "acc", .var "p"])
    -- r := acc1 & 0x3FF   (low-10-bit truncation = the mod-2^10 reduce)
    (.letBind "r" (.app "BitAnd" [.var "acc1", .var "mask"])
     (.var "r"))))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated
    as a plain `def` so the emitted form is explicit and auditable. This is the
    exact step-by-step computation `hawkMacSrc` performs: `wrapping_mul` is `*`,
    `wrapping_add` is `+`, `BitAnd` is `&&&`. -/
def hawkMacForm (acc a b : BitVec 64) : BitVec 64 :=
  let p    := a * b
  let acc1 := acc + p
  acc1 &&& 1023

/-- The HAWK MAC source denotes (under `denoteScalar`, parameters
    `["acc","a","b"]`) to the emit form `hawkMacForm`, reading `acc = inpGet I 0`,
    `a = inpGet I 1`, `b = inpGet I 2`. The closed let-normalized body reduces
    definitionally: `wrapping_mul` is `*`, `wrapping_add` is `+`, `BitAnd` is
    `&&&`. -/
theorem hawkMacSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["acc", "a", "b"] I hawkMacSrc (fun _ => none)
      = some (hawkMacForm (inpGet I 0) (inpGet I 1) (inpGet I 2)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the HAWK MAC (`w = 64`, three
    parameters). -/
theorem hawkMac_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] hawkMacSrc).isSome := by
  native_decide

/-- **HAWK ring-multiply MAC step emitted by the verified compiler (mask-reduce
    form).** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["acc","a","b"] hawkMacSrc = some c`, and for every
    `(acc, a, b)`, `c`'s `BitVec 64` denotation (under the input valuation
    `![acc, a, b]`) is exactly the closed emit form `hawkMacForm`. Routed through
    the C3 per-primitive obligation `compileFromHax_meets_spec`. This is a C4
    fan-out to the **power-of-two-modulus** lattice core of HAWK (the negacyclic
    ring-multiply inner step `acc + a·b mod 2^10`), reusing the
    SHA-256/Keccak/BLAKE2/GF(127)/Frodo/NTRU `wrapping_mul`/`wrapping_add`/`BitAnd`
    recognizers with no front change. The abstract `Zq1024` ring tie is
    `hawkMacForm_eq_ring` (companion module). -/
theorem hawkMac_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] hawkMacSrc = some prog ∧
      ∀ (acc a b : BitVec 64),
        prog.denote (inputValuation 64 3 ![acc, a, b])
          = hawkMacForm acc a b := by
  set prog := (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] hawkMacSrc).get
    hawkMac_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] hawkMacSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro acc a b
  have hspec : ImpExpr.denoteScalar ["acc", "a", "b"] ![acc, a, b]
      hawkMacSrc (fun _ => none) = some (hawkMacForm acc a b) := by
    have h := hawkMacSrc_denoteScalar (nIn := 3) ![acc, a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["acc", "a", "b"]
    ![acc, a, b] hawkMacSrc _ hc hspec

/-! ## The abstract mod-`2^10` tie (the power-of-two reduce identity)

The emit form `hawkMacForm` equals the abstract `(acc + a*b) mod 2^10`. Because
the modulus is a power of two dividing `2^64`, the `& 0x3FF` mask is exactly
`% 1024` at the `BitVec` level, so this is the genuine (and exact) ring reduce —
phrased in pure `BitVec` so `bv_decide` bitblasts the mask. No domain
restriction is needed: the mask reduces *any* 64-bit accumulator into `[0,2^10)`,
matching the `Z/1024` wraparound semantics. -/

/-- **HAWK MAC mask-form = `(acc + a*b) mod 1024`**, with no domain restriction.
    The `& 0x3FF` mask is exactly the `mod 2^10` reduction because `1024 = 2^10`
    is a power of two; the integer multiply `a*b` and accumulate `acc + ·` may
    wrap `BitVec 64`, but only their low 10 bits survive the mask, matching the
    `Z/1024` semantics HAWK's ring-multiply kernel reduces under. -/
theorem hawkMacForm_eq_mod (acc a b : BitVec 64) :
    hawkMacForm acc a b = (acc + a * b) % 1024#64 := by
  unfold hawkMacForm
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMul
