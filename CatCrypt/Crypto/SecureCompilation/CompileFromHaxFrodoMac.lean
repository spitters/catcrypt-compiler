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
# The verified compiler emits the FrodoKEM LWE multiply-accumulate step

This module applies the verified compile-from-hax front to the
inner-loop body of FrodoKEM's dense-LWE matrix–vector product
(`Frodo/FrodoMatmulVerified.lean`). FrodoKEM is the conservative,
no-ring-structure lattice KEM; its core arithmetic is the dense integer
matrix–vector product

```
    out[r] = Σ_{c=0..N-1} A[r][c] · s[c]    (mod 2^16)
```

over `Zq65536 := ZMod 65536 = Z/2^16`. The row sum is built by repeated
**multiply-accumulate** (MAC) of the form `acc := acc + a · b`, and because the
modulus `q = 65536 = 2^16` is a power of two, the reduction `mod 2^16` is *free*:
it is `u16` two's-complement truncation, the low 16 bits of the running word.
There is **no Barrett / Montgomery / Mersenne fold** — the single mask `& 0xFFFF`
*is* the modular reduction. This makes the Frodo MAC the cleanest lattice
fan-out target: a straight `*`, `+`, `&`-with-a-literal over GPRs.

## The Frodo MAC step, `w = 64`

The accumulator and the two operands are carried in `BitVec 64` (the owned-emit
convention). The body is

```
   p := a * b                 -- exact integer product of two coefficients
   acc1 := acc + p            -- accumulate
   r := acc1 & 0xFFFF         -- reduce mod 2^16 (u16 truncation = the LWE reduce)
```

All three steps are `*` / `+` / `&` over GPRs — exactly the
`wrapping_mul`/`wrapping_add`/`BitAnd` recognizers already accepted by the
SHA-256/Keccak/BLAKE2/GF(127) fronts, so **no change to the verified front is
required**. This is the power-of-two-modulus lattice analogue of the GF(127)
Mersenne-fold fan-out (`CompileFromHaxGf127`), with the fold collapsed to a
single mask because `2^16 ∣ 2^64`.

## Method (mirrors `CompileFromHaxGf127.gf127Mul_compiles`)

`frodoMacSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `frodoMacForm` is the explicit closed **emit form**
the source denotes to; the `_compiles` theorem routes the form source-spec
(`frodoMacSrc_denoteScalar`, a `rfl`) through the per-primitive obligation
`compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the emit form.

The abstract `Zq65536` field tie (`frodoMacForm_eq_field`, in the companion
`...Tie.lean`) shows the emitted leaf, read back through `Zq65536.fromNat ∘
toNat`, computes exactly the `ZMod 65536` MAC `accZ + aZ · bZ` that
`FrodoMatmulVerified.matmulRow` sums.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The Frodo MAC source — `w = 64`, parameters `["acc","a","b"]` -/

/-- The FrodoKEM multiply-accumulate source as a hax `ImpExpr`, fully
    let-normalized, parameters `["acc","a","b"]` (`nIn = 3`; `I 0 = acc`,
    `I 1 = a`, `I 2 = b`). Integer multiply `a·b`, accumulate into `acc`, then a
    single `& 0xFFFF` mask that *is* the `mod 2^16` reduction (Frodo's modulus is
    the power of two `65536`). Returns the reduced accumulator register `r`. -/
def frodoMacSrc : ImpExpr :=
  -- pre-bind the mask literal (binary-ALU literal operands must be `let`-bound
  -- under the front's ANF discipline)
  .letBind "mask" (.lit (.int 65535))
  -- p := a * b
  (.letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   -- acc1 := acc + p
   (.letBind "acc1" (.app "wrapping_add" [.var "acc", .var "p"])
    -- r := acc1 & 0xFFFF   (u16 truncation = the mod-2^16 reduce)
    (.letBind "r" (.app "BitAnd" [.var "acc1", .var "mask"])
     (.var "r"))))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated
    as a plain `def` so the emitted form is explicit and auditable. This is the
    exact step-by-step computation `frodoMacSrc` performs: `wrapping_mul` is `*`,
    `wrapping_add` is `+`, `BitAnd` is `&&&`. -/
def frodoMacForm (acc a b : BitVec 64) : BitVec 64 :=
  let p    := a * b
  let acc1 := acc + p
  acc1 &&& 65535

/-- The Frodo MAC source denotes (under `denoteScalar`, parameters
    `["acc","a","b"]`) to the emit form `frodoMacForm`, reading `acc = inpGet I 0`,
    `a = inpGet I 1`, `b = inpGet I 2`. The closed let-normalized body reduces
    definitionally: `wrapping_mul` is `*`, `wrapping_add` is `+`, `BitAnd` is
    `&&&`. -/
theorem frodoMacSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["acc", "a", "b"] I frodoMacSrc (fun _ => none)
      = some (frodoMacForm (inpGet I 0) (inpGet I 1) (inpGet I 2)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the Frodo MAC (`w = 64`, three
    parameters). -/
theorem frodoMac_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] frodoMacSrc).isSome := by
  native_decide

/-- **FrodoKEM MAC step emitted by the verified compiler (mask-reduce form).**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["acc","a","b"] frodoMacSrc = some c`, and for every
    `(acc, a, b)`, `c`'s `BitVec 64` denotation (under the input valuation
    `![acc, a, b]`) is exactly the closed emit form `frodoMacForm`. Routed through
    the per-primitive obligation `compileFromHax_meets_spec`. The target is
    the **power-of-two-modulus** lattice core of FrodoKEM (the LWE
    matrix–vector inner step `acc + a·b mod 2^16`), reusing the
    SHA-256/Keccak/BLAKE2/GF(127) `wrapping_mul`/`wrapping_add`/`BitAnd`
    recognizers with no front change. The abstract `Zq65536` field tie is
    `frodoMacForm_eq_field` (companion module). -/
theorem frodoMac_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] frodoMacSrc = some prog ∧
      ∀ (acc a b : BitVec 64),
        prog.denote (inputValuation 64 3 ![acc, a, b])
          = frodoMacForm acc a b := by
  set prog := (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] frodoMacSrc).get
    frodoMac_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] frodoMacSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro acc a b
  have hspec : ImpExpr.denoteScalar ["acc", "a", "b"] ![acc, a, b]
      frodoMacSrc (fun _ => none) = some (frodoMacForm acc a b) := by
    exact frodoMacSrc_denoteScalar (nIn := 3) ![acc, a, b]
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["acc", "a", "b"]
    ![acc, a, b] frodoMacSrc _ hc hspec

/-! ## The abstract mod-`2^16` tie (the power-of-two reduce identity)

The emit form `frodoMacForm` equals the abstract `(acc + a*b) mod 2^16`. Because
the modulus is a power of two dividing `2^64`, the `& 0xFFFF` mask is exactly
`% 65536` at the `BitVec` level, so this is the exact LWE reduce —
phrased in pure `BitVec` so `bv_decide` bitblasts the mask. No domain
restriction is needed: the mask reduces *any* 64-bit accumulator into `[0,2^16)`,
matching the `u16` wraparound semantics. -/

/-- **Frodo MAC mask-form = `(acc + a*b) mod 65536`**, with no domain restriction.
    The `& 0xFFFF` mask is exactly the `mod 2^16` reduction because `65536 = 2^16`
    is a power of two; the integer multiply `a*b` and accumulate `acc + ·` may
    wrap `BitVec 64`, but only their low 16 bits survive the mask, matching the
    `u16` semantics Frodo's matrix–vector kernel reduces under. -/
theorem frodoMacForm_eq_mod (acc a b : BitVec 64) :
    frodoMacForm acc a b = (acc + a * b) % 65536#64 := by
  unfold frodoMacForm
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac
