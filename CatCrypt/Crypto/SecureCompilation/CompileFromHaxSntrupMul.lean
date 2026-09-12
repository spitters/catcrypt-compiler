/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the sntrup761 schoolbook-multiply MAC step

This module extends the **C4** step of the verified-compiler plan to the
inner-loop body of Streamlined NTRU Prime / sntrup761's schoolbook
polynomial multiply (`NTRU/Sntrup761MulVerified.lean`). sntrup761 is the
**prime-modulus** lattice KEM (NTRU Prime's distinctive choice): its core
arithmetic is the schoolbook coefficient product

```
    out[k] = Σ_{i + j = k} a[i] · b[j]    (mod 4591)
```

over `Zq4591 := ZMod 4591`, a *prime field* (`q = 4591` is prime). Each output
coefficient is built by repeated **multiply-accumulate** (MAC) of the form
`acc := acc + a · b`, and — unlike the power-of-two FrodoKEM (`mod 2^16`) and
NTRU-HRSS (`mod 2^13`) siblings — the modulus is a **prime that does not divide
`2^64`**, so the reduction is *not* a single bit-mask. The schoolbook
accumulator therefore carries the *unreduced* integer sum of products; the
canonical mod-`4591` representative is taken by the ring projection at the
coefficient-readback, exactly as `Sntrup761MulVerified.coeffSum` accumulates
`a[i] · b[j]` in `Zq4591` (each `*`/`+` is already the ring op).

## The sntrup MAC step, `w = 64`

The accumulator and the two operands are carried in `BitVec 64` (the owned-emit
convention). The kernel body is the **unreduced integer MAC** — there is no mask
(the modulus is not a power of two), so the kernel emits exactly the two ARX ops
the front already accepts:

```
   p    := a * b        -- exact integer product of two coefficients
   acc1 := acc + p      -- accumulate (mod 4591 taken at readback, not here)
```

Both steps are `*` / `+` over GPRs — exactly the `wrapping_mul`/`wrapping_add`
recognizers already accepted by the SHA-256/Keccak/BLAKE2/GF(127)/Frodo/NTRU
fronts, so **no change to the verified front is required**. This is the
*prime-modulus* lattice analogue of the power-of-two Frodo/NTRU MAC fan-out: the
only structural change is that the `& mask` reduce drops out (a prime modulus
admits no mask), and the `mod 4591` lands in the abstract ring tie rather than in
the emitted kernel — the NTRU-Prime reduction.

## Method (mirrors `CompileFromHaxNtruMul.ntruMac_compiles`)

`sntrupMacSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `sntrupMacForm` is the explicit closed **emit form**
the source denotes to; the `_compiles` theorem routes the form source-spec
(`sntrupMacSrc_denoteScalar`, a `rfl`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the emit form.

The abstract `Zq4591` prime-field ring tie (`sntrupMacForm_eq_ring`, in the
companion `...Tie.lean`) shows the emitted leaf, read back through
`Zq4591.fromNat ∘ toNat`, computes exactly the `ZMod 4591` MAC `accZ + aZ · bZ`
that `Sntrup761MulVerified.coeffSum` sums.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMul

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The sntrup MAC source — `w = 64`, parameters `["acc","a","b"]` -/

/-- The sntrup761 multiply-accumulate source as a hax `ImpExpr`, fully
    let-normalized, parameters `["acc","a","b"]` (`nIn = 3`; `I 0 = acc`,
    `I 1 = a`, `I 2 = b`). Integer multiply `a·b`, accumulate into `acc`. There
    is **no mask** — `q = 4591` is prime (not a power of two), so the modular
    reduction is *not* a bitwise mask; the kernel carries the unreduced integer
    sum and the mod-`4591` canonical representative is taken by the ring
    projection at coefficient readback (the tie). Returns the accumulated
    register `acc1`. -/
def sntrupMacSrc : ImpExpr :=
  -- p := a * b
  .letBind "p" (.app "wrapping_mul" [.var "a", .var "b"])
   -- acc1 := acc + p
   (.letBind "acc1" (.app "wrapping_add" [.var "acc", .var "p"])
    (.var "acc1"))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated
    as a plain `def` so the emitted form is explicit and auditable. This is the
    exact step-by-step computation `sntrupMacSrc` performs: `wrapping_mul` is `*`,
    `wrapping_add` is `+`. No mask (prime modulus). -/
def sntrupMacForm (acc a b : BitVec 64) : BitVec 64 :=
  let p    := a * b
  acc + p

/-- The sntrup MAC source denotes (under `denoteScalar`, parameters
    `["acc","a","b"]`) to the emit form `sntrupMacForm`, reading `acc = inpGet I 0`,
    `a = inpGet I 1`, `b = inpGet I 2`. The closed let-normalized body reduces
    definitionally: `wrapping_mul` is `*`, `wrapping_add` is `+`. -/
theorem sntrupMacSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["acc", "a", "b"] I sntrupMacSrc (fun _ => none)
      = some (sntrupMacForm (inpGet I 0) (inpGet I 1) (inpGet I 2)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the sntrup MAC (`w = 64`, three
    parameters). -/
theorem sntrupMac_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] sntrupMacSrc).isSome := by
  native_decide

/-- **sntrup761 schoolbook-multiply MAC step emitted by the verified compiler
    (prime-modulus, unreduced-accumulate form).** There is a compiled
    `Com jasminDialect` `c` with
    `compileFromHax ["acc","a","b"] sntrupMacSrc = some c`, and for every
    `(acc, a, b)`, `c`'s `BitVec 64` denotation (under the input valuation
    `![acc, a, b]`) is exactly the closed emit form `sntrupMacForm`. Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. This is a
    C4 fan-out to the **prime-modulus** schoolbook core of sntrup761 (the
    convolution inner step `acc + a·b`, reduced mod `4591` at readback), reusing
    the SHA-256/Keccak/BLAKE2/GF(127)/Frodo/NTRU `wrapping_mul`/`wrapping_add`
    recognizers with no front change. The abstract `Zq4591` prime-field ring tie
    is `sntrupMacForm_eq_ring` (companion module). -/
theorem sntrupMac_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] sntrupMacSrc = some prog ∧
      ∀ (acc a b : BitVec 64),
        prog.denote (inputValuation 64 3 ![acc, a, b])
          = sntrupMacForm acc a b := by
  set prog := (compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] sntrupMacSrc).get
    sntrupMac_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["acc", "a", "b"] sntrupMacSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro acc a b
  have hspec : ImpExpr.denoteScalar ["acc", "a", "b"] ![acc, a, b]
      sntrupMacSrc (fun _ => none) = some (sntrupMacForm acc a b) := by
    have h := sntrupMacSrc_denoteScalar (nIn := 3) ![acc, a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["acc", "a", "b"]
    ![acc, a, b] sntrupMacSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMul
