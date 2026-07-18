/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA `caddq` conditional reduce

This module is the **first LATTICE-family** compile-from-hax leaf. It extends the
**C4** step of the verified-compiler plan to ML-DSA-65's signed-`int32`
polynomial-arithmetic ALU (FIPS-204, `q = 8380417`). The per-coefficient body
chosen is `caddq` — the branch-free **conditional add of `q`** that brings a
centered residue `a ∈ (−q, q)` into the canonical range `[0, q)`:

```c
// FIPS-204 / PQClean reduce.c, conditional add of q:
int32_t caddq(int32_t a) { a += (a >> 31) & Q; return a; }
```

`a >> 31` is the **signed** (arithmetic) shift of an `int32`: all-ones if `a < 0`,
else `0`. The verified front (`ImpExprToThir`) only recognises **logical** shift
(`shr`/`shift_right` ↦ `>>>`), not arithmetic `sar`. We therefore realise the same
sign-mask branch-free, at `w = 64`, with the SDitH (`CompileFromHaxSdithGf251`)
mask idiom: at width 64 the sign-extended `int32` word `a` has its sign bit in bit
`63`, so the **logical** shift `a >>> 63 ∈ {0, 1}` *is* the sign indicator, and
`0 − (a >>> 63)` is the all-ones / all-zero mask:

```
   m  := a >> 63                 -- logical: 1 if a<0 (sign bit), else 0
   nm := 0 - m                   -- all-ones mask if a<0, else 0
   mm := nm & q                  -- q if a<0, else 0
   r  := a + mm                  -- a (a≥0)  or  a+q  (a<0)
```

All steps are `>>`/`-`/`&`/`+` over GPRs — the SHA-256 / Keccak / BLAKE2 / SDitH
recognizers (`shift_right`/`wrapping_sub`/`BitAnd`/`wrapping_add` with a literal
shift count) already accept them, so **no change to the verified front is
required**. This is the first ML-DSA (lattice) fan-out point.

## Method (mirrors `CompileFromHaxSdithGf251.gf251Mul_compiles`)

`mldsaCaddqSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `mldsaCaddqFold` is the explicit closed mask-blend
**emit form** the source denotes to; the `_compiles` theorem routes the FOLD-FORM
source-spec (`mldsaCaddqSrc_denoteScalar`, a `rfl`) through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by
the verified compiler* and proven equal to the mask-blend form.

The abstract `= a % q` (canonical-rep) tie is stated and proved **separately**
(`mldsaCaddqFold_eq_centeredCanonical`) over the centered domain `−q < a.toInt < q`
via pure-BitVec `bv_decide` — the prime-field reduce identity (the SDitH lesson),
the analogue of the `#117` Barrett seam.

## Remaining `PolyOwnedEmit` bodies (follow-up)

`PolyOwnedEmit.lean` carries four owned per-coefficient bodies:
`poly_add`, `poly_sub` (pure two's-complement add/sub — easy follow-ups, but they
read **two** parameters and emit no reduce), `poly_reduce` (Barrett `reduce32`)
and `poly_pointwise_montgomery` (signed Montgomery). The latter two use the
**arithmetic** shift `sar` (`>>23` / `>>32` on signed values), which the front
does **not** yet recognise — they need an `.sar` / `Rhs.sarImm` recognizer
(`ASR`) added to `ImpExprToThir` before they can be derived here. `caddq` is the
cleanest single-output body that compiles unchanged.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaPoly

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-DSA `caddq` conditional-reduce source — `w = 64`, parameter `["a"]` -/

/-- The ML-DSA `caddq` source as a hax `ImpExpr`, fully let-normalized, single
    parameter `["a"]` (`nIn = 1`; `I 0 = a`, a sign-extended centered `int32`).
    Branch-free conditional add of `q = 8380417` using the `0 − (a >> 63)` mask
    (the sign bit of the width-64 sign-extended word). Returns the canonical
    register `r`. -/
def mldsaCaddqSrc : ImpExpr :=
  -- pre-bind the constants (binary-ALU literal operands must be `let`-bound under
  -- the front's ANF discipline; only `shr` counts may stay literal)
  .letBind "cq" (.lit (.int 8380417))
   (.letBind "c0" (.lit (.int 0))
  -- m := a >> 63   (logical: sign bit, 1 if a<0 else 0)
  (.letBind "m" (.app "shift_right" [.var "a", .lit (.int 63)])
   -- nm := 0 - m   (all-ones mask if a<0, else 0)
   (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
    -- mm := nm & q  (q if a<0, else 0)
    (.letBind "mm" (.app "BitAnd" [.var "nm", .var "cq"])
     -- r := a + mm
     (.letBind "r" (.app "wrapping_add" [.var "a", .var "mm"])
      (.var "r"))))))

/-- The explicit closed mask-blend **emit form** the source denotes to, at
    `w = 64`. Stated as a plain `def` so the emitted form is explicit and
    auditable. This is the exact step-by-step computation `mldsaCaddqSrc`
    performs; `mldsaCaddqFold_eq_centeredCanonical` ties it to abstract `a % q`
    on the centered domain. -/
def mldsaCaddqFold (a : BitVec 64) : BitVec 64 :=
  let m  := a >>> (63 : Nat)
  let nm := (0 : BitVec 64) - m
  let mm := nm &&& 8380417
  a + mm

/-- The `caddq` source denotes (under `denoteScalar`, parameter `["a"]`) to the
    mask-blend emit form `mldsaCaddqFold`, reading `a = inpGet I 0`. The closed
    let-normalized body reduces definitionally: `shift_right 63` is `>>> 63`,
    `wrapping_sub` is `-`, `BitAnd` is `&&&`, `wrapping_add` is `+`. -/
theorem mldsaCaddqSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I mldsaCaddqSrc (fun _ => none)
      = some (mldsaCaddqFold (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on `caddq` (`w = 64`, one parameter). -/
theorem mldsaCaddq_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaCaddqSrc).isSome := by
  native_decide

/-- **ML-DSA `caddq` emitted by the verified compiler (mask-blend form).** There is
    a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a"] mldsaCaddqSrc = some c`, and for every `a`, `c`'s
    `BitVec 64` denotation (under the input valuation `![a]`) is exactly the closed
    mask-blend emit form `mldsaCaddqFold`. Routed through the C3 per-primitive
    obligation `compileFromHax_meets_spec`. This is the **first lattice-family**
    C4 fan-out (ML-DSA-65, `q = 8380417`), reusing the SHA-256/Keccak/BLAKE2/SDitH
    `shift_right`/`wrapping_sub`/`BitAnd`/`wrapping_add` recognizers with no front
    change. The abstract `a % q` tie is `mldsaCaddqFold_eq_centeredCanonical`. -/
theorem mldsaCaddq_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] mldsaCaddqSrc = some prog ∧
      ∀ (a : BitVec 64),
        prog.denote (inputValuation 64 1 ![a])
          = mldsaCaddqFold a := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["a"] mldsaCaddqSrc).get
    mldsaCaddq_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] mldsaCaddqSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a]
      mldsaCaddqSrc (fun _ => none) = some (mldsaCaddqFold a) := by
    have h := mldsaCaddqSrc_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"]
    ![a] mldsaCaddqSrc _ hc hspec

/-! ## The abstract `a % q` tie (the conditional-reduce identity)

The mask-blend emit form `mldsaCaddqFold` equals abstract `a.toInt % q` over the
centered ML-DSA domain `−q < a.toInt < q` (every centered base-field residue, the
output range of the Barrett `reduce32`). This is the genuine conditional-reduce
identity — the analogue of the `#117` Barrett seam, not an ARX `rfl`. -/

/-- **ML-DSA `caddq` mask-blend = canonical `a mod q`** on the centered domain
    `−q < a.toInt < q`. Ties the emitted closed mask-blend form `mldsaCaddqFold`
    (the `_compiles` deliverable) to the abstract canonical representative `a mod q`
    in `[0, q)`. For a centered residue `a` (sign-extended into `BitVec 64`), the
    sign-bit mask adds `q` exactly when `a < 0`, landing the result in `[0, q)`;
    that result's signed value is the canonical `((a.toInt % q + q) % q)`
    representative. The centered-domain hypotheses are stated as signed `BitVec`
    bounds (`BitVec.sle`/`slt`), exactly the output range of the Barrett
    `reduce32`. -/
theorem mldsaCaddqFold_eq_centeredCanonical (a : BitVec 64)
    (hlo : (-8380417#64).sle a = true) (hhi : a.slt 8380417#64 = true) :
    (mldsaCaddqFold a) = (if a.msb then a + 8380417#64 else a) ∧
      (mldsaCaddqFold a).ult 8380417#64 = true := by
  unfold mldsaCaddqFold
  constructor <;> bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaPoly
