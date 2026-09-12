/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA `polyw1_pack` bit-pack byte

This module is a **LATTICE-family** compile-from-hax leaf. It extends the **C4**
step of the verified-compiler plan to ML-DSA-65's polynomial **bit-packing**
serializer (FIPS-204, `q = 8380417`). The body chosen is `polyw1_pack`, the
cleanest single-output bit-serialization in `CatCrypt/Crypto/MLDSA/PackEmit.lean`:

```c
/* polyw1_pack: 4-bit (ML-DSA-65), 2 coeffs -> 1 byte (PQClean ml-dsa-65/clean/poly.c) */
r[i] = a[2i+0] | (a[2i+1] << 4);
```

i.e. the packed byte `r = (a0 | (a1 << 4)) & 0xff` (the `(uint8_t)` truncation
modeled as a `& 0xff`). The two `w1` coefficients live in `[0, 15]` (4-bit
standard representatives), and the byte gathers `a0` in nibble `[3:0]` and `a1` in
nibble `[7:4]`.

## Why this body (shift kind / front scope)

Every operation is a **logical** shift / and / or on non-negative packed values:
the left shift `a1 << 4` is `shift_left`, the gather is `BitOr`, the byte
truncation is `BitAnd` with the `0xff` mask. The verified front
(`ImpExprToThir`) already recognises all three: `recogShift → .shl`,
`recogBin → .or`, `recogBin → .and`, the same recognizer chain used by the
ML-KEM `poly_frombytes` unpack (`CompileFromHaxMlkemSerial`). There is **no
arithmetic shift** here (contrast ML-DSA `reduce32`/`caddq`'s signed `>>`), so
the body compiles unchanged — **no front change required**. The `0xff` mask is a
pre-bound local (binary-ALU literal operands must be `let`-bound under the
front's ANF discipline); the `shift_left` count `4` stays literal.

## Method (mirrors `CompileFromHaxMldsaPoly.mldsaCaddq_compiles`)

`mldsaW1PackSrc` is the let-normalized `ImpExpr` (one op per `letBind`, all args
atoms or earlier locals); `mldsaW1PackFold` is the explicit closed bit-pack
**emit form** the source denotes to; the `_compiles` theorem routes the FOLD-FORM
source-spec (`mldsaW1PackSrc_denoteScalar`, a `rfl`) through the C3 per-primitive
obligation `compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by
the verified compiler* and proven equal to the bit-pack form.

The abstract FIPS-204 `polyw1_pack` encoding tie is stated and proved
**separately** (`mldsaW1PackFold_eq_byteEncode`) over the 4-bit coefficient domain
`a0, a1 < 2^4` via pure-`BitVec` `bv_decide`: on that domain the two nibbles are
disjoint, the `0xff` mask is exact (no loss, no overlap), and the packed byte is
exactly `a0 ||| (a1 <<< 4)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaPack

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-DSA `polyw1_pack` source — `w = 64`, parameters `["a0","a1"]` -/

/-- The ML-DSA-65 `polyw1_pack` 4-bit bit-pack source as a hax `ImpExpr`, fully
    let-normalized, parameters `["a0","a1"]` (`nIn = 2`; `I 0 = a0`, `I 1 = a1`,
    two 4-bit `w1` coefficients). The `0xff` byte-truncation mask is a pre-bound
    local; the `shift_left` count `4` stays literal.
    Body: `(a0 | (a1 << 4)) & 0xff`. Returns the packed-byte register `r`. -/
def mldsaW1PackSrc : ImpExpr :=
  .letBind "cMask" (.lit (.int 0xff))
   -- hi := a1 << 4
   (.letBind "hi" (.app "shift_left" [.var "a1", .lit (.int 4)])
    -- w := a0 | hi
    (.letBind "w" (.app "BitOr" [.var "a0", .var "hi"])
     -- r := w & 0xff
     (.letBind "r" (.app "BitAnd" [.var "w", .var "cMask"])
      (.var "r"))))

/-- The explicit closed **emit form** the source denotes to, at `w = 64`. Stated as
    a plain `def` so the emitted form is explicit and auditable: this is the exact
    step-by-step computation `mldsaW1PackSrc` performs.
    `mldsaW1PackFold_eq_byteEncode` ties it to the FIPS-204 `polyw1_pack` byte on
    the 4-bit coefficient domain. -/
def mldsaW1PackFold (a0 a1 : BitVec 64) : BitVec 64 :=
  let hi := a1 <<< (4 : Nat)
  (a0 ||| hi) &&& 0xff

/-- The ML-DSA `polyw1_pack` source denotes (under `denoteScalar`, parameters
    `["a0","a1"]`) to the closed bit-pack emit form `mldsaW1PackFold`, reading
    `a0 = inpGet I 0`, `a1 = inpGet I 1`. The closed let-normalized body reduces
    definitionally: `shift_left 4` is `<<< 4`, `BitOr` is `|||`, `BitAnd` is
    `&&&`. -/
theorem mldsaW1PackSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a0", "a1"] I mldsaW1PackSrc (fun _ => none)
      = some (mldsaW1PackFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the ML-DSA `polyw1_pack` body
    (`w = 64`, two parameters). -/
theorem mldsaW1Pack_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaW1PackSrc).isSome := by
  native_decide

/-- **ML-DSA-65 `polyw1_pack` (4-bit bit-pack) emitted by the verified compiler.**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a0","a1"] mldsaW1PackSrc = some c`, and for every coefficient
    pair `(a0, a1)`, `c`'s `BitVec 64` denotation (under the input valuation
    `![a0, a1]`) is exactly the closed bit-pack emit form `mldsaW1PackFold`
    (`(a0 | (a1 << 4)) & 0xff`). Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. This is a C4 fan-out to the **ML-DSA polynomial
    bit-packing** serializer (ML-DSA-65, `q = 8380417`), reusing the
    SHA-256/Keccak/BLAKE2/ML-KEM `shift_left`/`BitOr`/`BitAnd` recognizers (all
    *logical* shifts — no `sar`) with no front change. The abstract FIPS-204
    `polyw1_pack` encoding tie is `mldsaW1PackFold_eq_byteEncode`. -/
theorem mldsaW1Pack_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaW1PackSrc = some prog ∧
      ∀ (a0 a1 : BitVec 64),
        prog.denote (inputValuation 64 2 ![a0, a1])
          = mldsaW1PackFold a0 a1 := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaW1PackSrc).get
    mldsaW1Pack_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a0", "a1"] mldsaW1PackSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a0 a1
  have hspec : ImpExpr.denoteScalar ["a0", "a1"] ![a0, a1]
      mldsaW1PackSrc (fun _ => none)
        = some (mldsaW1PackFold a0 a1) := by
    have h := mldsaW1PackSrc_denoteScalar (nIn := 2) ![a0, a1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a0", "a1"]
    ![a0, a1] mldsaW1PackSrc _ hc hspec

/-! ## The abstract FIPS-204 `polyw1_pack` encoding tie

The emit form `mldsaW1PackFold` equals the FIPS-204 `polyw1_pack` byte
`a0 ||| (a1 << 4)` on the 4-bit coefficient domain `a0, a1 < 2^4`. On this domain
the contributing bits are exactly `a0[3:0]` (the low nibble) in positions `[3:0]`
and `a1[3:0]` in positions `[7:4]`, so the two nibbles are disjoint, the `0xff`
mask is exact, and there is no loss and no overlap. -/

/-- **ML-DSA `polyw1_pack` form = FIPS-204 4-bit bit-pack byte** on the coefficient
    domain `a0, a1 < 2^4`. Ties the emitted closed form `mldsaW1PackFold` (the
    `_compiles` deliverable) to the explicit packed byte: `a0` (the low `w1`
    coefficient) in bit positions `[3:0]` and `a1` (the high coefficient) in bit
    positions `[7:4]`. On the 4-bit domain the two contributions are disjoint and
    the `0xff` mask is exact. Closed by `bv_decide` (pure `BitVec`, bounded
    inputs). -/
theorem mldsaW1PackFold_eq_byteEncode (a0 a1 : BitVec 64)
    (ha0 : a0 < 0x10#64) (ha1 : a1 < 0x10#64) :
    mldsaW1PackFold a0 a1 = a0 ||| (a1 <<< (4 : Nat)) := by
  unfold mldsaW1PackFold
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaPack
