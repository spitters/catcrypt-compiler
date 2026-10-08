/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.MLKEM.LeafForms

/-!
# C4 fan-out: the verified compiler emits an ML-KEM `poly_frombytes` 12-bit unpack

This module extends the **C4** step of the verified-compiler plan to the
**ML-KEM-768** (FIPS-203) polynomial byte-**deserialization** primitive
`poly_frombytes`. It is the compile-from-hax sibling of the NTT-domain owned-emit
layer in `CatCrypt/Crypto/MLKEM/PolyEmit.lean`, here covering the 12-bit
coefficient unpack (the `ByteEncode₁₂⁻¹` step that consumes the serialized
secret-key / public-key polynomials).

## `poly_frombytes` (the clean, logical-shift-only body)

FIPS-203 `ByteDecode₁₂` reads a coefficient **pair** `(c0, c1)` from three bytes
`(b0, b1, b2)`, matching PQClean (`ml-kem-768/clean`, `polyvec.c` /
`poly_frombytes`):

```c
c0 = (b0 | ((uint16_t)b1 << 8)) & 0xFFF;
c1 = ((b1 >> 4) | ((uint16_t)b2 << 4)) & 0xFFF;
```

i.e. the high coefficient `c1 = ((b1 >> 4) | (b2 << 4)) & 0xFFF`. This is pure
`shift_right` / `shift_left` / `BitOr` / `BitAnd` — all **logical** shifts (the
inputs are unsigned bytes), a single straight-line output. We derive the high
coefficient `c1`, the body that exercises the full
`shift_right` + `shift_left` + `BitOr` recognizer chain (the low coefficient `c0`
is a strict sub-case: `b0 | (b1 << 8)`).

### Why this body (shift kind)

Every shift here is a **logical** right/left shift on an unsigned byte/`u16`
operand (`b1 >> 4`, `b2 << 4`), so this body is squarely in scope: the front's
`shift_right`/`shift_left` recognizers (`recogShift → .shr`/`.shl`) and the
`BitOr` recognizer (`recogBin → .or`) cover it with **no front change**. (Contrast
ML-DSA `reduce32`, whose `>> 23` on a *signed* `int32` is an arithmetic shift —
that one needs `sar`. ML-KEM `frombytes` has no `sar`.)

The form `LeafForms.mlkemFrombytesC1Form` is the closed `BitVec 32` body the source
denotes to; `mlkemFrombytesC1_compiles` routes the `rfl` source-spec
(`mlkemFrombytesC1Src_denoteScalar`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`, so the emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the form. An abstract tie that the body
recovers the exact 12-bit field-element `c1` from `(b1, b2)` on the byte domain
is `LeafForms.mlkemFrombytesC1Form_eq_decode`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemSerial

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)
open CatCrypt.Crypto.MLKEM.LeafForms (mlkemFrombytesC1Form)

/-! ## The ML-KEM `poly_frombytes` high-coefficient source — `w = 32`, params `["b1","b2"]` -/

/-- The ML-KEM-768 `poly_frombytes` high-coefficient unpack source as a hax
    `ImpExpr`, fully let-normalized, parameters `["b1","b2"]` (`nIn = 2`;
    `I 0 = b1`, `I 1 = b2`). The 12-bit output mask `0xFFF` is a pre-bound local
    (binary-ALU literal operands must be `let`-bound under the front's ANF
    discipline); the `shift_right`/`shift_left` counts `4` stay literal.
    Body: `((b1 >> 4) | (b2 << 4)) & 0xFFF`. Returns the coefficient register `r`. -/
def mlkemFrombytesC1Src : ImpExpr :=
  .letBind "cMask" (.lit (.int 0xFFF))
   -- hi := b1 >> 4
   (.letBind "hi" (.app "shift_right" [.var "b1", .lit (.int 4)])
    -- lo := b2 << 4
    (.letBind "lo" (.app "shift_left" [.var "b2", .lit (.int 4)])
     -- w := hi | lo
     (.letBind "w" (.app "BitOr" [.var "hi", .var "lo"])
      -- r := w & 0xFFF
      (.letBind "r" (.app "BitAnd" [.var "w", .var "cMask"])
       (.var "r")))))

/-- The ML-KEM `poly_frombytes` source denotes (under `denoteScalar`, parameters
    `["b1","b2"]`) to the closed emit form `mlkemFrombytesC1Form`, reading
    `b1 = inpGet I 0`, `b2 = inpGet I 1`. The closed let-normalized body reduces
    definitionally: `shift_right 4` is `>>> 4`, `shift_left 4` is `<<< 4`,
    `BitOr` is `|||`, `BitAnd` is `&&&`. -/
theorem mlkemFrombytesC1Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["b1", "b2"] I mlkemFrombytesC1Src (fun _ => none)
      = some (mlkemFrombytesC1Form (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the ML-KEM `poly_frombytes`
    high-coefficient body (`w = 32`, two parameters). -/
theorem mlkemFrombytesC1_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 2) ["b1", "b2"] mlkemFrombytesC1Src).isSome := by
  native_decide

/-- **ML-KEM-768 `poly_frombytes` high-coefficient (12-bit unpack) emitted by the
    verified compiler.** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["b1","b2"] mlkemFrombytesC1Src = some c`, and for every byte
    pair `(b1, b2)`, `c`'s `BitVec 32` denotation (under the input valuation
    `![b1, b2]`) is exactly the closed emit form `mlkemFrombytesC1Form`
    (`((b1 >> 4) | (b2 << 4)) & 0xFFF`). Routed through the C3 per-primitive
    obligation `compileFromHax_meets_spec`. This is a C4 fan-out to the **ML-KEM
    polynomial byte deserialization** primitive, reusing the SHA-256/Keccak/BLAKE2
    `shift_right`/`shift_left`/`BitOr`/`BitAnd` recognizers (all *logical* shifts —
    no `sar`) with no front change. The abstract 12-bit decode tie is
    `mlkemFrombytesC1Form_eq_decode`. -/
theorem mlkemFrombytesC1_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 2 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 2) ["b1", "b2"] mlkemFrombytesC1Src = some prog ∧
      ∀ (b1 b2 : BitVec 32),
        prog.denote (inputValuation 32 2 ![b1, b2])
          = mlkemFrombytesC1Form b1 b2 := by
  set prog := (compileFromHax (w := 32) (nIn := 2) ["b1", "b2"] mlkemFrombytesC1Src).get
    mlkemFrombytesC1_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 2) ["b1", "b2"] mlkemFrombytesC1Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro b1 b2
  have hspec : ImpExpr.denoteScalar ["b1", "b2"] ![b1, b2]
      mlkemFrombytesC1Src (fun _ => none)
        = some (mlkemFrombytesC1Form b1 b2) := by
    exact mlkemFrombytesC1Src_denoteScalar (nIn := 2) ![b1, b2]
  exact compileFromHax_meets_spec (w := 32) (nIn := 2) ["b1", "b2"]
    ![b1, b2] mlkemFrombytesC1Src _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemSerial
