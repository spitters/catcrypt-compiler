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
# C4 fan-out: the verified compiler emits the ML-KEM `decompress_d` per-coefficient body

This module extends the **C4** step of the verified-compiler plan to the
**ML-KEM-768** (FIPS-203) ciphertext (de)serialization rounding primitive
`Decompress_d`. It is the compile-from-hax sibling of the owned-emit kernel in
`CatCrypt/Crypto/MLKEM/CompressEmit.lean` (reuses its constants and the
`polyvec_decompress`, `du = 10`, reference arithmetic verbatim).

## `Decompress_d` (the clean, logical-shift-only body)

FIPS-203 `Decompress_d(y) = round(y·q / 2^d) = (y·q + 2^(d-1)) >> d`, computed by
PQClean (`ml-kem-768/clean`, `polyvec.c`) on a 10-bit coefficient `t` as

```c
coeff = ((t & 0x3ff) * KYBER_Q + 512) >> 10;     /* du = 10, KYBER_Q = 3329 */
```

i.e. `((t & 0x3ff)·3329 + 512) >>> 10`. This is pure `BitAnd` / `wrapping_mul` /
`wrapping_add` / `shift_right`, a single straight-line output — the simplest
ML-KEM (de)compress body, and the one chosen here.

### Why decompress and not compress (shift kind)

`Compress_d` uses the reciprocal multiply `((x<<d)+1665)·magic >> sh & mask` plus
a Barrett `mod q` (`CompressEmit.reduceModQ`); every one of its shifts is a
**logical** right shift (`d0 >>= 28` / `>>= 32` on unsigned `u32`/`u64`), so
compress is **NOT** sar-blocked — but it is a much longer body (multi-op reduce +
magic). `Decompress_d` is the single clean mul+add+logical-shift body, so we
derive it. (Contrast ML-DSA `reduce32`, whose `>> 23` on a *signed* `int32` is an
arithmetic shift — the front has no `sar` recognizer, so that one *is* sar-blocked.
ML-KEM decompress has no `sar`.)

The form `LeafForms.mlkemDecompress10Form` is the closed `BitVec 64` body the source
denotes to; `mlkemDecompress10_compiles` routes the `rfl` source-spec
(`mlkemDecompress10Src_denoteScalar`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`, so the emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the form. An abstract `round(y·q / 2^d)`
tie over the `t < 2^10` input domain is `LeafForms.mlkemDecompress10Form_eq_round`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemCompress

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)
open CatCrypt.Crypto.MLKEM.LeafForms (mlkemDecompress10Form)

/-! ## The ML-KEM `decompress_10` source — `w = 64`, parameter `["t"]` -/

/-- The ML-KEM-768 `polyvec_decompress` (`du = 10`) per-coefficient source as a
    hax `ImpExpr`, fully let-normalized, parameter `["t"]` (`nIn = 1`; `I 0 = t`).
    Constants `q = 3329`, the round-add `2^(d-1) = 512`, and the input mask
    `0x3ff` are pre-bound locals (binary-ALU literal operands must be `let`-bound
    under the front's ANF discipline); the `shift_right` count `10` stays literal.
    Body: `((t & 0x3ff)·q + 512) >> 10`. Returns the coefficient register `r`. -/
def mlkemDecompress10Src : ImpExpr :=
  .letBind "cMask" (.lit (.int 0x3ff))
   (.letBind "cQ" (.lit (.int 3329))
    (.letBind "cRound" (.lit (.int 512))
  -- m := t & 0x3ff
  (.letBind "m" (.app "BitAnd" [.var "t", .var "cMask"])
   -- mq := m * q
   (.letBind "mq" (.app "wrapping_mul" [.var "m", .var "cQ"])
    -- s := mq + 512
    (.letBind "s" (.app "wrapping_add" [.var "mq", .var "cRound"])
     -- r := s >> 10
     (.letBind "r" (.app "shift_right" [.var "s", .lit (.int 10)])
      (.var "r")))))))

/-- The ML-KEM decompress source denotes (under `denoteScalar`, parameter `["t"]`)
    to the closed emit form `mlkemDecompress10Form`, reading `t = inpGet I 0`. The
    closed let-normalized body reduces definitionally: `BitAnd` is `&&&`,
    `wrapping_mul` is `*`, `wrapping_add` is `+`, `shift_right 10` is `>>> 10`. -/
theorem mlkemDecompress10Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["t"] I mlkemDecompress10Src (fun _ => none)
      = some (mlkemDecompress10Form (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the ML-KEM decompress coefficient
    body (`w = 64`, one parameter). -/
theorem mlkemDecompress10_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["t"] mlkemDecompress10Src).isSome := by
  native_decide

/-- **ML-KEM-768 `decompress_10` per-coefficient body emitted by the verified
    compiler.** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["t"] mlkemDecompress10Src = some c`, and for every `t`, `c`'s
    `BitVec 64` denotation (under the input valuation `![t]`) is exactly the closed
    emit form `mlkemDecompress10Form` (`((t & 0x3ff)·3329 + 512) >> 10`). Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. This is a
    C4 fan-out to the **ML-KEM ciphertext deserialization** rounding primitive,
    reusing the SHA-256/Keccak/BLAKE2/GF(251)
    `BitAnd`/`wrapping_mul`/`wrapping_add`/`shift_right` recognizers (all *logical*
    shifts — no `sar`) with no front change. The abstract `round(y·q / 2^d)` tie
    is `mlkemDecompress10Form_eq_round`. -/
theorem mlkemDecompress10_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["t"] mlkemDecompress10Src = some prog ∧
      ∀ (t : BitVec 64),
        prog.denote (inputValuation 64 1 ![t])
          = mlkemDecompress10Form t := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["t"] mlkemDecompress10Src).get
    mlkemDecompress10_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["t"] mlkemDecompress10Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro t
  have hspec : ImpExpr.denoteScalar ["t"] ![t]
      mlkemDecompress10Src (fun _ => none) = some (mlkemDecompress10Form t) := by
    exact mlkemDecompress10Src_denoteScalar (nIn := 1) ![t]
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["t"]
    ![t] mlkemDecompress10Src _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemCompress
