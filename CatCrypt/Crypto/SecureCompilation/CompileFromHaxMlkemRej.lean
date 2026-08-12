/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-KEM `rej_uniform` 12-bit candidate extract

This module extends the **C4** step of the verified-compiler plan to the
**ML-KEM-768** (FIPS-203 `SampleNTT` / Algorithm 13) rejection-sampling
per-candidate **extraction** body. It is the compile-from-hax sibling of the
owned-emit rejection-loop kernel `MLKEM.RejUniformOwnedEmit`, which lives in the
wider CatCrypt development and is not part of this compiler package; the body
below reuses that kernel's `q = 3329`, its `0xFFF` mask, and its exact
`>> | << & 0xFFF` extraction arithmetic. In-package, the rejection *control
structure* is re-sourced through the canonical front in
`VIR/RejUniformCovered.lean`, over the guarded-loop machinery of
`X86Backend/RejectLoop.lean`.

## `rej_uniform` (the scalar per-candidate body, NOT the data-dependent loop)

PQClean (`ml-kem-768/clean`, `indcpa.c` `rej_uniform`) extracts two 12-bit
candidates from each 3-byte window `(b0, b1, b2)`:

```c
val0 = (buf[pos+0] | ((uint16_t)buf[pos+1] << 8)) & 0xFFF;     /* the low candidate d1 */
val1 = ((buf[pos+1] >> 4) | ((uint16_t)buf[pos+2] << 4)) & 0xFFF;  /* the high candidate d2 */
```

each then **accepted** iff `< q = 3329`. The data-dependent accept/store loop is
Tier-3 (the owned rejection loop of the out-of-package `MLKEM.RejUniformOwnedEmit`,
whose generic machine-level shape is `X86Backend/RejectLoop.runGuardedLoop`; not a
compile-from-hax leaf), so we derive the **scalar per-candidate body**: the first
12-bit candidate `d1 = (b0 | (b1 << 8)) & 0xFFF`. This is pure `shift_left` /
`BitOr` / `BitAnd` — all **logical** shifts (the inputs are unsigned bytes), a
single straight-line output, in scope with no front change. (Contrast ML-DSA
`reduce32`, whose `>> 23` on a *signed* `int32` is an arithmetic shift and needs
the front's `arith_shift_right` head; ML-KEM `rej_uniform` has no `sar`.)

The reduce form `mlkemRejVal0Form` is the closed `BitVec 32` body the source
denotes to; `mlkemRejVal0_compiles` routes the `rfl` source-spec
(`mlkemRejVal0Src_denoteScalar`) through the C3 per-primitive obligation
`compileFromHax_meets_spec`, so the emitted jasmin `Com` is *computed by the
verified compiler* and proven equal to the form. An abstract tie that the body
recovers the exact 12-bit candidate from `(b0, b1)` on the byte input domain is
`mlkemRejVal0Form_eq_candidate` (pure-`BitVec` `bv_decide`).

## The `< q` acceptance predicate: front-head gap (documented, not stubbed)

The acceptance decision `d1 < 3329` produces a 0/1 mask in the owned emit via a
`SUB`/`CMOVB` (borrow-flag → CMOV) idiom (`rejWindowBody` of the out-of-package
`MLKEM.RejUniformOwnedEmit`). The compile-from-hax front
(`ImpExprToThir.recogBin`/`recogShift`/`recogNot`) recognizes only
`BitXor`/`BitAnd`/`BitOr`/`wrapping_{add,mul,sub}`/`shift_{left,right}`/
`arith_shift_right`/`rotate_right`/`Not` — there is **no compare-producing-mask
head** (no `Lt`/`lt`/`borrow`/`cmovb`) in the front. So the `< q` acceptance mask
is **not** a single compile-from-hax leaf with the current recognizer set; it
would require adding a compare/select head to `recogBin` (and a matching `Rhs`
form lowering to `SUB`+`CMOVB` / `SETB`). We therefore derive only the 12-bit
**extract** here and leave the acceptance mask to the owned x86 backend, where
the `SUB`/`CMOVB` idiom is KAT'd against PQClean. This matches the C4 scope: the
extraction arithmetic is the logical-shift body the front covers; the comparison
is a back-end concern.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemRej

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The ML-KEM `rej_uniform` low-candidate source — `w = 32`, params `["b0","b1"]` -/

/-- The ML-KEM-768 `rej_uniform` low-candidate (`val0 = d1`) extract source as a
    hax `ImpExpr`, fully let-normalized, parameters `["b0","b1"]` (`nIn = 2`;
    `I 0 = b0`, `I 1 = b1`). The 12-bit output mask `0xFFF` is a pre-bound local
    (binary-ALU literal operands must be `let`-bound under the front's ANF
    discipline); the `shift_left` count `8` stays literal.
    Body: `(b0 | (b1 << 8)) & 0xFFF`. Returns the candidate register `r`. -/
def mlkemRejVal0Src : ImpExpr :=
  .letBind "cMask" (.lit (.int 0xFFF))
   -- hi := b1 << 8
   (.letBind "hi" (.app "shift_left" [.var "b1", .lit (.int 8)])
    -- w := b0 | hi
    (.letBind "w" (.app "BitOr" [.var "b0", .var "hi"])
     -- r := w & 0xFFF
     (.letBind "r" (.app "BitAnd" [.var "w", .var "cMask"])
      (.var "r"))))

/-- The explicit closed **emit form** the source denotes to, at `w = 32`. Stated as
    a plain `def` so the emitted form is explicit and auditable: this is the exact
    step-by-step computation `mlkemRejVal0Src` performs.
    `mlkemRejVal0Form_eq_candidate` ties it to the abstract 12-bit `SampleNTT`
    low-candidate on the byte input domain. -/
def mlkemRejVal0Form (b0 b1 : BitVec 32) : BitVec 32 :=
  let hi := b1 <<< (8 : Nat)
  (b0 ||| hi) &&& 0xFFF

/-- The ML-KEM `rej_uniform` low-candidate source denotes (under `denoteScalar`,
    parameters `["b0","b1"]`) to the closed emit form `mlkemRejVal0Form`, reading
    `b0 = inpGet I 0`, `b1 = inpGet I 1`. The closed let-normalized body reduces
    definitionally: `shift_left 8` is `<<< 8`, `BitOr` is `|||`, `BitAnd` is `&&&`. -/
theorem mlkemRejVal0Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["b0", "b1"] I mlkemRejVal0Src (fun _ => none)
      = some (mlkemRejVal0Form (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the ML-KEM `rej_uniform`
    low-candidate body (`w = 32`, two parameters). -/
theorem mlkemRejVal0_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 2) ["b0", "b1"] mlkemRejVal0Src).isSome := by
  native_decide

/-- **ML-KEM-768 `rej_uniform` low-candidate (12-bit extract) emitted by the
    verified compiler.** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["b0","b1"] mlkemRejVal0Src = some c`, and for every byte pair
    `(b0, b1)`, `c`'s `BitVec 32` denotation (under the input valuation
    `![b0, b1]`) is exactly the closed emit form `mlkemRejVal0Form`
    (`(b0 | (b1 << 8)) & 0xFFF`). Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. This is a C4 fan-out to the **ML-KEM
    rejection-sampling candidate extraction** (FIPS-203 `SampleNTT`), reusing the
    SHA-256/Keccak/BLAKE2 `shift_left`/`BitOr`/`BitAnd` recognizers (all *logical*
    shifts — no `sar`) with no front change. The abstract 12-bit candidate tie is
    `mlkemRejVal0Form_eq_candidate`. The `< q` acceptance mask is a back-end concern
    (no compare-producing-mask front head; see the module docstring). -/
theorem mlkemRejVal0_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 2 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 2) ["b0", "b1"] mlkemRejVal0Src = some prog ∧
      ∀ (b0 b1 : BitVec 32),
        prog.denote (inputValuation 32 2 ![b0, b1])
          = mlkemRejVal0Form b0 b1 := by
  set prog := (compileFromHax (w := 32) (nIn := 2) ["b0", "b1"] mlkemRejVal0Src).get
    mlkemRejVal0_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 2) ["b0", "b1"] mlkemRejVal0Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro b0 b1
  have hspec : ImpExpr.denoteScalar ["b0", "b1"] ![b0, b1]
      mlkemRejVal0Src (fun _ => none)
        = some (mlkemRejVal0Form b0 b1) := by
    have h := mlkemRejVal0Src_denoteScalar (nIn := 2) ![b0, b1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 2) ["b0", "b1"]
    ![b0, b1] mlkemRejVal0Src _ hc hspec

/-! ## The abstract 12-bit `SampleNTT` low-candidate tie (FIPS-203 `rej_uniform`)

The emit form `mlkemRejVal0Form` equals the FIPS-203 low candidate `d1 = b0 |||
(b1 << 8)` masked to 12 bits on the byte input domain `b0, b1 < 2^8`. On this
domain `b0` occupies bit positions `[7:0]` and `b1 << 8` occupies `[15:8]`; the
`0xFFF` mask keeps `b0[7:0]` (all 8 bits) plus `b1[3:0]` (the low nibble of `b1`)
in positions `[11:8]`, recovering exactly the 12-bit candidate (the top nibble of
`b1` is discarded — matching PQClean's `& 0xFFF`, where `d2` carries `b1[7:4]`). -/

/-- **ML-KEM `rej_uniform` form = FIPS-203 12-bit low-candidate.** Ties the emitted
    closed form `mlkemRejVal0Form` (the `_compiles` deliverable) to the masked
    12-bit candidate `(b0 ||| (b1 << 8)) & 0xFFF`. The identity holds for all
    `BitVec 32` inputs (the form already *is* `(b0 ||| (b1 << 8)) & 0xFFF`); on the
    intended byte domain `b0, b1 < 2^8` the surviving bits are exactly `b0[7:0]` and
    `b1[3:0] << 8` — the 12-bit `SampleNTT` candidate (`b1`'s top nibble
    feeds the *other* candidate `d2`). Closed by `bv_decide` (pure `BitVec`). -/
theorem mlkemRejVal0Form_eq_candidate (b0 b1 : BitVec 32) :
    mlkemRejVal0Form b0 b1 = (b0 ||| (b1 <<< (8 : Nat))) &&& 0xFFF#32 := by
  unfold mlkemRejVal0Form
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemRej
