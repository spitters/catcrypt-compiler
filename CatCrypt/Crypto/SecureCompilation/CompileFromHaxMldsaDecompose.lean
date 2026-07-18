/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ML-DSA-65 `power2round` rounding body

This module extends the **C4** step of the verified-compiler plan to the
**FIPS-204 rounding** family: ML-DSA-65's `power2round` (the bit-splitting
rounding pass of Dilithium). The C4 SHA-256 leaves (`CompileFromHaxLeaves`),
the Keccak `χ`/`θ`/`ι` lanes (`CompileFromHaxKeccak`), the BLAKE2s `G` step
(`CompileFromHaxBlake2`), the SDitH GF(251) prime-field multiply
(`CompileFromHaxSdithGf251`), and the MAYO GF(16) field multiply
(`CompileFromHaxMayoGf16`) showed `compileFromHax` *emitting* crypto leaves for
the bitwise, ARX, prime-field, and binary-field families. Here we do the same
for a **post-quantum signature rounding leaf**, the per-coefficient
straight-line shift/add/sub split that `MLDSA/Power2RoundOwnedEmit.lean` lowers
through the owned X86 loop backend — now derived through the *same* verified
`compileFromHax` front as the other C4 leaves, with no front change.

## FIPS-204 §7.4 `Power2Round` (ML-DSA-65: q = 8380417, D = 13)

Transcribed **verbatim** from PQClean `ml-dsa-65/clean/rounding.c`:

```c
int32_t power2round(int32_t *a0, int32_t a) {
    int32_t a1 = (a + (1 << (D - 1)) - 1) >> D;   // (a + 4095) >> 13
    *a0 = a - (a1 << D);                            // a - (a1 << 13)
    return a1;
}
```

`Power2Round(a) = (a1, a0)` splits a standard representative `a ∈ [0, q)` so that
`a = a1·2^D + a0` with `a0 ∈ (−2^{D−1}, 2^{D−1}]` the **centered** low part. Here
`D = 13`, `2^{D−1} − 1 = 4095`, `2^D = 8192`. `a1 = ⌊(a + 4095)/8192⌋` is the
rounded high part (a non-negative logical shift, since `a + 4095 < q + 4095 <
2^{23}`, so `shr`/`sar` agree); `a0 = a − a1·8192` is the signed two's-complement
low part (carried in the owned `BitVec 64` as its two's-complement word, which is
exactly `wrapping_sub` mod `2^64`).

## Why this is `compileFromHax`-emittable on the recognizer set

Every op is in the front's recognizer set used by the SHA-256/Keccak/BLAKE2/SDitH
leaves: `wrapping_add` (`a + 4095`), `shift_right` (`>> 13`, logical — all values
non-negative), `shift_left` (`a1 << 13`), and `wrapping_sub` (`a − …`). The shift
counts are literals; the addend `4095` is pre-bound to a local (binary-ALU literal
operands must be `let`-bound under the front's ANF discipline). **No change to the
verified front is required** — this reuses the SDitH/SHA-256 recognizers.

## Method (mirrors `CompileFromHaxSdithGf251.gf251Mul_compiles`)

We derive **two** single-output bodies through the pipeline (`power2round` has two
outputs; each is a clean single-register straight line):

* `power2roundA1Src` → `power2roundA1Spec` (the high part `a1`, pure add/shr);
* `power2roundA0Src` → `power2roundA0Spec` (the low part `a0`, the two's-complement
  `a − (a1 << 13)`).

For each, `_denoteScalar` is a `rfl` (the source and the spec are the *same* closed
term: `wrapping_add` is `+`, `shift_right n` is `>>> n`, `shift_left n` is `<<< n`,
`wrapping_sub` is `-`), `_compileFromHax_isSome` is `native_decide`, and `_compiles`
routes the source-spec through the C3 per-primitive obligation
`compileFromHax_meets_spec`. The emitted jasmin `Com` is *computed by the verified
compiler* and proven equal to the FIPS-204 rounding form.

## The reconstruction tie (FIPS-204 rounding identity, via `bv_decide`)

`power2roundReconstruct_eq` ties the two emitted forms together with the defining
`power2round` identity `a1·2^D + a0 = a` (mod `2^64`) over the standard-representative
domain `a < q` — the genuine rounding-correctness fact (the SDitH-lesson pure-BitVec
`bv_decide` tie, the rounding analogue of the GF(251) Solinas-fold seam), not an
ARX `rfl`. The spec forms match `Power2RoundOwnedEmit.refA1`/`refA0Bits`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecompose

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The `power2round` high-part source — `w = 64`, parameter `["a"]` -/

/-- The `power2round` high-part `a1 = (a + 4095) >> 13` as a hax `ImpExpr`, fully
    let-normalized, parameter `["a"]` (`nIn = 1`; `I 0 = a`). The rounding addend
    `4095 = 2^{D−1} − 1` is pre-bound to a local; the shift count `13 = D` stays a
    literal. `wrapping_add` is recognized as `+`, `shift_right` as logical `>>>`. -/
def power2roundA1Src : ImpExpr :=
  .letBind "c4095" (.lit (.int 4095))
   (.letBind "s" (.app "wrapping_add" [.var "a", .var "c4095"])
    (.letBind "a1" (.app "shift_right" [.var "s", .lit (.int 13)])
     (.var "a1")))

/-- The closed high-part emit form the source denotes to, at `w = 64`:
    `a1 = (a + 4095) >>> 13`. Matches `Power2RoundOwnedEmit.refA1` (with the
    public schedule inlined as the abstract input `a`). -/
def power2roundA1Spec (a : BitVec 64) : BitVec 64 :=
  (a + 4095) >>> (13 : Nat)

/-- The high-part source denotes (under `denoteScalar`, parameter `["a"]`) to the
    closed form `power2roundA1Spec`, reading `a = inpGet I 0`. A `rfl`: the source
    and the spec are the same closed term. -/
theorem power2roundA1Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I power2roundA1Src (fun _ => none)
      = some (power2roundA1Spec (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the `power2round` high part
    (`w = 64`, one parameter). -/
theorem power2roundA1_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA1Src).isSome := by
  native_decide

/-- **ML-DSA-65 `power2round` high part emitted by the verified compiler.** There is
    a compiled `Com jasminDialect` `c` with `compileFromHax ["a"] power2roundA1Src
    = some c`, and for every `a`, `c`'s `BitVec 64` denotation (under the input
    valuation `![a]`) is exactly the FIPS-204 high-part form
    `a1 = (a + 4095) >>> 13`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`. C4 fan-out to the post-quantum signature **rounding**
    family, reusing the SHA-256/Keccak/BLAKE2/SDitH `wrapping_add`/`shift_right`
    recognizers with no front change. -/
theorem power2roundA1_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA1Src = some prog ∧
      ∀ (a : BitVec 64),
        prog.denote (inputValuation 64 1 ![a])
          = power2roundA1Spec a := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA1Src).get
    power2roundA1_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA1Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a]
      power2roundA1Src (fun _ => none) = some (power2roundA1Spec a) := by
    have h := power2roundA1Src_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"]
    ![a] power2roundA1Src _ hc hspec

/-! ## The `power2round` low-part source — `w = 64`, parameter `["a"]` -/

/-- The `power2round` low-part `a0 = a − (a1 << 13)` (where `a1 = (a + 4095) >> 13`)
    as a hax `ImpExpr`, fully let-normalized, parameter `["a"]`. The whole split is
    a single straight line: compute `a1`, shift it left by `D = 13`, subtract from
    `a`. `wrapping_add`/`wrapping_sub` are `+`/`-`, `shift_right`/`shift_left` are
    `>>>`/`<<<`; `wrapping_sub` is two's-complement subtraction mod `2^64`. -/
def power2roundA0Src : ImpExpr :=
  .letBind "c4095" (.lit (.int 4095))
   (.letBind "s" (.app "wrapping_add" [.var "a", .var "c4095"])
    (.letBind "a1" (.app "shift_right" [.var "s", .lit (.int 13)])
     (.letBind "a1s" (.app "shift_left" [.var "a1", .lit (.int 13)])
      (.letBind "a0" (.app "wrapping_sub" [.var "a", .var "a1s"])
       (.var "a0")))))

/-- The closed low-part emit form the source denotes to, at `w = 64`:
    `a0 = a − (((a + 4095) >>> 13) <<< 13)`, the two's-complement low part.
    Matches `Power2RoundOwnedEmit.refA0Bits` (with the public schedule inlined as
    the abstract input `a`). -/
def power2roundA0Spec (a : BitVec 64) : BitVec 64 :=
  a - (((a + 4095) >>> (13 : Nat)) <<< (13 : Nat))

/-- The low-part source denotes (under `denoteScalar`, parameter `["a"]`) to the
    closed form `power2roundA0Spec`, reading `a = inpGet I 0`. A `rfl`. -/
theorem power2roundA0Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a"] I power2roundA0Src (fun _ => none)
      = some (power2roundA0Spec (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the `power2round` low part
    (`w = 64`, one parameter). -/
theorem power2roundA0_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA0Src).isSome := by
  native_decide

/-- **ML-DSA-65 `power2round` low part emitted by the verified compiler.** There is
    a compiled `Com jasminDialect` `c` with `compileFromHax ["a"] power2roundA0Src
    = some c`, and for every `a`, `c`'s `BitVec 64` denotation (under the input
    valuation `![a]`) is exactly the FIPS-204 low-part form
    `a0 = a − (((a + 4095) >>> 13) <<< 13)`. Routed through the C3 per-primitive
    obligation `compileFromHax_meets_spec`. The two's-complement low part is the
    genuinely-signed content (the centered `a0 ∈ (−2^{D−1}, 2^{D−1}]`), realised by
    `wrapping_sub` mod `2^64` exactly as the owned `x86_SUB`. -/
theorem power2roundA0_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA0Src = some prog ∧
      ∀ (a : BitVec 64),
        prog.denote (inputValuation 64 1 ![a])
          = power2roundA0Spec a := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA0Src).get
    power2roundA0_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA0Src
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a
  have hspec : ImpExpr.denoteScalar ["a"] ![a]
      power2roundA0Src (fun _ => none) = some (power2roundA0Spec a) := by
    have h := power2roundA0Src_denoteScalar (nIn := 1) ![a]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["a"]
    ![a] power2roundA0Src _ hc hspec

/-! ## The FIPS-204 reconstruction tie (`a1·2^D + a0 = a`, via `bv_decide`)

The two emitted forms satisfy the defining `power2round` identity: the high part
times `2^D` plus the low part reconstructs the input `a`, over the
standard-representative domain `a < q`. This is the genuine rounding-correctness
fact — the rounding analogue of the GF(251) Solinas-fold seam, proved as a pure
`BitVec 64` `bv_decide` over the constrained domain (the SDitH lesson). -/

/-- **`power2round` reconstruction:** `a1·2^D + a0 = a` (mod `2^64`) on the
    standard-representative domain `a < q = 8380417`, where `a1 = power2roundA1Spec a`
    is the emitted high part and `a0 = power2roundA0Spec a` is the emitted low part.
    Ties the two `_compiles` deliverables to the defining FIPS-204 §7.4 splitting
    identity. Since `a1 << 13 = a1·2^D` exactly (the multiply never wraps for
    `a < q`), and `a0 = a − (a1 << 13)`, the sum telescopes to `a`. -/
theorem power2roundReconstruct_eq (a : BitVec 64) (ha : a < 8380417#64) :
    (power2roundA1Spec a) <<< (13 : Nat) + power2roundA0Spec a = a := by
  unfold power2roundA1Spec power2roundA0Spec
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecompose
