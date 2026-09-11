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
# C4 fan-out: the verified compiler emits a SNOVA GF(16) multiply from extracted source

This module extends the **C4** step of the verified-compiler plan to SNOVA (NIST
additional-signatures Round; UOV over the non-commutative matrix ring
`R = Mat_l(GF(16))`, `GF(16) = GF(2)[x]/(x⁴+x+1)`, rank `l = matDim = 2`, oil
`o = 4`). SNOVA verifies a signature by **evaluating the public map** over `R`;
with the ring multiply unfolded to its GF(16) entries, every output cell is the
schoolbook GF(16) multiply-accumulate sweep
`out[r][c] = Σ_J Σ_k A_J[r][k] · v_J[k][c]` (`SNOVA/VerifyEmit.lean`'s
`gf16BitStep`/`gf16MulInline`).

SNOVA uses the **same** GF(16) field as MAYO (`SNOVA/VerifyEmit.lean`'s
`GF16 = GF(2)[x]/(x⁴+x+1)` matches `MAYO/VerifyEmit.lean`), and the
per-element multiply is the **same** 4-step bit-serial shift-and-conditional-xor
with the same reduce constant (`0x3 = x+1`, since `x⁴ ≡ x+1`) and the same
branch-free `0 − bit` mask — its KAT vectors `7·11 = 4` and `3·6 = 0xa` are
byte-identical (`SNOVA.VerifyEmit.gf16Mac_value`/`gf16Mac_value2`). So the
scalar GF(16) leaf the SNOVA ring-dot is built from is a direct port of
`CompileFromHaxMayoGf16.gf16Mul_compiles` (the matrix-ring/rank only set the
**index walk** that selects `m = A_J[r][k]` and `v = v_J[k][c]` per term; the
field arithmetic per term is ordinary GF(16)).

## GF(16) multiply (the bit-serial straight-line)

The product `a · b` over the low nibble is the standard 4-step shift-and-
conditional-xor with reduction: for each bit `k = 0..3` of `b`, conditionally XOR
the running shifted multiplicand `sh` into the accumulator `r` if bit `k` is set,
then `xtime(sh)` (multiply `sh` by `x`, reducing modulo `x⁴+x+1`). This is exactly
`SNOVA.VerifyEmit.gf16BitStep` (and `MAYO`'s).

The conditional XOR and the conditional reduce are both done **branch-free** via a
mask `mask = 0 − bit` (`0x0` or all-ones). The front exposes `BitAnd`/`BitXor`/
`Shl`/`Shr`/`wrapping_add` but **no subtract/negate**, so the two's-complement
mask `0 − bit` is materialized as `(bit ^ ones) + 1` (`~bit + 1`): for `bit = 0`
this is `0`, for `bit = 1` it is `0xFFFFFFFF = allOnes`. Mask/poly/ones constants
are first bound to their own locals.

## Method (mirrors `CompileFromHaxMayoGf16.gf16Mul_compiles`)

Every step is `BitAnd`/`BitXor`/`Shl`/`Shr`/`wrapping_add` over the low nibble —
the same recognizer chain as the SHA-256/Keccak/BLAKE2/MAYO leaves. **No change to
the verified front is required.** The source is fully let-normalized (one operator
per `letBind`, all arguments atoms or earlier locals), so the leaf follows the C3
obligation:

1. `snovaGf16MulSrc` — a let-normalized `ImpExpr` source.
2. `snovaGf16MulSpec` — the bit-serial closed form the source computes, stated in
   the exact `· ^^^ (· &&& mask)`-shifted form the source emits, so source-spec
   agreement closes by `rfl`.
3. `snovaGf16MulSrc_denoteScalar` — the source `denoteScalar` computes the spec.
4. `snovaGf16Mul_compileFromHax_isSome` — the compile succeeds (`native_decide`).
5. `snovaGf16Mul_compiles` — the emitted jasmin `Com` denotes to the spec, routed
   through the C3 per-primitive obligation `compileFromHax_meets_spec`.

This is the **scalar GF(16) multiply leaf** that SNOVA's ring-dot
multiply-accumulate is built from. The ring-dot composition (the matrix-ring index
walk `Σ_J Σ_k A_J[r][k] · v_J[k][c]` over flattened GF(16) entries) is the same
per-cell pointer-bump MAC the SNOVA-reference performs; its bounded-loop owned
emission is `SNOVA/VerifyEmit.lean` (`mapEvalLooped`), so the remaining step
is the loop-around-this-leaf composition, not the field arithmetic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSnovaGf16

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The SNOVA GF(16) multiply source — one bit-step, then the full straight line

Parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`), at `w = 32`. The two
operands hold a GF(16) element in their low nibble. The bit-serial multiply runs
four iterations over `b`'s low four bits; each iteration folds the running shifted
multiplicand `sh` into the accumulator `r` (via the `0 − bit` mask `(bit^ones)+1`)
and then `xtime`s `sh`. -/

/-- One unrolled bit-step `k` of the GF(16) multiply, as a chain of `ImpExpr`
    `letBind`s appended onto a continuation `cont`. Reads/writes the running
    `sh` (shifted multiplicand) and `r` (accumulator); per-step locals carry the
    decimal-string suffix `s` so the four steps don't collide.

    The step computes (mirroring `SNOVA.VerifyEmit.gf16BitStep`):
    `bit := (b >> k) & 1`; `mask := (bit ^ ones) + 1`; `r := r ^ (sh & mask)`;
    `t := (sh << 1) & 0xf`; `cy := (sh >> 3) & 1`; `cm := ((cy ^ ones) + 1) & 0x3`;
    `sh := t ^ cm`. -/
def snovaGf16Step (k : Nat) (s : String) (cont : ImpExpr) : ImpExpr :=
  -- bit := (b >> k) & 1
  .letBind ("bit" ++ s) (.app "Shr" [.var "b", .lit (.int (Int.ofNat k))])
   (.letBind ("bm" ++ s) (.app "BitAnd" [.var ("bit" ++ s), .var "one"])
    -- mask := (bit ^ ones) + 1   (= 0 - bit)
    (.letBind ("nb" ++ s) (.app "BitXor" [.var ("bm" ++ s), .var "ones"])
     (.letBind ("mask" ++ s) (.app "wrapping_add" [.var ("nb" ++ s), .var "one"])
      -- r := r ^ (sh & mask)
      (.letBind ("sm" ++ s) (.app "BitAnd" [.var "sh", .var ("mask" ++ s)])
       (.letBind "r" (.app "BitXor" [.var "r", .var ("sm" ++ s)])
        -- t := (sh << 1) & 0xf
        (.letBind ("sl" ++ s) (.app "Shl" [.var "sh", .lit (.int 1)])
         (.letBind ("t" ++ s) (.app "BitAnd" [.var ("sl" ++ s), .var "lo4"])
          -- cy := (sh >> 3) & 1 ; cm := ((cy ^ ones) + 1) & 0x3
          (.letBind ("cyr" ++ s) (.app "Shr" [.var "sh", .lit (.int 3)])
           (.letBind ("cy" ++ s) (.app "BitAnd" [.var ("cyr" ++ s), .var "one"])
            (.letBind ("ncy" ++ s) (.app "BitXor" [.var ("cy" ++ s), .var "ones"])
             (.letBind ("cmf" ++ s) (.app "wrapping_add" [.var ("ncy" ++ s), .var "one"])
              (.letBind ("cm" ++ s) (.app "BitAnd" [.var ("cmf" ++ s), .var "poly"])
               -- sh := t ^ cm
               (.letBind "sh" (.app "BitXor" [.var ("t" ++ s), .var ("cm" ++ s)])
                cont)))))))))))))

/-- The SNOVA GF(16) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]`. Materializes the constants `one = 1`, `lo4 = 0xf`,
    `poly = 0x3` (the reduce constant `x+1`, since `x⁴ ≡ x+1`), and
    `ones = 0xFFFFFFFF` into locals; initializes `sh := a & 0xf` and `r := 0`;
    runs the four unrolled bit-steps; returns `prod := r & 0xf`. -/
def snovaGf16MulSrc : ImpExpr :=
  .letBind "one" (.lit (.int 1))
   (.letBind "lo4" (.lit (.int 0xf))
    (.letBind "poly" (.lit (.int 0x3))
     (.letBind "ones" (.lit (.int 4294967295))
      (.letBind "r" (.lit (.int 0))
       (.letBind "sh" (.app "BitAnd" [.var "a", .var "lo4"])
        (snovaGf16Step 0 "0"
         (snovaGf16Step 1 "1"
          (snovaGf16Step 2 "2"
           (snovaGf16Step 3 "3"
            (.letBind "prod" (.app "BitAnd" [.var "r", .var "lo4"])
             (.var "prod")))))))))))

/-- The bit-serial closed form the source computes — stated in the exact shifted
    `&&&`/`^^^`/`+`-mask form the source emits, so source-spec agreement is `rfl`.
    Mirrors `snovaGf16Step` step-by-step over the low nibble. -/
def snovaGf16MulSpec (a b : BitVec 32) : BitVec 32 :=
  let ones : BitVec 32 := 4294967295
  let one : BitVec 32 := 1
  let lo4 : BitVec 32 := 0xf
  let poly : BitVec 32 := 0x3
  -- sh := a & 0xf ; r := 0
  let sh0 : BitVec 32 := a &&& lo4
  let r0 : BitVec 32 := 0
  -- step 0
  let bm0 := (b >>> (0 : Nat)) &&& one
  let r1 := r0 ^^^ (sh0 &&& ((bm0 ^^^ ones) + one))
  let sh1 := ((sh0 <<< (1 : Nat)) &&& lo4)
              ^^^ (((((sh0 >>> (3 : Nat)) &&& one) ^^^ ones) + one) &&& poly)
  -- step 1
  let bm1 := (b >>> (1 : Nat)) &&& one
  let r2 := r1 ^^^ (sh1 &&& ((bm1 ^^^ ones) + one))
  let sh2 := ((sh1 <<< (1 : Nat)) &&& lo4)
              ^^^ (((((sh1 >>> (3 : Nat)) &&& one) ^^^ ones) + one) &&& poly)
  -- step 2
  let bm2 := (b >>> (2 : Nat)) &&& one
  let r3 := r2 ^^^ (sh2 &&& ((bm2 ^^^ ones) + one))
  let sh3 := ((sh2 <<< (1 : Nat)) &&& lo4)
              ^^^ (((((sh2 >>> (3 : Nat)) &&& one) ^^^ ones) + one) &&& poly)
  -- step 3
  let bm3 := (b >>> (3 : Nat)) &&& one
  let r4 := r3 ^^^ (sh3 &&& ((bm3 ^^^ ones) + one))
  r4 &&& lo4

/-- The SNOVA GF(16) multiply source denotes (under `denoteScalar`, parameters
    `["a","b"]`) to the bit-serial closed form `snovaGf16MulSpec`, reading
    `a = inpGet I 0`, `b = inpGet I 1`. The closed let-normalized body reduces:
    `BitAnd` is `&&&`, `BitXor` is `^^^`, `Shl`/`Shr n` are `<<< n`/`>>> n`,
    `wrapping_add` is `+`; the constant locals fold to their literals. A `rfl`. -/
theorem snovaGf16MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b"] I snovaGf16MulSrc (fun _ => none)
      = some (snovaGf16MulSpec (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the SNOVA GF(16) multiply (`w = 32`,
    two parameters). -/
theorem snovaGf16Mul_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 2) ["a", "b"] snovaGf16MulSrc).isSome := by
  native_decide

/-- **SNOVA GF(16) multiply emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["a","b"] snovaGf16MulSrc = some c`,
    and for every operand pair `(a, b)`, `c`'s `BitVec 32` denotation (under the
    input valuation `![a, b]`) is exactly the bit-serial GF(16) product
    `snovaGf16MulSpec`. Routed through the C3 per-primitive obligation
    `compileFromHax_meets_spec`.

    This is the scalar GF(16) (GF(2⁴)) multiply leaf that SNOVA's ring-dot
    multiply-accumulate (`SNOVA/VerifyEmit.lean`) is built from — the same
    field, same bit-serial straight-line, same branch-free `(bit ^ ones) + 1 =
    0 − bit` mask, and same `7·11 = 4` / `3·6 = 0xa` KAT vectors as MAYO. The
    ring-dot composition (the matrix-ring index walk `Σ_J Σ_k A_J[r][k]·v_J[k][c]`)
    is the bounded loop around this leaf (`mapEvalLooped`); the field arithmetic per
    term is this emitted leaf, reusing the SHA-256/Keccak/BLAKE2/MAYO recognizers
    with no front change. -/
theorem snovaGf16Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 2 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 2) ["a", "b"] snovaGf16MulSrc = some prog ∧
      ∀ (a b : BitVec 32),
        prog.denote (inputValuation 32 2 ![a, b])
          = snovaGf16MulSpec a b := by
  set prog := (compileFromHax (w := 32) (nIn := 2) ["a", "b"] snovaGf16MulSrc).get
    snovaGf16Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 2) ["a", "b"] snovaGf16MulSrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b] snovaGf16MulSrc (fun _ => none)
      = some (snovaGf16MulSpec a b) := by
    have h := snovaGf16MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 32) (nIn := 2) ["a", "b"]
    ![a, b] snovaGf16MulSrc _ hc hspec

/-! ## Side lemma: the bit-serial closed form is the GF(16) field product

Not required for the `_compiles` deliverable above. This side lemma sanity-checks,
on representative operand pairs, that `snovaGf16MulSpec` is the GF(16) =
GF(2)[x]/(x⁴+x+1) product, matching `SNOVA.VerifyEmit.gf16Mac_value`/
`gf16Mac_value2`. -/

/-- `snovaGf16MulSpec` computes the GF(16) field product on the
    `SNOVA.VerifyEmit` KAT vectors: `7 · 11 = 4` and `3 · 6 = 0xa` over
    GF(2)[x]/(x⁴+x+1). -/
theorem snovaGf16MulSpec_kat :
    snovaGf16MulSpec 0x7 0xb = 0x4 ∧ snovaGf16MulSpec 0x3 0x6 = 0xa := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSnovaGf16
