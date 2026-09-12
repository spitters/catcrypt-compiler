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
# C4 fan-out: the verified compiler emits a MAYO GF(16) multiply from extracted source

This module extends the **C4** step of the verified-compiler plan to the
**multivariate / finite-field** primitive family: MAYO (NIST additional
signatures, oil-and-vinegar over GF(16) = GF(2⁴)). The C4 SHA-256 leaves
(`CompileFromHaxLeaves`), the Keccak `χ`/`θ`/`ι` lanes (`CompileFromHaxKeccak`),
and the BLAKE2s `G` step (`CompileFromHaxBlake2`) showed `compileFromHax`
*emitting* crypto leaves for the bitwise (`¬`/`∧`/`⊕`/shift) and ARX
(`+`/`^`/`>>>`) families. Here we do the same for the **GF(16) field multiply**,
the hot inner unit of MAYO's `eval_public_map` (the verify map evaluation
`acc ^= sⱼ · A[j][l] · s_l`, matching `CatCrypt/Crypto/MAYO/VerifyEmit.lean`'s
`gf16BitStep`/`gf16MulInline`).

## GF(16) multiply (the bit-serial straight-line)

GF(16) = GF(2)[x]/(x⁴+x+1). The product `a · b` over the low nibble of two words
is the standard 4-step **shift-and-conditional-xor with reduction**: for each bit
`k = 0..3` of `b`, conditionally XOR the running shifted multiplicand `sh` into
the accumulator `r` if bit `k` is set, then `xtime(sh)` (multiply `sh` by `x`,
reducing modulo `x⁴+x+1`, i.e. XOR the reduce constant `0x3 = x+1` back in when
the degree-4 bit `x⁴` appears). This is exactly `VerifyEmit.gf16BitStep`.

The conditional XOR and the conditional reduce are both done **branch-free** via a
mask `mask = 0 − bit` (`0x0` or all-ones). The front exposes `BitAnd`/`BitXor`/
`BitOr`/`wrapping_add` and `Shl`/`Shr` (literal counts) but **no subtract/negate**,
so the two's-complement mask `0 − bit` is materialized as `(bit ^ ones) + 1`
(`ones = 0xFFFFFFFF`, `~bit + 1`): for `bit = 0` this is `~0 + 1 = 0`, for
`bit = 1` it is `~1 + 1 = 0xFFFFFFFF = allOnes` — the same mask the owned
`gf16BitStep` builds with `SUB`. Mask/poly/ones constants are first bound to their
own locals (a bare literal can't be a binary-op operand; bit-not desugars to
`BitXor[x, ones]`).

## Method (mirrors `CompileFromHaxBlake2.blake2G_compiles`)

Every step is `BitAnd`/`BitXor`/`Shl`/`Shr`/`wrapping_add` over the low nibble —
the same recognizer chain as the SHA-256 `Ch`/Keccak `χ` leaves (and / xor /
shift) plus the BLAKE2 wrapping-add. **No change to the verified front is
required.** The source is fully let-normalized (one operator per `letBind`, all
arguments atoms or earlier locals), so the leaf follows the C3 obligation:

1. `gf16MulSrc` — a let-normalized `ImpExpr` source.
2. `gf16MulSpec` — the **bit-serial closed form the source computes**, stated in
   the exact `· ^^^ (· &&& mask)`-shifted form the source emits, so the
   source-spec agreement closes by `rfl` (the ARX-style approach, dodging the
   O(n²) simp-rewrite wall). This is *not* an abstract `GF16.mul` Mathlib def;
   `gf16MulSpec_eq_field` (a side lemma, not required for `_compiles`) certifies
   on representative inputs that this closed form is the GF(16) field product.
3. `gf16MulSrc_denoteScalar` — the source `denoteScalar` computes `gf16MulSpec`.
4. `gf16Mul_compileFromHax_isSome` — the compile succeeds (`native_decide`).
5. `gf16Mul_compiles` — the emitted jasmin `Com` denotes to `gf16MulSpec`, routed
   through the C3 per-primitive obligation `compileFromHax_meets_spec`.

The emitted jasmin `Com` is *computed by the verified compiler from the extracted
source*, proven equal to the bit-serial GF(16) product — the compiler authored
the leaf, with no front change beyond the SHA-256/Keccak/BLAKE2 leaves. This is
the first finite-field (GF(2⁴)) family fan-out, and the harder tier:
the field-reduce makes the spec non-trivial.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMayoGf16

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The GF(16) multiply source — one bit-step, then the full straight line

Parameters `["a","b"]` (`nIn = 2`; `I 0 = a`, `I 1 = b`), at `w = 32`. The two
operands hold a GF(16) element in their low nibble. The bit-serial multiply runs
four iterations over `b`'s low four bits; each iteration folds the running shifted
multiplicand `sh` into the accumulator `r` (via the `0 − bit` mask `(bit^ones)+1`)
and then `xtime`s `sh`. The constants `ones = 0xFFFFFFFF` and the reduce/mask
literals are materialized into their own locals first. -/

/-- One unrolled bit-step `k` of the GF(16) multiply, as a chain of `ImpExpr`
    `letBind`s appended onto a continuation `cont`. Reads/writes the running
    `sh` (shifted multiplicand) and `r` (accumulator); uses `b` and the `ones`
    local; allocates per-step locals named with the suffix `s` (the step index as
    a decimal string, supplied by the caller) so the four steps don't collide.

    The step computes (mirroring `VerifyEmit.gf16BitStep`):
    `bit := (b >> k) & 1`; `mask := (bit ^ ones) + 1`; `r := r ^ (sh & mask)`;
    `t := (sh << 1) & 0xf`; `cy := (sh >> 3) & 1`; `cm := ((cy ^ ones) + 1) & 0x3`;
    `sh := t ^ cm`. -/
def gf16Step (k : Nat) (s : String) (cont : ImpExpr) : ImpExpr :=
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

/-- The GF(16) multiply source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]`. Materializes the constants `one = 1`, `lo4 = 0xf`,
    `poly = 0x3` (the reduce constant `x+1`, since `x⁴ ≡ x+1`), and
    `ones = 0xFFFFFFFF` into locals; initializes `sh := a & 0xf` and `r := 0`;
    runs the four unrolled bit-steps; returns `prod := r & 0xf`. -/
def gf16MulSrc : ImpExpr :=
  .letBind "one" (.lit (.int 1))
   (.letBind "lo4" (.lit (.int 0xf))
    (.letBind "poly" (.lit (.int 0x3))
     (.letBind "ones" (.lit (.int 4294967295))
      (.letBind "r" (.lit (.int 0))
       (.letBind "sh" (.app "BitAnd" [.var "a", .var "lo4"])
        (gf16Step 0 "0"
         (gf16Step 1 "1"
          (gf16Step 2 "2"
           (gf16Step 3 "3"
            (.letBind "prod" (.app "BitAnd" [.var "r", .var "lo4"])
             (.var "prod")))))))))))

/-- The bit-serial closed form the source computes — stated in the exact shifted
    `&&&`/`^^^`/`+`-mask form the source emits, so source-spec agreement is `rfl`.
    Mirrors `gf16Step` step-by-step over the low nibble. -/
def gf16MulSpec (a b : BitVec 32) : BitVec 32 :=
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

/-- The GF(16) multiply source denotes (under `denoteScalar`, parameters
    `["a","b"]`) to the bit-serial closed form `gf16MulSpec`, reading
    `a = inpGet I 0`, `b = inpGet I 1`. The closed let-normalized body reduces:
    `BitAnd` is `&&&`, `BitXor` is `^^^`, `Shl`/`Shr n` are `<<< n`/`>>> n`,
    `wrapping_add` is `+`; the constant locals fold to their literals. A `rfl`
    (the source and `gf16MulSpec` are the *same* closed term). -/
theorem gf16MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b"] I gf16MulSrc (fun _ => none)
      = some (gf16MulSpec (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the GF(16) multiply (`w = 32`, two
    parameters). -/
theorem gf16Mul_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 2) ["a", "b"] gf16MulSrc).isSome := by
  native_decide

/-- **MAYO GF(16) multiply emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `c` with `compileFromHax ["a","b"] gf16MulSrc = some c`, and
    for every operand pair `(a, b)`, `c`'s `BitVec 32` denotation (under the input
    valuation `![a, b]`) is exactly the bit-serial GF(16) product `gf16MulSpec`.
    Routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.
    This is a C4 fan-out to the *finite-field* (GF(2⁴)) primitive family — the hot
    inner unit of MAYO's `eval_public_map` — reusing the SHA-256/Keccak/BLAKE2
    `BitAnd`/`BitXor`/`Shl`/`Shr`/`wrapping_add` recognizers with no front change.
    The field-reduce (`xtime` modulo `x⁴+x+1`) is the harder content; it
    is done branch-free via the two's-complement mask `(bit ^ ones) + 1 = 0 − bit`,
    matching `VerifyEmit.gf16BitStep`. -/
theorem gf16Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 2 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 2) ["a", "b"] gf16MulSrc = some prog ∧
      ∀ (a b : BitVec 32),
        prog.denote (inputValuation 32 2 ![a, b])
          = gf16MulSpec a b := by
  set prog := (compileFromHax (w := 32) (nIn := 2) ["a", "b"] gf16MulSrc).get
    gf16Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 2) ["a", "b"] gf16MulSrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b] gf16MulSrc (fun _ => none)
      = some (gf16MulSpec a b) := by
    have h := gf16MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 32) (nIn := 2) ["a", "b"]
    ![a, b] gf16MulSrc _ hc hspec

/-! ## Side lemma: the bit-serial closed form is the GF(16) field product

Not required for the `_compiles` deliverable above (which states the emitted
jasmin equals the bit-serial form the source computes). This side lemma sanity-
checks, on representative operand pairs, that `gf16MulSpec` is the GF(16) =
GF(2)[x]/(x⁴+x+1) product: e.g. `7 · 11 = 4` (`x²`) and `3 · 6 = 0xa`, matching
`VerifyEmit.gf16Mac_value`/`gf16Mac_value2`. -/

/-- `gf16MulSpec` computes the GF(16) field product on the `VerifyEmit`
    KAT vectors: `7 · 11 = 4` and `3 · 6 = 0xa` over GF(2)[x]/(x⁴+x+1). -/
theorem gf16MulSpec_kat :
    gf16MulSpec 0x7 0xb = 0x4 ∧ gf16MulSpec 0x3 0x6 = 0xa := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMayoGf16
