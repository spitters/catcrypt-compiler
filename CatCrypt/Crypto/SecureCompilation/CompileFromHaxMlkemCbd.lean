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
# C4 fan-out: the verified compiler emits the ML-KEM CBD_η=2 per-window coefficient

This module extends the **C4** step of the verified-compiler plan to the
**lattice / KEM** primitive family: ML-KEM (Kyber) centered-binomial-distribution
noise sampling, the per-window coefficient body of `SamplePolyCBD_η` (FIPS-203
Algorithm 8). The C4 SHA-256 leaves (`CompileFromHaxLeaves`), the Keccak lanes
(`CompileFromHaxKeccak`), the BLAKE2s `G` step (`CompileFromHaxBlake2`), the MAYO
GF(16) multiply (`CompileFromHaxMayoGf16`) and the SDitH GF(251) Solinas multiply
(`CompileFromHaxSdithGf251`) showed `compileFromHax` *emitting* crypto leaves for
the bitwise / ARX / finite-field families. Here we do the same for the **CBD_η=2
noise coefficient**, the per-coefficient arithmetic of ML-KEM-768's `cbd2`
(`cbd.c`, matching `CatCrypt/Crypto/MLKEM/CbdEmit.lean`'s `refCoeff`).

## CBD_η=2 per-window coefficient (FIPS-203 Alg. 8, η = 2)

For η = 2 each noise coefficient is a difference of two 2-bit binomial draws read
from a 4-bit window `b` of the keystream:

```
coeff = popcount(low 2 bits) − popcount(high 2 bits)
      = (b & 1) + ((b >> 1) & 1) − ((b >> 2) & 1) − ((b >> 3) & 1)
```

range `[−2, +2]` (two's-complement). This is exactly the `a − b` difference of
PQClean's `cbd2` after the `0x55555555` popcount trick has placed the two 2-bit
fields; here the window arrives already gathered into the low nibble of `b`, so
the body is the pure scalar bit-count + subtract — no popcount mask needed.

## Why this is owned-emittable on the scalar GP subset

Every step is `BitAnd` / `shift_right` (literal count) / `wrapping_add` /
`wrapping_sub` over the low nibble — the same recognizer chain as the SHA-256
`Ch`/Keccak `χ` leaves (and / shift) plus the BLAKE2 wrapping-add and the
GF(251) wrapping-sub. **No change to the verified front is required.** The
coefficient is branch-free (a popcount difference, no `Jcc`), so the source-spec
agreement closes by `rfl` — the same ARX-style approach as the GF leaves, dodging
the O(n²) simp-rewrite wall. The single bit-mask constant `1` is materialized
into its own local first (a bare literal cannot be a binary-op operand under the
front's ANF discipline; only shift counts may stay literal).

## Method (mirrors `CompileFromHaxMayoGf16.gf16Mul_compiles`)

1. `cbd2Src` — a let-normalized `ImpExpr` source (one operator per `letBind`).
2. `cbd2Spec` — the **closed form the source computes**, stated in the exact
   shifted `&&&`/`+`/`-` form the source emits, so source-spec agreement is `rfl`.
3. `cbd2Src_denoteScalar` — the source `denoteScalar` computes `cbd2Spec` (`rfl`).
4. `cbd2_compileFromHax_isSome` — the compile succeeds (`native_decide`).
5. `cbd2_compiles` — the emitted jasmin `Com` denotes to `cbd2Spec`, routed
   through the C3 per-primitive obligation `compileFromHax_meets_spec`.

The emitted jasmin `Com` is *computed by the verified compiler from the extracted
source*, proven equal to the CBD_η=2 coefficient form — the compiler authored the
leaf, with no front change beyond the SHA-256/Keccak/BLAKE2/GF leaves. This is
the first **lattice-KEM** family fan-out (ML-KEM noise sampling).

The `η = 3` variant (`cbd3`, ML-KEM-512 `η₁ = 3`) is a trivial extension: the
window is 6 bits and the coefficient is `(b&1)+((b>>1)&1)+((b>>2)&1) −
((b>>3)&1)−((b>>4)&1)−((b>>5)&1)` — two more `shift_right`/`BitAnd`/`wrapping_add`
and one more `wrapping_sub`, all in the same recognizer set.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemCbd

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The CBD_η=2 coefficient source — `w = 32`, parameter `["b"]` -/

/-- The ML-KEM CBD_η=2 per-window coefficient as a hax `ImpExpr`, fully
    let-normalized, parameter `["b"]` (`nIn = 1`; `I 0 = b`). The 4-bit keystream
    window sits in the low nibble of `b`. The coefficient is the popcount of the
    low 2 bits minus the popcount of the high 2 bits:
    `(b&1) + ((b>>1)&1) − ((b>>2)&1) − ((b>>3)&1)`. The mask constant `1` is
    materialized into a local `one` first; the three shift counts (`1`, `2`, `3`)
    stay literal (the front admits literal shift counts). Returns `r`. -/
def cbd2Src : ImpExpr :=
  .letBind "one" (.lit (.int 1))
   -- a0 := b & 1
   (.letBind "a0" (.app "BitAnd" [.var "b", .var "one"])
    -- a1 := (b >> 1) & 1
    (.letBind "s1" (.app "shift_right" [.var "b", .lit (.int 1)])
     (.letBind "a1" (.app "BitAnd" [.var "s1", .var "one"])
      -- a2 := (b >> 2) & 1
      (.letBind "s2" (.app "shift_right" [.var "b", .lit (.int 2)])
       (.letBind "a2" (.app "BitAnd" [.var "s2", .var "one"])
        -- a3 := (b >> 3) & 1
        (.letBind "s3" (.app "shift_right" [.var "b", .lit (.int 3)])
         (.letBind "a3" (.app "BitAnd" [.var "s3", .var "one"])
          -- lo := a0 + a1   (popcount of low 2 bits)
          (.letBind "lo" (.app "wrapping_add" [.var "a0", .var "a1"])
           -- hi := a2 + a3   (popcount of high 2 bits)
           (.letBind "hi" (.app "wrapping_add" [.var "a2", .var "a3"])
            -- r := lo - hi
            (.letBind "r" (.app "wrapping_sub" [.var "lo", .var "hi"])
             (.var "r")))))))))))

/-- The closed form the source computes — stated in the exact shifted `&&&`/`+`/`-`
    form the source emits, so source-spec agreement is `rfl`. This is the CBD_η=2
    coefficient: popcount of the low 2 bits minus popcount of the high 2 bits of
    the 4-bit window `b`, as a two's-complement `BitVec 32` in `[−2, 2]`. -/
def cbd2Spec (b : BitVec 32) : BitVec 32 :=
  let one : BitVec 32 := 1
  let a0 := b &&& one
  let a1 := (b >>> (1 : Nat)) &&& one
  let a2 := (b >>> (2 : Nat)) &&& one
  let a3 := (b >>> (3 : Nat)) &&& one
  (a0 + a1) - (a2 + a3)

/-- The CBD_η=2 source denotes (under `denoteScalar`, parameter `["b"]`) to the
    closed form `cbd2Spec`, reading `b = inpGet I 0`. The closed let-normalized
    body reduces definitionally: `BitAnd` is `&&&`, `shift_right n` is `>>> n`,
    `wrapping_add`/`wrapping_sub` are `+`/`-`; the constant local `one` folds to
    its literal. A `rfl` (the source and `cbd2Spec` are the *same* closed term). -/
theorem cbd2Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["b"] I cbd2Src (fun _ => none)
      = some (cbd2Spec (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the CBD_η=2 coefficient (`w = 32`,
    one parameter). -/
theorem cbd2_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 1) ["b"] cbd2Src).isSome := by
  native_decide

/-- **ML-KEM CBD_η=2 noise coefficient emitted by the verified compiler.** There
    is a compiled `Com jasminDialect` `c` with `compileFromHax ["b"] cbd2Src =
    some c`, and for every 4-bit keystream window `b`, `c`'s `BitVec 32`
    denotation (under the input valuation `![b]`) is exactly the CBD_η=2
    coefficient `cbd2Spec b = (b&1)+((b>>1)&1) − ((b>>2)&1)−((b>>3)&1)`. Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. This is a
    C4 fan-out to the **lattice-KEM** primitive family — the per-coefficient
    arithmetic of ML-KEM-768's `cbd2` noise sampler (FIPS-203 Alg. 8, matching
    `MLKEM/CbdEmit.refCoeff`) — reusing the SHA-256/Keccak/BLAKE2/GF
    `BitAnd`/`shift_right`/`wrapping_add`/`wrapping_sub` recognizers with no front
    change. The coefficient is a branch-free popcount difference, so the leaf is
    `rfl`-clean like the GF leaves. -/
theorem cbd2_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["b"] cbd2Src = some prog ∧
      ∀ (b : BitVec 32),
        prog.denote (inputValuation 32 1 ![b])
          = cbd2Spec b := by
  set prog := (compileFromHax (w := 32) (nIn := 1) ["b"] cbd2Src).get
    cbd2_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 1) ["b"] cbd2Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro b
  have hspec : ImpExpr.denoteScalar ["b"] ![b] cbd2Src (fun _ => none)
      = some (cbd2Spec b) := by
    exact cbd2Src_denoteScalar (nIn := 1) ![b]
  exact compileFromHax_meets_spec (w := 32) (nIn := 1) ["b"]
    ![b] cbd2Src _ hc hspec

/-! ## Side lemma: the closed form is the centered-binomial coefficient

Not required for the `_compiles` deliverable above. This side lemma sanity-checks
that `cbd2Spec` lands in the CBD_η=2 range `[−2, 2]` (two's-complement) over every
4-bit window, and matches a few representative `refCoeff`-style vectors. -/

/-- `cbd2Spec` produces a centered-binomial-η=2 coefficient on
    representative 4-bit windows: `0b0011 → 2−0 = 2`, `0b1100 → 0−2 = −2`,
    `0b1001 → 1−1 = 0`, `0b0001 → 1`, `0b1000 → −1`. -/
theorem cbd2Spec_kat :
    cbd2Spec 0b0011 = 2 ∧ cbd2Spec 0b1100 = (0 - 2) ∧
    cbd2Spec 0b1001 = 0 ∧ cbd2Spec 0b0001 = 1 ∧ cbd2Spec 0b1000 = (0 - 1) := by
  native_decide

/-- **Coefficient range.** Every 4-bit window yields a coefficient in the
    centered-binomial range `[−2, 2]` (`{0,1,2} ∪ {0xFFFF...FE, 0xFFFF...FF}`
    two's-complement). A sanity pin that the emitted body produces real CBD_η=2
    coefficients, not arbitrary words. -/
theorem cbd2Spec_in_range (b : BitVec 32) :
    cbd2Spec b = 0 ∨ cbd2Spec b = 1 ∨ cbd2Spec b = 2 ∨
    cbd2Spec b = (0 - 1) ∨ cbd2Spec b = (0 - 2) := by
  unfold cbd2Spec
  bv_decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMlkemCbd
