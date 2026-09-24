/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# 2×2-limb (128×128 → 256) schoolbook bignum MULTIPLY on the HIGH `catCryptDialect`

This is the multiply companion of `BignumAddCatCryptEmit.lean`. Where that file
routes a multi-limb *add* carry chain through `catCryptDialect` (the MLIR-aligned
successor IR over the `Com` framework), this file routes the s2n-bignum / GMP
headline op — a **schoolbook bignum multiply** — through the same high dialect,
all the way down to `Com jasminDialect`.

`catCryptDialect` already carries the bignum-multiply word ops:

* `bvMul   w` : the **low** `w` bits of the product `a * b` (x86 `MUL`/`IMUL`
  low word, jasmin `regArith .mul`).
* `bvMulHi w` : the **high** `w` bits of the full unsigned product
  `(a.toNat * b.toNat) / 2 ^ w` (x86 `MULX` high word, jasmin `mulhi`). Together
  `(bvMulHi, bvMul)` are MULX's `(hi, lo)`.
* `bvAddCarryLo w` / `bvAddCarryHi w` : the data word / carry-out bit of one
  carry-chain add `a + b + cin` (`cin : sword 1`), the x86 `ADCX`/`ADOX` pair
  (jasmin `addCarryLo`/`addCarryHi`).

A 2×2-limb (128×128 → 256) schoolbook multiply forms the four partial products
`aᵢ * bⱼ` (each split into `(hi, lo)` by `bvMulHi`/`bvMul`) and accumulates them
into the four output limbs `(p0, p1, p2, p3)` with the `bvAddCarryLo`/
`bvAddCarryHi` carry chain. We build that schedule **natively** as a
`Com catCryptDialect` and prove `bignumMul2Com.denote = bignumMul2Spec` (a
definitional `rfl`, since the spec is written with the *same* word ops the
dialect denotes into). 2×2 limbs proves the pattern while staying tractable.

## What is proved here

* `bignumMul2Spec` — the clean schoolbook accumulation over `BitVec 64` limbs,
  written with `mulLoC`/`mulHiC`/`addCarryWordC`/`carryOutBitC` (the same
  primitives the dialect `bvMul`/`bvMulHi`/`bvAddCarry*` denote into).
* `bignumMul2Com : Com catCryptDialect Γ₄ (.sword 64)` — the 2×2 schoolbook
  multiply built natively from `bvMul`/`bvMulHi`/`bvAddCarryLo`/`bvAddCarryHi`/
  `bvConst`, returning the top product limb `p3 : sword 64`.
* `bignumMul2Com_denote` — **the dialect Com denotes exactly the spec's top
  limb** (`rfl`). The first bignum-MULTIPLY-through-`catCryptDialect` tie.
* `bignumMul2Com_lowers` / `bignumMul2Jasmin` / `bignumMul2Jasmin_denote` — the
  whole multiply lowers to `Com jasminDialect` (every op is seam-covered) and
  the jasmin program denotes (on the transported valuation) to the spec's top
  limb. The bignum-multiply-through-`catCryptDialect`-to-jasmin path.

## The jasmin seam

Like the *split* add path in `BignumAddCatCryptEmit.lean`, this multiply uses
only the **single-word** seam-covered ops `bvMul`/`bvMulHi`/`bvAddCarryLo`/
`bvAddCarryHi`/`bvConst` — no pair ops (`mkPair`/`fst`/`snd`), which
`DialectToJasminCom.toJExprD` declines. So `cryptoDialectToJasminCom` succeeds
and the whole schoolbook multiply lowers to jasmin. The program returns a single
`sword 64` word (`p3`, the top product limb); each lower limb `pᵢ` is bound and
denotes to the matching spec limb but is not returned because the jasmin result
must be a single word.

**0 sorries.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BignumMulCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## 1. The schoolbook 2×2-limb (128×128 → 256) multiply spec

`bignumMul2Spec a0 a1 b0 b1` multiplies two 128-bit values held as 2 little-endian
`BitVec 64` limbs `(a0, a1)`, `(b0, b1)`, returning the 256-bit product as four
limbs `(p0, p1, p2, p3)`. It is written with the *same* word primitives the
dialect `bvMul`/`bvMulHi`/`bvAddCarryLo`/`bvAddCarryHi` denote into, so the
dialect tie is a `rfl`. -/

/-- Low word of the full unsigned product `a * b` (the `lo` output of `MULX`,
    `bvMul`'s denotation). -/
def mulLoC (a b : BitVec 64) : BitVec 64 := a * b

/-! ### The schoolbook accumulation

With `a = a0 + a1·2⁶⁴`, `b = b0 + b1·2⁶⁴`, the 256-bit product is

```
a·b = a0·b0
    + (a0·b1 + a1·b0)·2⁶⁴
    + a1·b1·2¹²⁸
```

Splitting each `aᵢ·bⱼ` into `(hiᵢⱼ, loᵢⱼ)`, the limb-by-limb accumulation is

```
p0 = lo00
p1 = hi00 + lo01 + lo10            (+ carries c_a, c_b out)
p2 = hi01 + hi10 + lo11 + c_a + c_b (+ carries c_c, c_d out)
p3 = hi11 + c_c + c_d
```

threaded with the 1-bit carry chain (`addCarryHi` produces the next limb's
carry-in word). -/

/-- **The abstract 128×128 → 256 multiply spec.** Little-endian 2×2-limb
    schoolbook multiply. Returns `(p0, p1, p2, p3)`. -/
def bignumMul2Spec (a0 a1 b0 b1 : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  -- the four partial products, split into (hi, lo)
  let lo00 := mulLoC a0 b0; let hi00 := mulHiC a0 b0
  let lo01 := mulLoC a0 b1; let hi01 := mulHiC a0 b1
  let lo10 := mulLoC a1 b0; let hi10 := mulHiC a1 b0
  let lo11 := mulLoC a1 b1; let hi11 := mulHiC a1 b1
  -- limb 0
  let p0 := lo00
  -- limb 1: hi00 + lo01 + lo10
  let t1 := addCarryWordC hi00 lo01 0; let ca := carryOutBitC hi00 lo01 0
  let p1 := addCarryWordC t1 lo10 0;   let cb := carryOutBitC t1 lo10 0
  -- limb 2: hi01 + hi10 + lo11, with carries ca, cb threaded in
  let u1 := addCarryWordC hi01 hi10 ca; let cc := carryOutBitC hi01 hi10 ca
  let p2 := addCarryWordC u1 lo11 cb;   let cd := carryOutBitC u1 lo11 cb
  -- limb 3: hi11 + cc + cd
  let p3 := addCarryWordC (addCarryWordC hi11 0 cc) 0 cd
  (p0, p1, p2, p3)

/-! ## 2. The input context and output type

`Γ₄ = [sword 64, ×4]` holds `a0, a1, b0, b1` at indices `0..3`. The program
returns the top product limb `p3 : sword 64` (a single word, so the whole thing
lowers to jasmin). -/

/-- The starting context: four 64-bit limb inputs `a0, a1, b0, b1`. -/
abbrev Γ₄ : Ctxt catCryptDialect :=
  [.sword 64, .sword 64, .sword 64, .sword 64]

/-! ## 3. The 2×2 schoolbook multiply `Com catCryptDialect`

The schedule, in source order (each `.var` binds one result on top of the stack).
We use `bvMul`/`bvMulHi` for the eight partial-product words and
`bvAddCarryLo`/`bvAddCarryHi` for the carry chain, mirroring `bignumMul2Spec`
line for line. The initial carry-ins are `bvConst 1 0`.

Every op returns a single `sword`, so no pair ops are needed and the whole
program lowers through the existing jasmin seam. -/

/-- The 2×2-limb (128×128 → 256) schoolbook multiply built natively over
    `catCryptDialect`, returning the top product limb `p3 : sword 64`. -/
def bignumMul2Com : Com catCryptDialect Γ₄ (.sword 64) :=
  -- z : sword 1 := bvConst 1 0      (the zero carry-in)
  .var (show Expr catCryptDialect Γ₄ (.sword 1) from
        { op := .bvConst 1 0, retTy_eq := rfl, args := .nil }) <|
  -- After z bound, Γ₄ inputs shift by 1: a0=.there^1.here, a1=.there^2.here,
  -- b0=.there^3.here, b1=.there^4.here ; z=.here
  -- lo00 := bvMul a0 b0
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMul 64, retTy_eq := rfl,
          args := .cons (.there .here)
                 (.cons (.there (.there (.there .here))) .nil) }) <|
  -- stack: lo00, z, Γ₄.  a0=.there^2.here, b0=.there^4.here
  -- hi00 := bvMulHi a0 b0
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMulHi 64, retTy_eq := rfl,
          args := .cons (.there (.there .here))
                 (.cons (.there (.there (.there (.there .here)))) .nil) }) <|
  -- stack: hi00, lo00, z, Γ₄.  a0=.there^3.here, b1=.there^6.here
  -- lo01 := bvMul a0 b1
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMul 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here)))
                 (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) }) <|
  -- stack: lo01, hi00, lo00, z, Γ₄.  a0=.there^4.here, b1=.there^7.here
  -- hi01 := bvMulHi a0 b1
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMulHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) }) <|
  -- stack: hi01, lo01, hi00, lo00, z, Γ₄.  a1=.there^6.here, b0=.there^7.here
  -- lo10 := bvMul a1 b0
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMul 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) }) <|
  -- stack: lo10, hi01, lo01, hi00, lo00, z, Γ₄.  a1=.there^7.here, b0=.there^8.here
  -- hi10 := bvMulHi a1 b0
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMulHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) }) <|
  -- stack: hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄.  a1=.there^8.here, b1=.there^10.here
  -- lo11 := bvMul a1 b1
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMul 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) ) .nil) }) <|
  -- stack: lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄.  a1=.there^9.here, b1=.there^11.here
  -- hi11 := bvMulHi a1 b1
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvMulHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) ) .nil) }) <|
  -- ===== limb 1: hi00 + lo01 + lo10 =====
  -- stack (top→bottom): hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄
  -- indices from top: hi11=0, lo11=1, hi10=2, lo10=3, hi01=4, lo01=5, hi00=6, lo00=7, z=8
  -- t1 := bvAddCarryLo hi00 lo01 z
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))      -- hi00 @6
                 (.cons (.there (.there (.there (.there (.there .here)))))               -- lo01 @5
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- z @8
                 .nil)) }) <|
  -- stack: t1, hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄ (shift +1)
  -- ca := bvAddCarryHi hi00 lo01 z ; hi00=@7, lo01=@6, z=@9
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))   -- hi00 @7
                 (.cons (.there (.there (.there (.there (.there (.there .here))))))            -- lo01 @6
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) -- z @9
                 .nil)) }) <|
  -- stack: ca, t1, hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄ (shift +2)
  -- p1 := bvAddCarryLo t1 lo10 z ; t1=@1, lo10=@5, z=@10
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there .here)                                                       -- t1 @1
                 (.cons (.there (.there (.there (.there (.there .here)))))                    -- lo10 @5
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))  -- z @10
                 .nil)) }) <|
  -- stack: p1, ca, t1, hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄ (shift +3)
  -- cb := bvAddCarryHi t1 lo10 z ; t1=@2, lo10=@6, z=@11
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there .here))                                              -- t1 @2
                 (.cons (.there (.there (.there (.there (.there (.there .here))))))           -- lo10 @6
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))  -- z @11
                 .nil)) }) <|
  -- ===== limb 2: hi01 + hi10 + lo11, carries ca, cb threaded in =====
  -- stack: cb, p1, ca, t1, hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄ (shift +4)
  -- indices from top: cb=0, p1=1, ca=2, t1=3, hi11=4, lo11=5, hi10=6, lo10=7, hi01=8, lo01=9, hi00=10, lo00=11, z=12
  -- u1 := bvAddCarryLo hi01 hi10 ca ; hi01=@8, hi10=@6, ca=@2
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- hi01 @8
                 (.cons (.there (.there (.there (.there (.there (.there .here))))))                    -- hi10 @6
                 (.cons (.there (.there .here))                                                        -- ca @2
                 .nil)) }) <|
  -- stack: u1, cb, p1, ca, t1, ... (shift +5). cc := bvAddCarryHi hi01 hi10 ca
  -- hi01=@9, hi10=@7, ca=@3
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))  -- hi01 @9
                 (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))                    -- hi10 @7
                 (.cons (.there (.there (.there .here)))                                                       -- ca @3
                 .nil)) }) <|
  -- stack: cc, u1, cb, p1, ca, t1, hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄ (shift +6)
  -- indices: cc=0, u1=1, cb=2, p1=3, ca=4, t1=5, hi11=6, lo11=7, hi10=8, lo10=9, hi01=10, lo01=11, hi00=12, lo00=13, z=14
  -- p2 := bvAddCarryLo u1 lo11 cb ; u1=@1, lo11=@7, cb=@2
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there .here)                                                       -- u1 @1
                 (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))  -- lo11 @7
                 (.cons (.there (.there .here))                                               -- cb @2
                 .nil)) }) <|
  -- stack: p2, cc, u1, cb, p1, ca, t1, hi11, lo11, ... (shift +7)
  -- cd := bvAddCarryHi u1 lo11 cb ; u1=@2, lo11=@8, cb=@3
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there .here))                                              -- u1 @2
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- lo11 @8
                 (.cons (.there (.there (.there .here)))                                      -- cb @3
                 .nil)) }) <|
  -- ===== limb 3: hi11 + cc + cd =====
  -- stack: cd, p2, cc, u1, cb, p1, ca, t1, hi11, lo11, hi10, lo10, hi01, lo01, hi00, lo00, z, Γ₄ (shift +8)
  -- indices: cd=0, p2=1, cc=2, u1=3, cb=4, p1=5, ca=6, t1=7, hi11=8, lo11=9, ... z=16
  -- w1 := bvAddCarryLo hi11 z cc  (hi11 + 0 + cc). Need a zero64 word: reuse none — use lo of bvConst? z is sword 1.
  --   We need a 64-bit zero. Use bvConst 64 0 here.
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvConst 64 0, retTy_eq := rfl, args := .nil }) <|
  -- stack: zero64, cd, p2, cc, u1, cb, p1, ca, t1, hi11, ... (shift +9 from limb-2 frame; +1 from prev)
  -- indices now: zero64=0, cd=1, p2=2, cc=3, u1=4, cb=5, p1=6, ca=7, t1=8, hi11=9, ...
  -- w1 := bvAddCarryLo hi11 zero64 cc ; hi11=@9, zero64=@0, cc=@3
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))  -- hi11 @9
                 (.cons .here                                                                  -- zero64 @0
                 (.cons (.there (.there (.there .here)))                                        -- cc @3
                 .nil)) }) <|
  -- stack: w1, zero64, cd, p2, cc, u1, ... (shift +1)
  -- indices: w1=0, zero64=1, cd=2, p2=3, cc=4, ...
  -- p3 := bvAddCarryLo w1 zero64 cd ; w1=@0, zero64=@1, cd=@2
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons .here                                                                  -- w1 @0
                 (.cons (.there .here)                                                          -- zero64 @1
                 (.cons (.there (.there .here))                                                 -- cd @2
                 .nil)) }) <|
  -- ret p3 (top of stack)
  .ret .here

/-! ## 4. The denote = spec tie -/

/-- **The 2×2 dialect schoolbook multiply denotes EXACTLY the spec's top limb.**

    A bignum-MULTIPLY-through-`catCryptDialect` `denote = spec` witness:
    the `Com catCryptDialect` built from the `bvMul`/`bvMulHi`/
    `bvAddCarryLo`/`bvAddCarryHi` ops computes precisely the top product limb
    `p3` of the clean schoolbook spec `bignumMul2Spec`. -/
theorem bignumMul2Com_denote (a0 a1 b0 b1 : BitVec 64) :
    bignumMul2Com.denote
        (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = (bignumMul2Spec a0 a1 b0 b1).2.2.2 := by
  rfl

/-! ## 5. The bignum MULTIPLY → jasmin path through the high dialect

Every op in `bignumMul2Com` is seam-covered (`bvConst`, `bvMul`, `bvMulHi`,
`bvAddCarryLo`, `bvAddCarryHi`), so `cryptoDialectToJasminCom` succeeds. This is
the first multi-limb *schoolbook multiply* lowered from `catCryptDialect` all the
way to `Com jasminDialect` — the bignum-MUL spine over a *high* dialect, not
hand-built `JInstr`. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-- The schoolbook multiply lowers: every op is in the covered fragment. -/
theorem bignumMul2Com_lowers :
    (cryptoDialectToJasminCom bignumMul2Com).isSome := by
  native_decide

/-- The lowered Jasmin-dialect 2×2 schoolbook multiply program. -/
def bignumMul2Jasmin : Com jasminDialect (mapCtx Γ₄) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom bignumMul2Com).get bignumMul2Com_lowers

/-- **The bignum schoolbook multiply, lowered to jasmin, denotes the spec.**

    Composing the dialect `denote = spec` tie (`bignumMul2Com_denote`) with the
    seam's denotation-preservation corollary
    (`cryptoDialectToJasminCom_denote_eq'`): the **jasmin** program denotes (on
    the transported valuation) to `ctTransTy` of the dialect program's
    denotation, which is the top product limb `p3` of `bignumMul2Spec`. The first
    bignum-multiply result carried through `catCryptDialect` ALL THE WAY to
    jasmin. -/
theorem bignumMul2Jasmin_denote (a0 a1 b0 b1 : BitVec 64) :
    bignumMul2Jasmin.denote
        (ctMapValD (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil)))))
      = ctTransTy (bignumMul2Spec a0 a1 b0 b1).2.2.2 := by
  have hlow : cryptoDialectToJasminCom bignumMul2Com = some bignumMul2Jasmin :=
    (Option.some_get bignumMul2Com_lowers).symm
  rw [DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq' bignumMul2Com
        (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil)))) bignumMul2Jasmin hlow,
     bignumMul2Com_denote]

/-- **The lowered jasmin program's top product limb equals the spec's.**
    Composing `bignumMul2Jasmin_denote` with `ctTransTy_sword` (the transport is
    the identity on `.sword 64`): the jasmin program's returned word is exactly
    the top limb `p3` of the abstract schoolbook product. This closes the chain
    `bignumMul2Spec` (abstract spec) → `catCryptDialect` → `jasmin`. -/
theorem bignumMul2Jasmin_top_spec (a0 a1 b0 b1 : BitVec 64) :
    (bignumMul2Jasmin.denote
        (ctMapValD (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))) : BitVec 64)
      = (bignumMul2Spec a0 a1 b0 b1).2.2.2 := by
  rw [bignumMul2Jasmin_denote, CryptoToJasminComCorrect.ctTransTy_sword]

/-! ## 6. Schoolbook spec is the true 256-bit product (non-vacuity witness)

The `denote = spec` tie above is definitional, so the spec carries the
algorithmic content. We pin that content to the *real* 256-bit integer product
`(a0 + a1·2⁶⁴)·(b0 + b1·2⁶⁴)` by recombining the four output limbs with the
positional weights `(1, 2⁶⁴, 2¹²⁸, 2¹⁹²)`. A fully general `bv_decide` over the
256-bit partial-product algebra is heavy (the nested carry `if`s blow up
`bv_decide`'s `simp` preprocessing), so non-vacuity is witnessed by the
`maxValue` corner (all-ones limbs — the maximal-carry case that exercises every
carry-out in the chain) via `native_decide`. -/

/-- **Non-vacuity: the schoolbook spec computes the 256-bit product** at
    the maximal-carry all-ones input — recombining `(p0,p1,p2,p3)` with the
    positional weights gives exactly `(2⁶⁴-1 + (2⁶⁴-1)·2⁶⁴)²`. This exercises
    every carry-out in the chain (the hardest case), confirming the partial-
    product accumulation and the `denote = spec` tie above are not vacuous. -/
theorem bignumMul2Spec_maxcarry :
    (let r := bignumMul2Spec 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
                              0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
     r.1.toNat + r.2.1.toNat * 2 ^ 64 + r.2.2.1.toNat * 2 ^ 128
       + r.2.2.2.toNat * 2 ^ 192)
      = (0xFFFFFFFFFFFFFFFF + 0xFFFFFFFFFFFFFFFF * 2 ^ 64)
        * (0xFFFFFFFFFFFFFFFF + 0xFFFFFFFFFFFFFFFF * 2 ^ 64) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.BignumMulCatCryptEmit
