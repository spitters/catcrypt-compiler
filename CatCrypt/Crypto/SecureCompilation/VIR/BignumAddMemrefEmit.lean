/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.BignumAddCatCryptEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.BignumAddCatCryptEmit

/-!
# Multi-output 256-bit bignum ADD: the WHOLE result emitted via an output memref

The committed `BignumAddCatCryptEmit` lowers a 4-limb add to jasmin, but the
single-return jasmin `Com` seam can only return **one** word. `bignumAdd4Jasmin`
therefore returns just the final carry-out bit — the four sum limbs are bound and
proved correct, but *not* returned. That is the multi-output bignum ABI residual:
a 256-bit add has a 256-bit result, and a one-word return drops it.

This file closes the residual the way a real ABI does: it writes **all four sum
limbs to an output memref**, passed in as a caller-provided output buffer (the
standard out-pointer ABI: `bignum_add(out, a, b)`). The `catCryptDialect`
runtime-index memref ops `memrefSetDyn`/`memrefGetDyn` ARE seam-covered (they
lower to jasmin `stackStore`/`stackLoad`), so the result memref survives the
lowering. The dialect program returns a `.memref 4` holding the whole 256-bit
sum, and we prove that reading each cell back (`memGetDyn` at index `0..3`) yields
the matching `bignumAdd4` sum limb. Then `cryptoDialectToJasminCom` lowers the
whole program to jasmin — the entire 256-bit result is now emitted, via
`stackStore`, not just the carry.

(`memrefZero` is *not* in the lowered fragment — only `memrefSetDyn`/`memrefGetDyn`
are — which is exactly the out-pointer ABI: the buffer is an argument, not a
freshly-stack-allocated value.)

## What is proved here

* `bignumAddMemrefSpec` — the abstract output: the input memref with the four
  `bignumAdd4` sum limbs written at indices `0..3`.
* `bignumAdd4ComMemref : Com catCryptDialect Γ₉ (.memref 4)` — the split carry
  chain (reusing `bvAddCarryLo`/`bvAddCarryHi`, all seam-covered) writing the four
  sum limbs into the output memref input via `memrefSetDyn` at runtime indices
  `0..3`. No pair ops and no `memrefZero`, so the whole program lowers.
* `bignumAdd4ComMemref_denote` — the dialect program denotes EXACTLY
  `bignumAddMemrefSpec` (a `rfl`).
* `bignumAdd4ComMemref_readback` — reading cell `i` back via `memGetDyn` returns
  the `i`-th `bignumAdd4` sum limb (the multi-output read API), independent of the
  buffer's prior contents.
* `bignumAdd4MemrefJasmin` + `bignumAdd4MemrefJasmin_denote` — the program lowered
  all the way to `Com jasminDialect`, denoting (on the transported valuation) to
  `ctTransTy` of the output memref. The whole 256-bit result, carried through
  `catCryptDialect` to jasmin via `stackStore`.

**0 sorries.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BignumAddMemrefEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.BignumAddCatCryptEmit

/-! ## 1. The input context and the abstract memref output spec

The context `Γ₉` holds the eight 64-bit limb inputs `a0..a3, b0..b3` followed by
the caller-provided output memref `out : .memref 4`. -/

/-- Context: the eight limb inputs `a0..a3, b0..b3`, then the output memref. -/
abbrev Γ₉ : Ctxt catCryptDialect :=
  [.sword 64, .sword 64, .sword 64, .sword 64,
   .sword 64, .sword 64, .sword 64, .sword 64, .memref 4]

/-- The output memref of a 256-bit add: the caller buffer `m` with the four sum
    limbs of `bignumAdd4Split` written at indices `0..3` (= bit-for-bit the
    `bignumAdd4` sum limbs, by `bignumAdd4Split_eq_spec`). Written by `memSetDyn`
    at runtime indices `0..3`, exactly as the dialect program below denotes. -/
def bignumAddMemrefSpec
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (m : Fin 4 → BitVec 64) :
    Fin 4 → BitVec 64 :=
  let s := (bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).2
  let m1 := memSetDyn m (0 : BitVec 64).toNat s.1
  let m2 := memSetDyn m1 (1 : BitVec 64).toNat s.2.1
  let m3 := memSetDyn m2 (2 : BitVec 64).toNat s.2.2.1
  let m4 := memSetDyn m3 (3 : BitVec 64).toNat s.2.2.2
  m4

/-! ## 2. The dialect program

The split carry chain (the `bvAddCarryLo`/`bvAddCarryHi` schedule of
`bignumAdd4ComSplit`, all seam-covered) producing the four sum limbs, followed by
four `memrefSetDyn` writes into the output memref input `out`. We use
`memrefSetDyn` (runtime index, the seam-covered op) with `bvConst 64 i` index
words. The result type is `.memref 4`.

In `Γ₉` the limb inputs are at indices `0..7` and `out` is at index `8`. As the
`Com` binds new lets, those indices shift one `.there` per bound expression. -/

/-- The 4-limb add writing the whole 256-bit result into the caller-provided
    output memref, built natively over `catCryptDialect`. The carry chain uses the
    seam-covered split ops; the writes use the seam-covered `memrefSetDyn`; the
    result is a `.memref 4` holding all four sum limbs. -/
def bignumAdd4ComMemref : Com catCryptDialect Γ₉ (.memref 4) :=
  -- z := bvConst 1 0     (initial carry-in)
  .var (show Expr catCryptDialect Γ₉ (.sword 1) from
        { op := .bvConst 1 0, retTy_eq := rfl, args := .nil }) <|
  -- s0 := bvAddCarryLo a0 b0 z    [a0=Γ₉idx1, b0=Γ₉idx5 after z bound; z=here]
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there .here)
                 (.cons (.there (.there (.there (.there (.there .here)))))
                 (.cons .here .nil)) }) <|
  -- c1 := bvAddCarryHi a0 b0 z
  --   stack (top→bottom): s0, z, then Γ₉.  a0=idx2, b0=idx6, z=.there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there .here))
                 (.cons (.there (.there (.there (.there (.there (.there .here))))))
                 (.cons (.there .here) .nil)) }) <|
  -- s1 := bvAddCarryLo a1 b1 c1
  --   stack: c1, s0, z, then Γ₉.  a1: Γ₉ idx1 + 3 → .there^4 .here
  --   b1: Γ₉ idx5 + 3 → .there^8 .here ; c1: top → .here
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons .here .nil)) }) <|
  -- c2 := bvAddCarryHi a1 b1 c1
  --   stack: s1, c1, s0, z, then Γ₉.  a1: Γ₉ idx1 + 4 → .there^5 .here
  --   b1: Γ₉ idx5 + 4 → .there^9 .here ; c1: .there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- s2 := bvAddCarryLo a2 b2 c2
  --   stack: c2, s1, c1, s0, z, then Γ₉.  a2: Γ₉ idx2 + 5 → .there^7 .here
  --   b2: Γ₉ idx6 + 5 → .there^11 .here ; c2: top → .here
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                 (.cons .here .nil)) }) <|
  -- c3 := bvAddCarryHi a2 b2 c2
  --   stack: s2, c2, s1, c1, s0, z, then Γ₉.  a2: Γ₉ idx2 + 6 → .there^8 .here
  --   b2: Γ₉ idx6 + 6 → .there^12 .here ; c2: .there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- s3 := bvAddCarryLo a3 b3 c3
  --   stack: c3, s2, c2, s1, c1, s0, z, then Γ₉.  a3: Γ₉ idx3 + 7 → .there^10 .here
  --   b3: Γ₉ idx7 + 7 → .there^14 .here ; c3: top → .here
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
                 (.cons .here .nil)) }) <|
  -- c4 := bvAddCarryHi a3 b3 c3 (bound to keep the carry chain shape identical to
  --   `bignumAdd4ComSplit`; the memref output does not consume the final carry)
  --   stack: s3, c3, s2, c2, s1, c1, s0, z, then Γ₉.  a3: Γ₉ idx3 + 8 → .there^11 .here
  --   b3: Γ₉ idx7 + 8 → .there^15 .here ; c3: .there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- stack now (top→bottom): c4, s3, c3, s2, c2, s1, c1, s0, z, then Γ₉
  -- i0 := bvConst 64 0
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvConst 64 0, retTy_eq := rfl, args := .nil }) <|
  -- i1 := bvConst 64 1
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvConst 64 1, retTy_eq := rfl, args := .nil }) <|
  -- i2 := bvConst 64 2
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvConst 64 2, retTy_eq := rfl, args := .nil }) <|
  -- i3 := bvConst 64 3
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvConst 64 3, retTy_eq := rfl, args := .nil }) <|
  -- m1 := memrefSetDyn 4 out i0 s0
  --   stack (top→bottom): i3, i2, i1, i0, c4, s3, c3, s2, c2, s1, c1, s0, z, then Γ₉
  --   out: Γ₉ idx8, shifted by 13 binders → .there^21 .here
  --   i0: idx3 from top → .there^3 .here
  --   s0: c4=4, s3=5, c3=6, s2=7, c2=8, s1=9, c1=10, s0=11 → .there^11 .here
  .var (show Expr catCryptDialect _ (.memref 4) from
        { op := .memrefSetDyn 4, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))
                 (.cons (.there (.there (.there .here)))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)) }) <|
  -- m2 := memrefSetDyn 4 m1 i1 s1
  --   stack (top→bottom): m1, i3, i2, i1, i0, c4, s3, c3, s2, c2, s1, c1, s0, z, then Γ₉
  --   m1: top → .here
  --   i1: m1=0,i3=1,i2=2,i1=3 → .there^3 .here
  --   s1: m1=0,i3=1,i2=2,i1=3,i0=4,c4=5,s3=6,c3=7,s2=8,c2=9,s1=10 → .there^10 .here
  .var (show Expr catCryptDialect _ (.memref 4) from
        { op := .memrefSetDyn 4, retTy_eq := rfl,
          args := .cons .here
                 (.cons (.there (.there (.there .here)))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) }) <|
  -- m3 := memrefSetDyn 4 m2 i2 s2
  --   stack (top→bottom): m2, m1, i3, i2, i1, i0, c4, s3, c3, s2, c2, s1, c1, s0, z, then Γ₉
  --   m2: top → .here
  --   i2: m2=0,m1=1,i3=2,i2=3 → .there^3 .here
  --   s2: m2=0,m1=1,i3=2,i2=3,i1=4,i0=5,c4=6,s3=7,c3=8,s2=9 → .there^9 .here
  .var (show Expr catCryptDialect _ (.memref 4) from
        { op := .memrefSetDyn 4, retTy_eq := rfl,
          args := .cons .here
                 (.cons (.there (.there (.there .here)))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) }) <|
  -- m4 := memrefSetDyn 4 m3 i3 s3
  --   stack (top→bottom): m3, m2, m1, i3, i2, i1, i0, c4, s3, c3, s2, c2, s1, c1, s0, z, then Γ₉
  --   m3: top → .here
  --   i3: m3=0,m2=1,m1=2,i3=3 → .there^3 .here
  --   s3: m3=0,m2=1,m1=2,i3=3,i2=4,i1=5,i0=6,c4=7,s3=8 → .there^8 .here
  .var (show Expr catCryptDialect _ (.memref 4) from
        { op := .memrefSetDyn 4, retTy_eq := rfl,
          args := .cons .here
                 (.cons (.there (.there (.there .here)))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) }) <|
  -- ret m4   (top of stack)
  .ret .here

/-! ## 3. The denote = spec tie -/

/-- **The output-memref dialect program denotes EXACTLY the abstract memref
    spec.** The carry chain writes the four sum limbs into the output memref at
    indices `0..3`, producing precisely `bignumAddMemrefSpec` — the whole 256-bit
    result, not just the carry. -/
theorem bignumAdd4ComMemref_denote
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (m : Fin 4 → BitVec 64) :
    bignumAdd4ComMemref.denote
        (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 (.cons m .nil)))))))))
      = bignumAddMemrefSpec a0 a1 a2 a3 b0 b1 b2 b3 m := by
  rfl

/-! ## 4. The multi-output read API: each cell holds the matching sum limb

`bignumAddMemrefSpec` writes the four limbs at distinct indices `0,1,2,3` of a
size-4 memref, so reading any cell back returns that limb regardless of the
buffer's prior contents `m`. We expose the readback through `memGetDyn` (the
runtime-index read = the dialect `memrefGetDyn` denote). -/

/-- Reading cell `i` of the output memref returns the `i`-th sum limb of
    `bignumAdd4Split` — i.e. the whole 256-bit result is recoverable, cell by
    cell, from the emitted memref (the multi-output read API). Independent of the
    caller buffer's prior contents `m`. -/
theorem bignumAdd4ComMemref_readback
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (m : Fin 4 → BitVec 64) :
    let r := bignumAddMemrefSpec a0 a1 a2 a3 b0 b1 b2 b3 m
    let s := (bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).2
    memGetDyn r (0 : BitVec 64).toNat = s.1
    ∧ memGetDyn r (1 : BitVec 64).toNat = s.2.1
    ∧ memGetDyn r (2 : BitVec 64).toNat = s.2.2.1
    ∧ memGetDyn r (3 : BitVec 64).toNat = s.2.2.2 := by
  simp only [bignumAddMemrefSpec, memGetDyn, memSetDyn]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- **Each emitted memref cell holds the matching `bignumAdd4` sum limb.**
    Composing `bignumAdd4ComMemref_readback` with `bignumAdd4Split_eq_spec`
    (the split sum equals the abstract `bignumAdd4` sum bit-for-bit): the four
    cells of the output memref are exactly the four limbs of the abstract 256-bit
    add. The whole result is emitted and recoverable. -/
theorem bignumAdd4ComMemref_readback_spec
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (m : Fin 4 → BitVec 64) :
    let r := bignumAddMemrefSpec a0 a1 a2 a3 b0 b1 b2 b3 m
    let s := (bignumAdd4 a0 a1 a2 a3 b0 b1 b2 b3).2
    memGetDyn r (0 : BitVec 64).toNat = s.1
    ∧ memGetDyn r (1 : BitVec 64).toNat = s.2.1
    ∧ memGetDyn r (2 : BitVec 64).toNat = s.2.2.1
    ∧ memGetDyn r (3 : BitVec 64).toNat = s.2.2.2 := by
  have hrb := bignumAdd4ComMemref_readback a0 a1 a2 a3 b0 b1 b2 b3 m
  have hsp := (bignumAdd4Split_eq_spec a0 a1 a2 a3 b0 b1 b2 b3).1
  simp only at hrb ⊢
  rw [hrb.1, hrb.2.1, hrb.2.2.1, hrb.2.2.2,
      show (bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).2
        = (bignumAdd4 a0 a1 a2 a3 b0 b1 b2 b3).2 from hsp]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. The whole result lowered to jasmin

The output-memref program contains only seam-covered ops (`bvConst`,
`bvAddCarryLo`, `bvAddCarryHi`, `memrefSetDyn`), so `cryptoDialectToJasminCom`
succeeds: the `memrefSetDyn` writes lower to jasmin `stackStore`. This is the
whole 256-bit result carried through `catCryptDialect` all the way to
`Com jasminDialect` — the multi-output ABI, not a one-word return. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-- The output-memref carry chain lowers: every op (carry split, `memrefSetDyn`)
    is in the covered fragment. -/
theorem bignumAdd4ComMemref_lowers :
    (cryptoDialectToJasminCom bignumAdd4ComMemref).isSome := by
  native_decide

/-- The lowered Jasmin-dialect output-memref 4-limb add program. -/
def bignumAdd4MemrefJasmin :
    Com jasminDialect (mapCtx Γ₉) (mapTy (.memref 4)) :=
  (cryptoDialectToJasminCom bignumAdd4ComMemref).get bignumAdd4ComMemref_lowers

/-- **The whole 256-bit result, lowered to jasmin.** Composing the dialect
    `denote = spec` tie (`bignumAdd4ComMemref_denote`) with the seam's
    denotation-preservation corollary (`cryptoDialectToJasminCom_denote_eq'`): the
    **jasmin** program denotes (on the transported valuation) to `ctTransTy` of the
    output memref `bignumAddMemrefSpec`. The full 256-bit sum carried through
    `catCryptDialect` ALL THE WAY to jasmin via `stackStore` — the multi-output
    ABI residual, closed. -/
theorem bignumAdd4MemrefJasmin_denote
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (m : Fin 4 → BitVec 64) :
    bignumAdd4MemrefJasmin.denote
        (ctMapValD (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 (.cons m .nil))))))))))
      = ctTransTy (bignumAddMemrefSpec a0 a1 a2 a3 b0 b1 b2 b3 m) := by
  have hlow : cryptoDialectToJasminCom bignumAdd4ComMemref
      = some bignumAdd4MemrefJasmin :=
    (Option.some_get bignumAdd4ComMemref_lowers).symm
  rw [DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq' bignumAdd4ComMemref
        (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 (.cons m .nil))))))))) bignumAdd4MemrefJasmin hlow,
     bignumAdd4ComMemref_denote]

end CatCrypt.Crypto.SecureCompilation.VIR.BignumAddMemrefEmit
