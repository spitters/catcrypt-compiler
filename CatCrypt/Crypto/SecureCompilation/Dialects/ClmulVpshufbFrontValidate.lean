/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd


@[expose] public section
set_option autoImplicit false

/-!
# FRONT validate: `vpclmulqdq` (`clmul`) + `vpshufb` through the LowCT vsimd surface

The `vsimd` front (`TranslateDialectVsimd.translateDialectControlV`) already
exposes the **full** `SimdOp` alphabet through the `RVsimdSetExpr`/`vsimdTag`
LowCT surface — no new front constructor is needed for any ext op:

* `gf2p8mulb` : tag `"vsimd.gf2p8mulb"`   (GFNI byte-wise GF(2^8) multiply)
* `vpshufb`   : tag `"vsimd.vpshufb"`     (per-byte table lookup / shuffle)
* `vpclmulqdq`: tag `"clmul.<imm>"`       (carry-less GF(2)[x] product — GHASH / FAEST)
* `vaesenc`   : tag `"vsimd.vaesenc"`     (one AES round)

`TranslateDialectVsimd` §7 already gates the `gf2p8mulb`+`xor` route end-to-end.
This module closes the coverage hole for the **FAEST QuickSilver / GHASH**-relevant
ext ops `clmul` (`vpclmulqdq`) and `vpshufb`, which had no LowCT-surface validate:
a `RVsimdSetExpr`-authored body is pushed through `translateDialectControlV`,
shown to (1) translate, (2) lower to `Com jasminDialect` through the verified
`cryptoDialectToJasminCom` (reaching owned `.s`), and (3) `denote = spec` on
sample 128-bit inputs — including the **carry-suppression KAT** that distinguishes
the front-routed carry-less product from an integer multiply.

The per-op `denote = spec` is the concrete face of the front-general preservation
theorem `TranslateDialectVsimd.translateDialectControlV_denote` (proven for *any*
covered `vsimd` body): the emitted `.vsimd (.clmul imm)` / `.vsimd .vpshufb` op
denotes by the same `SimdOp.denote` waist as the pure spec.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.Dialects.ClmulVpshufbFrontValidate`
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ClmulVpshufbFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (clmul128W vpshufbW)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 0. Two 128-bit vector params `a` (`.here`), `b` (`.there .here`) -/

/-- Input context: two 128-bit vectors carried as `.sword 128`. -/
def clΓ : Ctx := [.sword 128, .sword 128]

/-- `VarMap` binding `a`, `b` to the two 128-bit slots. -/
def clVM : VarMap clΓ := (VarMap.empty.bind "b").bind "a"

/-! ## 1. `clmul` (`vpclmulqdq`) — a FAEST-shaped multiply-then-accumulate body

`p := clmul.0(a, b)` (the carry-less GF(2)[x] product of the low 64-bit lanes)
then `out := p ⊕ b` — the `acc ^= bf128_mul(...)` accumulate shape at the core of
FAEST QuickSilver's `bf128` inner product, restricted to a straight-line body. -/

/-- The clmul multiply-accumulate LowCT body. -/
def clmulBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "p"   "clmul.0" ["a", "b"])
        (LowCT.RVsimdSetExpr "out" "vsimd.xor" ["p", "b"])

/-- The body is `IsCoveredV` (both ops are vsimd-tagged: `clmul.0`, `vsimd.xor`). -/
theorem clmulBody_covered : IsCoveredV clmulBody :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
        (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))

/-- (1) The body translates through the vsimd front. -/
theorem clmulBody_translates : (translateDialectControlV clVM clmulBody).isSome := by
  native_decide

/-- The front-emitted result program (returns the `.sword 128` slot `out`). -/
def clmulProg : Option (Com catCryptDialect clΓ (.sword 128)) :=
  vsimdResultProg clVM clmulBody "out"

/-- The front actually emits a result program. -/
theorem clmulProg_isSome : clmulProg.isSome := by native_decide

/-- (2) It lowers end-to-end to `Com jasminDialect` through the verified
    `cryptoDialectToJasminCom` map — i.e. it reaches owned `.s`. -/
theorem clmulProg_lowers : (clmulProg.bind cryptoDialectToJasminCom).isSome := by
  native_decide

/-- The pure-Lean spec of `clmulBody`: `clmul.0(a,b) ⊕ b`. -/
def clmulSpec (a b : BitVec 128) : BitVec 128 := clmul128W a b 0 ^^^ b

/-- Denote the front-emitted program at inputs `a` (slot `a`), `b` (slot `b`). -/
def clmulDenote (a b : BitVec 128) : Option (BitVec 128) :=
  clmulProg.map (fun com => com.denote (.cons a (.cons b .nil)))

/-! ### (3) `denote = spec` on sample 128-bit inputs -/

example : clmulDenote 0 0 = some (clmulSpec 0 0) := by native_decide

example :
    clmulDenote 0x00112233445566778899aabbccddeeff 0x0102040810204080ff00ff00ff00ff00
      = some (clmulSpec 0x00112233445566778899aabbccddeeff
                        0x0102040810204080ff00ff00ff00ff00) := by
  native_decide

/-! ### (3b) Carry-suppression KAT — the front routes a GENUINE carry-less product

`clmul.0` on low lanes `a = b = 3` (`x + 1`) yields `(x+1)² = x² + 1 = 5` over
`GF(2)[x]`, NOT the integer `3 · 3 = 9`. Threaded through the `⊕ b` accumulate:
`clmulSpec 3 3 = 5 ⊕ 3 = 6`. The smallest witness that the front-emitted op is
carry-*less* (schoolbook shift-and-XOR, no carry propagation), the defining
property a `vpclmulqdq` GHASH / FAEST field multiply relies on. Compare to the
integer path, which would give `9 ⊕ 3 = 10`. -/

/-- The raw front-routed clmul (no accumulate) at `a = b = 3` is `5`, not `9`. -/
theorem clmul_carry_suppression_kat :
    clmul128W (3 : BitVec 128) (3 : BitVec 128) 0 = 5 := by native_decide

/-- Full front `denote = spec` at the carry-suppression witness: `5 ⊕ 3 = 6`. -/
theorem clmulDenote_carry_suppression :
    clmulDenote 3 3 = some 6 := by native_decide

/-! ## 2. `vpshufb` — a per-byte shuffle body

`z := vpshufb(a, idx)` (byte-wise table lookup: `z[k] = a[idx[k] & 0x0F]`, `0`
when the index byte's top bit is set) — the AES / GF byte-permute at the core of
the SIMD S-box and GHASH byte-reflect kernels. -/

/-- The vpshufb LowCT body: `z := vpshufb(a, b)`. -/
def shufBody : LowCT :=
  LowCT.RVsimdSetExpr "z" "vsimd.vpshufb" ["a", "b"]

/-- The body is `IsCoveredV`. -/
theorem shufBody_covered : IsCoveredV shufBody :=
  isCoveredV_RVsimdSetExpr _ _ _ (by native_decide)

/-- (1) The body translates through the vsimd front. -/
theorem shufBody_translates : (translateDialectControlV clVM shufBody).isSome := by
  native_decide

/-- The front-emitted result program (returns the `.sword 128` slot `z`). -/
def shufProg : Option (Com catCryptDialect clΓ (.sword 128)) :=
  vsimdResultProg clVM shufBody "z"

/-- The front emits a result program. -/
theorem shufProg_isSome : shufProg.isSome := by native_decide

/-- (2) It lowers end-to-end to `Com jasminDialect` (reaches owned `.s`). -/
theorem shufProg_lowers : (shufProg.bind cryptoDialectToJasminCom).isSome := by
  native_decide

/-- The pure-Lean spec of `shufBody`: `vpshufb(a, b)`. -/
def shufSpec (a b : BitVec 128) : BitVec 128 := vpshufbW a b

/-- Denote the front-emitted program at inputs `a`, `b`. -/
def shufDenote (a b : BitVec 128) : Option (BitVec 128) :=
  shufProg.map (fun com => com.denote (.cons a (.cons b .nil)))

/-! ### (3) `denote = spec` on sample 128-bit inputs -/

example :
    shufDenote 0x000102030405060708090a0b0c0d0e0f
               0x0f0e0d0c0b0a09080706050403020100
      = some (shufSpec 0x000102030405060708090a0b0c0d0e0f
                       0x0f0e0d0c0b0a09080706050403020100) := by
  native_decide

/-- **Identity-shuffle KAT.** The index vector `0x0f0e…0100` has (little-endian)
    byte `i` equal to `i`, so `vpshufb a idx` copies source byte `i` to output byte
    `i` — the identity permutation `out = a`. A recognizable `vpshufb` behaviour
    (a lane-select mask that is a no-op). -/
example :
    shufDenote 0x000102030405060708090a0b0c0d0e0f
               0x0f0e0d0c0b0a09080706050403020100
      = some 0x000102030405060708090a0b0c0d0e0f := by
  native_decide

/-- **High-bit-clears-lane KAT.** Index bytes with the top bit set (`0x80`) zero
    the corresponding output lane — the documented `vpshufb` masking semantics. -/
example : shufDenote 0xffffffffffffffffffffffffffffffff 0x80808080808080808080808080808080
    = some 0 := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.ClmulVpshufbFrontValidate
