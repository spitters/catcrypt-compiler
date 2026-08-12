/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote

set_option autoImplicit false

/-!
# GHASH GF(2^128) one-block multiply re-sourced through the vsimd front (whole-program denote)

The GHASH `out = (y ⊕ x) ·_clmul h` block (the `VPCLMULQDQ` GF(2^128) multiply at
the core of AES-GCM's authenticator) is sourced here from a high-level `LowCT`
term routed through `translateDialectControlV` — the CLMUL analogue of the scalar
`Shake256Covered` — rather than authored directly as a straight-line
`Com jasminDialect` program that bypasses the vsimd front.

The block is the four-schoolbook-`clmul`-product XOR collapse (NO modular
reduction — exactly `ghashMulSpec` below):

```
xv  = y ⊕ x;
tLL = clmul(xv, h, 0x00);  tHL = clmul(xv, h, 0x01);
tLH = clmul(xv, h, 0x10);  tHH = clmul(xv, h, 0x11);
mid = tHL ⊕ tLH;
r   = tLL ⊕ mid;
out = r ⊕ tHH;
```

Every op is a `vsimd`-tagged `RCall` (authored via `RVsimdSetExpr`): the four
schoolbook products are `clmul.<imm>` (decimal imm `0`/`1`/`16`/`17` = `0x00`/
`0x01`/`0x10`/`0x11`), the whitening and collapse are `vsimd.xor`. All eight ops
live in the `SimdOp` alphabet already carried by `translateDialectControlV`, so no
new front constructor and no shape outside `IsCoveredV` is needed. The GHASH block
is UNREDUCED, so no `vpsrldq`/`vpslldq` reduction shifts appear; a fully reduced
GF(2^128) product would add those (also in the alphabet) but would no longer
match the unreduced `ghashMulSpec`.

## What is banked

* `ghashMulVsimdLowCT` — the block as an `RSeq` chain of eight `RVsimdSetExpr` ops.
* `ghashMul_coveredV : IsCoveredV ghashMulVsimdLowCT` — structural coverage.
* `ghashMul_frontV_fires` — the vsimd front fires (`isSome`, `native_decide`).
* `ghashMulProg_lowers` — the front-emitted program lowers end-to-end to
  `Com jasminDialect` through the verified `cryptoDialectToJasminCom` (reaches
  owned `.s`).
* `ghashMulVsimdCovered_denote` — **the deliverable**: the whole-program machine
  denote of the block through the vsimd front, a one-line instantiation of the
  front-general homomorphism `translateDialectControlV_denote`.
* `ghashMulDenote_spec` + samples — the front-emitted program denotes
  `ghashMulSpec` (the `clmul128W`-written GF(2^128) value), plus a
  carry-suppression KAT.

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.GhashClmulVsimdCovered`
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.GhashClmulVsimdCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (clmul128W)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 0. The GHASH-block input context `[y, x, h]` (three 128-bit vectors) -/

/-- Input context: `y`, `x`, `h` carried as `.sword 128`.
    De Bruijn order `y = .here`, `x = .there .here`, `h = .there .there .here`. -/
def ghΓ : Ctx := [.sword 128, .sword 128, .sword 128]

/-- `VarMap` binding `y`, `x`, `h` to the three 128-bit slots. -/
def ghVM : VarMap ghΓ := ((VarMap.empty.bind "h").bind "x").bind "y"

/-! ## 1. The high-level source: the GHASH block as eight `vsimd` ops -/

/-- The GHASH one-block multiply `out = (y ⊕ x) ·_clmul h` (unreduced): the
    `xv = y ⊕ x` whitening, the four schoolbook `clmul` products at lane immediates
    `0x00`/`0x01`/`0x10`/`0x11` (decimal `0`/`1`/`16`/`17`), and the three-`xor`
    collapse — authored as `RVsimdSetExpr` ops through the vsimd front. -/
def ghashMulVsimdLowCT : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "xv"  "vsimd.xor" ["y", "x"])
  (.RSeq (LowCT.RVsimdSetExpr "tLL" "clmul.0"   ["xv", "h"])
  (.RSeq (LowCT.RVsimdSetExpr "tHL" "clmul.1"   ["xv", "h"])
  (.RSeq (LowCT.RVsimdSetExpr "tLH" "clmul.16"  ["xv", "h"])
  (.RSeq (LowCT.RVsimdSetExpr "tHH" "clmul.17"  ["xv", "h"])
  (.RSeq (LowCT.RVsimdSetExpr "mid" "vsimd.xor" ["tHL", "tLH"])
  (.RSeq (LowCT.RVsimdSetExpr "r"   "vsimd.xor" ["tLL", "mid"])
         (LowCT.RVsimdSetExpr "out" "vsimd.xor" ["r", "tHH"])))))))

/-! ## 2. Coverage -/

/-- **The GHASH block is `IsCoveredV`**: an `RSeq` chain of eight `vsimd`-tagged
    `RVsimdSetExpr` ops (four `clmul.<imm>`, four `vsimd.xor`), each tag parsing. -/
theorem ghashMul_coveredV : IsCoveredV ghashMulVsimdLowCT :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
         (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))))))))

/-! ## 3. The vsimd front fires + reaches owned `.s` -/

/-- **The vsimd front fires on the whole GHASH block.** -/
theorem ghashMul_frontV_fires :
    (translateDialectControlV ghVM ghashMulVsimdLowCT).isSome := by native_decide

/-- The front-emitted result program (returns the `.sword 128` slot `out`). -/
def ghashMulProg : Option (Com catCryptDialect ghΓ (.sword 128)) :=
  vsimdResultProg ghVM ghashMulVsimdLowCT "out"

/-- The front actually emits a result program. -/
theorem ghashMulProg_isSome : ghashMulProg.isSome := by native_decide

/-- The front-emitted program lowers end-to-end to `Com jasminDialect` through the
    verified `cryptoDialectToJasminCom` map — i.e. it reaches owned `.s`. -/
theorem ghashMulProg_lowers :
    (ghashMulProg.bind cryptoDialectToJasminCom).isSome := by native_decide

/-! ## 4. `denote = spec`

`ghashMulSpec` is written in terms of `clmul128W` (the byte-identical PCLMULQDQ
lane semantics): the `xv = y ⊕ x` whitening, the four schoolbook carry-less products,
the XOR collapse, NO modular reduction. The front-emitted `.vsimd (.clmul imm)` / `.vsimd (.bitwise
.xor)` ops denote by the same `SimdOp.denote` waist as `clmul128W` / `^^^`, so the
front-routed program computes exactly this value. -/

/-- The GF(2^128) value of the GHASH block, written with `clmul128W` (the
    byte-identical PCLMULQDQ lane semantics). -/
def ghashMulSpec (yv xv hv : BitVec 128) : BitVec 128 :=
  let w := yv ^^^ xv
  let tLL := clmul128W w hv 0
  let tHL := clmul128W w hv 1
  let tLH := clmul128W w hv 16
  let tHH := clmul128W w hv 17
  let mid := tHL ^^^ tLH
  (tLL ^^^ mid) ^^^ tHH

/-- Denote the front-emitted program at inputs `y` (slot `y`), `x`, `h`. -/
def ghashMulDenote (y x h : BitVec 128) : Option (BitVec 128) :=
  ghashMulProg.map (fun com => com.denote (.cons y (.cons x (.cons h .nil))))

/-- **`denote = spec` on sample 128-bit inputs.** -/
theorem ghashMulDenote_spec :
    ghashMulDenote 0x00112233445566778899aabbccddeeff
                   0x0102040810204080ff00ff00ff00ff00
                   0xdeadbeefcafef00d0123456789abcdef
      = some (ghashMulSpec 0x00112233445566778899aabbccddeeff
                           0x0102040810204080ff00ff00ff00ff00
                           0xdeadbeefcafef00d0123456789abcdef) := by
  native_decide

/-- `denote = spec` at the all-zero input (the trivial GHASH block). -/
theorem ghashMulDenote_zero : ghashMulDenote 0 0 0 = some (ghashMulSpec 0 0 0) := by
  native_decide

/-- **Carry-suppression KAT.** With `y = 0`, `x = h = 3` (the field element
    `x + 1`), the block reduces to `(x+1) ·_clmul (x+1) = (x+1)² = x² + 1 = 5` over
    `GF(2)[x]` (the low-lane `clmul.0` product), the four cross products at the
    other immediates vanishing on these single-byte inputs — the defining
    carry-*less* property the `VPCLMULQDQ` GHASH multiply relies on, NOT the integer
    `3 · 3 = 9`. -/
theorem ghashMulDenote_carry_suppression :
    ghashMulDenote 0 3 3 = some 5 := by native_decide

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism

The front-general preservation theorem `translateDialectControlV_denote`,
instantiated at the GHASH block's coverage derivation: the `Com catCryptDialect`
prefix the vsimd front emits denotes exactly the block's `semV` `SimdOp`-fold
semantics, for any consistent context/valuation/env triple. A one-line
instantiation — the CLMUL analogue of `Shake256Covered.shake256Covered_denote`. -/

/-- **Whole-program machine denote of the GHASH block** through the vsimd front:
    for any consistent triple on which the front fires and `semV` succeeds, the
    descended dialect-`Com` prefix denotes exactly the block's `semV` semantics
    (per-tail continuation). -/
theorem ghashMulVsimdCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnv) (o : DTransOut Γ),
      ConsistentV vm V env →
      translateDialectControlV vm ghashMulVsimdLowCT = some o →
      semV ghashMulVsimdLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentV o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  translateDialectControlV_denote ghashMul_coveredV

/-! ## 6. Axiom audit -/

#print axioms ghashMul_coveredV
#print axioms ghashMul_frontV_fires
#print axioms ghashMulProg_lowers
#print axioms ghashMulDenote_spec
#print axioms ghashMulVsimdCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.GhashClmulVsimdCovered
