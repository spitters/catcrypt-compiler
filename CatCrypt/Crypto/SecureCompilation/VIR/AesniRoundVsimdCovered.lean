/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote


@[expose] public section
set_option autoImplicit false

/-!
# AES-NI encryption block re-sourced through the `vsimd` vector front

The AES-NI encryption block (FIPS-197 §5.1, the `_mm_aesenc_si128` /
`_mm_aesenclast_si128` intrinsic chain) is a straight-line composite of one
`vpxor` initial `AddRoundKey`, nine `vaesenc` rounds (each is the fused
`SubBytes ; ShiftRows ; MixColumns ; AddRoundKey`), and one closing `vaesenclast`
round (no `MixColumns`). Every op threads a `.sword 128` state register.

This is the **AES-NI analogue of the scalar `Shake256Covered`**: the block is
authored as a high-level `LowCT` term over the covered SIMD-vector fragment
`IsCoveredV` and descends through the **existing** vector front
`translateDialectControlV` (no new front), carrying a **whole-program machine
denote** banked from the front-general preservation theorem
`translateDialectControlV_denote`.

The current AES-NI emits (`AESCCM/BytesVsimdEmit`, `FAEST/Owf128VsimdEmit`) are
hand-built on `Com jasminDialect`; this re-sources the same `vaesenc`/
`vaesenclast`/`vpxor` chain from the LowCT surface, exactly as
`ClmulVpshufbFrontValidate` / `VconstFrontValidate` re-source the GHASH/FAEST
ext ops — but as a *whole-program* descent with a symbolic denote homomorphism,
not just per-input `denote = spec` pins.

## Key schedule

The eleven round keys enter as `.sword 128` **input slots** (`rk0 … rk10`),
matching the AES-NI convention where the schedule is expanded once and the round
keys are held in registers across the block. The AES key expansion itself
(`vaeskeygenassist` + `vpshufd $255` + `vpslldq` + `vpxor`) is *also* inside the
covered vector alphabet (`.ukeygen`/`.ushuf`/`.sll`/binary xor tags), so it could
be fused into the same body; it is kept as input slots here to keep the block the
clean AES-NI round chain the task targets.

## What is banked

* `aesBody` — the AES-128 block as `RSeq` of one `vsimd.xor`, nine
  `vsimd.vaesenc`, and one `vsimd.vaesenclast` `RVsimdSetExpr` node.
* `aesBody_covered : IsCoveredV aesBody` — the structural coverage proof.
* `aesBody_frontV_fires` — the vector front fires on the whole block
  (`native_decide`), and `aesProg_lowers` — it lowers end-to-end to
  `Com jasminDialect` through the verified `cryptoDialectToJasminCom`.
* `aesRoundVsimdCovered_denote` — **the deliverable**: the whole-program machine
  denote of the AES-NI block through the vector front, a one-line application of
  `translateDialectControlV_denote`.
* `aesDenote_fips197_c1` — the FIPS-197 Appendix C.1 known-answer test, run
  through the front-emitted program's own `denote`, corroborating the descent
  against the published AES-128 vector.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.AesniRoundVsimdCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The high-level source: AES-NI block as `xor ; aesenc×9 ; aesenclast` -/

/-- Twelve 128-bit vector slots: the plaintext `pt` and the eleven round keys
    `rk0 … rk10`, all carried as `.sword 128`. -/
def aesΓ : Ctx :=
  [.sword 128, .sword 128, .sword 128, .sword 128, .sword 128, .sword 128,
   .sword 128, .sword 128, .sword 128, .sword 128, .sword 128, .sword 128]

/-- Name resolver binding `pt` (`.here`) and `rk0 … rk10` (successive `.there`).
    The last `bind` is the head, so `pt` resolves to `.here`, `rk0` to
    `.there .here`, …, `rk10` to the deepest slot. -/
def aesVM : VarMap aesΓ :=
  ((((((((((((VarMap.empty.bind "rk10").bind "rk9").bind "rk8").bind "rk7").bind
    "rk6").bind "rk5").bind "rk4").bind "rk3").bind "rk2").bind "rk1").bind "rk0").bind "pt")

/-- **The AES-128 encryption block** authored over the covered vector fragment:
    the initial `AddRoundKey` (`vpxor`), nine full `vaesenc` rounds, and the
    closing `vaesenclast` round — each a `vsimd`-tagged `RVsimdSetExpr` threading
    the `.sword 128` running state. -/
def aesBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "s0" "vsimd.xor" ["pt", "rk0"])
  (.RSeq (LowCT.RVsimdSetExpr "s1" "vsimd.vaesenc" ["s0", "rk1"])
  (.RSeq (LowCT.RVsimdSetExpr "s2" "vsimd.vaesenc" ["s1", "rk2"])
  (.RSeq (LowCT.RVsimdSetExpr "s3" "vsimd.vaesenc" ["s2", "rk3"])
  (.RSeq (LowCT.RVsimdSetExpr "s4" "vsimd.vaesenc" ["s3", "rk4"])
  (.RSeq (LowCT.RVsimdSetExpr "s5" "vsimd.vaesenc" ["s4", "rk5"])
  (.RSeq (LowCT.RVsimdSetExpr "s6" "vsimd.vaesenc" ["s5", "rk6"])
  (.RSeq (LowCT.RVsimdSetExpr "s7" "vsimd.vaesenc" ["s6", "rk7"])
  (.RSeq (LowCT.RVsimdSetExpr "s8" "vsimd.vaesenc" ["s7", "rk8"])
  (.RSeq (LowCT.RVsimdSetExpr "s9" "vsimd.vaesenc" ["s8", "rk9"])
        (LowCT.RVsimdSetExpr "out" "vsimd.vaesenclast" ["s9", "rk10"]))))))))))

/-! ## 2. Coverage — the main structural proof -/

/-- **The AES-NI block is `IsCoveredV`**: an `RSeq` spine of eleven `vsimd`-tagged
    `RVsimdSetExpr` nodes (`vsimd.xor`, `vsimd.vaesenc`×9, `vsimd.vaesenclast`),
    every tag parsing. -/
theorem aesBody_covered : IsCoveredV aesBody :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
        (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide)))))))))))

/-! ## 3. The front fires and lowers -/

/-- **The vector front fires on the whole AES-NI block.** -/
theorem aesBody_frontV_fires : (translateDialectControlV aesVM aesBody).isSome := by
  native_decide

/-- The front-emitted result program, returning the `.sword 128` ciphertext slot
    `out`. -/
def aesProg : Option (Com catCryptDialect aesΓ (.sword 128)) :=
  vsimdResultProg aesVM aesBody "out"

/-- The front actually emits a result program. -/
theorem aesProg_isSome : aesProg.isSome := by native_decide

/-- It lowers end-to-end to `Com jasminDialect` through the verified
    `cryptoDialectToJasminCom` map — i.e. it reaches the owned `.s` backend. -/
theorem aesProg_lowers : (aesProg.bind cryptoDialectToJasminCom).isSome := by
  native_decide

/-! ## 4. THE DELIVERABLE — the whole-program denote homomorphism

The `Com catCryptDialect` prefix `translateDialectControlV` emits for the AES-NI
block denotes exactly the block's `semV` `SimdOp`-fold semantics (per-tail
continuation), for any consistent context/valuation/env triple. This is a one-line
application of the front-general preservation theorem
`translateDialectControlV_denote` — the AES-NI analogue of
`Shake256Covered.shake256Covered_denote`. The `vaesenc`/`vaesenclast`/`vpxor`
`SimdOp` denote (`wAESENCW`/`wAESENCLASTW`/xor, the FIPS-197 Sail anchor) is
carried by the theorem's per-op step. -/

/-- **Whole-program machine denote of the AES-NI encryption block** through the
    vector front. -/
theorem aesRoundVsimdCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnv) (o : DTransOut Γ),
      ConsistentV vm V env →
      translateDialectControlV vm aesBody = some o →
      semV aesBody env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentV o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  translateDialectControlV_denote aesBody_covered

/-! ## 5. FIPS-197 corroboration — the C.1 known-answer test through the front

The FIPS-197 Appendix C.1 AES-128 vector (`key = 000102…0f`, `plaintext =
00112233…ff`, `ciphertext = 69c4e0d8…c55a`), run through the **front-emitted
program's own `denote`**. AES-NI loads the 16-byte arrays little-endian into the
XMM register, so each published big-endian value is byte-reversed by `brev`; the
model's byte 0 is the register LSB (`JasminDialect.getByte128W`). The published
round keys are the standard AES-128 key schedule of the C.1 key. -/

/-- Byte-reverse a 128-bit value: published big-endian hex → the little-endian
    AES-NI register load. -/
def brev (x : BitVec 128) : BitVec 128 :=
  (List.range 16).foldl (fun acc i =>
    acc ||| (((x >>> ((15 - i) * 8)).truncate 8).zeroExtend 128 <<< (i * 8))) 0

/-- The FIPS-197 C.1 valuation: plaintext then the eleven expanded round keys, each
    published big-endian value byte-reversed for the AES-NI little-endian load. -/
def katVal : Ctxt.Valuation (d := catCryptDialect) aesΓ :=
  .cons (brev 0x00112233445566778899aabbccddeeff)   -- pt
  (.cons (brev 0x000102030405060708090a0b0c0d0e0f)   -- rk0
  (.cons (brev 0xd6aa74fdd2af72fadaa678f1d6ab76fe)   -- rk1
  (.cons (brev 0xb692cf0b643dbdf1be9bc5006830b3fe)   -- rk2
  (.cons (brev 0xb6ff744ed2c2c9bf6c590cbf0469bf41)   -- rk3
  (.cons (brev 0x47f7f7bc95353e03f96c32bcfd058dfd)   -- rk4
  (.cons (brev 0x3caaa3e8a99f9deb50f3af57adf622aa)   -- rk5
  (.cons (brev 0x5e390f7df7a69296a7553dc10aa31f6b)   -- rk6
  (.cons (brev 0x14f9701ae35fe28c440adf4d4ea9c026)   -- rk7
  (.cons (brev 0x47438735a41c65b9e016baf4aebf7ad2)   -- rk8
  (.cons (brev 0x549932d1f08557681093ed9cbe2c974e)   -- rk9
  (.cons (brev 0x13111d7fe3944a17f307a78b4d2b30c5)   -- rk10
   .nil)))))))))))

/-- Denote the front-emitted AES-NI program at the FIPS-197 C.1 inputs. -/
def aesDenote : Option (BitVec 128) := aesProg.map (fun com => com.denote katVal)

/-- **FIPS-197 Appendix C.1 KAT through the front.** The front-sourced AES-128
    block denotes to the published ciphertext `69c4e0d86a7b0430d8cdb78070b4c55a`
    (byte-reversed for the AES-NI register). -/
theorem aesDenote_fips197_c1 :
    aesDenote = some (brev 0x69c4e0d86a7b0430d8cdb78070b4c55a) := by native_decide

/-! ## 6. Axiom audit -/

#print axioms aesBody_covered
#print axioms aesBody_frontV_fires
#print axioms aesRoundVsimdCovered_denote
#print axioms aesDenote_fips197_c1

end CatCrypt.Crypto.SecureCompilation.VIR.AesniRoundVsimdCovered
