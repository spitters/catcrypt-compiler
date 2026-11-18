/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.AES.AESSpec
public import CatCrypt.Crypto.Jasmin.AES.AESJazz
public import CatCrypt.Crypto.Jasmin.JasminTranslate
public import CatCrypt.Core.Code
public import CatCrypt.Deep.Eval

/-!
# AES-128: instruction-level key expansion and decryption correctness

Two facts about the AES-NI instruction semantics of `JasminOps.lean` and the
functional AES-128 specification of `AESSpec.lean`.

## Main results

* `expandRound_correct` — one key-expansion round as the AES-NI instruction
  sequence of `AESJazz.expandRound` (`VAESKEYGENASSIST`, `VPSHUFD 0xFF`, three
  `VPSLLDQ 4`/`VPXOR` steps and a final `VPXOR`), computed on the instruction
  semantics, equals the FIPS 197 round `keyExpand`.
* `aes_inv_correct` — `aes128Inv` inverts `aes128`, by a ten-round telescoping
  argument from the cancellation lemmas of `JasminOps.lean`.

The statements are about the instruction semantics `wAESKEYGENASSIST`,
`wVPSHUFD`, `wVPSLLDQ`, `wVPXOR`, `wAESDEC` and `wAESDECLAST`; they do not
mention the Jasmin program `aesProg` or its translation `aesTranslated`.

## References

- FIPS 197, Sections 5.2 (key expansion) and 5.3 (inverse cipher)
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.AES

open CatCrypt.Deep
open CatCrypt.Core
open CatCrypt.Crypto.Jasmin

noncomputable section

/-! ## Key expansion through the AES-NI instruction sequence -/

/-- Byte `j` of `rotWord w` is byte `j - 1 mod 4` of `w`. -/
theorem rotWord_bytes (w : BitVec 32) :
    (rotWord w >>> 0).truncate 8 = (w >>> 24).truncate 8 ∧
    (rotWord w >>> 8).truncate 8 = (w >>> 0).truncate 8 ∧
    (rotWord w >>> 16).truncate 8 = (w >>> 8).truncate 8 ∧
    (rotWord w >>> 24).truncate 8 = (w >>> 16).truncate 8 := by
  unfold rotWord
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- `SubWord` commutes with `RotWord`: the S-box acts bytewise and `RotWord`
    permutes the bytes. -/
theorem subWord_rotWord (w : BitVec 32) : subWord (rotWord w) = rotWord (subWord w) := by
  obtain ⟨h0, h1, h2, h3⟩ := rotWord_bytes w
  unfold subWord
  rw [h0, h1, h2, h3]
  generalize aesSBox ((w >>> 0).truncate 8) = b0
  generalize aesSBox ((w >>> 8).truncate 8) = b1
  generalize aesSBox ((w >>> 16).truncate 8) = b2
  generalize aesSBox ((w >>> 24).truncate 8) = b3
  unfold rotWord
  bv_decide

/-- Unfolding lemma of `wVPSHUFD` at control byte `0xFF`: column 3 of the
    source in all four columns. -/
theorem wVPSHUFD_FF (src : BitVec 128) :
    wVPSHUFD src 0xFF =
      setCol128 (setCol128 (setCol128 (setCol128 0 0 (getCol128 src 3)) 1
        (getCol128 src 3)) 2 (getCol128 src 3)) 3 (getCol128 src 3) := by
  rfl

/-- Column 3 of `VAESKEYGENASSIST src rc` is `RotWord (SubWord w₃) ⊕ rc`. -/
theorem getCol128_wAESKEYGENASSIST_3 (src : BitVec 128) (rc : BitVec 8) :
    getCol128 (wAESKEYGENASSIST src rc) 3 =
      rotWord (subWord (getCol128 src 3)) ^^^ rc.zeroExtend 32 := by
  unfold wAESKEYGENASSIST
  simp only [getCol128, setCol128]
  bv_decide

/-- One AES-128 key-expansion round as computed by the AES-NI instruction
    sequence of `AESJazz.expandRound` on the instruction semantics:
    `tmp1 = VPSHUFD (VAESKEYGENASSIST key rc) 0xFF`, then three steps
    `key = key ⊕ VPSLLDQ key 4`, then `key = key ⊕ tmp1`. The result is the
    FIPS 197 round `keyExpand key rc`. -/
theorem expandRound_correct (key : BitVec 128) (rc : BitVec 8) :
    let tmp1 := wVPSHUFD (wAESKEYGENASSIST key rc) 0xFF
    let k1 := wVPXOR key (wVPSLLDQ key 4)
    let k2 := wVPXOR k1 (wVPSLLDQ k1 4)
    let k3 := wVPXOR k2 (wVPSLLDQ k2 4)
    wVPXOR k3 tmp1 = keyExpand key rc := by
  intro tmp1 k1 k2 k3
  simp only [tmp1, k3, k2, k1, wVPSHUFD_FF, getCol128_wAESKEYGENASSIST_3,
    ← subWord_rotWord]
  unfold keyExpand
  simp only [getKeyWord, mkKey]
  generalize subWord (rotWord (getCol128 key 3)) = t
  simp only [wVPXOR, wVPSLLDQ, getCol128, setCol128]
  bv_decide

/-! ## Decryption inverts encryption -/

/-- wAESDEC applied to SR(SB(s)) with key K simplifies via ISR∘ISB∘SR∘SB = id. -/
theorem wAESDEC_SR_SB (s K : BitVec 128) :
    wAESDEC (aesShiftRows (aesSubBytes s)) K =
    aesInvMixColumns (s ^^^ K) := by
  simp only [wAESDEC, aesInvShiftRows_aesInvSubBytes_aesShiftRows_aesSubBytes]

/-- wAESDEC cancels wAESENC when applied with the same key. -/
theorem wAESDEC_wAESENC (prev K : BitVec 128) :
    wAESDEC (aesShiftRows (aesSubBytes (wAESENC prev K))) K =
    aesShiftRows (aesSubBytes prev) := by
  rw [wAESDEC_SR_SB, wAESENC, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
      aesInvMixColumns_aesMixColumns]

/-- wAESDECLAST cancels SR∘SB via ISR∘ISB∘SR∘SB = id. -/
theorem wAESDECLAST_SR_SB (s K : BitVec 128) :
    wAESDECLAST (aesShiftRows (aesSubBytes s)) K = s ^^^ K := by
  simp only [wAESDECLAST, aesInvShiftRows_aesInvSubBytes_aesShiftRows_aesSubBytes]

/-- XOR is self-inverse. -/
theorem bv_xor_cancel {n : Nat} (a b : BitVec n) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

set_option maxHeartbeats 4000000 in
-- The ten unrolled rounds of both ciphers are elaborated as one term.
/-- Decryption is the inverse of encryption (10-round telescoping).
    Each decryption round peels off one encryption round using:
    ISR∘ISB∘SR∘SB = id, IMC∘MC = id, and XOR self-cancellation. -/
theorem aes_inv_correct (key msg : BitVec 128) :
    aes128Inv key (aes128 key msg) = msg := by
  unfold aes128Inv aes128
  simp only [List.range, List.range.loop, List.foldl_cons, List.foldl_nil]
  set K := keySchedule key
  set s₀ := msg ^^^ K 0
  set s₁ := wAESENC s₀ (K 1)
  set s₂ := wAESENC s₁ (K 2)
  set s₃ := wAESENC s₂ (K 3)
  set s₄ := wAESENC s₃ (K 4)
  set s₅ := wAESENC s₄ (K 5)
  set s₆ := wAESENC s₅ (K 6)
  set s₇ := wAESENC s₆ (K 7)
  set s₈ := wAESENC s₇ (K 8)
  set s₉ := wAESENC s₈ (K 9)
  change wAESDECLAST
    (wAESDEC (wAESDEC (wAESDEC (wAESDEC (wAESDEC (wAESDEC (wAESDEC (wAESDEC
      (wAESDEC (wAESENCLAST s₉ (K 10) ^^^ K 10) (K 9)) (K 8)) (K 7)) (K 6))
      (K 5)) (K 4)) (K 3)) (K 2)) (K 1)) (K 0) = msg
  -- Cancel K₁₀ from cipher ⊕ K₁₀
  rw [show wAESENCLAST s₉ (K 10) ^^^ K 10 =
        aesShiftRows (aesSubBytes s₉) from by unfold wAESENCLAST; exact bv_xor_cancel _ _]
  -- Peel off 9 encryption rounds
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₉)) (K 9) =
        aesShiftRows (aesSubBytes s₈) from wAESDEC_wAESENC s₈ (K 9)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₈)) (K 8) =
        aesShiftRows (aesSubBytes s₇) from wAESDEC_wAESENC s₇ (K 8)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₇)) (K 7) =
        aesShiftRows (aesSubBytes s₆) from wAESDEC_wAESENC s₆ (K 7)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₆)) (K 6) =
        aesShiftRows (aesSubBytes s₅) from wAESDEC_wAESENC s₅ (K 6)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₅)) (K 5) =
        aesShiftRows (aesSubBytes s₄) from wAESDEC_wAESENC s₄ (K 5)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₄)) (K 4) =
        aesShiftRows (aesSubBytes s₃) from wAESDEC_wAESENC s₃ (K 4)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₃)) (K 3) =
        aesShiftRows (aesSubBytes s₂) from wAESDEC_wAESENC s₂ (K 3)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₂)) (K 2) =
        aesShiftRows (aesSubBytes s₁) from wAESDEC_wAESENC s₁ (K 2)]
  rw [show wAESDEC (aesShiftRows (aesSubBytes s₁)) (K 1) =
        aesShiftRows (aesSubBytes s₀) from wAESDEC_wAESENC s₀ (K 1)]
  -- Final step: cancel K₀
  rw [wAESDECLAST_SR_SB s₀ (K 0)]
  exact bv_xor_cancel msg (K 0)

end

end CatCrypt.Crypto.Jasmin.AES
