/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VInstr
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2

/-!
# The SHA-NI instructions of `VInstr` against the SHA-256 reference

The SHA-NI operations of `X86Backend/VInstr.lean` (`VSha.round`, `sha256rnds2X`,
`sha256msg1X`, `sha256msg2X`) and the byte shuffle `vpshufb` stated against the reference
round `sha2RoundRef sha256P` and the message schedule `schedule sha256P` of
`HashTemplate/Sha2.lean`, under the register packings of the SHA-NI code: the working words
`a, b, e, f` in dwords 3 to 0 of one register (`abefOf`) and `c, d, g, h` in dwords 3 to 0
of another (`cdghOf`), and four consecutive schedule words in dwords 0 to 3 of a register
(`schedWin`).

## Main results

* `round_toState`: `VSha.round` with `wk = kt + wt` is `sha2RoundRef sha256P`.
* `rnds2_abef`, `cdgh_round2`: `SHA256RNDS2` performs the two rounds of the two low dwords
  of `XMM0`; the new `C, D, G, H` are the old `A, B, E, F`.
* `rnds2_quartet`: two `SHA256RNDS2` steps, the second on the high dwords of `XMM0`, perform
  four rounds.
* `msg1_window`: `SHA256MSG1` computes `W (t+j) + σ0 (W (t+j+1))` (Intel SDM).
* `schedule_window`: `SHA256MSG1`, `PALIGNR 4`, `PADDD` and `SHA256MSG2` compute the schedule
  words `t + 16` to `t + 19` from the four preceding windows.
* `pshufb_blockWords`: `PSHUFB` with the mask `shufMask` turns sixteen loaded bytes into
  four big-endian message words of `sha256BlockWords`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.VShaSpec

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.HashTemplate (sha256P sha256BlockWords)
open CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2FamilyParams (bigS smallS sha2RoundRef)
open VSha (dw pack rotr)

/-! ## Packings -/

/-- The tuple `(a, b, c, d, e, f, g, h)` of the working words `s 0` to `s 7`. -/
def toState (s : Fin 8 → BitVec 32) : VSha.State := (s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7)

/-- The `ABEF` register of the working words: `a, b, e, f` in dwords 3 to 0. -/
def abefOf (s : Fin 8 → BitVec 32) : BitVec 128 := pack (s 0) (s 1) (s 4) (s 5)

/-- The `CDGH` register of the working words: `c, d, g, h` in dwords 3 to 0. -/
def cdghOf (s : Fin 8 → BitVec 32) : BitVec 128 := pack (s 2) (s 3) (s 6) (s 7)

/-- Two reference rounds with round constants `k0`, `k1` and schedule words `w0`, `w1`. -/
def round2 (s : Fin 8 → BitVec 32) (k0 w0 k1 w1 : BitVec 32) : Fin 8 → BitVec 32 :=
  sha256P.sha2RoundRef (sha256P.sha2RoundRef s k0 w0) k1 w1

/-- The schedule word `W t` of `sha2CompressRef sha256P` on the message words `M`. -/
def schedW (M : Fin 16 → BitVec 32) (t : Nat) : BitVec 32 := sha256P.schedule M t

/-- The schedule words `t` to `t + 3` of the message `M` in dwords 0 to 3. -/
def schedWin (M : Fin 16 → BitVec 32) (t : Nat) : BitVec 128 :=
  pack (schedW M (t + 3)) (schedW M (t + 2)) (schedW M (t + 1)) (schedW M t)

/-- The `PSHUFB` mask that reverses the bytes of each dword. -/
def shufMask : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128

/-! ## Dword access -/

/-- Dword 3 of `pack a b c d` is `a`. -/
theorem dw_pack_3 (a b c d : BitVec 32) : dw (pack a b c d) 3 = a := by
  unfold dw pack; bv_decide

/-- Dword 2 of `pack a b c d` is `b`. -/
theorem dw_pack_2 (a b c d : BitVec 32) : dw (pack a b c d) 2 = b := by
  unfold dw pack; bv_decide

/-- Dword 1 of `pack a b c d` is `c`. -/
theorem dw_pack_1 (a b c d : BitVec 32) : dw (pack a b c d) 1 = c := by
  unfold dw pack; bv_decide

/-- Dword 0 of `pack a b c d` is `d`. -/
theorem dw_pack_0 (a b c d : BitVec 32) : dw (pack a b c d) 0 = d := by
  unfold dw pack; bv_decide

/-! ## Rounds -/

/-- `VSha.round` with `wk = kt + wt` is the reference round `sha2RoundRef sha256P` on the
    working words. -/
theorem round_toState (s : Fin 8 → BitVec 32) (kt wt : BitVec 32) :
    VSha.round (toState s) (kt + wt) = toState (sha256P.sha2RoundRef s kt wt) := by
  have e : ∀ x : BitVec 32, x + (kt + wt) = x + kt + wt :=
    fun x => (BitVec.add_assoc x kt wt).symm
  simp only [toState, VSha.round, e]
  rfl

/-- `SHA256RNDS2` on the `CDGH` and `ABEF` registers of `s`, with `W + K` of two rounds in
    dwords 0 and 1 of `XMM0`, gives the `ABEF` register of the two reference rounds. -/
theorem rnds2_abef (s : Fin 8 → BitVec 32) (wk : BitVec 128) (k0 w0 k1 w1 : BitVec 32)
    (h0 : dw wk 0 = k0 + w0) (h1 : dw wk 1 = k1 + w1) :
    sha256rnds2X (cdghOf s) (abefOf s) wk = abefOf (round2 s k0 w0 k1 w1) := by
  have hs : ((dw (abefOf s) 3, dw (abefOf s) 2, dw (cdghOf s) 3, dw (cdghOf s) 2,
      dw (abefOf s) 1, dw (abefOf s) 0, dw (cdghOf s) 1, dw (cdghOf s) 0) : VSha.State) =
      toState s := by
    simp [abefOf, cdghOf, toState, dw_pack_0, dw_pack_1, dw_pack_2, dw_pack_3]
  unfold sha256rnds2X
  simp only [hs, h0, h1, round_toState]
  rw [round_toState (sha256P.sha2RoundRef s k0 w0) k1 w1]
  rfl

/-- After two rounds, the `CDGH` register is the `ABEF` register before them. -/
theorem cdgh_round2 (s : Fin 8 → BitVec 32) (k0 w0 k1 w1 : BitVec 32) :
    cdghOf (round2 s k0 w0 k1 w1) = abefOf s := by
  simp [cdghOf, abefOf, round2, sha2RoundRef]

/-- **Four rounds by two `SHA256RNDS2` steps.** With `W + K` of four rounds in dwords 0 to 3
    of `wk` and dwords 2, 3 of `wk` in dwords 0, 1 of `wk'`, the first step on
    `(CDGH, ABEF, wk)` and the second on `(ABEF, result, wk')` leave the `ABEF` and `CDGH`
    registers of the four reference rounds. -/
theorem rnds2_quartet (s : Fin 8 → BitVec 32) (k w : Fin 4 → BitVec 32) (wk wk' : BitVec 128)
    (h : ∀ j : Fin 4, dw wk j = k j + w j)
    (h' : dw wk' 0 = dw wk 2 ∧ dw wk' 1 = dw wk 3) :
    ShaOp.denote .rnds2 (abefOf s) (ShaOp.denote .rnds2 (cdghOf s) (abefOf s) wk) wk' =
        abefOf (round2 (round2 s (k 0) (w 0) (k 1) (w 1)) (k 2) (w 2) (k 3) (w 3)) ∧
      ShaOp.denote .rnds2 (cdghOf s) (abefOf s) wk =
        cdghOf (round2 (round2 s (k 0) (w 0) (k 1) (w 1)) (k 2) (w 2) (k 3) (w 3)) := by
  have hA : ShaOp.denote .rnds2 (cdghOf s) (abefOf s) wk =
      abefOf (round2 s (k 0) (w 0) (k 1) (w 1)) := rnds2_abef s wk _ _ _ _ (h 0) (h 1)
  refine ⟨?_, ?_⟩
  · rw [hA, ← cdgh_round2 s (k 0) (w 0) (k 1) (w 1)]
    exact rnds2_abef _ wk' _ _ _ _ (h'.1.trans (h 2)) (h'.2.trans (h 3))
  · rw [hA, cdgh_round2]

/-! ## Vector operations of the SHA-NI code -/

/-- `PSHUFD $0x0e` moves dwords 2 and 3 of its source to dwords 0 and 1. -/
theorem pshufd_0e (a b : BitVec 128) :
    dw (VOp.denote128 .vpshufd 0x0e a b) 0 = dw a 2 ∧
      dw (VOp.denote128 .vpshufd 0x0e a b) 1 = dw a 3 := by
  simp only [VOp.denote128, SimdOp.denote, wVPSHUFDW, setCol128W, getCol128W, dw,
    BitVec.ofNat_eq_ofNat]
  bv_decide

/-- `PADDD` adds dword-wise. -/
theorem paddd_pack (a b : BitVec 128) :
    VOp.denote128 .vpaddd 0 a b =
      pack (dw a 3 + dw b 3) (dw a 2 + dw b 2) (dw a 1 + dw b 1) (dw a 0 + dw b 0) := by
  simp only [VOp.denote128, SimdOp.denote, v128PackLanesW, JasminBinOp.applyLane, pack, dw,
    show 128 / 32 = 4 from rfl, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  bv_decide

/-- `PALIGNR $4` takes dwords 1 to 3 of `SRC2` and dword 0 of `SRC1`. -/
theorem palignr4_pack (a b : BitVec 128) :
    VOp.denote128 .vpalignr 4 a b = pack (dw a 0) (dw b 3) (dw b 2) (dw b 1) := by
  simp only [VOp.denote128, palignr128W, pack, dw, show (4 : BitVec 8).toNat = 4 from rfl]
  bv_decide

/-! ## Message schedule -/

/-- The schedule recursion of `sha256P` with the `σ` functions of `VSha`. -/
theorem schedW_eq (M : Fin 16 → BitVec 32) (n m : Nat) (h : n = m + 16) :
    schedW M n = VSha.smallSigma1 (schedW M (m + 14)) + schedW M (m + 9) +
      VSha.smallSigma0 (schedW M (m + 1)) + schedW M m := by
  subst h
  unfold schedW
  refine (HashTemplate.Sha2FamilyParams.schedule_ge sha256P M (m + 16) (by omega)).trans ?_
  simp only [show m + 16 - 2 = m + 14 by omega, show m + 16 - 7 = m + 9 by omega,
    show m + 16 - 15 = m + 1 by omega, show m + 16 - 16 = m by omega]
  rfl

/-- `SHA256MSG1` on the windows at `t` and `t + 4` computes `W (t+j) + σ0 (W (t+j+1))` in
    dword `j`, with `W (t+4)` from dword 0 of the second window (Intel SDM). -/
theorem msg1_window (M : Fin 16 → BitVec 32) (t : Nat) (x0 : BitVec 128) :
    ShaOp.denote .msg1 (schedWin M t) (schedWin M (t + 4)) x0 =
      pack (schedW M (t + 3) + VSha.smallSigma0 (schedW M (t + 4)))
        (schedW M (t + 2) + VSha.smallSigma0 (schedW M (t + 3)))
        (schedW M (t + 1) + VSha.smallSigma0 (schedW M (t + 2)))
        (schedW M t + VSha.smallSigma0 (schedW M (t + 1))) := by
  simp only [ShaOp.denote, sha256msg1X, schedWin, dw_pack_0, dw_pack_1, dw_pack_2, dw_pack_3]

/-- **One message-schedule step of the SHA-NI code.** `SHA256MSG1` on the windows at `t` and
    `t + 4`, `PADDD` of `PALIGNR $4` of the windows at `t + 12` and `t + 8`, then
    `SHA256MSG2` with the window at `t + 12` give the window at `t + 16` of the schedule of
    `sha2CompressRef sha256P`. -/
theorem schedule_window (M : Fin 16 → BitVec 32) (t : Nat) (x0 x0' : BitVec 128) :
    ShaOp.denote .msg2
        (VOp.denote128 .vpaddd 0 (ShaOp.denote .msg1 (schedWin M t) (schedWin M (t + 4)) x0)
          (VOp.denote128 .vpalignr 4 (schedWin M (t + 12)) (schedWin M (t + 8))))
        (schedWin M (t + 12)) x0' =
      schedWin M (t + 16) := by
  have e16 := schedW_eq M (t + 16) t rfl
  have e17 := schedW_eq M (t + 17) (t + 1) (by omega)
  have e18 := schedW_eq M (t + 18) (t + 2) (by omega)
  have e19 := schedW_eq M (t + 19) (t + 3) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at e16 e17 e18 e19
  rw [msg1_window, palignr4_pack, paddd_pack]
  simp only [ShaOp.denote, sha256msg2X, schedWin, dw_pack_0, dw_pack_1, dw_pack_2, dw_pack_3,
    Nat.add_assoc, Nat.reduceAdd]
  rw [e16, e17, e18, e19]
  grind

/-! ## Byte order of the message words -/

/-- `PSHUFB` with `shufMask` on sixteen little-endian bytes gives in dword `j` the big-endian
    word of bytes `4j` to `4j + 3`. -/
theorem pshufb_bswap (b : Fin 16 → BitVec 8) :
    VOp.denote128 .vpshufb 0 (vPackBytesW b) shufMask =
      pack (b 12 ++ b 13 ++ b 14 ++ b 15) (b 8 ++ b 9 ++ b 10 ++ b 11)
        (b 4 ++ b 5 ++ b 6 ++ b 7) (b 0 ++ b 1 ++ b 2 ++ b 3) := by
  simp only [VOp.denote128, SimdOp.denote, vpshufbW, vPackBytesW, shufMask, pack,
    Fin.foldl_succ_last, Fin.foldl_zero, vByteOfW, Fin.reduceLast, Fin.reduceCastSucc,
    Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMul, Nat.reduceMod]
  bv_decide

/-- The big-endian 32-bit word of four bytes, as `Primitives.SHA256.messageSchedule` forms it,
    is the concatenation of the bytes. -/
theorem be32_toBitVec (a b c d : UInt8) :
    (a.toUInt32 <<< (24 : UInt32) ||| b.toUInt32 <<< (16 : UInt32) |||
      c.toUInt32 <<< (8 : UInt32) ||| d.toUInt32).toBitVec =
      a.toBitVec ++ b.toBitVec ++ c.toBitVec ++ d.toBitVec := by
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32]
  bv_decide

/-- Message word `j` of a SHA-256 block is the big-endian word of bytes `4j` to `4j + 3`. -/
theorem sha256BlockWords_eq (block : Fin 64 → UInt8) (j : Fin 16) :
    sha256BlockWords block j =
      (block ⟨4 * j, by omega⟩).toBitVec ++ (block ⟨4 * j + 1, by omega⟩).toBitVec ++
        (block ⟨4 * j + 2, by omega⟩).toBitVec ++ (block ⟨4 * j + 3, by omega⟩).toBitVec := by
  unfold sha256BlockWords Primitives.SHA256.messageSchedule
  obtain ⟨h1, _⟩ := HashTemplate.sha256_schedule_foldl _ _ (fun _ _ => rfl)
  simp only [Fin.getElem_fin]
  refine (congrArg UInt32.toBitVec (h1 j.val (by omega))).trans ?_
  simp only [Vector.getElem_ofFn, dite_eq_left (show j.val < 16 by omega)]
  exact be32_toBitVec _ _ _ _

/-- **Byte order of the message load.** `PSHUFB` with `shufMask` on bytes `16q` to `16q + 15`
    of a block, loaded little-endian, gives the message words `4q` to `4q + 3` of
    `sha256BlockWords` in dwords 0 to 3. -/
theorem pshufb_blockWords (block : Fin 64 → UInt8) (q : Fin 4) :
    VOp.denote128 .vpshufb 0
        (vPackBytesW fun k => (block ⟨16 * q + k, by omega⟩).toBitVec) shufMask =
      pack (sha256BlockWords block ⟨4 * q + 3, by omega⟩)
        (sha256BlockWords block ⟨4 * q + 2, by omega⟩)
        (sha256BlockWords block ⟨4 * q + 1, by omega⟩)
        (sha256BlockWords block ⟨4 * q, by omega⟩) := by
  rw [pshufb_bswap, sha256BlockWords_eq, sha256BlockWords_eq, sha256BlockWords_eq,
    sha256BlockWords_eq]
  congr 1 <;> grind

end CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.VShaSpec
