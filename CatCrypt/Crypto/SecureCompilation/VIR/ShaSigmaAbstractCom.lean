/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ShaRoundAbstractCom
public import CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom

/-!
# Abstract FIPS-180-4 SHA-512 σ₁ / Σ₀ / Σ₁ ties for the unified-`Com` lane kernels

`ShaRoundAbstractCom.lean` re-anchored the SHA-512 **σ₀** small-sigma lane
function (`Primitives.SHA512.smallSigma0`, `ROTR¹ ⊕ ROTR⁸ ⊕ SHR⁷`) onto the
unified `Com jasminDialect` `zmmPackQ` denotation, off the bespoke `Avx512Model`
machine. Per that module's own scope note, the companion σ/Σ mixing functions
reuse the **identical** `vpackZMM .shr/.shl/.or/.xor` idiom at different rotate
amounts:

* `smallSigma1 = ROTR¹⁹ ⊕ ROTR⁶¹ ⊕ SHR⁶`  (amounts `(19,61,6)`, one shift tail)
* `bigSigma0   = ROTR²⁸ ⊕ ROTR³⁴ ⊕ ROTR³⁹` (amounts `(28,34,39)`, rotate-only)
* `bigSigma1   = ROTR¹⁴ ⊕ ROTR¹⁸ ⊕ ROTR⁴¹` (amounts `(14,18,41)`, rotate-only)

This module completes that σ/Σ web. For each it (i) builds the
`Com jasminDialect` straight-line kernel out of broadcast-shift `vpackZMM` ops
(broadcast shift-counts threaded as context registers, exactly as `sigma0Com`),
(ii) pins its denotation to a packed `zmmPackQ` expression (`*Com_denote`, a
kernel `rfl`), (iii) characterises lane `k` (`*Com_lane`), and (iv) proves the
abstract tie `*Com_lane_abstract`: lane `k`, cast to `BitVec 64`, equals the
FIPS-180-4 abstract function `Primitives.SHA512.{smallSigma1,bigSigma0,bigSigma1}`
read off `toBitVec`.

The bridge generalises `ShaRoundAbstractCom.rotr1_toBitVec` /`rotr8_toBitVec`
to any rotate amount `n < 64` (`rotr_toBitVec`): the abstract
`UInt64` `rotr x n` on its `toBitVec` is the BitVec shift-or
`(x >>> n) ||| (x <<< (64 - n))`. The per-lane `zmmPackQ_lane`, `constZmm_lane`,
and the 8×u64 lane round-trip come straight from the pilot module.

There is no `runZBlock` / `ZInstr` / `ZState` / `jasminc` / `jasminc_preserves_ct`
in any theorem's `#print axioms`: every tie is between the verified
`Com jasminDialect` denotation and the abstract FIPS-180-4 σ/Σ function.

## Scope — the σ/Σ message-schedule + round-mixing lane functions

Together with the σ₀ pilot this re-anchors all four FIPS-180-4 §4.1.3 rotate-xor
mixing functions (the two message-schedule σ and the two round Σ). What remains
of the full SHA-512 round (FIPS-180-4 §6.4) is the **boolean / additive**
combine: `Ch`, `Maj`, and the `T1 = h + Σ₁ e + Ch + Kt + Wt` / `T2 = Σ₀ a + Maj`
modular-add accumulation — a different (vpand/vpor/vpaddq) idiom, not a
rotate-xor lane function, and out of scope for this rotate-anchoring web.

## References
* FIPS 180-4 — SHA-512 (§4.1.3 the σ/Σ functions; §6.4 the compression round).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.ShaSigmaAbstractCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ShaSigmaAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.Primitives
open CatCrypt.Crypto.SecureCompilation.VIR.ShaRoundAbstractCom
open CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated locally
    (mirrors `Sha512X8VpackZmmEmit.r512`). -/
abbrev r512 : JasminTy := .reg 512

/-! ## 1. The generalised abstract `UInt64` rotr ↔ BitVec shift-or bridge

`Primitives.SHA512.rotr x n = (x >>> n) ||| (x <<< (64 - n))` over `UInt64`; on
`toBitVec` this is the BitVec shift-or at the same amounts. This generalises the
pilot module's `rotr1_toBitVec` / `rotr8_toBitVec` to any amount `n < 64`. -/

/-- The abstract `UInt64` `rotr x n` on its `toBitVec` is the BitVec shift-or
    `(x.toBitVec >>> n.toNat) ||| (x.toBitVec <<< (64 - n.toNat))`, for a rotate
    amount below the word width.

    The bound is necessary, not bookkeeping: `UInt64`'s shifts reduce the amount
    modulo 64 while `BitVec`'s do not, and `64 - n.toNat` truncates in `Nat`, so
    the two sides diverge for every `n ≥ 64` — at `x = 7, n = 100` the left side
    is `1879048192` and the right side is `7`. The unconditional characterisation
    of the same operation is `(SHA512.rotr x n).toBitVec =
    x.toBitVec.rotateRight (n.toNat % 64)`. -/
theorem rotr_toBitVec (x n : UInt64) (hn : n.toNat < 64) :
    (SHA512.rotr x n).toBitVec
      = (x.toBitVec >>> n.toNat) ||| (x.toBitVec <<< (64 - n.toNat)) := by
  unfold SHA512.rotr
  rcases Nat.eq_zero_or_pos n.toNat with h0 | hpos
  · simp [h0]
  · simp [Nat.mod_eq_of_lt hn]
    congr 2
    omega

/-! ## 2. σ₁ — `Com` kernel, denotation, lane, abstract tie

`σ₁(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)` — `(rotr,rotr,shr)` shape, identical to
`sigma0Com` at amounts `{19,45,61,3,6}` (rotr-19 = shr 19 ∥ shl 45; rotr-61 =
shr 61 ∥ shl 3; shr 6). De-Bruijn context `[x,c19,c45,c61,c3,c6]`. -/

/-- The migrated SHA-512 σ₁ lane kernel as a `Com jasminDialect`, the same
    9-binding `vpackZMM` shape as `sigma0Com` at the σ₁ amounts. -/
def sigma1Com : Com jasminDialect Sha512X8VpackZmmEmit.sigma0Ctx r512 :=
  .var (.mk (.vpackZMM .shr) rfl
          (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there .here)))
            (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
              .nil)))
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              .nil)))
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)))
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))

/-- **σ₁ denotation pin.** Same packed shape as `sigma0Com_denote`, σ₁ amounts.

    Proved by the single-binding peel chain (`KeccakThetaPiCom.denote_var_vpackZMM`)
    rather than a whole-program `rfl`: each layer's `retTy_eq ▸` cast resolves
    once, so the cost is linear in the binding count. -/
theorem sigma1Com_denote (x c19 c45 c61 c3 c6 : BitVec 512) :
    sigma1Com.denote
        (.cons x (.cons c19 (.cons c45 (.cons c61 (.cons c3 (.cons c6 .nil))))))
      = zmmPackQ .xor
          (zmmPackQ .xor
            (zmmPackQ .or (zmmPackQ .shr x c19) (zmmPackQ .shl x c45))
            (zmmPackQ .or (zmmPackQ .shr x c61) (zmmPackQ .shl x c3)))
          (zmmPackQ .shr x c6) := by
  rw [sigma1Com, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **σ₁ lane characterization.** -/
theorem sigma1Com_lane (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (sigma1Com.denote
          (.cons x (.cons (constZmm 19) (.cons (constZmm 45)
            (.cons (constZmm 61) (.cons (constZmm 3) (.cons (constZmm 6) .nil))))))) k
      = (((zmmLane x k) >>> (19 : Nat) ||| (zmmLane x k) <<< (45 : Nat))
            ^^^ ((zmmLane x k) >>> (61 : Nat) ||| (zmmLane x k) <<< (3 : Nat)))
          ^^^ ((zmmLane x k) >>> (6 : Nat)) := by
  rw [sigma1Com_denote]
  rw [zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane,
    zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.applyLane, constZmm_lane]
  norm_num

/-- **THE ABSTRACT TIE — σ₁.** Lane `k` of the unified `sigma1Com` denotation
    equals the FIPS-180-4 §4.1.3 small-sigma-1 `ROTR¹⁹ ⊕ ROTR⁶¹ ⊕ SHR⁶`
    (`Primitives.SHA512.smallSigma1`), over the verified `Com jasminDialect`
    denotation with no `Avx512Model` dependence. -/
theorem sigma1Com_lane_abstract (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (sigma1Com.denote
          (.cons x (.cons (constZmm 19) (.cons (constZmm 45)
            (.cons (constZmm 61) (.cons (constZmm 3) (.cons (constZmm 6) .nil))))))) k
      = (SHA512.smallSigma1 (UInt64.ofBitVec (zmmLane x k))).toBitVec := by
  rw [sigma1Com_lane]
  unfold SHA512.smallSigma1
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_xor, rotr_toBitVec _ 19 (by decide),
    rotr_toBitVec _ 61 (by decide)]
  simp

/-! ## 3. Σ₀ — `Com` kernel, denotation, lane, abstract tie

`Σ₀(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)` — rotate-only (three rotates, no shift
tail). Each rotate is `shr ∥ shl`; amounts `{28,36,34,30,39,25}`. De-Bruijn
context `[x,c28,c36,c34,c30,c39,c25]` (7 regs). 11 bindings:
three `(shr,shl,or)` rotates + two `xor`. -/

/-- Σ₀'s input context: data word `x` plus six broadcast shift-count constants. -/
abbrev bigSigmaCtx : Ctxt jasminDialect := [r512, r512, r512, r512, r512, r512, r512]

/-- The migrated SHA-512 Σ₀ lane kernel as a `Com jasminDialect`: three rotates
    `(shr∥shl)` xored, amounts `{28,36,34,30,39,25}`. Context
    `[x,c28,c36,c34,c30,c39,c25]`. -/
def bigSigma0Com : Com jasminDialect bigSigmaCtx r512 :=
  -- t28 := x >>> 28 ; ctx [x,c28,c36,c34,c30,c39,c25]; x=0, c28=1
  .var (.mk (.vpackZMM .shr) rfl
          (.cons .here (.cons (.there .here) .nil)))
  -- ctx [t28,x,c28,c36,c34,c30,c39,c25]
  -- t36 := x <<< 36 ; x=1, c36=3
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there .here))) .nil)))
  -- ctx [t36,t28,x,c28,c36,c34,c30,c39,c25]
  -- r28 := t28 ||| t36 ; t28=1, t36=0
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  -- ctx [r28,t36,t28,x,c28,c36,c34,c30,c39,c25]
  -- t34 := x >>> 34 ; x=3, c34=6
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there .here)))
            (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- ctx [t34,r28,t36,t28,x,c28,c36,c34,c30,c39,c25]
  -- t30 := x <<< 30 ; x=4, c30=8
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
              .nil)))
  -- ctx [t30,t34,r28,t36,t28,x,c28,c36,c34,c30,c39,c25]
  -- r34 := t34 ||| t30 ; t34=1, t30=0
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  -- ctx [r34,t30,t34,r28,t36,t28,x,c28,c36,c34,c30,c39,c25]
  -- t39 := x >>> 39 ; x=6, c39=11
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              .nil)))
  -- ctx [t39,r34,t30,t34,r28,t36,t28,x,c28,c36,c34,c30,c39,c25]
  -- t25 := x <<< 25 ; x=7, c25=13
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
              .nil)))
  -- ctx [t25,t39,r34,t30,t34,r28,t36,t28,x,...]
  -- r39 := t39 ||| t25 ; t39=1, t25=0
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  -- ctx [r39,t25,t39,r34,t30,t34,r28,t36,t28,x,...]
  -- m := r28 ^^^ r34 ; r28=6, r34=3
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  -- ctx [m,r39,t25,t39,r34,t30,t34,r28,...]
  -- out := m ^^^ r39 ; m=0, r39=1
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))))

/-- **Σ₀ denotation pin.** Three packed rotates xored, Σ₀ amounts. Proved by the
    single-binding peel chain, as `sigma1Com_denote`. -/
theorem bigSigma0Com_denote (x c28 c36 c34 c30 c39 c25 : BitVec 512) :
    bigSigma0Com.denote
        (.cons x (.cons c28 (.cons c36 (.cons c34 (.cons c30 (.cons c39 (.cons c25 .nil)))))))
      = zmmPackQ .xor
          (zmmPackQ .xor
            (zmmPackQ .or (zmmPackQ .shr x c28) (zmmPackQ .shl x c36))
            (zmmPackQ .or (zmmPackQ .shr x c34) (zmmPackQ .shl x c30)))
          (zmmPackQ .or (zmmPackQ .shr x c39) (zmmPackQ .shl x c25)) := by
  rw [bigSigma0Com, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **Σ₀ lane characterization.** -/
theorem bigSigma0Com_lane (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (bigSigma0Com.denote
          (.cons x (.cons (constZmm 28) (.cons (constZmm 36) (.cons (constZmm 34)
            (.cons (constZmm 30) (.cons (constZmm 39) (.cons (constZmm 25) .nil)))))))) k
      = (((zmmLane x k) >>> (28 : Nat) ||| (zmmLane x k) <<< (36 : Nat))
            ^^^ ((zmmLane x k) >>> (34 : Nat) ||| (zmmLane x k) <<< (30 : Nat)))
          ^^^ ((zmmLane x k) >>> (39 : Nat) ||| (zmmLane x k) <<< (25 : Nat)) := by
  rw [bigSigma0Com_denote]
  rw [zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane,
    zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane,
    zmmPackQ_lane]
  simp only [JasminBinOp.applyLane, constZmm_lane]
  norm_num

/-- **THE ABSTRACT TIE — Σ₀.** Lane `k` of the unified `bigSigma0Com` denotation
    equals the FIPS-180-4 §4.1.3 big-sigma-0 `ROTR²⁸ ⊕ ROTR³⁴ ⊕ ROTR³⁹`
    (`Primitives.SHA512.bigSigma0`), over the verified `Com jasminDialect`
    denotation with no `Avx512Model` dependence. -/
theorem bigSigma0Com_lane_abstract (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (bigSigma0Com.denote
          (.cons x (.cons (constZmm 28) (.cons (constZmm 36) (.cons (constZmm 34)
            (.cons (constZmm 30) (.cons (constZmm 39) (.cons (constZmm 25) .nil)))))))) k
      = (SHA512.bigSigma0 (UInt64.ofBitVec (zmmLane x k))).toBitVec := by
  rw [bigSigma0Com_lane]
  unfold SHA512.bigSigma0
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_xor, rotr_toBitVec _ 28 (by decide),
    rotr_toBitVec _ 34 (by decide), rotr_toBitVec _ 39 (by decide)]
  simp

/-! ## 4. Σ₁ — `Com` kernel, denotation, lane, abstract tie

`Σ₁(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)` — rotate-only, amounts
`{14,50,18,46,41,23}`. Context `[x,c14,c50,c18,c46,c41,c23]`. -/

/-- The migrated SHA-512 Σ₁ lane kernel as a `Com jasminDialect`: three rotates
    `(shr∥shl)` xored, amounts `{14,50,18,46,41,23}`. -/
def bigSigma1Com : Com jasminDialect bigSigmaCtx r512 :=
  .var (.mk (.vpackZMM .shr) rfl
          (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there .here)))
            (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
              .nil)))
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              .nil)))
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
              .nil)))
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))))

/-- **Σ₁ denotation pin.** Three packed rotates xored, Σ₁ amounts. Proved by the
    single-binding peel chain, as `sigma1Com_denote`. -/
theorem bigSigma1Com_denote (x c14 c50 c18 c46 c41 c23 : BitVec 512) :
    bigSigma1Com.denote
        (.cons x (.cons c14 (.cons c50 (.cons c18 (.cons c46 (.cons c41 (.cons c23 .nil)))))))
      = zmmPackQ .xor
          (zmmPackQ .xor
            (zmmPackQ .or (zmmPackQ .shr x c14) (zmmPackQ .shl x c50))
            (zmmPackQ .or (zmmPackQ .shr x c18) (zmmPackQ .shl x c46)))
          (zmmPackQ .or (zmmPackQ .shr x c41) (zmmPackQ .shl x c23)) := by
  rw [bigSigma1Com, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **Σ₁ lane characterization.** -/
theorem bigSigma1Com_lane (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (bigSigma1Com.denote
          (.cons x (.cons (constZmm 14) (.cons (constZmm 50) (.cons (constZmm 18)
            (.cons (constZmm 46) (.cons (constZmm 41) (.cons (constZmm 23) .nil)))))))) k
      = (((zmmLane x k) >>> (14 : Nat) ||| (zmmLane x k) <<< (50 : Nat))
            ^^^ ((zmmLane x k) >>> (18 : Nat) ||| (zmmLane x k) <<< (46 : Nat)))
          ^^^ ((zmmLane x k) >>> (41 : Nat) ||| (zmmLane x k) <<< (23 : Nat)) := by
  rw [bigSigma1Com_denote]
  rw [zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane,
    zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane,
    zmmPackQ_lane]
  simp only [JasminBinOp.applyLane, constZmm_lane]
  norm_num

/-- **THE ABSTRACT TIE — Σ₁.** Lane `k` of the unified `bigSigma1Com` denotation
    equals the FIPS-180-4 §4.1.3 big-sigma-1 `ROTR¹⁴ ⊕ ROTR¹⁸ ⊕ ROTR⁴¹`
    (`Primitives.SHA512.bigSigma1`), over the verified `Com jasminDialect`
    denotation with no `Avx512Model` dependence. -/
theorem bigSigma1Com_lane_abstract (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (bigSigma1Com.denote
          (.cons x (.cons (constZmm 14) (.cons (constZmm 50) (.cons (constZmm 18)
            (.cons (constZmm 46) (.cons (constZmm 41) (.cons (constZmm 23) .nil)))))))) k
      = (SHA512.bigSigma1 (UInt64.ofBitVec (zmmLane x k))).toBitVec := by
  rw [bigSigma1Com_lane]
  unfold SHA512.bigSigma1
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_xor, rotr_toBitVec _ 14 (by decide),
    rotr_toBitVec _ 18 (by decide), rotr_toBitVec _ 41 (by decide)]
  simp

end CatCrypt.Crypto.SecureCompilation.VIR.ShaSigmaAbstractCom
