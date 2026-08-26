/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8VpackZmmEmit
import CatCrypt.Crypto.Primitives.SHA512
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Abstract FIPS-180-4 SHA-512 σ₀ tie for the unified-`Com` lane kernel (model-free)

`Sha512X8VpackZmmEmit.lean` migrated the SHA-512 8-way σ₀ message-schedule lane
kernel off the bespoke `Avx512Model` (`ZInstr`/`ZState`/`runZBlock`) machine onto
the unified `Com jasminDialect`, and pinned the denotation of `sigma0Com` to a
packed `zmmPackQ` (8×u64) expression over `BitVec 512`
(`sigma0Com_denote`):

```
σ₀(x) = (rotr-by-c1 ⊕ rotr-by-c8) ⊕ shr-by-c7
      = zmmPackQ .xor
          (zmmPackQ .xor
            (zmmPackQ .or (zmmPackQ .shr x c1) (zmmPackQ .shl x c63))
            (zmmPackQ .or (zmmPackQ .shr x c8) (zmmPackQ .shl x c56)))
          (zmmPackQ .shr x c7)
```

— but it stopped at the packed-`BitVec` level: it does NOT tie that packed
expression back to the abstract **FIPS-180-4 §4.1.3 small-sigma-0**
`σ₀(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)` (`Primitives.SHA512.smallSigma0`, over
`UInt64`), per scalar lane.

The bespoke realization web carries that abstract content over the `runZBlock`
machine (`Sha512X8Emit.protrZ_realises_rotr_lane0`, the `psigmaZ` σ-mixing
blocks). The *scalar per-lane σ₀ value* — `ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)` on each
of the 8 u64 lanes — is the abstract content that survives `Avx512Model`
deletion, and that this module **re-anchors** onto the unified `Com jasminDialect`
denotation.

## What is re-anchored (the abstract FIPS-180-4 σ₀ tie)

When the five broadcast shift-count registers are bound to the σ₀ constants
`c1 = 1`, `c63 = 63`, `c8 = 8`, `c56 = 56`, `c7 = 7` (each as `constZmm n`, the
ZMM holding `n` in every 64-bit lane), this module proves, on the unified
denotation and with **no `Avx512Model`** in the import set:

* `zmmOfLanes_zmmLane'` / `zmmPackQ_lane` — the 8×u64 lane round-trip and the
  per-lane characterization of `zmmPackQ` (reproved locally, no AVX-512 model).
* `rotr_toBitVec` — the abstract `UInt64` `rotr x n` equals, on its `toBitVec`,
  the BitVec shift-or `(x >>> n) ||| (x <<< (64-n))` (`0 < n < 64`); and that
  shift-or is `BitVec.rotateRight n`.
* `sigma0Com_lane` — lane `k` of the unified σ₀ denotation, with the σ₀ broadcast
  constants, is the scalar 64-bit value
  `((x_k >>> 1 ||| x_k <<< 63) ⊕ (x_k >>> 8 ||| x_k <<< 56)) ⊕ (x_k >>> 7)`,
  pure `BitVec 64`.
* `sigma0Com_lane_abstract` — **THE ABSTRACT TIE.** Lane `k` of the unified σ₀
  denotation, cast to `BitVec 64`, equals the FIPS-180-4 small-sigma-0
  `(Primitives.SHA512.smallSigma0 (UInt64.ofBitVec (x_k))).toBitVec` — the
  `ROTR¹ ⊕ ROTR⁸ ⊕ SHR⁷` SHA-512 message-schedule lane function, now over
  the verified `Com jasminDialect` denotation.

There is no `runZBlock` / `ZInstr` / `ZState` / `jasminc` / `jasminc_preserves_ct`
in any theorem's `#print axioms`: the tie is between the verified
`Com jasminDialect` denotation and the abstract FIPS-180-4 `smallSigma0`.

## Scope — the σ₀ message-schedule lane function

This re-anchors the **σ₀ small-sigma** lane function — one of the four σ/Σ
mixing functions of the SHA-512 round (FIPS-180-4 §6.4). The companion σ₁ and the
big-Σ₀/Σ₁ (`bigSigma0`/`bigSigma1`) reuse the identical `psigmaZ` idiom at
different rotate amounts (`smallSig1 = (19,61,6)`, `bigSig0 = (28,34,39)`,
`bigSig1 = (14,18,41)`) — each migratable to a `Com` kernel by re-instantiating
`sigma0Com`'s structure, then re-anchored by this module's `rotr_toBitVec` +
`zmmPackQ_lane` bridge. This module is the **pilot lane** of that SHA σ/Σ web:
the σ₀ value seam, proved over the unified denotation, off the bespoke machine.

The `Avx512Model`-side machine-realization wrappers (over `runZBlock`) are MOOT
once `Avx512Model` deletes; the ABSTRACT FIPS-180-4 σ₀ tie is the deliverable, and
it now stands on the unified `Com` denotation.

## References
* FIPS 180-4 — SHA-512 (§4.1.3 the σ/Σ functions; §6.4 the compression round and
  message schedule). `σ₀(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)`.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.ShaRoundAbstractCom`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ShaRoundAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.Primitives

/-! ## 0. The 8×u64 ZMM lane round-trip and per-lane `zmmPackQ`

The qword lane lemmas, reproved locally so this module imports no AVX-512 model —
only `JasminDialect`'s lane defs (transitively via `Sha512X8VpackZmmEmit`) and
Mathlib. Mirrors `MlkemNttAbstractCom.{zmmOfLanes_zmmLane',zmmPackQ_lane}`. -/

/-- Reading lane `k` (a 64-bit qword) of an assembled 8-lane ZMM register recovers
    the `k`-th lane function value: `zmmLane (zmmOfLanes f) k = f k`. -/
theorem zmmOfLanes_zmmLane' (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    (unfold zmmLane zmmOfLanes
     norm_num [Fin.val_ofNat, BitVec.extractLsb'_append_eq_of_le,
       BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_right,
       BitVec.extractLsb'_append_eq_left]) <;>
    rfl

/-- Lane `k` of `zmmPackQ bop a b` is `bop.apply (zmmLane a k) (zmmLane b k)`. -/
theorem zmmPackQ_lane (bop : JasminBinOp) (a b : BitVec 512) (k : Fin 8) :
    zmmLane (zmmPackQ bop a b) k = bop.apply (zmmLane a k) (zmmLane b k) := by
  unfold zmmPackQ
  rw [zmmOfLanes_zmmLane']

/-! ## 1. The σ₀ broadcast shift-count constants

The five shift-count registers are bound to the σ₀ amounts `{1,63,8,56,7}`, each
a ZMM holding the count in every 64-bit lane (the `vpbroadcastq` idiom of the
emitted `.rodata`). -/

/-- The broadcast constant ZMM register holding `m` in every 64-bit lane (the
    `.rodata` `.quad`×8 shift-count idiom of `Sha512X8VpackZmmEmit`). -/
def constZmm (m : Nat) : BitVec 512 := zmmOfLanes (fun _ => BitVec.ofNat 64 m)

/-- Lane `k` of a broadcast constant is the constant. -/
theorem constZmm_lane (m : Nat) (k : Fin 8) :
    zmmLane (constZmm m) k = BitVec.ofNat 64 m := by
  unfold constZmm; rw [zmmOfLanes_zmmLane']

/-! ## 2. The abstract `UInt64` rotr ↔ BitVec rotate bridge

`Primitives.SHA512.rotr x n = (x >>> n) ||| (x <<< (64 - n))` over `UInt64`; on
`toBitVec` this is the BitVec shift-or, which for `0 < n < 64` is the
`BitVec.rotateRight n`. -/

/-- The abstract `UInt64` `rotr x 1` on its `toBitVec` is the BitVec shift-or
    `(x.toBitVec >>> 1) ||| (x.toBitVec <<< 63)`. -/
theorem rotr1_toBitVec (x : UInt64) :
    (SHA512.rotr x 1).toBitVec
      = (x.toBitVec >>> (1 : Nat)) ||| (x.toBitVec <<< (63 : Nat)) := by
  unfold SHA512.rotr; simp

/-- The abstract `UInt64` `rotr x 8` on its `toBitVec` is the BitVec shift-or
    `(x.toBitVec >>> 8) ||| (x.toBitVec <<< 56)`. -/
theorem rotr8_toBitVec (x : UInt64) :
    (SHA512.rotr x 8).toBitVec
      = (x.toBitVec >>> (8 : Nat)) ||| (x.toBitVec <<< (56 : Nat)) := by
  unfold SHA512.rotr; simp

/-- The BitVec shift-or `(x >>> 1) ||| (x <<< 63)` is `rotateRight 1`. -/
theorem shiftor_rotr1 (x : BitVec 64) :
    x >>> (1 : Nat) ||| x <<< (63 : Nat) = x.rotateRight 1 := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

/-- The BitVec shift-or `(x >>> 8) ||| (x <<< 56)` is `rotateRight 8`. -/
theorem shiftor_rotr8 (x : BitVec 64) :
    x >>> (8 : Nat) ||| x <<< (56 : Nat) = x.rotateRight 8 := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

/-! ## 3. The per-lane σ₀ value, pure `BitVec 64`

Lane `k` of the unified σ₀ denotation, with the σ₀ broadcast constants, as the
scalar 64-bit value `((x>>>1 ||| x<<<63) ⊕ (x>>>8 ||| x<<<56)) ⊕ (x>>>7)`. -/

/-- **σ₀ lane characterization.** Lane `k` of `sigma0Com`'s denotation on
    `⟨x, constZmm 1, constZmm 63, constZmm 8, constZmm 56, constZmm 7⟩` is the
    scalar 64-bit value
    `((x_k >>> 1 ||| x_k <<< 63) ⊕ (x_k >>> 8 ||| x_k <<< 56)) ⊕ (x_k >>> 7)`,
    where `x_k = zmmLane x k`. -/
theorem sigma0Com_lane (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (Sha512X8VpackZmmEmit.sigma0Com.denote
          (.cons x (.cons (constZmm 1) (.cons (constZmm 63)
            (.cons (constZmm 8) (.cons (constZmm 56) (.cons (constZmm 7) .nil))))))) k
      = (((zmmLane x k) >>> (1 : Nat) ||| (zmmLane x k) <<< (63 : Nat))
            ^^^ ((zmmLane x k) >>> (8 : Nat) ||| (zmmLane x k) <<< (56 : Nat)))
          ^^^ ((zmmLane x k) >>> (7 : Nat)) := by
  rw [Sha512X8VpackZmmEmit.sigma0Com_denote]
  rw [zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane,
    zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.apply, constZmm_lane]
  norm_num

/-! ## 4. The abstract FIPS-180-4 σ₀ tie

Lane `k` of the unified σ₀ denotation, cast to `BitVec 64`, equals the FIPS-180-4
small-sigma-0 `(Primitives.SHA512.smallSigma0 (UInt64.ofBitVec x_k)).toBitVec`. -/

/-- **THE ABSTRACT TIE — σ₀.** With the σ₀ broadcast constants `{1,63,8,56,7}`,
    lane `k` of the unified `sigma0Com` denotation equals the FIPS-180-4 §4.1.3
    small-sigma-0 `ROTR¹(x_k) ⊕ ROTR⁸(x_k) ⊕ SHR⁷(x_k)` — the SHA-512
    message-schedule σ₀ lane function `Primitives.SHA512.smallSigma0`, read off
    `toBitVec`, now over the verified `Com jasminDialect` denotation with no
    dependence on the `Avx512Model` (`ZInstr`/`runZBlock`) machine. -/
theorem sigma0Com_lane_abstract (x : BitVec 512) (k : Fin 8) :
    zmmLane
        (Sha512X8VpackZmmEmit.sigma0Com.denote
          (.cons x (.cons (constZmm 1) (.cons (constZmm 63)
            (.cons (constZmm 8) (.cons (constZmm 56) (.cons (constZmm 7) .nil))))))) k
      = (SHA512.smallSigma0 (UInt64.ofBitVec (zmmLane x k))).toBitVec := by
  rw [sigma0Com_lane]
  unfold SHA512.smallSigma0
  simp only [UInt64.toBitVec_xor, rotr1_toBitVec, rotr8_toBitVec,
    UInt64.toBitVec_shiftRight]
  congr 1

end CatCrypt.Crypto.SecureCompilation.VIR.ShaRoundAbstractCom
