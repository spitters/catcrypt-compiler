/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.OwnedSha256DwordRoundCom
import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundWords

/-!
# SHA-256 dword round on the unified packed Com is the abstract FIPS-180-4 round

This is the **model-free, equal-strength** reproduction of the bespoke
`OwnedSha256DwordRoundRealization`'s abstract ties `dwordRound_aPrime_eq_SHA` /
`dwordRound_ePrime_eq_SHA`. Those ran the dword round on the bespoke
`Avx512DwordModel` machine (`ZInstr32D`, `runZBlock32D`) and tied each per-lane
output to the abstract `UInt32` round words `aPrimeWord` / `ePrimeWord`
(which anchor to the sealed `Primitives.SHA256.compressRound` via
`aPrimeWord_anchor` / `ePrimeWord_anchor`).

Here we run the round on the **unified packed dword `Com jasminDialect`** — the
committed `aPrimePacked` / `ePrimePacked` (`BitVec 512` outputs assembled from
the 16×u32 packed ops `zmmPackD` / `zmmRorD` of `OwnedSha256DwordRoundCom`) — and
prove **every 32-bit lane** equals the same abstract `UInt32` round word.

The proof is a lane projection: `ZmmDwordLane`'s `zmmPackD_lane` / `zmmRorD_lane`
push `zmmLane32` through each packed op to the per-lane `JasminBinOp.apply` /
`rotateRight`, and `Sha256DwordLane`'s `*_dword_bitExact` ties identify the
per-lane round-function bodies with the abstract `Primitives.SHA256`
`ch` / `maj` / `bigSigma0` / `bigSigma1`. No `native_decide` over `BitVec 512`,
no machine model.

## What is delivered

| result | content | abstract target |
|--------|---------|-----------------|
| `aPrimePacked_lane` | lane `k` of `aPrimePacked` `= (aPrimeWord …).toBitVec` | `aPrimeWord` (→ `compressRound … 0`) |
| `ePrimePacked_lane` | lane `k` of `ePrimePacked` `= (ePrimeWord …).toBitVec` | `ePrimeWord` (→ `compressRound … 4`) |
| `sha256DwordRoundCom_eq_SHA` | the conjunction of both lane ties | both |

`aPrimeWord` / `ePrimeWord` are the **same** abstract `UInt32` round words the
bespoke realization tied to (re-exported here from
`OwnedSha256DwordRoundRealization`), so this matches the bespoke tie's strength:
each lane of the unified-packed round output is the genuine FIPS-180-4 SHA-256
round word, bit-exact at width 32, for every lane and every input. This is the
last abstract gap before `Avx512DwordModel` can be deleted.

## References
* FIPS 180-4 — Secure Hash Standard (§6.2.2 — the compression round).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.OwnedSha256DwordRoundAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.OwnedSha256DwordRoundCom
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundWords
  (aPrimeWord ePrimeWord t1Word)
open CatCrypt.Crypto.Primitives.SHA256 (ch maj bigSigma0 bigSigma1)

/-! ## 1. Lane projection of the packed `Σ`/`Ch`/`Maj` sub-blocks

Each packed sub-expression projects per lane to its dword-lane body
(`Sha256DwordLane.sigma1D` etc.), then to the abstract `UInt32` value via the
`*_dword_bitExact` ties. `zmmRorD n` denotes `BitVec.rotateRight n` per lane,
which equals the `Sha256DwordLane.rorD` shift-decomposition for the SHA amounts
`< 32` (`rorD_eq_rotateRight`). -/

/-- Lane `k` of the packed `Σ₁(e)` block equals the dword-lane `sigma1D` of lane
    `k` of `we`. -/
theorem sig1Packed_lane (we : BitVec 512) (k : Fin 16) :
    zmmLane32 (sig1Packed we) k = sigma1D (zmmLane32 we k) := by
  unfold sig1Packed sigma1D
  rw [zmmPackD_lane, zmmPackD_lane, zmmRorD_lane, zmmRorD_lane, zmmRorD_lane,
    rorD_eq_rotateRight _ _ (by norm_num), rorD_eq_rotateRight _ _ (by norm_num),
    rorD_eq_rotateRight _ _ (by norm_num)]
  rfl

/-- Lane `k` of the packed `Σ₀(a)` block equals the dword-lane `sigma0D`. -/
theorem sig0Packed_lane (wa : BitVec 512) (k : Fin 16) :
    zmmLane32 (sig0Packed wa) k = sigma0D (zmmLane32 wa k) := by
  unfold sig0Packed sigma0D
  rw [zmmPackD_lane, zmmPackD_lane, zmmRorD_lane, zmmRorD_lane, zmmRorD_lane,
    rorD_eq_rotateRight _ _ (by norm_num), rorD_eq_rotateRight _ _ (by norm_num),
    rorD_eq_rotateRight _ _ (by norm_num)]
  rfl

/-- Lane `k` of the packed `Ch(e,f,g)` block equals the dword-lane `chD`. -/
theorem chPacked_lane (we wf wg : BitVec 512) (k : Fin 16) :
    zmmLane32 (chPacked we wf wg) k
      = chD (zmmLane32 we k) (zmmLane32 wf k) (zmmLane32 wg k) := by
  unfold chPacked chD
  rw [zmmPackD_lane, zmmPackD_lane, zmmPackD_lane]
  rfl

/-- Lane `k` of the packed `Maj(a,b,c)` block equals the dword-lane `majD`. -/
theorem majPacked_lane (wa wb wc : BitVec 512) (k : Fin 16) :
    zmmLane32 (majPacked wa wb wc) k
      = majD (zmmLane32 wa k) (zmmLane32 wb k) (zmmLane32 wc k) := by
  unfold majPacked majD
  rw [zmmPackD_lane, zmmPackD_lane, zmmPackD_lane, zmmPackD_lane, zmmPackD_lane]
  rfl

/-! ## 2. Lane projection of the packed `T₁`/`a'`/`e'` -/

/-- Lane `k` of the packed `T₁` is the dword-lane `T₁` of the lane-`k` words. -/
theorem t1Packed_lane (we wf wg wh kt wt : BitVec 512) (k : Fin 16) :
    zmmLane32 (t1Packed we wf wg wh kt wt) k
      = (((((zmmLane32 wh k) + sigma1D (zmmLane32 we k))
            + chD (zmmLane32 we k) (zmmLane32 wf k) (zmmLane32 wg k))
            + zmmLane32 kt k) + zmmLane32 wt k) := by
  unfold t1Packed
  rw [zmmPackD_lane, zmmPackD_lane, zmmPackD_lane, zmmPackD_lane,
    sig1Packed_lane, chPacked_lane]
  rfl

/-! ## 3. The bit-exact tie of each packed lane to the abstract `UInt32` round

With the eight working words `a … h`, the round constant `Kₜ`, and schedule word
`Wₜ` held as `UInt32`-bit-vectors in lane `k`, lane `k` of `aPrimePacked` /
`ePrimePacked` is **exactly** the bit-vector of the abstract `UInt32` round word
`aPrimeWord` / `ePrimeWord` — the same target the bespoke realization's
`dwordRound_aPrime_eq_SHA` / `_ePrime_eq_SHA` tie to, hence equal strength. The
`vpaddd` lane add is `+` at `BitVec 32`, which is the `UInt32` mod-2³² add
(`UInt32.toBitVec_add`); `Ch`/`Maj`/`Σ₀`/`Σ₁` are bit-exact by the
`Sha256DwordLane` ties. No `inputs < 2³²` caveat: the lane is 32 bits wide. -/

/-- The packed `T₁` lane is the bit-vector of the abstract `UInt32` `t1Word`. -/
theorem t1Packed_lane_eq_SHA (we wf wg wh kt wt : BitVec 512) (k : Fin 16)
    (e f g h ktw wtw : UInt32)
    (he : zmmLane32 we k = e.toBitVec) (hf : zmmLane32 wf k = f.toBitVec)
    (hg : zmmLane32 wg k = g.toBitVec) (hh : zmmLane32 wh k = h.toBitVec)
    (hkt : zmmLane32 kt k = ktw.toBitVec) (hwt : zmmLane32 wt k = wtw.toBitVec) :
    zmmLane32 (t1Packed we wf wg wh kt wt) k = (t1Word e f g h ktw wtw).toBitVec := by
  rw [t1Packed_lane, he, hf, hg, hh, hkt, hwt,
    bigSigma1_dword_bitExact, ch_dword_bitExact]
  simp only [t1Word, UInt32.toBitVec_add]

/-- **Packed `a'` lane tie.** Lane `k` of the unified-packed `aPrimePacked` equals
    the bit-vector of the abstract `UInt32` SHA-256 round word `aPrimeWord` — the
    same abstract target as the bespoke `dwordRound_aPrime_eq_SHA`, bit-exact at
    width 32, for every lane. Composed with the bespoke `aPrimeWord_anchor`, this
    is the genuine FIPS-180-4 `compressRound … 0`. -/
theorem aPrimePacked_lane (wa wb wc we wf wg wh kt wt : BitVec 512) (k : Fin 16)
    (a b c e f g h ktw wtw : UInt32)
    (ha : zmmLane32 wa k = a.toBitVec) (hb : zmmLane32 wb k = b.toBitVec)
    (hc : zmmLane32 wc k = c.toBitVec) (he : zmmLane32 we k = e.toBitVec)
    (hf : zmmLane32 wf k = f.toBitVec) (hg : zmmLane32 wg k = g.toBitVec)
    (hh : zmmLane32 wh k = h.toBitVec) (hkt : zmmLane32 kt k = ktw.toBitVec)
    (hwt : zmmLane32 wt k = wtw.toBitVec) :
    zmmLane32 (aPrimePacked wa wb wc we wf wg wh kt wt) k
      = (aPrimeWord a b c e f g h ktw wtw).toBitVec := by
  unfold aPrimePacked
  rw [zmmPackD_lane, t1Packed_lane_eq_SHA we wf wg wh kt wt k e f g h ktw wtw
        he hf hg hh hkt hwt, zmmPackD_lane, sig0Packed_lane, majPacked_lane,
      ha, hb, hc, bigSigma0_dword_bitExact, maj_dword_bitExact]
  simp only [aPrimeWord, JasminBinOp.apply, UInt32.toBitVec_add]

/-- **Packed `e'` lane tie.** Lane `k` of the unified-packed `ePrimePacked` equals
    the bit-vector of the abstract `UInt32` SHA-256 round word `ePrimeWord` — the
    same abstract target as the bespoke `dwordRound_ePrime_eq_SHA`. Composed with
    the bespoke `ePrimeWord_anchor`, this is `compressRound … 4`. -/
theorem ePrimePacked_lane (wd we wf wg wh kt wt : BitVec 512) (k : Fin 16)
    (d e f g h ktw wtw : UInt32)
    (hd : zmmLane32 wd k = d.toBitVec) (he : zmmLane32 we k = e.toBitVec)
    (hf : zmmLane32 wf k = f.toBitVec) (hg : zmmLane32 wg k = g.toBitVec)
    (hh : zmmLane32 wh k = h.toBitVec) (hkt : zmmLane32 kt k = ktw.toBitVec)
    (hwt : zmmLane32 wt k = wtw.toBitVec) :
    zmmLane32 (ePrimePacked wd we wf wg wh kt wt) k
      = (ePrimeWord d e f g h ktw wtw).toBitVec := by
  unfold ePrimePacked
  rw [zmmPackD_lane, t1Packed_lane_eq_SHA we wf wg wh kt wt k e f g h ktw wtw
        he hf hg hh hkt hwt, hd]
  simp only [ePrimeWord, JasminBinOp.apply, UInt32.toBitVec_add]

/-! ## 4. The packaged abstract tie (equal-strength successor)

The conjunction of the two lane ties — the model-free, equal-strength successor
of the bespoke `dwordRound_aPrime_eq_SHA` / `dwordRound_ePrime_eq_SHA`. Every lane
of the unified-packed dword round output is the abstract FIPS-180-4 SHA-256 round
word (`aPrimeWord` → `compressRound … 0`, `ePrimeWord` → `compressRound … 4`),
bit-exact at width 32. -/

/-- **The unified-packed SHA-256 dword round is the abstract FIPS-180-4 round.**
    On a lane-`k` valuation holding `a … h`, `Kₜ`, `Wₜ` as `UInt32`-bit-vectors,
    lane `k` of `aPrimePacked` / `ePrimePacked` equals the bit-vector of the
    abstract `UInt32` round words `aPrimeWord` / `ePrimeWord`. Model-free,
    equal-strength successor of the bespoke `dwordRound_aPrime_eq_SHA` /
    `dwordRound_ePrime_eq_SHA`. -/
theorem sha256DwordRoundCom_eq_SHA
    (wa wb wc wd we wf wg wh kt wt : BitVec 512) (k : Fin 16)
    (a b c d e f g h ktw wtw : UInt32)
    (ha : zmmLane32 wa k = a.toBitVec) (hb : zmmLane32 wb k = b.toBitVec)
    (hc : zmmLane32 wc k = c.toBitVec) (hd : zmmLane32 wd k = d.toBitVec)
    (he : zmmLane32 we k = e.toBitVec) (hf : zmmLane32 wf k = f.toBitVec)
    (hg : zmmLane32 wg k = g.toBitVec) (hh : zmmLane32 wh k = h.toBitVec)
    (hkt : zmmLane32 kt k = ktw.toBitVec) (hwt : zmmLane32 wt k = wtw.toBitVec) :
    zmmLane32 (aPrimePacked wa wb wc we wf wg wh kt wt) k
        = (aPrimeWord a b c e f g h ktw wtw).toBitVec
      ∧ zmmLane32 (ePrimePacked wd we wf wg wh kt wt) k
        = (ePrimeWord d e f g h ktw wtw).toBitVec :=
  ⟨aPrimePacked_lane wa wb wc we wf wg wh kt wt k a b c e f g h ktw wtw
      ha hb hc he hf hg hh hkt hwt,
   ePrimePacked_lane wd we wf wg wh kt wt k d e f g h ktw wtw
      hd he hf hg hh hkt hwt⟩

end CatCrypt.Crypto.SecureCompilation.VIR.OwnedSha256DwordRoundAbstractCom
