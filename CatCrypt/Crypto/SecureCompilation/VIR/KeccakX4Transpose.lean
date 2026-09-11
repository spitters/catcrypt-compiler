/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit

/-!
# SoA ↔ AoS transpose for the 4-way Keccak-f1600 batch (#587)

The verified scalar Keccak permutation (`KeccakEmit.keccakF1600Com`, KAT'd
byte-identical to FIPS 202) operates on a single 25-lane state. The 4-way
batched kernel `keccak_f1600_x4` (`bench/keccak_compare`, AVX2 YMM) keeps
**four** independent states interleaved in a `u64[100]` *structure-of-arrays*
(SoA) layout

```
soa[lane*4 + i] = state_i[lane]      (lane ∈ {0..24}, i ∈ {0..3})
```

so that lane `lane` of all four states sits contiguously in one `__m256i` and a
single packed instruction advances all four at once. This file gives the pure
index-arithmetic transpose between the four scalar 25-lane states and that SoA
layout, plus the round-trip identity that lets the batched emit
(`KeccakX4Emit.lean`) reason about the SoA buffer as four independent scalar
states.

Everything here is `Fin`-indexed bookkeeping over `BitVec 64` lane words; there
is no cryptographic content and no dialect `Com` — the round-trip is a pure
`funext` + index `omega`/`decide`. -/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakX4Transpose

set_option autoImplicit false

/-- One Keccak state as 25 lane words (an array-of-structs lane view). The bit
    layout matches `Fin 25 → BitVec 64`; `KeccakEmit` packs these into a single
    `BitVec 1600` register, but for the transpose only the lane indexing
    matters. -/
abbrev Lanes : Type := Fin 25 → BitVec 64

/-- The four scalar states, as a function of the batch index `i ∈ {0..3}`. -/
abbrev X4 : Type := Fin 4 → Lanes

/-- The interleaved structure-of-arrays buffer: 100 = 25 lanes × 4 states. -/
abbrev Soa : Type := Fin 100 → BitVec 64

/-- The flattened SoA index `lane*4 + i` for `lane ∈ {0..24}`, `i ∈ {0..3}`. -/
def soaIdx (lane : Fin 25) (i : Fin 4) : Fin 100 :=
  ⟨lane.val * 4 + i.val, by
    have hl : lane.val ≤ 24 := by omega
    have hi : i.val ≤ 3 := by omega
    omega⟩

/-- Pack four scalar states into the interleaved SoA buffer:
    `soa[lane*4 + i] = state_i[lane]`. The recovery of `(lane, i)` from a flat
    index `j` is `lane = j / 4`, `i = j % 4`. -/
def scalar_to_x4_soa (s : X4) : Soa :=
  fun j => s ⟨j.val % 4, by omega⟩ ⟨j.val / 4, by omega⟩

/-- Recover the four scalar states from the interleaved SoA buffer:
    `state_i[lane] = soa[lane*4 + i]`. -/
def x4_soa_to_scalar (soa : Soa) : X4 :=
  fun i lane => soa (soaIdx lane i)

/-- **Round-trip identity (SoA ∘ scalar = id).** Unpacking the SoA buffer that
    was packed from four scalar states recovers exactly those four states. Pure
    index arithmetic: `(lane*4 + i) % 4 = i` and `(lane*4 + i) / 4 = lane` for
    `i < 4`. -/
theorem x4_soa_to_scalar_scalar_to_x4_soa (s : X4) :
    x4_soa_to_scalar (scalar_to_x4_soa s) = s := by
  funext i lane
  unfold x4_soa_to_scalar scalar_to_x4_soa soaIdx
  have hi : i.val < 4 := i.isLt
  have hmod : (lane.val * 4 + i.val) % 4 = i.val := by omega
  have hdiv : (lane.val * 4 + i.val) / 4 = lane.val := by omega
  -- Reduce the two `Fin` reindexings to identities, then `Fin.ext`.
  congr 1 <;> apply Fin.ext <;> simp only [] <;> omega

/-- **Round-trip identity (scalar ∘ SoA = id).** Re-packing the four states
    unpacked from an SoA buffer recovers the original buffer. Pure index
    arithmetic: every flat index `j < 100` factors uniquely as `(j/4)*4 + j%4`. -/
theorem scalar_to_x4_soa_x4_soa_to_scalar (soa : Soa) :
    scalar_to_x4_soa (x4_soa_to_scalar soa) = soa := by
  funext j
  unfold scalar_to_x4_soa x4_soa_to_scalar soaIdx
  apply congrArg
  apply Fin.ext
  have hj : j.val < 100 := j.isLt
  simp only
  omega

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakX4Transpose
