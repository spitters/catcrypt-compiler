/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.OwnedChacha20DwordCom
import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
import CatCrypt.Crypto.Jasmin.ChaCha20QR

/-!
# Abstract RFC-8439 §2.1 ChaCha20 quarter-round tie for the unified-`Com` dword kernel

`X86Backend/OwnedChacha20Realization.lean` carries the ChaCha20 quarter-round as a
straight-line owned `ZInstr` block (`qrBlockP`, over the bespoke `Avx512Model`
`runZBlock` machine) — but at the **64-bit** ZMM lane, as the `vpsllvq | vpsrlvq |
vporq` shift-decomposition `qrSpec`, with the module's Width statement making **no**
bit-exact 32-bit ChaCha claim. The realization web's `runZBlock`/`Avx512Model`
wrappers are MOOT once `Avx512Model` deletes; the abstract RFC-8439 §2.1
**quarter-round** — the add/xor/rotate over `u32` lanes — is the deliverable.

`OwnedChacha20DwordCom.lean` migrated the **bit-exact 16-way (`16 × u32`)**
quarter-round onto the unified `Com jasminDialect`, pinning each output register's
denotation (`qrCom{A,B,C,D}_denote`) to the packed dword spec `qrSpecZ`, written in
the verified-dialect dword waist functions `zmmPackD` (`VPADDD`/`VPXORD`) and
`zmmRorD` (`VPRORD`). But `qrSpecZ` stops at the **packed `BitVec 512`** level: it
does not tie each lane back to the abstract RFC-8439 §2.1 quarter-round
`quarterRound : BitVec 32 → … ` (`CatCrypt.Crypto.Jasmin.ChaCha20QR`, model-free
over a single `u32` word).

This module **re-anchors** the per-lane content onto the unified denotation: for
every one of the 16 dword lanes, lane `k` of the unified `qrCom{A,B,C,D}`
denotation equals the corresponding component of the model-free RFC-8439 §2.1
`quarterRound` applied to lane `k` of the four input registers — with **no
`Avx512Model`** in the import set.

## What is re-anchored (the abstract RFC-8439 §2.1 quarter-round tie)

The bridge is three layers, all over the verified `Com jasminDialect`:

* `qrCom{A,B,C,D}_denote` (imported from `OwnedChacha20DwordCom`) — each output
  register's `Com` denotation is the packed-`BitVec 512` spec `qrSpecZ`.
* `zmmPackD_lane` / `zmmRorD_lane` (imported from `ZmmDwordLane`) — the packed
  dword ops are per-lane: lane `k` of `zmmPackD bop a b` is
  `bop.apply (lane a k) (lane b k)`, and lane `k` of `zmmRorD n a` is
  `(lane a k).rotateRight n`.
* `rotateRight_eq_rotL32` (proved here) — for the ChaCha rotate amounts, the
  per-lane `BitVec 32` `rotateRight (32-k)` equals the abstract
  `ChaCha20QR.rotL32 _ k = (x <<< k) ||| (x >>> (32-k))`.

Composing these, `qrSpecZ_lane` characterizes lane `k` of `qrSpecZ` as
`quarterRound (lane a k) (lane b k) (lane c k) (lane d k)`, and
`qrCom{A,B,C,D}_lane_abstract` is **THE ABSTRACT TIE**: lane `k` of the unified
`Com jasminDialect` quarter-round denotation equals the genuine RFC-8439 §2.1
`quarterRound`, now over the verified dialect denotation with no `runZBlock` /
`ZInstr` / `Avx512Model` / `jasminc` / `jasminc_preserves_ct` in any theorem's
`#print axioms`.

## References
* RFC 8439 §2.1 — the ChaCha20 quarter-round
  `a += b; d ^= a; d <<<= 16; c += d; b ^= c; b <<<= 12; a += b; d ^= a;
   d <<<= 8; c += d; b ^= c; b <<<= 7`.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.OwnedChacha20AbstractCom`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.OwnedChacha20AbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.OwnedChacha20DwordCom
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
open CatCrypt.Crypto.Jasmin.ChaCha20QR

/-! ## 1. The per-lane rotate bridge: `rotateRight (32-k)` is the abstract `rotL32 _ k`

`zmmRorD n` rotates each `u32` lane RIGHT by `n`; the quarter-round's left-rotate
by `k` is emitted as `zmmRorD (32-k)`. The abstract RFC-8439 left-rotate is
`ChaCha20QR.rotL32 x k = (x <<< k) ||| (x >>> (32-k))`. For the four ChaCha rotate
amounts these coincide on each `BitVec 32` lane. -/

/-- `rotateRight 16` (the `<<<16` emission) on a `u32` lane is `rotL32 _ 16`. -/
theorem rotateRight16_eq_rotL32 (x : BitVec 32) :
    x.rotateRight 16 = rotL32 x 16 := by
  unfold rotL32
  simp [BitVec.rotateRight, BitVec.rotateRightAux, BitVec.or_comm]

/-- `rotateRight 20` (the `<<<12` emission, `32-12 = 20`) on a `u32` lane is
    `rotL32 _ 12`. -/
theorem rotateRight20_eq_rotL32 (x : BitVec 32) :
    x.rotateRight 20 = rotL32 x 12 := by
  unfold rotL32
  simp [BitVec.rotateRight, BitVec.rotateRightAux, BitVec.or_comm]

/-- `rotateRight 24` (the `<<<8` emission, `32-8 = 24`) on a `u32` lane is
    `rotL32 _ 8`. -/
theorem rotateRight24_eq_rotL32 (x : BitVec 32) :
    x.rotateRight 24 = rotL32 x 8 := by
  unfold rotL32
  simp [BitVec.rotateRight, BitVec.rotateRightAux, BitVec.or_comm]

/-- `rotateRight 25` (the `<<<7` emission, `32-7 = 25`) on a `u32` lane is
    `rotL32 _ 7`. -/
theorem rotateRight25_eq_rotL32 (x : BitVec 32) :
    x.rotateRight 25 = rotL32 x 7 := by
  unfold rotL32
  simp [BitVec.rotateRight, BitVec.rotateRightAux, BitVec.or_comm]

/-! ## 2. The per-lane characterization of the packed dword spec `qrSpecZ`

Pushing the lane reader `zmmLane32 · k` through `qrSpecZ` (`pAdd`/`pXor` = packed
`zmmPackD .add`/`.xor`, the rotates = `zmmRorD {16,20,24,25}`) by the per-lane
lemmas `zmmPackD_lane` / `zmmRorD_lane` and the rotate bridge above, lane `k` of
each `qrSpecZ` component is exactly the corresponding component of the abstract
RFC-8439 §2.1 `quarterRound` on lane `k`. -/

/-- **`qrSpecZ` lane characterization.** Lane `k` of the four components of the
    packed dword quarter-round spec `qrSpecZ a b c d` is the corresponding
    component of the abstract RFC-8439 §2.1 `quarterRound` on lane `k` of the four
    inputs `(zmmLane32 a k, …, zmmLane32 d k)`. -/
theorem qrSpecZ_lane (a b c d : BitVec 512) (k : Fin 16) :
    zmmLane32 (qrSpecZ a b c d).1 k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).1
      ∧ zmmLane32 (qrSpecZ a b c d).2.1 k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).2.1
      ∧ zmmLane32 (qrSpecZ a b c d).2.2.1 k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).2.2.1
      ∧ zmmLane32 (qrSpecZ a b c d).2.2.2 k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).2.2.2 := by
  unfold qrSpecZ quarterRound pAdd pXor
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [zmmRorD_lane, zmmPackD_lane, JasminBinOp.apply,
      rotateRight16_eq_rotL32, rotateRight20_eq_rotL32, rotateRight24_eq_rotL32,
      rotateRight25_eq_rotL32]

/-! ## 3. The abstract RFC-8439 §2.1 quarter-round tie on the unified denotation

Composing the imported `qrCom{A,B,C,D}_denote` (each `Com jasminDialect` output
denotes to the matching `qrSpecZ` component) with `qrSpecZ_lane`, lane `k` of the
unified quarter-round denotation equals the abstract `quarterRound` on lane `k`. -/

/-- **THE ABSTRACT TIE — `a'`.** Lane `k` of the unified `Com jasminDialect`
    quarter-round program `qrComA`'s denotation equals the `a'` component of the
    model-free RFC-8439 §2.1 `quarterRound` on lane `k` of the four input
    registers — over the verified dialect denotation, no `Avx512Model`. -/
theorem qrComA_lane_abstract (a b c d : BitVec 512) (k : Fin 16) :
    zmmLane32 (qrComA.denote (qrVal a b c d)) k
      = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
          (zmmLane32 c k) (zmmLane32 d k)).1 := by
  rw [qrComA_denote]; exact (qrSpecZ_lane a b c d k).1

/-- **THE ABSTRACT TIE — `b'`.** Lane `k` of `qrComB`'s unified denotation is the
    `b'` component of the RFC-8439 §2.1 `quarterRound` on lane `k`. -/
theorem qrComB_lane_abstract (a b c d : BitVec 512) (k : Fin 16) :
    zmmLane32 (qrComB.denote (qrVal a b c d)) k
      = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
          (zmmLane32 c k) (zmmLane32 d k)).2.1 := by
  rw [qrComB_denote]; exact (qrSpecZ_lane a b c d k).2.1

/-- **THE ABSTRACT TIE — `c'`.** Lane `k` of `qrComC`'s unified denotation is the
    `c'` component of the RFC-8439 §2.1 `quarterRound` on lane `k`. -/
theorem qrComC_lane_abstract (a b c d : BitVec 512) (k : Fin 16) :
    zmmLane32 (qrComC.denote (qrVal a b c d)) k
      = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
          (zmmLane32 c k) (zmmLane32 d k)).2.2.1 := by
  rw [qrComC_denote]; exact (qrSpecZ_lane a b c d k).2.2.1

/-- **THE ABSTRACT TIE — `d'`.** Lane `k` of `qrComD`'s unified denotation is the
    `d'` component of the RFC-8439 §2.1 `quarterRound` on lane `k`. -/
theorem qrComD_lane_abstract (a b c d : BitVec 512) (k : Fin 16) :
    zmmLane32 (qrComD.denote (qrVal a b c d)) k
      = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
          (zmmLane32 c k) (zmmLane32 d k)).2.2.2 := by
  rw [qrComD_denote]; exact (qrSpecZ_lane a b c d k).2.2.2

/-- **The full abstract quarter-round tie (the deliverable).** For every dword
    lane `k`, the four unified `Com jasminDialect` quarter-round programs
    `qrCom{A,B,C,D}`, denoted and read at lane `k`, are exactly the four components
    of the model-free RFC-8439 §2.1 `quarterRound` on lane `k` of the four input
    registers. The tie stands on the verified dialect denotation with no
    `Avx512Model` (`ZInstr`/`runZBlock`) machine in the import set. -/
theorem qrCom_lane_abstract (a b c d : BitVec 512) (k : Fin 16) :
    zmmLane32 (qrComA.denote (qrVal a b c d)) k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).1
      ∧ zmmLane32 (qrComB.denote (qrVal a b c d)) k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).2.1
      ∧ zmmLane32 (qrComC.denote (qrVal a b c d)) k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).2.2.1
      ∧ zmmLane32 (qrComD.denote (qrVal a b c d)) k
        = (quarterRound (zmmLane32 a k) (zmmLane32 b k)
            (zmmLane32 c k) (zmmLane32 d k)).2.2.2 :=
  ⟨qrComA_lane_abstract .., qrComB_lane_abstract ..,
   qrComC_lane_abstract .., qrComD_lane_abstract ..⟩

end CatCrypt.Crypto.SecureCompilation.VIR.OwnedChacha20AbstractCom
