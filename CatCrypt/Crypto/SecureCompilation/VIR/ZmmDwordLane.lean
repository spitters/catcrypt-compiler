/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.BitVec

/-!
# ZMM dword (16×u32) lane round-trip for the verified Jasmin VIR dialect

The dword analogue of the 8×u64 `zmmOfLanes_zmmLane` round-trip proved in
[`Poseidon2Avx512Jasmin.lean`](Poseidon2Avx512Jasmin.lean).  The verified Jasmin
VIR dialect ([`JasminDialect.lean`](JasminDialect.lean)) carries the 16×u32 ZMM
lane view (`zmmLane32`, the `extractLsb'` reader), its inverse assembler
(`zmmOfLanes32`), and the two packed dword ops `zmmPackD` (`#VPADDD`/`#VPSUBD`/
`#VPXORD`/…) and `zmmRorD` (`#VPRORD`).  This module proves they are coherent:

* `zmmOfLanes32_zmmLane32` — reading lane `k` of an assembled 16-lane ZMM
  recovers the `k`-th lane function value.  This is the dword image of the
  qword round-trip; the only change is 16 lanes (32-bit slices) versus 8.
* `zmmRorD_lane` / `zmmPackD_lane` — the two op denotations are per-lane: lane
  `k` of the result is the op applied to lane `k` of the input(s).  Both fall
  out of the round-trip by unfolding the op and rewriting with it.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane`
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The 16×u32 ZMM lane round-trip -/

/-- Reading lane `k` (a 32-bit dword) of an assembled 16-lane ZMM register
    recovers the `k`-th lane function value: `zmmLane32 (zmmOfLanes32 f) k = f k`.
    The little-endian concatenation places `f k` at bits `[32k, 32k+32)`, exactly
    what `zmmLane32` extracts.  Dword analogue of `zmmOfLanes_zmmLane` (8×u64). -/
theorem zmmOfLanes32_zmmLane32 (f : Fin 16 → BitVec 32) (k : Fin 16) :
    zmmLane32 (zmmOfLanes32 f) k = f k := by
  -- For each lane `k`, peel the 16-fold little-endian `++` at the `extractLsb'`
  -- level: `extractLsb'_append_eq_of_le` drops the `k` high lanes above the
  -- window, then `extractLsb'_append_eq_right` reads off `f k`.  (The 16-deep
  -- `getLsbD`/`split_ifs` route the 8-lane qword proof uses blows up here.)
  fin_cases k <;>
    (unfold zmmLane32 zmmOfLanes32
     norm_num [Fin.val_ofNat, BitVec.extractLsb'_append_eq_of_le,
       BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_right,
       BitVec.extractLsb'_append_eq_left]) <;>
    rfl

/-! ## 2. The op denotations are per-lane -/

/-- Lane `k` of `zmmRorD n a` is `(zmmLane32 a k).rotateRight n`: the `#VPRORD`
    op rotates each 32-bit lane independently. -/
theorem zmmRorD_lane (n : Nat) (a : BitVec 512) (k : Fin 16) :
    zmmLane32 (zmmRorD n a) k = (zmmLane32 a k).rotateRight n := by
  unfold zmmRorD
  rw [zmmOfLanes32_zmmLane32]

/-- Lane `k` of `zmmPackD bop a b` is `bop.apply (zmmLane32 a k) (zmmLane32 b k)`:
    each packed dword op (`#VPADDD`/`#VPSUBD`/`#VPXORD`/`#VPANDD`/`#VPORD`) acts on
    lane `k` of the two inputs independently. -/
theorem zmmPackD_lane (bop : JasminBinOp) (a b : BitVec 512) (k : Fin 16) :
    zmmLane32 (zmmPackD bop a b) k = bop.apply (zmmLane32 a k) (zmmLane32 b k) := by
  unfold zmmPackD
  rw [zmmOfLanes32_zmmLane32]

end CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
