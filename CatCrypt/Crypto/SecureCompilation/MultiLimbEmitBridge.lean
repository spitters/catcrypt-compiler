/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-!
# Bridging the emitted curve kernels and the multi-limb proof stack

The emitted Montgomery curve kernels (`SchoolbookProductRunBlock`, `MontReduceRunBlock`,
`Curve4LimbTierA`) state their `runBlock`-value correctness against
`Cios4LimbProven.valLimbs : List (BitVec 64) → Nat`. The new multi-limb field stack
(`MultiLimbKernel`) states its correctness against `MultiLimbKernel.bignumVal`. These
two limb-readouts are the *same* little-endian fold — so the two worlds compose, and a
result proven in one is a result in the other.

* `valLimbs_eq_bignumVal` — the readout identity.
* `montForm_zmod` — the emitted kernels' Montgomery congruence
  `out · R ≡ x · y [MOD p]` read as a `ZMod p` field relation `out · R = x · y` (the
  defining property of the Montgomery product), the tie from emitted bytes to the
  abstract field.
-/

namespace CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-- **Readout identity.** The emit kernels' `valLimbs` and the multi-limb stack's
    `bignumVal` are the same little-endian limb fold. -/
theorem valLimbs_eq_bignumVal : ∀ l : List (BitVec 64), valLimbs l = bignumVal l
  | [] => rfl
  | w :: ws => by rw [valLimbs_cons, bignumVal, valLimbs_eq_bignumVal ws]

/-- **Montgomery form as a field relation.** The Montgomery congruence the emitted
    curve kernels prove — `out · R ≡ x · y [MOD p]` — is exactly the `ZMod p` identity
    `out · R = x · y`: the emitted output is the Montgomery product of `x` and `y`. -/
theorem montForm_zmod (p R out x y : Nat) [NeZero p]
    (h : out * R ≡ x * y [MOD p]) :
    ((out : ZMod p)) * (R : ZMod p) = (x : ZMod p) * (y : ZMod p) := by
  have hcast := (ZMod.natCast_eq_natCast_iff (out * R) (x * y) p).mpr h
  rwa [Nat.cast_mul, Nat.cast_mul] at hcast

/-- When `R` is a unit mod `p` (the Montgomery radix, coprime to the prime), the
    emitted output is pinned to the genuine field product `x · y · R⁻¹`. -/
theorem montForm_zmod_eq (p R out x y : Nat) [NeZero p]
    (hR : IsUnit (R : ZMod p)) (h : out * R ≡ x * y [MOD p]) :
    (out : ZMod p) = (x : ZMod p) * (y : ZMod p) * (↑(hR.unit⁻¹) : ZMod p) := by
  have hbase := montForm_zmod p R out x y h
  have hu : (R : ZMod p) = (hR.unit : ZMod p) := hR.unit_spec.symm
  rw [hu] at hbase
  rw [← hbase, mul_assoc, ← Units.val_mul]; simp

end CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge
