/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# The shipped Montgomery curve multiply, read as a `ZMod p` field relation

The Tier-A curve kernels (`Curve4LimbTierA`) prove that the emitted P256 Montgomery
multiply's `runBlock` output satisfies the Montgomery congruence `out · 2^256 ≡ x·y
[MOD p]`. Through `MultiLimbEmitBridge.montForm_zmod`, that congruence is exactly the
`ZMod p` field identity `out · 2^256 = x·y` — the defining property of the Montgomery
product. This ties the production-path emitted P256 `.s` (the one that ships and is
KAT-gated against GMP/s2n) to the abstract prime field `ZMod (valLimbs p256Limbs)`.
-/

namespace CatCrypt.Crypto.SecureCompilation.MontMulFieldTie

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

set_option maxRecDepth 4000

/-- The P256 base-field prime is nonzero (it is `2^256 − 2^224 + 2^192 + 2^96 − 1`). -/
instance : NeZero (valLimbs p256Limbs) := ⟨by rw [p256Limbs_value]; norm_num⟩

/-- **The emitted P256 Montgomery multiply computes the Montgomery product in the
    field.** The shipped `runBlock`-of-emitted kernel's output `out`, cast into
    `ZMod (valLimbs p256Limbs)`, satisfies `out · 2^256 = x · y` — i.e. `out` is
    `x·y·(2^256)⁻¹`, the Montgomery product of the two field elements. -/
theorem p256_montmul_zmod
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64) (Nprime256 : Nat)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs x < valLimbs p256Limbs)
    (hy_red : valLimbs yv < valLimbs p256Limbs)
    (hNprime : (valLimbs p256Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    (↑(Number.montgomeryReduce (valLimbs p256Limbs) (2 ^ 256) Nprime256
          (runBlockProductValue accs as ys hi lo s)) : ZMod (valLimbs p256Limbs))
        * ((2 ^ 256 : ℕ) : ZMod (valLimbs p256Limbs))
      = (↑(valLimbs x) : ZMod (valLimbs p256Limbs)) * (↑(valLimbs yv)) := by
  have hcong := (p256_emit_montmul_runBlock accs as ys x yv hi lo s Nprime256
    haslen hyslen hcap hfresh hx hy hacc0 hcf hof hx_red hy_red hNprime).2.2
  exact montForm_zmod _ _ _ _ _ hcong

end CatCrypt.Crypto.SecureCompilation.MontMulFieldTie
