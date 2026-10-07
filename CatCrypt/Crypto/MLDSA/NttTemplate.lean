/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.MLDSA.Spec.Ntt
public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttInverse

/-!
# The ML-DSA NTT as an instance of the negacyclic NTT template

`VIR/NegacyclicNttTemplate.lean` lowers the merged-twiddle negacyclic NTT to a
`fieldDialect` program `nttProg P`, generic in the parameter record `P`, and
proves once that lane `i` of the program is `nttSpec` at `i`.  At
`P = mldsaNtt` (`q = 8380417`, 256 coefficients, eight layers, `ψ = 1753`) the
lanes are the FIPS 204 transform `Spec.Ntt.ntt` (Algorithm 41), and the scaled
inverse `inttSpec` with scaling `256⁻¹ = 8347681` is the FIPS 204 inverse
transform `Spec.Ntt.invNtt` (Algorithm 42).

## Main results

* `nttSpec_eq_ntt` — `nttSpec` at the ML-DSA parameters is `Spec.Ntt.ntt`.
* `nttProg_mldsa_eq_ntt` — lane `i` of `nttProg mldsaNtt` on the coefficients
  of `w` is `Spec.Ntt.ntt w i`.
* `inttSpec_eq_invNtt` — `inttSpec` at the ML-DSA parameters and scaling
  `8347681` is `Spec.Ntt.invNtt`.
* `inttProg_mldsa_eq_invNtt` — lane `i` of `inttProg mldsaNtt 8347681` on the
  lanes of `v` is `Spec.Ntt.invNtt v i`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.NttTemplate

open CatCrypt.Crypto.MLDSA.Spec.Ntt
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral (hvGetD)

/-- The coefficients of `w` as a lane function, zero past index `255`. -/
def lanes (w : Fin 256 → ZMod 8380417) (j : ℕ) : ZMod 8380417 :=
  if h : j < 256 then w ⟨j, h⟩ else 0

/-- At `ψ = 1753`, eight layers and 256 coefficients, `nttSpec` is the FIPS 204
transform. -/
theorem nttSpec_eq_ntt (w : Fin 256 → ZMod 8380417) (i : Fin 256) :
    nttSpec (1753 : ZMod 8380417) 8 8 (lanes w) i = ntt w i := by
  rw [ntt_eq_sum, nttSpec]
  simp only [Nat.sub_self, pow_zero, Nat.mod_one, Nat.div_one, mul_one, Nat.zero_add]
  rw [show (2 : ℕ) ^ 8 = 256 from by norm_num, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lanes, dif_pos j.isLt]
  rfl

/-- **The ML-DSA instance.** Lane `i` of the template program at `mldsaNtt` is
the FIPS 204 NTT. -/
theorem nttProg_mldsa_eq_ntt (w : Fin 256 → ZMod 8380417) (i : Fin 256) :
    hvGetD ((nttProg mldsaNtt).denote (fnVal 8380417 (lanes w) 256 0)) i = ntt w i := by
  rw [mldsaNtt_denote (lanes w) i i.isLt, nttSpec_eq_ntt]

/-- At `ψ = 1753`, eight layers, 256 coefficients and scaling `256⁻¹ = 8347681`,
`inttSpec` is the FIPS 204 inverse transform. -/
theorem inttSpec_eq_invNtt (v : Fin 256 → ZMod 8380417) (i : Fin 256) :
    inttSpec (1753 : ZMod 8380417) 8 8 (8347681 : ZMod 8380417) (lanes v) i = invNtt v i := by
  set u : Fin 256 → ZMod 8380417 :=
    fun j => inttSpec (1753 : ZMod 8380417) 8 8 (8347681 : ZMod 8380417) (lanes v) j with hu
  have hntt : ntt u = v := by
    funext k
    have hcongr : ∀ j, j < 2 ^ 8 →
        lanes u j = inttSpec (1753 : ZMod 8380417) 8 8 (8347681 : ZMod 8380417) (lanes v) j := by
      intro j hj
      rw [lanes, dif_pos (show j < 256 from hj)]
    rw [← nttSpec_eq_ntt, nttSpec_congr _ 8 8 le_rfl _ _ hcongr,
      nttSpec_inttSpec (1753 : ZMod 8380417) 8 8 (mldsaNtt.psi_pow mldsaNtt_ok) (by norm_num)
        le_rfl (8347681 : ZMod 8380417) (ScaleOk.cast mldsaNtt 8347681 mldsa_scaleOk) _ k k.isLt,
      lanes, dif_pos k.isLt]
  show u i = invNtt v i
  rw [← hntt, invNtt_ntt]

/-- **The ML-DSA inverse instance.** Lane `i` of the template inverse program at
`mldsaNtt` with scaling `8347681` is the FIPS 204 inverse NTT. -/
theorem inttProg_mldsa_eq_invNtt (v : Fin 256 → ZMod 8380417) (i : Fin 256) :
    hvGetD ((inttProg mldsaNtt 8347681).denote (fnVal 8380417 (lanes v) 256 0)) i
      = invNtt v i :=
  (inttProg_denote mldsaNtt mldsaNtt_ok 8347681 (lanes v) i i.isLt).trans
    (inttSpec_eq_invNtt v i)

end CatCrypt.Crypto.MLDSA.NttTemplate
