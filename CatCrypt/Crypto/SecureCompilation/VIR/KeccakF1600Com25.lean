/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComSpecialize
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakLaneMapYmm

/-!
# Keccak-p[1600,24] over its 25 state lanes

`KeccakEmit.keccakF1600Com` takes `nInputs` input words: the 25 state lanes, 32 slot
seeds that are written before they are read, and the literal table `immList` (the NOT
mask, the round constants and the rotate counts). `keccakF1600Com25` is its input
specialisation (`ComSpecialize.specialize`) to the 25 state lanes: the seeds are the
constant `0` and each literal input is a `regConst` binding of its literal, so a lane map
broadcasts the constants instead of holding each one in a register.

## Main results

* `keccakF1600Com25_denote_spec`: on the state valuation of `a`, `keccakF1600Com25` is
  lane 24 of the FIPS 202 permutation of `a`.
* `keccakF1600Com25_denote_fips`: the same on every valuation of the 25 state inputs.
* `covered_keccakF1600Com25`: every lane shape of 64-bit lanes covering every
  `JasminBinOp` covers `keccakF1600Com25`; instances `qwordYmmV` and `qwordZmm`.
* `laneMapYmmV_keccakF1600Com25_fips`, `laneMapZmm_keccakF1600Com25_fips`: four (YMM)
  and eight (ZMM) FIPS 202 permutations per vector register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600Com25

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.ComSpecialize
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakFipsAscent
  (keccakVal fipsRounds keccakF1600Com_denote_spec mkVal)

/-! ## 1. The specialised program -/

/-- The constant carried by input `25 + j` of `keccakF1600Com`: `0` for a slot seed,
    the literal `immList[25 + j - firstImm]` for a literal input. -/
def keccakConst (j : Nat) : Nat :=
  if 25 + j < numSlots then 0 else immList.getD (25 + j - firstImm) 0

/-- The input assignment of `keccakF1600Com`: the 25 state lanes stay inputs, the 32
    slot seeds are `0`, and the literal inputs carry `immList`. -/
def keccakSpec : Spec inCtxt (List.replicate 25 r64) :=
  Spec.keepN (d := jasminDialect) r64 (fixRegs 64 keccakConst (nInputs - 25)) 25

/-- The Keccak-p[1600,24] permutation program over its 25 state lanes. -/
def keccakF1600Com25 : Com jasminDialect (List.replicate 25 r64) r64 :=
  specialize keccakSpec keccakF1600Com

/-- The valuation of the 25 state inputs carrying the state `a`. -/
def stateVal (a : KeccakDiffuseExact.Lanes) :
    Ctxt.Valuation (d := jasminDialect) (List.replicate 25 r64) :=
  mkVal (fun i => if h : i < 25 then a ⟨i, h⟩ else 0) 25

/-- The valuation of all inputs extending the state valuation of `a` with the
    constants of `keccakSpec` is the canonical input valuation `keccakVal a`. -/
theorem keccakSpec_extend_stateVal (a : KeccakDiffuseExact.Lanes) :
    keccakSpec.extend (stateVal a) = keccakVal a :=
  rfl

/-- The state lanes read from a valuation of the 25 state inputs. -/
def stateLanes (V : Ctxt.Valuation (d := jasminDialect) (List.replicate 25 r64)) :
    KeccakDiffuseExact.Lanes :=
  fun i => (KeccakEmit.inputVar 24 i.val).lookup V

theorem mkVal_congr (g g' : Nat → BitVec 64) :
    (n : Nat) → (∀ i < n, g i = g' i) → mkVal g n = mkVal g' n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [mkVal]
      rw [h 0 (by omega), mkVal_congr (fun j => g (j + 1)) (fun j => g' (j + 1)) n
        (fun i hi => h (i + 1) (by omega))]

theorem mkVal_lookup_inputVar :
    (m : Nat) → (V : Ctxt.Valuation (d := jasminDialect) (List.replicate (m + 1) r64)) →
    mkVal (fun i => (KeccakEmit.inputVar m i).lookup V) (m + 1) = V
  | 0, .cons x .nil => rfl
  | m + 1, .cons x V => by
      simp only [mkVal]
      congr 1
      exact mkVal_lookup_inputVar m V

theorem stateVal_stateLanes (V : Ctxt.Valuation (d := jasminDialect) (List.replicate 25 r64)) :
    stateVal (stateLanes V) = V := by
  rw [stateVal, mkVal_congr _ (fun i => (KeccakEmit.inputVar 24 i).lookup V) 25
    (fun i hi => by simp only [stateLanes, dite_eq_left hi])]
  exact mkVal_lookup_inputVar 24 V

/-! ## 2. The FIPS 202 statement -/

/-- **Denotation of the specialised permutation.** On a valuation of the 25 state
    inputs it is `keccakF1600Com` on the input valuation that extends it with the
    constants. -/
theorem keccakF1600Com25_denote
    (V : Ctxt.Valuation (d := jasminDialect) (List.replicate 25 r64)) :
    keccakF1600Com25.denote V = keccakF1600Com.denote (keccakSpec.extend V) :=
  specialize_denote keccakSpec keccakF1600Com V

/-- **The specialised permutation computes FIPS 202.** On the state valuation of `a`,
    `keccakF1600Com25` is lane 24 of the 24-fold FIPS 202 round iteration of `a`. -/
theorem keccakF1600Com25_denote_spec (a : KeccakDiffuseExact.Lanes) :
    keccakF1600Com25.denote (stateVal a) = fipsRounds 24 0 a ⟨24, by decide⟩ := by
  rw [keccakF1600Com25_denote, keccakSpec_extend_stateVal]
  exact keccakF1600Com_denote_spec a

/-- The FIPS 202 statement on every valuation of the 25 state inputs. -/
theorem keccakF1600Com25_denote_fips
    (V : Ctxt.Valuation (d := jasminDialect) (List.replicate 25 r64)) :
    keccakF1600Com25.denote V = fipsRounds 24 0 (stateLanes V) ⟨24, by decide⟩ := by
  conv_lhs => rw [← stateVal_stateLanes V]
  exact keccakF1600Com25_denote_spec (stateLanes V)

/-! ## 3. Coverage by lane shapes of 64-bit lanes -/

open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

section Coverage

variable (S : LaneShape)

/-- Renaming preserves coverage: `CoveredExpr` reads only the operation. -/
theorem covered_rename : {Γ Γ' : Ctxt jasminDialect} → {t : JasminTy} →
    (h : Ctxt.Hom Γ Γ') → (c : Com jasminDialect Γ t) → S.Covered c →
    S.Covered (Com.rename h c)
  | _, _, _, _, .ret _, _ => trivial
  | _, _, _, h, .var _ body, hc => ⟨hc.1, covered_rename h.lift body hc.2⟩

theorem covered_bindConsts {Δ : Ctxt jasminDialect} {t : JasminTy} :
    (l : Ctxt jasminDialect) → (cs : HVector (ConstOp jasminDialect) l) →
    (c : Com jasminDialect (l ++ Δ) t) →
    ConstOp.All (fun k => ∀ {Γ : Ctxt jasminDialect}, S.CoveredExpr (k.expr (Γ := Γ))) cs →
    S.Covered c → S.Covered (bindConsts l cs c)
  | [], .nil, _, _, hc => hc
  | _ :: l, .cons _ ks, _, hks, hc => covered_bindConsts l ks _ hks.2 ⟨hks.1, hc⟩

/-- A lane shape covers a specialised program when it covers the program and every
    constant of the assignment. -/
theorem covered_specialize {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (s : Spec Γ Δ)
    (c : Com jasminDialect Γ t)
    (hs : s.AllOps (fun k => ∀ {Γ : Ctxt jasminDialect}, S.CoveredExpr (k.expr (Γ := Γ))))
    (hc : S.Covered c) : S.Covered (specialize s c) :=
  covered_bindConsts S _ _ _ (Spec.allOps_ops _ s hs) (covered_rename S _ c hc)

/-- **Coverage of the specialised permutation.** A lane shape of 64-bit lanes covering
    every `JasminBinOp` other than the register-count shifts, and lowering the
    immediate-count shifts at every count below 64, covers `keccakF1600Com25`. -/
theorem covered_keccakF1600Com25 (h64 : S.laneBits = 64)
    (hcov : ∀ bop, bop ≠ .shl → bop ≠ .shr → S.covers bop = true)
    (himm : ∀ n, n < 64 → (S.immBlock .shl).isSome = true ∧ S.immCovers .shl n = true ∧
      (S.immBlock .shr).isSome = true ∧ S.immCovers .shr n = true) :
    S.Covered keccakF1600Com25 :=
  covered_specialize S keccakSpec keccakF1600Com
    (Spec.allOps_keepN _ r64 _ (allOps_fixRegs _ 64 (fun _ {_} => h64.symm) _ _) 25)
    (KeccakLaneMapYmm.covered_keccakF1600Com S h64 hcov himm)

end Coverage

/-- `qwordYmmV` covers `keccakF1600Com25`. -/
theorem covered_qwordYmmV_keccakF1600Com25 : qwordYmmV.Covered keccakF1600Com25 :=
  covered_keccakF1600Com25 qwordYmmV rfl (fun bop hl hr => by cases bop <;> simp_all <;> rfl)
    (fun n hn => ⟨rfl, decide_eq_true hn, rfl, decide_eq_true hn⟩)

/-- `qwordZmm` covers `keccakF1600Com25`: its immediate block (`zmmQImmBlock`) lowers
    the rotates' immediate-count shifts. -/
theorem covered_qwordZmm_keccakF1600Com25 : qwordZmm.Covered keccakF1600Com25 :=
  covered_keccakF1600Com25 qwordZmm rfl (fun bop hl hr => by cases bop <;> simp_all <;> rfl)
    (fun n hn => ⟨rfl, decide_eq_true hn, rfl, decide_eq_true hn⟩)

/-! ## 4. Several permutations per vector register -/

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect (yQwordW) in
/-- **Four FIPS 202 permutations per YMM register.** When lane `k` of the inputs is the
    state valuation of `a k`, qword lane `k` of the 256-bit lane map of
    `keccakF1600Com25` is lane 24 of the FIPS 202 permutation of `a k`. -/
theorem laneMapYmmV_keccakF1600Com25_fips
    (W : Ctxt.Valuation (qwordYmmV.widenCtxt (List.replicate 25 r64)))
    (a : Fin 4 → KeccakDiffuseExact.Lanes)
    (hW : ∀ k : Fin 4, qwordYmmV.laneOf k _ W = stateVal (a k)) (k : Fin 4) :
    yQwordW ((laneMapVec qwordYmmV keccakF1600Com25).denote W) k.val
      = fipsRounds 24 0 (a k) ⟨24, by decide⟩ := by
  rw [laneMapYmmV_denote_default keccakF1600Com25 covered_qwordYmmV_keccakF1600Com25 W k,
    hW k]
  exact keccakF1600Com25_denote_spec (a k)

/-- **Eight FIPS 202 permutations per ZMM register.** When lane `k` of the inputs is
    the state valuation of `a k`, lane `k` of the 512-bit lane map of
    `keccakF1600Com25` is lane 24 of the FIPS 202 permutation of `a k`. -/
theorem laneMapZmm_keccakF1600Com25_fips
    (W : Ctxt.Valuation (qwordZmm.widenCtxt (List.replicate 25 r64)))
    (a : Fin 8 → KeccakDiffuseExact.Lanes)
    (hW : ∀ k : Fin 8, qwordZmm.laneOf k _ W = stateVal (a k)) (k : Fin 8) :
    qwordZmm.laneOfTy k r64 ((laneMapVec qwordZmm keccakF1600Com25).denote W)
      = fipsRounds 24 0 (a k) ⟨24, by decide⟩ := by
  rw [laneMapVec_denote_default qwordZmm rfl keccakF1600Com25
    covered_qwordZmm_keccakF1600Com25 W k, hW k]
  exact keccakF1600Com25_denote_spec (a k)

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600Com25
