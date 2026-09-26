/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakFipsAscent

/-!
# Four Keccak-p[1600,24] permutations in the lanes of YMM registers

`KeccakEmit.keccakF1600Com` is a chain of `regArith` bindings at width 64 over the ops
`xor`, `or`, `and`, `shl` and `shr`; its rotates are `shl` / `shr` by register counts
read from the input context. A lane shape of 64-bit lanes that covers every
`JasminBinOp` covers the whole program. At `LaneMapVec.qwordYmmV` the lane map runs
four independent permutations, one per qword lane of each YMM register, with the
rotates lowered to `vpsllvq` / `vpsrlvq`.

The coverage proof follows the emitter's own recursion, so its cost does not depend on
the size of the unrolled program.

## Main results

* `covered_keccakF1600Com`: every lane shape of 64-bit lanes covering every
  `JasminBinOp` covers `keccakF1600Com`.
* `laneMapYmmV_keccakF1600Com_denote`: qword lane `k` of the mapped program is the
  scalar program on the lane-`k` valuation.
* `laneMapYmmV_keccakF1600Com_fips`: when lane `k` of the inputs is the canonical
  input valuation of the state `a k`, qword lane `k` of the mapped program is lane 24
  of the FIPS 202 permutation of `a k`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakLaneMapYmm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

/-! ## 1. Coverage of the emitter chain -/

section Coverage

variable (S : LaneShape) (h64 : S.laneBits = 64) (hcov : ∀ bop, S.covers bop = true)

/-- A Keccak emitter continuation whose every instance is covered by `S`. -/
def ContCovered {t : JasminTy} (k : Cont t) : Prop :=
  ∀ {Γ' : Ctxt jasminDialect} (bs : BState Γ') (iv : Nat → Ctxt.Var Γ' r64), S.Covered (k bs iv)

include h64 hcov

/-- One `emitOp` binding before a covered continuation is covered. -/
theorem covered_emitOp {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (op : JasminBinOp) (dst : Fin numSlots) (a b : Src)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitOp bs iv op dst a b k) :=
  ⟨⟨h64.symm, hcov op⟩, hk _ _⟩

/-- A slot copy before a covered continuation is covered. -/
theorem covered_emitMov {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (dst src : Fin numSlots)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitMov bs iv dst src k) :=
  covered_emitOp S h64 hcov bs iv _ _ _ _ k hk

/-- A rotate before a covered continuation is covered. -/
theorem covered_emitRotL {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (dst : Fin numSlots) (n : Nat)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitRotL bs iv dst n k) := by
  unfold emitRotL
  split
  · exact hk bs iv
  · refine covered_emitOp S h64 hcov _ _ _ _ _ _ _ fun _ _ => ?_
    refine covered_emitOp S h64 hcov _ _ _ _ _ _ _ fun _ _ => ?_
    exact covered_emitOp S h64 hcov _ _ _ _ _ _ _ hk

omit h64 hcov in
/-- Closes a chain of `emitOp` / `emitMov` / `emitRotL` steps ending in the induction
    hypothesis `ih`. -/
macro "cov_chain" ih:term : tactic => `(tactic| repeat' (first
  | exact $ih _ _ _ _ ‹_›
  | apply covered_emitOp _ ‹_› ‹_›
  | apply covered_emitMov _ ‹_› ‹_›
  | apply covered_emitRotL _ ‹_› ‹_›
  | (intro _ _ _; beta_reduce)))

/-- One Keccak round before a covered continuation is covered. -/
theorem covered_emitRound {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (round : Nat)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitRound bs iv round k) := by
  have hC : ∀ (m s : Nat) {Γ : Ctxt jasminDialect} (bs : BState Γ) (iv : Nat → Ctxt.Var Γ r64)
      (k : Cont t), ContCovered S k → S.Covered (emitTheta_C m s bs iv k) := by
    intro m
    induction m with
    | zero => intro _ _ bs iv k hk; exact hk bs iv
    | succ m ih =>
      intro s _ bs iv k hk
      simp only [emitTheta_C, emitThetaCCol]
      cov_chain ih
  have hD : ∀ (m s : Nat) {Γ : Ctxt jasminDialect} (bs : BState Γ) (iv : Nat → Ctxt.Var Γ r64)
      (k : Cont t), ContCovered S k → S.Covered (emitTheta_D m s bs iv k) := by
    intro m
    induction m with
    | zero => intro _ _ bs iv k hk; exact hk bs iv
    | succ m ih =>
      intro s _ bs iv k hk
      simp only [emitTheta_D, emitThetaDCol]
      cov_chain ih
  have hR : ∀ (m s : Nat) {Γ : Ctxt jasminDialect} (bs : BState Γ) (iv : Nat → Ctxt.Var Γ r64)
      (k : Cont t), ContCovered S k → S.Covered (emitRhoPi m s bs iv k) := by
    intro m
    induction m with
    | zero => intro _ _ bs iv k hk; exact hk bs iv
    | succ m ih =>
      intro s _ bs iv k hk
      simp only [emitRhoPi, emitRhoPiLane]
      cov_chain ih
  have hX : ∀ (m s : Nat) {Γ : Ctxt jasminDialect} (bs : BState Γ) (iv : Nat → Ctxt.Var Γ r64)
      (k : Cont t), ContCovered S k → S.Covered (emitChi m s bs iv k) := by
    intro m
    induction m with
    | zero => intro _ _ bs iv k hk; exact hk bs iv
    | succ m ih =>
      intro s _ bs iv k hk
      simp only [emitChi, emitChiLane]
      cov_chain ih
  exact hC 5 0 bs iv _ fun _ _ => hD 5 0 _ _ _ fun _ _ => hR 25 0 _ _ _ fun _ _ =>
    hX 25 0 _ _ _ fun _ _ => covered_emitOp S h64 hcov _ _ _ _ _ _ _ hk

/-- **Coverage of the permutation.** A lane shape of 64-bit lanes covering every
    `JasminBinOp` covers `keccakF1600Com`. -/
theorem covered_keccakF1600Com : S.Covered keccakF1600Com := by
  have hRs : ∀ (m s : Nat) {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
      (iv : Nat → Ctxt.Var Γ r64) (k : Cont t), ContCovered S k →
      S.Covered (emitRounds m s bs iv k) := by
    intro m
    induction m with
    | zero => intro _ _ _ bs iv k hk; exact hk bs iv
    | succ m ih =>
      intro s _ _ bs iv k hk
      simp only [emitRounds]
      exact covered_emitRound S h64 hcov _ _ _ _ fun _ _ => ih _ _ _ _ hk
  have hO : ∀ (m s : Nat) {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
      (iv : Nat → Ctxt.Var Γ r64) (k : Cont t), ContCovered S k →
      S.Covered (emitOutStage m s bs iv k) := by
    intro m
    induction m with
    | zero => intro _ _ _ bs iv k hk; exact hk bs iv
    | succ m ih =>
      intro s _ _ bs iv k hk
      simp only [emitOutStage, emitLaneSelfMov]
      cov_chain ih
  exact hRs 24 0 _ _ _ fun _ _ => hO 25 0 _ _ _ fun _ _ => trivial

end Coverage

/-! ## 2. Four permutations per YMM register -/

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect (yQwordW)

/-- `qwordYmmV` covers `keccakF1600Com`. -/
theorem covered_qwordYmmV_keccakF1600Com : qwordYmmV.Covered keccakF1600Com :=
  covered_keccakF1600Com qwordYmmV rfl (fun _ => rfl)

/-- **Four permutations per YMM register.** Qword lane `k` of the 256-bit lane map of
    `keccakF1600Com` is the scalar permutation program on the lane-`k` valuation. -/
theorem laneMapYmmV_keccakF1600Com_denote (W : Ctxt.Valuation (qwordYmmV.widenCtxt inCtxt))
    (k : Fin 4) :
    yQwordW ((laneMapVec qwordYmmV keccakF1600Com).denote W) k.val
      = keccakF1600Com.denote (qwordYmmV.laneOf k inCtxt W) :=
  laneMapYmmV_denote_default keccakF1600Com covered_qwordYmmV_keccakF1600Com W k

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakFipsAscent
  (keccakVal fipsRounds keccakF1600Com_denote_spec) in
/-- **Four FIPS 202 permutations per YMM register.** When lane `k` of the inputs is
    the canonical input valuation `keccakVal (a k)` of the state `a k`, qword lane `k` of
    the 256-bit lane map of `keccakF1600Com` is lane 24 of the FIPS 202
    Keccak-p[1600,24] permutation of `a k`. -/
theorem laneMapYmmV_keccakF1600Com_fips (W : Ctxt.Valuation (qwordYmmV.widenCtxt inCtxt))
    (a : Fin 4 → KeccakDiffuseExact.Lanes)
    (hW : ∀ k : Fin 4, qwordYmmV.laneOf k inCtxt W = keccakVal (a k)) (k : Fin 4) :
    yQwordW ((laneMapVec qwordYmmV keccakF1600Com).denote W) k.val
      = fipsRounds 24 0 (a k) ⟨24, by decide⟩ := by
  rw [laneMapYmmV_keccakF1600Com_denote W k, hW k]
  exact keccakF1600Com_denote_spec (a k)

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakLaneMapYmm
