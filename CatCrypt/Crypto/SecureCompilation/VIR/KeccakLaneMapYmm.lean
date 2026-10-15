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

`KeccakEmit.keccakF1600Com` is a chain of bindings at width 64: `regArith` over the
ops `xor`, `or` and `and`, and the immediate-count shifts `shlImm` / `shrImm` of its
rotates, at literal counts below 64. A lane shape of 64-bit lanes that covers every
`JasminBinOp` other than the register-count shifts and lowers the immediate-count
shifts at counts below 64 covers the whole program. At `LaneMapVec.qwordYmmV` the
lane map runs four independent permutations, one per qword lane of each YMM register,
with the rotates lowered to `vpsllq` / `vpsrlq`.

The coverage proof follows the emitter's own recursion, so its cost does not depend on
the size of the unrolled program.

## Main results

* `covered_keccakF1600Com`: every lane shape of 64-bit lanes covering the
  `JasminBinOp`s other than `shl` / `shr` and the immediate-count shifts below 64
  covers `keccakF1600Com`.
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

variable (S : LaneShape) (h64 : S.laneBits = 64)
  (hcov : ∀ bop, bop ≠ .shl → bop ≠ .shr → S.covers bop = true)
  (himm : ∀ n, n < 64 → (S.immBlock .shl).isSome = true ∧ S.immCovers .shl n = true ∧
    (S.immBlock .shr).isSome = true ∧ S.immCovers .shr n = true)

/-- A Keccak emitter continuation whose every instance is covered by `S`. -/
def ContCovered {t : JasminTy} (k : Cont t) : Prop :=
  ∀ {Γ' : Ctxt jasminDialect} (bs : BState Γ') (iv : Nat → Ctxt.Var Γ' r64), S.Covered (k bs iv)

include h64 hcov himm

omit himm in
/-- One `emitOp` binding of an op other than the register-count shifts, before a
    covered continuation, is covered. -/
theorem covered_emitOp {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (op : JasminBinOp) (hl : op ≠ .shl) (hr : op ≠ .shr)
    (dst : Fin numSlots) (a b : Src)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitOp bs iv op dst a b k) :=
  ⟨⟨h64.symm, hcov op hl hr⟩, hk _ _⟩

omit hcov in
/-- One immediate-count shift binding with a count below 64, before a covered
    continuation, is covered. -/
theorem covered_emitShImm {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (left : Bool) (dst src : Fin numSlots) (n : Nat)
    (hn : n < 64) (k : Cont t) (hk : ContCovered S k) :
    S.Covered (emitShImm bs iv left dst src n k) := by
  obtain ⟨hl1, hl2, hr1, hr2⟩ := himm n hn
  cases left
  · exact ⟨⟨h64.symm, hr1, hr2⟩, hk _ _⟩
  · exact ⟨⟨h64.symm, hl1, hl2⟩, hk _ _⟩

omit himm in
/-- A slot copy before a covered continuation is covered. -/
theorem covered_emitMov {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (dst src : Fin numSlots)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitMov bs iv dst src k) :=
  covered_emitOp S h64 hcov bs iv _ (by decide) (by decide) _ _ _ k hk

/-- A rotate by a count below 64 before a covered continuation is covered. -/
theorem covered_emitRotL {t : JasminTy} {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (iv : Nat → Ctxt.Var Γ r64) (dst : Fin numSlots) (n : Nat) (hn : n < 64)
    (k : Cont t) (hk : ContCovered S k) : S.Covered (emitRotL bs iv dst n k) := by
  unfold emitRotL
  split
  · exact hk bs iv
  · next h0 =>
    have hn0 : n ≠ 0 := by simpa using h0
    refine covered_emitShImm S h64 himm _ _ _ _ _ _ (by omega) _ fun _ _ => ?_
    refine covered_emitShImm S h64 himm _ _ _ _ _ _ hn _ fun _ _ => ?_
    exact covered_emitOp S h64 hcov _ _ _ (by decide) (by decide) _ _ _ _ hk

omit h64 hcov himm in
/-- Closes a chain of `emitOp` / `emitMov` / `emitRotL` steps ending in the induction
    hypothesis `ih`. -/
macro "cov_chain" ih:term : tactic => `(tactic| repeat' (first
  | exact $ih _ _ _ _ ‹_›
  | exact rhoOffset_lt_64 _
  | decide
  | apply covered_emitOp _ ‹_› ‹_›
  | apply covered_emitMov _ ‹_› ‹_›
  | apply covered_emitRotL _ ‹_› ‹_› ‹_›
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
    hX 25 0 _ _ _ fun _ _ =>
      covered_emitOp S h64 hcov _ _ _ (by decide) (by decide) _ _ _ _ hk

/-- **Coverage of the permutation.** A lane shape of 64-bit lanes covering every
    `JasminBinOp` other than the register-count shifts, and lowering the
    immediate-count shifts `shlImm` / `shrImm` at every count below 64, covers
    `keccakF1600Com`. -/
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
      exact covered_emitRound S h64 hcov himm _ _ _ _ fun _ _ => ih _ _ _ _ hk
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

/-- `qwordYmmV` covers `keccakF1600Com`: its immediate block (`ymmQImmBlock`, from
    `qwordYmmImm`) lowers the rotates' immediate-count shifts. -/
theorem covered_qwordYmmV_keccakF1600Com : qwordYmmV.Covered keccakF1600Com :=
  covered_keccakF1600Com qwordYmmV rfl (fun bop hl hr => by cases bop <;> simp_all <;> rfl)
    (fun n hn => ⟨rfl, decide_eq_true hn, rfl, decide_eq_true hn⟩)

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
