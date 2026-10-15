/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterInitEnv
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterInitEnv

/-!
# SHA-2 emitter readout half — closing `EmitRoundDenotesClosedFormFaithful`

This module proves the readout half of the SHA-2 emitter composition. The
denotation half of `EmitRoundDenotesClosedFormFaithful` is in
`Sha2EmitterComposition`; the faithfulness predicates are in
`Sha2EmitterInitEnv`. The *readout half* states that under faithful inputs,
`readSt envF VF` after the 46-binding `emitRound` chain equals
`roundClosedForm sp …` slot-by-slot.

The strategy here is a single `simp` blast over the substrate's `@[simp]`
slot-reading lemmas (`readSlot_envAfterOp_eq/_ne`, `readInp_envAfterOp`),
discharging the slot-disjointness side conditions by `decide` over the
concrete `Nat` constants (`wkA, t1S, t2S, sigS, chmS, scA, scB, scC, scD`).

Together with the denotation half in `Sha2EmitterComposition`, this inhabits
`EmitRoundDenotesClosedFormFaithful sp rt e V` for any width-faithful
valuation. Plugged into `Sha2EmitterInitEnv.emitRound_initEnv_eq_fips_sha{256,512}`,
the bridges become **unconditional**: SHA-2's emitted round denotes
bit-exactly to FIPS 180-4 with no KAT dependence anywhere, modulo only the
six `bv_decide` LRAT certs from `Sha2DiffuseExact.crotr_eq_rotr_sha{256,512}`.

## Contents

* `EmitRoundDenotesClosedFormFaithful_holds` (§2): the structural Prop is
  inhabited as a *theorem*. All goals closed; no `native_decide`.

* `emitRound_initEnv_eq_fips_sha256_unconditional`,
  `emitRound_initEnv_eq_fips_sha512_unconditional` (§3): the unconditional
  forms of the `Sha2EmitterInitEnv` bridges — `EmitRoundDenotesClosedFormFaithful` hypothesis
  dropped.

## Axiom budget

`[propext, Classical.choice, Quot.sound]` plus the six `bv_decide` LRAT
certs from `Sha2DiffuseExact.crotr_eq_rotr_sha{256,512}` (inherited via
`closed_form_eq_fips_sha*`). No new custom axioms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReadoutHalf

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2DiffuseExact
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterComposition
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterInitEnv

/-! ## 1. The discharge strategy

`emitRound` is a 46-binding chain through 5 FIPS sub-blocks. The
strategy that closes the readout half:

* **Step 0 — Substrate rewrites.** Unfold `emitRound` and rewrite the
  helper chain through the substrate's `_denote` lemmas
  (`emitOp_denote`, `cp_denote'`, `sigma_branch_rotr`, `or_self_apply`).
  Refine the existential by `rfl`; the unifier picks `envF`, `VF`.

* **Step 1 — Slot-disjointness simp blast.** A single `simp` blast over
  the substrate's `@[simp]` slot-reading lemmas
  (`readSlot_envAfterOp_eq/_ne`, `readInp_envAfterOp`) with
  `decide := true` collapses every read at a concrete working/scratch
  slot (`100..117`). The only reads that survive are at the symbolic
  schedule slot `rt`.

* **Step 2 — `rt`-disjointness rewrites.** Pre-derive `rt ≠ d` for
  every chain write target `d ∈ {110..117}` from `hrt : rt < wkA = 100`,
  then iterate `rw [readSlot_envAfterOp_ne … _ rt h_rt_d]` per layer.
  This peels off the remaining envAfterOp layers in the chain reads
  at slot `rt`.

* **Step 3 — Algebraic normalisation.** Unfold `JasminBinOp.{add, xor,
  and, or, shl, shr}.apply` (→ `+`/`^^^`/`&&&`/`|||`/`<<<`/`>>>`) and
  the closed-form definitions (`cBigSigma`, `cCh`, `cMaj`, `crotr`).
  Apply the faithfulness rewrites `hAmt _ hSig*` for each shift amount
  and `hAllOnes` for the mask. -/

/-! ## 2. Inhabitation of `EmitRoundDenotesClosedFormFaithful`

The structural Prop holds for any environment and valuation, provided
the faithful-environment hypotheses are supplied as the Prop demands. -/

/-- Bounds on a `Sha2Spec`'s sigma rotation amounts, needed for the readout-half
    discharge to apply the `hAmt` faithfulness premise (which requires
    `n ≤ sp.w`). Satisfied by `sha256Spec` and `sha512Spec` (proven by `decide`). -/
structure Sha2SpecBounds (sp : Sha2Spec) : Prop where
  /-- `Σ0`'s three rotate amounts each fit in `sp.w`. -/
  bigSig0_le : sp.bigSig0.1 ≤ sp.w ∧ sp.bigSig0.2.1 ≤ sp.w ∧ sp.bigSig0.2.2 ≤ sp.w
  /-- `Σ1`'s three rotate amounts each fit in `sp.w`. -/
  bigSig1_le : sp.bigSig1.1 ≤ sp.w ∧ sp.bigSig1.2.1 ≤ sp.w ∧ sp.bigSig1.2.2 ≤ sp.w

/-- `sha256Spec` satisfies the bounds. -/
theorem sha256_bounds : Sha2SpecBounds sha256Spec where
  bigSig0_le := by decide
  bigSig1_le := by decide

/-- `sha512Spec` satisfies the bounds. -/
theorem sha512_bounds : Sha2SpecBounds sha512Spec where
  bigSig0_le := by decide
  bigSig1_le := by decide

/-- The mask of a count equal to the width is `0` or the width. -/
theorem shiftMask_self_cases (w : Nat) : shiftMask w w = 0 ∨ shiftMask w w = w := by
  unfold shiftMask
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- The shift-or rotation with masked counts equals the unmasked one for every
    amount `k ≤ w`. -/
theorem rotr_masked_eq {w k : Nat} (hk : k ≤ w) (x : BitVec w) :
    (x >>> shiftMask w k ||| x <<< shiftMask w (w - k)) = (x >>> k ||| x <<< (w - k)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rcases shiftMask_self_cases w with h | h <;> simp [h]
  · rcases Nat.lt_or_ge k w with hlt | hge
    · rw [shiftMask_of_lt hlt, shiftMask_of_lt (by omega : w - k < w)]
    · obtain rfl : k = w := by omega
      rcases shiftMask_self_cases k with h | h <;>
        simp [h, BitVec.ushiftRight_eq_zero (Nat.le_refl k)]

theorem EmitRoundDenotesClosedFormFaithful_holds
    (sp : Sha2Spec) (rt : Nat) (hrt : rt < wkA) (hSp : Sha2SpecBounds sp)
    {Γ : Ctxt jasminDialect}
    (e : Env sp.w Γ) (V : Ctxt.Valuation Γ) :
    EmitRoundDenotesClosedFormFaithful sp rt e V := by
  intro hAmt hAllOnes k
  -- Reduce the chain through the substrate.
  unfold emitRound
  simp only [emitSigma, emitRotr, cp, sigma_branch_rotr, emitOp_denote, or_self_apply]
  -- Discharge the denotation half by `rfl`; the unifier picks `envF`, `VF`.
  refine ⟨_, _, _, rfl, ?_⟩
  -- Now the readout half: `readSt sp envF VF = roundClosedForm sp …`.
  -- envF / VF are concrete nested `envAfterOp` / `V.extend` chains.
  -- The reads at slot `rt` (the schedule word) are pushed through every
  -- layer using `hrt : rt < wkA = 100`, so `rt ≠ d` for every chain write
  -- target `d ∈ {100..117}`. Pre-derive these inequalities for simp.
  have h_rt_100 : rt ≠ 100 := by unfold wkA at hrt; omega
  have h_rt_101 : rt ≠ 101 := by unfold wkA at hrt; omega
  have h_rt_102 : rt ≠ 102 := by unfold wkA at hrt; omega
  have h_rt_103 : rt ≠ 103 := by unfold wkA at hrt; omega
  have h_rt_104 : rt ≠ 104 := by unfold wkA at hrt; omega
  have h_rt_105 : rt ≠ 105 := by unfold wkA at hrt; omega
  have h_rt_106 : rt ≠ 106 := by unfold wkA at hrt; omega
  have h_rt_107 : rt ≠ 107 := by unfold wkA at hrt; omega
  have h_rt_110 : rt ≠ 110 := by unfold wkA at hrt; omega
  have h_rt_111 : rt ≠ 111 := by unfold wkA at hrt; omega
  have h_rt_112 : rt ≠ 112 := by unfold wkA at hrt; omega
  have h_rt_113 : rt ≠ 113 := by unfold wkA at hrt; omega
  have h_rt_114 : rt ≠ 114 := by unfold wkA at hrt; omega
  have h_rt_115 : rt ≠ 115 := by unfold wkA at hrt; omega
  have h_rt_116 : rt ≠ 116 := by unfold wkA at hrt; omega
  have h_rt_117 : rt ≠ 117 := by unfold wkA at hrt; omega
  -- Step 1: rewrite all reads at fixed working/scratch slots {100..117}
  -- via the substrate's @[simp] set with `decide := true` (every Nat
  -- side-condition is decidable: 100 ≠ 110, 100 ≠ 113, etc.). This
  -- collapses all reads except those at the symbolic schedule slot `rt`.
  simp (config := { decide := true }) only [readSt, roundClosedForm,
    readSrc_sl, readSrc_iw, readSrc_amt,
    readSlot_envAfterOp_eq, readSlot_envAfterOp_ne,
    readInp_envAfterOp,
    wkA, t1S, t2S, sigS, chmS, scA, scB, scC, scD]
  -- Step 2: discharge the remaining `readSlot (envAfterOp_chain) (V.extend_chain) rt`.
  -- Loop until no more `readSlot_envAfterOp_ne` rewrites apply.
  -- Each iteration peels off one chain layer of the read at slot `rt`.
  repeat (first
    | rw [readSlot_envAfterOp_ne _ 110 _ _ rt h_rt_110]
    | rw [readSlot_envAfterOp_ne _ 111 _ _ rt h_rt_111]
    | rw [readSlot_envAfterOp_ne _ 112 _ _ rt h_rt_112]
    | rw [readSlot_envAfterOp_ne _ 113 _ _ rt h_rt_113]
    | rw [readSlot_envAfterOp_ne _ 114 _ _ rt h_rt_114]
    | rw [readSlot_envAfterOp_ne _ 115 _ _ rt h_rt_115]
    | rw [readSlot_envAfterOp_ne _ 116 _ _ rt h_rt_116]
    | rw [readSlot_envAfterOp_ne _ 117 _ _ rt h_rt_117])
  -- Step 3: normalize LHS = RHS via algebraic identities.
  -- Unfold `JasminBinOp.xx.apply` (→ `+`/`&&&`/`|||`/`^^^`/`>>>`/`<<<`) and
  -- the closed-form definitions (`cBigSigma`, `cCh`, `cMaj`, `crotr`) so
  -- both sides reduce to a common BitVec expression in the original `(e, V)`
  -- reads. Apply the faithfulness rewrites for shift amounts (`hAmt`) and
  -- the mask (`hAllOnes`).
  obtain ⟨⟨hB01, hB02, hB03⟩, ⟨hB11, hB12, hB13⟩⟩ := hSp
  have hSub1 : sp.w - sp.bigSig1.1 ≤ sp.w := Nat.sub_le _ _
  have hSub2 : sp.w - sp.bigSig1.2.1 ≤ sp.w := Nat.sub_le _ _
  have hSub3 : sp.w - sp.bigSig1.2.2 ≤ sp.w := Nat.sub_le _ _
  have hSub4 : sp.w - sp.bigSig0.1 ≤ sp.w := Nat.sub_le _ _
  have hSub5 : sp.w - sp.bigSig0.2.1 ≤ sp.w := Nat.sub_le _ _
  have hSub6 : sp.w - sp.bigSig0.2.2 ≤ sp.w := Nat.sub_le _ _
  simp only [JasminBinOp.apply, cBigSigma, cCh, cMaj, crotr, hAllOnes,
    rotr_masked_eq hB01, rotr_masked_eq hB02, rotr_masked_eq hB03,
    rotr_masked_eq hB11, rotr_masked_eq hB12, rotr_masked_eq hB13,
    hAmt _ hB01, hAmt _ hB02, hAmt _ hB03,
    hAmt _ hB11, hAmt _ hB12, hAmt _ hB13,
    hAmt _ hSub1, hAmt _ hSub2, hAmt _ hSub3,
    hAmt _ hSub4, hAmt _ hSub5, hAmt _ hSub6]

/-! ## 3. Unconditional FIPS bridges for the emitter on `initEnv`

With `EmitRoundDenotesClosedFormFaithful` inhabited as a theorem,
`Sha2EmitterInitEnv.emitRound_initEnv_eq_fips_sha{256,512}` can drop its
`hProp` hypothesis. The resulting statements are the **unconditional**
FIPS bit-exact identities: under a faithful runtime store (the input layout
that the C harness provides), the emitted SHA-2 round denotes bit-exactly to
FIPS 180-4 — no KAT, no `native_decide`, no residual hypothesis.

`rt < wkA` is the trivial loop-context premise (`emitRound` is invoked
with `rt ∈ {0..rounds-1}`, all ≤ 79 < 100 = `wkA`). -/

/-- **SHA-256 unconditional FIPS bridge for `initEnv`** — KAT-free.
    Given a faithful runtime store, the emitted `emitRound sha256Spec rt`
    on `initEnv sha256Spec` denotes bit-exactly to the FIPS 180-4 round.
    The `rt < wkA` premise is satisfied by every round index used by
    `emitRounds` (`rt ∈ {0..63}`, all < 100 = `wkA`). -/
theorem emitRound_initEnv_eq_fips_sha256_unconditional (rt : Nat) (hrt : rt < wkA)
    (V : Ctxt.Valuation (inCtxt sha256Spec.w))
    (msg chain Kc : Nat → BitVec sha256Spec.w)
    (hV : InpFaithful sha256Spec V msg chain Kc)
    (k : SCont sha256Spec.w (Rw sha256Spec.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha256Spec.w Γ')
      (VF : Ctxt.Valuation Γ'),
      (emitRound sha256Spec rt (initEnv sha256Spec) k).denote V = (k envF).denote VF ∧
      readSt sha256Spec envF VF
        = fipsRound sha256Spec (readSt sha256Spec (initEnv sha256Spec) V)
            (readInp (initEnv sha256Spec) V (kIdx rt))
            (readSlot (initEnv sha256Spec) V rt) :=
  emitRound_initEnv_eq_fips_sha256 rt V msg chain Kc hV
    (EmitRoundDenotesClosedFormFaithful_holds sha256Spec rt hrt sha256_bounds _ V) k

/-- **SHA-512 unconditional FIPS bridge for `initEnv`** — KAT-free.
    Same shape as SHA-256, at width 64. `rt ∈ {0..79}`, all < 100 = `wkA`. -/
theorem emitRound_initEnv_eq_fips_sha512_unconditional (rt : Nat) (hrt : rt < wkA)
    (V : Ctxt.Valuation (inCtxt sha512Spec.w))
    (msg chain Kc : Nat → BitVec sha512Spec.w)
    (hV : InpFaithful sha512Spec V msg chain Kc)
    (k : SCont sha512Spec.w (Rw sha512Spec.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha512Spec.w Γ')
      (VF : Ctxt.Valuation Γ'),
      (emitRound sha512Spec rt (initEnv sha512Spec) k).denote V = (k envF).denote VF ∧
      readSt sha512Spec envF VF
        = fipsRound sha512Spec (readSt sha512Spec (initEnv sha512Spec) V)
            (readInp (initEnv sha512Spec) V (kIdx rt))
            (readSlot (initEnv sha512Spec) V rt) :=
  emitRound_initEnv_eq_fips_sha512 rt V msg chain Kc hV
    (EmitRoundDenotesClosedFormFaithful_holds sha512Spec rt hrt sha512_bounds _ V) k

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReadoutHalf
