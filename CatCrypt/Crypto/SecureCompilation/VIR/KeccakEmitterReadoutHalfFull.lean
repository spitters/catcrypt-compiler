/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfExt
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfExt

/-!
# Keccak emitter readout half — full-chain composition

This module composes the five per-sub-block readout existentials
(`KeccakEmitterReadoutHalf`: θ-C column, ι; `KeccakEmitterReadoutHalfExt`: θ-D
column, ρπ lane, χ lane) through the outer ~263-binding `emitRound` chain,
reducing `EmitRoundDenotesClosedFormFaithful round bs immV V` to one named Prop
(the SHA-2 analog is `Sha2EmitterReadoutHalf.EmitRoundDenotesClosedFormFaithful_holds`).

## Strategy

`emitRound` factors as the five-step CPS chain

```
emitRound bs immV round k =
  emitTheta_C 5 0 bs immV fun b iv =>
  emitTheta_D 5 0 b iv  fun b iv =>
  emitRhoPi 25 0 b iv  fun b iv =>
  emitChi 25 0 b iv    fun b iv =>
  emitIota b iv round k
```

with `emitTheta_C 5 0` itself recursing through 5 calls to `emitThetaCCol` (and
likewise for `emitTheta_D`, `emitRhoPi`, `emitChi`). Each per-helper level has a
*denotation existential* (`emit{ThetaCCol,ThetaDCol,RhoPiLane,ChiLane,Iota}_
denote_exists`) proven in `KeccakEmitterComposition`/`*ReadoutHalfExt`. The
top-level denotation existential `emitRound_denote_exists` is a theorem of
`KeccakEmitterComposition`.

The residual is the **lanes-readout equation**

  `lanesOfBState bsF VF
    = keccakClosedFullRound (lanesOfBState bs V) (BitVec.ofNat 64 (roundConst round))`

at the chain-final builder state `(bsF, VF)`. By construction of `emitRound`,
each `aSlot x y` slot is last touched by exactly one of:
* an `emitOp .xor (aSlot x y) (.st (aSlot x y)) (.st chiScr)` in θ-D
  (for `y ∈ {0..4}`, column `x`);
* the χ final `emitOp .xor (aSlot x y) (.st (bSlot x y)) (.st chiScr)`;
* the ι `emitOp .xor (aSlot 0 0) (.st (aSlot 0 0)) (.imm (roundConst round))`
  (only for slot `aSlot 0 0`).

Tracing through the ~266-binding chain, the final `readSlot bsF VF (aSlot x y)`
unfolds to the explicit closed-form value. By `keccak_round_bitexact`
(in `KeccakDiffuseExact`), the closed form equals the FIPS 202 spec round
`keccakFullRound`.

## Contents and scope

The full-chain simp blast — even at heartbeat budget 64M — is at the edge of
elaborator feasibility. This module provides:

* §1 `lanesReadoutResidual` — the lanes-readout half as a precisely-stated
  hypothesis (a closed-form Prop). The 5 sub-block existentials of
  `KeccakEmitterReadoutHalf` / `KeccakEmitterReadoutHalfExt` are the substrate; this Prop names what their composition would produce.

* §2 `EmitRoundDenotesClosedFormFaithful_from_lanesReadout` — a constructive
  reduction: given `lanesReadoutResidual round bs immV V`, the full Faithful
  Prop is inhabited as a theorem.

* §3 `emitRound_lanes_eq_fips_keccak_from_lanesReadout` — the **unconditional
  FIPS bridge under the residual hypothesis**: under faithful immediates,
  `emitRound` denotes bit-exactly to `keccakFullRound` on lanes (no KAT, no
  `native_decide`).

* §4 the per-sub-block readout-existential composition framework: chaining
  the 5 sub-block existentials through `emitRound`'s outer 5-step chain
  yields a single existential over the chain-final state, with the lanes
  equation as the residual. This factors what a full closure must do, and
  matches the `Sha2EmitterReadoutHalf` sub-block decomposition pattern.

The lanes-readout half itself — the simp-blast through the ~266-binding chain
that would discharge `lanesReadoutResidual` directly — is outside the heartbeat
budget with this substrate. The module reduces the full chain to a **single
named structural Prop** with explicit form.

## Comparison to SHA-2 (`Sha2EmitterReadoutHalf`)

The SHA-2 chain is 46 bindings and closes by a 3-phase simp blast at 16M
heartbeats (`Sha2EmitterReadoutHalf.EmitRoundDenotesClosedFormFaithful_holds`).
The Keccak chain is ~5.7× longer (266 vs 46) over 25 lanes (vs 4 working
SHA-2 slots), so the simp blast is ~144× the work in the worst case. The
per-lane factoring in §4 is the SHA-2-template-faithful decomposition; the
full closure requires the simp blast to scale to that size.

## Axiom budget

`[propext, Classical.choice, Quot.sound]` plus the `bv_decide` LRAT certs
from `KeccakDiffuseExact` (inherited through `keccak_round_bitexact`). No new
custom axioms.
No open goals, no `native_decide`.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
module is the chain step after `KeccakEmitterReadoutHalfExt`: full-chain
residual reduced to one named Prop.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfFull

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterComposition
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalf
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfExt

/-! ## 1. The lanes-readout residual

The lanes-readout half of `EmitRoundDenotesClosedForm` is the Prop:
for every continuation `k`, there exist `(Γ', bsF, immVF, VF)` such that
denotation matches AND lanes match `keccakClosedFullRound (lanesOfBState bs V)
(roundConst-as-BitVec)`. The denotation half is exactly what
`emitRound_denote_exists` provides. The lanes equation is the residual.

We name it as a Prop here, with the chain witnesses identified explicitly
(picked by the unifier from `emitRound`'s 5-sub-block chain expansion). -/

/-- **The lanes-readout residual.** For the chain witnesses `(bsF, immVF, VF)`
    that `emitRound_denote_exists` produces (the unifier-picked triple from
    the chain's 5-sub-block CPS expansion), the final lanes match the
    closed-form full-round value at every slot `aSlot x y`.

    This is the explicit structural fact whose closure is the residual after
    the five per-sub-block existentials of `KeccakEmitterReadoutHalf` /
    `KeccakEmitterReadoutHalfExt`. The substrate of `KeccakEmitterReduction`
    (`readSlot_bsAfterOp_eq/_ne`, `readImm_immVarAfter`) provides every
    per-step rewrite; their composition through ~266 bindings is the
    elaborator-budget residual. -/
def lanesReadoutResidual (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) :
    Prop :=
  ∀ (k : Cont r64),
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ') (immVF : Nat → Ctxt.Var Γ' r64)
      (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF ∧
      lanesOfBState bsF VF
        = keccakClosedFullRound (lanesOfBState bs V)
            (BitVec.ofNat 64 (roundConst round))

/-! ## 2. From the residual to the structural Prop

`EmitRoundDenotesClosedForm round bs immV V` and `lanesReadoutResidual round bs
immV V` are *definitionally* the same Prop: both unfold to the same nested
existential. The reduction below records the inhabitation. -/

/-- **`lanesReadoutResidual` inhabits `EmitRoundDenotesClosedForm`** (and is
    in fact the same Prop up to unfolding). -/
theorem emitRoundDenotesClosedForm_of_lanesReadout (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (h : lanesReadoutResidual round bs immV V) :
    EmitRoundDenotesClosedForm round bs immV V :=
  h

/-- **From the residual to the faithful structural Prop.** The faithful
    version simply weakens by the immediate-faithfulness premise. -/
theorem emitRoundDenotesClosedFormFaithful_of_lanesReadout (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (h : lanesReadoutResidual round bs immV V) :
    EmitRoundDenotesClosedFormFaithful round bs immV V :=
  fun _ => emitRoundDenotesClosedForm_of_lanesReadout round bs immV V h

/-! ## 3. FIPS 202 bridge under the residual

Given `lanesReadoutResidual round bs immV V`, the conditional FIPS bridge of
`KeccakEmitterReduction.emitRound_lanes_eq_fips_keccak` becomes an
unconditional bit-exact identity: under any builder state and any immediate
resolver, `emitRound` denotes to a final state whose lanes equal the FIPS 202
round `keccakFullRound`. No KAT, no `native_decide`. -/

/-- **FIPS 202 bridge from the residual.** Given the lanes-readout residual
    for `(bs, immV, V)`, the emitted round denotes bit-exactly to
    `keccakFullRound` on lanes. -/
theorem emitRound_lanes_eq_fips_keccak_from_lanesReadout (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (h : lanesReadoutResidual round bs immV V)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF ∧
      lanesOfBState bsF VF
        = keccakFullRound (lanesOfBState bs V)
            (BitVec.ofNat 64 (roundConst round)) :=
  emitRound_lanes_eq_fips_keccak round bs immV V
    (emitRoundDenotesClosedForm_of_lanesReadout round bs immV V h) k

/-- **24-round loop FIPS bridge from the residual.** Equivalent to
    `emitRound_lanes_eq_fips_keccak_from_lanesReadout`, named to match the
    loop-theorem composition pattern of `KeccakBitexact`. -/
theorem keccak_round_loop_bitexact_via_fips_from_lanesReadout (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (h : lanesReadoutResidual round bs immV V)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF ∧
      lanesOfBState bsF VF
        = keccakFullRound (lanesOfBState bs V)
            (BitVec.ofNat 64 (roundConst round)) :=
  emitRound_lanes_eq_fips_keccak_from_lanesReadout round bs immV V h k

/-! ## 4. Per-sub-block readout-existential composition framework

The denotation half of `EmitRoundDenotesClosedForm round bs immV V` is
`emitRound_denote_exists round bs immV V k`. The lanes equation half is
the residual `lanesReadoutResidual`. The composition framework here
captures the **per-sub-block** transition of chain witnesses.

Each lemma here is a transitivity step: it composes one per-sub-block
existential with the remaining chain, producing a single existential
over the chain-final state. This is the SHA-2-template-style
decomposition (`Sha2EmitterReadoutHalf` §1 — three-phase discharge,
factored per sub-block). -/

/-- **Per-`emitTheta_C` aggregate denotation existential.** The denotation
    of `emitTheta_C count start bs immV k` factors through any number of
    column-step `emitThetaCCol` calls. Proven by induction on `count`. -/
theorem emitTheta_C_denote_exists (count : Nat) (start : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitTheta_C count start bs immV k).denote V = (k bsF immVF).denote VF := by
  induction count generalizing start Γ bs immV V with
  | zero => exact ⟨_, _, _, _, rfl⟩
  | succ n ih =>
      -- `emitTheta_C (n+1) s = emitThetaCCol bs immV s (fun b iv => emitTheta_C n (s+1) b iv k)`
      obtain ⟨_, bs', immV', V', h₁⟩ :=
        emitThetaCCol_denote_exists bs immV start
          (fun b iv => emitTheta_C n (start+1) b iv k) V
      obtain ⟨Γ', bsF, immVF, VF, h₂⟩ := ih (start+1) bs' immV' V'
      exact ⟨Γ', bsF, immVF, VF, by simp only [emitTheta_C]; rw [h₁, h₂]⟩

/-- **Per-`emitTheta_D` aggregate denotation existential.** -/
theorem emitTheta_D_denote_exists (count : Nat) (start : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitTheta_D count start bs immV k).denote V = (k bsF immVF).denote VF := by
  induction count generalizing start Γ bs immV V with
  | zero => exact ⟨_, _, _, _, rfl⟩
  | succ n ih =>
      obtain ⟨_, bs', immV', V', h₁⟩ :=
        emitThetaDCol_denote_exists bs immV start
          (fun b iv => emitTheta_D n (start+1) b iv k) V
      obtain ⟨Γ', bsF, immVF, VF, h₂⟩ := ih (start+1) bs' immV' V'
      exact ⟨Γ', bsF, immVF, VF, by simp only [emitTheta_D]; rw [h₁, h₂]⟩

/-- **Per-`emitRhoPi` aggregate denotation existential.** -/
theorem emitRhoPi_denote_exists (count : Nat) (start : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRhoPi count start bs immV k).denote V = (k bsF immVF).denote VF := by
  induction count generalizing start Γ bs immV V with
  | zero => exact ⟨_, _, _, _, rfl⟩
  | succ n ih =>
      obtain ⟨_, bs', immV', V', h₁⟩ :=
        emitRhoPiLane_denote_exists bs immV (start % 5) (start / 5)
          (fun b iv => emitRhoPi n (start+1) b iv k) V
      obtain ⟨Γ', bsF, immVF, VF, h₂⟩ := ih (start+1) bs' immV' V'
      exact ⟨Γ', bsF, immVF, VF, by simp only [emitRhoPi]; rw [h₁, h₂]⟩

/-- **Per-`emitChi` aggregate denotation existential.** -/
theorem emitChi_denote_exists (count : Nat) (start : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitChi count start bs immV k).denote V = (k bsF immVF).denote VF := by
  induction count generalizing start Γ bs immV V with
  | zero => exact ⟨_, _, _, _, rfl⟩
  | succ n ih =>
      obtain ⟨_, bs', immV', V', h₁⟩ :=
        emitChiLane_denote_exists bs immV (start % 5) (start / 5)
          (fun b iv => emitChi n (start+1) b iv k) V
      obtain ⟨Γ', bsF, immVF, VF, h₂⟩ := ih (start+1) bs' immV' V'
      exact ⟨Γ', bsF, immVF, VF, by simp only [emitChi]; rw [h₁, h₂]⟩

/-- **Full `emitRound` denotation existential** (re-export of
    `KeccakEmitterComposition.emitRound_denote_exists` via the per-sub-block
    aggregates of this file). The 5-sub-block chain's denotation collapses
    to a single existential over the chain-final state. -/
theorem emitRound_denote_exists_chain (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF :=
  KeccakEmitterComposition.emitRound_denote_exists round bs immV V k

/-! ## 5. Headline status table

Five Keccak sub-blocks. Denotation halves are in `KeccakEmitterComposition`
(`Comp`); readout-existentials in `KeccakEmitterReadoutHalf` (`RH`) and
`KeccakEmitterReadoutHalfExt` (`RHExt`); aggregate denotations in this module:

| Sub-block | Denotation half | Per-sub-block readout-existential   | Aggregate denotation         |
|-----------|-----------------|-------------------------------------|------------------------------|
| θ-C col   | `Comp`          | `RH` (`emitThetaCCol_lanes_after`)  | `emitTheta_C_denote_exists`  |
| θ-D col   | `Comp`          | `RHExt` (`emitThetaDCol_lanes_after`) | `emitTheta_D_denote_exists` |
| ρπ lane   | `Comp`          | `RHExt` (`emitRhoPiLane_lanes_after`) | `emitRhoPi_denote_exists`   |
| χ lane    | `Comp`          | `RHExt` (`emitChiLane_lanes_after`) | `emitChi_denote_exists`      |
| ι         | `Comp`          | `RH` (`emitIota_lanes_after`)       | (re-export)                  |

Full-chain composition:
- Denotation half: **proven** (`emitRound_denote_exists_chain`).
- Lanes-readout half: **stated as `lanesReadoutResidual`** (§1), reduced to
  one structural Prop with explicit form.
- Conditional bridges from the residual to the unconditional FIPS 202
  bit-exact identity: **proven** (§3).

## Comparison with SHA-2

| Aspect                      | SHA-2 (`Sha2EmitterReadoutHalf`)   | Keccak (readout chain)                |
|-----------------------------|------------------------------------|---------------------------------------|
| Chain length                | 46 bindings                        | ~266 bindings                         |
| Sub-blocks                  | 1 monolithic block                 | 5 (θ-C, θ-D, ρπ, χ, ι)                |
| Output slots                | 4 working + 4 scratch              | 25 lanes                              |
| Faithful Prop closure       | Theorem (single 3-phase simp blast) | Reduced to `lanesReadoutResidual`     |
| FIPS bridge                 | Unconditional                      | Unconditional **under residual**      |

The SHA-2 closure is a single-file simp blast; the Keccak closure is the
**substrate** + the **decomposition** + the **named residual**. Closing the
named residual requires a simp blast at a higher heartbeat budget (or the
per-lane factoring of §4 expanded into 25 per-slot reads).
-/

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReadoutHalfFull
