/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenoteSeqExt
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenoteSeqExt

/-!
# Spartan / Jolt BabyBear sum-check whole-prover through the covered `RSeq`-of-control fragment

The Spartan/Jolt sum-check prover hot path is a **multi-phase counted-round
kernel**: seed the Fiat–Shamir transcript with the claimed sum, then run the
per-round loop — each round folds the round polynomial into the accumulator
(`round_eval`, a BabyBear Horner fold) and squeezes the next challenge from the
Poseidon2 transcript. Spartan's R1CS sum-check is two-phase:
`num_rounds_x = 4` cubic rounds followed by `num_rounds_y = 5` quad rounds. Its
top-level control is therefore a *sequence of a straight-line FS-init prologue
and two counted round loops*:

```
fs_init ; (for rx in 0..numRoundsX  round_step ; fs_squeeze)
        ; (for ry in 0..numRoundsY  round_step ; fs_squeeze)
```

The round count of each phase is a **compile-time constant** (`num_rounds_x`,
`num_rounds_y` — fixed by the R1CS instance shape, exactly the `MOV r8, #n`
seed of the hand `ZkSumCheckWholeProverEmit.sumcheckLoop`), so each phase
is an `RFor` and the three phases are sequenced with `RSeq`. This is exactly the
shape the canonical front accepts after the `RSeq`-of-control increment:
`translateDialectControl` closes under `RSeq`-sequencing of control blocks, so
the whole sum-check prover descends through the canonical front and carries a
**whole-program machine denote**.

This re-sources the sum-check whole-prover from a high-level `LowCT` term
(`zkSumCheckLowCT = RSeq fsInit (RSeq phase1Loop phase2Loop)`) through the
**existing covered-fragment front** — no new front — and banks the whole-program
denote homomorphism, the same recipe as
`Fe25519ScalarmultCovered.fullScalarmultCovered_denote`,
`Shake256Covered.shake256Covered_denote`, and `MayoSolveCovered.mayoSolveCovered_denote`.
It strengthens the hand `ZkSumCheckWholeProverEmit` OrchStep schedule (a
`loopLcmd` owned-back-edge object with no whole-program machine denote) to a
high-level-source descent.

## Opaque leaves — the per-round BabyBear work, exactly the exemplar tier

Each per-round leaf is **opaque** (`RCall`), exactly as `keccakf1600` /
`x25519_ladder_iter` are opaque in the two exemplars — and exactly the owned
BabyBear leaves the hand emit `Lcall`s: `round_step` is the owned
`Plonky3FriFoldEmit.friFoldCom` Horner mul-add (`acc ← α·acc + cᵢ`); `fs_squeeze`
is the owned Poseidon2 `Plonky3HashLeafEmit.hashLeafCom` challenger squeeze;
`fs_init` is the owned Poseidon2 `Plonky3CompressEmit.compressComFinal` transcript
absorb. What is banked here is the descent of the sum-check prover's **control
structure** — the FS-init prologue and the two counted round loops sequenced —
through the canonical front, with a whole-program denote. The per-round BabyBear
arithmetic (the fused Barrett mul-add, the Poseidon2 permutation, the BabyBear
inverse used in round-poly normalisation) is the separate byte-KAT obligation
(`bench/spartan_compare`, `make zk-sumcheck-fieldcore-emit-kat`), just as
Keccak-f's permutation correctness is the FIPS-202 KAT.

## What is banked

* `zkSumCheckLowCT` — the sum-check prover as `RSeq fsInit (RSeq phase1Loop phase2Loop)`.
* `zkSumCheck_coveredSeq : IsCoveredSCtlSeq zkSumCheckLowCT` — the structural
  coverage proof (an `RSeq` of a straight-line FS-init leaf and two covered
  `RFor` round loops, each looping a straight-line `RSeq` of two leaf calls).
* `zkSumCheck_front_fires` — the covered front fires on the whole prover
  (`native_decide`).
* `zkSumCheckCovered_denote` — **the main theorem**: the whole-program machine
  denote of the sum-check prover through the canonical front, via
  `transCtlSeq_denote_seq` and the `zkSumCheck_front_eq` bridge
  (`transCtlSeq = translateDialectControl` on this `RSeq`-of-leaves term, via the
  nested `transCtlSeq_rseq_congr`).

## The boundary — static round count fits; PCS curve MSM stays out

The sum-check round count is a static per-instance constant (`num_rounds_x`,
`num_rounds_y`), so `RFor` suffices — no `RWhileNz` at the round level, and the
whole prover control descends. A number of trailing loops in a *fully general*
prover would be data-dependent (a variable-length transcript, a runtime-sized
witness), which would need the `RWhileNz`/`forLoopNRt` data-dependent-count arm
outside this static-count `RFor`+`RSeq` fragment; those are not part of the
counted sum-check round schedule banked here. Orthogonally, the PCS commitment
**curve MSM** (Spartan Hyrax / Jolt commit) is curve-group arithmetic with no
owned-x86 emit — it stays outside this owned BabyBear field-core prover, exactly
as `ZkSumCheckWholeProverEmit` documents; it is a *byte-emit* residual (the
curve backend), not a *control-coverage* residual, so it does not obstruct the
whole-program control descent banked here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 0. Spartan sum-check parameters (the two-phase R1CS schedule) -/

/-- Phase-1 round count `num_rounds_x = 4` (the cubic rounds over the R1CS `x`
    variables) — the `MOV r8, #4` seed of the hand emit's Spartan loop. -/
def numRoundsX : Nat := 4
/-- Phase-2 round count `num_rounds_y = 5` (the quad rounds over the R1CS `y`
    variables) — the `MOV r8, #5` seed. Total `4 + 5 = 9` rounds, matching
    `ZkSumCheckWholeProverEmit.spartanSumcheckLoop`'s `n = 9`. -/
def numRoundsY : Nat := 5

/-! ## 1. The high-level source: the prover as `fs_init ; phase1 ; phase2` -/

/-- Tower type of the sum-check prover state bundle (round-poly buffer, Poseidon2
    transcript sponge, accumulator/challenges). All bundles (`rpoly`, `tr`,
    `acc`, `claim`) are of this placeholder type; the per-round BabyBear layout
    is the leaves' KAT concern, not the control descent's. -/
def bundleTy : TowerType := .TBytes 200

/-- A located slot of a state-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- **FS-init prologue:** absorb the claimed sum / public input into the Poseidon2
    Fiat–Shamir transcript — an opaque leaf (the owned `compressComFinal` absorb)
    threading the transcript `tr`. Straight-line (`IsCoveredS`). -/
def fsInitBody : LowCT :=
  .RCall "zk_sumcheck_fs_init" (loc "tr") [loc "tr", loc "claim"]

/-- One sum-check round body: fold the round polynomial into the accumulator
    (`round_step`, the owned BabyBear Horner mul-add), then squeeze the next
    challenge from the Poseidon2 transcript (`fs_squeeze`). Straight-line
    (`IsCoveredS`): an `RSeq` of two `RCall`s, exactly the shape of SHAKE256's
    `absorbBlockBody`. -/
def roundBody : LowCT :=
  .RSeq (.RCall "zk_sumcheck_round_step" (loc "acc") [loc "acc", loc "rpoly"])
        (.RCall "zk_fs_squeeze" (loc "tr") [loc "tr", loc "acc"])

/-- **Phase 1 — cubic rounds:** `RFor` over the `num_rounds_x` cubic rounds
    (static). A single `RFor` over the straight-line round body, so it lives in
    the denote-carrying covered fragment `IsCoveredSCtl`. -/
def phase1Loop : LowCT :=
  .RFor "rx" numRoundsX roundBody

/-- **Phase 2 — quad rounds:** `RFor` over the `num_rounds_y` quad rounds
    (static). Same owned round step + FS squeeze body. -/
def phase2Loop : LowCT :=
  .RFor "ry" numRoundsY roundBody

/-- **The full Spartan sum-check whole-prover as a multi-phase kernel:** the
    FS-init prologue *sequenced* with the two counted round-loop phases — the
    top-level `RSeq (RCall …) (RSeq (RFor …) (RFor …))` shape. -/
def zkSumCheckLowCT : LowCT :=
  .RSeq fsInitBody (.RSeq phase1Loop phase2Loop)

/-! ## 2. Coverage — the central structural proofs -/

/-- The FS-init prologue is straight-line covered. -/
theorem fsInitBody_coveredS : IsCoveredS fsInitBody :=
  .rCall "zk_sumcheck_fs_init" (loc "tr") [loc "tr", loc "claim"]

/-- The per-round body (`round_step ; fs_squeeze`) is straight-line covered. -/
theorem roundBody_coveredS : IsCoveredS roundBody :=
  .rSeq (.rCall "zk_sumcheck_round_step" (loc "acc") [loc "acc", loc "rpoly"])
        (.rCall "zk_fs_squeeze" (loc "tr") [loc "tr", loc "acc"])

/-- The phase-1 round loop is Stage-2 covered (`IsCoveredSCtl`): a bounded `RFor`
    over the straight-line round body. -/
theorem phase1Loop_covered : IsCoveredSCtl phase1Loop :=
  .rFor (.ofStraight roundBody_coveredS)

/-- The phase-2 round loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem phase2Loop_covered : IsCoveredSCtl phase2Loop :=
  .rFor (.ofStraight roundBody_coveredS)

/-- **The full Spartan sum-check prover is control-sequencing covered**
    (`IsCoveredSCtlSeq`): the FS-init leaf sequenced with the two counted round
    loops. Not expressible in `IsCoveredSCtl` (which has no `RSeq`-over-control) —
    this is exactly the `RSeq`-of-control increment, here a three-phase spine. -/
theorem zkSumCheck_coveredSeq : IsCoveredSCtlSeq zkSumCheckLowCT :=
  .rSeq (.ofCtl (.ofStraight fsInitBody_coveredS))
    (.rSeq (.ofCtl phase1Loop_covered) (.ofCtl phase2Loop_covered))

/-! ## 3. Concrete argument context — the front fires -/

/-- Four-argument context: the `tr`, `rpoly`, `acc`, `claim` bundles. -/
def proverArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `tr`/`rpoly`/`acc`/`claim` to the four bundle arguments. -/
def proverArgVM : VarMap proverArgCtx where
  lookup := fun s =>
    if s = "tr" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "rpoly" then some ⟨encodeTy bundleTy, .there .here⟩
    else if s = "acc" then some ⟨encodeTy bundleTy, .there (.there .here)⟩
    else if s = "claim" then some ⟨encodeTy bundleTy, .there (.there (.there .here))⟩
    else none

/-- **The covered front fires on the whole Spartan sum-check prover.** The FS-init
    leaf resolves its transcript/claim arguments, the two bounded `RFor` round
    loops unroll through `loopRForD` (each round body a two-leaf
    `RSeq` threading `acc`/`tr`), the `RSeq` spine composes the phase prefixes,
    and the top-level terminator closes. -/
theorem zkSumCheck_front_fires :
    (translateDialectControlTop proverArgVM zkSumCheckLowCT).isSome := by
  native_decide

/-! ## 4. `transCtlSeq` coincides with the canonical front on this term

The control-sequencing front `transCtlSeq` folds `translateDialectControl` along
the `RSeq` spine with `ComCont.comp`; the canonical `translateDialectControl`
does the *same* (its `RSeq` arm recurses into itself). On leaves (`RFor`, `RCall`)
`transCtlSeq` delegates to `translateDialectControl` through its wildcard. So on
this pure `RSeq`-of-leaves term the two fronts coincide, letting the
canonical-front translation hypothesis feed the control-sequencing homomorphism
`transCtlSeq_denote_seq` directly. -/

/-- `RSeq` congruence for the two fronts: if both children agree pointwise, the
    sequence agrees. Both fronts share the identical `RSeq` arm (recurse into
    self, compose with `ComCont.comp`), so this is a one-layer unfold. -/
theorem transCtlSeq_rseq_congr {c₁ c₂ : LowCT}
    (h1 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₁ = translateDialectControl w c₁)
    (h2 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₂ = translateDialectControl w c₂)
    {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq c₁ c₂) = translateDialectControl vm (.RSeq c₁ c₂) := by
  simp only [transCtlSeq, translateDialectControl, h1, h2]
  rfl

/-- On the inner `RSeq phase1Loop phase2Loop` (two `RFor` leaves), `transCtlSeq`
    coincides with the canonical front. -/
theorem inner_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq phase1Loop phase2Loop)
      = translateDialectControl vm (.RSeq phase1Loop phase2Loop) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => rfl) vm

/-- **The full prover front-agreement.** `transCtlSeq` coincides with the
    canonical `translateDialectControl` on `zkSumCheckLowCT`: the outer `RSeq`
    uses the congruence with the leaf `fsInitBody` (`RCall`, agrees by the
    `transCtlSeq` wildcard) and the inner two-phase round sequence
    (`inner_front_eq`). -/
theorem zkSumCheck_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm zkSumCheckLowCT = translateDialectControl vm zkSumCheckLowCT :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner_front_eq _) vm

/-! ## 5. MAIN THEOREM — the whole-program denote homomorphism

For the Spartan sum-check prover, the descended `Com catCryptDialect` prefix
denotes exactly the kernel's `semScalar` waist — the three-phase whole-program
denote through the canonical front, banked via the control-sequencing
homomorphism `transCtlSeq_denote_seq` (which equals `translateDialectControl` on
this `RSeq`-of-leaves term by `zkSumCheck_front_eq`, so the canonical-front
translation hypothesis feeds it directly). The per-round BabyBear work (the
Horner mul-add, the Poseidon2 squeeze, the FS absorb) are opaque leaves; their
correctness is the separate byte-KAT obligation. -/

/-- **Whole-program machine denote of the Spartan sum-check prover** (fs_init `;`
    phase1 round loop `;` phase2 round loop). For any context/valuation/env
    consistent triple on which the canonical front fires and the `semScalar`
    waist succeeds, the descended dialect-`Com` prefix denotes exactly the
    prover's `semScalar` semantics (per-tail continuation). -/
theorem zkSumCheckCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm zkSumCheckLowCT = some o →
      semScalar zkSumCheckLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← zkSumCheck_front_eq vm] at htr
  exact transCtlSeq_denote_seq zkSumCheck_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. Axiom audit -/

#print axioms zkSumCheck_coveredSeq
#print axioms zkSumCheck_front_fires
#print axioms zkSumCheck_front_eq
#print axioms zkSumCheckCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckCovered
