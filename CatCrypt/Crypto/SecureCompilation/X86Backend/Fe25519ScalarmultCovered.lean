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
public meta import CatCrypt.Crypto.Jasmin.X25519Reflect
public import CatCrypt.Crypto.Jasmin.X25519Reflect

/-!
# X25519 counted-loop whole-program denote through the covered fragment

The X25519 Montgomery-ladder scalar multiplication is a **counted loop over an
opaque leaf**: the 255-fold iteration of `x25519_ladder_iter` (RFC 7748 §5).
This file re-sources that ladder loop from a high-level `LowCT` term
(`x25519LadderLoopLowCT = RFor "i" 255 (RCall "x25519_ladder_iter" …)`) through
the **existing covered-fragment front** — no new front — and banks the
**whole-program denote homomorphism** for it: the descended
`Com catCryptDialect` prefix denotes exactly the body's `semScalar` waist
semantics, with `x25519_ladder_iter` an opaque leaf (the Poseidon2-tier leaf
model; the leaf's field-arithmetic correctness is the separate RFC 7748 §5.2
KAT obligation).

The hand-authored `UStep` schedule
(`Fe25519UnifyingFront` / `Fe25519LfundefBridge`) carries **no** machine
denote. Here the denote is the image of the verified homomorphism
`TranslateDialectScalar.translateDialectControl_denote_ctl`, applied to the
structural coverage proof `x25519LadderLoop_covered`.

## What is banked

The single counted loop (the 255-fold ladder) is banked whole via the
covered-fragment homomorphism `translateDialectControl_denote_ctl` over
`IsCoveredSCtl` (`x25519LadderLoopCovered_denote`).

The canonical front `translateDialectControl` closes under **sequencing**
control blocks with `RSeq` (its `RSeq` arm recurses into itself), so the *full*
scalarmult `RSeq (RFor ladder) (RCall encode)` — a top-level `RSeq` of an `RFor`
with subsequent work — also descends and carries a whole-program denote
(`fullScalarmultCovered_denote`, via `transCtlSeq_denote_seq` over the
control-sequencing-closed `IsCoveredSCtlSeq`, definitionally the canonical front
on this `RSeq`-of-leaves term). The inversion chain `z^(p−2)` is itself a
sequence of squaring-runs (`RFor`) interleaved with `RCall fe25519_mul`, the
same `RSeq`-of-control shape, equally coverable.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519ScalarmultCovered

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
open CatCrypt.Crypto.Jasmin.LowCTReflect (x25519LadderStateTowerType)

/-! ## 1. The high-level source: the 255-fold ladder as one counted loop -/

/-- Tower type of the 24-u64-word ladder accumulator bundle (`TBytes 192`). -/
def bundleTy : TowerType := x25519LadderStateTowerType

/-- A located slot of the ladder-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- One Montgomery-ladder step, threaded on the accumulator `acc`:
    `acc := x25519_ladder_iter(acc)`. Reuses the shape of
    `X25519Reflect.x25519LadderStepReified.body` (`RSeq RSkip (RCall …)`), but
    with `dest = arg = "acc"` so the counted loop folds the
    accumulator. Straight-line (`IsCoveredS`): `RSeq` of `RSkip` and one
    `RCall`. -/
def ladderStepBody : LowCT :=
  .RSeq .RSkip (.RCall "x25519_ladder_iter" (loc "acc") [loc "acc"])

/-- **The X25519 ladder scalarmult as one counted loop.** `RFor "i" 255` over
    the opaque per-step leaf — the 255-fold iteration that RFC 7748 §5 specifies
    as the whole Montgomery ladder. A single `RFor`, so it lives inside the
    denote-carrying covered fragment `IsCoveredSCtl`. -/
def x25519LadderLoopLowCT : LowCT :=
  .RFor "i" 255 ladderStepBody

/-! ## 2. Coverage — the structural proof

`x25519LadderLoopLowCT ∈ IsCoveredSCtl`, by the constructors: `rFor` over the
straight-line ladder step (`ofStraight` of an `IsCoveredS` `RSeq`/`RSkip`/`RCall`
tree). -/

/-- The ladder-step body is straight-line covered. -/
theorem ladderStepBody_coveredS : IsCoveredS ladderStepBody :=
  .rSeq .rSkip (.rCall "x25519_ladder_iter" (loc "acc") [loc "acc"])

/-- **The 255-fold ladder loop is Stage-2 covered** (`IsCoveredSCtl`): a bounded
    `RFor` over the straight-line ladder step. This is the key lemma —
    it feeds *both* the whole-program denote homomorphism
    (`translateDialectControl_denote_ctl`) and the operational front. -/
theorem x25519LadderLoop_covered : IsCoveredSCtl x25519LadderLoopLowCT :=
  .rFor (.ofStraight ladderStepBody_coveredS)

/-! ## 3. Concrete argument context — the front fires -/

/-- Single-argument context: the ladder bundle `acc`. -/
def ladderArgCtx : Ctx := [encodeTy bundleTy]

/-- Name resolver binding `acc` to the sole bundle argument. -/
def ladderArgVM : VarMap ladderArgCtx where
  lookup := fun s =>
    if s = "acc" then some ⟨encodeTy bundleTy, .here⟩ else none

/-- **The covered front fires on the whole 255-fold ladder loop.** The bounded
    `RFor` unrolls through `loopRForD`, threading the accumulator
    `acc` across all 255 iterations, and the top-level terminator closes. -/
theorem x25519LadderLoop_front_fires :
    (translateDialectControlTop ladderArgVM x25519LadderLoopLowCT).isSome := by
  native_decide

/-! ## 4. THE DELIVERABLE — the whole-program denote homomorphism

For the 255-fold ladder loop, the descended `Com catCryptDialect` prefix denotes
exactly the body's `semScalar` waist semantics — the Poseidon2-tier
whole-program denote, banked via the verified fragment homomorphism
`translateDialectControl_denote_ctl`. `x25519_ladder_iter` is an **opaque leaf**
(the machine denote of the counted loop is established here; the leaf's
per-step field correctness over `GF(2²⁵⁵ − 19)` is the separate RFC 7748 §5.2
KAT obligation, recorded by `X25519Reflect.X25519LeanSpecCorrect`). -/

/-- **Whole-program machine denote of the X25519 ladder scalarmult loop.** For
    any context/valuation/env consistent triple on which the covered front fires
    and the `semScalar` waist succeeds, the descended dialect-`Com` prefix
    denotes exactly the ladder loop's `semScalar` semantics (per-tail
    continuation). Direct image of the verified homomorphism at
    `x25519LadderLoopLowCT`, discharged by structural coverage. -/
theorem x25519LadderLoopCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm x25519LadderLoopLowCT = some o →
      semScalar x25519LadderLoopLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  translateDialectControl_denote_ctl x25519LadderLoop_covered

/-! ## 5. Sequencing control blocks — the full scalarmult descends

The canonical front `translateDialectControl` closes under **sequencing**
control blocks with `RSeq` (its `RSeq` arm recurses into itself rather than
delegating to the straight-line `translateDialectFull`). So the *full*
scalarmult `RSeq (RFor ladder) (RCall encode)` — a counted loop sequenced with
subsequent work — descends through the canonical front and carries a
whole-program denote (via the control-sequencing homomorphism
`transCtlSeq_denote_seq` over `IsCoveredSCtlSeq`, which is definitionally the
canonical front on this `RSeq`-of-leaves term). -/

/-- A bit-dependent ladder step inside the counted loop, written as a select:
    both step variants are computed into `t1` and `t0`, and `acc` takes `t1`
    when `bit` is nonzero and `t0` otherwise. `RFor N (RSeq … RSelect …)` is
    `IsCoveredSCtl` (`rFor` over a straight-line body). -/
example :
    IsCoveredSCtl
      (.RFor "i" 255
        (.RSeq (.RCall "x25519_cswap_dblad" (loc "t1") [loc "acc"])
          (.RSeq (.RCall "x25519_dblad" (loc "t0") [loc "acc"])
            (.RSelect (loc "acc") "bit" (loc "t0") (loc "t1"))))) :=
  .rFor
    (.ofStraight
      (.rSeq (.rCall "x25519_cswap_dblad" (loc "t1") [loc "acc"])
        (.rSeq (.rCall "x25519_dblad" (loc "t0") [loc "acc"])
          (.rSelect (loc "acc") "bit" (loc "t0") (loc "t1")))))

/-- **The full X25519 scalarmult as a multi-phase kernel:** the 255-fold ladder
    loop *sequenced* with the final `fe25519_encode` — the top-level `RSeq (RFor …) …`
    shape. -/
def fullScalarmultLowCT : LowCT :=
  .RSeq x25519LadderLoopLowCT (.RCall "fe25519_encode" (loc "out") [loc "acc"])

/-- The full scalarmult is control-sequencing covered (`IsCoveredSCtlSeq`): a
    sequence of the covered ladder loop and a straight-line encode leaf. Not
    expressible in `IsCoveredSCtl` (which has no `RSeq`-over-control). -/
theorem fullScalarmult_coveredSeq : IsCoveredSCtlSeq fullScalarmultLowCT :=
  .rSeq (.ofCtl x25519LadderLoop_covered)
    (.ofCtl (.ofStraight (.rCall "fe25519_encode" (loc "out") [loc "acc"])))

/-- **The front descends through `RSeq` over control.** The full scalarmult
    `RSeq (RFor …) …` descends through the canonical front: `RSeq` translates its
    `RFor` child with `translateDialectControl`, not `translateDialectFull`. -/
theorem fullScalarmult_sequences_control_fires :
    (translateDialectControlTop ladderArgVM fullScalarmultLowCT).isSome := by
  native_decide

/-- On the full scalarmult term (an `RSeq` of two leaf-shaped children), the
    control-sequencing front `transCtlSeq` coincides with the canonical
    `translateDialectControl`: both fold the top `RSeq` with `ComCont.comp`, and
    `transCtlSeq` delegates each leaf child (`RFor`, `RCall`) to
    `translateDialectControl`. A shallow unfold (no `loopRForD` unrolling). -/
theorem fullScalarmult_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm fullScalarmultLowCT = translateDialectControl vm fullScalarmultLowCT := by
  -- The `RFor` child reduces `transCtlSeq → translateDialectControl` in ONE step
  -- (the `transCtlSeq` wildcard), no `loopRForD` unrolling; keep it folded.
  have hchild : transCtlSeq vm x25519LadderLoopLowCT
      = translateDialectControl vm x25519LadderLoopLowCT := rfl
  simp only [fullScalarmultLowCT, transCtlSeq, translateDialectControl, hchild]
  -- Both sides are the same `RSeq` fold over the folded `RFor` translation;
  -- case-split the shared scrutinee so the two (per-def) matchers iota-reduce.
  rcases translateDialectControl vm x25519LadderLoopLowCT with _ | o₁
  · rfl
  · rcases translateDialectFull o₁.vm (.RCall "fe25519_encode" (loc "out") [loc "acc"])
      with _ | o₂ <;> rfl

/-- **Whole-program machine denote of the full X25519 scalarmult** (ladder loop
    `;` encode). The descended dialect-`Com` prefix denotes exactly the kernel's
    `semScalar` waist — the multi-phase whole-program denote through the canonical
    front, banked via the control-sequencing homomorphism `transCtlSeq_denote_seq`
    (which equals `translateDialectControl` on this `RSeq`-of-leaves term by
    `fullScalarmult_front_eq`, so the canonical-front translation hypothesis feeds
    it directly). -/
theorem fullScalarmultCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm fullScalarmultLowCT = some o →
      semScalar fullScalarmultLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← fullScalarmult_front_eq vm] at htr
  exact transCtlSeq_denote_seq fullScalarmult_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. Axiom audit -/

#print axioms x25519LadderLoopCovered_denote
#print axioms x25519LadderLoop_covered
#print axioms x25519LadderLoop_front_fires
#print axioms fullScalarmult_coveredSeq
#print axioms fullScalarmultCovered_denote

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519ScalarmultCovered
