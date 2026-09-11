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
# SHAKE256 sponge whole-program denote through the covered `RSeq`-of-control fragment

The FIPS-202 SHAKE256 sponge is a **multi-phase kernel**: an absorb loop over the
input rate blocks, the `pad10*1` domain pad, and a squeeze loop over the output
rate blocks — `absorb ; pad ; squeeze`. Each phase is a counted loop (`RFor`)
over the opaque Keccak-f[1600] permutation, or a straight-line pad leaf, and the
three phases are sequenced with `RSeq`. This is exactly the shape the canonical
front now accepts after the `RSeq`-of-control increment: `translateDialectControl`
closes under `RSeq`-sequencing of control blocks, so the whole sponge descends
through the canonical front and carries a **whole-program machine denote**.

This re-sources the sponge from a high-level `LowCT` term
(`shake256LowCT = RSeq absorbLoop (RSeq padPhase squeezeLoop)`) through the
**existing covered-fragment front** — no new front — and banks the whole-program
denote homomorphism for it, the same recipe as
`Fe25519ScalarmultCovered.fullScalarmultCovered_denote`. It strengthens the hand
`Shake256SpongeFront` `SpStep` schedule (a verified-DSL step schedule with no
machine denote) to a genuine high-level-source descent.

Keccak-f[1600] is an **opaque leaf** (`RCall "keccakf1600"`) — its permutation
correctness is the separate FIPS-202 KAT obligation, exactly as `x25519_ladder_iter`
and the `fe25519` field leaves are opaque in the exemplar. The absorb rate-XOR
and the domain pad are likewise opaque leaves; what is banked here is the descent
of the sponge **control structure** (the two counted loops sequenced with the
pad) through the canonical front, with a whole-program denote.

## What is banked

* `shake256LowCT` — the sponge as `RSeq absorbLoop (RSeq padPhase squeezeLoop)`.
* `shake256_coveredSeq : IsCoveredSCtlSeq shake256LowCT` — the structural coverage
  proof (an `RSeq` of two covered `RFor` loops and a straight-line pad leaf).
* `shake256_front_fires` — the covered front fires on the whole sponge
  (`native_decide`).
* `shake256Covered_denote` — **the deliverable**: the whole-program machine
  denote of the sponge through the canonical front, via `transCtlSeq_denote_seq`
  and the `shake256_front_eq` bridge (`transCtlSeq = translateDialectControl` on
  this `RSeq`-of-leaves term).

## SHAKE256 block counts

For a fixed-length KAT input the absorb block count (`⌈inlen / rate⌉`) and the
squeeze block count (`⌈outlen / rate⌉`) are **static**, so `RFor` suffices — no
`RWhileNz` is needed. A variable-length streaming sponge (runtime `inlen` /
`outlen`) would need `RWhileNz`, the data-dependent-count arm; that is the hand
`Shake256SpongeFront`'s runtime-`N` capability and is a separate obligation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Shake256Covered

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

/-! ## 1. The high-level source: SHAKE256 as `absorb ; pad ; squeeze` -/

/-- Tower type of the 200-byte (25-lane) Keccak state bundle. -/
def bundleTy : TowerType := .TBytes 200

/-- A located slot of the state-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- Absorb block count for the KAT input (`⌈inlen / rate⌉`, static). -/
def absorbBlocks : Nat := 4

/-- Squeeze block count for the KAT output (`⌈outlen / rate⌉`, static). -/
def squeezeBlocks : Nat := 2

/-- One absorb iteration: XOR the next input rate block into the state
    (`shake256_xor_block` opaque leaf), then permute in place
    (`keccakf1600` opaque leaf). Straight-line (`IsCoveredS`): an `RSeq` of two
    `RCall`s threading the state bundle. -/
def absorbBlockBody : LowCT :=
  .RSeq (.RCall "shake256_xor_block" (loc "state") [loc "state", loc "inp"])
        (.RCall "keccakf1600" (loc "state") [loc "state"])

/-- **The absorb phase**: `RFor` over the input rate blocks — a counted loop over
    the opaque XOR-in + permute leaf. A single `RFor`, so it lives in the
    denote-carrying covered fragment `IsCoveredSCtl`. -/
def absorbLoop : LowCT :=
  .RFor "i" absorbBlocks absorbBlockBody

/-- **The pad phase**: the FIPS-202 `pad10*1` domain pad (`0x1f` suffix + `0x80`
    high bit), a straight-line opaque leaf on the state bundle. -/
def padPhase : LowCT :=
  .RCall "shake256_pad" (loc "state") [loc "state"]

/-- One squeeze iteration: permute in place (`keccakf1600` opaque leaf), then
    extract the next output rate block from the state (`shake256_extract_block`
    opaque leaf). Straight-line (`IsCoveredS`): an `RSeq` of two `RCall`s. -/
def squeezeBlockBody : LowCT :=
  .RSeq (.RCall "keccakf1600" (loc "state") [loc "state"])
        (.RCall "shake256_extract_block" (loc "out") [loc "state", loc "out"])

/-- **The squeeze phase**: `RFor` over the output rate blocks — a counted loop
    over the opaque permute + extract leaf. -/
def squeezeLoop : LowCT :=
  .RFor "k" squeezeBlocks squeezeBlockBody

/-- **The full SHAKE256 sponge as a multi-phase kernel:** the absorb loop
    *sequenced* with the pad and the squeeze loop — the top-level
    `RSeq (RFor …) (RSeq (RCall …) (RFor …))` shape. -/
def shake256LowCT : LowCT :=
  .RSeq absorbLoop (.RSeq padPhase squeezeLoop)

/-! ## 2. Coverage — the load-bearing structural proofs -/

/-- The absorb-block body is straight-line covered. -/
theorem absorbBlockBody_coveredS : IsCoveredS absorbBlockBody :=
  .rSeq (.rCall "shake256_xor_block" (loc "state") [loc "state", loc "inp"])
        (.rCall "keccakf1600" (loc "state") [loc "state"])

/-- The absorb loop is Stage-2 covered (`IsCoveredSCtl`): a bounded `RFor` over
    the straight-line absorb-block body. -/
theorem absorbLoop_covered : IsCoveredSCtl absorbLoop :=
  .rFor (.ofStraight absorbBlockBody_coveredS)

/-- The pad phase is straight-line covered. -/
theorem padPhase_coveredS : IsCoveredS padPhase :=
  .rCall "shake256_pad" (loc "state") [loc "state"]

/-- The squeeze-block body is straight-line covered. -/
theorem squeezeBlockBody_coveredS : IsCoveredS squeezeBlockBody :=
  .rSeq (.rCall "keccakf1600" (loc "state") [loc "state"])
        (.rCall "shake256_extract_block" (loc "out") [loc "state", loc "out"])

/-- The squeeze loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem squeezeLoop_covered : IsCoveredSCtl squeezeLoop :=
  .rFor (.ofStraight squeezeBlockBody_coveredS)

/-- **The full SHAKE256 sponge is control-sequencing covered** (`IsCoveredSCtlSeq`):
    the absorb loop sequenced with the pad leaf and the squeeze loop. Not
    expressible in `IsCoveredSCtl` (which has no `RSeq`-over-control) — this is
    exactly the `RSeq`-of-control increment. -/
theorem shake256_coveredSeq : IsCoveredSCtlSeq shake256LowCT :=
  .rSeq (.ofCtl absorbLoop_covered)
    (.rSeq (.ofCtl (.ofStraight padPhase_coveredS)) (.ofCtl squeezeLoop_covered))

/-! ## 3. Concrete argument context — the front fires -/

/-- Three-argument context: the state, input, and output bundles. -/
def spongeArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `state`/`inp`/`out` to the three bundle arguments. -/
def spongeArgVM : VarMap spongeArgCtx where
  lookup := fun s =>
    if s = "state" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "inp" then some ⟨encodeTy bundleTy, .there .here⟩
    else if s = "out" then some ⟨encodeTy bundleTy, .there (.there .here)⟩
    else none

/-- **The covered front fires on the whole SHAKE256 sponge.** The two bounded
    `RFor` loops unroll `CProg`-free through `loopRForD`, the pad leaf and permute
    leaves resolve their state/input/output arguments, the `RSeq` spine composes
    the phase prefixes, and the top-level terminator closes. -/
theorem shake256_front_fires :
    (translateDialectControlTop spongeArgVM shake256LowCT).isSome := by
  native_decide

/-! ## 4. `transCtlSeq` coincides with the canonical front on this term

The control-sequencing front `transCtlSeq` folds `translateDialectControl` along
the `RSeq` spine with `ComCont.comp`; the canonical `translateDialectControl` now
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

/-- On the inner `RSeq padPhase squeezeLoop` (two leaves — an `RCall` and an
    `RFor`), `transCtlSeq` coincides with the canonical front. -/
theorem inner_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq padPhase squeezeLoop)
      = translateDialectControl vm (.RSeq padPhase squeezeLoop) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => rfl) vm

/-- **The full sponge front-agreement.** `transCtlSeq` coincides with the
    canonical `translateDialectControl` on `shake256LowCT`: the outer `RSeq` uses
    the congruence with the leaf `absorbLoop` (`RFor`, agrees by the `transCtlSeq`
    wildcard) and the inner sequence (`inner_front_eq`). -/
theorem shake256_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm shake256LowCT = translateDialectControl vm shake256LowCT :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner_front_eq _) vm

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism

For the SHAKE256 sponge, the descended `Com catCryptDialect` prefix denotes
exactly the kernel's `semScalar` waist — the multi-phase whole-program denote
through the canonical front, banked via the control-sequencing homomorphism
`transCtlSeq_denote_seq` (which equals `translateDialectControl` on this
`RSeq`-of-leaves term by `shake256_front_eq`, so the canonical-front translation
hypothesis feeds it directly). Keccak-f[1600] (and the absorb-XOR / pad / extract)
are opaque leaves; their FIPS-202 correctness is the separate KAT obligation. -/

/-- **Whole-program machine denote of the SHAKE256 sponge** (absorb loop `;` pad
    `;` squeeze loop). For any context/valuation/env consistent triple on which
    the canonical front fires and the `semScalar` waist succeeds, the descended
    dialect-`Com` prefix denotes exactly the sponge's `semScalar` semantics
    (per-tail continuation). -/
theorem shake256Covered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm shake256LowCT = some o →
      semScalar shake256LowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← shake256_front_eq vm] at htr
  exact transCtlSeq_denote_seq shake256_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. Axiom audit -/

#print axioms shake256_coveredSeq
#print axioms shake256_front_fires
#print axioms shake256_front_eq
#print axioms shake256Covered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.Shake256Covered
