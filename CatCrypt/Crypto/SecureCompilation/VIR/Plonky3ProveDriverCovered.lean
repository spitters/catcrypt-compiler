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
# Plonky3 `prove()` phase driver whole-program denote through the covered `RSeq`-of-control fragment

The Plonky3 `prove()` glue is a **straight-line multi-phase driver**: it sequences
the prover's phases — generate the execution trace, commit the trace, derive the
first Fiat–Shamir challenge, commit the quotient, derive the next challenge, form
the DEEP reduced opening, run FRI (fold + PoW + queries), and serialize the proof.
Its top-level control is a *sequence of phase calls* — no loops at the driver
level (the loops live one level down, inside each phase's own body):

```
trace_gen ; commit_trace ; fs_alpha ; commit_quotient ; fs_zeta ; deep_open ; fri_prove ; serialize
```

Each phase is an **opaque leaf** (`RCall`), and the phases are sequenced with
`RSeq`. This is the *simplest* shape the canonical front accepts after the
`RSeq`-of-control increment: a pure `RSeq` spine of `RCall` leaves — no `RFor`, no
`RIfNz`, just straight-line phase sequencing. `translateDialectControl` closes
under `RSeq`-sequencing of control blocks, so the whole `prove()` driver descends
through the canonical front and carries a **whole-program machine denote**.

This re-sources the driver from a high-level `LowCT` term
(`plonky3ProveDriverLowCT = RSeq traceGen (RSeq commitTrace (RSeq … serialize))`)
through the **existing covered-fragment front** — no new front — and banks the
whole-program denote homomorphism, the same recipe as
`ZkSumCheckCovered.zkSumCheckCovered_denote`,
`Shake256Covered.shake256Covered_denote`, and
`MayoSolveCovered.mayoSolveCovered_denote`. It strengthens the hand
`Plonky3ProveDriverEmit.proveDriverFundef` OrchStep schedule (a degenerate
no-loop `buildOrchCallSeq` band with no whole-program machine denote) to a
high-level-source descent.

## Opaque leaves — the per-phase work, exactly the exemplar tier

Each phase is an **opaque leaf** (`RCall`), exactly as `keccakf1600` /
`x25519_ladder_iter` are opaque in the exemplars — and exactly the owned phase
loop-drivers + field leaves the hand emit `Lcall`s: `commit_trace` is the column
LDE + Merkle leaf/compress loops (`Plonky3OrchLoopsEmit`), `fs_alpha`/`fs_zeta`
are the Poseidon2 Fiat–Shamir observe/sample leaves, `deep_open` is the degree-4
extension-field DEEP arithmetic (`ext4_*_rc`), `fri_prove` is the FRI fold/PoW/query
loop drivers, and `serialize` is the proof serializer (`p3_ser_*`). What is banked
here is the descent of the `prove()` driver's **control structure** — the ordered
phase sequence — through the canonical front, with a whole-program denote. The
per-phase field/hash/FRI arithmetic is the separate byte-KAT obligation
(`bench/plonky3_compare`), just as Keccak-f's permutation correctness is the
FIPS-202 KAT.

## The inter-phase buffer marshalling stays inside the leaves

The `prove()` driver's residual — noted in `Plonky3ProveDriverEmit` as the
Gap-2 marshalling — is the loading of each phase's pointer operands into the SysV
argument registers and the sizing of the work buffers to match p3's layout. That
is **marshalling, not control**: it is per-phase data plumbing, not a control
construct, so it is kept **inside each opaque phase leaf** (each `RCall` threads
the proof-state bundle `st` and reads the public-input bundle `pub`), exactly as
Keccak-f's 24 rounds live inside `keccakf1600` and MAYO's data-dependent inner
sweeps live inside `mayo_solve_ef_step`. It is a *byte-emit* residual (the exact
pointer/size layout), not a *control-coverage* residual, so it does not obstruct
the whole-program control descent banked here.

## What is banked

* `plonky3ProveDriverLowCT` — the driver as an `RSeq` spine of eight `RCall`
  phase leaves.
* `plonky3ProveDriver_coveredSeq : IsCoveredSCtlSeq plonky3ProveDriverLowCT` —
  the structural coverage proof (an `RSeq` spine of eight straight-line
  `RCall` leaves).
* `plonky3ProveDriver_front_fires` — the covered front fires on the whole driver
  (`native_decide`).
* `plonky3ProveDriverCovered_denote` — **the deliverable**: the whole-program
  machine denote of the `prove()` driver through the canonical front, via
  `transCtlSeq_denote_seq` and the `plonky3ProveDriver_front_eq` bridge
  (`transCtlSeq = translateDialectControl` on this `RSeq`-of-leaves term, via the
  nested `transCtlSeq_rseq_congr`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverCovered

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

/-! ## 1. The high-level source: the driver as a phase-call sequence -/

/-- Tower type of the prover state bundle (trace / commitment roots / transcript
    sponge / opening buffers). Both the proof-state bundle `st` and the
    public-input bundle `pub` are of this placeholder type; the per-phase p3
    layout is the leaves' KAT/marshalling concern, not the control descent's. -/
def bundleTy : TowerType := .TBytes 200

/-- A located slot of a state-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- One `prove()` phase as an opaque leaf: the phase `sym` reads the proof-state
    bundle `st` and the public-input bundle `pub` and writes back the updated
    state `st` (in-place). Straight-line (`IsCoveredS`). The phase's own loops and
    pointer marshalling live inside the opaque leaf. -/
def phase (sym : String) : LowCT :=
  .RCall sym (loc "st") [loc "st", loc "pub"]

/-- Phase 0 — trace generation (the Fibonacci AIR front, `fib_trace_gen_rc`). -/
def traceGen : LowCT := phase "p3_trace_gen"
/-- Phase 1 — commit the trace: column LDE + Merkle leaf/compress loops. -/
def commitTrace : LowCT := phase "p3_commit_trace"
/-- Fiat–Shamir: observe trace root, sample `alpha`. -/
def fsAlpha : LowCT := phase "p3_fs_alpha"
/-- Phase 2 — commit the quotient: LDE + Merkle. -/
def commitQuotient : LowCT := phase "p3_commit_quotient"
/-- Fiat–Shamir: observe quotient root, sample `zeta`. -/
def fsZeta : LowCT := phase "p3_fs_zeta"
/-- Phase 3 — DEEP reduced opening (degree-4 extension-field arithmetic). -/
def deepOpen : LowCT := phase "p3_deep_open"
/-- Phase 4 — FRI: fold rounds + commit each, PoW grind, queries. -/
def friProve : LowCT := phase "p3_fri_prove"
/-- Phase 5 — serialize the `Proof<SC>`. -/
def serialize : LowCT := phase "p3_serialize"

/-- **The full Plonky3 `prove()` driver as a multi-phase kernel:** the eight phases
    *sequenced* — the top-level right-nested `RSeq` spine of `RCall` leaves. This is
    the degenerate no-loop case of the `RSeq`-of-control fragment: pure straight-line
    phase sequencing, no `RFor`/`RIfNz` at the driver level. -/
def plonky3ProveDriverLowCT : LowCT :=
  .RSeq traceGen
    (.RSeq commitTrace
      (.RSeq fsAlpha
        (.RSeq commitQuotient
          (.RSeq fsZeta
            (.RSeq deepOpen
              (.RSeq friProve serialize))))))

/-! ## 2. Coverage — the central structural proofs -/

/-- Every `prove()` phase leaf is straight-line covered (`IsCoveredS`): a single
    `RCall` threading the proof-state bundle. -/
theorem phase_coveredS (sym : String) : IsCoveredS (phase sym) :=
  .rCall sym (loc "st") [loc "st", loc "pub"]

/-- **The full Plonky3 `prove()` driver is control-sequencing covered**
    (`IsCoveredSCtlSeq`): the eight phase leaves sequenced. Not expressible in
    `IsCoveredSCtl` (which has no `RSeq`-over-control) — this is the `RSeq`-of-control
    increment, here a straight-line eight-phase spine of `RCall` leaves. -/
theorem plonky3ProveDriver_coveredSeq : IsCoveredSCtlSeq plonky3ProveDriverLowCT :=
  .rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_trace_gen")))
    (.rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_commit_trace")))
      (.rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_fs_alpha")))
        (.rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_commit_quotient")))
          (.rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_fs_zeta")))
            (.rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_deep_open")))
              (.rSeq (.ofCtl (.ofStraight (phase_coveredS "p3_fri_prove")))
                (.ofCtl (.ofStraight (phase_coveredS "p3_serialize")))))))))

/-! ## 3. Concrete argument context — the front fires -/

/-- Two-argument context: the proof-state `st` and public-input `pub` bundles. -/
def driverArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `st`/`pub` to the two bundle arguments. -/
def driverArgVM : VarMap driverArgCtx where
  lookup := fun s =>
    if s = "st" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "pub" then some ⟨encodeTy bundleTy, .there .here⟩
    else none

/-- **The covered front fires on the whole Plonky3 `prove()` driver.** Each opaque
    phase leaf resolves its `st`/`pub` arguments and writes back the updated state,
    the `RSeq` spine composes the phase prefixes, and the top-level terminator
    closes. -/
theorem plonky3ProveDriver_front_fires :
    (translateDialectControlTop driverArgVM plonky3ProveDriverLowCT).isSome := by
  native_decide

/-! ## 4. `transCtlSeq` coincides with the canonical front on this term

The control-sequencing front `transCtlSeq` folds `translateDialectControl` along
the `RSeq` spine with `ComCont.comp`; the canonical `translateDialectControl` does
the *same* (its `RSeq` arm recurses into itself). On leaves (`RCall`) `transCtlSeq`
delegates to `translateDialectControl` through its wildcard. So on this pure
`RSeq`-of-`RCall`-leaves term the two fronts coincide, letting the canonical-front
translation hypothesis feed the control-sequencing homomorphism
`transCtlSeq_denote_seq` directly. -/

/-- `RSeq` congruence for the two fronts: if both children agree pointwise, the
    sequence agrees. Both fronts share the identical `RSeq` arm (recurse into self,
    compose with `ComCont.comp`), so this is a one-layer unfold. -/
theorem transCtlSeq_rseq_congr {c₁ c₂ : LowCT}
    (h1 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₁ = translateDialectControl w c₁)
    (h2 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₂ = translateDialectControl w c₂)
    {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq c₁ c₂) = translateDialectControl vm (.RSeq c₁ c₂) := by
  simp only [transCtlSeq, translateDialectControl, h1, h2]
  rfl

/-- On `RSeq friProve serialize` (two `RCall` leaves), the fronts coincide. -/
theorem inner1_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq friProve serialize)
      = translateDialectControl vm (.RSeq friProve serialize) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => rfl) vm

/-- On `RSeq deepOpen (…)`, the fronts coincide. -/
theorem inner2_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq deepOpen (.RSeq friProve serialize))
      = translateDialectControl vm (.RSeq deepOpen (.RSeq friProve serialize)) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner1_front_eq _) vm

/-- On `RSeq fsZeta (…)`, the fronts coincide. -/
theorem inner3_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize)))
      = translateDialectControl vm (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize))) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner2_front_eq _) vm

/-- On `RSeq commitQuotient (…)`, the fronts coincide. -/
theorem inner4_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq commitQuotient (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize))))
      = translateDialectControl vm
          (.RSeq commitQuotient (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize)))) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner3_front_eq _) vm

/-- On `RSeq fsAlpha (…)`, the fronts coincide. -/
theorem inner5_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm
        (.RSeq fsAlpha
          (.RSeq commitQuotient (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize)))))
      = translateDialectControl vm
          (.RSeq fsAlpha
            (.RSeq commitQuotient (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize))))) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner4_front_eq _) vm

/-- On `RSeq commitTrace (…)`, the fronts coincide. -/
theorem inner6_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm
        (.RSeq commitTrace
          (.RSeq fsAlpha
            (.RSeq commitQuotient (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize))))))
      = translateDialectControl vm
          (.RSeq commitTrace
            (.RSeq fsAlpha
              (.RSeq commitQuotient (.RSeq fsZeta (.RSeq deepOpen (.RSeq friProve serialize)))))) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner5_front_eq _) vm

/-- **The full driver front-agreement.** `transCtlSeq` coincides with the canonical
    `translateDialectControl` on `plonky3ProveDriverLowCT`: the outer `RSeq` uses the
    congruence with the leaf `traceGen` (`RCall`, agrees by the `transCtlSeq`
    wildcard) and the inner seven-phase sequence (`inner6_front_eq`). -/
theorem plonky3ProveDriver_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm plonky3ProveDriverLowCT
      = translateDialectControl vm plonky3ProveDriverLowCT :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner6_front_eq _) vm

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism

For the Plonky3 `prove()` driver, the descended `Com catCryptDialect` prefix
denotes exactly the driver's `semScalar` waist — the eight-phase whole-program
denote through the canonical front, banked via the control-sequencing homomorphism
`transCtlSeq_denote_seq` (which equals `translateDialectControl` on this
`RSeq`-of-leaves term by `plonky3ProveDriver_front_eq`, so the canonical-front
translation hypothesis feeds it directly). The per-phase work (LDE/Merkle,
Fiat–Shamir, DEEP, FRI, serialize — and each phase's own loops + pointer
marshalling) are opaque leaves; their correctness is the separate byte-KAT
obligation. -/

/-- **Whole-program machine denote of the Plonky3 `prove()` driver** (trace_gen `;`
    commit_trace `;` fs_alpha `;` commit_quotient `;` fs_zeta `;` deep_open `;`
    fri_prove `;` serialize). For any context/valuation/env consistent triple on
    which the canonical front fires and the `semScalar` waist succeeds, the
    descended dialect-`Com` prefix denotes exactly the driver's `semScalar`
    semantics (per-tail continuation). -/
theorem plonky3ProveDriverCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm plonky3ProveDriverLowCT = some o →
      semScalar plonky3ProveDriverLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← plonky3ProveDriver_front_eq vm] at htr
  exact transCtlSeq_denote_seq plonky3ProveDriver_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. Axiom audit -/

#print axioms plonky3ProveDriver_coveredSeq
#print axioms plonky3ProveDriver_front_fires
#print axioms plonky3ProveDriver_front_eq
#print axioms plonky3ProveDriverCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverCovered
