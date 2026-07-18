/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCompileRobust

/-!
# The owned-layer full-pipeline RHP: discharging the opaque `X86Prog.isCT`

This module is the **owned-fragment analogue** of the framework's general
full-pipeline RHP theorem
`LowCTRHPFull.RHP_pipeline_full_labeled`. That general theorem returns a
three-clause conjunction for a source compiled through the verified middle and
the Jasmin back-end:

* (A) `x86.isCT` — machine constant-time. But `X86Prog` is an `opaque Type` and
  `X86Prog.isCT` is an `opaque` predicate (see `JasminCompilerBridge.lean`),
  bridged to a real meaning *only* through the cited axiom
  `jasminc_preserves_ct` (Arranz-Olmos, Barthe, Blatter, Grégoire, Laporte,
  Torrini, arXiv 2511.11292).
* (B) structural leak-trace factoring — the CryptoSSA leak trace factors as
  `pre ++ body.leakTrace`.
* (C) back-translation — target contexts back-translate to source contexts with
  matching unified-trace lifts (identity at the symmetric-adversary level).

For the **owned** `LowCT → JInstr` fragment (the leaves our backend emits
itself) the leakage model is the *concrete* `blockLeak` over `JInstr`/`JState`,
and the CT keystones are *proved*, not axiom-bridged
(`OwnedCompileRobust.ownedCompile_secure_and_CT` already carries
security-preservation ∧ concrete CT together, axiom-free of
`jasminc_preserves_ct`).

This module builds the **discharge** explicitly: a single theorem mirroring the
three-clause shape of `RHP_pipeline_full_labeled`, but where clause (A)'s opaque
`X86Prog.isCT` is *replaced* by the concrete owned `blockLeak`-determined
constant-time. The whole statement is therefore axiom-free of
`jasminc_preserves_ct` — for owned leaves the concrete (A') discharges what the
general theorem can only get for clause (A) via the cited axiom.

## The three clauses, owned-fragment form

* (A') **concrete machine CT** — `blockLeak s₁ (lowerSeq ρ tgtP) = blockLeak s₂
  (lowerSeq ρ tgtP)` for all states (from `lowerSeq_constant_time`). This is the
  owned, axiom-free replacement of the opaque `x86.isCT`.
* (B') **structural leak-trace factoring** — for any direct-addressed tail
  `ctx`, the leak of the linked block factors as a state-independent prefix
  followed by the tail's own leak: `blockLeak s (lowerSeq ρ tgtP ++ ctx) = pre
  ++ blockLeak (runBlock s (lowerSeq ρ tgtP)) ctx`, with `pre` *independent of
  the initial state* (it is the constant `blockLeak` of the owned block). This
  is the concrete `blockLeak`-level analogue of clause (B)'s `pre ++
  body.leakTrace`, proved from the existing `blockLeak_append` plus the
  owned block's state-independence (`lowerSeq_constant_time`).
* (C') **security-preservation / identity back-translation** — `sdist (compiled
  tgtP) ideal ≤ ε` from `compiled_preserves_security`. The correct
  back-translation here is the *identity*, because the compiler preserves the
  full observational denotation (`progEquiv` is `SPComp`-denotation equality),
  exactly as `OwnedCompileRobust`'s docstring argues.

## Scope notes

This is the unification for the **bounded owned fragment** (straight-line
scalar-arith leaves; the whole-function variant threads identical call
structure). The discharge of `jasminc_preserves_ct` is leaf-by-leaf over the
owned fragment: the *general* un-owned backend still routes clause (A) through
the cited axiom in `RHP_pipeline_full_labeled`. This module removes the axiom
only for the owned leaves; it does not by itself remove it from the general
pipeline.

## Iris-freeness

The import closure is `OwnedCompileRobust` and its owned `X86Backend` security +
CT dependencies only. Nothing under `Bridges/` or `IrisBridge/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedRHPFull

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTCallCompose
open CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCompileRobust
open scoped ENNReal

/-! ## §1. The structural leak-trace factoring (clause (B'))

The general theorem's clause (B) states `out.cont body .leakTrace = pre ++
body.leakTrace` with `pre` independent of `body`. The concrete owned analogue:
the leak of the lowered owned block followed by any tail `ctx` factors as a
*state-independent* prefix `pre` followed by the tail's own leak. The prefix is
the constant `blockLeak` of the owned block — it is the same from any initial
state, which is exactly the owned-fragment CT fact (`lowerSeq_constant_time`).
The factoring identity itself is the existing `blockLeak_append`. -/

/-- **Structural leak-trace factoring for the owned block (clause (B')).**

    For any direct-addressed tail context `ctx` and any initial state `s`, the
    leak of the linked block factors as `pre ++ (tail leak)`, where the prefix
    `pre := blockLeak s₀ (lowerSeq ρ tgtP)` is *independent of the initial
    state* `s` (it is the same for every `s`, by `lowerSeq_constant_time`).

    This is the concrete `blockLeak` analogue of the general theorem's
    `out.cont body .leakTrace = pre ++ body.leakTrace`: a syntactic prefix,
    determined by the program text alone, followed by the tail's own behaviour.
    The factoring identity is `blockLeak_append`; the state-independence of the
    prefix is the owned-fragment CT keystone. -/
theorem owned_leakTrace_factors (ρ : RegMap) (tgtP : List ArithSrc) :
    ∃ pre : List MLeak,
      ∀ (ctx : List (JInstr 64)) (s : JState 64),
        blockLeak s (lowerSeq ρ tgtP ++ ctx) =
          pre ++ blockLeak (runBlock s (lowerSeq ρ tgtP)) ctx := by
  -- The prefix is the constant leak of the owned block from a fixed zero state.
  refine ⟨blockLeak (w := 64) { regs := fun _ => 0 } (lowerSeq ρ tgtP), ?_⟩
  intro ctx s
  rw [blockLeak_append]
  -- The realized prefix `blockLeak s (lowerSeq ρ tgtP)` equals the constant one
  -- by owned-fragment state-independence.
  rw [lowerSeq_constant_time ρ tgtP s { regs := fun _ => 0 }]

/-! ## §2. The owned-layer full-pipeline RHP (call-free)

The single theorem mirroring `RHP_pipeline_full_labeled`'s three-clause shape,
with clause (A) replaced by the concrete owned (A'). -/

/-- **Owned-layer full-pipeline RHP — the (c)-full unification.**

    For an owned source/target scalar-arith program `srcP`/`tgtP` with the
    `compile_correct` agreement `hcc : srcDenote srcP rs = srcDenote tgtP rs` and
    a source security bound `hsec`, the conjunction mirroring
    `LowCTRHPFull.RHP_pipeline_full_labeled` holds — but with clause (A)'s opaque
    `X86Prog.isCT` *replaced* by concrete owned constant-time:

    * (A') **concrete machine CT** — `blockLeak s₁ (lowerSeq ρ tgtP) = blockLeak
      s₂ (lowerSeq ρ tgtP)` for all states (`lowerSeq_constant_time`). The
      axiom-free replacement of the opaque `x86.isCT`.
    * (B') **structural leak-trace factoring** — a state-independent prefix `pre`
      such that the leak of the owned block linked with any tail factors as `pre
      ++ (tail leak)` (`owned_leakTrace_factors`).
    * (C') **security-preservation** — `sdist (compiled tgtP) ideal ≤ ε`
      (`compiled_preserves_security`). The correct back-translation is the
      identity because the compiler preserves full observational denotation.

    Every clause is about the same `tgtP` / `lowerSeq ρ tgtP`, down the same
    `LowCT → JInstr` chain. The CT clause (A') is *proved* over the concrete
    `blockLeak` model, so the whole statement is **axiom-free of**
    `jasminc_preserves_ct`.

    `(secure compilation via SCIO RrHP + deterministic-to-pure lift, bundled with
    owned-model concrete constant-time and structural leak-trace factoring)` -/
theorem ownedRHP_pipeline_full {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (srcP tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hcc : srcDenote srcP rs = srcDenote tgtP rs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
                  (fun _ : α => ideal) ≤ ε) :
    -- (A') concrete machine constant-time (replaces opaque `x86.isCT`):
    (∀ s₁ s₂ : JState 64,
      blockLeak s₁ (lowerSeq ρ tgtP) = blockLeak s₂ (lowerSeq ρ tgtP)) ∧
    -- (B') structural leak-trace factoring: a state-independent prefix:
    (∃ pre : List MLeak,
      ∀ (ctx : List (JInstr 64)) (s : JState 64),
        blockLeak s (lowerSeq ρ tgtP ++ ctx) =
          pre ++ blockLeak (runBlock s (lowerSeq ρ tgtP)) ctx) ∧
    -- (C') security-preservation (identity back-translation):
    (sdist (fun _ : α => interpSP h (itreeDenoteArith tgtP rs))
           (fun _ : α => ideal) ≤ ε) :=
  ⟨ fun s₁ s₂ => lowerSeq_constant_time ρ tgtP s₁ s₂
  , owned_leakTrace_factors ρ tgtP
  , compiled_preserves_security h srcP tgtP rs ideal hcc hsec ⟩

/-! ## §3. Relation to `RHP_pipeline_full_labeled`: the axiom discharge

The general theorem's clause (A) is `x86.isCT`, an `opaque` predicate over an
`opaque Type`, given meaning only through the cited `jasminc_preserves_ct`. The
owned theorem's clause (A') is the concrete `blockLeak`-determined CT, proved
over our own verified x86 model. This section states the relation explicitly. -/

/-- **The owned (A') discharges the opaque (A) for owned leaves.**

    For the owned fragment, machine constant-time is the *concrete*
    state-independence of `blockLeak` — provided by `lowerSeq_constant_time`,
    with no appeal to `jasminc_preserves_ct`. This is precisely the content that
    `LowCTRHPFull.RHP_pipeline_full_labeled` can supply for its clause (A) only
    by routing the opaque `X86Prog.isCT` through the cited axiom.

    Stated honestly: this removes the axiom **only for the owned leaves**. The
    general un-owned pipeline (`RHP_pipeline_full_labeled` over an arbitrary
    `X86Prog` from `Jasminc.compilesTo`) still routes clause (A) through
    `jasminc_preserves_ct`; this discharge does not by itself remove the axiom
    from that statement. -/
theorem ownedRHP_discharges_opaque_isCT (ρ : RegMap) (tgtP : List ArithSrc) :
    ∀ s₁ s₂ : JState 64,
      blockLeak s₁ (lowerSeq ρ tgtP) = blockLeak s₂ (lowerSeq ρ tgtP) :=
  fun s₁ s₂ => lowerSeq_constant_time ρ tgtP s₁ s₂

/-! ## §4. The whole-function variant (with calls)

Mirroring `ownedCompile_wholeFn_secure_and_CT` over `segScalarBlock`: the same
three-clause owned RHP for a whole function whose inter-call scalar segments are
lowered to the concatenated `JInstr` block. The constant-time and factoring
clauses are about that compiled scalar block; the security clause is about the
whole-function `interpSP` denotation, threaded through the call structure. -/

/-- **Owned-layer full-pipeline RHP — whole-function variant (with calls).**

    For a source whole function `srcSegs` and its compilation `tgtSegs` (with
    `hag : SegsAgree srcSegs tgtSegs` — identical call structure, per-segment
    `srcDenote` agreement), if the source function is `ε`-close to an `ideal`,
    the same three-clause owned RHP holds for the compiled inter-call scalar
    block `segScalarBlock ρ tgtSegs`:

    * (A') concrete machine CT of `segScalarBlock ρ tgtSegs` (from
      `allDirect_constant_time` + `segScalarBlock_allDirect`);
    * (B') structural leak-trace factoring with a state-independent prefix;
    * (C') security-preservation through the call structure
      (`wholeFn_preserves_security`).

    The `call`/`vis` boundary is framework-handled identically on both sides; the
    machine CT obligation lives on the owned straight-line scalar code. Axiom-free
    of `jasminc_preserves_ct`. -/
theorem ownedRHP_pipeline_wholeFn_full {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (srcSegs tgtSegs : List CallSeg) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hag : SegsAgree srcSegs tgtSegs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenote (segToStmts srcSegs) rs))
                  (fun _ : α => ideal) ≤ ε) :
    -- (A') concrete machine constant-time of the inter-call scalar block:
    (∀ s₁ s₂ : JState 64,
      blockLeak s₁ (segScalarBlock ρ tgtSegs) =
      blockLeak s₂ (segScalarBlock ρ tgtSegs)) ∧
    -- (B') structural leak-trace factoring with a state-independent prefix:
    (∃ pre : List MLeak,
      ∀ (ctx : List (JInstr 64)) (s : JState 64),
        blockLeak s (segScalarBlock ρ tgtSegs ++ ctx) =
          pre ++ blockLeak (runBlock s (segScalarBlock ρ tgtSegs)) ctx) ∧
    -- (C') security-preservation through the call structure:
    (sdist (fun _ : α => interpSP h (itreeDenote (segToStmts tgtSegs) rs))
           (fun _ : α => ideal) ≤ ε) := by
  have hCT : ∀ s₁ s₂ : JState 64,
      blockLeak s₁ (segScalarBlock ρ tgtSegs) =
      blockLeak s₂ (segScalarBlock ρ tgtSegs) :=
    fun s₁ s₂ =>
      allDirect_constant_time (segScalarBlock ρ tgtSegs)
        (segScalarBlock_allDirect ρ tgtSegs) s₁ s₂
  refine ⟨hCT, ?_, wholeFn_preserves_security h srcSegs tgtSegs rs ideal hag hsec⟩
  -- The prefix is the constant leak of the owned scalar block from a fixed zero state.
  refine ⟨blockLeak (w := 64) { regs := fun _ => 0 } (segScalarBlock ρ tgtSegs), ?_⟩
  intro ctx s
  rw [blockLeak_append, hCT s { regs := fun _ => 0 }]

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedRHPFull
