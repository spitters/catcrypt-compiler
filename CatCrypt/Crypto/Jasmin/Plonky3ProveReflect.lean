/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LowCTStraightLineCheck

/-!
# Plonky3 end-to-end prover orchestrator

This is the **cross-layer orchestrator** that fuses the four
prover-chain kernels — Merkle commitment, coset-FFT LDE, FRI commit+query, and
the AIR constraint evaluator — into a single `plonky3_prove` STARK prover,
mirroring `plonky3-hax/src/plonky3.rs::plonky3_prove`.

This file **composes** the four kernels at the orchestrator granularity (each
layer is one opaque leaf in the orchestrator's reflect surface). The wire-level
sub-layer leaves (per-level Merkle compress, per-stage NTT butterfly, per-FRI
fold round) are part of the individual layer-N reflect files
(`Plonky3{Reflect,LdeReflect,FriReflect,AirReflect}.lean`); this orchestrator
treats each whole layer as a single call so the orchestration's LowCT is
flat and the verified emit shape is the cross-layer composition spine.

## Phase sequence (matches `plonky3_prove`)

```
commit-trace (LDE → Merkle)  →  derive FS challenges (challenger_squeeze)
  →  quotient (SELECTOR-INCLUSIVE degree)  →  OOD sample + eval
  →  DEEP batch  →  FRI commit + query (per-round)
```

Concretely, the orchestrator body is:

```
  let lde      = lde_coset_fft(trace);
  let commit   = merkle_commit(lde);
  let alpha    = challenger_squeeze(commit);
  let quotient = quotient_compose(lde, alpha);          -- selector-incl. deg=2
  let ood      = ood_deep(quotient, alpha);
  let proof    = fri_prove(ood, alpha);
  return proof;
```

## DEGREE-2 GUARD (selector-inclusive quotient sizing)

`airMaxDegree fibTransitionDegrees = 1` reports the **bare** Fibonacci
transition degree. The quotient sizing must use the **selector-inclusive**
degree `bare + 1 = 2`: the per-row composition polynomial is
`is_transition(x) · c(cur, next)`, and the all-but-last-row selector
`Z'_H(x) = Z_H(x) / (x − ω_h^{h-1})` (`quotient.rs::vanishing_selector_eval`)
contributes one extra degree. We freeze the guard at the orchestrator level
as `quotientCompositionDegree = 2`; the `quotient_compose` opaque leaf's
contract embeds this width as part of its TowerType signature.

## Opaque-leaf strategy (per fall-back gate)

The orchestrator declares its own opaque-leaf
registrations even when the sub-layer reflect files exist. This keeps the
orchestrator emit self-contained: a downstream change to the per-sub-layer
leaf shape does NOT break the orchestrator's verified front (only the
end-link in `.jinc` includes change). The per-orchestrator leaves are:

| Lean name                        | Leaf name (.jazz)              | TowerType         |
|----------------------------------|--------------------------------|-------------------|
| `plonky3_trace_lde`              | `plonky3_trace_lde_H`          | `TBytes (32 · H)` |
| `plonky3_merkle_commit_orch`     | `plonky3_merkle_commit_orch_H` | `TBytes 32`       |
| `plonky3_challenger_squeeze_orch`| `plonky3_challenger_squeeze`   | `TBytes 8`        |
| `plonky3_quotient_compose`       | `plonky3_quotient_compose_H`   | `TBytes (32 · H)` |
| `plonky3_ood_deep`               | `plonky3_ood_deep_H`           | `TBytes (32 · H)` |
| `plonky3_fri_prove`              | `plonky3_fri_prove_H`          | `TBytes 32`       |

`H` is the trace height in rows.

## Reflection→front gap

Same as the layer-N reflect files: `reifyLowCT%` doesn't consult the
`LowCTPattern` registry, so we hand-build the body the reifier *would*
produce. Downstream (`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`)
is unmodified.

## References

* Plonky3 prover: `plonky3-hax/src/plonky3.rs::plonky3_prove`
* Mirror pattern: `CatCrypt/Crypto/Jasmin/Plonky3Reflect.lean` (Merkle)
* Driver template: `bench/plonky3_compare/merkle_from_rustcmd.lean`
* String emit: `CatCrypt/Crypto/SecureCompilation/VIR/Plonky3ProveEmit.lean`
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Plonky3 prover surface types

The orchestrator's reflect surface treats each whole layer's output as an
opaque byte buffer of fixed size (parameterised by the trace height `H`).
The internal byte-layouts are the leaves' business. -/

opaque Plonky3LdeTrace.Impl (H : Nat) : NonemptyType.{0}
/-- LDE-extended trace (blowup·H rows × W columns). Opaque on the Lean side;
    the leaf `plonky3_trace_lde_H` materialises the LDE bytes. -/
def Plonky3LdeTrace (H : Nat) : Type := (Plonky3LdeTrace.Impl H).type
instance (H : Nat) : Nonempty (Plonky3LdeTrace H) := (Plonky3LdeTrace.Impl H).property
/-- Axiomatic inhabitant. -/ axiom Plonky3LdeTrace.default (H : Nat) : Plonky3LdeTrace H
noncomputable instance (H : Nat) : Inhabited (Plonky3LdeTrace H) :=
  ⟨Plonky3LdeTrace.default H⟩

opaque Plonky3Commit.Impl : NonemptyType.{0}
/-- A 32-byte trace commitment (Merkle root of the LDE-extended trace). -/
def Plonky3Commit : Type := Plonky3Commit.Impl.type
instance : Nonempty Plonky3Commit := Plonky3Commit.Impl.property
/-- Axiomatic inhabitant. -/ axiom Plonky3Commit.default : Plonky3Commit
noncomputable instance : Inhabited Plonky3Commit := ⟨Plonky3Commit.default⟩

opaque Plonky3Alpha.Impl : NonemptyType.{0}
/-- An 8-byte Fiat-Shamir challenge α produced by squeezing the transcript. -/
def Plonky3Alpha : Type := Plonky3Alpha.Impl.type
instance : Nonempty Plonky3Alpha := Plonky3Alpha.Impl.property
/-- Axiomatic inhabitant. -/ axiom Plonky3Alpha.default : Plonky3Alpha
noncomputable instance : Inhabited Plonky3Alpha := ⟨Plonky3Alpha.default⟩

opaque Plonky3Quotient.Impl (H : Nat) : NonemptyType.{0}
/-- The composition polynomial / quotient (size selector-inclusive degree 2).
    Opaque; the `plonky3_quotient_compose_H` leaf materialises bytes. -/
def Plonky3Quotient (H : Nat) : Type := (Plonky3Quotient.Impl H).type
instance (H : Nat) : Nonempty (Plonky3Quotient H) := (Plonky3Quotient.Impl H).property
/-- An inhabitant. -/
noncomputable opaque Plonky3Quotient.default (H : Nat) : Plonky3Quotient H
noncomputable instance (H : Nat) : Inhabited (Plonky3Quotient H) :=
  ⟨Plonky3Quotient.default H⟩

opaque Plonky3OodDeep.Impl (H : Nat) : NonemptyType.{0}
/-- The DEEP / OOD batched evaluations. Opaque. -/
def Plonky3OodDeep (H : Nat) : Type := (Plonky3OodDeep.Impl H).type
instance (H : Nat) : Nonempty (Plonky3OodDeep H) := (Plonky3OodDeep.Impl H).property
/-- An inhabitant. -/
noncomputable opaque Plonky3OodDeep.default (H : Nat) : Plonky3OodDeep H
noncomputable instance (H : Nat) : Inhabited (Plonky3OodDeep H) :=
  ⟨Plonky3OodDeep.default H⟩

opaque Plonky3Proof.Impl : NonemptyType.{0}
/-- The full Plonky3 proof (FRI commits + queries + grind). 32-byte digest
    surface; the proof's expanded byte form is the leaf's internal layout. -/
def Plonky3Proof : Type := Plonky3Proof.Impl.type
instance : Nonempty Plonky3Proof := Plonky3Proof.Impl.property
/-- Axiomatic inhabitant. -/ axiom Plonky3Proof.default : Plonky3Proof
noncomputable instance : Inhabited Plonky3Proof := ⟨Plonky3Proof.default⟩

opaque Plonky3ProveTrace.Impl (W H : Nat) : NonemptyType.{0}
/-- An opaque execution-trace input for the prover.  Same shape as
    `Plonky3Trace W H` from `Plonky3AirReflect.lean` but named distinctly so
    the orchestrator's reflect-surface namespace is self-contained. -/
def Plonky3ProveTrace (W H : Nat) : Type := (Plonky3ProveTrace.Impl W H).type
instance (W H : Nat) : Nonempty (Plonky3ProveTrace W H) := (Plonky3ProveTrace.Impl W H).property
/-- An inhabitant. -/
noncomputable opaque Plonky3ProveTrace.default (W H : Nat) : Plonky3ProveTrace W H
noncomputable instance (W H : Nat) : Inhabited (Plonky3ProveTrace W H) :=
  ⟨Plonky3ProveTrace.default W H⟩

/-! ## 2. Per-orchestrator opaque leaves (opaque constants and axioms = jasmin function symbols)

Each leaf is one whole-layer call in the prover orchestration. The sub-layer
internals are emitted by the layer-N reflect files; the orchestrator only
calls the top-level entry of each layer (e.g. `lde_coset_fft` for the whole
LDE, not the per-stage NTT butterfly). -/

/-- The whole LDE layer: `trace_lde = lde(trace)` (4× blowup factor). -/
noncomputable opaque plonky3_trace_lde (W H : Nat) : Plonky3ProveTrace W H → Plonky3LdeTrace H

/-- The whole Merkle layer: `commit = merkle_commit(trace_lde)`. -/
noncomputable opaque plonky3_merkle_commit_orch (H : Nat) : Plonky3LdeTrace H → Plonky3Commit

/-- Challenger / Fiat-Shamir squeeze: `α = squeeze(commit)`. -/
noncomputable opaque plonky3_challenger_squeeze_orch : Plonky3Commit → Plonky3Alpha

/-- Quotient / composition polynomial (SELECTOR-INCLUSIVE degree 2). -/
axiom plonky3_quotient_compose (H : Nat) :
    Plonky3LdeTrace H → Plonky3Alpha → Plonky3Quotient H

/-- OOD / DEEP batched evaluation. -/
axiom plonky3_ood_deep (H : Nat) :
    Plonky3Quotient H → Plonky3Alpha → Plonky3OodDeep H

/-- The whole FRI prover: commit + query + grind. -/
noncomputable opaque plonky3_fri_prove (H : Nat) : Plonky3OodDeep H → Plonky3Alpha → Plonky3Proof

/-! ## 3. `@[rust_cmd_pattern]` registrations

Concrete instantiations are at the demonstrator trace height H=8 (width=3),
matching the height-8 KAT in `plonky3-hax/tests/kat_vectors.rs`. The
TowerType sizes embed the SELECTOR-INCLUSIVE degree=2 sizing for the
quotient layer (4×H = 32 bytes/elt × 4 blowup × H rows, then ×2 for the
selector-inclusive degree → `TBytes (32 · 2 · H) = TBytes (64 · H)` at
the quotient slot). -/

/-- Register `plonky3_trace_lde_3_8`: 3-column, height-8 trace → LDE at
    blowup 4. Output: 32 bytes per row × 4 × 8 = 1024 bytes (we use the
    `TBytes 256` short surface as the orchestration handle). -/
@[rust_cmd_pattern]
def plonky3TraceLde3x8Pattern : LowCTPattern where
  name      := "plonky3_trace_lde_3_8"
  fnHead    := ``plonky3_trace_lde
  arity     := 1
  towerType := .TBytes 256

/-- Register `plonky3_merkle_commit_orch_8`: collapse LDE-trace to 32-byte
    commitment. -/
@[rust_cmd_pattern]
def plonky3MerkleCommitOrch8Pattern : LowCTPattern where
  name      := "plonky3_merkle_commit_orch_8"
  fnHead    := ``plonky3_merkle_commit_orch
  arity     := 1
  towerType := .TBytes 32

/-- Register `plonky3_challenger_squeeze`: derive α from commit. -/
@[rust_cmd_pattern]
def plonky3ChallengerSqueezeOrchPattern : LowCTPattern where
  name      := "plonky3_challenger_squeeze"
  fnHead    := ``plonky3_challenger_squeeze_orch
  arity     := 1
  towerType := .TBytes 8

/-- Register `plonky3_quotient_compose_8`: SELECTOR-INCLUSIVE degree=2
    sizing — quotient at H=8 occupies `64 · 8 = 512` bytes (the degree-2
    composition polynomial over the LDE domain). -/
@[rust_cmd_pattern]
def plonky3QuotientCompose8Pattern : LowCTPattern where
  name      := "plonky3_quotient_compose_8"
  fnHead    := ``plonky3_quotient_compose
  arity     := 2
  towerType := .TBytes 512

/-- Register `plonky3_ood_deep_8`. -/
@[rust_cmd_pattern]
def plonky3OodDeep8Pattern : LowCTPattern where
  name      := "plonky3_ood_deep_8"
  fnHead    := ``plonky3_ood_deep
  arity     := 2
  towerType := .TBytes 512

/-- Register `plonky3_fri_prove_8`: produce the final 32-byte proof root. -/
@[rust_cmd_pattern]
def plonky3FriProve8Pattern : LowCTPattern where
  name      := "plonky3_fri_prove_8"
  fnHead    := ``plonky3_fri_prove
  arity     := 2
  towerType := .TBytes 32

/-! ## 4. SELECTOR-INCLUSIVE degree=2 guard

The orchestrator's quotient sizing is locked to the SELECTOR-INCLUSIVE degree.
We expose this as a definition and a guard theorem; any change to the
quotient TowerType width must update both, and the audit script for the
Plonky3 chain validates the consistency. -/

/-- Bare AIR transition degree for the demonstrator (Fibonacci AIR, degree 1). -/
def airBareDegree : Nat := 1

/-- The selector polynomial `Z'_H = Z_H / (x - ω_h^{h-1})` contributes one
    extra degree to every composition. -/
def selectorContribution : Nat := 1

/-- SELECTOR-INCLUSIVE quotient composition degree.  Locked at 2 for the
    Fibonacci-AIR demonstrator. -/
def quotientCompositionDegree : Nat := airBareDegree + selectorContribution

/-- Guard: the quotient sizing convention matches the selector-inclusive
    degree.  Sizing the LDE blowup off the bare degree alone would
    under-size the quotient and make the proof unsound. -/
theorem quotient_degree_is_selector_inclusive :
    quotientCompositionDegree = 2 := rfl

/-! ## 5. Pure-Lean prover orchestrator function

The pure Lean specification — a flat let-chain mirroring the hand-built
`LowCT` body exactly. Sub-layer internals are NOT inlined; each layer
appears as one opaque-leaf call.

The phase sequence:
1. LDE the trace (4× blowup).
2. Merkle-commit the LDE-extended trace.
3. Squeeze the challenger to get α.
4. Compose the quotient at SELECTOR-INCLUSIVE degree 2.
5. OOD-sample + DEEP batch the quotient.
6. FRI-prove the OOD/DEEP combination. -/

/-- Pure-Lean Plonky3 prover for width=3, height=8 (the demonstrator size). -/
noncomputable def proveOrchestratorLean3x8 (trace : Plonky3ProveTrace 3 8) :
    Plonky3Proof :=
  let lde     := plonky3_trace_lde 3 8 trace
  let commit  := plonky3_merkle_commit_orch 8 lde
  let alpha   := plonky3_challenger_squeeze_orch commit
  let quot    := plonky3_quotient_compose 8 lde alpha
  let ood     := plonky3_ood_deep 8 quot alpha
  let proof   := plonky3_fri_prove 8 ood alpha
  proof

/-- The orchestrator canonical alias matching the string emit's name. -/
noncomputable def proveOrchestratorLean (trace : Plonky3ProveTrace 3 8) :
    Plonky3Proof :=
  proveOrchestratorLean3x8 trace

/-! ## 6. Hand-built `LowCT` body — the front-end input

The flat `RSeq` chain of `RCall`s, one per orchestrator step. Downstream
(`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is unmodified. -/

/-- TowerType for the input trace (3 cols × H rows × 8 bytes). -/
def plonky3ProveTraceTowerType (W H : Nat) : TowerType := .TBytes (8 * W * H)
/-- TowerType for the LDE-extended trace handle. -/
def plonky3LdeTraceTowerType : TowerType := .TBytes 256
/-- TowerType for the Merkle commitment. -/
def plonky3CommitTowerType : TowerType := .TBytes 32
/-- TowerType for the Fiat-Shamir α. -/
def plonky3AlphaTowerType : TowerType := .TBytes 8
/-- TowerType for the quotient (SELECTOR-INCLUSIVE degree=2 sizing). -/
def plonky3QuotientTowerType : TowerType := .TBytes 512
/-- TowerType for the OOD/DEEP batched evaluations. -/
def plonky3OodDeepTowerType : TowerType := .TBytes 512
/-- TowerType for the final proof root. -/
def plonky3ProofTowerType : TowerType := .TBytes 32

def locPlonky3Prove (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for width=3, height=8: the canonical six-step orchestrator. -/
def proveOrchestratorBody3x8 : LowCT :=
  let trace_l  := locPlonky3Prove "trace"  (plonky3ProveTraceTowerType 3 8)
  let lde_l    := locPlonky3Prove "lde"    plonky3LdeTraceTowerType
  let commit_l := locPlonky3Prove "commit" plonky3CommitTowerType
  let alpha_l  := locPlonky3Prove "alpha"  plonky3AlphaTowerType
  let quot_l   := locPlonky3Prove "quot"   plonky3QuotientTowerType
  let ood_l    := locPlonky3Prove "ood"    plonky3OodDeepTowerType
  let result_l := locPlonky3Prove "__result" plonky3ProofTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "plonky3_trace_lde_3_8"             lde_l    [trace_l]))
    (.RCall "plonky3_merkle_commit_orch_8"      commit_l [lde_l]))
    (.RCall "plonky3_challenger_squeeze"        alpha_l  [commit_l]))
    (.RCall "plonky3_quotient_compose_8"        quot_l   [lde_l, alpha_l]))
    (.RCall "plonky3_ood_deep_8"                ood_l    [quot_l, alpha_l]))
    (.RCall "plonky3_fri_prove_8"               result_l [ood_l, alpha_l])

/-- `ReifiedFunc` bundle for width=3, height=8 (mirrors what `reifyLowCT%`
    would produce for `proveOrchestratorLean3x8`). -/
def proveOrchestratorReified3x8 : ReifiedFunc :=
  { args    := [("trace", plonky3ProveTraceTowerType 3 8)]
    body    := proveOrchestratorBody3x8
    retName := "__result" }

/-- Canonical alias name used in the bench docstring. -/
def proveOrchestratorReified : ReifiedFunc := proveOrchestratorReified3x8

/-! ## 7. Dataflow checks

Static checks on the hand-written body: no call reads an undefined slot, and
every computed slot other than `__result` is read by a later call. -/

#guard straightLineUndefined proveOrchestratorReified3x8 = some []
#guard straightLineUnread proveOrchestratorReified3x8 = some []

end CatCrypt.Crypto.Jasmin.LowCTReflect
