/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedRHPFull
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnifiedMem
import CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge

/-!
# U4: the CT-provenance adapter for machine constant-time

This module is the **U4 adapter**. It unifies the
three distinct ways the constant-time property of a machine artifact can be
established, and makes the *provenance* of each — and hence the trust set it
pulls in — first-class and inspectable.

## The three CT-provenance routes

A machine artifact's constant-time can be established in three ways, which carry
genuinely different evidence over genuinely different artifact types:

* **owned emit (U2).** The leaf is emitted by our own verified `LowCT → JInstr`
  backend. Its CT is the *concrete* `blockLeak` state-independence over
  `List (JInstr 64)`, **proved** (e.g. `lowerSeq_constant_time`,
  `LowCTUnifiedMem.bignumKernel_constant_time`). Axiom-free of
  `jasminc_preserves_ct`.
* **TV-validated (U1).** The leaf is `jasminc`'s output, *decoded* back to a
  `List (JInstr 64)` and **validated** by the U1 translation-validation CT
  checker. The CT evidence has the *same shape* as the owned route
  (`blockLeak` state-independence); U1's `isCTChecked_sound` supplies it. The
  constructor's tag records the provenance as "validated, not trusted". Also
  axiom-free of `jasminc_preserves_ct`.
* **cited axiom.** The leaf is an un-owned, undecoded back-end artifact — an
  opaque `X86Prog` for which Lean has no operational semantics. Its CT is
  `X86Prog.isCT x`, given meaning *only* through the cited axiom
  `jasminc_preserves_ct` (Arranz-Olmos, Barthe, Blatter, Grégoire, Laporte,
  Torrini, arXiv 2511.11292). This is the **only** route that keeps the axiom
  in the trust set.

## The honest difficulty, and the adapter shape

The owned/TV CT is `blockLeak` state-independence over a *concrete*
`List (JInstr 64)`; the cited route is `X86Prog.isCT` over an *opaque, different*
type with no Lean semantics. There is no common artifact type, so the
unification is necessarily a **sum** over the artifact together with its CT
evidence (`MachineCTWitness`), equipped with a uniform `isCT` projection and a
first-class `provenanceTag`.

The key payoff (`§3`) is that **the provenance tag exactly predicts the trust
set**: projecting `isCT` from an `ownedConcrete` or `tvValidated` witness is
axiom-free of `jasminc_preserves_ct`; only `citedAxiom` pulls the axiom in.
This is demonstrated, not merely asserted, by the `#print axioms`-checkable
lemmas in `§3` (use `lean_verify` / `#print axioms`).

## Relation to `RHP_pipeline_full_labeled`

This file **does not modify** `LowCTRHPFull.RHP_pipeline_full_labeled`. That
general theorem's clause (A) is `x86.isCT` over the opaque `X86Prog`, bridged by
the cited axiom; refactoring it to consume this provenance abstraction (so that
its clause (A) is axiom-free precisely when every leaf is `ownedConcrete` /
`tvValidated`) is a later, separate step. This module provides the abstraction
that refactor would consume. Each leaf the self-emission work flips to owned
emit becomes an `ownedConcrete` witness here — a free axiom-discharge once
wired. The TV route (`tvValidated`) consumes U1's decoded-output CT checker.

## Iris-freeness

The import closure is `OwnedRHPFull` (owned `X86Backend` security + CT),
`LowCTUnifiedMem` (the worked owned kernel), and `JasminCompilerBridge` (the
opaque `X86Prog` + cited axiom). Nothing under `Bridges/` or `IrisBridge/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedRHPProvenance

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnifiedMem
open CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge

/-! ## §1. The provenance tag

A small enum naming the three CT-provenance routes. It is the first-class,
inspectable record of *how* a witness establishes constant-time — and therefore
of which trust set it pulls in. -/

/-- The provenance of a `MachineCTWitness`'s constant-time evidence. The tag is
    inspectable (`provenanceTag` below) and exactly predicts the trust set:
    `owned` and `tvValidated` are axiom-free of `jasminc_preserves_ct`; only
    `citedAxiom` keeps that axiom in the trust set. -/
inductive CTProvenance where
  /-- Owned emit: concrete `blockLeak` CT proved by our verified backend (U2). -/
  | owned
  /-- `jasminc` output decoded + validated by the U1 CT checker. -/
  | tvValidated
  /-- Un-owned opaque back-end artifact; CT via the cited axiom. -/
  | citedAxiom
  deriving DecidableEq, Repr

/-! ## §2. The CT-provenance witness

A sum over the machine artifact together with its CT evidence. The owned and
TV routes carry a concrete `List (JInstr 64)` and `blockLeak` state-independence
evidence; the cited route carries an opaque `X86Prog` and `X86Prog.isCT`. -/

/-- **The CT-provenance witness.** One of three constructors, each carrying the
    machine artifact together with its constant-time evidence:

    * `ownedConcrete b h` — owned emit: the concrete block `b : List (JInstr 64)`
      with proved `blockLeak` state-independence `h` (U2);
    * `tvValidated b h` — decoded `jasminc` output: the same evidence type, with
      the tag recording provenance = "validated by the U1 checker, not trusted"
      (U1's `isCTChecked_sound` supplies `h`);
    * `citedAxiom x h` — un-owned opaque back-end artifact `x : X86Prog` with
      `h : X86Prog.isCT x`, the predicate given meaning only through the cited
      `jasminc_preserves_ct` axiom. -/
inductive MachineCTWitness where
  /-- Owned emit, concrete CT proved (U2). -/
  | ownedConcrete (b : List (JInstr 64))
      (h : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b)
  /-- Decoded `jasminc` output, CT validated by the U1 checker (same evidence
      type; the tag records provenance = "validated, not trusted"). -/
  | tvValidated (b : List (JInstr 64))
      (h : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b)
  /-- Un-owned back-end artifact, CT via the cited `jasminc_preserves_ct`. -/
  | citedAxiom (x : X86Prog) (h : X86Prog.isCT x)

/-- **The provenance tag** of a witness: which of the three routes established its
    constant-time. First-class and inspectable; `§3` shows it exactly predicts
    the trust set. -/
def MachineCTWitness.provenanceTag : MachineCTWitness → CTProvenance
  | .ownedConcrete _ _ => .owned
  | .tvValidated _ _   => .tvValidated
  | .citedAxiom _ _    => .citedAxiom

/-- **The uniform `isCT` projection.** The constant-time fact carried by the
    witness, projected from whichever constructor: a concrete `blockLeak`
    state-independence statement for the owned and TV routes, and the opaque
    `X86Prog.isCT x` for the cited route. -/
def MachineCTWitness.isCT : MachineCTWitness → Prop
  | .ownedConcrete b _ => ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b
  | .tvValidated b _   => ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b
  | .citedAxiom x _    => X86Prog.isCT x

/-- The `isCT` projection is exactly the evidence the constructor carries: an
    owned/TV witness's `isCT` is discharged by its own `h` field. -/
theorem MachineCTWitness.ownedConcrete_isCT (b : List (JInstr 64))
    (h : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b) :
    (MachineCTWitness.ownedConcrete b h).isCT :=
  h

theorem MachineCTWitness.tvValidated_isCT (b : List (JInstr 64))
    (h : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b) :
    (MachineCTWitness.tvValidated b h).isCT :=
  h

theorem MachineCTWitness.citedAxiom_isCT (x : X86Prog) (h : X86Prog.isCT x) :
    (MachineCTWitness.citedAxiom x h).isCT :=
  h

/-! ## §3. Axiom-freeness: the tag predicts the trust set

The entire point of the adapter. Constructing a witness via `ownedConcrete` or
`tvValidated` and projecting `isCT` does **not** depend on
`jasminc_preserves_ct`; only the `citedAxiom` route does. The lemmas below are
the `#print axioms`-checkable demonstrations (use `lean_verify` /
`#print axioms`): `ownedConcrete_axiomFree` and `tvValidated_axiomFree` build a
witness from a concrete owned/decoded block and project its `isCT`, and their
axiom set contains no `jasminc_preserves_ct`. -/

/-- **Owned route is axiom-free of `jasminc_preserves_ct`.** Building an
    `ownedConcrete` witness from a concrete block with proved `blockLeak`
    state-independence and projecting `isCT` depends only on the supplied proof
    `h` — not on the cited axiom. `#print axioms` on this lemma shows
    `jasminc_preserves_ct` absent. -/
theorem ownedConcrete_axiomFree (b : List (JInstr 64))
    (h : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b) :
    (MachineCTWitness.ownedConcrete b h).isCT ∧
      (MachineCTWitness.ownedConcrete b h).provenanceTag = CTProvenance.owned :=
  ⟨h, rfl⟩

/-- **TV-validated route is axiom-free of `jasminc_preserves_ct`.** The decoded
    `jasminc` output carries the same `blockLeak` evidence type (supplied by
    U1's `isCTChecked_sound`); projecting `isCT` does not touch the cited axiom.
    The tag records the provenance as "validated by the checker, not trusted".
    `#print axioms` shows `jasminc_preserves_ct` absent. -/
theorem tvValidated_axiomFree (b : List (JInstr 64))
    (h : ∀ s₁ s₂ : JState 64, blockLeak s₁ b = blockLeak s₂ b) :
    (MachineCTWitness.tvValidated b h).isCT ∧
      (MachineCTWitness.tvValidated b h).provenanceTag = CTProvenance.tvValidated :=
  ⟨h, rfl⟩

/-- **The cited route — and only it — keeps the axiom in the trust set.** The
    `citedAxiom` constructor's CT evidence is `X86Prog.isCT x`, which is given
    meaning only through `jasminc_preserves_ct`; supplying it from
    `jasminc_preserves_ct` (as the general pipeline does) pulls that axiom into
    the trust set. This lemma exhibits the construction whose axiom set *does*
    contain `jasminc_preserves_ct`, contrasting with the two owned/TV lemmas
    above whose axiom sets do not. -/
theorem citedAxiom_pullsAxiom
    {sourceJasmin : Jasmin.JasminProg} {targetX86 : X86Prog}
    (hcompile : Jasminc.compilesTo sourceJasmin targetX86)
    (hCT : ∀ fd ∈ sourceJasmin.funcs, Jasmin.isCT_Cmd fd.body = true) :
    (MachineCTWitness.citedAxiom targetX86
        (jasminc_preserves_ct hcompile hCT)).isCT ∧
      (MachineCTWitness.citedAxiom targetX86
          (jasminc_preserves_ct hcompile hCT)).provenanceTag
        = CTProvenance.citedAxiom :=
  ⟨jasminc_preserves_ct hcompile hCT, rfl⟩

/-! ## §4. A worked owned discharge — the U2 piggyback point

We wire a **real** owned kernel into `ownedConcrete`. The witness must carry an
*unconditional* `∀ s₁ s₂` `blockLeak` state-independence, so we use the
straight-line scalar block `lowerSeq ρ ps`, whose CT
(`lowerSeq_constant_time`) is unconditional — as opposed to
`LowCTUnifiedMem.bignumKernel_constant_time`, which is conditioned on
`agreePub bmPub s₁ s₂` (a memory-indexed kernel's CT holds only across states
agreeing on the public frame registers, so it is not an unconditional
`∀ s₁ s₂` witness). The unconditional `lowerSeq` route gives the clean witness
the `ownedConcrete` constructor wants.

Each owned leaf the self-emission work flips to owned emit becomes such a
witness — a free axiom-discharge once wired here. -/

/-- **A worked owned-kernel CT witness (the U2 piggyback).** The straight-line
    scalar-arith owned block `lowerSeq ρ ps` wired into `ownedConcrete` via its
    *unconditional* CT keystone `lowerSeq_constant_time`. Projecting its `isCT`
    is axiom-free of `jasminc_preserves_ct` (see `ownedKernelCTWitness_axiomFree`
    and verify with `#print axioms`). -/
def ownedKernelCTWitness (ρ : RegMap) (ps : List ArithSrc) : MachineCTWitness :=
  MachineCTWitness.ownedConcrete (lowerSeq ρ ps)
    (fun s₁ s₂ => lowerSeq_constant_time ρ ps s₁ s₂)

/-- The worked owned-kernel witness carries the `owned` provenance tag. -/
theorem ownedKernelCTWitness_tag (ρ : RegMap) (ps : List ArithSrc) :
    (ownedKernelCTWitness ρ ps).provenanceTag = CTProvenance.owned := rfl

/-- **The worked owned-kernel witness's `isCT` is the concrete block CT,
    axiom-free of `jasminc_preserves_ct`.** Its proof term is exactly
    `lowerSeq_constant_time`; `#print axioms` on this lemma shows no
    `jasminc_preserves_ct`. This is the U2 discharge: the owned leaf supplies
    machine CT with no appeal to the cited axiom. -/
theorem ownedKernelCTWitness_axiomFree (ρ : RegMap) (ps : List ArithSrc) :
    (ownedKernelCTWitness ρ ps).isCT :=
  fun s₁ s₂ => lowerSeq_constant_time ρ ps s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedRHPProvenance
