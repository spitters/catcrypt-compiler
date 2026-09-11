/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond

/-!
# Robust safety preservation for the lattice → Jasmin lowering (RSP/RHP)

This file builds the first **robust-compilation** artifact on the VIR `Com`
substrate, in the Robust-Safety-Preservation (RSP) / Robust-Hyperproperty
style of Abate, Blanco, Garg, Hriţcu, Patrignani, Thibault,
*"Journey Beyond Full Abstraction: Exploring Robust Property Preservation for
Secure Compilation"* (CSF 2019). The RSP criterion there reads:

> A compiler robustly preserves a class of (hyper)properties iff, for every
> source program `P` that satisfies the property *against all source linking
> contexts*, the compiled program `P↓` satisfies the property *against all
> target linking contexts*.

The point is that the quantification is over **adversarial contexts**: the
property is not just satisfied by the closed program, but by the program
linked with *any* environment an attacker may supply. Preservation transports
this whole-program-against-all-contexts guarantee from source to target.

## The substrate and the convergence payoff

On CatCrypt's ANF `Com` substrate (`VIR/Core.lean`) the lattice optimizer runs
on `Com latticeDialect` and the backend printer consumes `Com jasminDialect`;
the bridge is `lowerLatticeToJasmin` (`VIR/LatticeToJasmin.lean`). Proving robust
safety preservation **once on `Com`** is exactly the convergence payoff: every
backend hanging off the shared `Com` inherits it.

## The safety property: constant-time (leakage non-interference)

The trace property the program robustly satisfies is **constant-time** — the
program performs no variable-time memory access, so its leakage trace carries
no secret-derived data. `JasminCTPredicate.ctSafeJasmin` (B2a) is the syntactic
enforcer of this: it flags `stackLoad` / `stackStore` whose *index* is labelled
`.Secret`. CT is a safety property in the RSP sense (a violation is witnessed by
a finite trace prefix: the first secret-indexed access).

## The context / linking model

A **linking context** for a Jasmin program `c : Com jasminDialect Γ t` is, in
this first artifact, an adversarial *classification* of the program's free
inputs: a `LabelCtxt Γ` choosing which inputs the attacker treats as secret.
(The denotational half — the actual input `Ctxt.Valuation` the context feeds in,
and the value/leakage it observes — is handled by A3,
`lowerLatticeToJasmin_denote_eq_uncond`; see §4.) This is the simplest faithful
context model: the attacker picks the secrecy labelling, and CT must hold for
*that* choice. Robust satisfaction quantifies over **all** such choices.

## What is proved here

1. `RobustlyCTSafe c` — `c` is CT-safe under *every* label context (RSP-style
   robust satisfaction of the CT safety property).
2. `lowerLatticeToJasmin_robustlyCTSafe` — the lowered program is robustly
   CT-safe, for *every* source lattice `Com`. This is the headline robust-safety
   artifact; its proof is exactly the `∀ L` repackaging of B2a
   (`lowerLatticeToJasmin_ctSafeJasmin`).
3. `RobustlyCTSafeSource` + `latticeSource_robustlyCTSafe` — the source side is
   *vacuously* robustly CT-safe: the lattice dialect has no addressed memory
   access, so there is no secret-indexed access for any context to exploit.
4. `robustCTPreservation` — the genuine RSP shape:
   `(robust source CT) → (robust target CT)`, with `lowerLatticeToJasmin` as the
   compiler. Combined with (3), the source hypothesis discharges unconditionally,
   so the conclusion holds for every source program (`robustCTPreservation_uncond`).
5. `lowerLatticeToJasmin_robust_correctness` — a leakage-non-interference reading
   via A3: a context that fixes the input valuation observes the *same* result
   value through the lowering, so the observable behaviour the attacker links
   against is preserved exactly.

## What a fuller RSP would still add

A complete RSP (à la Abate et al.) additionally requires a *back-translation*: a
map from arbitrary **target** contexts to source contexts establishing that no
target attacker has more power than some source attacker. Here the context model
is the secrecy labelling, which is shared across the two dialects via `tau`
(`LatticeTy → JasminTy`), so the back-translation is the identity on labels and
the implication in (4) is direct. A richer context model — a `Com`-with-a-hole
that supplies *and consumes* variables, with the attacker observing a full
leakage trace — would need a genuine back-translation of target program
fragments to source ones. That is deliberately out of scope for this first
artifact; the present statements are honest about quantifying over the
secrecy-labelling context only.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Robust satisfaction of the constant-time safety property

The attacker's linking context is the secrecy labelling `LabelCtxt Γ`. A program
**robustly** satisfies CT iff it is CT-safe against *every* such labelling — i.e.
no matter how the attacker classifies the free inputs as public or secret, the
program never performs a secret-indexed memory access. -/

/-- **Robust CT-safety (target / Jasmin).** A Jasmin program is robustly
    constant-time iff it is `ctSafeJasmin` under *every* label context. This is
    the RSP-style "satisfies CT against all (secrecy-labelling) linking
    contexts" judgement. -/
def RobustlyCTSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Prop :=
  ∀ L : LabelCtxt Γ, ctSafeJasmin c L = true

/-- A robustly CT-safe program is, in particular, CT-safe under any *given*
    context — the elimination form. -/
theorem RobustlyCTSafe.atContext {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t} (h : RobustlyCTSafe c) (L : LabelCtxt Γ) :
    ctSafeJasmin c L = true := h L

/-! ## 2. Headline: the lowering's output is robustly CT-safe

B2a (`lowerLatticeToJasmin_ctSafeJasmin`) proves CT-safety under *any* label
context. Robust satisfaction is exactly the universal closure of that statement,
so the headline robust-safety artifact is a direct repackaging. -/

/-- **Robust safety, by construction.** For *every* source lattice program `c`,
    the lowered Jasmin program is robustly constant-time: it satisfies CT against
    every (secrecy-labelling) linking context an attacker may supply. The lattice
    dialect has no data-dependent addressing — every op is whole-poly — so the
    lowering emits no `stackLoad` / `stackStore`, and there is nothing for any
    context to exploit. The proof is the `∀ L` closure of B2a. -/
theorem lowerLatticeToJasmin_robustlyCTSafe
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafe (lowerLatticeToJasmin c) :=
  fun L => lowerLatticeToJasmin_ctSafeJasmin c L

/-- Concrete corollary: the lowered NTT-expanded target program (`ntt a; ntt b;
    basemul; invntt`) is robustly constant-time at ML-KEM-flavoured parameters. -/
theorem tgt_robustlyCTSafe (q n : Nat) :
    RobustlyCTSafe (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) :=
  lowerLatticeToJasmin_robustlyCTSafe (LatticeDialect.tgtCom q n)

/-- Concrete corollary: the lowered unexpanded source program (`poly_mul`) is
    robustly constant-time. -/
theorem src_robustlyCTSafe (q n : Nat) :
    RobustlyCTSafe (lowerLatticeToJasmin (LatticeDialect.srcCom q n)) :=
  lowerLatticeToJasmin_robustlyCTSafe (LatticeDialect.srcCom q n)

/-! ## 3. The source side is vacuously robustly CT-safe

For the genuine RSP shape we also need a *source*-level robust-CT judgement. The
lattice dialect has no addressed memory op at all (every op is whole-poly), so
the only meaningful source-level CT property is "the program lowers to something
robustly CT-safe" — which holds for *every* lattice program. We phrase the
source robust judgement directly through the lowering so that the secrecy-label
context (a `LabelCtxt (Γ.map tau)`, shared across dialects via `tau`) is the
common notion of attacker context on both sides. -/

/-- **Robust CT-safety (source / lattice).** A lattice program robustly satisfies
    CT iff, against every (`tau`-transported) secrecy-labelling context, its
    image under the lowering is CT-safe. This is the source-side reading of the
    *same* trace property: the lattice dialect has no addressed access, so the
    property is about the program's observable (post-lowering) memory behaviour.
    It holds vacuously for every lattice program — see
    `latticeSource_robustlyCTSafe`. -/
def RobustlyCTSafeSource {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t) : Prop :=
  ∀ L : LabelCtxt (Γ.map tau), ctSafeJasmin (lowerLatticeToJasmin c) L = true

/-- **Source robust safety (vacuous).** Every lattice program robustly satisfies
    CT: the dialect has no data-dependent addressing, so no secret-indexed access
    exists for any context to exploit. -/
theorem latticeSource_robustlyCTSafe
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafeSource c :=
  fun L => lowerLatticeToJasmin_ctSafeJasmin c L

/-! ## 4. The RSP-shaped preservation theorem

The genuine RSP shape: *if the source robustly satisfies CT (against all source
contexts), then the target robustly satisfies CT (against all target contexts)*,
with `lowerLatticeToJasmin` as the compiler. Because the context model is the
secrecy labelling — shared across the two dialects via `tau` — the
back-translation of target contexts to source contexts is the identity on
labels, so the implication holds directly. -/

/-- **Robust safety preservation (RSP shape).** If a source lattice program
    robustly satisfies constant-time against all source (secrecy-labelling)
    contexts, then its compilation robustly satisfies constant-time against all
    target contexts. The compiler is `lowerLatticeToJasmin`; the context model is
    the secrecy labelling, identified across dialects by `tau`. -/
theorem robustCTPreservation
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hSrc : RobustlyCTSafeSource c) :
    RobustlyCTSafe (lowerLatticeToJasmin c) :=
  -- The target contexts (`LabelCtxt (Γ.map tau)`) coincide with the source
  -- contexts of `RobustlyCTSafeSource`, so the hypothesis applies directly.
  fun L => hSrc L

/-- **Robust safety preservation (unconditional).** Combining the RSP shape with
    the vacuous discharge of its source hypothesis (`latticeSource_robustlyCTSafe`):
    *every* compiled lattice program robustly satisfies constant-time. This is the
    end-to-end robust-compilation guarantee for the lattice → Jasmin path. -/
theorem robustCTPreservation_uncond
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafe (lowerLatticeToJasmin c) :=
  robustCTPreservation c (latticeSource_robustlyCTSafe c)

/-! ## 5. Robust correctness: the linked observable behaviour is preserved

CT is a non-interference *safety* property; for it to be meaningful the compiler
must also preserve the program's observable behaviour, so that the attacker links
against the same function in source and target. A3
(`lowerLatticeToJasmin_denote_eq_uncond`) gives exactly this: a context that
fixes an input valuation `V` observes, through the lowering, the `tau`-transport
of the source result — no semantic drift the attacker could distinguish. Together
with §4 this is the "secure compilation" pairing: robust CT-safety *and*
behaviour preservation. -/

/-- **Robust correctness (behaviour preservation under linking).** For every
    source lattice program and every input valuation a context may supply, the
    lowered program denotes to the `tau`-transport of the source denotation. Thus
    the observable behaviour the attacker links against is preserved exactly. This
    is the A3 result, framed as the behavioural half of the secure-compilation
    pairing. -/
theorem lowerLatticeToJasmin_robust_correctness
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (V : Ctxt.Valuation Γ) :
    (lowerLatticeToJasmin c).denote (mapVal V) = transTy (c.denote V) :=
  lowerLatticeToJasmin_denote_eq_uncond c V

/-! ## 6. The two halves packaged: secure compilation of the lattice path

The combined statement: for every source lattice program, the lowering is both
robustly constant-time (against all secrecy-labelling contexts) *and*
behaviour-preserving (against all input-supplying contexts). This is the
single-`Com` secure-compilation artifact the convergence buys us. -/

/-- **Secure compilation (combined).** The lattice → Jasmin lowering is, for every
    source program, simultaneously robustly constant-time and
    behaviour-preserving. The first conjunct is the RSP robust-safety guarantee
    (`robustCTPreservation_uncond`, ultimately B2a); the second is robust
    correctness (`lowerLatticeToJasmin_robust_correctness`, A3). -/
theorem lowerLatticeToJasmin_secure_compilation
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafe (lowerLatticeToJasmin c)
      ∧ (∀ V : Ctxt.Valuation Γ,
          (lowerLatticeToJasmin c).denote (mapVal V) = transTy (c.denote V)) :=
  ⟨robustCTPreservation_uncond c,
   fun V => lowerLatticeToJasmin_robust_correctness c V⟩

/-! ## 7. Smoke: robust CT is non-vacuous as a predicate

`RobustlyCTSafe` is genuinely restrictive: a hand-built program with a
`stackLoad` is *not* robustly CT-safe, because the attacker can choose the
context labelling its index `.Secret`. (Compare `JasminCTPredicate`'s
`loadProg_secret_not_ctSafe`.) This confirms the robust judgement is not
vacuously true on all programs — the lattice path satisfies it by *construction*,
not by triviality of the predicate. -/

/-- The single-`stackLoad` program of `JasminCTPredicate` is **not** robustly
    CT-safe: the secret-index labelling is a valid attacker context that breaks
    CT. Witness via `JasminCTPredicate.secretIdxLabels`. -/
theorem loadProg_not_robustlyCTSafe :
    ¬ RobustlyCTSafe JasminCTPredicate.loadProg := by
  intro h
  have hbad := h JasminCTPredicate.secretIdxLabels
  rw [JasminCTPredicate.loadProg_secret_not_ctSafe] at hbad
  exact Bool.noConfusion hbad

end CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
