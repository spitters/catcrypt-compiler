/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Framework
public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminCT

/-!
# Jasmin Compiler Bridge

Lean-side mirror of the main result of

> Arranz-Olmos, Barthe, Blatter, Grégoire, Laporte, Torrini.
> *"The Jasmin Compiler Preserves Cryptographic Security."*
> arXiv 2511.11292 (2025).

Their Coq mechanization establishes that the Jasmin compiler `jasminc`
preserves UC-style cryptographic security and constant-time leakage when
lowering a Jasmin source program to x86-64 assembly. This file states
that result as a Lean axiom and uses it to build an end-to-end transfer
theorem from CryptoSSA programs to x86-64 assembly, by composition with
the (unconditionally proved) `compiler_preserves_uc` of `Framework.lean`.

Track A3 in `BLS/NEXT.md`: "cite path" — cite the Jasmin paper's
x86 CT result in Lean without re-mechanizing x86 semantics ourselves.

## What is and isn't axiomatized

* `jasminc_preserves_uc` — axiom; the Lean statement of the Coq theorem
  proved in arXiv 2511.11292 §4.
* `jasminc_preserves_ct` — axiom; the leakage-side of the same paper.
* `cryptoSSA_to_x86_preserves_uc` — *theorem*, derived by composing
  the Lean-side `compiler_preserves_uc` with `jasminc_preserves_uc`.
  Two glue hypotheses (CryptoSSA ↔ Jasmin source denotational match,
  and "x86 program is `jasminc`'s output") are taken as parameters
  because the relevant equivalence lemma does not yet exist on the
  Lean side; see the docstring on the theorem.

The trust dependency for the axioms is on (a) the published Coq proof
and (b) `jasminc`'s implementation matching its formal model.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.SecureCompilation
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open scoped ENNReal

/-! ## Abstract types for trusted-back-end programs

We keep the Jasmin source program type concrete (the existing
`Jasmin.JasminProg` AST), but introduce an abstract Lean type for the
x86-64 target, since this codebase has no formalized x86 semantics.

The two abstract relations
`Jasminc.compilesTo  : JasminProg → X86Prog → Prop` and
`X86Prog.isCT        : X86Prog → Prop`
are exactly the proof obligations that the Coq mechanization of
arXiv 2511.11292 discharges; they are introduced here as opaque
predicates on the abstract target type. -/

/-- Abstract Lean stand-in for an x86-64 assembly program. The Coq
mechanization in arXiv 2511.11292 works with a fully formal x86 model;
we expose only its Prop-level interface here. -/
opaque X86Prog : Type

/-- "x86 program `t` is the result of running `jasminc` on Jasmin source
`s`."  Treated as opaque on the Lean side. -/
opaque Jasminc.compilesTo : JasminProg → X86Prog → Prop

/-- Abstract constant-time predicate on the x86-64 target program. The
Jasmin Coq proof exposes a corresponding leakage-equivalence predicate
on the assembly side; this is its Lean handle. -/
opaque X86Prog.isCT : X86Prog → Prop

/-! ## Abstract source/target denotational embeddings

`compiler_preserves_uc` (Framework.lean) talks about
`hon → StatefulITreeN S n E (out ⊕ leak)`. To talk about UC security
of a Jasmin or x86 *program* we need a way to view the program as such
a stateful ITree. We treat both views opaquely; on the Jasmin side,
`JasminToSSA` plus `CryptoToVIR` already give one concrete
implementation of `denoteJasmin` (modulo gluing), but the bridge does
not depend on which one.  -/

/-- Axiom-level "denote a Jasmin source program as a stateful ITree".
Parameterized over the entire UC interface (honest input, state, output,
leakage, event signature, fuel). Stated as an `axiom` rather than
`opaque` because the denotation type need not be Lean-Inhabited at
arbitrary parameters; the Lean side is interested only in the
*existence* of such a denotation as discharged by the JasminToSSA
correctness chain. -/
axiom denoteJasmin :
    ∀ {hon S out leak : Type} {E : EventSig} {n : Nat}
      (_s : JasminProg), hon → StatefulITreeN S n E (out ⊕ leak)

/-- Axiom-level "denote an x86-64 program as a stateful ITree". Same
shape as `denoteJasmin`. The whole content of arXiv 2511.11292 §4 is
that, when `Jasminc.compilesTo s t`, this denotation is sufficiently
close to `denoteJasmin s` for UC properties to transfer. -/
axiom denoteX86 :
    ∀ {hon S out leak : Type} {E : EventSig} {n : Nat}
      (_t : X86Prog), hon → StatefulITreeN S n E (out ⊕ leak)

/-! ## Axiom 1: jasminc preserves UC security -/

/--
**Jasmin compiler preserves cryptographic security.**

This axiom is the Lean-side mirror of the main theorem in the
Coq-mechanized proof:

> Arranz-Olmos, Barthe, Blatter, Grégoire, Laporte, Torrini.
> *"The Jasmin Compiler Preserves Cryptographic Security."*
> arXiv 2511.11292 (2025).

Their §4 establishes, via a relational Hoare logic on interaction-tree
semantics, that for any source-level Jasmin program `s`, target x86-64
program `t = jasminc(s)`, environment `E`, ε ≥ 0, ideal functionality
`F`, and adversary class:
   ε-UC-secure(s, E) → ε-UC-secure(t, E).

The trust dependency is on (a) the published Coq proof and (b) `jasminc`'s
implementation matching its formal model.

The Lean-side `compiler_preserves_uc` in `Framework.lean` proves the same
property at the *CryptoSSA* level by `funext`/equality of denotations;
this axiom transports it through the trusted-back-end gap to x86-64
assembly, where Lean has no native semantics. The connector below
composes the two.
-/
axiom jasminc_preserves_uc
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {hon S out leak view : Type}
    {sourceJasmin : JasminProg} {targetX86 : X86Prog}
    {F : hon → StatefulITreeN S n E (out ⊕ view)}
    {ε : ℝ≥0∞}
    (_hcompile : Jasminc.compilesTo sourceJasmin targetX86)
    (_hsec : UCEmulatesConcurrentStateful handler n ε
              (denoteJasmin (hon := hon) (S := S) (out := out) (leak := leak)
                            (E := E) (n := n) sourceJasmin) F) :
    UCEmulatesConcurrentStateful handler n ε
      (denoteX86 (hon := hon) (S := S) (out := out) (leak := leak)
                 (E := E) (n := n) targetX86) F

/-! ## Axiom 2: jasminc preserves constant-time leakage -/

/--
**Jasmin compiler preserves constant-time.**

The leakage-side of the same paper (arXiv 2511.11292): if the Jasmin
source program is constant-time according to the Lean syntactic CT
predicate `isCT_Cmd` (extended to whole programs by checking every
function body), then the emitted x86-64 program is constant-time on the
target's leakage model.

The Lean side proves syntactic CT-preservation through the
`SecureCompilation/` passes (`isCT_optimize`, etc.). This axiom carries
that property across the trusted back-end.

### Boundary of the Lean CT guarantee (read before citing this)

This axiom is **the boundary** of what the Lean development proves about
constant-time.  Everything *above* it is a Lean proof; everything
*at and below* it is trusted, imported from the cited paper:

* **Proved in Lean (syntactic, axiom-free of this axiom):**
  - `LowCTCTBridge.isCT_LowCT'_imp_jasminCTSafe` — the user-facing
    source CT predicate `isCT_LowCT'` implies the certified
    `jasminCTSafe` **unconditionally** (#235; the two predicates were
    collapsed into one agreeing fragment, so no side-condition remains);
  - `LowCTCTBridge.isCT_Cmd_of_jasminCTSafe` — `jasminCTSafe` lifts to
    the *syntactic AST whitelist* `isCT_Cmd` on the emitted Jasmin
    command;
  - `isCT_optimize` and the four per-pass lemmas — the optimizer passes
    *preserve* the `isCT_Cmd` whitelist.
  None of these is a semantic CT property: `isCT_Cmd` is a **decidable
  shape whitelist** over the AST, not a quantification over
  secret-dependent leakage traces.

* **Trusted, NOT proved in Lean (this axiom):** the step from the
  syntactic whitelist `isCT_Cmd` on every function body to **actual
  hardware / machine constant-time** of the emitted x86-64 binary.
  This is `jasminc_preserves_ct`, citing the Coq mechanization of
  arXiv 2511.11292.  The conclusion `X86Prog.isCT targetX86` is an
  **opaque, uninterpreted** predicate (see `X86Prog.isCT` above): there
  is **no x86 operational/leakage semantics in this codebase**, so its
  meaning lives entirely in the cited paper's model and in `jasminc`'s
  implementation matching that model.

The Lean development establishes *syntactic*
CT-whitelist preservation from the user-facing source predicate down to
the emitted Jasmin; the leap to hardware CT is this external axiom over
an opaque `X86Prog.isCT`, not a Lean proof. -/
axiom jasminc_preserves_ct
    {sourceJasmin : JasminProg} {targetX86 : X86Prog}
    (_hcompile : Jasminc.compilesTo sourceJasmin targetX86)
    (_hCT : ∀ fd ∈ sourceJasmin.funcs, isCT_Cmd fd.body = true) :
    X86Prog.isCT targetX86

/-! ## Connector: CryptoSSA → x86-64 -/

/--
**End-to-end UC transfer from CryptoSSA to x86-64 assembly.**

Composes two preservation results:

* `compiler_preserves_uc` (`Framework.lean`, **Qed**) — UC security at
  the CryptoSSA / ITree level transfers along any
  `CompilerCorrectStateful`-equivalence.
* `jasminc_preserves_uc` (axiom above, citing arXiv 2511.11292) —
  UC security transfers from Jasmin source to x86-64 along `jasminc`.

The hypothesis `h_cssa_jasmin` ties the two by asking that the
CryptoSSA program and the Jasmin program denote the same stateful
ITree. Producing such a witness is exactly the job of the
`JasminToSSA` correctness chain (currently in progress; see the SSA
bridge files).
Until that lemma is fully closed, `h_cssa_jasmin` is required as a
parameter; once it's discharged for the standard `JasminToSSA`
denotational embedding, this theorem becomes unconditional in the
CryptoSSA → x86 direction.

The hypothesis `h_jasmin_x86` is the *trusted* link: "x86 binary is
what `jasminc` produced". On the Coq side this is decided by
extraction; on the Lean side we treat it as an opaque fact about the
build pipeline.
-/
theorem cryptoSSA_to_x86_preserves_uc
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {hon S out leak view : Type}
    (cssa : hon → StatefulITreeN S n E (out ⊕ leak))
    (jasmin : JasminProg) (x86 : X86Prog)
    {F : hon → StatefulITreeN S n E (out ⊕ view)}
    {ε : ℝ≥0∞}
    (h_cssa_jasmin :
      CompilerCorrectStateful cssa
        (denoteJasmin (hon := hon) (S := S) (out := out) (leak := leak)
                      (E := E) (n := n) jasmin))
    (h_jasmin_x86 : Jasminc.compilesTo jasmin x86)
    (hsec : UCEmulatesConcurrentStateful handler n ε cssa F) :
    UCEmulatesConcurrentStateful handler n ε
      (denoteX86 (hon := hon) (S := S) (out := out) (leak := leak)
                 (E := E) (n := n) x86) F :=
  jasminc_preserves_uc handler (F := F) (ε := ε)
    h_jasmin_x86
    (compiler_preserves_uc handler h_cssa_jasmin hsec)

/-- **End-to-end CT transfer**: CryptoSSA program is well-typed, lowers
to a syntactically-CT Jasmin program, which `jasminc` then compiles to
a constant-time x86-64 binary. The CryptoSSA → Jasmin syntactic CT step
is provided by `JasminCT.isCT_optimize` and friends; this theorem just
threads it through the back-end axiom. -/
theorem cryptoSSA_to_x86_preserves_ct
    (jasmin : JasminProg) (x86 : X86Prog)
    (h_compile : Jasminc.compilesTo jasmin x86)
    (h_CT : ∀ fd ∈ jasmin.funcs, isCT_Cmd fd.body = true) :
    X86Prog.isCT x86 :=
  jasminc_preserves_ct h_compile h_CT

/-! ## Smoke test

Pick a tiny Jasmin program and exercise the connector end-to-end.
The facts that live outside Lean — the CryptoSSA ↔ Jasmin denotational
match, the `Jasminc.compilesTo` fact about a specific `jasminc`
invocation, and the source-side UC proof — are hypotheses of the
example, so its body is an actual application of
`cryptoSSA_to_x86_preserves_uc`. The point of the smoke test is to
check the *axiom shape*: the connector accepts these inputs and
delivers a UC statement about the x86 target.

The example mirrors `S2NBignumSSA.Simple` (a 2-instruction add/sub).
-/

namespace Smoke

/-- Trivial smoke-test Jasmin program: a single empty function body.
Real callers would use a port from `S2NBignumSSA.lean`. -/
def trivialJasmin : JasminProg :=
  { funcs := [{
      name    := { name := "smoke" },
      params  := [],
      body    := [],
      results := [] }] }

/-- Existence of *some* x86 program that `jasminc` produces from
`trivialJasmin`, plus an end-to-end UC statement about it derived
through the connector. This is a *type-level* smoke test: the facts
about the external toolchain — the x86 binary `jasminc` emits for
`trivialJasmin`, its `Jasminc.compilesTo` witness, and the
CryptoSSA-side denotational match — are hypotheses, so the body is
an application of `cryptoSSA_to_x86_preserves_uc` producing a UC
statement about the x86 target. -/
example
    {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {hon S out leak view : Type}
    (cssa : hon → StatefulITreeN S n E (out ⊕ leak))
    (F : hon → StatefulITreeN S n E (out ⊕ view))
    (ε : ℝ≥0∞)
    (hsec : UCEmulatesConcurrentStateful handler n ε cssa F)
    (x86 : X86Prog)
    (h_jasmin_x86 : Jasminc.compilesTo trivialJasmin x86)
    (h_cssa_jasmin :
      CompilerCorrectStateful cssa
        (denoteJasmin (hon := hon) (S := S) (out := out) (leak := leak)
                      (E := E) (n := n) trivialJasmin)) :
    ∃ x86 : X86Prog,
      UCEmulatesConcurrentStateful handler n ε
        (denoteX86 (hon := hon) (S := S) (out := out) (leak := leak)
                   (E := E) (n := n) x86) F :=
  ⟨x86, cryptoSSA_to_x86_preserves_uc handler cssa trivialJasmin x86
          h_cssa_jasmin h_jasmin_x86 hsec⟩

end Smoke

end CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge
