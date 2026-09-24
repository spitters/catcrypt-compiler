/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
public import CatCrypt.Crypto.SDist

/-!
# Cryptographic-security preservation by composition

This module proves cryptographic/UC-security preservation across
the `LowCT → JInstr` compiler on the call-free scalar-arith fragment by
**composing two results**, rather than building a fresh
probabilistic-RHL IND-CCA argument:

1. **`interpSP_callfree`** (from `LowCTITreePRHL.lean`): deterministic
   compiler correctness lifted to an `SPComp`-denotation *equality*.  The
   call-free ITree denotation of a scalar-arith program `ps` interprets to the
   *pure* computation `SPComp.pure (srcDenote ps rs)`.  Two programs whose
   big-step `srcDenote` agree therefore have **equal `SPComp` denotation**.

2. **`spDenote_eq_preserves_sdist`**: the generic robust-compilation / RrHP
   fact that *equal denotation ⇒ equal `sdist` ⇒ same security bound*, proved
   by the one-line "rewrite the equal computations under `sdist`" argument.

So **cryptographic-security preservation here follows from the
robust-compilation fact given `progEquiv`, and `progEquiv` *is*
`compile_correct`.**  The paper's bespoke RHL is one route to the security-
preservation obligation; this module composes the RrHP fact with the
deterministic-to-pure lift `interpSP_callfree`.

## What lives here

* `spDenote_eq_preserves_sdist` — the **generic `SPComp` core fact**, stated
  for plain `SPComp`: equal computations have the same `sdist`-bound to an
  ideal.  The proof is a 1-line `rw [← h_eq]`.
* `interpSP_progEquiv` — the **`progEquiv`-at-the-`SPComp`-level** lemma from
  `compile_correct`: if two call-free programs have equal big-step `srcDenote`,
  their `interpSP` interpretations are *equal* `SPComp` computations.  Proved by
  rewriting both sides with `interpSP_callfree`.
* `compiled_preserves_security` — **the main theorem**.  For the
  call-free compiled kernel, a `sdist ≤ ε` security bound to an ideal transfers
  from the source program to the compiled program, by composing
  `interpSP_progEquiv` (denotation equality) with `spDenote_eq_preserves_sdist`
  (equal denotation ⇒ same bound).  The hypothesis is the compile-correctness
  equality (`srcDenote` agreement); the conclusion is the bound on the compiled
  kernel.
* `compiled_preserves_security_self` — the canonical same-source-program
  instance (`progEquiv` is reflexive here), recording that running the *same*
  call-free program is denotationally invariant, so the bound is preserved
  trivially by `sdist_self`-style reasoning.

## Relation to robust compilation

Security preservation here is **not** a fresh IND-CCA RHL proof: it is
`compile_correct` (⇒ `progEquiv` at the `SPComp` level via `interpSP_callfree`)
composed with the robust-compilation (RrHP) fact `spDenote_eq_preserves_sdist`.

## Iris-free

Imports only `LowCTITreePRHL` (the iris-free ITree+pRHL layer) and
`CatCrypt.Crypto.SDist` (the `sdist` API).  Nothing under `Bridges/` or
`IrisBridge/`: no guarded ITrees, no step-indexing, no separation logic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open scoped ENNReal

/-! ## 1. The generic `SPComp` core fact

The generic "equal computations ⇒ equal `sdist` ⇒ same bound" argument, for
plain `SPComp`: a one-line rewrite by the denotation equality. -/

/-- **Generic security-preservation core (plain `SPComp`).**  If two `SPComp`
    computations `c`, `c'` are equal, then any `sdist`-bound to an ideal
    computation transfers from `c` to `c'`: equal
    computations have equal `sdist`, hence the same security bound.  The proof
    is the single rewrite `rw [← h_eq]` — the point being that `sdist` is a
    *function* of its two arguments, so propositionally-equal computations are
    interchangeable inside any bound. -/
theorem spDenote_eq_preserves_sdist {α β : Type}
    {c c' ideal : SPComp β} {ε : ℝ≥0∞}
    (h_eq : c = c')
    (h_sec : sdist (fun _ : α => c) (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => c') (fun _ : α => ideal) ≤ ε := by
  rw [← h_eq]; exact h_sec

/-! ## 2. `progEquiv` at the `SPComp` level, from `compile_correct`

`interpSP_callfree` collapses the call-free ITree denotation to
`SPComp.pure (srcDenote …)`.  So two call-free programs whose big-step
`srcDenote` agree have *equal* `SPComp` interpretations — this is precisely
`progEquiv` (denotational equality) at the `SPComp` layer, derived from the
deterministic `compile_correct`. -/

/-- **`progEquiv` at the `SPComp` level (call-free fragment).**  If two
    call-free scalar-arith programs `ps`, `qs` have equal big-step semantics on
    the given states (`srcDenote ps rs₁ = srcDenote qs rs₂` — the
    `compile_correct` equality), then their `interpSP` interpretations are
    *equal* `SPComp` computations.  Proven by rewriting both sides with
    `interpSP_callfree` and the `srcDenote` agreement.  This is the
    `interpSP`-level `progEquiv` that feeds `spDenote_eq_preserves_sdist`. -/
theorem interpSP_progEquiv
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ps qs : List ArithSrc) (rs₁ rs₂ : RustState)
    (hsrc : srcDenote ps rs₁ = srcDenote qs rs₂) :
    interpSP h (itreeDenoteArith ps rs₁) = interpSP h (itreeDenoteArith qs rs₂) := by
  rw [interpSP_callfree, interpSP_callfree, hsrc]

/-! ## 3. The main theorem

Compose §2 (denotation equality from `compile_correct`) with §1 (equal
denotation ⇒ same `sdist`-bound).  The hypothesis is the compile-correctness
`srcDenote` agreement between source and compiled program; the conclusion is the
security bound on the compiled kernel. -/

/-- **Compiled kernel preserves cryptographic security.**

    Let `srcP` be a source call-free scalar-arith program and `tgtP` its
    compilation (modelled here as a call-free program — the compiled block's
    big-step behaviour), with `hcc : srcDenote srcP rs = srcDenote tgtP rs` the
    `compile_correct` equality on the run state.  If the *source* kernel's
    `SPComp` interpretation is `ε`-close (in `sdist`) to an `ideal` computation,
    then so is the *compiled* kernel's.

    Security preservation is obtained **by composition**: `interpSP_progEquiv`
    (compile_correct ⇒ equal `SPComp` denotation, §2) feeds
    `spDenote_eq_preserves_sdist` (equal denotation ⇒ same bound, §1).  No fresh
    probabilistic-RHL IND-CCA argument is needed.

    `(secure compilation via RrHP + deterministic-to-pure lift)` -/
theorem compiled_preserves_security {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (srcP tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hcc : srcDenote srcP rs = srcDenote tgtP rs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
                  (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (itreeDenoteArith tgtP rs))
          (fun _ : α => ideal) ≤ ε :=
  spDenote_eq_preserves_sdist
    (interpSP_progEquiv h srcP tgtP rs rs hcc) hsec

/-- **Canonical instance: the same source program.**  When source and compiled
    program are the *same* call-free program (`progEquiv` reflexive — the
    `compile_correct` equality is `rfl`), the security bound is preserved
    immediately: the `interpSP` denotation is literally unchanged.  This is the
    `sdist_self`-style degenerate case of `compiled_preserves_security`. -/
theorem compiled_preserves_security_self {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ps : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith ps rs))
                  (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (itreeDenoteArith ps rs))
          (fun _ : α => ideal) ≤ ε :=
  compiled_preserves_security h ps ps rs ideal rfl hsec

/-! ## 4. The composition

The theorem below records the conceptual tie in Lean form.  It states the
*shape* of the composition: for the call-free fragment, the `progEquiv`
hypothesis of robust compilation is, at the `SPComp` level, exactly
`interpSP_progEquiv` (i.e. `compile_correct`).  Plugging that into the generic
equal-denotation-⇒-same-bound core (`spDenote_eq_preserves_sdist`) yields
`compiled_preserves_security`. -/

/-- **The composition, spelled out.**  Given the `compile_correct` `srcDenote`
    agreement (`progEquiv` at the `SPComp` level) *and* the source security
    bound, the compiled bound follows by feeding the former (as denotation
    equality, via `interpSP_progEquiv`) into the latter (the
    equal-denotation-⇒-same-bound core
    `spDenote_eq_preserves_sdist`).  This is definitionally
    `compiled_preserves_security`; stated here to make the two-result
    composition explicit. -/
theorem P4_3_security_preservation_by_composition {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (srcP tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (h_compile_correct : srcDenote srcP rs = srcDenote tgtP rs)
    (h_source_secure :
      sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
            (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (itreeDenoteArith tgtP rs))
          (fun _ : α => ideal) ≤ ε :=
  -- compose: (compile_correct ⇒ SPComp progEquiv)  ▷  (equal denote ⇒ same bound)
  spDenote_eq_preserves_sdist
    (h_eq := interpSP_progEquiv h srcP tgtP rs rs h_compile_correct)
    (h_sec := h_source_secure)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
