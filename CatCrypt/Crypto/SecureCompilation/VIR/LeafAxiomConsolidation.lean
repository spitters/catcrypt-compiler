/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# Cross-side leaf-axiom consolidation

The central trust edge of the whole emit-correctness chain is the
**cross-side leaf agreement**: the claim that the emitted jasmin/x86 *leaf*
binary computes the Lean leaf *spec* it is supposed to implement.  Across the
development this edge shows up under several names — `DialectJasminLeafAgrees`
(`DialectToJasminComCorrect`, the front-lowering edge), `LeafAgrees`
(`JasminPrintSemCorrect`, the named-evaluator edge), and the per-protocol
forms (`FAEST.Leaves.FaestLeafAgrees`, `Pairing.Bls12381AUCurves.*Backed`,
`LatticeToJasminDenote.LeafAgrees`).

This module **consolidates** the two complementary discharge paths and names the
single irreducible residual precisely, so the trust edge stops living in
docstring prose and becomes a citable Lean object.

## The two corroborating paths

1. **Structural / semantic path.** For the *front lowering*
   (`cryptoDialectToJasminCom` / `toJExprD`) the leaf-agreement obligation is
   discharged **axiom-free** by
   `DialectToJasminComCorrect.dialectJasminLeafAgrees_holds`: every
   arithmetic/const leaf agrees by computation, and every opaque `extCall` leaf
   agrees on the canonical default (both the dialect leaf and the model's
   `jasminExtSem` are the stub default, transported by `ctTransTy_default`).
   This is the model side: it says "the lowering preserves the model's leaf
   denotation", with no external input.

2. **Differential-validation path.** For a *concrete emitted* leaf, the leaf's
   machine semantics is differentially validated against Jasmin's Rocq reference
   and against KAT/NIST vectors (the pattern used for NOT/NEG, the ADX trio,
   the ZMM packed op, the AUCurves pairing tower, and the
   FAEST AES-NI/SHAKE128 libjade leaves). That validation is what *earns* the
   claim "the emitted binary's modelled leaf semantics equals the model leaf
   `jasminExtSem`". We package that earned claim as the named predicate
   `LeafFFIValidated` below.

Where both paths cover a leaf, the agreement is **doubly corroborated**: the
structural path closes the front-lowering edge unconditionally, and
`LeafFFIValidated` closes the emitted-binary-vs-model edge.  The corroboration
theorem `leafAgrees_of_FFIValidated` derives the named-evaluator
`JasminPrintSemCorrect.LeafAgrees` from `LeafFFIValidated`, so a caller that
has validated its leaves gets the full evaluator-preservation chain
(`execCom_eq`, `lowerComToProg_sem_eq`) with **no** bare leaf axiom.

## The irreducible residual (the FFI trust edge)

`LeafFFIValidated leafSem` is the **only** remaining assumption: it is the FFI
boundary to an externally compiled leaf binary.  Lean
has no operational model of the produced machine code, so "the binary computes
the modelled `leafSem`" cannot be a Lean theorem — it is established *outside*
Lean by the differential validation + KAT and *named* here, scoped to the
concrete leaf, rather than left as a bare global `axiom`.  This is the same
boundary as `JasminCompilerBridge.jasminc_preserves_uc` (the cited Jasmin
compiler-correctness paper): everything *above* it is a Lean proof; the step to
the running binary is trusted and explicitly delimited.

No bare axiom, no `sorry`: `LeafFFIValidated` is a parametric hypothesis, not a
global `axiom`, exactly like the per-protocol `*LeafAgrees` it generalises.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LeafAxiomConsolidation

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-! ## 1. The named FFI trust edge

`LeafFFIValidated leafSem` is the scoped assumption that the (model of the)
externally-compiled leaf, captured by the leaf semantics `leafSem`, computes the
model's leaf interpretation `jasminExtSem` pointwise, at every leaf name /
signature.  This is precisely what the per-leaf differential validation (jasmin
Rocq reference + KAT/NIST vectors) establishes outside Lean; here it is a named
predicate over the leaf semantics rather than a bare global axiom. -/

/-- **FFI-validated leaf semantics (the residual trust edge).** The emitted
    leaf's modelled semantics `leafSem` agrees pointwise with the model leaf
    interpretation `jasminExtSem`.  This is the claim earned, *outside Lean*, by
    differentially validating the emitted binary against Jasmin's Rocq reference
    and the KAT/NIST vectors; it is named here (scoped to the concrete leaf
    semantics) instead of being assumed as a bare global axiom. -/
def LeafFFIValidated (leafSem : LeafSem) : Prop :=
  ∀ (name : String) (argTys : List JasminTy) (retTy : JasminTy)
    (args : HVector (fun t => ⟦t⟧) argTys),
    leafSem name argTys retTy args = jasminExtSem name argTys retTy args

/-- The intended canonical witness of `LeafFFIValidated`: the model leaf
    interpretation `jasminExtSem` validates against itself.  This shows the
    residual edge is **non-vacuous** — there is a concrete `leafSem` satisfying
    it (the one a stub-bound emitter produces), and `LeafFFIValidated` reduces to
    a pointwise-equality obligation discharged per concrete leaf by the
    differential KAT. -/
theorem leafFFIValidated_jasminExtSem : LeafFFIValidated jasminExtSem :=
  fun _ _ _ _ => rfl

/-! ## 2. Differential path ⇒ named-evaluator leaf agreement

`JasminPrintSemCorrect.LeafAgrees leafSem` is the leaf edge the whole evaluator
chain (`execExpr_eq`, `execCom_eq`, `lowerComToProg_sem_eq`) is parametric over.
Under the FFI-validated hypothesis it is immediate: the evaluator's leaf reads
its arguments out of the store (`lookupArgsStore`), which equals reading them out
of the valuation (`Expr.lookupArgs`) under `StoreAgrees`, and then
`LeafFFIValidated` rewrites `leafSem` to `jasminExtSem`. -/

/-- **Differential path discharge.** A leaf semantics that is `LeafFFIValidated`
    satisfies the named-evaluator leaf-agreement `JasminPrintSemCorrect.LeafAgrees`.
    This is the second corroborating path: the emitted binary (modelled by
    `leafSem`, validated against the Rocq reference + KAT) drives the full
    evaluator-preservation chain with no bare leaf axiom. -/
theorem leafAgrees_of_FFIValidated {leafSem : LeafSem}
    (hVal : LeafFFIValidated leafSem) :
    JasminPrintSemCorrect.LeafAgrees leafSem := by
  intro Γ vm V s name argTys retTy args hS
  rw [hVal name argTys retTy (lookupArgsStore vm s args)]
  rw [lookupArgsStore_eq hS args]

/-! ## 3. The two-path corroboration

For the validated-leaf fragment both paths fire:

* the **structural** path (`dialectJasminLeafAgrees_holds`) closes the
  *front-lowering* edge `DialectToJasminComCorrect.DialectJasminLeafAgrees`
  unconditionally (axiom-free, no hypothesis);
* the **differential** path (`leafAgrees_of_FFIValidated`) closes the
  *named-evaluator* edge `JasminPrintSemCorrect.LeafAgrees` from the single
  scoped residual `LeafFFIValidated`.

`leafEdge_doublyCorroborated` records exactly this conjunction.  Its first
component carries **no** hypothesis; only its second component consumes the
residual `hVal`.  So the residual trust surface of the cross-side leaf axiom is
*exactly* `LeafFFIValidated` — the FFI boundary to the externally compiled leaf
— and nothing more. -/

/-- **Two-path corroboration of the cross-side leaf edge.** Under the
    single scoped residual `LeafFFIValidated leafSem` (the FFI trust edge to the
    externally compiled leaf), both leaf-agreement obligations hold:

    1. the **front-lowering** edge
       `DialectToJasminComCorrect.DialectJasminLeafAgrees` — discharged *without*
       using `hVal`, by the structural proof `dialectJasminLeafAgrees_holds`;
    2. the **named-evaluator** edge `JasminPrintSemCorrect.LeafAgrees leafSem`
       — discharged from `hVal` by `leafAgrees_of_FFIValidated`.

    The asymmetry is the point: path (1) is unconditional, so the residual trust
    surface is precisely `LeafFFIValidated`, the FFI boundary. -/
theorem leafEdge_doublyCorroborated {leafSem : LeafSem}
    (hVal : LeafFFIValidated leafSem) :
    DialectToJasminComCorrect.DialectJasminLeafAgrees ∧
      JasminPrintSemCorrect.LeafAgrees leafSem :=
  ⟨DialectToJasminComCorrect.dialectJasminLeafAgrees_holds,
   leafAgrees_of_FFIValidated hVal⟩

/-- **Residual is the only edge.** Restated for the canonical stub-bound emitter
    (`leafSem = jasminExtSem`), where the residual `LeafFFIValidated` is itself
    discharged (`leafFFIValidated_jasminExtSem`): *both* leaf-agreement
    obligations hold with **no** hypothesis at all.  This is the fully
    closed-loop instance — the model leaf agrees with itself on both edges. -/
theorem leafEdge_closed_stub :
    DialectToJasminComCorrect.DialectJasminLeafAgrees ∧
      JasminPrintSemCorrect.LeafAgrees jasminExtSem :=
  leafEdge_doublyCorroborated leafFFIValidated_jasminExtSem

end CatCrypt.Crypto.SecureCompilation.VIR.LeafAxiomConsolidation
