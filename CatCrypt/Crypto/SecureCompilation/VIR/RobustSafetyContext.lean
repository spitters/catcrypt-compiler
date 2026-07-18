/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety

/-!
# A genuine context model for robust constant-time safety (fuller RSP/RHP)

This file strengthens the first robust-compilation artifact
(`RobustSafety.lean`) from "constant-time **by construction** against attacker
**labellings**" to a fuller Robust-Safety-Preservation (RSP) shape with a
**genuine context model on `Com`**: a program-with-a-hole and a real linking
operation, following Abate, Blanco, Garg, Hriţcu, Patrignani, Thibault,
*"Journey Beyond Full Abstraction: Exploring Robust Property Preservation for
Secure Compilation"* (CSF 2019).

## What `RobustSafety.lean` left open

`RobustSafety.lean`'s module docstring is explicit about the gap. Its context
model is the *secrecy labelling* `LabelCtxt Γ` — the attacker only chooses which
**top-level inputs** are secret. The docstring states that a fuller RSP needs

> a `Com`-with-a-hole that supplies *and consumes* variables, with the attacker
> observing a full leakage trace … a genuine back-translation of arbitrary
> target contexts to source ones.

This file supplies the first half of that: a real **`Com`-with-a-hole** linking
model, the CT-compositionality lemma over linking, and the resulting robust
preservation theorem quantifying over **all target contexts** (not just over
labellings of the top-level inputs).

## The context model: `ComCtx`, a typed program with a hole

On CatCrypt's ANF `Com` substrate (`VIR/Core.lean`) a program is a chain of
`var` let-bindings ending in a `ret`. The natural, faithful notion of a
*linking context* is therefore a **let-prefix with a typed hole** at the tail:
the context binds some variables (extending the de Bruijn context), then the
hole expects a sub-`Com` to act as the continuation. Because in ANF the tail's
result type *is* the whole program's result type, the hole and the outer
interface share the result type `th`. Concretely

* `ComCtx d Γh th Γ` is a context whose hole expects a `Com d Γh th` and which,
  once plugged, yields a `Com d Γ th`;
* `ComCtx.hole` is the trivial context (the hole *is* the whole program, so the
  outer context `Γ` equals the hole context `Γh`);
* `ComCtx.var e C` binds `e : Expr d Γ tb` and then continues with the context
  `C` in the extended de Bruijn context `tb :: Γ` — so the prefix genuinely
  **supplies** a fresh variable that the plugged program may **consume**.

`plug C p : Com d Γ th` performs the linking. This is exactly the lean-mlir /
SSProve "link a fragment as the continuation of a prefix" model, intrinsically
typed so that the supplied variables are visible to the hole.

## Compositionality (the load-bearing lemmas)

* `ComCtx.plug_denote` — **denotational compositionality**: the denotation of
  `plug C p` factors through `p.denote`, evaluated in the valuation the prefix
  `C` accumulates from the outer valuation. This is the `Com` analogue of the
  reduction-semantics "evaluate the prefix, then run the plugged program".
* `ctSafeCtxJasmin` lifts `ctSafeJasmin` to contexts (the prefix's own ops are
  CT-safe, threading the same `.Public`-extension discipline as `ctSafeJasmin`),
  and `ctSafeJasmin_plug` proves **CT-compositionality**:
  `ctSafeJasmin (plug C p)` holds iff the context's prefix is CT-safe *and* the
  plugged program is CT-safe in the propagated label context. CT is a safety
  property, and safety properties compose over linking exactly this way.

## The fuller robust-preservation theorem

`lowerLatticeToJasmin_robustlyCTSafe_ctx` is the headline: *for every target
(Jasmin) linking context `C` whose own prefix is CT-safe, the whole linked
program `plug C (lowerLatticeToJasmin c)` is CT-safe under every labelling*.
That is robust CT in the genuine context sense — the attacker may wrap the
compiled program in **any** CT-safe let-prefix that supplies inputs and consumes
its output, and CT still holds. It is the compositionality lemma
(`ctSafeJasmin_plug`) fed by B2a (`lowerLatticeToJasmin_ctSafeJasmin`).

## Back-translation (item 4): the type-map obstruction, documented

A complete RSP additionally back-translates **target** contexts to **source**
ones. Here the type map is `tau : LatticeTy → JasminTy`, and it is **not
surjective onto target contexts**: a target context may bind Jasmin ops
(`stackLoad`, `regArith`, …) and Jasmin types (`reg 64`, `stackArr w n`) that
have no lattice pre-image — the lattice dialect has only whole-poly types
(`polyC`, `polyN`). So an arbitrary target context is *not* the `tau`-image of
any source context, and a literal back-translation `ComCtx jasmin → ComCtx
lattice` does not exist. We therefore prove the **forward** robust-preservation
direction (the load-bearing half, items 1–3) and characterise back-translation
precisely as an explicit hypothesis: `backTranslates` packages "every target
context is realised by a source context", and `robustCTPreservation_ctx_of_back`
shows that *given* such a back-translation the source-to-target robust
implication holds. The forward result needs no such hypothesis.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The context model: a `Com` with a typed hole

A `ComCtx d Γh th Γ` is a program *with a hole*: given any `Com d Γh th` it
produces a `Com d Γ th`. We take the faithful ANF shape — a let-prefix that binds
fresh variables (extending the de Bruijn context) and then defers to the hole as
its continuation. Because in ANF the tail's result type *is* the whole program's
result type, the hole and the output share the result type `th`. `hole` is the
trivial (identity) context; `var e C` is "bind `e`, then continue with context
`C` in the extended context". -/

/-- A typed program-with-a-hole over a dialect `d`. The hole expects a sub-program
    `Com d Γh th`; the context wraps it as a let-prefix to yield a `Com d Γ th`.
    `Γh` is the hole's input context, `Γ` the outer input context, and `th` the
    result type shared by the hole and the output (the hole is the ANF tail). -/
inductive ComCtx (d : Dialect) [DialectSignature d] :
    Ctxt d → d.Ty → Ctxt d → Type _ where
  /-- The trivial context: the hole is the whole program. The outer input context
      coincides with the hole input context. -/
  | hole {Γh : Ctxt d} {th : d.Ty} : ComCtx d Γh th Γh
  /-- Bind an expression `e`, then continue with the context `C` in the de Bruijn
      context extended by `e`'s result. The prefix supplies a fresh variable that
      the plugged program may consume. -/
  | var {Γh : Ctxt d} {th : d.Ty} {Γ : Ctxt d} {tb : d.Ty}
      (e : Expr d Γ tb) (C : ComCtx d Γh th (tb :: Γ)) :
      ComCtx d Γh th Γ

namespace ComCtx

/-- **Linking (plug).** Plug a program `p : Com d Γh th` into the hole of a
    context `C : ComCtx d Γh th Γ`, yielding the linked whole program
    `Com d Γ th`. `hole` returns `p` unchanged; `var e C` prepends the let-binding
    `e` to the linked tail. -/
def plug {d : Dialect} [DialectSignature d] :
    {Γh : Ctxt d} → {th : d.Ty} → {Γ : Ctxt d} →
    ComCtx d Γh th Γ → Com d Γh th → Com d Γ th
  | _, _, _, .hole, p => p
  | _, _, _, .var e C, p => .var e (plug C p)

@[simp]
theorem plug_hole {d : Dialect} [DialectSignature d]
    {Γh : Ctxt d} {th : d.Ty} (p : Com d Γh th) :
    plug (ComCtx.hole) p = p := by simp only [plug]

@[simp]
theorem plug_var {d : Dialect} [DialectSignature d]
    {Γh : Ctxt d} {th : d.Ty} {Γ : Ctxt d} {tb : d.Ty}
    (e : Expr d Γ tb) (C : ComCtx d Γh th (tb :: Γ)) (p : Com d Γh th) :
    plug (ComCtx.var e C) p = .var e (plug C p) := by simp only [plug]

/-! ## 2. Denotational compositionality

The denotation of a plugged program factors through the plugged program's own
denotation, evaluated in the valuation the prefix accumulates from the outer
valuation. We express the accumulated valuation by the same recursion as `plug`:
`hole` leaves the valuation unchanged; `var e C` extends it with `e.denote`. -/

/-- The valuation the context's let-prefix accumulates: starting from the outer
    valuation `V : Valuation Γ`, run the prefix's bindings to reach a valuation of
    the hole's context `Γh`. -/
def propagate {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] :
    {Γh : Ctxt d} → {th : d.Ty} → {Γ : Ctxt d} →
    (C : ComCtx d Γh th Γ) → Ctxt.Valuation Γ → Ctxt.Valuation Γh
  | _, _, _, .hole, V => V
  | _, _, _, .var e C, V => propagate C (V.extend (e.denote V))

/-- **Denotational compositionality.** The denotation of the linked program is
    the denotation of the plugged program in the valuation the prefix propagates
    from the outer valuation. This is the `Com` analogue of "evaluate the prefix,
    then run the plugged continuation". -/
theorem plug_denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] :
    {Γh : Ctxt d} → {th : d.Ty} → {Γ : Ctxt d} →
    (C : ComCtx d Γh th Γ) → (p : Com d Γh th) → (V : Ctxt.Valuation Γ) →
    (plug C p).denote V = p.denote (propagate C V)
  | _, _, _, .hole, _, _ => by simp only [plug_hole, propagate]
  | _, _, _, .var e C, p, V => by
      rw [plug_var, Com.denote, show propagate (ComCtx.var e C) V
            = propagate C (V.extend (e.denote V)) from by simp only [propagate]]
      exact plug_denote C p (V.extend (e.denote V))

end ComCtx

/-! ## 3. CT-safety of contexts and CT-compositionality over linking

We lift `ctSafeJasmin` to contexts. A context is CT-safe iff every op in its
let-prefix is CT-safe, threading the same `.Public`-extension discipline that
`ctSafeJasmin` uses on `Com`. The hole imposes no constraint of its own — the
plugged program carries its own CT obligation. The key lemma `ctSafeJasmin_plug`
then shows CT is **compositional over linking**: the linked whole program is
CT-safe iff the context prefix is CT-safe and the plugged program is CT-safe in
the label context the prefix propagates. -/

/-- The label context a Jasmin context's prefix propagates: starting from a
    labelling `L` of the outer context `Γ`, extend by `.Public` per binding (the
    same discipline `ctSafeJasmin` uses), reaching a labelling of the hole's
    context `Γh`. -/
def propagateLabel :
    {Γh : Ctxt jasminDialect} → {th : JasminTy} → {Γ : Ctxt jasminDialect} →
    (C : ComCtx jasminDialect Γh th Γ) → LabelCtxt Γ → LabelCtxt Γh
  | _, _, _, .hole, L => L
  | _, _, _, .var _ C, L => propagateLabel C (L.extend SecretLevel.Public)

/-- **CT-safety of a context.** A Jasmin context is CT-safe under a labelling `L`
    iff every op in its let-prefix is CT-safe, with the label context extended by
    `.Public` per binding. The hole contributes nothing — it is the plugged
    program's own obligation. Mirrors `ctSafeJasmin` on `Com`, dropping the `ret`
    case (the hole replaces it). -/
def ctSafeCtxJasmin :
    {Γh : Ctxt jasminDialect} → {th : JasminTy} → {Γ : Ctxt jasminDialect} →
    ComCtx jasminDialect Γh th Γ → LabelCtxt Γ → Bool
  | _, _, _, .hole, _ => true
  | _, _, _, .var e C, L =>
      ctSafeExprJasmin e L && ctSafeCtxJasmin C (L.extend SecretLevel.Public)

@[simp]
theorem ctSafeCtxJasmin_hole {Γh : Ctxt jasminDialect} {th : JasminTy}
    (L : LabelCtxt Γh) :
    ctSafeCtxJasmin (ComCtx.hole : ComCtx jasminDialect Γh th Γh) L = true := by
  simp only [ctSafeCtxJasmin]

@[simp]
theorem ctSafeCtxJasmin_var {Γh : Ctxt jasminDialect} {th : JasminTy}
    {Γ : Ctxt jasminDialect} {tb : JasminTy}
    (e : Expr jasminDialect Γ tb) (C : ComCtx jasminDialect Γh th (tb :: Γ))
    (L : LabelCtxt Γ) :
    ctSafeCtxJasmin (ComCtx.var e C) L
      = (ctSafeExprJasmin e L
          && ctSafeCtxJasmin C (L.extend SecretLevel.Public)) := by
  simp only [ctSafeCtxJasmin]

/-- **CT-compositionality over linking (the key lemma).** Constant-time safety is
    compositional over `plug`: the linked whole program `plug C p` is CT-safe
    under labelling `L` iff the context prefix `C` is CT-safe under `L` *and* the
    plugged program `p` is CT-safe under the labelling `C` propagates. Hence
    CT-safety of a linked program follows from CT-safety of the context plus
    CT-safety of the plugged program — the robust-safety compositionality that
    makes the fuller RSP go through. Proved by induction on `C`. -/
theorem ctSafeJasmin_plug :
    {Γh : Ctxt jasminDialect} → {th : JasminTy} → {Γ : Ctxt jasminDialect} →
    (C : ComCtx jasminDialect Γh th Γ) → (p : Com jasminDialect Γh th) →
    (L : LabelCtxt Γ) →
    ctSafeJasmin (ComCtx.plug C p) L
      = (ctSafeCtxJasmin C L && ctSafeJasmin p (propagateLabel C L))
  | _, _, _, .hole, _, L => by
      simp only [ComCtx.plug_hole, ctSafeCtxJasmin_hole, Bool.true_and,
        show propagateLabel (ComCtx.hole) L = L from by simp only [propagateLabel]]
  | _, _, _, .var e C, p, L => by
      rw [ComCtx.plug_var, ctSafeJasmin_var, ctSafeCtxJasmin_var,
        ctSafeJasmin_plug C p (L.extend SecretLevel.Public),
        show propagateLabel (ComCtx.var e C) L
          = propagateLabel C (L.extend SecretLevel.Public) from by
            simp only [propagateLabel]]
      simp only [Bool.and_assoc]

/-- **CT of a linked program, from its two parts.** The directly usable corollary
    of `ctSafeJasmin_plug`: if the context is CT-safe and the plugged program is
    CT-safe in the propagated labelling, the linked whole program is CT-safe. This
    is the "safety composes over linking" implication. -/
theorem ctSafeJasmin_plug_of {Γh : Ctxt jasminDialect} {th : JasminTy}
    {Γ : Ctxt jasminDialect}
    (C : ComCtx jasminDialect Γh th Γ) (p : Com jasminDialect Γh th)
    (L : LabelCtxt Γ)
    (hC : ctSafeCtxJasmin C L = true)
    (hp : ctSafeJasmin p (propagateLabel C L) = true) :
    ctSafeJasmin (ComCtx.plug C p) L = true := by
  rw [ctSafeJasmin_plug, hC, hp, Bool.and_true]

/-! ## 4. The fuller robust-safety preservation theorem

We now state robust CT in the genuine context sense. A Jasmin program is
**robustly CT-safe against all contexts** iff, for every CT-safe linking context
`C` and every labelling, the linked whole program is CT-safe. This quantifies
over all `Com`-with-a-hole contexts — not merely over labellings of the top-level
inputs as in `RobustSafety.RobustlyCTSafe`. -/

/-- **Robust CT-safety against all contexts (target / Jasmin).** A Jasmin program
    `p` robustly satisfies constant-time in the genuine context sense iff, for
    every linking context `C` whose prefix is CT-safe and every labelling `L`, the
    linked whole program `plug C p` is CT-safe. The quantification is over all
    `Com`-with-a-hole contexts: the attacker may wrap `p` in any CT-safe let-prefix
    that supplies inputs and consumes `p`'s output. -/
def RobustlyCTSafeCtx {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : Com jasminDialect Γ t) : Prop :=
  ∀ {Δ : Ctxt jasminDialect}
    (C : ComCtx jasminDialect Γ t Δ) (L : LabelCtxt Δ),
    ctSafeCtxJasmin C L = true → ctSafeJasmin (ComCtx.plug C p) L = true

/-- The trivial (identity) context recovers `RobustlyCTSafe`: robust CT against
    all contexts implies robust CT against all labellings of the program itself.
    (`hole` propagates the labelling unchanged, so this specialises the context
    quantifier to the empty prefix.) -/
theorem RobustlyCTSafeCtx.toRobustlyCTSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : Com jasminDialect Γ t} (h : RobustlyCTSafeCtx p) :
    RobustlyCTSafe p := by
  intro L
  have hsafe := h (ComCtx.hole) L (ctSafeCtxJasmin_hole L)
  rwa [ComCtx.plug_hole] at hsafe

/-- **Headline: the lowering is robustly CT-safe against all contexts.** For every
    source lattice program `c`, the lowered Jasmin program is robustly
    constant-time in the genuine context sense: wrapped in *any* CT-safe linking
    context, the whole linked program is constant-time, under every labelling.
    Proof: CT-compositionality (`ctSafeJasmin_plug_of`) reduces the linked-program
    obligation to (i) the context's own CT-safety — the hypothesis — and (ii) the
    plugged program's CT-safety in the propagated labelling — exactly B2a
    (`lowerLatticeToJasmin_ctSafeJasmin`). -/
theorem lowerLatticeToJasmin_robustlyCTSafe_ctx
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafeCtx (lowerLatticeToJasmin c) := by
  intro Δ C L hC
  exact ctSafeJasmin_plug_of C (lowerLatticeToJasmin c) L hC
    (lowerLatticeToJasmin_ctSafeJasmin c (propagateLabel C L))

/-- Concrete corollary: the lowered NTT-expanded target program is robustly
    constant-time against all contexts. -/
theorem tgt_robustlyCTSafe_ctx (q n : Nat) :
    RobustlyCTSafeCtx (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) :=
  lowerLatticeToJasmin_robustlyCTSafe_ctx (LatticeDialect.tgtCom q n)

/-- Concrete corollary: the lowered unexpanded source program (`poly_mul`) is
    robustly constant-time against all contexts. -/
theorem src_robustlyCTSafe_ctx (q n : Nat) :
    RobustlyCTSafeCtx (lowerLatticeToJasmin (LatticeDialect.srcCom q n)) :=
  lowerLatticeToJasmin_robustlyCTSafe_ctx (LatticeDialect.srcCom q n)

/-! ## 5. Robust correctness against all (input-supplying) contexts

Pairing the safety guarantee with behaviour preservation in the richer model:
when a context supplies an input valuation, the linked program's observable
denotation factors through the plugged program's denotation
(`ComCtx.plug_denote`), and the lowering preserves that denotation (A3). So the
behaviour the attacker links against is preserved exactly, through the context. -/

/-- **Robust correctness under linking.** For every source lattice program `c`,
    every Jasmin context `C` linking the lowered program, and every outer
    valuation `V`, the linked program's denotation is the denotation of the
    lowered program in the valuation `C` propagates. Combined with A3 this equals
    the `tau`-transport of the source program's denotation, so the observable
    behaviour the attacker links against is preserved exactly. -/
theorem lowerLatticeToJasmin_robust_correctness_ctx
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    {Δ : Ctxt jasminDialect}
    (C : ComCtx jasminDialect (Γ.map tau) (tau t) Δ)
    (V : Ctxt.Valuation Δ) :
    (ComCtx.plug C (lowerLatticeToJasmin c)).denote V
      = (lowerLatticeToJasmin c).denote (ComCtx.propagate C V) :=
  ComCtx.plug_denote C (lowerLatticeToJasmin c) V

/-! ## 6. The two halves packaged (genuine context model) -/

/-- **Secure compilation against all contexts (combined).** For every source
    lattice program, the lowering is simultaneously robustly constant-time against
    all linking contexts (§4) and behaviour-preserving under linking (§5). This is
    the secure-compilation pairing in the genuine `Com`-with-a-hole context model,
    strengthening `RobustSafety.lowerLatticeToJasmin_secure_compilation` (which
    quantified only over top-level secrecy labellings). -/
theorem lowerLatticeToJasmin_secure_compilation_ctx
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafeCtx (lowerLatticeToJasmin c)
      ∧ (∀ {Δ : Ctxt jasminDialect}
          (C : ComCtx jasminDialect (Γ.map tau) (tau t) Δ)
          (V : Ctxt.Valuation Δ),
          (ComCtx.plug C (lowerLatticeToJasmin c)).denote V
            = (lowerLatticeToJasmin c).denote (ComCtx.propagate C V)) :=
  ⟨lowerLatticeToJasmin_robustlyCTSafe_ctx c,
   fun C V => lowerLatticeToJasmin_robust_correctness_ctx c C V⟩

/-! ## 7. Back-translation (item 4): the type-map obstruction, made precise

A complete RSP back-translates **target** contexts to **source** contexts to show
no target attacker has more power than some source attacker. The type map
`tau : LatticeTy → JasminTy` is **not surjective onto target contexts**: a Jasmin
context may bind ops and types (`stackLoad`, `reg 64`, `stackArr w n` with no
`tau`-pre-image) that the whole-poly lattice dialect cannot express. So a literal
`ComCtx jasmin → ComCtx lattice` back-translation does not exist.

We make this precise rather than attempt the impossible. `lowerCtx` is the
context-level *image* of the lowering (lattice contexts to Jasmin contexts), used
only to state the source-side judgement. `backTranslates p` packages "every
CT-safe target context linking `p` is realised, on CT-safety, by *some* source
context"; `robustCTPreservation_ctx_of_back` then derives the source→target
robust implication *given* such a back-translation. The forward result (§4) needs
no such hypothesis — it is the load-bearing half. -/

/-- Lower a lattice context to a Jasmin context along the lowering, in lockstep
    with `lowerLatticeToJasmin` on `Com`. This is the context-level *image* of the
    lowering (not a back-translation): it is used only to *state* the source-side
    robust judgement and the back-translation hypothesis. -/
def lowerCtx {Γh : Ctxt latticeDialect} {th : LatticeTy} :
    {Γ : Ctxt latticeDialect} →
    ComCtx latticeDialect Γh th Γ →
    ComCtx jasminDialect (Γh.map tau) (tau th) (Γ.map tau)
  | _, .hole => .hole
  | _, .var e C => .var (lowerExpr e) (lowerCtx C)

/-- **Source-side robust CT against all (lattice) contexts.** Phrased through the
    lowering so the CT property is the same post-lowering memory-behaviour
    property on both sides (the lattice dialect has no addressed access of its
    own). A lattice program robustly satisfies CT against all source contexts iff,
    for every lattice context `C` whose lowered prefix is CT-safe, the lowered
    linked program is CT-safe. -/
def RobustlyCTSafeCtxSource {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t) : Prop :=
  ∀ {Δ : Ctxt latticeDialect}
    (C : ComCtx latticeDialect Γ t Δ) (L : LabelCtxt (Δ.map tau)),
    ctSafeCtxJasmin (lowerCtx C) L = true →
    ctSafeJasmin (lowerLatticeToJasmin (ComCtx.plug C c)) L = true

/-- **Back-translatability hypothesis.** "Every CT-safe *target* context linking
    the lowered program `lowerLatticeToJasmin c` is realised, on the CT-safety of
    the linked program, by some *source* context's lowering." This is the
    statement a genuine back-translation would discharge. Because `tau` is not
    surjective onto target contexts (Jasmin-only ops/types have no lattice
    pre-image), it cannot be proved in general — we carry it as an explicit
    hypothesis, never an axiom. -/
def backTranslates {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t) : Prop :=
  ∀ {Δ : Ctxt jasminDialect}
    (C : ComCtx jasminDialect (Γ.map tau) (tau t) Δ) (L : LabelCtxt Δ),
    ctSafeCtxJasmin C L = true →
    ∃ (Δ₀ : Ctxt latticeDialect) (C₀ : ComCtx latticeDialect Γ t Δ₀)
      (L₀ : LabelCtxt (Δ₀.map tau)),
      ctSafeCtxJasmin (lowerCtx C₀) L₀ = true ∧
      (ctSafeJasmin (lowerLatticeToJasmin (ComCtx.plug C₀ c)) L₀ = true →
        ctSafeJasmin (ComCtx.plug C (lowerLatticeToJasmin c)) L = true)

/-- **Robust preservation via back-translation (conditional).** *Given* a
    back-translation (`backTranslates c`), source robust CT against all lattice
    contexts implies target robust CT against all Jasmin contexts. This is the
    RSP back-translation direction; it is conditional precisely because the type
    map obstructs an unconditional back-translation. The forward direction (§4,
    `lowerLatticeToJasmin_robustlyCTSafe_ctx`) holds unconditionally and is the
    load-bearing half. -/
theorem robustCTPreservation_ctx_of_back
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hback : backTranslates c) (hSrc : RobustlyCTSafeCtxSource c) :
    RobustlyCTSafeCtx (lowerLatticeToJasmin c) := by
  intro Δ C L hC
  obtain ⟨Δ₀, C₀, L₀, hC₀, himpl⟩ := hback C L hC
  exact himpl (hSrc C₀ L₀ hC₀)

/-- The back-translation is, however, **unnecessary** for the headline guarantee:
    §4 already proves the target side robustly CT-safe against all contexts with
    no back-translation hypothesis. This restates that the forward result subsumes
    any conclusion `robustCTPreservation_ctx_of_back` could draw. -/
theorem robustCTPreservation_ctx_uncond
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafeCtx (lowerLatticeToJasmin c) :=
  lowerLatticeToJasmin_robustlyCTSafe_ctx c

/-! ## 8. Smoke: robust CT against contexts is non-vacuous

The genuine context judgement is restrictive: a context that itself performs a
secret-indexed `stackLoad` is not CT-safe, so it is excluded from the robust
quantifier — confirming `RobustlyCTSafeCtx` is not vacuously true by admitting
every context. We reuse `JasminCTPredicate.loadProg`'s secret-index load as the
hostile prefix. -/

/-- A hostile context: a let-prefix performing a secret-indexed `stackLoad`, with
    a hole expecting the loaded value as the continuation. Its own prefix is
    *not* CT-safe under the secret-index labelling, so it is rightly excluded from
    the robust quantifier. -/
def hostileCtx :
    ComCtx jasminDialect (.reg 16 :: JasminCTPredicate.loadCtxt) (.reg 16)
      JasminCTPredicate.loadCtxt :=
  .var (.mk (.stackLoad 16 8) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (ComCtx.hole)

/-- The hostile context is **not** CT-safe under the secret-index labelling: its
    prefix's `stackLoad` reads a secret-derived address. So the robust context
    quantifier (`RobustlyCTSafeCtx`) genuinely excludes it — the judgement is not
    vacuously satisfied by admitting every context. -/
theorem hostileCtx_not_ctSafe :
    ctSafeCtxJasmin hostileCtx JasminCTPredicate.secretIdxLabels = false := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext
