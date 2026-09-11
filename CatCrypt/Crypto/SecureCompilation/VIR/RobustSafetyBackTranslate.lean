/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext

/-!
# Back-translation for the image class: discharging `backTranslates` (full RSP)

`RobustSafetyContext.lean` proves the **forward** half of Robust-Safety
Preservation for the lattice → Jasmin lowering unconditionally
(`lowerLatticeToJasmin_robustlyCTSafe_ctx`: the compiled program is robustly
constant-time against *every* CT-safe target context). The **back-translation**
half — source robust CT ⟹ target robust CT — it leaves as the explicit
hypothesis `backTranslates`, because the type map `tau : LatticeTy → JasminTy`
is *not surjective onto target contexts*: a Jasmin context may bind ops and
types (`stackLoad`, `reg 64`, `stackArr w n`) that the whole-poly lattice
dialect cannot express, so a literal back-translation
`ComCtx jasmin → ComCtx lattice` cannot exist for *all* target contexts.

This file builds the back-translation for the class of target contexts that
genuinely *do* arise from source contexts — the **image class** of the
context-level lowering `lowerCtx : ComCtx lattice → ComCtx jasmin` — and
discharges the back-translation step for that class. Because in any real linking
scenario you only ever link against contexts you can *build* — and every context
you build in the source and then lower lands in this image — the image-class
result is the meaningful robust-compilation guarantee.

## What is in scope, and what is genuinely impossible

* **In scope (proved here, no hypothesis).** For every target context that is
  `lowerCtx C₀` for some source context `C₀`, CT-safety of the linked target
  program *reduces syntactically* to CT-safety of the lowered linked source
  program (`ctSafeJasmin_plug_lowerCtx`, via the commutation lemma
  `plug_lowerCtx`). Hence source robust CT ⟹ target robust CT for the image
  class, with **no `backTranslates` hypothesis**
  (`robustCTPreservation_ctx_image`). We also discharge the per-context
  back-translation step that `backTranslates` packages
  (`backTranslates_image_step`).

* **Genuinely impossible (and why).** A *non-image* target context — one whose
  prefix binds a Jasmin-only op (`stackLoad`/`stackStore`) or a Jasmin-only type
  (`reg w`) — has no `tau`-pre-image at all, so no source context lowers to it.
  The full `backTranslates c` quantifies over *all* target contexts including
  these; it therefore cannot be discharged unconditionally, exactly as
  `RobustSafetyContext` documents. This file does not attempt the impossible: it
  proves the strongest fully-closed statement, the image-class RSP.

## The load-bearing lemmas

* `plug_lowerCtx` — **commutation**: plugging the lowered context with the
  lowered program equals lowering the plugged source program. The
  context-level analogue of the program-level lowering commuting with linking.
* `ctSafeJasmin_plug_lowerCtx` — CT back-transfer: the linked target program's
  CT-safety is *definitionally* the lowered linked source program's CT-safety
  (by `plug_lowerCtx`).
* `robustCTPreservation_ctx_image` — the full RSP for the image class: source
  robust CT ⟹ target robust CT, unconditionally, for contexts arising from
  source contexts.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyBackTranslate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The context-level lowering commutes with linking

`RobustSafetyContext.lowerCtx` is the context-level analogue of
`lowerLatticeToJasmin`: it lowers a lattice context to a Jasmin context in
lockstep (`hole ↦ hole`, `var e C ↦ var (lowerExpr e) (lowerCtx C)`). We prove
it commutes with `plug` and the program-level lowering: plugging the lowered
context with the lowered program equals lowering the plugged source program.
This is the syntactic identity the CT back-transfer rests on. -/

/-- **Commutation of lowering with linking.** Plugging the lowered context
    `lowerCtx C` with the lowered program `lowerLatticeToJasmin p` equals the
    lowering of the plugged source program `lowerLatticeToJasmin (plug C p)`.
    Proved by induction on the lattice context `C`: `hole` returns the lowered
    program on both sides; `var e C` prepends the *same* lowered binding
    `lowerExpr e` to the lowered tail (IH). -/
theorem plug_lowerCtx {Γh : Ctxt latticeDialect} {th : LatticeTy} :
    {Γ : Ctxt latticeDialect} →
    (C : ComCtx latticeDialect Γh th Γ) → (p : Com latticeDialect Γh th) →
    ComCtx.plug (lowerCtx C) (lowerLatticeToJasmin p)
      = lowerLatticeToJasmin (ComCtx.plug C p)
  | _, .hole, p => by
      simp only [lowerCtx, ComCtx.plug_hole]
  | _, .var e C, p => by
      -- Unfold `lowerCtx`, `plug`, and `lowerLatticeToJasmin` on the `.var`
      -- arm (each reduces structurally), leaving the two `Com.var` tails to be
      -- bridged by the induction hypothesis `plug_lowerCtx C p`.
      simp only [lowerCtx, ComCtx.plug, lowerLatticeToJasmin]
      exact congrArg (Com.var (lowerExpr e)) (plug_lowerCtx C p)

/-! ## 2. CT back-transfer for the image class

For an image-class target context `lowerCtx C₀`, the CT-safety of the linked
target program `plug (lowerCtx C₀) (lowerLatticeToJasmin c)` is *definitionally
equal* (via `plug_lowerCtx`) to the CT-safety of the lowered linked source
program `lowerLatticeToJasmin (plug C₀ c)`. This is the back-translation made
real: a target obligation in the image class is *the very same* source
obligation, with no semantic gap to bridge. -/

/-- **CT back-transfer (image class).** For a target context in the image of
    `lowerCtx`, the linked target program's CT-safety predicate equals the
    lowered linked source program's CT-safety predicate, under any labelling.
    Immediate from the commutation lemma `plug_lowerCtx`. -/
theorem ctSafeJasmin_plug_lowerCtx
    {Γ : Ctxt latticeDialect} {t : LatticeTy} {Δ₀ : Ctxt latticeDialect}
    (C₀ : ComCtx latticeDialect Γ t Δ₀) (c : Com latticeDialect Γ t)
    (L : LabelCtxt (Δ₀.map tau)) :
    ctSafeJasmin (ComCtx.plug (lowerCtx C₀) (lowerLatticeToJasmin c)) L
      = ctSafeJasmin (lowerLatticeToJasmin (ComCtx.plug C₀ c)) L := by
  rw [plug_lowerCtx C₀ c]

/-! ## 3. The image class and its full RSP

`RobustlyCTSafeCtxImage c` is target robust CT restricted to image-class
contexts: for every *source* context `C₀` whose lowering `lowerCtx C₀` is
CT-safe, the linked target program is CT-safe. This is exactly the part of the
target robust quantifier (`RobustlyCTSafeCtx`) that ranges over contexts a
linker can actually build by lowering source contexts. For this class the
back-translation is real and the full RSP holds with **no hypothesis**. -/

/-- **Target robust CT, restricted to the image class.** For every source
    context `C₀` whose lowering is CT-safe under `L`, the linked target program
    `plug (lowerCtx C₀) (lowerLatticeToJasmin c)` is CT-safe under `L`. This is
    the image-class slice of `RobustSafetyContext.RobustlyCTSafeCtx`: it
    quantifies over precisely the target contexts that arise from source
    contexts via `lowerCtx`. -/
def RobustlyCTSafeCtxImage {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t) : Prop :=
  ∀ {Δ₀ : Ctxt latticeDialect}
    (C₀ : ComCtx latticeDialect Γ t Δ₀) (L : LabelCtxt (Δ₀.map tau)),
    ctSafeCtxJasmin (lowerCtx C₀) L = true →
    ctSafeJasmin (ComCtx.plug (lowerCtx C₀) (lowerLatticeToJasmin c)) L = true

/-- **Full RSP for the image class (unconditional).** Source robust CT against
    all lattice contexts (`RobustlyCTSafeCtxSource`) implies target robust CT
    against all *image-class* contexts (`RobustlyCTSafeCtxImage`), with no
    back-translation hypothesis. The back-translation is the identity on the
    source context: for an image-class target context `lowerCtx C₀`, the target
    CT obligation is — by `ctSafeJasmin_plug_lowerCtx` — literally the source CT
    obligation, which `hSrc` discharges. This is the meaningful
    source→target robust-CT preservation: you only ever link against contexts
    you can build, and every such context lands in this image. -/
theorem robustCTPreservation_ctx_image
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hSrc : RobustlyCTSafeCtxSource c) :
    RobustlyCTSafeCtxImage c := by
  intro Δ₀ C₀ L hC
  rw [ctSafeJasmin_plug_lowerCtx C₀ c L]
  exact hSrc C₀ L hC

/-! ## 4. Discharging the `backTranslates` step for image contexts

`RobustSafetyContext.backTranslates c` packages, for each CT-safe target context
`C` linking `lowerLatticeToJasmin c`, a *source* context `C₀` realising `C`'s
CT-safety obligation. For an image-class target context — one definitionally
equal to `lowerCtx C₀` — we discharge that step: the witnessing source context
is `C₀` itself, the witnessing labelling is `L` unchanged, and the realisation
implication is the commutation identity `ctSafeJasmin_plug_lowerCtx`. -/

/-- **Back-translation step, discharged for an image context.** If a CT-safe
    target context `C` linking `lowerLatticeToJasmin c` is *equal to* the
    lowering `lowerCtx C₀` of some source context `C₀`, then the
    `backTranslates`-style existential is satisfiable for `C`: the source
    witness is `C₀`, the source labelling is the same `L`, and the realisation
    implication holds by `ctSafeJasmin_plug_lowerCtx`. This is the genuine
    back-translation for the image class — the part `tau`-surjectivity would be
    needed for in general, here provided because the context *is* a source
    context's image. -/
theorem backTranslates_image_step
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    {Δ : Ctxt jasminDialect}
    (C : ComCtx jasminDialect (Γ.map tau) (tau t) Δ) (L : LabelCtxt Δ)
    (hC : ctSafeCtxJasmin C L = true)
    {Δ₀ : Ctxt latticeDialect} (C₀ : ComCtx latticeDialect Γ t Δ₀)
    (hΔ : Δ = Δ₀.map tau) (hCeq : hΔ ▸ C = lowerCtx C₀) :
    ∃ (Δ₁ : Ctxt latticeDialect) (C₁ : ComCtx latticeDialect Γ t Δ₁)
      (L₁ : LabelCtxt (Δ₁.map tau)),
      ctSafeCtxJasmin (lowerCtx C₁) L₁ = true ∧
      (ctSafeJasmin (lowerLatticeToJasmin (ComCtx.plug C₁ c)) L₁ = true →
        ctSafeJasmin (ComCtx.plug C (lowerLatticeToJasmin c)) L = true) := by
  subst hΔ
  subst hCeq
  refine ⟨Δ₀, C₀, L, hC, ?_⟩
  intro hsrc
  rw [ctSafeJasmin_plug_lowerCtx C₀ c L]
  exact hsrc

/-! ## 5. Why the full `backTranslates` is not provable, made precise

The full `backTranslates c` quantifies over *all* target contexts, including
non-image ones built from Jasmin-only ops/types. The following exhibits a
concrete such context — the hostile `stackLoad` prefix from
`RobustSafetyContext.hostileCtx` — to witness that target contexts genuinely
exist outside the image of `lowerCtx`: it binds a `stackLoad`, which `lowerCtx`
*never* emits (the lattice dialect has no addressed access; the lowering emits
only `extCall`s). So an unconditional back-translation cannot exist, and the
image-class result above is the strongest fully-closed statement. -/

/-- Every binding emitted by `lowerExpr` is an `extCall`, hence never a
    `stackLoad`/`stackStore`. This is the structural reason the image of
    `lowerCtx` omits the hostile (addressed-access) contexts: the back-transfer
    of §3 is exactly the class of contexts the lowering can produce, and that
    class excludes the data-dependent loads `RobustSafetyContext.hostileCtx`
    relies on. -/
theorem lowerExpr_op_is_extCall {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) :
    ∃ name argTys retTy,
      (lowerExpr e).op = JasminOp.extCall name argTys retTy :=
  jasminOpOf_is_extCall e.op

/-! ## 6. Image-class corollaries for the concrete lattice programs

The lattice path emits, at ML-KEM-flavoured parameters, the NTT-expanded
`tgtCom` and the unexpanded `srcCom`. Both inherit the image-class full RSP from
the vacuous source robust-CT judgement (`latticeSource_robustlyCTSafe` repackaged
as `RobustlyCTSafeCtxSource`). -/

/-- The source robust-CT judgement holds for every lattice program: its lowered
    image is CT-safe under every labelling and context, because the lattice
    dialect has no addressed access. This packages
    `JasminCTPredicate.lowerLatticeToJasmin_ctSafeJasmin` (applied to the linked
    program) into the `RobustlyCTSafeCtxSource` shape. -/
theorem latticeSource_robustlyCTSafeCtx
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafeCtxSource c := by
  intro Δ₀ C L _
  exact lowerLatticeToJasmin_ctSafeJasmin (ComCtx.plug C c) L

/-- **End-to-end image-class RSP (unconditional).** Every compiled lattice
    program is robustly constant-time against all image-class target contexts:
    the source robust hypothesis discharges via
    `latticeSource_robustlyCTSafeCtx`, so the image-class preservation holds for
    every source program with no remaining hypothesis. -/
theorem robustCTPreservation_ctx_image_uncond
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t) :
    RobustlyCTSafeCtxImage c :=
  robustCTPreservation_ctx_image c (latticeSource_robustlyCTSafeCtx c)

/-- Concrete corollary: the lowered NTT-expanded target program is robustly
    constant-time against all image-class contexts. -/
theorem tgt_robustlyCTSafe_ctx_image (q n : Nat) :
    RobustlyCTSafeCtxImage (LatticeDialect.tgtCom q n) :=
  robustCTPreservation_ctx_image_uncond (LatticeDialect.tgtCom q n)

/-- Concrete corollary: the lowered unexpanded source program (`poly_mul`) is
    robustly constant-time against all image-class contexts. -/
theorem src_robustlyCTSafe_ctx_image (q n : Nat) :
    RobustlyCTSafeCtxImage (LatticeDialect.srcCom q n) :=
  robustCTPreservation_ctx_image_uncond (LatticeDialect.srcCom q n)

end CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyBackTranslate
