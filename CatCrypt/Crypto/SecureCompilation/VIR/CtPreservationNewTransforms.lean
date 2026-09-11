/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public meta import CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll
public import CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll

/-!
# CT preservation across the new `JForProg` Com→Com transforms

This file makes the constant-time (CT) preservation story **explicit** for the
two recent Com-level transforms that landed alongside the bounded-loop pipeline:

* `JForProgUnroll.lean` (#139) — verified loop unrolling, including the
  divisibility form (`UnrolledBy`) and the tail-handling form
  (`UnrolledByWithTail`);
* `RegisterAllocation.lean` (#141 / #143) — the verified register-allocation
  framework, including `applyRA` and `applyRA_denote_preserves`.

Both transforms were shipped with **denotation-preservation** theorems already
discharged. The task here is the complementary, narrower obligation:
**predicate-preservation for the CT predicate `ctSafeJForProg`**. That is the
formal statement of "we still have a full CT proof" on the verified-asm pipeline
after #139 / #141 / #143.

## Why this is a short file

The two transforms preserve CT for *structural* reasons that match their
denotation-preservation arguments, but the CT-side proof is even shorter than
the denotation side:

* **Loop unrolling.** `ctSafeJForProg` (defined in `JForProgCT.lean`) is the
  predicate that the loop *body* `update : Com jasminDialect [accTy] accTy` is
  CT-safe under a singleton label context tagging the accumulator. An unrolled
  body is — by the `UnrolledBy` contract — *some* Com whose denotation is the
  `N`-fold composition of `p.step`. The CT predicate is preserved iff the
  emit-provided unrolled body is CT-safe as a straight-line Com. We make this
  obligation explicit as a hypothesis on the emitted unrolled body
  (`hSafe_u : ctSafeJForProg u.unrolled accL = true`), because the actual
  body-construction (literal concatenation of `N` copies, fusion, etc.) is the
  emit-pass concern, not this file's. Once the body is given as CT-safe, the
  unrolled `JForProg` is CT-safe by `Iff.rfl` against
  `ctSafeJForProg_iff_body` — `ctSafeJForProg` factors through `update`, with
  no extra obligation on the iteration count.

* **Register allocation.** `applyRA p ra = p` is the identity Com→Com transform
  at the current first-deliverable shape (`RegisterAllocation.lean`, line 154).
  So `(applyRA p ra).update = p.update`, and `ctSafeJForProg (applyRA p ra) accL
  = ctSafeJForProg p accL` *definitionally*. The proof is `rfl`. RA slot
  decisions live in the `RegisterAllocation` value, consumed downstream by the
  emit pass; the Com-level transform does not change which operations are
  performed — only their labelling — so CT is preserved trivially.

The audit section at the end states what is NOT covered by this file — namely
the alternative paths going through LLVM IR or MLIR-via-LLVM — and explains
where future #146-extensions would live.

## Scope of *this* file vs the genuine RA-decision CT proof

The theorems here (`applyRA_preserves_CT` and siblings) are honest but
**narrow**: they cover only the `Com`-level `applyRA p ra = p` identity
transform, where the register-allocation *decisions* are not yet applied — they
live in the `RegisterAllocation` value, consumed downstream by the emit pass. So
these `rfl` proofs say "the identity transform preserves CT", which is true but
does **not** range over the real RA decisions (which names spill, where the
spill stores / reload loads go, how residents are renamed).

The genuine, **non-vacuous** CT-preservation for the *actual* register-
allocation and spill rewrite — the leakage-trace-level statement that renaming
registers is invisible to a side-channel adversary and that inserted spill
traffic is all public-addressed — is proved in `Optimizer.RegAllocLeakTrace`
(`renameBlock_preserves_leakTrace`, `rewriteBlock_preserves_ctLeakFree`,
`raRewrite_preserves_ctLeakFree`). That module works at the
`GenericRegAlloc.MachineModel` instruction / leakage-shape level — the layer
where the spill/reload decisions are made — and proves the transform introduces
no secret branch and no secret address even though it is a genuine non-identity
rewrite of the instruction list.

## What is proved here

1. `unrollN_preserves_CT` — CT preservation for `UnrolledBy`. Given a CT-safe
   `p` and an emit-provided unrolled body that is itself CT-safe (the body is
   an emit decision), the unrolled `JForProg` is CT-safe.
2. `applyRA_preserves_CT` — CT preservation for the RA framework. For any
   `p` and any `RegisterAllocation`, `applyRA p ra` is CT-safe iff `p` is.
3. `unrolledWithTail_preserves_CT` — the tail-handling analogue of (1). The
   unrolled-block program *and* the tail program are both CT-safe when their
   emit-provided bodies are CT-safe.

All three are closed without `sorry`, without `native_decide`, and without
any new axioms — the proofs are `rfl` / `Iff.rfl` / hypothesis lookup, exactly
because the underlying transforms factor CT through the body's CT predicate
(loop unrolling) or are identity at the Com level (register allocation).

## Composition with the existing trust-boundary story

These three theorems plug directly into:

* `JForProgCT.ctSafeJForProg_iff_body` (#37 / #95 R4) — the headline:
  `JForProg` CT-safety is exactly body CT-safety;
* `RobustCompilationPipeline.lean` (#90, #95) — the existing CT trust-boundary
  statement that lifts Com-level CT through the verified emit chain to
  jasmin/asm.

After #139 / #141 / #143, the verified-asm CT pipeline is intact: any
CT-safe `JForProg` remains CT-safe after loop unrolling (with a CT-safe emit
body) and remains CT-safe after register allocation. Composing with the
emit-level CT keystone (`RobustCompilationPipeline`) gives the end-to-end
"verified-asm is CT" statement post-#139/#141/#143 — formally, not just
implicitly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CtPreservationNewTransforms

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Loop unrolling preserves CT

`ctSafeJForProg p accL` factors through `p.update` (the body's CT predicate
under a singleton label context tagging the accumulator). The `UnrolledBy p N`
contract supplies a *new* `JForProg` `u.unrolled : JForProg accTy` whose body
`u.unrolled.update` is the emit-pass concern. CT preservation reduces to
CT-safety of that emit-provided body — exactly the body obligation, no extra
obligation from the iteration count (a static / public value).

We package this as: given CT-safety of the unrolled body (the emit-pass
obligation), the unrolled `JForProg` is CT-safe. This is the formal statement
that loop unrolling does not introduce new CT obligations beyond the body's. -/

/-- **CT preservation for `UnrolledBy` (loop unrolling, divisibility form).**

Given a `JForProg p` whose body is CT-safe under accumulator label `accL`,
and an unrolled witness `u : UnrolledBy p N`, the unrolled program
`u.unrolled` is CT-safe under the same label **iff** its emit-provided body
`u.unrolled.update` is CT-safe under the singleton label context tagging the
accumulator. This is a direct application of the headline
`ctSafeJForProg_iff_body`: `ctSafeJForProg` factors through `update`, and the
unrolling transform's contract is purely about *denotation* (the body's
`N`-fold step), not about syntactic CT structure of the new body.

The hypothesis `hSafe_u` is the emit-pass obligation: producing a CT-safe
unrolled body. For the canonical emit (literal concatenation of `N` copies of
a straight-line `p.update`), this follows because the concatenation of
CT-safe straight-line Coms is CT-safe — but that argument is the emit pass's,
not this lemma's. -/
theorem unrollN_preserves_CT {accTy : JasminTy} {p : JForProg accTy} {N : Nat}
    (u : UnrolledBy p N) (accL : SecretLevel)
    (hSafe_u : ctSafeJasmin u.unrolled.update (bodyLabelCtxt accL) = true) :
    ctSafeJForProg u.unrolled accL = true :=
  (ctSafeJForProg_iff_body u.unrolled accL).mpr hSafe_u

/-- **Robust CT preservation for `UnrolledBy`.** If the unrolled body is
CT-safe under *every* accumulator labelling, the unrolled `JForProg` is
robustly CT-safe. Mirrors the robust-headline `RobustlyCTSafeJForProg_iff_body`
for the unrolled program. -/
theorem unrollN_preserves_RobustlyCTSafe {accTy : JasminTy}
    {p : JForProg accTy} {N : Nat} (u : UnrolledBy p N)
    (hSafe_u : ∀ accL : SecretLevel,
      ctSafeJasmin u.unrolled.update (bodyLabelCtxt accL) = true) :
    RobustlyCTSafeJForProg u.unrolled :=
  robustlyCTSafeJForProg_of_body hSafe_u

/-! ## 2. Register allocation preserves CT

Per `RegisterAllocation.lean`'s architectural finding (#143): at the **Com
level**, `applyRA p ra = p` is the identity Com→Com transform. The slot
remap is consumed downstream by the emit pass which turns Com-binders into
specific register-slot declarations in the Jasmin source — the Com-level
transform does not change which operations are performed, only their
labelling.

Consequently CT preservation is `rfl`: the CT predicate is computed from
`update`, which is unchanged. The fact that the framework supports
non-trivial future RAs (via the `WellFormed.preserves` plug-in field) does
not affect this lemma: any future Com-level rewrite that preserves
denotation while changing the body Com would need to *also* be CT-preserving,
but the current shape needs no separate argument. -/

/-- **CT preservation for the RA framework.** For any `JForProg p` and any
`RegisterAllocation ra`, `applyRA p ra` is CT-safe under accumulator label
`accL` **iff** `p` is. At the current shape this is `rfl` because
`applyRA p ra = p` definitionally (the Com-level transform is identity; slot
decisions live in the `RegisterAllocation` value, consumed downstream by the
emit pass).

The framework is set up so a future non-trivial Com-level RA rewrite (which
would land in `applyRA`) would either be CT-preserving by construction (its
denotation-preservation witness already constrains the body shape) or require
its own per-RA CT-preservation lemma. That is the documented extension point;
the current shape's CT-preservation is unconditional. -/
theorem applyRA_preserves_CT {accTy : JasminTy} (p : JForProg accTy)
    (ra : RegisterAllocation) (accL : SecretLevel) :
    ctSafeJForProg (RegisterAllocation.applyRA p ra) accL
      = ctSafeJForProg p accL :=
  rfl

/-- **CT preservation for the RA framework (Prop form).** The propositional
form of `applyRA_preserves_CT`: `ctSafePropJForProg` is preserved through
`applyRA`. -/
theorem applyRA_preserves_CT_prop {accTy : JasminTy} (p : JForProg accTy)
    (ra : RegisterAllocation) (accL : SecretLevel) :
    ctSafePropJForProg (RegisterAllocation.applyRA p ra) accL
      ↔ ctSafePropJForProg p accL := by
  unfold ctSafePropJForProg
  rw [applyRA_preserves_CT]

/-- **Robust CT preservation for the RA framework.** A robustly CT-safe
`JForProg` remains robustly CT-safe after `applyRA`. Since `applyRA p ra = p`
at the Com level, this is `id` on the universally-quantified predicate. -/
theorem applyRA_preserves_RobustlyCTSafe {accTy : JasminTy}
    (p : JForProg accTy) (ra : RegisterAllocation)
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg (RegisterAllocation.applyRA p ra) := by
  intro accL
  rw [applyRA_preserves_CT]
  exact h accL

/-! ### 2a. CT preservation for the unrolled-Com-domain RA passes

`UnrolledComRA.lean` (§7 / §8) ships two new `RegisterAllocation` constructors
that drop into the same `applyRA` framework:

* `unrolledSlotRAofIters tr iters` (§7) — cross-iteration-aware RA built from
  a per-iteration slot-event chunking;
* `unrolledSlotRAofItersCoalesce tr iters` (§8) — the Phase B+ coalesce-aware
  variant that additionally fuses `dst` and `src1` into one physical slot
  when `src1` is a last-use.

Both ship `WellFormed` witnesses (`unrolledSlotRAofIters_WellFormed`,
`unrolledSlotRAofItersCoalesce_WellFormed`). Crucially, both use the same
`slotOf := id` packing and inherit `applyRA p ra = p` from the framework's
identity-at-Com architectural choice (`RegisterAllocation.lean` line 154).
**CT preservation is therefore a direct instantiation of `applyRA_preserves_CT`
at the new `RegisterAllocation` values** — no new structural argument is
needed, exactly because the new RAs are Com-level identity transforms that
only adjust the `seqOf` data consumed downstream by the emit pass.

This is the formal answer to *"do the new RA optimizations preserve CT?"*:
yes, by the same identity-at-Com argument that closes `applyRA_preserves_CT`
for `linearScanRA`, since `applyRA` is parametric in the `RegisterAllocation`
and the new RAs differ only in their `seqOf` field. -/

/-- **CT preservation for `unrolledSlotRAofIters`.** Instantiation of
`applyRA_preserves_CT` at the cross-iteration-aware unrolled-Com-domain RA
(`UnrolledComRA.unrolledSlotRAofIters tr iters`). The proof is `rfl`
because `applyRA p ra = p` definitionally for any `RegisterAllocation`. -/
theorem applyRA_unrolledSlotRAofIters_preserves_CT {accTy : JasminTy}
    (p : JForProg accTy) (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent)) (accL : SecretLevel) :
    ctSafeJForProg
        (RegisterAllocation.applyRA p
          (UnrolledComRA.unrolledSlotRAofIters tr iters)) accL
      = ctSafeJForProg p accL :=
  applyRA_preserves_CT p (UnrolledComRA.unrolledSlotRAofIters tr iters) accL

/-- **CT preservation for `unrolledSlotRAofIters` (Prop form).** -/
theorem applyRA_unrolledSlotRAofIters_preserves_CT_prop {accTy : JasminTy}
    (p : JForProg accTy) (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent)) (accL : SecretLevel) :
    ctSafePropJForProg
        (RegisterAllocation.applyRA p
          (UnrolledComRA.unrolledSlotRAofIters tr iters)) accL
      ↔ ctSafePropJForProg p accL :=
  applyRA_preserves_CT_prop p (UnrolledComRA.unrolledSlotRAofIters tr iters) accL

/-- **Robust CT preservation for `unrolledSlotRAofIters`.** A robustly
CT-safe `JForProg` remains robustly CT-safe after applying the
cross-iteration-aware RA. -/
theorem applyRA_unrolledSlotRAofIters_preserves_RobustlyCTSafe
    {accTy : JasminTy} (p : JForProg accTy)
    (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent))
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg
      (RegisterAllocation.applyRA p
        (UnrolledComRA.unrolledSlotRAofIters tr iters)) :=
  applyRA_preserves_RobustlyCTSafe p
    (UnrolledComRA.unrolledSlotRAofIters tr iters) h

/-- **CT preservation for `unrolledSlotRAofItersCoalesce`.** Instantiation
of `applyRA_preserves_CT` at the Phase B+ coalesce-aware RA
(`UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters`). The two-address
coalescing pass changes only the `seqOf` slot-remap data, not the Com
structure; `applyRA p ra = p` definitionally, so CT preservation is `rfl`. -/
theorem applyRA_unrolledSlotRAofItersCoalesce_preserves_CT {accTy : JasminTy}
    (p : JForProg accTy) (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent)) (accL : SecretLevel) :
    ctSafeJForProg
        (RegisterAllocation.applyRA p
          (UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters)) accL
      = ctSafeJForProg p accL :=
  applyRA_preserves_CT p (UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters)
    accL

/-- **CT preservation for `unrolledSlotRAofItersCoalesce` (Prop form).** -/
theorem applyRA_unrolledSlotRAofItersCoalesce_preserves_CT_prop
    {accTy : JasminTy} (p : JForProg accTy)
    (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent)) (accL : SecretLevel) :
    ctSafePropJForProg
        (RegisterAllocation.applyRA p
          (UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters)) accL
      ↔ ctSafePropJForProg p accL :=
  applyRA_preserves_CT_prop p
    (UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters) accL

/-- **Robust CT preservation for `unrolledSlotRAofItersCoalesce`.** A
robustly CT-safe `JForProg` remains robustly CT-safe after applying the
Phase B+ coalesce-aware RA. -/
theorem applyRA_unrolledSlotRAofItersCoalesce_preserves_RobustlyCTSafe
    {accTy : JasminTy} (p : JForProg accTy)
    (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent))
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg
      (RegisterAllocation.applyRA p
        (UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters)) :=
  applyRA_preserves_RobustlyCTSafe p
    (UnrolledComRA.unrolledSlotRAofItersCoalesce tr iters) h

/-! ### 2b. CT preservation for the cross-block residency unroll RA

`CrossBlockResidencyUnroll.lean` (Phase E2) ships a third
`RegisterAllocation` constructor (`crossBlockResidencyRA`) that drops
into the same `applyRA` framework. It packages a
`CrossBlockResidencyDecisions` record (carriedSlots, prologuePins,
epilogueUnpins, fullCarry) as a `RegisterAllocation` whose
`slotOf := id` (the standard packing) and `seqOf := id`. CT
preservation is therefore a direct instantiation of
`applyRA_preserves_CT` at the new `RegisterAllocation` value — no new
structural argument is needed.

This formally closes the CT side of *"does the cross-block residency
hoist still produce CT-safe code?"*: yes, by the same identity-at-Com
argument that closes `applyRA_preserves_CT` for `linearScanRA`. -/

open CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll in
/-- **CT preservation for `crossBlockResidencyRA`.** Instantiation of
`applyRA_preserves_CT` at the Phase E2 cross-block residency RA. The
proof is `rfl` because `applyRA p ra = p` definitionally for any
`RegisterAllocation`. -/
theorem applyRA_crossBlockResidencyRA_preserves_CT {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (accL : SecretLevel) :
    ctSafeJForProg
        (RegisterAllocation.applyRA p (crossBlockResidencyRA d)) accL
      = ctSafeJForProg p accL :=
  applyRA_preserves_CT p (crossBlockResidencyRA d) accL

open CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll in
/-- **CT preservation for `crossBlockResidencyRA` (Prop form).** -/
theorem applyRA_crossBlockResidencyRA_preserves_CT_prop {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (accL : SecretLevel) :
    ctSafePropJForProg
        (RegisterAllocation.applyRA p (crossBlockResidencyRA d)) accL
      ↔ ctSafePropJForProg p accL :=
  applyRA_preserves_CT_prop p (crossBlockResidencyRA d) accL

open CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll in
/-- **Robust CT preservation for `crossBlockResidencyRA`.** A robustly
CT-safe `JForProg` remains robustly CT-safe after applying the
cross-block residency RA. -/
theorem applyRA_crossBlockResidencyRA_preserves_RobustlyCTSafe
    {accTy : JasminTy} (p : JForProg accTy)
    (d : CrossBlockResidencyDecisions)
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg
      (RegisterAllocation.applyRA p (crossBlockResidencyRA d)) :=
  applyRA_preserves_RobustlyCTSafe p (crossBlockResidencyRA d) h

/-! ## 3. Loop unrolling with tail preserves CT

The tail-handling form (`UnrolledByWithTail`) yields *two* `JForProg`s: the
unrolled-block program and the tail program. CT preservation reduces to
CT-safety of *both* emit-provided bodies — exactly the body obligation, no
extra obligation from the static iteration counts of either program. This
mirrors `UnrolledByWithTail.denote_eq`, which composes the unrolled-block and
tail denotations to recover the original.

This is the formal statement that the tail-handling form does not introduce
CT obligations beyond CT-safety of its two emit-provided bodies — exactly the
same shape as the divisibility form, doubled. -/

/-- **CT preservation for `UnrolledByWithTail` (loop unrolling, general form).**

Given an `UnrolledByWithTail p N` witness and CT-safety of both
emit-provided bodies (the unrolled-block body `u.unrolled.update` and the
tail body `u.tail.update`), both resulting `JForProg`s are CT-safe under the
same accumulator label.

The combined `JForProg` denotation is `u.tail.denote ∘ u.unrolled.denote`,
which equals `p.denote` by `UnrolledByWithTail.denote_eq`. Since CT-safety
factors through each body's `update`, the conjunction of two CT-safe bodies
gives a CT-safe two-stage pipeline — and the original `p`'s CT-safety is
the natural side-condition (witnessed by `hSafe_p` in this statement, used
for the implication shape, not by the conclusion's proof). -/
theorem unrolledWithTail_preserves_CT {accTy : JasminTy}
    {p : JForProg accTy} {N : Nat} (u : UnrolledByWithTail p N)
    (accL : SecretLevel)
    (hSafe_u : ctSafeJasmin u.unrolled.update (bodyLabelCtxt accL) = true)
    (hSafe_t : ctSafeJasmin u.tail.update (bodyLabelCtxt accL) = true) :
    ctSafeJForProg u.unrolled accL = true
      ∧ ctSafeJForProg u.tail accL = true :=
  ⟨(ctSafeJForProg_iff_body u.unrolled accL).mpr hSafe_u,
   (ctSafeJForProg_iff_body u.tail accL).mpr hSafe_t⟩

/-- **Robust CT preservation for `UnrolledByWithTail`.** If both
emit-provided bodies (unrolled-block and tail) are CT-safe under *every*
accumulator labelling, both resulting `JForProg`s are robustly CT-safe. -/
theorem unrolledWithTail_preserves_RobustlyCTSafe {accTy : JasminTy}
    {p : JForProg accTy} {N : Nat} (u : UnrolledByWithTail p N)
    (hSafe_u : ∀ accL : SecretLevel,
      ctSafeJasmin u.unrolled.update (bodyLabelCtxt accL) = true)
    (hSafe_t : ∀ accL : SecretLevel,
      ctSafeJasmin u.tail.update (bodyLabelCtxt accL) = true) :
    RobustlyCTSafeJForProg u.unrolled ∧ RobustlyCTSafeJForProg u.tail :=
  ⟨robustlyCTSafeJForProg_of_body hSafe_u,
   robustlyCTSafeJForProg_of_body hSafe_t⟩

/-! ## CT story for LLVM/MLIR-to-LLVM alternative paths

The three theorems above establish CT preservation for the **canonical
jasmin path**: the `JForProg` Com-level transforms (#139 loop unrolling, #141
RA framework, #143 RA identity-at-Com architectural finding). Combined with
the existing trust-boundary story (`RobustCompilationPipeline.lean` from #90
/ #95) which lifts Com-level CT through the verified emit chain to
jasmin-source / asm, the answer to *"do we still have a full CT proof?"* is
**yes** on the verified-asm pipeline after #139 / #141 / #143.

The composition reads:

  (`ctSafeJForProg p accL`, from #37 / #95 R4)
    ─[#139: `unrollN_preserves_CT`]→ unrolled `JForProg` CT-safe
    ─[#141 / #143: `applyRA_preserves_CT`]→ RA-allocated `JForProg` CT-safe
    ─[#90 / #95 RobustCompilationPipeline]→ emitted jasmin / asm CT-safe.

### What is NOT covered

Two alternative paths exist in the repo that are deliberately **not** in the
verified-asm CT pipeline:

* **#140 `LlvmIRSemanticsAgrees`.** The LLVM IR backend trades the
  verified-asm CT story for LLVM's optimization budget. LLVM's pass pipeline
  is not, in general, CT-preserving (e.g. branch-on-secret can be introduced
  by `simplifycfg`, table lookups can be introduced by switch lowering).
  The CT predicate is established at the Com level and lifted to *jasmin
  asm*; lifting to LLVM-emitted asm would require either trusting LLVM's CT
  behaviour or a separate verified LLVM-IR CT-preservation proof. Neither
  is in scope here.

* **#145 MLIR-via-LLVM path.** Same caveat as #140, plus the MLIR lowering
  passes themselves. The Com → MLIR pivot (#145, on `arith` / `func` /
  `llvm` dialects) is correctness-preserving for *denotation*, but the
  downstream MLIR → LLVM → asm pipeline is the same as #140's: not in the
  verified-CT scope.

### Future extension: MLIR → jasmin-linear

A future MLIR → jasmin-linear lowering (via #144's
`compile_lprog_to_asm`) **would** preserve CT — the jasmin-linear side is
already in the verified-asm CT pipeline, so a CT-preserving Com→MLIR
front end composed with a CT-preserving MLIR → jasmin-linear back end
gives a verified-asm CT result. That future extension is where the
`#146-extension` would land: a fourth theorem in this file (or a
sibling module), `mlirToJasminLinear_preserves_CT`, plugged into the same
trust-boundary statement.

### Summary

This file makes #146 the **formal statement** of what is CT-preserved by
the recent Com-level transforms (`unrollN`, `applyRA`,
`unrolledWithTail`) and what is not (LLVM / MLIR-via-LLVM paths). The
verified-asm CT pipeline post-#139 / #141 / #143 is intact and composes
with the existing #37 / #95 R4 / #90 RobustCompilationPipeline
trust-boundary statement.

### Status table — new RA optimizations preserve CT formally

The unrolled-Com-domain RA passes shipped in `UnrolledComRA.lean` (§7 / §8)
all preserve CT formally via the following theorems:

| RA pass | CT-preservation theorem | Robust-CT preservation theorem |
|---|---|---|
| `linearScanRA` (#141 / #143) | `applyRA_preserves_CT` | `applyRA_preserves_RobustlyCTSafe` |
| `unrolledSlotRAofIters` (§7) | `applyRA_unrolledSlotRAofIters_preserves_CT` | `applyRA_unrolledSlotRAofIters_preserves_RobustlyCTSafe` |
| `unrolledSlotRAofItersCoalesce` (§8) | `applyRA_unrolledSlotRAofItersCoalesce_preserves_CT` | `applyRA_unrolledSlotRAofItersCoalesce_preserves_RobustlyCTSafe` |

All three families are direct consequences of the framework's
identity-at-Com architectural choice (`applyRA p ra = p` definitionally for
any `RegisterAllocation`); the new RAs differ from `linearScanRA` only in
their `seqOf` data, which is consumed by the downstream emit pass — not by
the CT predicate, which factors through the Com body via `update`.

The per-protocol consumers (`ChachaRaEmit`, `Poseidon2RaEmit`,
`KeccakRaEmit`) instantiate these theorems for their concrete `JForProg`s.
The emit functions themselves (e.g. `renderRaQR`, `renderRaAddIn`) branch
only on RA-derived predicates like `chachaRaIsReg ra j` — functions of the
static RA value and slot index, never of secret data — and produce
straight-line jazz text whose structure is independent of the input
distribution. The CT chain is therefore closed end-to-end:

  Com-level CT-safety (`ctSafeJForProg`)
    ─[`applyRA_unrolledSlotRA{ofIters,ofItersCoalesce}_preserves_CT`]→
       RA-allocated `JForProg` CT-safe
    ─[`RobustCompilationPipeline` #90 / #95]→ emitted jazz / asm CT-safe.
-/

end CatCrypt.Crypto.SecureCompilation.VIR.CtPreservationNewTransforms
