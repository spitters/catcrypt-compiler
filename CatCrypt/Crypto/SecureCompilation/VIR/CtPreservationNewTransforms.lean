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

This file states preservation of the constant-time predicate `ctSafeJForProg`
for two `JForProg` constructions:

* `JForProgUnroll.lean` — loop unrolling, in the divisibility form
  (`UnrolledBy`) and the tail-handling form (`UnrolledByWithTail`);
* `RegisterAllocation.lean` — `RegisterAllocation.applyRA`, which is the
  identity.

## Proof shape

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

* **Register allocation.** `applyRA p ra = p` definitionally, so
  `ctSafeJForProg (applyRA p ra) accL = ctSafeJForProg p accL` holds by `rfl`
  for every allocation. These theorems state nothing about any allocation:
  which names spill, where spill stores and reloads go, or how residents are
  renamed.

## Register-allocation CT at the instruction level

CT preservation for a register renaming and spill rewrite of an instruction
list is proved in `Optimizer.RegAllocLeakTrace`
(`renameBlock_preserves_leakTrace`, `rewriteBlock_preserves_ctLeakFree`,
`raRewrite_preserves_ctLeakFree`), over the `GenericRegAlloc.MachineModel`
instruction and leakage-shape level: renaming registers leaves the leakage trace
unchanged, and inserted spill traffic is publicly addressed. The physical
allocator with a semantic theorem is `physScanSpill`
(`toLprogPhysAbi_faithful_uniform`).

## Contents

1. `unrollN_preserves_CT` — given an unrolled body that is CT-safe (a
   hypothesis on the emit-provided body), the unrolled `JForProg` is CT-safe.
2. `applyRA_preserves_CT` — `applyRA p ra` is CT-safe iff `p` is; `rfl`,
   because `applyRA` is the identity.
3. `unrolledWithTail_preserves_CT` — the tail-handling analogue of (1): the
   unrolled-block program and the tail program are CT-safe when their
   emit-provided bodies are.

The proofs are `rfl`, `Iff.rfl` or hypothesis lookup, with no `sorry`,
`native_decide` or axioms beyond the standard ones.

## Related statements

* `JForProgCT.ctSafeJForProg_iff_body` — `JForProg` CT-safety is body
  CT-safety.
* `RobustCompilationPipeline.lean` — lifts `Com`-level CT to the Jasmin and
  assembly levels.
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

/-! ## 2. `applyRA` preserves CT

`RegisterAllocation.applyRA p ra = p` definitionally, so the CT predicate,
computed from `update`, is unchanged; each theorem in this section is `rfl` or
follows from one that is, and holds for every allocation. -/

/-- For any `JForProg p` and any `RegisterAllocation ra`, `applyRA p ra` is
CT-safe under accumulator label `accL` iff `p` is. The proof is `rfl` because
`applyRA` is the identity; the statement says nothing about the allocation. -/
theorem applyRA_preserves_CT {accTy : JasminTy} (p : JForProg accTy)
    (ra : RegisterAllocation) (accL : SecretLevel) :
    ctSafeJForProg (RegisterAllocation.applyRA p ra) accL
      = ctSafeJForProg p accL :=
  rfl

/-- **CT preservation through `applyRA` (Prop form).** The propositional
form of `applyRA_preserves_CT`: `ctSafePropJForProg` is preserved through
`applyRA`. -/
theorem applyRA_preserves_CT_prop {accTy : JasminTy} (p : JForProg accTy)
    (ra : RegisterAllocation) (accL : SecretLevel) :
    ctSafePropJForProg (RegisterAllocation.applyRA p ra) accL
      ↔ ctSafePropJForProg p accL := by
  unfold ctSafePropJForProg
  rw [applyRA_preserves_CT]

/-- **Robust CT preservation through `applyRA`.** A robustly CT-safe
`JForProg` remains robustly CT-safe after `applyRA`. Since `applyRA p ra = p`,
this is `id` on the universally quantified predicate. -/
theorem applyRA_preserves_RobustlyCTSafe {accTy : JasminTy}
    (p : JForProg accTy) (ra : RegisterAllocation)
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg (RegisterAllocation.applyRA p ra) := by
  intro accL
  rw [applyRA_preserves_CT]
  exact h accL

/-! ### 2a. CT preservation for the unrolled-Com-domain RA passes

`UnrolledComRA.lean` (§7 / §8) defines two `RegisterAllocation` values:

* `unrolledSlotRAofIters tr iters` (§7) — cross-iteration-aware allocation
  built from a per-iteration slot-event chunking;
* `unrolledSlotRAofItersCoalesce tr iters` (§8) — the coalesce-aware variant
  that additionally fuses `dst` and `src1` into one physical slot when `src1`
  is a last use.

Both have `slotOf := id` and `WellFormed` witnesses
(`unrolledSlotRAofIters_WellFormed`, `unrolledSlotRAofItersCoalesce_WellFormed`).
The theorems below instantiate `applyRA_preserves_CT` at them. Because `applyRA`
is the identity, they say nothing about the CT behaviour of text rendered
through these allocations' `seqOf`. -/

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

`CrossBlockResidencyUnroll.lean` defines `crossBlockResidencyRA`, which
packages a `CrossBlockResidencyDecisions` record (carriedSlots, prologuePins,
epilogueUnpins, fullCarry) as a `RegisterAllocation` with `slotOf := id` and
`seqOf := id`. The theorems below instantiate `applyRA_preserves_CT` at it;
they hold because `applyRA` is the identity and say nothing about the
residency decisions. -/

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

/-! ## Scope

The theorems above concern `ctSafeJForProg` of `JForProg` values. For loop
unrolling they reduce to CT-safety of the emit-provided bodies. For register
allocation they are `rfl`, because `applyRA` is the identity: the `JForProg`
after `applyRA` is the program before it, and no theorem here concerns text
rendered through an allocation's `seqOf`. `RobustCompilationPipeline.lean` lifts
`Com`-level CT to the Jasmin and assembly levels.

### Paths outside this file

Two alternative paths exist in the repo that are deliberately **not** in the
verified-asm CT pipeline:

* **LLVM IR backend.** The LLVM IR backend trades the
  verified-asm CT story for LLVM's optimization budget. LLVM's pass pipeline
  is not, in general, CT-preserving (e.g. branch-on-secret can be introduced
  by `simplifycfg`, table lookups can be introduced by switch lowering).
  The CT predicate is established at the Com level and lifted to *jasmin
  asm*; lifting to LLVM-emitted asm would require either trusting LLVM's CT
  behaviour or a separate verified LLVM-IR CT-preservation proof. Neither
  is in scope here.

* **MLIR-via-LLVM path.** Same caveat as the LLVM IR backend, plus the MLIR
  lowering passes themselves. The Com → MLIR lowering (on `arith` / `func` /
  `llvm` dialects) is correctness-preserving for *denotation*, but the
  downstream MLIR → LLVM → asm pipeline is the same as the LLVM IR backend's:
  not in the verified-CT scope.

### Theorem index for allocations

| Allocation | CT theorem | Robust-CT theorem |
|---|---|---|
| any (`linearScanRA` included) | `applyRA_preserves_CT` | `applyRA_preserves_RobustlyCTSafe` |
| `unrolledSlotRAofIters` (§7) | `applyRA_unrolledSlotRAofIters_preserves_CT` | `applyRA_unrolledSlotRAofIters_preserves_RobustlyCTSafe` |
| `unrolledSlotRAofItersCoalesce` (§8) | `applyRA_unrolledSlotRAofItersCoalesce_preserves_CT` | `applyRA_unrolledSlotRAofItersCoalesce_preserves_RobustlyCTSafe` |
| `crossBlockResidencyRA` | `applyRA_crossBlockResidencyRA_preserves_CT` | `applyRA_crossBlockResidencyRA_preserves_RobustlyCTSafe` |

Each holds because `applyRA p ra = p` definitionally. The emit functions of
`ChachaRaEmit`, `Poseidon2RaEmit` and `KeccakRaEmit` read an allocation's
`seqOf` when rendering text; no theorem in this file concerns that text. CT of
a register renaming and spill rewrite at the instruction level is
`Optimizer.RegAllocLeakTrace.raRewrite_preserves_ctLeakFree`.
-/

end CatCrypt.Crypto.SecureCompilation.VIR.CtPreservationNewTransforms
