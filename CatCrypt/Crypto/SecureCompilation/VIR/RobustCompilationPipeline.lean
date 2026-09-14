/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyBackTranslate
public import CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignment
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond

/-!
# Robust compilation source → x86: composition of the lattice → Jasmin → x86 path

This file composes three results on the shared ANF `Com` substrate and its
emission into source → x86 statements for the lattice → Jasmin → x86 path:

1. **Com-level robust constant-time safety** — the lattice → Jasmin lowering is
   robustly CT-safe against every CT-safe linking context
   (`RobustSafetyContext.lowerLatticeToJasmin_robustlyCTSafe_ctx`), and the
   image-class RSP holds without a back-translation hypothesis
   (`RobustSafetyBackTranslate.robustCTPreservation_ctx_image_uncond`).
2. **Semantics preservation of the lowering** — running the emitted jasmin
   program under the Lean evaluator `runProg` equals the source `Com` denotation
   (`JasminPrintSemCorrect.lowerComToProg_sem_eq`, under its hypotheses
   `LeafAgrees`, `StraightLine`, and injectivity of `freshName` and of the
   parameter resolver), composed with the dialect-lowering denotation
   preservation (`LatticeToJasminDenoteUncond.lowerLatticeToJasmin_denote_eq_uncond`).
3. **Per-opcode alignment with Lean transcriptions of jasmin's `psem`** —
   `JasmincSemAlignment.opcode_alignment_total` proves, for every
   `JasminBinOp` operator of `regArith`, for `castW`, and for the
   `stackLoad`/`stackStore` element accessors, that the evaluator's primitive
   equals a Lean `def` transcribing the corresponding Coq `psem` primitive
   (`jWordOp`, `jZeroExt`, `jArrGetEl`, `jArrSetEl`); each row is `rfl`. The
   faithfulness of those transcriptions to the Coq definitions is not proved in
   Lean. The `extCall` row is the predicate
   `JasmincSemAlignment.ExtCallAgrees`, which is the `LeafAgrees` hypothesis.
   `vv_lane_agrees_jasmin` / `gf_vv_agrees_jasmin` state the analogous rows for
   the SIMD/GF lanes.

The composition uses these results as lemmas and does not re-prove them.

## The jasmin IR → x86 edge as a hypothesis record

Below the emitted jasmin IR, the path relies on jasmin's Coq
compiler-correctness theorem `compile_prog_to_asmP`
(`proofs/compiler/compiler_proof.v` in the jasmin development): the source
program under `psem` (`sem_call`) refines the generated x86
(`asmsem_exportcall`), together with jasmin's CT-preservation results (Barthe et
al.). These are Coq theorems. This file does not axiomatise them; it carries the
edge as the hypothesis record **`JasminIRToX86`**, in the same way
`JasminPrintSemCorrect` carries the opaque-leaf edge `LeafAgrees`. The record
has two fields:

* `semRefine` — the x86 observable of a program on an input is a decode
  `obsOf` of the program's result under the Lean evaluator `runProg`. This
  corresponds to the value half of `compile_prog_to_asmP`; obtaining it from the
  Coq theorem additionally requires that `runProg` agree with `psem` on the
  whole program, for which item 3 records the per-opcode rows;
* `ctPreserve` — a program that is `RobustlyCTSafe` at the Com / jasmin-IR level
  satisfies the x86-level CT predicate (the CT-preservation half).

`x86Behaviour` / `x86CTSafe` are the abstract x86-side observable and CT
predicate the record is parametric in. The record `JasminVerifiedCompiler`
has an additional field `psemFaithful`, which follows from `semRefine`
(`JasminVerifiedCompiler.ofIRToX86`). The theorems below prove the source → x86
conclusions from such a record together with the hypotheses `LeafAgrees`,
injectivity of `freshName`, and injectivity of the parameter resolver.
`trust_boundary_is_jasmin_ir_to_x86` states the conclusion from a
`JasminIRToX86` record.

## What is proved here

* `lowerLatticeToJasmin_straightLine` — the lowering emits only `extCall`s, so the
  emitted jasmin `Com` is straight-line: the side condition of
  `lowerComToProg_sem_eq` is met for every lattice program.
* `source_to_evaluator_behaviour` — source → emitted-jasmin behaviour
  preservation: `runProg` of the lowered program on the transported valuation is
  `transTy` of the source denotation (composition of `lowerComToProg_sem_eq` and
  the dialect lowering preservation), under `hLeaf`, `hInj`, `hPinj`.
* `robustCompilation_source_to_x86` — given a `JasminVerifiedCompiler` record and
  `hLeaf`, `hInj`, `hPinj`, every compiled lattice program satisfies (i) the x86
  observable on the transported input is `obsOf` of `transTy` of the source
  denotation and (ii) the lowered program satisfies `x86CTSafe`. The proof uses
  results (1)–(2) and the record's `semRefine` and `ctPreserve` fields.
* `robustCompilation_source_to_x86_image` — the same conclusion with the CT half
  obtained from the context-level guarantee, additionally returning
  `RobustlyCTSafeCtx` of the lowered program and `RobustlyCTSafeCtxImage` of the
  source.
* `trust_boundary_is_jasmin_ir_to_x86` — the conclusion of
  `robustCompilation_source_to_x86` from a `JasminIRToX86` record, with the same
  hypotheses `hLeaf`, `hInj`, `hPinj`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyBackTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The emitted jasmin `Com` is straight-line

`lowerComToProg_sem_eq` ranges over `StraightLine` programs: every binder
is `regArith`/`castW`/`stackLoad`/`extCall`, never the aliasing `stackStore`.
The lattice → Jasmin lowering emits only `extCall` ops
(`jasminOpOf_is_extCall`), so its output is straight-line and the side
condition holds for every lattice program. -/

/-- A lowered expression's op is never `stackStore` (it is always an `extCall`),
    so it satisfies `ExprNotStackStore`. -/
theorem lowerExpr_notStackStore {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) :
    ExprNotStackStore (lowerExpr e) := by
  intro w n hop
  obtain ⟨name, argTys, retTy, hext⟩ := jasminOpOf_is_extCall e.op
  -- `(lowerExpr e).op = jasminOpOf e.op = extCall …`, which is not `stackStore`.
  rw [show (lowerExpr e).op = jasminOpOf e.op from rfl, hext] at hop
  exact JasminOp.noConfusion hop

/-- **The emitted jasmin `Com` is straight-line, for every lattice program.**
    The lowering emits only `extCall` bindings, none of which is the aliasing
    `stackStore`, so `lowerComToProg_sem_eq`'s straight-line side condition is met
    unconditionally. Proved by induction on the source `Com`. -/
theorem lowerLatticeToJasmin_straightLine :
    ∀ {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t),
      StraightLine (lowerLatticeToJasmin c)
  | _, _, .ret _ => trivial
  | _, _, .var e body => by
      rw [show lowerLatticeToJasmin (Com.var e body)
            = Com.var (lowerExpr e) (lowerLatticeToJasmin body) from rfl]
      exact ⟨lowerExpr_notStackStore e, lowerLatticeToJasmin_straightLine body⟩

/-! ## 2. Source → emitted-jasmin behaviour preservation

Composition of two semantics-preservation results: running the emitted jasmin
program under the Lean evaluator equals the lowered `Com` denotation
(`lowerComToProg_sem_eq`, the `runProg = Com.denote` half), and the lowered `Com`
denotation is `transTy` of the source denotation
(`lowerLatticeToJasmin_denote_eq_uncond`). The straight-line side condition is
discharged by §1; the remaining hypotheses (`LeafAgrees`, name/param injectivity)
are those of `lowerComToProg_sem_eq`. -/

/-- **Source → emitted-jasmin behaviour preservation.** For every source lattice
    program `c`, running the emitted jasmin program (`runProg`) on the transported
    parameter valuation `mapVal V` equals `transTy (c.denote V)` — the source
    program's denotation, transported along `tau`. This is `lowerComToProg_sem_eq`
    precomposed with the dialect-lowering preservation; the straight-line
    side condition is `lowerLatticeToJasmin_straightLine`. The hypotheses
    (`hLeaf`, `hInj`, `hPinj`) are the opaque-leaf and SSA-naming hypotheses of
    `lowerComToProg_sem_eq`. -/
theorem source_to_evaluator_behaviour {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s) (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    runProg leafSem (lowerLatticeToJasmin c) (mapVal V) = transTy (c.denote V) := by
  rw [lowerComToProg_sem_eq hLeaf hInj (lowerLatticeToJasmin c)
        (lowerLatticeToJasmin_straightLine c) hPinj (mapVal V)]
  exact lowerLatticeToJasmin_denote_eq_uncond c V

/-! ## 3. The jasmin compiler edge (jasmin IR → x86) as a hypothesis record

The final step relies on jasmin's Coq compiler-correctness theorem
`compile_prog_to_asmP` (`proofs/compiler/compiler_proof.v` in the jasmin
development): the source program **under jasmin's `psem`** refines the
generated x86, and the pipeline preserves constant-time. The following are
proved in Lean:

* the semantic preservation of the lattice → jasmin **lowering**
  (`lowerLatticeToJasmin`), as `lowerComToProg_sem_eq` composed with the
  dialect-lowering preservation, under `LeafAgrees` and the naming hypotheses;
* the **per-opcode rows** relating the evaluator's primitives to Lean
  transcriptions of jasmin's `psem` primitives
  (`JasmincSemAlignment.opcode_alignment_total`: every `JasminBinOp` operator
  of `regArith`, `castW`, and the `stackLoad`/`stackStore` element accessors,
  all `rfl`; the `extCall` row is the predicate `ExtCallAgrees`, and
  `JasmincWArrayAlignment` relates the element accessors to a byte-addressed
  array);
* the Com-level **robust constant-time** guarantee
  (`robustCTPreservation_uncond`, `lowerLatticeToJasmin_robustlyCTSafe_ctx`).

`compile_prog_to_asmP` is a Coq theorem. The jasmin IR → x86 edge is carried as
the hypothesis record `JasminIRToX86`, not as an axiom. It is parametric in:

* `X86Obs` — the type of x86-level observable behaviour (e.g. the export-call
  return value / final memory the attacker reads);
* `x86Behaviour` — what an emitted-and-compiled program observably computes on an
  input, as seen at the x86 level;
* `x86CTSafe` — the x86-level constant-time predicate (a leakage-trace property
  on the compiled assembly);

and has two fields, value refinement (stated against the Lean evaluator
`runProg`) and CT preservation. The record `JasminVerifiedCompiler` (below)
has the same fields plus a `psemFaithful` field, which follows from value
refinement (`JasminVerifiedCompiler.ofIRToX86`). The main theorems take a
`JasminVerifiedCompiler`; `trust_boundary_is_jasmin_ir_to_x86` takes a
`JasminIRToX86`. -/

/-- **The jasmin-IR → x86 hypothesis record.** Two obligations corresponding to
    jasmin's Coq compiler-correctness theorem `compile_prog_to_asmP` and its
    CT-preservation counterpart: value refinement, stated against the Lean
    evaluator `runProg`, and CT preservation. Deriving `semRefine` from the Coq
    theorem additionally requires `runProg` to agree with jasmin's `psem` on
    the program. Parametric in the x86-side observable `X86Obs`, behaviour
    `x86Behaviour`, and CT predicate `x86CTSafe`. Carried as a hypothesis, not
    an axiom. -/
structure JasminIRToX86
    (leafSem : LeafSem) (X86Obs : Type)
    (x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs)
    (x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop) where
  /-- **Value refinement (jasmin IR → x86).** The x86 observable of a program on
      an input is the decode (`obsOf`) of the program's result under the Lean
      evaluator `runProg`. This corresponds to the value-equivalence half of
      `compile_prog_to_asmP`, with `runProg` in place of jasmin's `psem`. -/
  obsOf : {t : JasminTy} → ⟦t⟧ → X86Obs
  semRefine : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
      (com : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      x86Behaviour com V = obsOf (runProg leafSem com V)
  /-- **CT preservation (jasmin IR → x86).** If the emitted program is CT-safe at
      the Com / jasmin-IR level under every labelling (`RobustlyCTSafe`),
      jasmin's compiler produces x86 that is CT-safe (`x86CTSafe`) — the
      constant-time-preservation half of the jasmin compiler proofs (Barthe et
      al.), the CT analogue of `compile_prog_to_asmP`. -/
  ctPreserve : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
      (com : Com jasminDialect Γ t),
      RobustlyCTSafe com → x86CTSafe com

/-- **The jasmin compiler edge with a `psemFaithful` field.** Carries the
    jasmin IR → x86 edge corresponding to `compile_prog_to_asmP`, parametric in
    the x86-side observable `X86Obs`, behaviour `x86Behaviour`, and CT predicate
    `x86CTSafe`.

    This is the record taken by `robustCompilation_source_to_x86` and
    `robustCompilation_source_to_x86_image`. Its `psemFaithful` field follows
    from `semRefine`: `JasminVerifiedCompiler.ofIRToX86` builds this record from
    a `JasminIRToX86` record. -/
structure JasminVerifiedCompiler
    (leafSem : LeafSem) (X86Obs : Type)
    (x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs)
    (x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop) where
  /-- **Evaluator-determined x86 behaviour.** Equal `runProg` (jasmin-IR)
      results give equal x86 behaviour. This is implied by `semRefine` (equal
      evaluator results decode to equal observables);
      `JasminVerifiedCompiler.ofIRToX86` derives it from a `JasminIRToX86`
      record. -/
  psemFaithful : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
      (com : Com jasminDialect Γ t) (V V' : Ctxt.Valuation Γ),
      runProg leafSem com V = runProg leafSem com V' →
      x86Behaviour com V = x86Behaviour com V'
  /-- **Value-refinement reflection.** The x86 observable of a program on an input
      is a function of the program's evaluator meaning — i.e. there is a decode
      `obsOf` from evaluator results to x86 observables through which
      `x86Behaviour` factors (corresponding to the value-equivalence half of
      `compile_prog_to_asmP`, with `runProg` in place of `psem`). -/
  obsOf : {t : JasminTy} → ⟦t⟧ → X86Obs
  semRefine : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
      (com : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      x86Behaviour com V = obsOf (runProg leafSem com V)
  /-- **CT preservation (jasmin IR → x86).** If the emitted program is CT-safe at the
      Com level under every labelling (the `RobustlyCTSafe` source-level CT
      guarantee), the jasmin pipeline produces x86 that is CT-safe
      (`x86CTSafe`) — the constant-time-preservation half of the jasmin
      compiler proofs (Barthe et al.). -/
  ctPreserve : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
      (com : Com jasminDialect Γ t),
      RobustlyCTSafe com → x86CTSafe com

/-- **`JasminVerifiedCompiler` from `JasminIRToX86`.** Builds a
    `JasminVerifiedCompiler` from a `JasminIRToX86` record. `psemFaithful`
    follows from `semRefine`: equal `runProg` results decode (via `obsOf`) to
    equal x86 observables; the other fields are copied. -/
def JasminVerifiedCompiler.ofIRToX86
    {leafSem : LeafSem} {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    {x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop}
    (jir : JasminIRToX86 leafSem X86Obs x86Behaviour x86CTSafe) :
    JasminVerifiedCompiler leafSem X86Obs x86Behaviour x86CTSafe where
  psemFaithful := fun com V V' h => by
    rw [jir.semRefine com V, jir.semRefine com V', h]
  obsOf := jir.obsOf
  semRefine := jir.semRefine
  ctPreserve := jir.ctPreserve

/-! ## 4. Robust compilation source → x86

Behaviour preservation source → x86 follows from
`source_to_evaluator_behaviour` (§2) decoded through the record's `semRefine`.
Robust CT at the x86 level follows from the Com-level robust-CT guarantee
(`RobustSafety.robustCTPreservation_uncond`, which rests on
`lowerLatticeToJasmin_ctSafeJasmin`) through the record's `ctPreserve`. -/

/-- **Robust compilation, source → x86.** Given a `JasminVerifiedCompiler`
    record `jvc` (the jasmin IR → x86 edge), the leaf hypothesis `hLeaf`, and
    the naming hypotheses `hInj` and `hPinj`, for every source lattice program
    `c` and every input valuation `V`:

    1. **Behaviour preservation to x86.** The x86 observable `x86Behaviour` of
       the lowered program on the transported input `mapVal V` is the decode
       (`jvc.obsOf`) of `transTy (c.denote V)`, the source program's meaning
       transported along `tau`.
    2. **Constant-time at x86.** The lowered program satisfies `x86CTSafe`.
       This composes the Com-level robust-CT guarantee
       (`robustCTPreservation_uncond`, which rests on
       `lowerLatticeToJasmin_ctSafeJasmin`) with the record's `ctPreserve`
       field.

    The proof composes existing results. The hypotheses are `jvc` (the jasmin
    IR → x86 edge corresponding to Coq's `compile_prog_to_asmP`, carried as a
    record, not an axiom), `hLeaf`, `hInj` and `hPinj`. -/
theorem robustCompilation_source_to_x86
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    {x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop}
    (jvc : JasminVerifiedCompiler leafSem X86Obs x86Behaviour x86CTSafe)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s) (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    x86Behaviour (lowerLatticeToJasmin c) (mapVal V)
        = jvc.obsOf (transTy (c.denote V))
      ∧ x86CTSafe (lowerLatticeToJasmin c) := by
  refine ⟨?_, ?_⟩
  · -- Behaviour: decode the source→evaluator preservation (§2) through `semRefine`.
    rw [jvc.semRefine (lowerLatticeToJasmin c) (mapVal V),
      source_to_evaluator_behaviour hLeaf hInj c hPinj V]
  · -- Robust CT: Com-level robust-CT guarantee through `ctPreserve`.
    exact jvc.ctPreserve (lowerLatticeToJasmin c) (robustCTPreservation_uncond c)

/-! ## 5. Routing through the image-class full RSP back-translation

`RobustSafetyBackTranslate.robustCTPreservation_ctx_image_uncond` is the
*image-class* full RSP: source robust CT against all lattice contexts implies
target robust CT against all image-class (buildable-by-lowering) target contexts,
without a back-translation hypothesis. The theorem of §4 uses the
labelling-level robust-CT guarantee (`robustCTPreservation_uncond`); the theorem
below uses the context-level (`Com`-with-a-hole) judgement and also returns it.
The x86-CT side condition the record consumes is the labelling specialisation
(`RobustlyCTSafeCtx.toRobustlyCTSafe`), so the x86-CT conjunct is the same
predicate as in §4. -/

/-- **Robust compilation source → x86, via the context model.** Under the same
    hypotheses as `robustCompilation_source_to_x86` (`jvc`, `hLeaf`, `hInj`,
    `hPinj`), the same two conjuncts hold, with the CT half obtained from the
    context-level guarantee
    `RobustSafetyContext.lowerLatticeToJasmin_robustlyCTSafe_ctx` (robust CT
    against all CT-safe `Com`-with-a-hole linking contexts), specialised to the
    record's labelling-level CT field via `toRobustlyCTSafe`. The conclusion
    additionally contains `RobustlyCTSafeCtx (lowerLatticeToJasmin c)` and
    `RobustlyCTSafeCtxImage c` (`robustCTPreservation_ctx_image_uncond`): the
    lowered program plugged into the lowering `lowerCtx C₀` of any lattice
    context `C₀` is CT-safe under every labelling for which that lowered
    context is CT-safe. -/
theorem robustCompilation_source_to_x86_image
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    {x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop}
    (jvc : JasminVerifiedCompiler leafSem X86Obs x86Behaviour x86CTSafe)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s) (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    x86Behaviour (lowerLatticeToJasmin c) (mapVal V)
        = jvc.obsOf (transTy (c.denote V))
      ∧ x86CTSafe (lowerLatticeToJasmin c)
      ∧ RobustlyCTSafeCtx (lowerLatticeToJasmin c)
      ∧ RobustlyCTSafeCtxImage c := by
  -- The `Com`-with-a-hole robust-CT guarantee (no hypotheses).
  have hctx : RobustlyCTSafeCtx (lowerLatticeToJasmin c) :=
    lowerLatticeToJasmin_robustlyCTSafe_ctx c
  refine ⟨?_, ?_, hctx, robustCTPreservation_ctx_image_uncond c⟩
  · rw [jvc.semRefine (lowerLatticeToJasmin c) (mapVal V),
      source_to_evaluator_behaviour hLeaf hInj c hPinj V]
  · -- x86-CT from the context-level guarantee, specialised to labellings.
    exact jvc.ctPreserve (lowerLatticeToJasmin c) hctx.toRobustlyCTSafe

/-! ## 6. Per-opcode alignment rows, re-exported

`JasmincSemAlignment` proves per-opcode rows relating the evaluator's primitives
to Lean `def`s that transcribe jasmin's Coq `psem` primitives
(`opcode_alignment_total`): for every `JasminBinOp` operator of `regArith`
(`JasminBinOp.apply bop = jWordOp bop`), for `castW` (`zeroExtend = jZeroExt`),
and for the `stackLoad`/`stackStore` element accessors (`stackGet = jArrGetEl`,
`stackSet = jArrSetEl`), all definitional. The `extCall` row is the predicate
`ExtCallAgrees`, and `JasmincWArrayAlignment` relates the element accessors to
a byte-addressed array. These rows concern the transcriptions; their
faithfulness to the Coq definitions is not proved in Lean. They do not
discharge a field of `JasminIRToX86`: `semRefine` is stated against `runProg`
and remains a hypothesis. -/

/-- The ALU/cast per-opcode rows, re-exported: for every `JasminBinOp` operator,
    `JasminBinOp.apply` equals the transcription `jWordOp`, and `zeroExtend`
    equals the transcription `jZeroExt`
    (`JasmincSemAlignment.alu_cast_agrees_jasmin`). -/
theorem psem_alu_cast_discharged :
    (∀ {w : Nat} (bop : JasminBinOp) (a b : BitVec w),
        JasminBinOp.apply bop a b = JasmincSemAlignment.jWordOp bop a b)
    ∧ (∀ {w w' : Nat} (src : BitVec w),
        src.zeroExtend w' = JasmincSemAlignment.jZeroExt w' src) :=
  JasmincSemAlignment.alu_cast_agrees_jasmin

/-- **The per-opcode rows for the non-`extCall` ops, re-exported.** For every
    `jasminDialect` op other than `extCall`, the evaluator's primitive equals
    the Lean transcription of the corresponding jasmin `psem` primitive: every
    `JasminBinOp` operator of `regArith` (`jWordOp`), `castW` (`jZeroExt`), and
    the `stackLoad`/`stackStore` element accessors (`jArrGetEl`, `jArrSetEl`),
    all `rfl` (`JasmincSemAlignment.opcode_alignment_total`). The `extCall` op
    is not covered; its row is the predicate `JasmincSemAlignment.ExtCallAgrees`
    (the `LeafAgrees` hypothesis). -/
theorem psem_alignment_total_discharged :
    (∀ {w : Nat} (bop : JasminBinOp) (a b : BitVec w),
        JasminBinOp.apply bop a b = JasmincSemAlignment.jWordOp bop a b)
    ∧ (∀ {w w' : Nat} (src : BitVec w),
        src.zeroExtend w' = JasmincSemAlignment.jZeroExt w' src)
    ∧ (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat),
        stackGet a k = JasmincSemAlignment.jArrGetEl a k)
    ∧ (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat) (v : BitVec w),
        stackSet a k v = JasmincSemAlignment.jArrSetEl a k v) :=
  JasmincSemAlignment.opcode_alignment_total

/-! ## 7. The trust boundary

`trust_boundary_is_jasmin_ir_to_x86` states the source → x86 conclusion from a
`JasminIRToX86` record together with `hLeaf`, `hInj` and `hPinj`. Its hypotheses
are therefore the jasmin IR → x86 record (value refinement against `runProg`
and CT preservation), the opaque-leaf agreement `LeafAgrees`, and the two
injectivity hypotheses of `lowerComToProg_sem_eq`. -/

/-- **The source → x86 conclusion from `JasminIRToX86`.** Given a
    `JasminIRToX86` record `jir` (value refinement against `runProg` and CT
    preservation, corresponding to jasmin's Coq theorem `compile_prog_to_asmP`
    and its CT counterpart), the leaf hypothesis `hLeaf`, and the naming
    hypotheses `hInj` and `hPinj`, the conclusion of
    `robustCompilation_source_to_x86` holds. The proof applies that theorem to
    `JasminVerifiedCompiler.ofIRToX86 jir`. The Lean results it composes are:

    * the lattice → jasmin lowering and its semantic preservation
      (`lowerComToProg_sem_eq` with the dialect-lowering preservation);
    * the Com-level robust constant-time guarantee (`robustCTPreservation_uncond`).

    The per-opcode rows of `psem_alignment_total_discharged` are not used in
    the proof; they relate `runProg`'s primitives to Lean transcriptions of
    jasmin's `psem` primitives, which is the condition under which `semRefine`
    can be obtained from `compile_prog_to_asmP`. -/
theorem trust_boundary_is_jasmin_ir_to_x86
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    {x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop}
    (jir : JasminIRToX86 leafSem X86Obs x86Behaviour x86CTSafe)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s) (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    x86Behaviour (lowerLatticeToJasmin c) (mapVal V)
        = jir.obsOf (transTy (c.denote V))
      ∧ x86CTSafe (lowerLatticeToJasmin c) :=
  robustCompilation_source_to_x86 hLeaf hInj (JasminVerifiedCompiler.ofIRToX86 jir) c hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
