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

This file composes two results on the shared ANF `Com` substrate and its
emission into source → x86 statements for the lattice → Jasmin → x86 path:

1. **Semantics preservation of the lowering** — running the emitted jasmin
   program under the Lean evaluator `runProg` equals the source `Com` denotation
   (`JasminPrintSemCorrect.lowerComToProg_sem_eq`, under its hypotheses
   `LeafAgrees`, `StraightLine`, and injectivity of `freshName` and of the
   parameter resolver), composed with the dialect-lowering denotation
   preservation (`LatticeToJasminDenoteUncond.lowerLatticeToJasmin_denote_eq_uncond`).
2. **Per-opcode alignment with Lean transcriptions of jasmin's `psem`** —
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
(`asmsem_exportcall`). This is a Coq theorem. This file does not axiomatise it; it
carries the value edge as the hypothesis record **`JasminIRToX86`**, in the same
way `JasminPrintSemCorrect` carries the opaque-leaf edge `LeafAgrees`. Its field
`semRefine` states that the x86 observable of a program on an input is a decode
`obsOf` of the program's result under the Lean evaluator `runProg`. This
corresponds to the value half of `compile_prog_to_asmP`; obtaining it from the
Coq theorem additionally requires that `runProg` agree with `psem` on the whole
program, for which item 2 records the per-opcode rows.

## Constant time

The records carry no constant-time field and the theorems below have no x86
constant-time conjunct. Constant time of emitted code is proved at the decoded
bytes: `X86Backend.DecodedCT.bytesCTCheck_sound` states that a program accepted by
the checker `bytesCTCheck` has equal leakage traces (branch outcomes and effective
addresses) on the address machine from states agreeing on the public locations,
and `DecodedCT.mul1Node_bytesCT` and `DecodedCT.feAddFramed_bytesCT` are its
acceptance of the decoded `mpn_mul_1` and `fe25519_add` bytes.

`x86Behaviour` is the abstract x86-side observable the record is parametric in.
The record `JasminVerifiedCompiler`
has an additional field `psemFaithful`, which follows from `semRefine`
(`JasminVerifiedCompiler.ofIRToX86`). The theorems below prove the source → x86
conclusions from such a record together with the hypotheses `LeafAgrees`,
injectivity of `freshName`, and injectivity of the parameter resolver.
`trust_boundary_is_jasmin_ir_to_x86` states the conclusion from a
`JasminIRToX86` record.

## Main results

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
  denotation. The proof uses result (1) and the record's `semRefine` field.
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
generated x86. The following are proved in Lean:

* the semantic preservation of the lattice → jasmin **lowering**
  (`lowerLatticeToJasmin`), as `lowerComToProg_sem_eq` composed with the
  dialect-lowering preservation, under `LeafAgrees` and the naming hypotheses;
* the **per-opcode rows** relating the evaluator's primitives to Lean
  transcriptions of jasmin's `psem` primitives
  (`JasmincSemAlignment.opcode_alignment_total`: every `JasminBinOp` operator
  of `regArith`, `castW`, and the `stackLoad`/`stackStore` element accessors,
  all `rfl`; the `extCall` row is the predicate `ExtCallAgrees`, and
  `JasmincWArrayAlignment` relates the element accessors to a byte-addressed
  array).

`compile_prog_to_asmP` is a Coq theorem. The jasmin IR → x86 edge is carried as
the hypothesis record `JasminIRToX86`, not as an axiom. It is parametric in:

* `X86Obs` — the type of x86-level observable behaviour (e.g. the export-call
  return value / final memory the attacker reads);
* `x86Behaviour` — what an emitted-and-compiled program observably computes on an
  input, as seen at the x86 level;

and has one obligation, value refinement stated against the Lean evaluator
`runProg`. The record `JasminVerifiedCompiler` (below) has the same field plus a
`psemFaithful` field, which follows from value refinement
(`JasminVerifiedCompiler.ofIRToX86`). The main theorems take a
`JasminVerifiedCompiler`; `trust_boundary_is_jasmin_ir_to_x86` takes a
`JasminIRToX86`. -/

/-- **The jasmin-IR → x86 hypothesis record.** The obligation corresponding to
    jasmin's Coq compiler-correctness theorem `compile_prog_to_asmP`: value
    refinement, stated against the Lean evaluator `runProg`. Deriving `semRefine`
    from the Coq theorem additionally requires `runProg` to agree with jasmin's
    `psem` on the program. Parametric in the x86-side observable `X86Obs` and
    behaviour `x86Behaviour`. Carried as a hypothesis, not an axiom. -/
structure JasminIRToX86
    (leafSem : LeafSem) (X86Obs : Type)
    (x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs) where
  /-- **Value refinement (jasmin IR → x86).** The x86 observable of a program on
      an input is the decode (`obsOf`) of the program's result under the Lean
      evaluator `runProg`. This corresponds to the value-equivalence half of
      `compile_prog_to_asmP`, with `runProg` in place of jasmin's `psem`. -/
  obsOf : {t : JasminTy} → ⟦t⟧ → X86Obs
  semRefine : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
      (com : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      x86Behaviour com V = obsOf (runProg leafSem com V)

/-- **The jasmin compiler edge with a `psemFaithful` field.** Carries the
    jasmin IR → x86 edge corresponding to `compile_prog_to_asmP`, parametric in
    the x86-side observable `X86Obs` and behaviour `x86Behaviour`.

    This is the record taken by `robustCompilation_source_to_x86`. Its
    `psemFaithful` field follows
    from `semRefine`: `JasminVerifiedCompiler.ofIRToX86` builds this record from
    a `JasminIRToX86` record. -/
structure JasminVerifiedCompiler
    (leafSem : LeafSem) (X86Obs : Type)
    (x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs) where
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

/-- **`JasminVerifiedCompiler` from `JasminIRToX86`.** Builds a
    `JasminVerifiedCompiler` from a `JasminIRToX86` record. `psemFaithful`
    follows from `semRefine`: equal `runProg` results decode (via `obsOf`) to
    equal x86 observables; the other fields are copied. -/
def JasminVerifiedCompiler.ofIRToX86
    {leafSem : LeafSem} {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    (jir : JasminIRToX86 leafSem X86Obs x86Behaviour) :
    JasminVerifiedCompiler leafSem X86Obs x86Behaviour where
  psemFaithful := fun com V V' h => by
    rw [jir.semRefine com V, jir.semRefine com V', h]
  obsOf := jir.obsOf
  semRefine := jir.semRefine

/-! ## 4. Robust compilation source → x86

Behaviour preservation source → x86 follows from
`source_to_evaluator_behaviour` (§2) decoded through the record's `semRefine`.
Constant time of emitted code is proved at the decoded bytes
(`X86Backend.DecodedCT.bytesCTCheck_sound`), not by this theorem. -/

/-- **Robust compilation, source → x86.** Given a `JasminVerifiedCompiler`
    record `jvc` (the jasmin IR → x86 edge), the leaf hypothesis `hLeaf`, and
    the naming hypotheses `hInj` and `hPinj`, for every source lattice program
    `c` and every input valuation `V`, the x86 observable `x86Behaviour` of the
    lowered program on the transported input `mapVal V` is the decode
    (`jvc.obsOf`) of `transTy (c.denote V)`, the source program's meaning
    transported along `tau`.

    The theorem states no constant-time property. Constant time is proved at the
    decoded bytes by `X86Backend.DecodedCT.bytesCTCheck_sound`, with the
    acceptance theorems `DecodedCT.mul1Node_bytesCT` (`mpn_mul_1`) and
    `DecodedCT.feAddFramed_bytesCT` (`fe25519_add`).

    The proof composes existing results. The hypotheses are `jvc` (the jasmin
    IR → x86 edge corresponding to Coq's `compile_prog_to_asmP`, carried as a
    record, not an axiom), `hLeaf`, `hInj` and `hPinj`. -/
theorem robustCompilation_source_to_x86
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    (jvc : JasminVerifiedCompiler leafSem X86Obs x86Behaviour)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s) (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    x86Behaviour (lowerLatticeToJasmin c) (mapVal V)
        = jvc.obsOf (transTy (c.denote V)) := by
  rw [jvc.semRefine (lowerLatticeToJasmin c) (mapVal V),
    source_to_evaluator_behaviour hLeaf hInj c hPinj V]

/-! ## 5. Per-opcode alignment rows, re-exported

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

/-! ## 6. The trust boundary

`trust_boundary_is_jasmin_ir_to_x86` states the source → x86 conclusion from a
`JasminIRToX86` record together with `hLeaf`, `hInj` and `hPinj`. Its hypotheses
are therefore the jasmin IR → x86 record (value refinement against `runProg`),
the opaque-leaf agreement `LeafAgrees`, and the two injectivity hypotheses of
`lowerComToProg_sem_eq`. -/

/-- **The source → x86 conclusion from `JasminIRToX86`.** Given a
    `JasminIRToX86` record `jir` (value refinement against `runProg`,
    corresponding to jasmin's Coq theorem `compile_prog_to_asmP`), the leaf
    hypothesis `hLeaf`, and the naming hypotheses `hInj` and `hPinj`, the
    conclusion of `robustCompilation_source_to_x86` holds. The proof applies that
    theorem to `JasminVerifiedCompiler.ofIRToX86 jir`, which composes the lattice →
    jasmin lowering and its semantic preservation (`lowerComToProg_sem_eq` with
    the dialect-lowering preservation). Constant time of emitted code is proved at
    the decoded bytes by `X86Backend.DecodedCT.bytesCTCheck_sound`.

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
    (jir : JasminIRToX86 leafSem X86Obs x86Behaviour)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hPinj : ∀ (s s' : jasminDialect.Ty)
                (v : Ctxt.Var (Γ.map tau) s) (v' : Ctxt.Var (Γ.map tau) s'),
                (paramsAndMap (Γ.map tau)).2 s v
                  = (paramsAndMap (Γ.map tau)).2 s' v' →
                (∃ h : s = s', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    x86Behaviour (lowerLatticeToJasmin c) (mapVal V)
        = jir.obsOf (transTy (c.denote V)) :=
  robustCompilation_source_to_x86 hLeaf hInj (JasminVerifiedCompiler.ofIRToX86 jir) c hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
