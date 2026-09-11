/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
public import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

/-!
# The compiler is functionally correct and robust — the general waist statement

`RobustCompilationPipeline.robustCompilation_source_to_x86` is the *lattice-route*
capstone: it composes behaviour-preservation and robust constant-time all the way
to x86, but specialised to `lowerLatticeToJasmin` and its `robustCTPreservation_uncond`.

This file states the **source-agnostic** version, at the **`Com jasminDialect`
waist** where *both* frontends (hax and lean/rupicola) converge: for *any* emitted
jasmin `Com` program `c`, the compiled x86

* **computes the source value** — its x86 observable is the decode of `c`'s
  denotation (functional correctness), and
* **is robustly constant-time** — if `c` is CT-safe at the Com level, the x86 is
  CT-safe (robustness).

The proof composes three proven, general pieces:

* `JasminIRToX86.semRefine` — the jasmin-IR → x86 value-refinement edge
  (`x86Behaviour c V = obsOf (runProg leafSem c V)`);
* `WholeFnLowering.lowerComToProg_sem_eq'` — the owned backend is faithful
  (`runProg leafSem c V = c.denote V`), for any straight-line jasmin `Com`;
* `JasminIRToX86.ctPreserve` — CT-preservation across the jasmin-IR → x86 edge
  (`RobustlyCTSafe c → x86CTSafe c`).

Carried hypotheses, all explicit (never axioms): the `JasminIRToX86` edge (jasmin's
verified `compile_prog_to_asmP`, or the owned encoder — for the owned bytes-direct
path this is discharged without `jasminc_preserves_ct`), `LeafAgrees` (opaque-leaf
agreement), `StraightLine c`, and `RobustlyCTSafe c` (the source program's
Com-level constant-time, discharged per-route — e.g. `robustCTPreservation_uncond`
for the lattice route).

## Scope

This is the **`Com`-waist** statement: it is about any emitted `Com jasminDialect`
program, which is what every frontend produces and every backend route consumes.
The lattice route's `robustCompilation_source_to_x86` is the instance where
`RobustlyCTSafe` is discharged unconditionally; the owned scalar route
(`X86Backend/CorrectAndRobust`) is the instance where the `JasminIRToX86` edge
is the owned encoder and the whole triple is axiom-free of `jasminc_preserves_ct`;
the algebraic arms (`VIR/DialectLoweringCorrectAndRobust`) supply the Field/ModArith/EC
source programs and their CT. The remaining residuals are the per-route
`RobustlyCTSafe` discharge and the cross-arch (`ARM`/`RISC-V`) value edges.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectAndRobust

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety

/-- **The compiler is functionally correct and robustly constant-time (the
`Com`-waist statement).**

For any emitted jasmin `Com` program `c` (what both frontends produce), given the
jasmin-IR → x86 edge, opaque-leaf agreement, straight-line-ness, and the source's
Com-level constant-time, the compiled x86:

* (functional) its observable equals the decode of `c`'s denotation —
  `x86Behaviour c V = edge.obsOf (c.denote V)`; **and**
* (robust) it is x86-CT-safe — `x86CTSafe c`.

Proof: `edge.semRefine` decodes the owned-evaluator behaviour, which is faithful
by `lowerComToProg_sem_eq'`; `edge.ctPreserve` carries the Com-level robust CT to
x86. This is the source-agnostic generalisation of
`robustCompilation_source_to_x86` (the lattice instance) to the whole `Com`
waist; for the owned bytes-direct edge it carries no `jasminc_preserves_ct`. -/
theorem compiler_correct_and_robust
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    {x86CTSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Prop}
    (edge : JasminIRToX86 leafSem X86Obs x86Behaviour x86CTSafe)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (hSL : StraightLine c) (hct : RobustlyCTSafe c)
    (V : Ctxt.Valuation Γ) :
    x86Behaviour c V = edge.obsOf (c.denote V) ∧ x86CTSafe c := by
  refine ⟨?_, edge.ctPreserve c hct⟩
  rw [edge.semRefine c V, lowerComToProg_sem_eq' hLeaf c hSL V]

end CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectAndRobust
