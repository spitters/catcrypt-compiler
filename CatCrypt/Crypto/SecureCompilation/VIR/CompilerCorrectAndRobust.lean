/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
public import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

/-!
# The compiler is functionally correct — the general waist statement

`RobustCompilationPipeline.robustCompilation_source_to_x86` is the *lattice-route*
behaviour-preservation theorem to x86, specialised to `lowerLatticeToJasmin`.

This file states the **source-agnostic** version, at the **`Com jasminDialect`
waist** where *both* frontends (hax and lean/rupicola) converge: for *any* emitted
straight-line jasmin `Com` program `c`, the x86 observable of the compiled program is
the decode of `c`'s denotation.

The proof composes two general pieces:

* `JasminIRToX86.semRefine` — the jasmin-IR → x86 value-refinement edge
  (`x86Behaviour c V = obsOf (runProg leafSem c V)`);
* `WholeFnLowering.lowerComToProg_sem_eq'` — the owned backend is faithful
  (`runProg leafSem c V = c.denote V`), for any straight-line jasmin `Com`.

Carried hypotheses, all explicit (never axioms): the `JasminIRToX86` edge (jasmin's
verified `compile_prog_to_asmP`, or the owned encoder), `LeafAgrees` (opaque-leaf
agreement) and `StraightLine c`.

## Constant time

The statement has no constant-time conjunct. Constant time of emitted code is proved
at the decoded bytes: `X86Backend.DecodedCT.bytesCTCheck_sound` gives equal leakage
traces on the address machine for a program accepted by `bytesCTCheck`, and
`DecodedCT.mul1Node_bytesCT` and `DecodedCT.feAddFramed_bytesCT` are its acceptance of
the decoded `mpn_mul_1` and `fe25519_add` bytes.

## Scope

This is the **`Com`-waist** statement: it is about any emitted `Com jasminDialect`
program, which is what every frontend produces and every backend route consumes.
The lattice route's `robustCompilation_source_to_x86` is its lattice instance; the
owned scalar route (`X86Backend/CorrectAndRobust`) is the instance where the
`JasminIRToX86` edge is the owned encoder. The remaining residual is the cross-arch
(`ARM`/`RISC-V`) value edges.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectAndRobust

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-- **The compiler is functionally correct (the `Com`-waist statement).**

For any emitted straight-line jasmin `Com` program `c` (what both frontends produce),
given the jasmin-IR → x86 edge and opaque-leaf agreement, the x86 observable of the
compiled program equals the decode of `c`'s denotation:
`x86Behaviour c V = edge.obsOf (c.denote V)`.

Proof: `edge.semRefine` decodes the owned-evaluator behaviour, which is faithful by
`lowerComToProg_sem_eq'`. This is the source-agnostic generalisation of
`robustCompilation_source_to_x86` (the lattice instance) to the whole `Com` waist.
Constant time is proved at the decoded bytes by
`X86Backend.DecodedCT.bytesCTCheck_sound`, with the acceptance theorems
`DecodedCT.mul1Node_bytesCT` and `DecodedCT.feAddFramed_bytesCT`. -/
theorem compiler_correct_and_robust
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    {X86Obs : Type}
    {x86Behaviour : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
        Com jasminDialect Γ t → Ctxt.Valuation Γ → X86Obs}
    (edge : JasminIRToX86 leafSem X86Obs x86Behaviour)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (hSL : StraightLine c) (V : Ctxt.Valuation Γ) :
    x86Behaviour c V = edge.obsOf (c.denote V) := by
  rw [edge.semRefine c V, lowerComToProg_sem_eq' hLeaf c hSL V]

end CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectAndRobust
