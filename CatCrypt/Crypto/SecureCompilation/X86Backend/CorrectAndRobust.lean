/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileRobust

/-!
# The owned compiler: functionally correct **and** robust (the complete triple)

`CompileRobust.ownedCompile_secure_and_CT` already carries, for one owned
lowering, **cryptographic-security preservation** (`sdist ≤ ε`) **and**
**constant-time** (`blockLeak` state-independence) together. What that capstone
does *not* state is the third, value-level guarantee the word "functionally
correct" names: that the compiled machine block computes the **source's value**.

This file adds exactly that conjunct, giving the complete triple over the *same*
owned program `lowerSeq ρ tgtP`:

* **functional correctness** — `LowCTToJInstrCT.lowerSeq_denote`: running the
  lowered block from any matching state yields a state matching the source
  denotation (`StateMatch`), i.e. `⟦compile p⟧ = ⟦p⟧` at the machine level;
* **security preservation** — the `sdist ≤ ε` bound transfers to the compiled
  kernel (`SecureAndCT.security`);
* **constant-time** — the `blockLeak` leakage trace is input-independent
  (`SecureAndCT.constant_time`).

All three are about the same `lowerSeq ρ tgtP`, down the same `LowCT → JInstr`
owned chain, and the proof is **axiom-free of `jasminc_preserves_ct`**.

The extra robust layers — unified-alphabet CT, CT-under-linking, and
CT-surviving-spill — are carried by `CompileRobust.ownedCompile_secure_and_CT_full`
about this same `tgtP`; they are not re-stated here.

## Scope

This is the **owned scalar-arith fragment** (`List ArithSrc`). Widening the
source coverage across the algebraic dialect stack (`Field → ModArith → …`) is
done by transporting these squares along the lowerings — where the
`Related`/`Param` (Trocq) `param_solve` already discharges the functional
transport (`ParamDialectTransport`) and the constant-time square transports the
same way — and connecting the lattice/`Com` route's leakage model. This theorem
is the anchor those phases compose onto.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CorrectAndRobust

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTCallCompose
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileRobust
open scoped ENNReal

/-- **The owned compiler is functionally correct, security-preserving, and
constant-time — one statement, one compiled program.**

Given the optimizer/source agreement `hcc : srcDenote srcP rs = srcDenote tgtP rs`
and the source security bound `hsec`, the owned lowering `lowerSeq ρ tgtP`:

* **computes the source value** — its machine run matches the source denotation
  (`lowerSeq_denote`, needs `ρ` injective and the owned well-formedness
  `p.b ≠ p.dst`); **and**
* **is secure and constant-time** — the `sdist ≤ ε` bound transfers and the
  leakage trace is input-independent (`ownedCompile_secure_and_CT`).

Axiom-free of `jasminc_preserves_ct` (the owned bytes-direct path). This is the
owned scalar-arith level of "the compiler is functionally correct and robust";
the dialect-stack widening (Trocq-transported) is the next phase. -/
theorem ownedCompile_correct_secure_and_CT {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (hρ : Function.Injective ρ)
    (srcP tgtP : List ArithSrc) (hwf : ∀ p ∈ tgtP, p.b ≠ p.dst)
    (rs : RustState) (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hcc : srcDenote srcP rs = srcDenote tgtP rs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
                  (fun _ : α => ideal) ≤ ε) :
    (∀ (js : JState 64), StateMatch ρ rs js →
        StateMatch ρ (srcDenote tgtP rs) (runBlock js (lowerSeq ρ tgtP)))
    ∧ SecureAndCT (α := α) h ρ tgtP rs ideal ε :=
  ⟨fun js hmatch => lowerSeq_denote ρ hρ tgtP hwf rs js hmatch,
   ownedCompile_secure_and_CT h ρ srcP tgtP rs ideal hcc hsec⟩

/-! ## The whole-function variant (across call boundaries) -/

/-- `lowerSeq` distributes over list append (from `lowerSeq_cons`). -/
theorem lowerSeq_append (ρ : RegMap) (xs ys : List ArithSrc) :
    lowerSeq ρ (xs ++ ys) = lowerSeq ρ xs ++ lowerSeq ρ ys := by
  induction xs with
  | nil => simp
  | cons p ps ih => rw [List.cons_append, lowerSeq_cons, lowerSeq_cons, ih, List.append_assoc]

/-- The whole-function inter-call scalar block is the lowering of the concatenated
    per-segment scalar lists — so the straight-line `lowerSeq_denote` applies to it. -/
theorem segScalarBlock_eq (ρ : RegMap) (segs : List CallSeg) :
    segScalarBlock ρ segs = lowerSeq ρ (segs.flatMap (·.scalars)) := by
  induction segs with
  | nil => rfl
  | cons s rest ih => rw [segScalarBlock_cons, List.flatMap_cons, lowerSeq_append, ih]

/-- **The owned whole-function compiler is functionally correct, security-preserving,
and constant-time.** Same triple as `ownedCompile_correct_secure_and_CT`, lifted across
call boundaries: the security side is threaded through the call structure
(`wholeFn_preserves_security`) and the functional + constant-time sides are about the
compiled inter-call scalar block `segScalarBlock ρ tgtSegs`, which (by `segScalarBlock_eq`)
is the lowering of the concatenated segment scalars, so `lowerSeq_denote` discharges the
functional half. Axiom-free of `jasminc_preserves_ct`. -/
theorem ownedCompile_wholeFn_correct_secure_and_CT {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (hρ : Function.Injective ρ)
    (srcSegs tgtSegs : List CallSeg)
    (hwf : ∀ p ∈ tgtSegs.flatMap (·.scalars), p.b ≠ p.dst)
    (rs : RustState) (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hag : SegsAgree srcSegs tgtSegs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenote (segToStmts srcSegs) rs))
                  (fun _ : α => ideal) ≤ ε) :
    (∀ (js : JState 64), StateMatch ρ rs js →
        StateMatch ρ (srcDenote (tgtSegs.flatMap (·.scalars)) rs)
          (runBlock js (segScalarBlock ρ tgtSegs)))
    ∧ (sdist (fun _ : α => interpSP h (itreeDenote (segToStmts tgtSegs) rs))
             (fun _ : α => ideal) ≤ ε)
    ∧ (∀ s₁ s₂ : JState 64,
        blockLeak s₁ (segScalarBlock ρ tgtSegs) =
        blockLeak s₂ (segScalarBlock ρ tgtSegs)) :=
  ⟨fun js hmatch => by
      rw [segScalarBlock_eq]
      exact lowerSeq_denote ρ hρ (tgtSegs.flatMap (·.scalars)) hwf rs js hmatch,
   (ownedCompile_wholeFn_secure_and_CT h ρ srcSegs tgtSegs rs ideal hag hsec).1,
   (ownedCompile_wholeFn_secure_and_CT h ρ srcSegs tgtSegs rs ideal hag hsec).2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.CorrectAndRobust
