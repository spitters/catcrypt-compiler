/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# `RFor` constructor extension lemmas

This module extends the **robust-compilation** and **CT-preservation**
meta-theorems to cover the bounded for-loop constructor `RFor`. It states the
per-constructor obligations explicitly and discharges them by composing the
foundation lemmas.

## Scope

Two obligations per constructor:

1. **Translation preservation** — the dialect front
   `translateDialectControl` produces a denotationally-preserving
   `catCryptDialect` prefix. For `RFor`, this is mediated by the `loopRForD`
   helper. At the foundation layer, the simulation theorem
   `rustExecSimulatesDialect` is the named carrier: any executable `RFor`
   produced by `translateDialectControl` yields a `RustStateInterp`-preserving
   continuation. We expose the specialization to `RFor` as a named lemma here so
   downstream `RFor` consumers cite it directly.

2. **CT preservation** — `RFor x N body`'s loop counter `x` is bound to a
   structurally-public index `i ∈ [0..N)`, since `N` is a *closed Nat
   literal* at the AST level (no runtime / secret control). Therefore
   `RFor` is **CT by construction**: the loop introduces no new secret
   branch and no new secret-dependent control flow, and CT reduces to the
   body's CT. This is discharged inside the global soundness
   theorem `cmdCT_sound` (case `forSucc` / `forZero`); we extract that
   discharge into a named extension lemma here.

## What is *not* claimed

We do **not** restate or re-prove the underlying simulation /
CT-soundness theorems. The lemmas below are *named witnesses* for the
per-constructor extension claim — composition of the foundation lemmas
with the constructor's specific shape (closed `N`, structurally public
counter).

The composition into the meta-theorem chain is in `CombinedExtended.lean`.

## References

* `translateDialectControl` / `loopRForD` (dialect front, read-only).
* `rustExecSimulatesDialect` (robust-compilation carrier, foundation).
* `cmdCT_sound` (CT-preservation carrier, foundation).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.LowCTExtensions.RForPreservation

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

/-! ## 1. Translation preservation for `RFor` (dialect front)

The foundational theorem `rustExecSimulatesDialect` says: if
`translateDialectControl vm c = some o` and `RustExec N leafSpec c rs rs'`, then
there exists `V' : HVec o.Γ'` with `RustStateInterp o.vm rs' V'`. We specialize
it to the `RFor` constructor over the dialect front.

The `RFor` constructor is one of the cases of `translateDialectControl` (it
dispatches to `loopRForD`), so the foundational theorem covers it — no new proof obligation. We expose the specialization as a *named*
lemma so downstream consumers can cite the per-constructor coverage.
-/

/-- **`RFor` translation preserves `RustStateInterp` over the dialect front.**
    A specialization of `rustExecSimulatesDialect` to the bounded-for
    constructor over `translateDialectControl` (whose `RFor` arm is
    `loopRForD`). Stated on the covered control fragment `IsCoveredCtl body`. -/
theorem loopRForD_denotation_preserved
    {Γ : Ctx} (vm : VarMap Γ) (x : String) (N_loop : Nat) (body : LowCT)
    (o : DTransOut Γ) (N : Nat) (leafSpec : LeafSpec)
    (rs rs' : RustState)
    (hCov : IsCoveredCtl body)
    (hTrans : translateDialectControl vm (.RFor x N_loop body) = some o)
    (hExec : RustExec N leafSpec (.RFor x N_loop body) rs rs')
    (V : HVec Γ) (hInv : RustStateInterp vm rs V) :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V' :=
  rustExecSimulatesDialect vm (.RFor x N_loop body) o N leafSpec rs rs'
    (.rFor hCov) hTrans hExec V hInv

/-- **Unrolling at `N = 0` is the identity (dialect front).** The empty loop
    translates to the identity continuation `ComCont.id` over `loopRForD`. -/
theorem loopRForD_zero_denotation
    {Γ : Ctx} (vm : VarMap Γ) (x : String) (body : LowCT) :
    translateDialectControl vm (.RFor x 0 body)
      = some { Γ' := Γ, cont := ComCont.id, vm := vm } := by
  simp only [translateDialectControl, loopRForD]

/-! ## 2. CT preservation for `RFor`

The loop bound `N` is a *closed Nat literal* in the AST: it cannot depend on
any secret. The loop counter `x` is bound by the loop to each `i ∈ [0..N)`,
so it is structurally Public — the value at each iteration depends only on
the loop index, not on any secret state.

`cmdCT (RFor x N body) lt leafCT = cmdCT body lt leafCT` (no extra obligation
on the loop bound or counter), and the soundness theorem `cmdCT_sound`
discharges the inductive case for `forZero` / `forSucc` by chaining the
body's IH with `PublicEquiv.set_scalar_same x n`. We name the corresponding
extension lemma here.
-/

/-- **CT-check reduces to the body**: `cmdCT` for `RFor` is exactly the body
    CT check. Computed directly from the `cmdCT` definition; no extra
    obligation from the loop bound or the counter. -/
@[simp]
theorem cmdCT_RFor (x : String) (N_loop : Nat) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RFor x N_loop body) lt leafCT = cmdCT body lt leafCT := rfl

/-- **`RFor` preserves CT (`PublicEquiv`) when the body does.**

    Specialization of `cmdCT_sound` to the `RFor` constructor: a CT-safe
    body composed with a closed loop bound `N` and a structurally-public
    loop counter yields a CT-safe loop. The loop bound `N : Nat` cannot
    introduce secret-dependent control flow because it is fixed at AST
    elaboration time.

    The `CMOVInvariant` hypothesis is the standard side condition of
    `cmdCT_sound`; for `RFor` it reduces structurally to the body's
    `CMOVInvariant`. -/
theorem loopRFor_ct_preserves
    (x : String) (N_loop : Nat) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (leafSpec : LeafSpec) (N : Nat)
    (hCT_body : cmdCT body lt leafCT = true)
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCMOV : CMOVInvariant (.RFor x N_loop body))
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RFor x N_loop body) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RFor x N_loop body) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  have hCT_for : cmdCT (.RFor x N_loop body) lt leafCT = true := by
    rw [cmdCT_RFor]; exact hCT_body
  exact cmdCT_sound (.RFor x N_loop body) lt leafCT leafSpec N
    hCT_for hLeaf hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-- **Closed-bound RFor is CT by construction.**

    Restatement of `loopRFor_ct_preserves` highlighting that the AST-level
    `N : Nat` literal forces a static iteration count — no runtime
    branching on secrets. The loop's information-flow contribution is
    exactly the body's; this is the precise formal sense of "static
    bounds → CT by construction". -/
theorem RFor_ct_by_construction
    (x : String) (N_loop : Nat) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RFor x N_loop body) lt leafCT = true
      ↔ cmdCT body lt leafCT = true := by
  rw [cmdCT_RFor]

end CatCrypt.Crypto.SecureCompilation.LowCTExtensions.RForPreservation
