/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTAscentBridge
public import HaxAscent.Ascent.SquareKleisli
public import HaxLean.Phase.IterStepBy
public import HaxLean.Phase.Monomorphise

/-!
# Source rewrites over the ascent judgment

Two source rewrites of the front, stated over `Hax.Ascent.Corres`.

`Hax.IterStepBy.stepFn N` rewrites each stepped-range loop of a function body to a
counted loop. Under a builtin table meeting `Hax.IterStepBy.VSpec`, the rewritten body
has the runs of the source at every fuel and environment
(`Hax.IterStepBy.stepFn_run`), so the two carry the same `Corres` statements.

`Hax.Monomorphise.monomorphise tbl insts` renames the trait-method calls of a generic
body to their implementations at the instances `insts`. The specialised body under
`bi` agrees with the generic body under `Hax.Monomorphise.withInstances bi tbl insts`
up to the text of an error (`Hax.Monomorphise.denote'_monomorphise`). A `Corres` run
ends in a value, never in an error, so the two carry the same `Corres` statements,
the generic one read under the extended table.

The continue-flag rewriting `Hax.ContinueFlag.contFn` is transported in
`CatCrypt.Crypto.Hax.HaxToLowCTAscentBridgeLoop` (`corres_contFn`). `CorresX` is
`Corres` at an encoded exception value, so the statements below cover it.

## Main results

* `corres_stepFn_iff` — a `Corres` statement for a function body is one for its
  stepped-range rewriting, and conversely
* `corres_monomorphise_iff` — a `Corres` statement for the generic body under the
  extended table is one for the specialised body under `bi`, and conversely
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Value Env Outcome Builtins denote')
open _root_.Hax.Ascent (Corres)
open _root_.Hax.IterStepBy (Names VSpec stepFn)
open _root_.Hax.Monomorphise (ErrEq MonoTable withInstances monomorphise)

variable {S : Type} {bi : Builtins}

/-- **Stepped ranges.** Under a table meeting `VSpec`, a function body and its
    rewriting `stepFn N` carry the same `Corres` statements. -/
theorem corres_stepFn_iff {N : Names} (hN : VSpec bi N) {e : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value} :
    Corres bi P G (stepFn N e) V Q ↔ Corres bi P G e V Q :=
  _root_.Hax.Ascent.corres_congr_run fun fuel env =>
    _root_.Hax.IterStepBy.stepFn_run hN e fuel env

/-- Agreement up to the text of an error is symmetric. -/
theorem errEq_symm {m₁ m₂ : StateM Env Outcome} (h : ErrEq m₁ m₂) : ErrEq m₂ m₁ :=
  fun env => ⟨(h env).1.symm, (h env).2.symm⟩

/-- A `Corres` statement transfers along runs that agree up to the text of an error at
    every fuel. -/
theorem corres_of_errEq {bi₁ bi₂ : Builtins} {e₁ e₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel e₁) (denote' bi₂ fuel e₂))
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hc : Corres bi₂ P G e₂ V Q) : Corres bi₁ P G e₁ V Q := by
  intro env σ hP hG
  obtain ⟨f₀, env', hQ, hrun⟩ := hc env σ hP hG
  exact ⟨f₀, env', hQ, fun fuel hf => (h fuel).run_eq (hrun fuel hf) (fun _ h => by cases h)⟩

/-- **Monomorphisation.** The specialised body `monomorphise tbl insts e` under `bi`
    carries the `Corres` statements of the generic body `e` under the table
    `withInstances bi tbl insts`, and conversely. -/
theorem corres_monomorphise_iff (tbl : MonoTable) (insts : List String) {e : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value} :
    Corres bi P G (monomorphise tbl insts e) V Q ↔
      Corres (withInstances bi tbl insts) P G e V Q :=
  ⟨corres_of_errEq fun fuel =>
      errEq_symm (_root_.Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel),
    corres_of_errEq fun fuel => _root_.Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel⟩

end CatCrypt.Crypto.Hax
