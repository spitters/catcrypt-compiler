/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTyped

/-!
# The typed exit lowering of the route through `NFProg`

The route `nfRoute` of an expression is the front `impToNF`, dead-code elimination and the
readback `nfToImp`; its run keeps the value of the source run (`nfRoute_run`). The typed exit
lowering `haxToLowCTFnT` of the `ImpExpr` that the route returns therefore simulates the
source expression, by `haxToLowCTFnT_simulates_exit`.

## Main results

* `nfRoute_simulates_exit` — the typed exit lowering of the route through `NFProg` simulates
  the source, from an environment related to a valuation by the environment of names and
  the reading.
* `nfRouteEntry_simulates_exit` — the same for the route of a function body, from every
  source environment typed at the parameters (`EntryTyped`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpToNF

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins IntWidth denote' denoteArgs')
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec) in
/-- **The typed exit lowering of the route through `NFProg` simulates the source.** Under
    `TypedCalls bi sigOf`, `RepeatCalls bi` and the leaf conditions of `haxToLowCTFnT_simulates_exit`, for an
    expression `e` whose route through `NFProg` is in the fragment `exitSimOkT A R` and lowers
    to `c`, a run of `e` to a value from an environment related to a valuation by `σ` and
    `ρ`, and to a `RustState` by the placement `A`, is matched by a run of `c` to a state
    whose result slot agrees with the value. -/
theorem nfRoute_simulates_exit (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (hR : RepeatCalls bi) (N : Nat) (leafSpec : LeafSpec)
    (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {ρ : RBEnv Γ} {e e' : ImpExpr} {c : LowCT}
    (h : nfRoute sigOf σ ρ e = some e') (hok : exitSimOkT A R true true e' = true)
    (hK : haxToLowCTFnT A e' = some c) {env : Env} {V : Valuation Γ}
    (hσ : EnvRel σ env V) (hρ : RBRel ρ env V) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denote' bi fuel e).run env = (.val v, env')) (rs : RustState)
    (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeAgreesT br R (.val v) rs' := by
  obtain ⟨fuel', env₂, hrun'⟩ := nfRoute_run bi sigOf hT hR h hσ hρ hrun
  exact haxToLowCTFnT_simulates_exit bi N leafSpec br A R hL e' c hok hK fuel' env env₂
    (.val v) rs hrun' ⟨v, rfl⟩ hag

open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec) in
/-- **The typed exit lowering of the route through `NFProg` of a function body simulates
    the source**, from every source environment holding at the parameters `ps` the encodings
    of values of their types (`EntryTyped`). -/
theorem nfRouteEntry_simulates_exit (bi : Builtins)
    (sigOf : String → List NfTy → Option NfTy) (hT : TypedCalls bi sigOf)
    (hR : RepeatCalls bi) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    {ps : List (String × NfTy)} {e e' : ImpExpr} {c : LowCT}
    (h : nfRouteEntry sigOf ps e = some e') (hok : exitSimOkT A R true true e' = true)
    (hK : haxToLowCTFnT A e' = some c) {env : Env} (hent : EntryTyped env ps) {fuel : Nat}
    {v : Value} {env' : Env} (hrun : (denote' bi fuel e).run env = (.val v, env'))
    (rs : RustState) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeAgreesT br R (.val v) rs' := by
  obtain ⟨V, hV⟩ := entryVals_of_typed hent
  exact nfRoute_simulates_exit bi sigOf hT hR N leafSpec br A R hL h hok hK (entryEnv_rel hV)
    (entryRB_rel hV) hrun rs hag

end CatCrypt.Crypto.Hax.ImpToNF
