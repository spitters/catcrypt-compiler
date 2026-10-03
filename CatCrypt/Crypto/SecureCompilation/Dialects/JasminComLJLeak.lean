/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToMulti
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ

/-!
# The constant-time leakage of `ComLJ`

`ComLJ.leakRun M fuel c V` runs a carried-register loop program from `V` and returns its
result with the list of its events, or `none` when a do-while runs out of fuel:

* a lifted `ComL` program emits `ComL.ctLeak`;
* a binding emits the events of its operation (`Expr.ctLeak`);
* a counted loop emits `trip n` for its trip count `n`, then the events of each trip's
  body (`MultiReturnCom.ctLeak`) in order (`NFLeak.forIterLeak`), then the events of its
  continuation;
* a do-while emits, per run of its body, the body's events followed by `branch true`
  when the loop continues and `branch false` at the exit (`NFLeak.whileIterLeak`), then the
  events of its continuation. The exit bit is a public branch event.

These are the clauses of `NFLeak.NFProg.leakRun` for `forLoop` and `whileLoop`, so the
bisimulation with a source `NFProg jasminDialect` is `NFProgRel.forIterLeak_rel_bisim` and
`NFProgRel.whileIterLeak_rel_bisim` at the steps of `ComLJ.leakRun`.

## Main definitions

* `ComLJ.forStepLeak`, `ComLJ.whileStepLeak` — one trip with its events.
* `ComLJ.leakRun`, `ComLJ.ctLeak` — the run with its events, and the events.

## Main results

* `ComLJ.leakRun_fst` — the result of the run is the denotation.
* `ComLJ.ctLeak_lift` — a lifted `ComL` program emits `ComL.ctLeak`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLJLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

/-- One trip of a counted carried-register loop with its events: `ComLJ.forStep` and the
    events of the body on the same valuation. -/
def ComLJ.forStepLeak (M : LeakModel jasminDialect) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invsV : Ctxt.Valuation invTys) (i : Nat) (acc : Ctxt.Valuation cs) :
    Option (Ctxt.Valuation cs × List CTLeak) :=
  some (ComLJ.forStep update invsV acc i,
    MultiReturnCom.ctLeak M update (hvAppend acc (.cons (BitVec.ofNat 64 i) invsV)))

/-- One run of a do-while body with its events: `ComLJ.whileStep` and the events of the
    body on the same valuation. -/
def ComLJ.whileStepLeak (M : LeakModel jasminDialect) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invsV : Ctxt.Valuation invTys) (acc : Ctxt.Valuation cs) :
    Option (Ctxt.Valuation (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak) :=
  some (update.denote (hvAppend acc invsV),
    MultiReturnCom.ctLeak M update (hvAppend acc invsV))

/-- The run of a `ComLJ` program from a valuation with the list of its events, in
    execution order; `fuel` bounds the runs of each do-while body. -/
def ComLJ.leakRun (M : LeakModel jasminDialect) (fuel : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComLJ Γ t → Ctxt.Valuation Γ →
    Option (⟦t⟧ × List CTLeak)
  | _, _, .lift c, V => some (c.denote V, ComL.ctLeak M c V)
  | _, _, .var e body, V =>
      (ComLJ.leakRun M fuel body (V.extend (e.denote V))).map fun r =>
        (r.1, Expr.ctLeak M e V ++ r.2)
  | _, _, .forLoopRegs update count inits invs body, V =>
      (forIterLeak (d := jasminDialect) (ComLJ.forStepLeak M update (Expr.lookupArgs invs V))
          (List.range (count.lookup V).toNat) (Expr.lookupArgs inits V)).bind fun r =>
        (ComLJ.leakRun M fuel body (hvAppend r.1 V)).map fun q =>
          (q.1, .trip (count.lookup V).toNat :: (r.2 ++ q.2))
  | _, _, .whileRegs update inits invs body, V =>
      (whileIterLeak (d := jasminDialect) (ComLJ.whileStepLeak M update (Expr.lookupArgs invs V))
          fuel (Expr.lookupArgs inits V)).bind fun r =>
        (ComLJ.leakRun M fuel body (hvAppend r.1 V)).map fun q => (q.1, r.2 ++ q.2)

/-- The events of the run of a `ComLJ` program, or `none` when a do-while runs out of
    fuel. -/
def ComLJ.ctLeak (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : ComLJ Γ t) (V : Ctxt.Valuation Γ) : Option (List CTLeak) :=
  (ComLJ.leakRun M fuel c V).map Prod.snd

/-- A lifted `ComL` program emits `ComL.ctLeak`, at every fuel. -/
theorem ComLJ.ctLeak_lift (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (V : Ctxt.Valuation Γ) :
    ComLJ.ctLeak M fuel (.lift c) V = some (ComL.ctLeak M c V) := rfl

/-- A monadic fold in `Option` of a step that always succeeds is `some` of the pure
    fold. -/
theorem foldlM_some_eq {α β : Type} (g : α → β → α) :
    (l : List β) → (a : α) → l.foldlM (fun a i => some (g a i)) a = some (l.foldl g a)
  | [], _ => rfl
  | i :: l, a => by
      rw [List.foldlM_cons, List.foldl_cons]
      exact foldlM_some_eq g l (g a i)

/-- **The result of the leakage run is the denotation**, at every fuel. -/
theorem ComLJ.leakRun_fst (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t) (V : Ctxt.Valuation Γ) :
    (ComLJ.leakRun M fuel c V).map Prod.fst = c.denote fuel V := by
  induction c with
  | lift c => rfl
  | var e body ih =>
      simp only [ComLJ.leakRun, Option.map_map]
      exact ih _
  | forLoopRegs update count inits invs body ih =>
      have hfold := forIterLeak_fst (d := jasminDialect)
        (ComLJ.forStepLeak M update (Expr.lookupArgs invs V))
        (fun acc i => some (ComLJ.forStep update (Expr.lookupArgs invs V) acc i))
        (fun _ _ => rfl) (List.range (count.lookup V).toNat) (Expr.lookupArgs inits V)
      rw [foldlM_some_eq] at hfold
      simp only [ComLJ.leakRun, ComLJ.denote]
      rcases h : forIterLeak (d := jasminDialect) _ _ _ with _ | ⟨a, tr⟩
      · rw [h] at hfold; cases hfold
      · rw [h, Option.map_some] at hfold
        cases hfold
        simp only [Option.bind_some, Option.map_map]
        exact ih _
  | whileRegs update inits invs body ih =>
      have hw := whileIterLeak_fst (d := jasminDialect)
        (ComLJ.whileStepLeak M update (Expr.lookupArgs invs V))
        (ComLJ.whileStep update (Expr.lookupArgs invs V)) (fun _ => rfl) fuel
        (Expr.lookupArgs inits V)
      simp only [ComLJ.leakRun, ComLJ.denote]
      rw [← hw]
      rcases whileIterLeak (d := jasminDialect) _ _ _ with _ | ⟨a, tr⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map, Option.bind_eq_bind]
        exact ih _

end CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLJLeak
