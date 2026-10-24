/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# The front-compiled loop body as a `JLoopBodyN` step and fold

`FrontLoopBodyDenote.frontLoopBodyJ_denote` relates the front-compiled loop
body to its source `LowCT` body's `semScalar` run, concluding at
`update.denote (ctMapValD V) = ctTransTy accval`. The `ComL` loop nodes consume
the same body through `JLoopBodyN.stepC update invs t acc` — the denotation at
the valuation `[acc, BitVec.ofNat 64 t, *invs]` — folded over the trip indices
by `JLoopBodyN.denote`. This module closes that gap once, for every kernel of
the runtime-loop front whose body context is `accCTy :: .sword 64 :: invCTys`:

* per trip, the adequacy conclusion at the trip valuation IS a `stepC`
  (`ctMapValD` distributes over `.cons` and `ctTransTy` is applied per slot);
* over the fold, per-trip agreement with a model step `f` makes
  `JLoopBodyN.denote` the `ctTransTy` transport of the model fold
  `(List.range n).foldl f init`.

A kernel instantiates `frontLoopBodyJ_denote_foldl` with its word-model step
(`mul1FoldStep`, `bcFold`'s step, …); the per-kernel residue is the finite
`semScalar` run of its concrete body from a `ConsistentS` entry state — the
per-command check — and the model-level value theorem (`mul1Fold_val`, …) then
reads on the compiled program's denotation.
`X86Backend.MpnMul1FrontDenote` is the `mpn_mul_1` instance.

## Main results

* `consistentS_bind` — `ConsistentS` extends along `VarMap.bind` /
  `Valuation.extend` / `SEnvScalar.upd` at an arbitrary value, so a loop-body
  entry state is built by chaining binds from `consistentS_empty`.
* `stepC_of_denote` — a denotation equation at the trip valuation, read as a
  `JLoopBodyN.stepC` equation.
* `denote_fold_of_step` — per-trip denotation agreement with a model step
  gives the whole `JLoopBodyN.denote` fold.
* `frontLoopBodyJ_stepC` — `frontLoopBodyJ_denote` at the trip valuation, as
  one `stepC`.
* `frontLoopBodyJ_denote_foldl` — the composite: per-trip source runs of the
  body give the compiled loop body's fold as the model fold.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredSCtl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote (frontLoopBodyJ_denote)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. Building the entry state -/

/-- `ConsistentS` extends along one binder: binding a name in the varmap, the
    matching value at the head of the valuation, and the same value in the
    environment keeps the three consistent. Chained from `consistentS_empty`,
    this builds the entry state of any loop-body context. -/
theorem consistentS_bind {Γ : Ctx} {t : CryptoTy} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) (n : String) (v : ⟦t⟧) :
    ConsistentS (vm.bind (t := t) n) (V.extend v) (env.upd n v) := by
  intro s
  by_cases hsd : s = n
  · subst hsd
    simp only [VarMap.bind, TranslateDialectScalar.SEnvScalar.upd]
    rfl
  · simp only [VarMap.bind, TranslateDialectScalar.SEnvScalar.upd, ite_eq_right hsd]
    rw [← hc s]
    cases hl : vm.lookup s with
    | none => rfl
    | some p => obtain ⟨t', v'⟩ := p; rfl

/-! ## 2. The trip valuation as a `stepC` -/

/-- A denotation equation at the trip valuation
    `[acc, BitVec.ofNat 64 t, *invsC]`, read as a `JLoopBodyN.stepC` equation:
    `ctMapValD` distributes over `.cons` and `ctTransTy` is the per-slot
    transport, so the two sides coincide definitionally. -/
theorem stepC_of_denote {accCTy : CryptoTy} {invCTys : Ctx}
    (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (t : Nat) (acc : ⟦accCTy⟧) (accval : ⟦accCTy⟧)
    (update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy))
    (hden : update.denote (ctMapValD (.cons acc (.cons (BitVec.ofNat 64 t) invsC)))
      = ctTransTy accval) :
    JLoopBodyN.stepC (accTy := mapTy accCTy) (invTys := mapCtx invCTys) update
      (ctMapValD invsC) t (ctTransTy acc) = ctTransTy accval := hden

/-- Per-trip denotation agreement with a model step `f` gives the whole
    `JLoopBodyN.denote` fold: the compiled loop body's `n`-trip denotation is
    the `ctTransTy` transport of `(List.range n).foldl f init`. -/
theorem denote_fold_of_step {accCTy : CryptoTy} {invCTys : Ctx}
    (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy))
    (f : ⟦accCTy⟧ → Nat → ⟦accCTy⟧) :
    ∀ n : Nat,
      (∀ t (acc : ⟦accCTy⟧), t < n →
        update.denote (ctMapValD (.cons acc (.cons (BitVec.ofNat 64 t) invsC)))
          = ctTransTy (f acc t)) →
      ∀ init : ⟦accCTy⟧,
        JLoopBodyN.denote (accTy := mapTy accCTy) (invTys := mapCtx invCTys)
          ⟨n, update⟩ (ctMapValD invsC) (ctTransTy init)
          = ctTransTy ((List.range n).foldl f init)
  | 0, _, _ => rfl
  | k + 1, h, init => by
      erw [JLoopBodyN.denote_succ]
      rw [denote_fold_of_step invsC update f k (fun t acc ht => h t acc (by omega)) init,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact stepC_of_denote invsC k _ _ update (h k _ (Nat.lt_succ_self k))

/-! ## 3. The source-run forms -/

/-- **One trip of the front-compiled loop body computes the source step.** For
    an `IsCoveredSCtl` body over `accCTy :: .sword 64 :: invCTys`, a
    `ConsistentS` entry state at the trip valuation, and a `semScalar` run
    leaving `accval` in the accumulator name, one `JLoopBodyN.stepC` of the
    front body carries `ctTransTy acc` to `ctTransTy accval`.
    `frontLoopBodyJ_denote` at the trip valuation. -/
theorem frontLoopBodyJ_stepC {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT) (hcov : IsCoveredSCtl body)
    (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (t : Nat) (acc : ⟦accCTy⟧)
    (env env' : SEnvScalar) (accval : ⟦accCTy⟧)
    (hc : ConsistentS vmBody (.cons acc (.cons (BitVec.ofNat 64 t) invsC)) env)
    (hsem : semScalar body env = some env')
    (hval : env' accName = some ⟨accCTy, accval⟩)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update) :
    JLoopBodyN.stepC (accTy := mapTy accCTy) (invTys := mapCtx invCTys) update
      (ctMapValD invsC) t (ctTransTy acc) = ctTransTy accval :=
  stepC_of_denote invsC t acc accval update
    (frontLoopBodyJ_denote vmBody accName body hcov
      (.cons acc (.cons (BitVec.ofNat 64 t) invsC)) env env' accval hc hsem hval hupd)

/-- **The front-compiled loop body's fold computes the model fold.** When every
    trip below `n` has a source run leaving the model step's value in the
    accumulator name from a consistent entry state, the `n`-trip
    `JLoopBodyN.denote` of the front body is the `ctTransTy` transport of the
    model fold. The per-kernel residue is exactly the `hstep` hypothesis: one
    finite `semScalar` run of the concrete body per trip shape. -/
theorem frontLoopBodyJ_denote_foldl {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT) (hcov : IsCoveredSCtl body)
    (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (f : ⟦accCTy⟧ → Nat → ⟦accCTy⟧) (n : Nat)
    (hstep : ∀ t (acc : ⟦accCTy⟧), t < n →
      ∃ env env', ConsistentS vmBody (.cons acc (.cons (BitVec.ofNat 64 t) invsC)) env ∧
        semScalar body env = some env' ∧ env' accName = some ⟨accCTy, f acc t⟩)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (init : ⟦accCTy⟧) :
    JLoopBodyN.denote (accTy := mapTy accCTy) (invTys := mapCtx invCTys)
      ⟨n, update⟩ (ctMapValD invsC) (ctTransTy init)
      = ctTransTy ((List.range n).foldl f init) :=
  denote_fold_of_step invsC update f n
    (fun t acc ht => by
      obtain ⟨env, env', hc, hsem, hval⟩ := hstep t acc ht
      exact frontLoopBodyJ_denote vmBody accName body hcov
        (.cons acc (.cons (BitVec.ofNat 64 t) invsC)) env env' (f acc t) hc hsem hval hupd)
    init

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC
