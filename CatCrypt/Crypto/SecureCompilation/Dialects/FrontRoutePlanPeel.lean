/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

@[expose] public section

set_option autoImplicit false

/-!
# Route selection under a prefix of binders

A front may open a function body with a chain of binders, `RLetU64Zero x b` (a word slot
set to zero) and `RLetZero x t b` (a tower slot declared before it is written), and place
the loop inside the innermost of them. `FrontRoutePlan.split` reads the command spine of
its argument, on which such a chain is one non-loop command, and reports
`RouteGap.noLoop`.

`peelBinders c` splits `c` into the list of its leading binders and the command under
them (the core); `wrapAll` rebuilds `c` from the two (`wrapAll_peelBinders`). Under
`semScalar` a binder is its effect on the environment (`Binder.env`: a word binder sets its
name to zero, a tower binder does nothing), so a run of `c` is a run of the core from the
environment the binders produce (`semScalar_peelBinders`). `analysePeeled` and
`compilePeeled` are `analyse` and `compile` on the core, and `compilePeeled_denote` is
`compile_denote` for them.

The section on the inputs of a compilation inverts `compile` into the stages it ran
(`compile_stages`), and computes the split of a single runtime-count loop node whose body
has no loop (`split_rForRuntime`), so the body the route compiled and its trip count are
read off the result (`compile_rForRuntime`).

## Main results

* `Binder`, `wrapAll`, `peelBinders`, `wrapAll_peelBinders` — the binder prefix.
* `Binder.env`, `bindersEnv`, `semScalar_wrapAll`, `semScalar_peelBinders` — the prefix
  under `semScalar`.
* `analysePeeled`, `compilePeeled`, `compilePeeled_denote` — route selection and dispatch
  on the core.
* `compile_stages`, `split_rForRuntime`, `plan_loopShape_runtimeN`, `compile_rForRuntime` —
  the stages of a compilation, and their values on a single runtime-count loop node.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (SEnvScalar semScalar)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 1. The binder prefix -/

/-- A leading binder of a function body. -/
inductive Binder where
  /-- `RLetU64Zero x`: a word slot `x` set to zero. -/
  | u64Zero (x : String)
  /-- `RLetZero x t`: a tower slot `x` of type `t`. -/
  | zero (x : String) (t : TowerType)

/-- The binder around a command. -/
def Binder.wrap : Binder → LowCT → LowCT
  | .u64Zero x, b => .RLetU64Zero x b
  | .zero x t, b => .RLetZero x t b

/-- The binders `bs`, outermost first, around the core `core`. -/
def wrapAll (bs : List Binder) (core : LowCT) : LowCT := bs.foldr Binder.wrap core

/-- The leading binders of a command, outermost first, and the command under them. -/
def peelBinders : LowCT → List Binder × LowCT
  | .RLetU64Zero x b => ((.u64Zero x) :: (peelBinders b).1, (peelBinders b).2)
  | .RLetZero x t b => ((.zero x t) :: (peelBinders b).1, (peelBinders b).2)
  | c => ([], c)

/-- A command is its binders around its core. -/
theorem wrapAll_peelBinders (c : LowCT) : wrapAll (peelBinders c).1 (peelBinders c).2 = c := by
  induction c with
  | RLetU64Zero x b ih =>
      simp only [peelBinders, wrapAll, List.foldr_cons] at ih ⊢
      rw [ih]; rfl
  | RLetZero x t b ih =>
      simp only [peelBinders, wrapAll, List.foldr_cons] at ih ⊢
      rw [ih]; rfl
  | _ => rfl

/-! ## 2. The binder prefix under `semScalar` -/

/-- The effect of a binder on a scalar environment: a word binder sets its name to the zero
    word, a tower binder leaves the environment unchanged. -/
def Binder.env : Binder → SEnvScalar → SEnvScalar
  | .u64Zero x, e => e.upd x (t := .sword 64) (0 : BitVec 64)
  | .zero _ _, e => e

/-- The environment the binders `bs`, outermost first, produce from `env`. -/
def bindersEnv (bs : List Binder) (env : SEnvScalar) : SEnvScalar :=
  bs.foldl (fun e b => b.env e) env

/-- A run of the binders around a core is a run of the core from the environment the
    binders produce. -/
theorem semScalar_wrapAll (bs : List Binder) (core : LowCT) (env : SEnvScalar) :
    semScalar (wrapAll bs core) env = semScalar core (bindersEnv bs env) := by
  induction bs generalizing env with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | u64Zero x =>
          simp only [wrapAll, List.foldr_cons, Binder.wrap, bindersEnv, List.foldl_cons,
            Binder.env] at ih ⊢
          rw [TranslateDialectScalar.semScalar]
          exact ih _
      | zero x t =>
          simp only [wrapAll, List.foldr_cons, Binder.wrap, bindersEnv, List.foldl_cons,
            Binder.env] at ih ⊢
          rw [TranslateDialectScalar.semScalar]
          exact ih _

/-- **The denotation of the binder prefix.** A run of a command is a run of its core from
    the environment its binders produce. -/
theorem semScalar_peelBinders (c : LowCT) (env : SEnvScalar) :
    semScalar c env = semScalar (peelBinders c).2 (bindersEnv (peelBinders c).1 env) := by
  conv_lhs => rw [← wrapAll_peelBinders c]
  exact semScalar_wrapAll _ _ env

/-! ## 3. Route selection and dispatch on the core -/

/-- The route of a command's core. -/
def analysePeeled (out : OutputForm) (src : LowCT) : Except RouteGap CompilePlan :=
  analyse out (peelBinders src).2

/-- `compile` on a command's core. -/
def compilePeeled {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (out : OutputForm) (src : LowCT)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64)))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Except RouteGap (CompileResult Γouter accCTy) :=
  compile out (peelBinders src).2 countVar vmBody accName init invs

/-- **`compilePeeled`'s program denotes the `JLoopBodyN` fold at the plan's trip count**,
    as `compile_denote` on the core. -/
theorem compilePeeled_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (out : OutputForm) (src : LowCT)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64)))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {r : CompileResult Γouter accCTy}
    (h : compilePeeled out src countVar vmBody accName init invs = .ok r)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : r.plan.bodyFront.front (accCTy := accCTy) vmBody accName r.body = some update)
    (V : Ctxt.Valuation Γouter) :
    ComL.denote r.prog V
      = JLoopBodyN.denote ⟨r.trip.value V, update⟩ (Expr.lookupArgs invs V)
          (init.lookup V) :=
  compile_denote out _ countVar vmBody accName init invs h hupd V

/-! ## 4. The stages of a compilation -/

/-- **The stages of a compilation.** A result of `compile` comes from a split `sp` of the
    source, the plan of `sp`, the trip count of the plan, and a front output on the body of
    `sp`, which is the result's body. -/
theorem compile_stages {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (out : OutputForm) (src : LowCT)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64)))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {r : CompileResult Γouter accCTy}
    (h : compile out src countVar vmBody accName init invs = .ok r) :
    ∃ sp u, split src = .ok sp ∧ plan out sp = .ok r.plan ∧ tripOf r.plan countVar = .ok r.trip ∧
      r.body = sp.body ∧
      r.plan.bodyFront.front (accCTy := accCTy) vmBody accName r.body = some u := by
  unfold compile at h
  split at h
  · exact absurd h (by simp)
  · rename_i sp hsp
    split at h
    · exact absurd h (by simp)
    · rename_i p hp
      split at h
      · exact absurd h (by simp)
      · rename_i trip htrip
        split at h
        · exact absurd h (by simp)
        · rename_i u hu
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · cases h
                exact ⟨sp, u, hsp, hp, htrip, rfl, hu⟩
              · exact absurd h (by simp)

/-- The split of a runtime-count loop node whose body has no loop: the shape `runtimeN`,
    the node's body, no tail and no prologue. -/
theorem split_rForRuntime (x : String) (b : SExpr) (body : LowCT) (hd : loopDepth body = 0) :
    split (.RForRuntime x b body) =
      .ok { shape := .runtimeN, body := body, hasTail := false, prologueCmds := 0,
            loopDepth := 1 } := by
  simp [split, CarryChainSelect.flattenSeq, isLoopNode, hd]

/-- A plan of a split of shape `runtimeN` has the loop shape `runtimeN`. -/
theorem plan_loopShape_runtimeN (out : OutputForm) (sp : SourceSplit)
    (hs : sp.shape = .runtimeN) {p : CompilePlan} (h : plan out sp = .ok p) :
    p.loopShape = .runtimeN := by
  unfold plan at h
  rw [hs] at h
  dsimp only at h
  cases hb : bodyFrontOf sp.body <;> simp only [hb] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (cases h; rfl)

/-- **A compiled runtime-count loop node.** When `compile` succeeds on a runtime-count loop
    node whose body has no loop, with the count variable `cv`, the result's body is the
    node's body and its trip count is read from `cv`. -/
theorem compile_rForRuntime {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (out : OutputForm) (x : String) (b : SExpr) (body : LowCT) (hd : loopDepth body = 0)
    (cv : Ctxt.Var Γouter (JasminTy.reg 64))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {r : CompileResult Γouter accCTy}
    (h : compile out (.RForRuntime x b body) (some cv) vmBody accName init invs = .ok r) :
    r.body = body ∧ r.trip = .runtime cv ∧
      ∃ u, r.plan.bodyFront.front (accCTy := accCTy) vmBody accName body = some u := by
  obtain ⟨sp, u, hsp, hp, htrip, hbody, hu⟩ := compile_stages out _ _ vmBody accName init invs h
  rw [split_rForRuntime x b body hd] at hsp
  cases hsp
  have hshape := plan_loopShape_runtimeN out _ rfl hp
  simp only at hbody
  refine ⟨hbody, ?_, u, hbody ▸ hu⟩
  simp only [tripOf, hshape, Except.ok.injEq] at htrip
  exact htrip.symm

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
