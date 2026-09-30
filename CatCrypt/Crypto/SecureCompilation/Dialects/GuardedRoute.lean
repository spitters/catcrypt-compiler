/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlanPeel
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC

@[expose] public section

set_option autoImplicit false

/-!
# The guarded scalar semantics of the two routes, and their denotation

A function body reaches the dialect by one of two routes: straight-line, through the
guarded translator `translateDialectGuardedIn` from a bound input list `S`; or one
runtime-count loop under a prefix of binders, whose trip body is converted by the guarded
conversion and compiled by `FrontRoutePlan.compile`.

`semRouteG S c` is the scalar semantics of both routes. When the core of `c` under its
binders (`peelBinders`) is a runtime-count loop `RForRuntime x (SVar n) body`, it runs the
binders and then the trip fold `guardedTrips` of `body` over the word the count `n` holds,
with the bound list extended by the word binders (`boundAfter`). Otherwise it is
`semScalar` of the guarded conversion `ifConvert none S 0 c`, the semantics
`translateDialectGuardedIn` realises. On the guarded fragment, which has no loop, the second
case always applies (`semRouteG_of_covered`).

The denotation of each route:

* straight line: the jasmin program lowered from `translateDialectGuardedIn` returning a
  name denotes that name's value after the `semScalar` run of the conversion
  (`translateDialectGuardedIn_denote`);
* loop: the loop program `FrontRoutePlan.compile` produces on
  `RForRuntime x (SVar n) T`, with a trip body `T` in the straight covered fragment and the
  plain body front, denotes the accumulator value `accTrips` computes: the trip body run
  under `semScalar`, trip by trip, from the environment of the body `VarMap` at the
  accumulator, the trip index and the invariants (`loopRoute_denote`).

## Main results

* `boundAfter`, `semRouteG` — the bound list after a binder prefix, and the route
  semantics.
* `peelBinders_covered`, `semRouteG_of_covered` — on the guarded fragment the route
  semantics is `semScalar` of the guarded conversion.
* `semRouteG_loop` — the route semantics of a loop under binders.
* `translateDialectGuardedIn_denote` — denotation of the straight-line route.
* `envOf`, `accOf`, `accTrips` — the accumulator semantics of the loop route.
* `loopDepth_of_isCoveredS`, `denote_of_accTrips`, `loopRoute_denote` — denotation of the
  loop route.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute

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
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
  (ifConvert IsCoveredSCtlGuarded ifConvert_covered)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree (translateDialectGuardedIn)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop (guardedTrips)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC (frontLoopBodyJ_stepC)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The route semantics -/

/-- The bound list after the binders `bs`, outermost first, from the bound list `S`: each
    word binder puts its name in front, as the guarded conversion of `RLetU64Zero` does. -/
def boundAfter : List Binder → List String → List String
  | [], S => S
  | .u64Zero x :: bs, S => boundAfter bs (x :: S)
  | .zero _ _ :: bs, S => boundAfter bs S

/-- **The guarded scalar semantics of the two routes** from the bound list `S`. A runtime-count
    loop over a count variable under binders runs the binders and then `guardedTrips` of its
    body over the word the count holds; any other command runs as `semScalar` of its guarded
    conversion. -/
def semRouteG (S : List String) (c : LowCT) (env : SEnvScalar) : Option SEnvScalar :=
  match peelBinders c with
  | (bs, .RForRuntime x (.SVar n) body) =>
      match bindersEnv bs env n with
      | some ⟨.sword 64, w⟩ => guardedTrips x (boundAfter bs S) body w.toNat (bindersEnv bs env)
      | _ => none
  | _ => semScalar (ifConvert none S 0 c).1 env

/-- The core of a command of the guarded fragment is no runtime-count loop. -/
theorem peelBinders_covered {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    ∀ x b body, (peelBinders c).2 ≠ .RForRuntime x b body := by
  induction hc with
  | rLetU64Zero _ _ ih => simpa [peelBinders] using ih
  | _ => intro x b body h; simp [peelBinders] at h

/-- **On the guarded fragment the route semantics is the guarded conversion's.** -/
theorem semRouteG_of_covered {c : LowCT} (hc : IsCoveredSCtlGuarded c) (S : List String)
    (env : SEnvScalar) : semRouteG S c env = semScalar (ifConvert none S 0 c).1 env := by
  unfold semRouteG
  split
  · rename_i bs x n body h
    exact absurd (congrArg Prod.snd h) (peelBinders_covered hc x _ body)
  · rfl

/-- The route semantics of a runtime-count loop under binders. -/
theorem semRouteG_loop {c : LowCT} {bs : List Binder} {x n : String} {body : LowCT}
    (h : peelBinders c = (bs, .RForRuntime x (.SVar n) body)) (S : List String)
    (env : SEnvScalar) :
    semRouteG S c env =
      match bindersEnv bs env n with
      | some ⟨.sword 64, w⟩ => guardedTrips x (boundAfter bs S) body w.toNat (bindersEnv bs env)
      | _ => none := by
  unfold semRouteG
  rw [h]

/-! ## 2. The straight-line route -/

/-- **Denotation of the straight-line route.** For a command of the guarded fragment, a
    `VarMap`, valuation and environment that are consistent, and a `semScalar` run of the
    guarded conversion from the bound list `S` leaving `val` in `name`: the jasmin program
    lowered from the output of `translateDialectGuardedIn` returning the slot of `name`
    denotes `ctTransTy val`. -/
theorem translateDialectGuardedIn_denote {c : LowCT} (hc : IsCoveredSCtlGuarded c)
    {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) (S : List String) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env env' : SEnvScalar) (name : String)
    (w : CVar o.Γ' t) (val : ⟦t⟧) (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (htr : translateDialectGuardedIn vm S c = some o) (hcons : ConsistentS vm V env)
    (hsem : semScalar (ifConvert none S 0 c).1 env = some env')
    (hname : o.vm.lookup name = some ⟨t, w⟩) (hval : env' name = some ⟨t, val⟩)
    (hret : o.cont (Com.ret (toVIRVar w)) = some com)
    (hcom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy val :=
  CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq vm _ o V env env' name w val
    com jcom (.ofStraight (ifConvert_covered hc none S 0 (fun _ h => by cases h))) htr hcons
    hsem hname hval hret hcom

/-! ## 3. The loop route -/

/-- The environment of a `VarMap` at a valuation: each name bound in the `VarMap` holds its
    slot's value. -/
def envOf {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    SEnvScalar :=
  fun s => (vm.lookup s).map (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))

theorem consistentS_envOf {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) : ConsistentS vm V (envOf vm V) :=
  fun _ => rfl

/-- The value of type `t` an environment holds at `name`. -/
def accOf (t : CryptoTy) (name : String) (e : SEnvScalar) : Option ⟦t⟧ :=
  match e name with
  | some ⟨t', v⟩ => if h : t' = t then some (h ▸ v) else none
  | none => none

theorem eq_of_accOf {t : CryptoTy} {name : String} {e : SEnvScalar} {a : ⟦t⟧}
    (h : accOf t name e = some a) : e name = some ⟨t, a⟩ := by
  unfold accOf at h
  split at h
  · rename_i t' v hv
    split at h
    · rename_i ht
      subst ht
      cases h
      exact hv
    · cases h
  · cases h

/-- **The accumulator semantics of the loop route.** `accTrips vm accName T invsC k a` runs
    the trip body `T` under `semScalar` for the trips `0, …, k - 1`: trip `t` starts from the
    environment of `vm` at the accumulator, the word `t` and the invariants `invsC`, and
    reads the next accumulator from `accName`. -/
def accTrips {accCTy : CryptoTy} {invCTys : Ctx}
    (vm : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String) (T : LowCT)
    (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys) :
    Nat → ⟦accCTy⟧ → Option ⟦accCTy⟧
  | 0, a => some a
  | k + 1, a => (accTrips vm accName T invsC k a).bind fun a' =>
      (semScalar T (envOf vm (.cons a' (.cons (BitVec.ofNat 64 k) invsC)))).bind
        (accOf accCTy accName)

/-- A command of the straight covered fragment has no loop node. -/
theorem loopDepth_of_isCoveredS {c : LowCT} (hc : IsCoveredS c) : loopDepth c = 0 := by
  induction hc <;> simp_all [loopDepth]

/-- The loop fold of the plain front's body computes the accumulator semantics. -/
theorem denote_of_accTrips {accCTy : CryptoTy} {invCTys : Ctx}
    (vm : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String) (T : LowCT)
    (hT : IsCoveredSCtl T) (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vm accName T = some update) :
    ∀ (k : Nat) (a0 a : ⟦accCTy⟧), accTrips vm accName T invsC k a0 = some a →
      JLoopBodyN.denote (accTy := mapTy accCTy) (invTys := mapCtx invCTys)
        ⟨k, update⟩ (ctMapValD invsC) (ctTransTy a0) = ctTransTy a
  | 0, a0, a, h => by
      simp only [accTrips, Option.some.injEq] at h
      subst h
      rfl
  | k + 1, a0, a, h => by
      simp only [accTrips] at h
      cases ha : accTrips vm accName T invsC k a0 with
      | none => rw [ha] at h; cases h
      | some a' =>
          rw [ha, Option.bind_some] at h
          cases he : semScalar T (envOf vm (.cons a' (.cons (BitVec.ofNat 64 k) invsC))) with
          | none => rw [he] at h; cases h
          | some e' =>
              rw [he, Option.bind_some] at h
              erw [JLoopBodyN.denote_succ]
              rw [denote_of_accTrips vm accName T hT invsC hupd k a0 a' ha]
              exact frontLoopBodyJ_stepC vm accName T hT invsC k a' _ e' a
                (consistentS_envOf vm _) he (eq_of_accOf h) hupd

/-- **Denotation of the loop route.** Let `FrontRoutePlan.compile` produce `r` on the
    runtime-count loop node `RForRuntime x b T` with the count variable `cv`, where the trip
    body `T` is in the straight covered fragment and the plan's body front is `plain`. At a
    valuation `V` whose invariant and seed lookups are the transports of `invsC` and `a0`, if
    the accumulator semantics over the trip count `cv` holds takes `a0` to `a`, the program
    denotes `ctTransTy a`. -/
theorem loopRoute_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (x : String) (b : SExpr) (T : LowCT) (hT : IsCoveredS T)
    (cv : Ctxt.Var Γouter (JasminTy.reg 64))
    (vm : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {r : CompileResult Γouter accCTy}
    (h : compile .lprog (.RForRuntime x b T) (some cv) vm accName init invs = .ok r)
    (hplain : r.plan.bodyFront = .plain)
    (V : Ctxt.Valuation Γouter) (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (a0 a : ⟦accCTy⟧)
    (hinvs : Expr.lookupArgs invs V = ctMapValD invsC) (hinit : init.lookup V = ctTransTy a0)
    (htrips : accTrips vm accName T invsC (cv.lookup V).toNat a0 = some a) :
    ComL.denote r.prog V = ctTransTy a := by
  obtain ⟨hbody, htrip, u, hu⟩ :=
    compile_rForRuntime .lprog x b T (loopDepth_of_isCoveredS hT) cv vm accName init invs h
  have hu' : frontLoopBodyJ (accCTy := accCTy) vm accName T = some u := by
    rw [hplain] at hu; exact hu
  rw [compile_denote .lprog _ (some cv) vm accName init invs h (hbody ▸ hu) V, htrip, hinvs,
    hinit]
  exact denote_of_accTrips vm accName T (.ofStraight hT) invsC hu' _ a0 a htrips

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute
