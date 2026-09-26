/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-!
# The loop front: `LowCT` to `ComLoop catCryptDialect`

`translateDialectLoop` translates a runtime-trip loop `RForRuntime x (SVar n) body`,
alone or followed by a continuation (`RSeq (RForRuntime …) c₂`), to a
`ComLoop.forRt` node. A prefix of scalar sets (`RSeq (RScalarSet name k) c₂`) and
zero-initialised bindings (`RLetU64Zero name body`) becomes a chain of
`ComLoop.var` bindings of word constants. Every other `LowCT` term becomes a
`ComLoop.block` through `translateDialectControl`, returning its last scalar set,
or the default result name the enclosing binding or loop supplies (`blockRet`).

The loop node reads its trip count from the scalar `n`, which must be bound at
`.sword 64`. The loop-carried value is the scalar `loopAccName body` names, the
last scalar the body sets, which must be bound before the loop (its value is the
seed). The body runs over the context `accTy :: .sword 64 :: Γ`: the accumulator,
the trip index `x`, and the whole outer context `Γ` as invariants (`allVars Γ`).
It is front-compiled by `frontLoopBodyCD`, which caps the output of
`translateDialectControl` with `ret accName`. After the loop the accumulator name
is bound to the loop result.

## Semantics of a trip

In the target each trip starts from the entry valuation, with only the index and
the accumulator updated; the body's other writes do not survive a trip.
`semTripsInv` is the matching source-side fold of `semScalar`: trip `t` runs the
body on the entry environment updated at `x` to `t` and at the accumulator name to
the current accumulator value, and keeps the accumulator it leaves.
`runtimeLoopNode_denote` states the loop denotation against `semTripsInv`. The
`RustExec` rule of `RForRuntime` threads the whole state through the trips. On the
word fragment `IsCoveredAdeq`, the two agree on a body satisfying the decidable
trip frame `loopBodyFrame body x acc`: every name the body writes, other than the
accumulator and `x`, is written before the body reads it
(`semTripsInv_of_rustExec_rFor`).

## Main definitions

* `allVars` — every variable of a context, as an argument vector.
* `loopAccName` — the loop-carried scalar of a loop body.
* `runtimeLoopNode` — the `forRt` node of a runtime-trip loop.
* `blockRet` — a straight-line program returning a named scalar.
* `translateDialectLoopR`, `translateDialectLoop` — the loop front.
* `semTripsInv` — the source-side fold of the loop body.
* `loopReads`, `loopWrites`, `loopReadsOK`, `frameReads`, `loopBodyFrame` — the
  syntactic trip frame.

## Main results

* `lookupArgs_allVars` — `allVars Γ` reads back the whole valuation.
* `consistentS_bind` — binding a name to a value preserves `ConsistentS`.
* `frontLoopBodyCD_denote` — a front-compiled loop body computes the accumulator the
  body's `semScalar` run leaves.
* `foldl_body_eq_of_semTripsInv` — the trip fold of the loop body is `semTripsInv`.
* `runtimeLoopNode_denote`, `translateDialectLoop_rSeq_rForRuntime_denote` — the
  loop node denotes its continuation at the loop result.
* `rustExec_rsScalar_of_not_mem_loopWrites` — a `RustExec` run leaves every scalar
  outside `loopWrites` unchanged.
* `semTripsInv_of_rustExec_rFor` — the trip-wise fold agrees with the threaded run.
* `runtimeLoopNode_denote_rustExec`, `translateDialectLoop_rForRuntime_denote_rustExec`,
  `translateDialectLoop_rSeq_rScalarSet_rForRuntime_denote_rustExec` — the loop
  denotes the accumulator's exit word of a `RustExec` run.
* `blockRet_denote`, `translateDialectLoopR_rSeq_rScalarSet_denote`,
  `translateDialectLoopR_rLetU64Zero_denote` — the fallback and the prefix arms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoop

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar SEnvScalar.upd ConsistentS ConsistentS.lookup_eq semScalar IsCoveredSCtl
   translateDialectControl_denote_ctl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyCD)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote (frontLoopBodyCD_inv)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The whole context as invariants -/

/-- Shift an argument vector of variables under one more binding. -/
def shiftVars {d : Dialect.{0, 0}} {Γ : Ctxt d} {s : d.Ty} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (s :: Γ) ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (.there v) (shiftVars rest)

/-- Every variable of `Γ`, in order, as an argument vector. -/
def allVars {d : Dialect.{0, 0}} : (Γ : Ctxt d) → HVector (fun ty => Ctxt.Var Γ ty) Γ
  | [] => .nil
  | _ :: Γ => .cons .here (shiftVars (allVars Γ))

/-- A shifted argument vector reads the valuation below the new binding. -/
theorem lookupArgs_shiftVars {d : Dialect.{0, 0}} [TyDenote d.Ty] {Γ : Ctxt d} {s : d.Ty}
    (x : ⟦s⟧) (V : Ctxt.Valuation Γ) :
    {tys : List d.Ty} → (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    Expr.lookupArgs (shiftVars (s := s) hv) (V.extend x) = Expr.lookupArgs hv V
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons (v.lookup V) (Expr.lookupArgs (shiftVars (s := s) rest) (V.extend x)) = _
      rw [lookupArgs_shiftVars x V rest]
      rfl

/-- `allVars Γ` reads back the whole valuation. -/
theorem lookupArgs_allVars {d : Dialect.{0, 0}} [TyDenote d.Ty] :
    {Γ : Ctxt d} → (V : Ctxt.Valuation Γ) → Expr.lookupArgs (allVars Γ) V = V
  | [], .nil => rfl
  | _ :: _, .cons x V =>
      congrArg (HVector.cons x) ((lookupArgs_shiftVars x V (allVars _)).trans (lookupArgs_allVars V))

/-! ## 2. The loop front -/

/-- The loop-carried scalar of a loop body: the last scalar it sets. -/
def loopAccName : LowCT → Option String
  | .RScalarSet x _ => some x
  | .RScalarSetExpr x _ => some x
  | .RSeq c₁ c₂ =>
      match loopAccName c₂ with
      | some x => some x
      | none => loopAccName c₁
  | _ => none

/-- A `ComLoop catCryptDialect` program over `Γ` with its result type. -/
abbrev LoopOut (Γ : Ctx) : Type := Σ t : CryptoTy, ComLoop catCryptDialect Γ t

/-- The continuation returning the value at `.here`. -/
def retHere {Γ : Ctx} {t : CryptoTy} (_ : VarMap (t :: Γ)) : Option (LoopOut (t :: Γ)) :=
  some ⟨t, .block (.ret .here)⟩

/-- The `forRt` node of `RForRuntime x (SVar n) body` with the continuation `kont`,
    which receives the `VarMap` binding the accumulator name to the loop result.
    `none` unless `n` is bound at `.sword 64`, the accumulator name is bound, and
    the body front-compiles. -/
def runtimeLoopNode {Γ : Ctx} (vm : VarMap Γ) (x n : String) (body : LowCT)
    (kont : ∀ {t : CryptoTy}, VarMap (t :: Γ) → Option (LoopOut (t :: Γ))) :
    Option (LoopOut Γ) :=
  match loopAccName body with
  | none => none
  | some accName =>
      match vm.lookup n, vm.lookup accName with
      | some ⟨.sword 64, cv⟩, some ⟨accTy, av⟩ =>
          match frontLoopBodyCD (accCTy := accTy)
              ((vm.bind (t := .sword 64) x).bind (t := accTy) accName) accName body,
            kont (vm.bind (t := accTy) accName) with
          | some bodyCom, some ⟨s, k⟩ =>
              some ⟨s, .forRt (invTys := Γ) (toVIRVar cv) (toVIRVar av)
                (allVars (d := catCryptDialect) Γ) bodyCom k⟩
          | _, _ => none
      | _, _ => none

/-- The straight-line program `c` returning the scalar named `res` at its end:
    `translateDialectControl` capped with `ret` of the slot `res` resolves to.
    `none` when the front declines or `res` is unbound at the end. -/
def blockRet {Γ : Ctx} (vm : VarMap Γ) (res : String) (c : LowCT) : Option (LoopOut Γ) :=
  match translateDialectControl vm c with
  | some o =>
      match o.vm.lookup res with
      | some ⟨t, v⟩ => (o.cont (Com.ret (toVIRVar v))).map fun com => ⟨t, .block com⟩
      | none => none
  | none => none

/-- The word constant `n` as a `catCryptDialect` expression. -/
def constWord {Γ : Ctx} (n : Nat) : Expr catCryptDialect Γ (.sword 64) :=
  { op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil }

/-- The loop front at the default result name `dflt`.

    * A runtime-trip loop over a scalar bound becomes a `forRt` node returning the
      loop result; followed by a continuation `c₂`, a `forRt` node continuing with
      the translation of `c₂` at the default result name `loopAccName body`.
    * A scalar set `RScalarSet name n` followed by `c₂` becomes a `ComLoop.var`
      binding of the constant, continuing with `c₂` at the default result `name`;
      `RLetU64Zero name body` becomes a binding of `0` continuing with `body`.
    * Every other term is translated by `translateDialectControl` and returns the
      scalar `loopAccName c` names, or `dflt` when `c` sets no scalar (`blockRet`). -/
def translateDialectLoopR {Γ : Ctx} (dflt : Option String) (vm : VarMap Γ) :
    LowCT → Option (LoopOut Γ)
  | .RForRuntime x (.SVar n) body => runtimeLoopNode vm x n body retHere
  | .RSeq (.RForRuntime x (.SVar n) body) c₂ =>
      runtimeLoopNode vm x n body (fun vm' => translateDialectLoopR (loopAccName body) vm' c₂)
  | .RSeq (.RScalarSet name n) c₂ =>
      (translateDialectLoopR (some name) (vm.bind (t := .sword 64) name) c₂).map
        fun p => ⟨p.1, .var (constWord n) p.2⟩
  | .RLetU64Zero name body =>
      (translateDialectLoopR dflt (vm.bind (t := .sword 64) name) body).map
        fun p => ⟨p.1, .var (constWord 0) p.2⟩
  | c =>
      match loopAccName c <|> dflt with
      | some res => blockRet vm res c
      | none => none

/-- The loop front: `translateDialectLoopR` with no default result name. -/
def translateDialectLoop {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) : Option (LoopOut Γ) :=
  translateDialectLoopR none vm c

/-- `translateDialectLoopR` on a runtime-trip loop. -/
theorem translateDialectLoopR_rForRuntime {Γ : Ctx} (dflt : Option String) (vm : VarMap Γ)
    (x n : String) (body : LowCT) :
    translateDialectLoopR dflt vm (.RForRuntime x (.SVar n) body) =
      runtimeLoopNode vm x n body retHere := rfl

/-- `translateDialectLoop` on a runtime-trip loop. -/
theorem translateDialectLoop_rForRuntime {Γ : Ctx} (vm : VarMap Γ) (x n : String)
    (body : LowCT) :
    translateDialectLoop vm (.RForRuntime x (.SVar n) body) =
      runtimeLoopNode vm x n body retHere := rfl

/-- `translateDialectLoopR` on a runtime-trip loop followed by a continuation. -/
theorem translateDialectLoopR_rSeq_rForRuntime {Γ : Ctx} (dflt : Option String)
    (vm : VarMap Γ) (x n : String) (body c₂ : LowCT) :
    translateDialectLoopR dflt vm (.RSeq (.RForRuntime x (.SVar n) body) c₂) =
      runtimeLoopNode vm x n body
        (fun vm' => translateDialectLoopR (loopAccName body) vm' c₂) := rfl

/-- `translateDialectLoopR` on a scalar set followed by a continuation. -/
theorem translateDialectLoopR_rSeq_rScalarSet {Γ : Ctx} (dflt : Option String)
    (vm : VarMap Γ) (name : String) (n : Nat) (c₂ : LowCT) :
    translateDialectLoopR dflt vm (.RSeq (.RScalarSet name n) c₂) =
      (translateDialectLoopR (some name) (vm.bind (t := .sword 64) name) c₂).map
        fun p => ⟨p.1, .var (constWord n) p.2⟩ := rfl

/-- `translateDialectLoopR` on a zero-initialised scalar binding. -/
theorem translateDialectLoopR_rLetU64Zero {Γ : Ctx} (dflt : Option String)
    (vm : VarMap Γ) (name : String) (body : LowCT) :
    translateDialectLoopR dflt vm (.RLetU64Zero name body) =
      (translateDialectLoopR dflt (vm.bind (t := .sword 64) name) body).map
        fun p => ⟨p.1, .var (constWord 0) p.2⟩ := rfl

/-! ## 3. The loop body -/

/-- Binding a name to a value preserves `ConsistentS`. -/
theorem consistentS_bind {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (name : String) (v : ⟦t⟧) :
    ConsistentS (vm.bind (t := t) name) (V.extend v) (env.upd name v) := by
  intro s
  by_cases hsd : s = name
  · subst hsd
    simp only [VarMap.bind, SEnvScalar.upd]
    rfl
  · simp only [VarMap.bind, SEnvScalar.upd, if_neg hsd]
    rw [← hc s]
    cases hl : vm.lookup s with
    | none => rfl
    | some p =>
        obtain ⟨t', w⟩ := p
        rfl

/-- **A front-compiled loop body computes the accumulator.** For a covered body, a
    valuation consistent with the environment, and a `semScalar` run leaving
    `accval` in `accName`, the program `frontLoopBodyCD` emits denotes `accval`. -/
theorem frontLoopBodyCD_denote {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γbody)
    (env env' : SEnvScalar) (accval : ⟦accCTy⟧)
    (hc : ConsistentS vmBody V env)
    (hsem : semScalar body env = some env')
    (hval : env' accName = some ⟨accCTy, accval⟩)
    {com : Com catCryptDialect Γbody accCTy}
    (hcd : frontLoopBodyCD (accCTy := accCTy) vmBody accName body = some com) :
    com.denote V = accval := by
  obtain ⟨o, w, htr, hlk, hret⟩ := frontLoopBodyCD_inv hcd
  obtain ⟨V', hc', hcont⟩ := translateDialectControl_denote_ctl hcov vmBody V env env' o hc htr hsem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hret, Option.some.injEq] at hcom'
  subst hcom'
  rw [hden]
  exact hc'.lookup_eq hlk hval

/-! ## 4. The source-side trip fold -/

/-- The source-side fold of a runtime-trip loop body: trip `t` runs `semScalar body`
    on `env` updated at `x` to `t` and at `accName` to the current accumulator,
    and keeps the value of `accName` it leaves. `none` when a trip fails or leaves
    `accName` unbound or at another type. -/
def semTripsInv (body : LowCT) (x accName : String) (accTy : CryptoTy) (env : SEnvScalar) :
    List Nat → ⟦accTy⟧ → Option ⟦accTy⟧
  | [], a => some a
  | t :: ts, a =>
      match semScalar body
          ((env.upd x (t := .sword 64) (BitVec.ofNat 64 t)).upd accName (t := accTy) a) with
      | some env' =>
          match env' accName with
          | some ⟨ty, v⟩ => if h : ty = accTy then semTripsInv body x accName accTy env ts (h ▸ v)
                            else none
          | none => none
      | none => none

/-- **The trip fold of the loop body is `semTripsInv`.** For a covered body
    front-compiled over the loop-body `VarMap`, and a valuation consistent with the
    environment, folding the body over the trips `L` from `a` gives the value
    `semTripsInv` computes. -/
theorem foldl_body_eq_of_semTripsInv {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (x accName : String) {accTy : CryptoTy} (body : LowCT)
    (hcov : IsCoveredSCtl body)
    {bodyCom : Com catCryptDialect (accTy :: .sword 64 :: Γ) accTy}
    (hcd : frontLoopBodyCD (accCTy := accTy)
      ((vm.bind (t := .sword 64) x).bind (t := accTy) accName) accName body = some bodyCom) :
    (L : List Nat) → (a aF : ⟦accTy⟧) →
    semTripsInv body x accName accTy env L a = some aF →
    L.foldl (fun acc t => bodyCom.denote (.cons acc (.cons (BitVec.ofNat 64 t) V))) a = aF
  | [], a, aF, h => by
      simp only [semTripsInv, Option.some.injEq] at h
      exact h
  | t :: ts, a, aF, h => by
      simp only [List.foldl_cons]
      simp only [semTripsInv] at h
      split at h
      · rename_i env' hsem
        split at h
        · rename_i ty v hv
          split at h
          · rename_i hty
            subst hty
            have hcT : ConsistentS ((vm.bind (t := .sword 64) x).bind (t := ty) accName)
                (.cons a (.cons (BitVec.ofNat 64 t) V))
                ((env.upd x (t := .sword 64) (BitVec.ofNat 64 t)).upd accName (t := ty) a) :=
              consistentS_bind _ _ _ (consistentS_bind vm V env hc x _) accName a
            rw [frontLoopBodyCD_denote _ accName body hcov _ _ env' v hcT hsem hv hcd]
            exact foldl_body_eq_of_semTripsInv vm V env hc x accName body hcov hcd ts v aF h
          · cases h
        · cases h
      · cases h

/-! ## 5. The loop node -/

/-- **The loop node denotes its continuation at the loop result.** Suppose
    `runtimeLoopNode vm x n body kont = some cl`, the body is covered, `V` is
    consistent with `env`, `n` and the accumulator name resolve to `cv` and `av`,
    and the source-side fold from the seed `av` over `count` trips gives `aF`. Then
    `kont` accepts the post-loop `VarMap`, and `cl` denotes the continuation at `V`
    extended with `aF`. -/
theorem runtimeLoopNode_denote {Γ : Ctx} (vm : VarMap Γ) (x n : String) (body : LowCT)
    (kont : ∀ {t : CryptoTy}, VarMap (t :: Γ) → Option (LoopOut (t :: Γ)))
    {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : runtimeLoopNode vm x n body kont = some ⟨s, cl⟩)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {accName : String} (hacc : loopAccName body = some accName)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {accTy : CryptoTy} {av : CVar Γ accTy} (ha : vm.lookup accName = some ⟨accTy, av⟩)
    {aF : ⟦accTy⟧}
    (hsem : semTripsInv body x accName accTy env
      (List.range ((toVIRVar cv).lookup V).toNat) ((toVIRVar av).lookup V) = some aF) :
    ∃ k, kont (vm.bind (t := accTy) accName) = some ⟨s, k⟩ ∧
      cl.denote V = k.denote (V.extend aF) := by
  unfold runtimeLoopNode at h
  rw [hacc] at h
  simp only [hn, ha] at h
  split at h
  · rename_i bodyCom s' k hcd hk
    simp only [Option.some.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    refine ⟨k, hk, ?_⟩
    rw [ComLoop.denote_forRt (d := catCryptDialect)]
    congr 2
    show (List.range ((toVIRVar cv).lookup V).toNat).foldl
        (fun acc t => bodyCom.denote (.cons acc (.cons (BitVec.ofNat 64 t)
          (Expr.lookupArgs (allVars (d := catCryptDialect) Γ) V)))) ((toVIRVar av).lookup V) = aF
    rw [lookupArgs_allVars (d := catCryptDialect)]
    exact foldl_body_eq_of_semTripsInv vm V env hc x accName body hcov hcd _ _ _ hsem
  · cases h

/-- `runtimeLoopNode_denote` at the `RSeq (RForRuntime x (SVar n) body) c₂` arm of
    `translateDialectLoopR`: the continuation is the loop front's translation of
    `c₂` under the post-loop `VarMap`, at the default result name `accName`. -/
theorem translateDialectLoop_rSeq_rForRuntime_denote {Γ : Ctx} (dflt : Option String)
    (vm : VarMap Γ)
    (x n : String) (body c₂ : LowCT) {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoopR dflt vm (.RSeq (.RForRuntime x (.SVar n) body) c₂) =
      some ⟨s, cl⟩)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {accName : String} (hacc : loopAccName body = some accName)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {accTy : CryptoTy} {av : CVar Γ accTy} (ha : vm.lookup accName = some ⟨accTy, av⟩)
    {aF : ⟦accTy⟧}
    (hsem : semTripsInv body x accName accTy env
      (List.range ((toVIRVar cv).lookup V).toNat) ((toVIRVar av).lookup V) = some aF) :
    ∃ k, translateDialectLoopR (some accName) (vm.bind (t := accTy) accName) c₂ =
        some ⟨s, k⟩ ∧ cl.denote V = k.denote (V.extend aF) := by
  have := runtimeLoopNode_denote vm x n body _ h hcov V env hc hacc hn ha hsem
  rwa [hacc] at this

/-- **The runtime-trip loop denotes the loop result.** At the `RForRuntime x (SVar n)
    body` arm of `translateDialectLoop`, under the hypotheses of
    `runtimeLoopNode_denote`, the program has the accumulator type and denotes the
    value `aF` of the source-side fold. -/
theorem translateDialectLoop_rForRuntime_denote {Γ : Ctx} (vm : VarMap Γ)
    (x n : String) (body : LowCT) {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoop vm (.RForRuntime x (.SVar n) body) = some ⟨s, cl⟩)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {accName : String} (hacc : loopAccName body = some accName)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {accTy : CryptoTy} {av : CVar Γ accTy} (ha : vm.lookup accName = some ⟨accTy, av⟩)
    {aF : ⟦accTy⟧}
    (hsem : semTripsInv body x accName accTy env
      (List.range ((toVIRVar cv).lookup V).toNat) ((toVIRVar av).lookup V) = some aF) :
    ∃ hs : accTy = s, cl.denote V = hs ▸ aF := by
  obtain ⟨k, hk, hd⟩ := runtimeLoopNode_denote vm x n body retHere h hcov V env hc hacc hn ha hsem
  simp only [retHere, Option.some.injEq, Sigma.mk.inj_iff] at hk
  obtain ⟨rfl, hk⟩ := hk
  cases hk
  exact ⟨rfl, hd⟩

/-! ## 6. The trip-wise fold against the threaded run -/

open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
  (EnvBoundOn ScalarInRange IsCoveredAdeq IsCoveredAdeqS afterB readsOK varsBoundIn le_afterB
   rustExec_semScalar_agree_scoped scalarInRange_upd envBoundOn_mono envBoundOn_upd)
open CatCrypt.Crypto.Jasmin.LowCT (RustExec RustState rsSetScalar LeafSpec)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName)

/-- The variables an `SExpr` reads, on the arms `varsBoundIn` constrains. -/
def sexprReads : SExpr → List String
  | .SVar x => [x]
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => sexprReads a ++ sexprReads b
  | _ => []

/-- The scalars a loop body reads, on the arms `readsOK` constrains. -/
def loopReads : LowCT → List String
  | .RBlock b => loopReads b
  | .RSeq c₁ c₂ => loopReads c₁ ++ loopReads c₂
  | .RLetU64Zero _ b => loopReads b
  | .RScalarSetExpr _ e => sexprReads e
  | .RFor _ _ b => loopReads b
  | .RIfNz name _ _ => [name]
  | _ => []

/-- The scalars a loop body may write: scalar-set destinations, `RLetU64Zero`
    names and `RFor` counters. -/
def loopWrites : LowCT → List String
  | .RBlock b => loopWrites b
  | .RSeq c₁ c₂ => loopWrites c₁ ++ loopWrites c₂
  | .RLetU64Zero n b => n :: loopWrites b
  | .RScalarSet n _ => [n]
  | .RScalarSetExpr x _ => [x]
  | .RFor x _ b => x :: loopWrites b
  | .RIfNz _ t e => loopWrites t ++ loopWrites e
  | _ => []

/-- The list form of `afterB`: the bound names after `c` from the bound list `K`. -/
def loopAfter (K : List String) : LowCT → List String
  | .RBlock b => loopAfter K b
  | .RSeq c₁ c₂ => loopAfter (loopAfter K c₁) c₂
  | .RLetU64Zero n b => loopAfter (K ++ [n]) b
  | .RScalarSet n _ => K ++ [n]
  | .RScalarSetExpr x _ => K ++ [x]
  | _ => K

/-- Whether every variable an `SExpr` reads is in `K`. -/
def sexprVarsIn (K : List String) (e : SExpr) : Bool := (sexprReads e).all (K.contains ·)

/-- The decidable form of `readsOK` at the bound list `K`. -/
def loopReadsOK (K : List String) : LowCT → Bool
  | .RBlock b => loopReadsOK K b
  | .RSeq c₁ c₂ => loopReadsOK K c₁ && loopReadsOK (loopAfter K c₁) c₂
  | .RLetU64Zero n b => loopReadsOK (K ++ [n]) b
  | .RScalarSetExpr _ e => sexprVarsIn K e
  | .RFor x _ b => loopReadsOK (K ++ [x]) b
  | .RIfNz name _ _ => K.contains name
  | _ => true

/-- The names a loop body reads from the entry environment: its reads other than
    the counter `x`, the accumulator `acc`, and the names it writes. -/
def frameReads (body : LowCT) (x acc : String) : List String :=
  (loopReads body).filter (fun y => y != x && y != acc && !(loopWrites body).contains y)

/-- A name that does not start with the fresh-temporary prefix `"__sx"`. -/
def notTmpB (s : String) : Bool := s.toList.take 4 != "__sx".toList

/-- **The trip-frame condition of a loop body.** The accumulator differs from the
    counter and is not a fresh temporary, and every read of the body is bound, in
    the `readsOK` sense, from the counter, the accumulator and `frameReads`. A name
    the body writes other than the counter and the accumulator is then written
    before the body reads it, so each trip reads only the counter, the accumulator
    and names no trip changes. -/
def loopBodyFrame (body : LowCT) (x acc : String) : Bool :=
  acc != x && notTmpB acc && loopReadsOK (x :: acc :: frameReads body x acc) body

/-- A name `notTmpB` accepts is not a fresh temporary. -/
theorem not_isTmpName_of_notTmpB {s : String} (h : notTmpB s = true) : ¬ isTmpName s := by
  rintro ⟨k, rfl⟩
  simp only [notTmpB, TranslateDialectDirectArms.tmpName, String.toList_append] at h
  rw [List.take_left' (by rfl)] at h
  simp at h

/-- `afterB` on a list-membership predicate is membership in `loopAfter`. -/
theorem afterB_mem_eq : ∀ (c : LowCT) (K : List String),
    afterB (· ∈ K) c = (· ∈ loopAfter K c) := by
  intro c
  induction c with
  | RBlock b ih => exact ih
  | RSeq c₁ c₂ ih₁ ih₂ => intro K; simp only [afterB, loopAfter, ih₁, ih₂]
  | RLetU64Zero n b ih =>
      intro K
      have : (fun y => y ∈ K ∨ y = n) = (· ∈ K ++ [n]) := by funext y; simp
      simp only [afterB, loopAfter, this, ih]
  | RScalarSet n _ => intro K; funext y; simp [afterB, loopAfter]
  | RScalarSetExpr x _ => intro K; funext y; simp [afterB, loopAfter]
  | _ => intro K; rfl

/-- `sexprVarsIn` implies `varsBoundIn`. -/
theorem varsBoundIn_of_sexprVarsIn (K : List String) :
    ∀ e : SExpr, sexprVarsIn K e = true → varsBoundIn (· ∈ K) e := by
  intro e
  induction e with
  | SVar x => intro h; simpa [sexprVarsIn, sexprReads, varsBoundIn] using h
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro h
      simp only [sexprVarsIn, sexprReads, List.all_append, Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | _ => intro _; trivial

/-- `loopReadsOK` implies `readsOK`. -/
theorem readsOK_of_loopReadsOK : ∀ (c : LowCT) (K : List String),
    loopReadsOK K c = true → readsOK (· ∈ K) c := by
  intro c
  induction c with
  | RBlock b ih => exact ih
  | RSeq c₁ c₂ ih₁ ih₂ =>
      intro K h
      simp only [loopReadsOK, Bool.and_eq_true] at h
      refine ⟨ih₁ K h.1, ?_⟩
      rw [afterB_mem_eq]
      exact ih₂ _ h.2
  | RLetU64Zero n b ih =>
      intro K h
      have : (fun y => y ∈ K ∨ y = n) = (· ∈ K ++ [n]) := by funext y; simp
      show readsOK (fun y => y ∈ K ∨ y = n) b
      rw [this]
      exact ih _ h
  | RScalarSetExpr x e => intro K h; exact varsBoundIn_of_sexprVarsIn K e h
  | RFor x N b ih =>
      intro K h
      have : (fun y => y ∈ K ∨ y = x) = (· ∈ K ++ [x]) := by funext y; simp
      show readsOK (fun y => y ∈ K ∨ y = x) b
      rw [this]
      exact ih _ h
  | RIfNz name t e _ _ =>
      intro K h
      simpa [loopReadsOK, readsOK] using h
  | _ => intro _ _; trivial

/-- On the straight-line word fragment, a `RustExec` run leaves every scalar the
    command does not write unchanged. -/
theorem rustExec_rsScalar_of_not_mem_loopWrites_S {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hcov : IsCoveredAdeqS c) :
    ∀ {rs rs' : RustState}, RustExec N leafSpec c rs rs' →
      ∀ {y : String}, y ∉ loopWrites c → rs'.rsScalar y = rs.rsScalar y := by
  induction hcov with
  | rSkip => intro rs rs' h y _; cases h; rfl
  | rBlock _ ih =>
      intro rs rs' h y hy
      cases h with
      | block _ _ _ hb => exact ih hb hy
  | rSeq _ _ ih₁ ih₂ =>
      intro rs rs' h y hy
      simp only [loopWrites, List.mem_append, not_or] at hy
      cases h with
      | seq _ _ _ r₁ _ h₁ h₂ => exact (ih₂ h₂ hy.2).trans (ih₁ h₁ hy.1)
  | rLetU64Zero _ ih =>
      rename_i name body
      intro rs rs' h y hy
      simp only [loopWrites, List.mem_cons, not_or] at hy
      cases h with
      | letU64Zero _ _ _ _ hb =>
          rw [ih hb hy.2]
          simp [rsSetScalar, hy.1]
  | rScalarSet name _ =>
      intro rs rs' h y hy
      simp only [loopWrites, List.mem_singleton] at hy
      cases h
      simp [rsSetScalar, hy]
  | rScalarSetExpr x e _ _ =>
      intro rs rs' h y hy
      simp only [loopWrites, List.mem_singleton] at hy
      cases h
      simp [rsSetScalar, hy]

/-- A counted loop whose body leaves `y` unchanged leaves `y` unchanged. -/
theorem rustExec_rFor_rsScalar_of_body {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    {y : String} (hyx : y ≠ x)
    (hbody : ∀ {rs rs' : RustState}, RustExec N leafSpec body rs rs' →
      rs'.rsScalar y = rs.rsScalar y) :
    ∀ (k : Nat) {rs rs' : RustState}, RustExec N leafSpec (.RFor x k body) rs rs' →
      rs'.rsScalar y = rs.rsScalar y
  | 0, _, _, h => by cases h; rfl
  | k + 1, _, _, h => by
      cases h with
      | forSucc _ _ _ _ r₁ _ hf hb =>
          rw [hbody hb]
          simp only [rsSetScalar, beq_iff_eq, if_neg hyx]
          exact rustExec_rFor_rsScalar_of_body hyx hbody k hf

/-- **Write frame.** On the word fragment `IsCoveredAdeq`, a `RustExec` run leaves
    every scalar outside `loopWrites c` unchanged. -/
theorem rustExec_rsScalar_of_not_mem_loopWrites {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hcov : IsCoveredAdeq c) :
    ∀ {rs rs' : RustState}, RustExec N leafSpec c rs rs' →
      ∀ {y : String}, y ∉ loopWrites c → rs'.rsScalar y = rs.rsScalar y := by
  induction hcov with
  | ofStraight hs => exact rustExec_rsScalar_of_not_mem_loopWrites_S hs
  | @rFor x N' body _ _ ih =>
      intro rs rs' h y hy
      simp only [loopWrites, List.mem_cons, not_or] at hy
      exact rustExec_rFor_rsScalar_of_body hy.1 (fun hb => ih hb hy.2) N' h
  | rIfNz name mergeName tv ev _ _ _ =>
      intro rs rs' h y hy
      simp only [loopWrites, List.mem_append, List.mem_singleton, or_self] at hy
      cases h with
      | ifTrue _ _ _ _ _ _ _ _ hb => cases hb; simp [rsSetScalar, hy]
      | ifFalse _ _ _ _ _ _ hb => cases hb; simp [rsSetScalar, hy]

/-- `semTripsInv` over a concatenation is the fold over the first part followed by
    the fold over the second. -/
theorem semTripsInv_append (body : LowCT) (x accName : String) (accTy : CryptoTy)
    (env : SEnvScalar) :
    ∀ (L₁ L₂ : List Nat) (a : ⟦accTy⟧),
      semTripsInv body x accName accTy env (L₁ ++ L₂) a =
        (semTripsInv body x accName accTy env L₁ a).bind
          (semTripsInv body x accName accTy env L₂)
  | [], _, _ => rfl
  | t :: ts, L₂, a => by
      simp only [List.cons_append, semTripsInv]
      cases semScalar body ((env.upd x (t := .sword 64) (BitVec.ofNat 64 t)).upd accName
          (t := accTy) a) with
      | none => rfl
      | some env' =>
          simp only
          cases env' accName with
          | none => rfl
          | some p =>
              obtain ⟨ty, v⟩ := p
              simp only
              split
              · exact semTripsInv_append body x accName accTy env ts L₂ _
              · rfl

/-- **The trip-wise fold agrees with the threaded run.** For a word-fragment body
    satisfying `loopBodyFrame body x accName`, an entry environment binding the
    accumulator and `frameReads body x accName` to the `RustState` values, and a
    `RustExec` run of `RFor x k body` (`k ≤ 2^64`) to `rs'`, `semTripsInv` from the
    accumulator's entry word returns its exit word. The run also leaves every name
    of `frameReads` unchanged and keeps scalars in range. -/
theorem semTripsInv_of_rustExec_rFor {N : Nat} {leafSpec : LeafSpec} {body : LowCT}
    {x accName : String} (hcov : IsCoveredAdeq body) (hfr : loopBodyFrame body x accName = true)
    {rs : RustState} {env : SEnvScalar}
    (henv : EnvBoundOn rs env (· ∈ accName :: frameReads body x accName))
    (hir : ScalarInRange rs) :
    ∀ (k : Nat) (rs' : RustState), k ≤ 2 ^ 64 → RustExec N leafSpec (.RFor x k body) rs rs' →
      semTripsInv body x accName (.sword 64) env (List.range k)
          (BitVec.ofNat 64 (rs.rsScalar accName)) = some (BitVec.ofNat 64 (rs'.rsScalar accName)) ∧
        (∀ y ∈ frameReads body x accName, rs'.rsScalar y = rs.rsScalar y) ∧ ScalarInRange rs'
  | 0, rs', _, hexec => by
      cases hexec
      exact ⟨rfl, fun _ _ => rfl, hir⟩
  | k + 1, rs', hk, hexec => by
      cases hexec with
      | forSucc _ _ _ _ r₁ _ hfor hbody =>
          obtain ⟨hsem, hfrm, hir₁⟩ :=
            semTripsInv_of_rustExec_rFor hcov hfr henv hir k r₁ (by omega) hfor
          have hfr' := hfr
          simp only [loopBodyFrame, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfr'
          obtain ⟨⟨hax, hnt⟩, hrok⟩ := hfr'
          have hF : EnvBoundOn (rsSetScalar r₁ x k)
              ((env.upd x (t := .sword 64) (BitVec.ofNat 64 k)).upd accName (t := .sword 64)
                (BitVec.ofNat 64 (r₁.rsScalar accName)))
              (· ∈ x :: accName :: frameReads body x accName) := by
            intro y hy hnty
            by_cases hya : y = accName
            · subst hya
              simp [SEnvScalar.upd, rsSetScalar, hax]
            · by_cases hyx : y = x
              · subst hyx
                simp [SEnvScalar.upd, rsSetScalar, hya]
              · have hyf : y ∈ frameReads body x accName := by
                  simpa [hya, hyx] using hy
                simp only [SEnvScalar.upd, rsSetScalar, if_neg hya, if_neg hyx, beq_iff_eq]
                rw [henv y (List.mem_cons_of_mem _ hyf) hnty, hfrm y hyf]
          have hirT : ScalarInRange (rsSetScalar r₁ x k) := scalarInRange_upd hir₁ x (by omega)
          obtain ⟨O, hO, hOb, hir'⟩ := rustExec_semScalar_agree_scoped hcov hbody hF hirT
            (readsOK_of_loopReadsOK body _ hrok)
          have hOacc : O accName = some ⟨.sword 64, BitVec.ofNat 64 (rs'.rsScalar accName)⟩ :=
            hOb accName (le_afterB body _ accName (by simp)) (not_isTmpName_of_notTmpB hnt)
          refine ⟨?_, ?_, hir'⟩
          · rw [List.range_succ, semTripsInv_append, hsem]
            simp only [Option.bind_some, semTripsInv, hO, hOacc, dite_true]
          · intro y hy
            have hy' := hy
            simp only [frameReads, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq,
              Bool.not_eq_true'] at hy'
            have hyw : y ∉ loopWrites body := by simpa using hy'.2.2
            rw [rustExec_rsScalar_of_not_mem_loopWrites hcov hbody hyw]
            simp only [rsSetScalar, beq_iff_eq, if_neg hy'.2.1.1]
            exact hfrm y hy

/-- **The loop node against the threaded run.** `runtimeLoopNode_denote` with the
    premise `semTripsInv … = some aF` replaced by a `RustExec` run of
    `RForRuntime x (SVar n) body` from `rs` to `rs'`: for a word-fragment body with
    the trip frame `loopBodyFrame body x accName`, the accumulator bound at
    `.sword 64`, and an entry environment binding `n`, the accumulator and
    `frameReads body x accName` to the `rs` values, the loop node denotes its
    continuation at the accumulator's exit word. -/
theorem runtimeLoopNode_denote_rustExec {Γ : Ctx} (vm : VarMap Γ) (x n : String) (body : LowCT)
    (kont : ∀ {t : CryptoTy}, VarMap (t :: Γ) → Option (LoopOut (t :: Γ)))
    {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : runtimeLoopNode vm x n body kont = some ⟨s, cl⟩)
    (hcov : IsCoveredAdeq body)
    {accName : String} (hacc : loopAccName body = some accName)
    (hfr : loopBodyFrame body x accName = true)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {av : CVar Γ (.sword 64)} (ha : vm.lookup accName = some ⟨.sword 64, av⟩)
    {N : Nat} {leafSpec : LeafSpec} {rs rs' : RustState}
    (hexec : RustExec N leafSpec (.RForRuntime x (.SVar n) body) rs rs')
    (hnT : ¬ isTmpName n)
    (henv : EnvBoundOn rs env (fun y => y = n ∨ y ∈ accName :: frameReads body x accName))
    (hir : ScalarInRange rs) :
    ∃ k, kont (vm.bind (t := .sword 64) accName) = some ⟨s, k⟩ ∧
      cl.denote V = k.denote (V.extend (BitVec.ofNat 64 (rs'.rsScalar accName))) := by
  have hfr' := hfr
  simp only [loopBodyFrame, Bool.and_eq_true] at hfr'
  have hnt := not_isTmpName_of_notTmpB hfr'.1.2
  have hav : (toVIRVar av).lookup V = BitVec.ofNat 64 (rs.rsScalar accName) := by
    have h1 := hc accName
    rw [ha, henv accName (Or.inr (List.mem_cons_self ..)) hnt] at h1
    simpa using h1
  have hcv : (toVIRVar cv).lookup V = BitVec.ofNat 64 (rs.rsScalar n) := by
    have h1 := hc n
    rw [hn, henv n (Or.inl rfl) hnT] at h1
    simpa using h1
  cases hexec with
  | forRuntime _ _ _ _ _ hfor =>
      obtain ⟨hsem, -, -⟩ := semTripsInv_of_rustExec_rFor hcov hfr
        (envBoundOn_mono henv (fun y hy => Or.inr hy)) hir _ rs' (le_of_lt (hir n)) hfor
      refine runtimeLoopNode_denote vm x n body kont h hcov.toIsCoveredSCtl V env hc hacc hn ha ?_
      rw [hcv, hav, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir n)]
      exact hsem

/-- `runtimeLoopNode_denote_rustExec` at the `RForRuntime x (SVar n) body` arm of
    `translateDialectLoop`: the program has type `.sword 64` and denotes the
    accumulator's exit word of the `RustExec` run. -/
theorem translateDialectLoop_rForRuntime_denote_rustExec {Γ : Ctx} (vm : VarMap Γ)
    (x n : String) (body : LowCT) {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoop vm (.RForRuntime x (.SVar n) body) = some ⟨s, cl⟩)
    (hcov : IsCoveredAdeq body)
    {accName : String} (hacc : loopAccName body = some accName)
    (hfr : loopBodyFrame body x accName = true)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {av : CVar Γ (.sword 64)} (ha : vm.lookup accName = some ⟨.sword 64, av⟩)
    {N : Nat} {leafSpec : LeafSpec} {rs rs' : RustState}
    (hexec : RustExec N leafSpec (.RForRuntime x (.SVar n) body) rs rs')
    (hnT : ¬ isTmpName n)
    (henv : EnvBoundOn rs env (fun y => y = n ∨ y ∈ accName :: frameReads body x accName))
    (hir : ScalarInRange rs) :
    ∃ hs : CryptoTy.sword 64 = s, cl.denote V = hs ▸ BitVec.ofNat 64 (rs'.rsScalar accName) := by
  obtain ⟨k, hk, hd⟩ := runtimeLoopNode_denote_rustExec vm x n body retHere h hcov hacc hfr V env
    hc hn ha hexec hnT henv hir
  simp only [retHere, Option.some.injEq, Sigma.mk.inj_iff] at hk
  obtain ⟨rfl, hk⟩ := hk
  cases hk
  exact ⟨rfl, hd⟩

/-! ## 7. The straight-line prefix and the loop-free fallback -/

/-- **The loop-free fallback returns the result scalar.** For a covered `c`, a
    valuation consistent with `env`, and a `semScalar` run leaving `w` in `res`,
    the program `blockRet vm res c` denotes `w`. -/
theorem blockRet_denote {Γ : Ctx} (vm : VarMap Γ) (res : String) (c : LowCT)
    {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : blockRet vm res c = some ⟨s, cl⟩) (hcov : IsCoveredSCtl c)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env env' : SEnvScalar)
    (hc : ConsistentS vm V env) (hsem : semScalar c env = some env')
    {w : ⟦s⟧} (hval : env' res = some ⟨s, w⟩) :
    cl.denote V = w := by
  unfold blockRet at h
  split at h
  · rename_i o htr
    split at h
    · rename_i t v hlk
      obtain ⟨V', hc', hcont⟩ :=
        translateDialectControl_denote_ctl hcov vm V env env' o hc htr hsem
      obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar v))
      rw [hcom'] at h
      simp only [Option.map_some, Option.some.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rw [ComLoop.denote_block (d := catCryptDialect), hden]
      exact hc'.lookup_eq hlk hval
    · cases h
  · cases h

/-- The prefix `RScalarSet name n; c₂` denotes the translation of `c₂` at the
    valuation extended with the constant. -/
theorem translateDialectLoopR_rSeq_rScalarSet_denote {Γ : Ctx} (dflt : Option String)
    (vm : VarMap Γ) (name : String) (n : Nat) (c₂ : LowCT)
    {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoopR dflt vm (.RSeq (.RScalarSet name n) c₂) = some ⟨s, cl⟩) :
    ∃ k, translateDialectLoopR (some name) (vm.bind (t := .sword 64) name) c₂ = some ⟨s, k⟩ ∧
      ∀ V : Ctxt.Valuation (d := catCryptDialect) Γ,
        cl.denote V = k.denote (V.extend (BitVec.ofNat 64 n)) := by
  rw [translateDialectLoopR_rSeq_rScalarSet] at h
  cases hk : translateDialectLoopR (some name) (vm.bind (t := .sword 64) name) c₂ with
  | none => rw [hk] at h; cases h
  | some p =>
      obtain ⟨s', k⟩ := p
      rw [hk] at h
      simp only [Option.map_some, Option.some.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      exact ⟨k, rfl, fun V => rfl⟩

/-- The binding `RLetU64Zero name body` denotes the translation of `body` at the
    valuation extended with `0`. -/
theorem translateDialectLoopR_rLetU64Zero_denote {Γ : Ctx} (dflt : Option String)
    (vm : VarMap Γ) (name : String) (body : LowCT)
    {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoopR dflt vm (.RLetU64Zero name body) = some ⟨s, cl⟩) :
    ∃ k, translateDialectLoopR dflt (vm.bind (t := .sword 64) name) body = some ⟨s, k⟩ ∧
      ∀ V : Ctxt.Valuation (d := catCryptDialect) Γ,
        cl.denote V = k.denote (V.extend (0 : BitVec 64)) := by
  rw [translateDialectLoopR_rLetU64Zero] at h
  cases hk : translateDialectLoopR dflt (vm.bind (t := .sword 64) name) body with
  | none => rw [hk] at h; cases h
  | some p =>
      obtain ⟨s', k⟩ := p
      rw [hk] at h
      simp only [Option.map_some, Option.some.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      exact ⟨k, rfl, fun V => rfl⟩

/-- **A seeded runtime-trip loop against the threaded run.** The program
    `RSeq (RScalarSet accName v) (RForRuntime x (SVar n) body)` through
    `translateDialectLoop`: under the hypotheses of `runtimeLoopNode_denote_rustExec`
    at the post-seed state, with the seed `v < 2^64`, the bound `n` other than the
    accumulator and an entry environment binding `n` and `frameReads body x accName`
    to the `rs` values, the program has type `.sword 64` and denotes the
    accumulator's exit word of the `RustExec` run. -/
theorem translateDialectLoop_rSeq_rScalarSet_rForRuntime_denote_rustExec {Γ : Ctx}
    (vm : VarMap Γ) (accName : String) (v : Nat) (x n : String) (body : LowCT)
    {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoop vm
      (.RSeq (.RScalarSet accName v) (.RForRuntime x (.SVar n) body)) = some ⟨s, cl⟩)
    (hcov : IsCoveredAdeq body) (hacc : loopAccName body = some accName)
    (hfr : loopBodyFrame body x accName = true)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩) (hna : n ≠ accName)
    {N : Nat} {leafSpec : LeafSpec} {rs rs' : RustState}
    (hexec : RustExec N leafSpec
      (.RSeq (.RScalarSet accName v) (.RForRuntime x (.SVar n) body)) rs rs')
    (hv : v < 2 ^ 64) (hnT : ¬ isTmpName n)
    (henv : EnvBoundOn rs env (fun y => y = n ∨ y ∈ frameReads body x accName))
    (hir : ScalarInRange rs) :
    ∃ hs : CryptoTy.sword 64 = s, cl.denote V = hs ▸ BitVec.ofNat 64 (rs'.rsScalar accName) := by
  obtain ⟨k, hk, hkd⟩ := translateDialectLoopR_rSeq_rScalarSet_denote none vm accName v _ h
  rw [translateDialectLoopR_rForRuntime] at hk
  cases hexec with
  | seq _ _ _ r₁ _ h₁ h₂ =>
      cases h₁
      have hc' := consistentS_bind vm V env hc accName (t := .sword 64) (BitVec.ofNat 64 v)
      have hn' : (vm.bind (t := .sword 64) accName).lookup n = some ⟨.sword 64, .there cv⟩ := by
        simp [VarMap.bind, hna, hn]
      have ha' : (vm.bind (t := .sword 64) accName).lookup accName =
          some ⟨.sword 64, .here⟩ := by
        simp [VarMap.bind]
      have henv' : EnvBoundOn (rsSetScalar rs accName v)
          (env.upd accName (t := .sword 64) (BitVec.ofNat 64 v))
          (fun y => y = n ∨ y ∈ accName :: frameReads body x accName) :=
        envBoundOn_mono (envBoundOn_upd henv accName v) (fun y hy => by
          rcases hy with hy | hy
          · exact Or.inl (Or.inl hy)
          · rcases List.mem_cons.mp hy with hy | hy
            · exact Or.inr hy
            · exact Or.inl (Or.inr hy))
      obtain ⟨k', hk', hd⟩ := runtimeLoopNode_denote_rustExec _ x n body retHere hk hcov hacc
        hfr _ _ hc' hn' ha' h₂ hnT henv' (scalarInRange_upd hir accName hv)
      simp only [retHere, Option.some.injEq, Sigma.mk.inj_iff] at hk'
      obtain ⟨rfl, hk'⟩ := hk'
      cases hk'
      exact ⟨rfl, (hkd V).trans hd⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoop
