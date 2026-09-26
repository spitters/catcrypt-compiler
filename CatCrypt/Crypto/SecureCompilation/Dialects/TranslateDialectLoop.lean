/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# The loop front: `LowCT` to `ComLoop catCryptDialect`

`translateDialectLoop` translates a runtime-trip loop `RForRuntime x (SVar n) body`,
alone or followed by a continuation (`RSeq (RForRuntime …) c₂`), to a
`ComLoop.forRt` node, and every other `LowCT` term to a `ComLoop.block` through
`translateDialectControl`.

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
`RForRuntime` arm of the `LowCT` semantics threads the whole environment through
the trips; the two agree on a body that writes, among the names it reads, only the
accumulator and `x`.

## Main definitions

* `allVars` — every variable of a context, as an argument vector.
* `loopAccName` — the loop-carried scalar of a loop body.
* `runtimeLoopNode` — the `forRt` node of a runtime-trip loop.
* `translateDialectLoop` — the loop front.
* `semTripsInv` — the source-side fold of the loop body.

## Main results

* `lookupArgs_allVars` — `allVars Γ` reads back the whole valuation.
* `consistentS_bind` — binding a name to a value preserves `ConsistentS`.
* `frontLoopBodyCD_denote` — a front-compiled loop body computes the accumulator the
  body's `semScalar` run leaves.
* `foldl_body_eq_of_semTripsInv` — the trip fold of the loop body is `semTripsInv`.
* `runtimeLoopNode_denote`, `translateDialectLoop_rSeq_rForRuntime_denote` — the
  loop node denotes its continuation at the loop result.
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

/-- The unit terminator `constUnit; ret`. -/
def unitCom {Γ : Ctx} : Com catCryptDialect Γ .unit :=
  Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here)

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

/-- The loop front. A runtime-trip loop over a scalar bound becomes a `forRt` node
    returning the loop result, or, followed by a continuation `c₂`, a `forRt` node
    continuing with the translation of `c₂`; every other term is translated by
    `translateDialectControl` and capped with the unit terminator. -/
def translateDialectLoop {Γ : Ctx} (vm : VarMap Γ) : LowCT → Option (LoopOut Γ)
  | .RForRuntime x (.SVar n) body => runtimeLoopNode vm x n body retHere
  | .RSeq (.RForRuntime x (.SVar n) body) c₂ =>
      runtimeLoopNode vm x n body (fun vm' => translateDialectLoop vm' c₂)
  | c =>
      match translateDialectControl vm c with
      | some o => (o.cont unitCom).map fun com => ⟨.unit, .block com⟩
      | none => none

/-- `translateDialectLoop` on a runtime-trip loop. -/
theorem translateDialectLoop_rForRuntime {Γ : Ctx} (vm : VarMap Γ) (x n : String)
    (body : LowCT) :
    translateDialectLoop vm (.RForRuntime x (.SVar n) body) =
      runtimeLoopNode vm x n body retHere := rfl

/-- `translateDialectLoop` on a runtime-trip loop followed by a continuation. -/
theorem translateDialectLoop_rSeq_rForRuntime {Γ : Ctx} (vm : VarMap Γ) (x n : String)
    (body c₂ : LowCT) :
    translateDialectLoop vm (.RSeq (.RForRuntime x (.SVar n) body) c₂) =
      runtimeLoopNode vm x n body (fun vm' => translateDialectLoop vm' c₂) := rfl

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
    `translateDialectLoop`: the continuation is the loop front's translation of
    `c₂` under the post-loop `VarMap`. -/
theorem translateDialectLoop_rSeq_rForRuntime_denote {Γ : Ctx} (vm : VarMap Γ)
    (x n : String) (body c₂ : LowCT) {s : CryptoTy} {cl : ComLoop catCryptDialect Γ s}
    (h : translateDialectLoop vm (.RSeq (.RForRuntime x (.SVar n) body) c₂) = some ⟨s, cl⟩)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {accName : String} (hacc : loopAccName body = some accName)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {accTy : CryptoTy} {av : CVar Γ accTy} (ha : vm.lookup accName = some ⟨accTy, av⟩)
    {aF : ⟦accTy⟧}
    (hsem : semTripsInv body x accName accTy env
      (List.range ((toVIRVar cv).lookup V).toNat) ((toVIRVar av).lookup V) = some aF) :
    ∃ k, translateDialectLoop (vm.bind (t := accTy) accName) c₂ = some ⟨s, k⟩ ∧
      cl.denote V = k.denote (V.extend aF) :=
  runtimeLoopNode_denote vm x n body _ h hcov V env hc hacc hn ha hsem

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

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoop
