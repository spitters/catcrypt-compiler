/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL

/-!
# Straight-line `NFProg` bodies as multi-result programs

`NFProg.toMulti? p` reads an `NFProg` made of let-bindings and a multi-result return as
the straight-line program `MultiReturnCom d Γ ts` with the same bindings and the same
returned variables; a region constructor gives `none`. It is the multi-result analogue of
`NFProg.toCom?`, and reads the body of a `forLoop` or a `whileLoop` with any carried tuple.

`MultiReturnCom.restrict? m f` restricts a multi-result program along a partial map of
variables `f` (the `NFProgToComL.comRestrict` of `MultiReturnCom`), and
`MultiReturnCom.usedSelM Γ n m` selects the variables of the outer context `Γ` that a
program over `n` local binders followed by `Γ` reads: each once, in decreasing index (the
`NFProgToComL.usedSel` of `MultiReturnCom`). `VMap.liftApp f Δ` lifts a partial map under
the binders `Δ`, which is how a selection of the outer context reaches a loop body over
`cs ++ word :: Γ` or `cs ++ Γ`.

## Main definitions

* `NFProg.toMultiAt`, `NFProg.toMulti?` — the straight-line reading.
* `MultiReturnCom.ctLeak` — the events of a multi-result program, in binding order.
* `MultiReturnCom.restrict?`, `MultiReturnCom.idxs`, `MultiReturnCom.usedSelM` — the
  restriction, the indices a program reads, and the outer variables it reads.
* `NFProgToComL.VMap.liftApp` — a partial map under a list of binders.

## Main results

* `MultiReturnCom.lookupVars_eq_lookupArgs` — `lookupVars` is `Expr.lookupArgs`.
* `NFProg.denote_of_toMulti?` — a program read as `m` denotes `some (m.denote V)` at every
  fuel.
* `NFProg.leakRun_of_toMulti?` — a program read as `m` runs to `m.denote V` with the
  events `m.ctLeak M V` at every fuel.
* `MultiReturnCom.restrict?_denote` — the restriction keeps the denotation at valuations the
  map relates.
* `NFProgToComL.VMap.agree_liftApp` — a lifted map relates the valuations extended by the
  same values.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open NFProgToComL (VMap VMap.lift VMap.args VMap.Agree VMap.agree_lift VMap.lookupArgs_args
  argIdxs selOf)

/-! ## 1. The straight-line reading of an `NFProg` -/

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The straight-line multi-result program of an `NFProg` made of let-bindings and a
    return; `none` on a region constructor. -/
def toMultiAt : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts →
    Option (MultiReturnCom d Γ ts)
  | _, _, .ret vs => some (.ret vs)
  | _, _, .var e k => (toMultiAt k).map (.var e)
  | _, _, .forLoop .. => none
  | _, _, .ifThenElse .. => none
  | _, _, .whileLoop .. => none

/-- The straight-line multi-result program of an `NFProg` made of let-bindings and a
    return (`toMultiAt`); `none` on a region constructor. -/
def toMulti? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    Option (MultiReturnCom d Γ ts) :=
  toMultiAt p

end NFProg

namespace MultiReturnCom

/-- `lookupVars` is `Expr.lookupArgs`. -/
theorem lookupVars_eq_lookupArgs {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d} :
    {ts : List d.Ty} → (vs : HVector (fun ty => Var Γ ty) ts) → (V : Valuation Γ) →
    lookupVars vs V = Expr.lookupArgs vs V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons (v.lookup V) (lookupVars rest V) =
        HVector.cons (v.lookup V) (Expr.lookupArgs rest V)
      rw [lookupVars_eq_lookupArgs rest V]

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]

/-- The events of the run of a multi-result program from a valuation, in binding order:
    each binding emits the events of its operation (`Expr.ctLeak`). -/
def ctLeak (M : LeakModel d) : {Γ : Ctxt d} → {ts : List d.Ty} →
    MultiReturnCom d Γ ts → Valuation Γ → List CTLeak
  | _, _, .ret _, _ => []
  | _, _, .var e k, V => Expr.ctLeak M e V ++ ctLeak M k (V.extend (e.denote V))

end MultiReturnCom

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- **A straight-line reading preserves the denotation**: a program `toMulti?` reads as
    the multi-result program `m` denotes `some (m.denote V)`, at every fuel. -/
theorem denote_of_toMulti? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    {m : MultiReturnCom d Γ ts} (hm : p.toMulti? = some m) (fuel : Nat) (V : Valuation Γ) :
    p.denote fuel V = some (m.denote V) := by
  induction p with
  | ret vs =>
      simp only [toMulti?, toMultiAt, Option.some.injEq] at hm
      subst hm
      exact congrArg some (MultiReturnCom.lookupVars_eq_lookupArgs vs V).symm
  | var e k ih =>
      simp only [toMulti?, toMultiAt, Option.map_eq_some_iff] at hm
      obtain ⟨m', hk, rfl⟩ := hm
      simp only [denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some]
      exact ih hk _
  | forLoop => simp [toMulti?, toMultiAt] at hm
  | ifThenElse => simp [toMulti?, toMultiAt] at hm
  | whileLoop => simp [toMulti?, toMultiAt] at hm

/-- **A straight-line reading preserves the leakage run**: a program `toMulti?` reads as
    the multi-result program `m` runs to `m.denote V` with the events `m.ctLeak M V`, at
    every fuel. -/
theorem leakRun_of_toMulti? (M : LeakModel d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) {m : MultiReturnCom d Γ ts} (hm : p.toMulti? = some m)
    (fuel : Nat) (V : Valuation Γ) :
    NFProg.leakRun M fuel p V = some (m.denote V, m.ctLeak M V) := by
  induction p with
  | ret vs =>
      simp only [toMulti?, toMultiAt, Option.some.injEq] at hm
      subst hm
      simp only [NFProg.leakRun, MultiReturnCom.denote, MultiReturnCom.ctLeak,
        MultiReturnCom.lookupVars_eq_lookupArgs]
  | var e k ih =>
      simp only [toMulti?, toMultiAt, Option.map_eq_some_iff] at hm
      obtain ⟨m', hk, rfl⟩ := hm
      simp only [NFProg.leakRun, ih hk, Option.map_some, MultiReturnCom.denote,
        MultiReturnCom.ctLeak]
  | forLoop => simp [toMulti?, toMultiAt] at hm
  | ifThenElse => simp [toMulti?, toMultiAt] at hm
  | whileLoop => simp [toMulti?, toMultiAt] at hm

end NFProg

/-! ## 2. The restriction of a multi-result program -/

namespace NFProgToComL

variable {d : Dialect} [DialectSignature d] [TyDenote d.Ty]

/-- A partial map of variables under the binders `Δ` of both contexts. -/
def VMap.liftApp {Γ Γ' : Ctxt d} (f : VMap Γ Γ') : (Δ : Ctxt d) → VMap (Δ ++ Γ) (Δ ++ Γ')
  | [] => f
  | _ :: Δ => VMap.lift (VMap.liftApp f Δ)

omit [DialectSignature d] in
/-- A lifted map relates the valuations extended by the same values under `Δ`. -/
theorem VMap.agree_liftApp {Γ Γ' : Ctxt d} {f : VMap Γ Γ'} {V : Valuation Γ}
    {V' : Valuation Γ'} (h : VMap.Agree f V V') :
    (Δ : Ctxt d) → (A : Valuation Δ) →
    VMap.Agree (VMap.liftApp f Δ) (hvAppend A V) (hvAppend A V')
  | [], .nil => h
  | _ :: Δ, .cons a A => VMap.agree_lift (VMap.agree_liftApp h Δ A) a

end NFProgToComL

namespace MultiReturnCom

variable {d : Dialect} [DialectSignature d] [TyDenote d.Ty]

/-- **The restriction of a multi-result program** along `f`: every variable it reads
    mapped by `f`, or `none` when one is outside the domain of `f`. -/
def restrict? : {Γ Γ' : Ctxt d} → {ts : List d.Ty} → MultiReturnCom d Γ ts →
    VMap Γ Γ' → Option (MultiReturnCom d Γ' ts)
  | _, _, _, .ret vs, f => (VMap.args f vs).map .ret
  | _, _, _, .var e k, f =>
      (VMap.args f e.args).bind fun as =>
        (restrict? k (VMap.lift f)).map fun k' => .var ⟨e.op, e.retTy_eq, as⟩ k'

/-- **The restriction keeps the denotation** at valuations the map relates. -/
theorem restrict?_denote [DialectDenote d] : {Γ Γ' : Ctxt d} → {ts : List d.Ty} →
    (m : MultiReturnCom d Γ ts) → (f : VMap Γ Γ') → (m' : MultiReturnCom d Γ' ts) →
    m.restrict? f = some m' → (V : Valuation Γ) → (V' : Valuation Γ') →
    VMap.Agree f V V' → m'.denote V' = m.denote V
  | _, _, _, .ret vs, f, m', h, V, V', hag => by
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
      change lookupVars ws V' = lookupVars vs V
      rw [lookupVars_eq_lookupArgs, lookupVars_eq_lookupArgs]
      exact VMap.lookupArgs_args hag vs ws hws
  | _, _, _, .var e k, f, m', h, V, V', hag => by
      obtain ⟨as, has, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have he : (⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V' = e.denote V := by
        unfold Expr.denote
        rw [VMap.lookupArgs_args hag e.args as has]
      change k'.denote (V'.extend ((⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V')) =
        k.denote (V.extend (e.denote V))
      rw [he]
      exact restrict?_denote k (VMap.lift f) k' hk' _ _ (VMap.agree_lift hag _)

/-- The de Bruijn indices of the variables of `Γ` a multi-result program reads. -/
def idxs : {Γ : Ctxt d} → {ts : List d.Ty} → MultiReturnCom d Γ ts → List Nat
  | _, _, .ret vs => argIdxs vs
  | _, _, .var e k =>
      argIdxs e.args ++ (idxs k).filterMap fun i => if i = 0 then none else some (i - 1)

/-- **The outer variables a multi-result program reads.** The program runs over `n` local
    binders followed by the outer context `Γ` (a loop body over `cs ++ word :: Γ` has
    `n = cs.length + 1`, one over `cs ++ Γ` has `n = cs.length`); the selection lists the
    variables of `Γ` it reads, each once, in decreasing index. -/
def usedSelM {Δ : Ctxt d} (Γ : Ctxt d) (n : Nat) {ts : List d.Ty}
    (m : MultiReturnCom d Δ ts) : Σ Γ' : Ctxt d, HVector (fun t => Var Γ t) Γ' :=
  selOf Γ ((((idxs m).filterMap fun i => if i < n then none else some (i - n)).eraseDups
    ).mergeSort fun i j => decide (j ≤ i))

end MultiReturnCom

end CatCrypt.Crypto.SecureCompilation.VIR
