/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops

/-!
# Lowering the counted-loop fragment of `NFProg catCryptDialect` to `ComL`

`nfToComL` maps an `NFProg catCryptDialect` program with one result, built from
let-bindings, a return and counted loops carrying one value, to a `ComL` program: a
return to `ComL.ret`, a let-binding through `toJExprD`, and a `forLoop` with one
carried value whose body is straight-line (`NFProg.toCom?`) to `ComL.forLoopNRt`, with
its body through `cryptoDialectToJasminCom`, its count and seed variables through
`toJVarD`, and the whole enclosing context as the invariants (`allVars`). The trip
counter `CryptoTy.sword 64` maps to `JasminTy.reg 64`, so the body context
`acc :: .sword 64 :: Γ` maps to the `forLoopNRt` body context
`mapTy acc :: .reg 64 :: Γ.map mapTy`. Every other program is `none`.

`nfToComL_denote` is the preservation square of
`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`, lifted to loops: the
source program denotes `some` of one value, and the lowered program on the
transported valuation `ctMapValD V` denotes `ctTransTy` of that value.

## Main definitions

* `comToComL` — the embedding of `Com jasminDialect` into `ComL`.
* `nfToComLAt`, `nfToComL` — the lowering.

## Main results

* `comToComL_denote` — the embedding preserves denotation.
* `lookupArgs_toJArgsD_ctMapValD` — the lowered argument variables read the
  transported values.
* `foldl_stepC_ctTransTy` — a lowered loop body folds the transported accumulator
  to the transported source fold.
* `nfToComLAt_denote`, `nfToComL_denote` — the lowering preserves denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-! ## 1. `Com jasminDialect` inside `ComL` -/

/-- The straight-line jasmin program as a `ComL` program with no loop node. -/
def comToComL : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → ComL Γ t
  | _, _, .ret v => .ret v
  | _, _, .var e body => .var e (comToComL body)

/-- `comToComL` preserves denotation. -/
theorem comToComL_denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (comToComL c).denote V = c.denote V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V => comToComL_denote body (V.extend (e.denote V))

/-! ## 2. The lowering -/

/-- The `ComL.forLoopNRt` node of a counted loop carrying the tuple `cs`, with the
    lowered continuation `k'`: `none` unless `cs` is one type, the body is
    straight-line (`NFProg.toCom?`) and `cryptoDialectToJasminCom` lowers it. -/
def forNode {Γ : Ctx} {t : CryptoTy} : {cs : List CryptoTy} →
    Ctxt.Var Γ (HasWord64.word (d := catCryptDialect)) →
    HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) cs →
    NFProg catCryptDialect (cs ++ HasWord64.word (d := catCryptDialect) :: Γ) cs →
    ComL (mapCtx (cs ++ Γ)) (mapTy t) → Option (ComL (mapCtx Γ) (mapTy t))
  | [], _, .nil, _, _ => none
  | [_], count, .cons init .nil, body, k' =>
      body.toCom?.bind fun bc => (cryptoDialectToJasminCom bc).map fun jb =>
        ComL.forLoopNRt (invTys := Γ.map mapTy) jb (toJVarD count) (toJVarD init)
          (toJArgsD (allVars (d := catCryptDialect) Γ)) k'
  | _ :: _ :: _, _, .cons _ (.cons _ _), _, _ => none

/-- Lower an `NFProg catCryptDialect` program with the one result `t` (`ts = [t]`) to
    `ComL`. `none` on a branch, an exit-flag loop, a counted loop carrying other than
    one value or with a body that is not straight-line, and when a bound expression or
    a loop body falls outside the fragment `cryptoDialectToJasminCom` lowers. -/
def nfToComLAt : {Γ : Ctx} → {ts : List CryptoTy} → NFProg catCryptDialect Γ ts →
    (t : CryptoTy) → ts = [t] → Option (ComL (mapCtx Γ) (mapTy t))
  | _, _, .ret vs, _, h => by
      subst h
      exact match vs with
        | .cons v .nil => some (.ret (toJVarD v))
  | _, _, .var e k, t, h =>
      (toJExprD e).bind fun e' => (nfToComLAt k t h).map fun k' => .var e' k'
  | _, _, .forLoop count inits body k, t, h =>
      (nfToComLAt k t h).bind (forNode count inits body)
  | _, _, .ifThenElse .., _, _ => none
  | _, _, .whileLoop .., _, _ => none

/-- Lower an `NFProg catCryptDialect` program with one result to `ComL`
    (`nfToComLAt` at `ts = [t]`). -/
def nfToComL {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t]) :
    Option (ComL (mapCtx Γ) (mapTy t)) :=
  nfToComLAt p t rfl

/-! ## 3. Transport lemmas -/

/-- The lowered argument variables, looked up in the transported valuation, are the
    transported argument values. -/
theorem lookupArgs_toJArgsD_ctMapValD {Γ : Ctx} :
    {tys : List CryptoTy} →
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    Expr.lookupArgs (toJArgsD args) (ctMapValD V) = ctMapValD (Expr.lookupArgs args V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((toJVarD v).lookup (ctMapValD V))
        (Expr.lookupArgs (toJArgsD rest) (ctMapValD V)) = _
      rw [ctMapValD_lookup, lookupArgs_toJArgsD_ctMapValD rest V]
      rfl

/-- A lowered loop body, folded over any list of trip indices from the transported
    accumulator, gives the transported fold of the source body. -/
theorem foldl_stepC_ctTransTy {acc : CryptoTy} {invTys : Ctx}
    (body : Com catCryptDialect (acc :: .sword 64 :: invTys) acc)
    (jb : Com jasminDialect (mapTy acc :: .reg 64 :: invTys.map mapTy) (mapTy acc))
    (hb : cryptoDialectToJasminCom body = some jb)
    (W : Ctxt.Valuation (d := catCryptDialect) invTys) :
    (L : List Nat) → (a : CryptoTy.denote acc) →
    L.foldl (fun x t => JLoopBodyN.stepC jb (ctMapValD W) t x) (ctTransTy a) =
      ctTransTy (L.foldl
        (fun x t => body.denote (.cons x (.cons (BitVec.ofNat 64 t) W))) a)
  | [], _ => rfl
  | t :: L, a => by
      simp only [List.foldl_cons]
      have hstep : JLoopBodyN.stepC jb (ctMapValD W) t (ctTransTy a) =
          ctTransTy (body.denote (.cons a (.cons (BitVec.ofNat 64 t) W))) :=
        cryptoDialectToJasminCom_denote_eq' body
          (.cons a (.cons (BitVec.ofNat 64 t) W)) jb hb
      rw [hstep]
      exact foldl_stepC_ctTransTy body jb hb W L _

/-! ## 4. Preservation -/

/-- **Preservation.** When `nfToComLAt p t h = some jcom`, the source program denotes
    `some` of one value `x`, at every fuel, and the lowered program on the transported
    valuation denotes `ctTransTy x`. -/
theorem nfToComLAt_denote {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts)
    (t : CryptoTy) (h : ts = [t]) (jcom : ComL (mapCtx Γ) (mapTy t))
    (hj : nfToComLAt p t h = some jcom) (fuel : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ x : CryptoTy.denote t, p.denote fuel V = some (h ▸ .cons x .nil) ∧
      jcom.denote (ctMapValD V) = ctTransTy x := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      have hr : nfToComLAt (.ret (.cons v .nil)) t rfl = some (.ret (toJVarD v)) := rfl
      rw [hr, Option.some.injEq] at hj
      subst hj
      exact ⟨v.lookup V, rfl, ctMapValD_lookup v V⟩
  | var e k ih =>
      subst h
      simp only [nfToComLAt] at hj
      rcases he : toJExprD e with _ | e'
      · rw [he] at hj; cases hj
      rcases hk : nfToComLAt k t rfl with _ | k'
      · rw [he, hk] at hj; cases hj
      rw [he, hk] at hj
      cases hj
      obtain ⟨x, hx, hx'⟩ := ih rfl k' hk (V.extend (e.denote V))
      refine ⟨x, ?_, ?_⟩
      · simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
          Option.bind_some]
        exact hx
      · show k'.denote ((ctMapValD V).extend (e'.denote (ctMapValD V))) = _
        rw [dialectJasminLeafAgrees_holds e V e' he, ← ctMapValD_extend V (e.denote V)]
        exact hx'
  | forLoop count inits body k _ ihk =>
      simp only [nfToComLAt] at hj
      rcases hk : nfToComLAt k t h with _ | k'
      · rw [hk] at hj; cases hj
      rw [hk, Option.bind_some] at hj
      rcases inits with _ | ⟨init, _ | _⟩
      · simp [forNode] at hj
      · simp only [forNode] at hj
        rcases hbc : body.toCom? with _ | bc
        · rw [hbc] at hj; cases hj
        rcases hb : cryptoDialectToJasminCom bc with _ | jb
        · rw [hbc, Option.bind_some, hb] at hj; cases hj
        rw [hbc, Option.bind_some, hb, Option.map_some, Option.some.injEq] at hj
        subst hj
        have hfold := NFProg.foldlM_single (d := catCryptDialect)
          (fun acc i => body.denote fuel
            (MultiBlockLowering.hvAppend acc (.cons (HasWord64.ofNat (d := catCryptDialect) i) V)))
          (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) V)))
          (fun a i => NFProg.denote_of_toCom? body hbc fuel _)
          (List.range (count.lookup V).toNat) (init.lookup V)
        obtain ⟨x, hx, hx'⟩ := ihk h k' hk
          (V.extend ((List.range (count.lookup V).toNat).foldl
            (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) V))) (init.lookup V)))
        refine ⟨x, ?_, ?_⟩
        · rw [NFProg.denote_forLoop]
          exact (congrArg (· >>= _) hfold).trans hx
        · show k'.denote ((ctMapValD V).extend
            ((List.range ((toJVarD count).lookup (ctMapValD V)).toNat).foldl
              (fun x t => JLoopBodyN.stepC jb
                (Expr.lookupArgs (toJArgsD (allVars _)) (ctMapValD V)) t x)
              ((toJVarD init).lookup (ctMapValD V)))) = _
          rw [lookupArgs_toJArgsD_ctMapValD, lookupArgs_allVars, ctMapValD_lookup,
            ctMapValD_lookup, foldl_stepC_ctTransTy bc jb hb V, ← ctMapValD_extend]
          exact hx'
      · simp [forNode] at hj
  | ifThenElse => simp [nfToComLAt] at hj
  | whileLoop => simp [nfToComLAt] at hj

/-- **Preservation** for a program with one result: when `nfToComL p = some jcom`, the
    source program denotes `some` of one value `x`, at every fuel, and the lowered
    program on the transported valuation denotes `ctTransTy x`. -/
theorem nfToComL_denote {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (jcom : ComL (mapCtx Γ) (mapTy t)) (hj : nfToComL p = some jcom) (fuel : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ x : CryptoTy.denote t, p.denote fuel V = some (.cons x .nil) ∧
      jcom.denote (ctMapValD V) = ctTransTy x :=
  nfToComLAt_denote p t rfl jcom hj fuel V

end CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
