/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops

/-!
# Lowering `ComLoop catCryptDialect` to the jasmin loop layer `ComL`

`comLoopToComL` maps a `ComLoop catCryptDialect` program to a `ComL` program: a
block through `cryptoDialectToJasminCom` followed by `comToComL`, a let-binding
through `toJExprD`, and a runtime-trip loop `forRt` to `ComL.forLoopNRt`, with its
body through `cryptoDialectToJasminCom` and its count, seed and invariant variables
through `toJVarD` / `toJArgsD`. The trip counter `CryptoTy.sword 64` maps to
`JasminTy.reg 64`, so the body context `acc :: .sword 64 :: invTys` maps to the
`forLoopNRt` body context `mapTy acc :: .reg 64 :: invTys.map mapTy`.

`comLoopToComL_denote` is the preservation square of
`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`, lifted to loops:
the lowered program on the transported valuation `ctMapValD V` denotes to
`ctTransTy` of the source denotation.

## Main definitions

* `comToComL` — the embedding of `Com jasminDialect` into `ComL`.
* `comLoopToComL` — the lowering.

## Main results

* `comToComL_denote` — the embedding preserves denotation.
* `lookupArgs_toJArgsD_ctMapValD` — the lowered argument variables read the
  transported values.
* `foldl_stepC_ctTransTy` — a lowered loop body folds the transported accumulator
  to the transported source fold.
* `comLoopToComL_denote` — the lowering preserves denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComLoopToComL

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

/-- Lower a `ComLoop catCryptDialect` program to `ComL`. `none` when a block, a
    bound expression or a loop body falls outside the fragment
    `cryptoDialectToJasminCom` lowers. -/
def comLoopToComL : {Γ : Ctx} → {t : CryptoTy} →
    ComLoop catCryptDialect Γ t → Option (ComL (mapCtx Γ) (mapTy t))
  | _, _, .block c => (cryptoDialectToJasminCom c).map comToComL
  | _, _, .var e k =>
      (toJExprD e).bind fun e' => (comLoopToComL k).map fun k' => .var e' k'
  | _, _, .forRt (invTys := invTys) count init invs body k =>
      (cryptoDialectToJasminCom body).bind fun jb => (comLoopToComL k).map fun k' =>
        ComL.forLoopNRt (invTys := invTys.map mapTy) jb (toJVarD count)
          (toJVarD init) (toJArgsD invs) k'

/-- `comLoopToComL` on a block. -/
theorem comLoopToComL_block {Γ : Ctx} {t : CryptoTy} (c : Com catCryptDialect Γ t) :
    comLoopToComL (.block c) = (cryptoDialectToJasminCom c).map comToComL := rfl

/-- `comLoopToComL` on a let-binding. -/
theorem comLoopToComL_var {Γ : Ctx} {t s : CryptoTy} (e : Expr catCryptDialect Γ t)
    (k : ComLoop catCryptDialect (t :: Γ) s) :
    comLoopToComL (.var e k) =
      (toJExprD e).bind fun e' => (comLoopToComL k).map fun k' => .var e' k' := rfl

/-- `comLoopToComL` on a runtime-trip loop. -/
theorem comLoopToComL_forRt {Γ : Ctx} {acc s : CryptoTy} {invTys : Ctx}
    (count : Ctxt.Var (d := catCryptDialect) Γ (.sword 64))
    (init : Ctxt.Var (d := catCryptDialect) Γ acc)
    (invs : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) invTys)
    (body : Com catCryptDialect (acc :: .sword 64 :: invTys) acc)
    (k : ComLoop catCryptDialect (acc :: Γ) s) :
    comLoopToComL (.forRt count init invs body k) =
      (cryptoDialectToJasminCom body).bind fun jb => (comLoopToComL k).map fun k' =>
        ComL.forLoopNRt (invTys := invTys.map mapTy) jb (toJVarD count)
          (toJVarD init) (toJArgsD invs) k' := rfl

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

/-- **Preservation.** When `comLoopToComL com = some jcom`, the lowered program on
    the transported valuation denotes to `ctTransTy` of the source denotation. -/
theorem comLoopToComL_denote : {Γ : Ctx} → {t : CryptoTy} →
    (com : ComLoop catCryptDialect Γ t) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    (jcom : ComL (mapCtx Γ) (mapTy t)) →
    comLoopToComL com = some jcom →
    jcom.denote (ctMapValD V) = ctTransTy (com.denote V)
  | _, _, .block c, V, jcom, h => by
      rw [comLoopToComL_block] at h
      rcases hc : cryptoDialectToJasminCom c with _ | jc
      · rw [hc] at h; cases h
      · rw [hc] at h
        cases h
        rw [comToComL_denote]
        exact cryptoDialectToJasminCom_denote_eq' c V jc hc
  | _, _, .var e k, V, jcom, h => by
      rw [comLoopToComL_var] at h
      rcases he : toJExprD e with _ | e'
      · rw [he] at h; cases h
      rcases hk : comLoopToComL k with _ | k'
      · rw [he, hk] at h; cases h
      rw [he, hk] at h
      cases h
      show k'.denote ((ctMapValD V).extend (e'.denote (ctMapValD V))) = _
      rw [dialectJasminLeafAgrees_holds e V e' he, ← ctMapValD_extend V (e.denote V)]
      exact comLoopToComL_denote k (V.extend (e.denote V)) k' hk
  | _, _, .forRt (invTys := invTys) count init invs body k, V, jcom, h => by
      rw [comLoopToComL_forRt] at h
      rcases hb : cryptoDialectToJasminCom body with _ | jb
      · rw [hb] at h; cases h
      rcases hk : comLoopToComL k with _ | k'
      · rw [hb, hk] at h; cases h
      rw [hb, hk] at h
      cases h
      show k'.denote ((ctMapValD V).extend
        ((List.range ((toJVarD count).lookup (ctMapValD V)).toNat).foldl
          (fun x t => JLoopBodyN.stepC jb (Expr.lookupArgs (toJArgsD invs) (ctMapValD V)) t x)
          ((toJVarD init).lookup (ctMapValD V)))) = _
      rw [lookupArgs_toJArgsD_ctMapValD, ctMapValD_lookup, ctMapValD_lookup,
        foldl_stepC_ctTransTy body jb hb]
      exact comLoopToComL_denote k
        (V.extend (ComLoop.forRtFold body (Expr.lookupArgs invs V) (count.lookup V).toNat
          (init.lookup V))) k' hk

end CatCrypt.Crypto.SecureCompilation.VIR.ComLoopToComL
