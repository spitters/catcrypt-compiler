/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle

/-!
# `cryptoDialectToJasminCom` preserves denotation at every leaf oracle

`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'` relates the
denotation of a lowered program under `jasminDenote` to the denotation of the source
under `catCryptDenote`, where both give an opaque leaf call its default value. This
module states the same square at a pair of leaf oracles: the source denotes under
`catCryptDenoteWith ls` and the lowered program under `jasminDenoteWith jls`.

The lowering passes the arguments of an `extCall` through unchanged, variable by
variable (`lookupArgs_toJArgsD`), so the square holds whenever the jasmin oracle
applied to the transported arguments is the transport of the dialect oracle
(`LeafTransport ls jls`). The default oracles `defaultLeaf` and `jasminExtSem` are
such a pair (`leafTransport_default`), and at them the result is
`cryptoDialectToJasminCom_denote_eq'` (`cryptoDialectToJasminCom_denote_eq'_of_default`).

## Main definitions

* `JLeafSem` — the jasmin leaf oracle type, the argument of `jasminDenoteWith`
* `ctMapHV` — the pointwise value transport of an argument vector
* `LeafTransport` — the jasmin oracle commutes with the value transport
* `DialectJasminLeafAgreesWith` — per-expression agreement at a pair of oracles

## Main results

* `jasminDenoteWith_jasminExtSem` — at `jasminExtSem`, `jasminDenoteWith` is
  `jasminDenote`
* `leafTransport_default` — the default oracles are related by `LeafTransport`
* `dialectJasminLeafAgreesWith_holds` — agreement from `LeafTransport`
* `cryptoDialectToJasminCom_denote_eqWith`,
  `cryptoDialectToJasminCom_denote_eq_of_transport` — preservation at the oracles
* `cryptoDialectToJasminCom_denote_eq'_of_default` — the default instance
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComLeaf

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect
  (ctTransTy ctTransTy_default jasminExtSem_reg jasminExtSem_stackArr64)

/-- A jasmin leaf oracle: the value of an `extCall` from its name, argument types,
    return type and argument values. `jasminExtSem` is the default one. -/
abbrev JLeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-- At `jasminExtSem` the leaf-parametric jasmin denotation is `jasminDenote`. -/
theorem jasminDenoteWith_jasminExtSem : jasminDenoteWith jasminExtSem = jasminDenote := by
  unfold jasminDenoteWith
  congr 1
  funext op
  cases op <;> rfl

/-- The value transport `ctTransTy`, applied to each entry of a value vector. -/
def ctMapHV : {tys : List CryptoTy} → HVector (fun t => ⟦t⟧) tys →
    HVector (fun t => ⟦t⟧) (tys.map mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (ctTransTy v) (ctMapHV rest)

/-- The lowered argument variables, looked up in the transported valuation, are the
    transported argument values. -/
theorem lookupArgs_toJArgsD {Γ : Ctx} :
    {tys : List CryptoTy} →
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    Expr.lookupArgs (toJArgsD args) (ctMapValD V) = ctMapHV (Expr.lookupArgs args V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((toJVarD v).lookup (ctMapValD V))
        (Expr.lookupArgs (toJArgsD rest) (ctMapValD V)) = _
      rw [ctMapValD_lookup, lookupArgs_toJArgsD rest V]
      rfl

/-- The jasmin oracle `jls` applied to transported arguments at the mapped types is the
    transport of the dialect oracle `ls`. -/
def LeafTransport (ls : SemLeafSpec) (jls : JLeafSem) : Prop :=
  ∀ (name : String) (argTys : List CryptoTy) (retTy : CryptoTy)
    (args : HVector (fun t => ⟦t⟧) argTys),
    jls name (argTys.map mapTy) (mapTy retTy) (ctMapHV args)
      = ctTransTy (ls name retTy (hvecSigmaList args))

/-- The default oracles are related: `jasminExtSem` returns the jasmin default on every
    type `mapTy` produces, which is the transport of `CryptoTy.default`. -/
theorem leafTransport_default : LeafTransport defaultLeaf jasminExtSem := by
  intro name argTys retTy args
  show _ = ctTransTy (CryptoTy.default retTy)
  rw [ctTransTy_default]
  cases retTy with
  | sword w => exact jasminExtSem_reg _ _ _ _
  | bit => exact jasminExtSem_reg _ _ _ _
  | unit => exact jasminExtSem_reg _ _ _ _
  | pair a b => exact jasminExtSem_reg _ _ _ _
  | sum a b => exact jasminExtSem_reg _ _ _ _
  | memref n => exact jasminExtSem_stackArr64 _ _ _ _

/-- Per-expression leaf agreement at the oracle pair `(ls, jls)`: an expression the
    lowering accepts denotes, lowered and under the transported valuation, to the
    transport of its source denotation. -/
def DialectJasminLeafAgreesWith (ls : SemLeafSpec) (jls : JLeafSem) : Prop :=
  ∀ {Γ : Ctx} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (e' : Expr jasminDialect (mapCtx Γ) (mapTy t)),
    toJExprD e = some e' →
    @Expr.denote jasminDialect _ _ (jasminDenoteWith jls) _ _ e' (ctMapValD V)
      = ctTransTy (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ e V)

/-- Leaf agreement at an oracle pair related by `LeafTransport`. The `extCall` case is
    the transport hypothesis after `lookupArgs_toJArgsD`; on every other op both
    oracle denotations are the default ones, and the case is
    `dialectJasminLeafAgrees_holds`. -/
theorem dialectJasminLeafAgreesWith_holds {ls : SemLeafSpec} {jls : JLeafSem}
    (h : LeafTransport ls jls) : DialectJasminLeafAgreesWith ls jls := by
  intro Γ t e V e' he
  obtain ⟨op, hop, args⟩ := e
  cases op
  case extCall name argTys retTy =>
    cases hop
    simp only [toJExprD, Option.some.injEq] at he
    subst he
    show jls name (argTys.map mapTy) (mapTy retTy)
        (Expr.lookupArgs (toJArgsD args) (ctMapValD V))
      = ctTransTy (ls name retTy (hvecSigmaList (Expr.lookupArgs args V)))
    rw [lookupArgs_toJArgsD]
    exact h name argTys retTy _
  case vsimd sop =>
    cases hop
    have h0 := dialectJasminLeafAgrees_holds ⟨_, rfl, args⟩ V e' he
    cases sop <;> (simp only [toJExprD, reduceCtorEq] at he ⊢) <;> (try cases he) <;> exact h0
  case ite ty =>
    cases hop
    have h0 := dialectJasminLeafAgrees_holds ⟨_, rfl, args⟩ V e' he
    cases ty <;> (simp only [toJExprD, reduceCtorEq] at he ⊢) <;> (try cases he) <;> exact h0
  all_goals
    cases hop
    have h0 := dialectJasminLeafAgrees_holds ⟨_, rfl, args⟩ V e' he
    first
    | (simp only [toJExprD, reduceCtorEq] at he; done)
    | (simp only [toJExprD] at he; cases he; exact h0)

/-- **Preservation at a pair of leaf oracles, under leaf agreement.** Whenever the
    lowering succeeds, the lowered program at `jasminDenoteWith jls`, on the transported
    valuation, denotes to the transport of the source at `catCryptDenoteWith ls`. -/
theorem cryptoDialectToJasminCom_denote_eqWith {ls : SemLeafSpec} {jls : JLeafSem}
    (hLeaf : DialectJasminLeafAgreesWith ls jls) {Γ : Ctx} {t : CryptoTy} :
    (com : Com catCryptDialect Γ t) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t)) →
    cryptoDialectToJasminCom com = some jcom →
    @Com.denote jasminDialect _ _ (jasminDenoteWith jls) _ _ jcom (ctMapValD V)
      = ctTransTy (@Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V)
  | .ret v, V, jcom, hcom => by
      simp only [cryptoDialectToJasminCom, Option.some.injEq] at hcom
      subst hcom
      show (toJVarD v).lookup (ctMapValD V) = _
      exact ctMapValD_lookup v V
  | .var e body, V, jcom, hcom => by
      simp only [cryptoDialectToJasminCom] at hcom
      split at hcom
      · next e' he =>
          split at hcom
          · next body' hbody =>
              simp only [Option.some.injEq] at hcom
              subst hcom
              show @Com.denote jasminDialect _ _ (jasminDenoteWith jls) _ _ body'
                ((ctMapValD V).extend
                  (@Expr.denote jasminDialect _ _ (jasminDenoteWith jls) _ _ e' (ctMapValD V)))
                = _
              rw [hLeaf e V e' he, ← ctMapValD_extend V _]
              exact cryptoDialectToJasminCom_denote_eqWith hLeaf body _ body' hbody
          · exact absurd hcom (by simp)
      · exact absurd hcom (by simp)

/-- **Preservation at every oracle pair related by `LeafTransport`.** -/
theorem cryptoDialectToJasminCom_denote_eq_of_transport {ls : SemLeafSpec} {jls : JLeafSem}
    (h : LeafTransport ls jls) {Γ : Ctx} {t : CryptoTy}
    (com : Com catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hcom : cryptoDialectToJasminCom com = some jcom) :
    @Com.denote jasminDialect _ _ (jasminDenoteWith jls) _ _ jcom (ctMapValD V)
      = ctTransTy (@Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V) :=
  cryptoDialectToJasminCom_denote_eqWith (dialectJasminLeafAgreesWith_holds h) com V jcom hcom

/-- At the default oracles, `cryptoDialectToJasminCom_denote_eq_of_transport` is the
    statement of `cryptoDialectToJasminCom_denote_eq'`. -/
theorem cryptoDialectToJasminCom_denote_eq'_of_default {Γ : Ctx} {t : CryptoTy}
    (com : Com catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hcom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy (com.denote V) := by
  have h := cryptoDialectToJasminCom_denote_eq_of_transport leafTransport_default com V jcom hcom
  rwa [jasminDenoteWith_jasminExtSem, catCryptDenoteWith_default] at h

end CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComLeaf
