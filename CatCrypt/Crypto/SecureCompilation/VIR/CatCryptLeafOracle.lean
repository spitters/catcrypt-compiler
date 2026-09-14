/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# Leaf oracles for `catCryptDialect`

The dialect op `extCall name argTys retTy` denotes, under the instance
`catCryptDenote`, to `CryptoTy.default retTy` whatever its arguments. A leaf oracle
`SemLeafSpec` assigns an `extCall` a value computed from the leaf name, the
destination type and the argument values, and `catCryptDenoteWith ls` is the
denotation that consults `ls` at every `extCall` and agrees with `catCryptDenote` on
every other op. The oracle `defaultLeaf` returns `CryptoTy.default`, and
`catCryptDenoteWith defaultLeaf` is `catCryptDenote` (`catCryptDenoteWith_default`).

The argument values are passed as a list of typed values, the form in which the
scalar waist semantics reads them from its environment
(`Dialects.LeafOracleScalar.argVals`).

## Main definitions

* `SemLeafSpec`, `defaultLeaf` — the leaf oracle type and the default oracle
* `hvecSigmaList` — an `HVector` of values as a list of typed values
* `catCryptDenoteWith` — the dialect denotation at a leaf oracle

## Main results

* `catCryptDenoteWith_default` — at `defaultLeaf` the denotation is `catCryptDenote`
* `expr_denoteWith_extCall` — an `extCall` denotes to the oracle applied to its
  argument values
* `com_denoteWith_default` — at `defaultLeaf`, `Com.denote` is the default one
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-- A leaf oracle: the value of an opaque leaf call, as a function of the leaf name,
    the type of the destination and the typed argument values. -/
abbrev SemLeafSpec : Type :=
  (name : String) → (retTy : CryptoTy) → List ((t : CryptoTy) × ⟦t⟧) → ⟦retTy⟧

/-- The default leaf oracle: `CryptoTy.default` of the destination type, independent
    of the name and the arguments. -/
def defaultLeaf : SemLeafSpec := fun _ retTy _ => CryptoTy.default retTy

/-- An `HVector` of values as the list of its typed entries. -/
def hvecSigmaList : {tys : List CryptoTy} → HVector (fun t => ⟦t⟧) tys →
    List ((t : CryptoTy) × ⟦t⟧)
  | [], .nil => []
  | t :: _, .cons v rest => ⟨t, v⟩ :: hvecSigmaList rest

/-- The `catCryptDialect` denotation at the leaf oracle `ls`: an `extCall` denotes to
    `ls` applied to its name, return type and argument values; every other op denotes
    as under `catCryptDenote`. -/
@[instance_reducible]
def catCryptDenoteWith (ls : SemLeafSpec) : DialectDenote catCryptDialect where
  denote op := match op with
    | .extCall name _ retTy => fun args => ls name retTy (hvecSigmaList args)
    | o => catCryptDenote.denote o

/-- At the default oracle the leaf-parametric denotation is `catCryptDenote`. -/
theorem catCryptDenoteWith_default : catCryptDenoteWith defaultLeaf = catCryptDenote := by
  unfold catCryptDenoteWith
  congr 1
  funext op
  cases op <;> rfl

/-- An `extCall` expression at the oracle `ls` denotes to `ls` applied to the looked-up
    argument values. -/
theorem expr_denoteWith_extCall (ls : SemLeafSpec) {Γ : Ctxt catCryptDialect}
    (name : String) (argTys : List CryptoTy) (retTy : CryptoTy)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) argTys)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    @Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) Γ retTy
        ⟨.extCall name argTys retTy, rfl, args⟩ V
      = ls name retTy (hvecSigmaList (Expr.lookupArgs args V)) :=
  rfl

/-- At the default oracle, `Com.denote` is the denotation under `catCryptDenote`. -/
theorem com_denoteWith_default {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (com : Com catCryptDialect Γ t) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    @Com.denote catCryptDialect _ _ (catCryptDenoteWith defaultLeaf) Γ t com V
      = com.denote V := by
  rw [catCryptDenoteWith_default]

end CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
