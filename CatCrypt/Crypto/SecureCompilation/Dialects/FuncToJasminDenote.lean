/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.FuncToJasmin

/-!
# `lowerFuncToJasmin` is denotation-preserving — UNCONDITIONALLY

The `LatticeToJasminDenote` / `LatticeToJasminDenoteUncond` mirror for the neutral
`func` dialect (D0 fan-out of the MLIR dialect-alignment restructure). The
structural lowering `lowerFuncToJasmin : Com funcDialect Γ t → Com jasminDialect
(Γ.map FuncTy.toJasmin) (FuncTy.toJasmin t)` and the transport lemma
`Func.mapVal_lookup` are proved in `FuncToJasmin.lean`; this file closes the
**denotational** half with no leaf-agreement hypothesis.

## Why the leaf agreement is exact (and unconditional)

A `func.call`/`func.callN` is an **opaque** named call: its `func`-side denotation
is the per-type default (`FuncTy.default`). It lowers to a jasmin `extCall`/`callN`,
whose denotation is *also* an opaque default:

* `func.call` → jasmin `extCall name … (.reg w)`. Because the lowered return type
  is a scalar `reg w` — never the 16-bit `stackArr` that `jasminExtSem`'s lattice
  arms require — the `extCall` denotation falls into `jasminExtSem`'s **catch-all**
  `fun _ => JasminTy.default retTy`. So both sides are `JasminTy.default (.reg w)`.
* `func.callN` → jasmin `callN`, whose denotation is `JasminTy.default (callNRet …)`
  directly.

Both defaults agree across `toJasmin` (`FuncTy.default (.int w) = (0 : BitVec w) =
JasminTy.default (.reg w)`), so the leaf agreement holds by `cases`/`rfl`, with no
hypothesis. This is the lattice `extCall` pattern (the agreement is settled by the
jasmin leaf semantics) specialised to the opaque-default leaf.

## The value transport `transTy` (the identity)

`⟦func .int w⟧ = BitVec w = ⟦jasmin .reg w⟧` definitionally, so `transTy` returns
the value unchanged in its single branch — exactly the `arith` template.

0 sorries.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Func

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The per-value transport `transTy` (the identity) -/

/-- Transport a `func` value to its `FuncTy.toJasmin`-image type. The source
    `⟦.int w⟧ = BitVec w` and target `⟦(.int w).toJasmin⟧ = ⟦.reg w⟧ = BitVec w`
    are the *same* type, so the value passes through unchanged. -/
def transTy : {t : FuncTy} → TyDenote.denote t → TyDenote.denote (FuncTy.toJasmin t)
  | .int _, v => v

/-- On a concrete integer type, `transTy` is the identity. -/
theorem transTy_int {w : Nat} (v : BitVec w) :
    transTy (t := .int w) v = v := rfl

/-- `transTy` carries the `func` opaque default to the jasmin opaque default.
    `FuncTy.default (.int w) = (0 : BitVec w) = JasminTy.default (.reg w)`. -/
theorem transTy_default (t : FuncTy) :
    transTy (FuncTy.default t) = JasminTy.default (FuncTy.toJasmin t) := by
  cases t <;> rfl

/-! ## 2. `mapVal_lookup` in `transTy` form

`Func.mapVal_lookup` (in `FuncToJasmin.lean`) states `(mapVar v).lookup (mapVal V)
= v.lookup V`. Since `transTy = id`, that is exactly the `transTy` form. -/

/-- Variable lookup commutes with the valuation transport, in `transTy` form.
    Definitionally `Func.mapVal_lookup` since `transTy` is the identity. -/
theorem mapVal_lookup_transTy {Γ : Ctxt funcDialect} {s : FuncTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) :=
  mapVal_lookup v V

/-! ## 3. `mapVal` commutes with valuation extension -/

/-- `mapVal` commutes with valuation extension via `transTy` on the new value.
    By `rfl` (`mapVal` is the matching `.cons`, `Valuation.extend` is `.cons`). -/
theorem mapVal_extend {Γ : Ctxt funcDialect} {t : FuncTy}
    (V : Ctxt.Valuation Γ) (x : TyDenote.denote t) :
    mapVal (V.extend x) = (mapVal V).extend (transTy (t := t) x) :=
  rfl

/-! ## 4. Leaf agreement (the crux)

For one `func` expression `e`, the jasmin lowering `lowerExpr e` denotes (under the
transported valuation) to `transTy` of `e`'s denotation. Both sides are opaque
defaults:

* `call`: `cases e.op` makes the `extCall`'s declared signature `(sig op).map
  toJasmin` reduce so the `▸`/`retTy_eq` cast vanishes, and `jasminExtSem name
  (argTys.map toJasmin) (.reg w) _` reduces to the catch-all `JasminTy.default
  (.reg w)` (the scalar `.reg w` return cannot match the lattice arms' `.stackArr
  16 m`). The `func` side is `transTy (FuncTy.default (.int w))`, equal by
  `transTy_default`.
* `callN`: the jasmin `callN` denotes to `JasminTy.default (callNRet (retTys.map
  toJasmin))`; the `func` side is `transTy (FuncTy.default (funcCallNRet retTys))`,
  bridged by `transTy_default` + `funcCallNRet_toJasmin`. -/

/-- A jasmin `extCall` with a **scalar `reg w` return** denotes to the opaque default,
    for ANY argument types: its `reg w` result is type-incompatible with the `stackArr 16`
    arms of `jasminExtSem`, so the match is forced to the catch-all. -/
private theorem jasminExtSem_reg_default {name : String} {argTys : List JasminTy} {w : Nat}
    (args : HVector (fun t => ⟦t⟧) argTys) :
    jasminExtSem name argTys (.reg w) args = JasminTy.default (.reg w) := by
  rcases argTys with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [jasminExtSem]

/-- **Leaf agreement.** The lowered jasmin expression's denotation agrees with
    `transTy` of the original `func` expression's denotation, for both ops. -/
theorem lowerExpr_denote {Γ : Ctxt funcDialect} {t : FuncTy}
    (e : Expr funcDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerExpr e).denote (mapVal V) = transTy (e.denote V) := by
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | call name argTys retTy =>
      subst hop
      -- `retTy : FuncTy` is `int w`, so `retTy.toJasmin = reg w` (never `stackArr`):
      -- casing it makes the `jasminExtSem` match reduce to its opaque catch-all.
      cases retTy with
      | int w =>
        -- `retTy.toJasmin = reg w` (not `stackArr`), so the dependent `jasminExtSem`
        -- match is type-forced to its opaque catch-all `(reg w).default`, defeq to
        -- `transTy (int w).default` (`transTy_default`).
        show jasminExtSem name (argTys.map FuncTy.toJasmin) (.reg w)
              (Expr.lookupArgs (mapVarHV args) (mapVal V)) = transTy (FuncTy.default (.int w))
        rw [transTy_default]
        exact jasminExtSem_reg_default _
  | callN name argTys retTys =>
      subst hop
      -- Both sides are the opaque multi-result default; the head-result types agree
      -- by `funcCallNRet_toJasmin`. `cases retTys` makes the `headD` concrete so the
      -- dependent `▸` cast resolves.
      cases retTys with
      | nil => rfl
      | cons t ts => cases t with | int w => exact (transTy_default (.int w)).symm

/-! ## 5. The `Com` induction -/

/-- **Preservation (unconditional).** The func→jasmin dialect lowering preserves
    `Com.denote`: the lowered jasmin program on the transported valuation denotes
    to `transTy` of the original `func` program's denotation. -/
theorem lowerFuncToJasmin_denote {Γ : Ctxt funcDialect} {t : FuncTy} :
    (com : Com funcDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (lowerFuncToJasmin com).denote (mapVal V) = transTy (com.denote V)
  | .ret v, V => by
      simpa [lowerFuncToJasmin, Com.denote] using mapVal_lookup_transTy v V
  | .var e body, V => by
      show (lowerFuncToJasmin body).denote
            ((mapVal V).extend ((lowerExpr e).denote (mapVal V))) = _
      rw [lowerExpr_denote e V, ← mapVal_extend V (e.denote V)]
      exact lowerFuncToJasmin_denote body (V.extend (e.denote V))

/-! ## 6. Worked corollary on `smokeProg` -/

/-- **Smoke.** Lowering the one-call `smokeProg` preserves its denotation. -/
theorem smokeProg_denote_preserved
    (V : Ctxt.Valuation (d := funcDialect) [.int 32, .int 32]) :
    (lowerFuncToJasmin smokeProg).denote (mapVal V) = transTy (smokeProg.denote V) :=
  lowerFuncToJasmin_denote smokeProg V

end CatCrypt.Crypto.SecureCompilation.Dialects.Func
