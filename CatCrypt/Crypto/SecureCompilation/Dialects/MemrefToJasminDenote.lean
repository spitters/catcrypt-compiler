/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasmin

/-!
# `lowerMemrefToJasmin` is denotation-preserving — UNCONDITIONALLY

The `ArithToJasminDenote` / `LatticeToJasminDenoteUncond` mirror for the neutral
`memref` dialect of the MLIR dialect alignment. The
structural lowering `lowerMemrefToJasmin : Com memrefDialect Γ t → Com jasminDialect
(Γ.map MemrefTy.toJasmin) (MemrefTy.toJasmin t)`, the per-value transport `transTy`,
and the lookup transport `Memref.mapVal_lookup` are already proved in
`MemrefToJasmin.lean`; this module proves the **denotational** half.

## Why the value transport is the identity

`⟦memref .int w⟧ = BitVec w = ⟦jasmin .reg w⟧` and `⟦memref .buf w n⟧ =
(Fin n → BitVec w) = ⟦jasmin .stackArr w n⟧` definitionally, so `transTy` is the
identity in every branch.

## Scalar (`load`) vs. array (`store`) leaf agreement

`memrefDenote` is *defined* equal to `jasminDenote (op.toJasmin)` on every op, so
the leaf agreement is exact.

* `load` (scalar result `int w`): the standard scalar tactic applies — `cases op`
  collapses the propositional `toJasmin_sig`/`toJasmin_ret` casts to `rfl`, `simp`
  unfolds both denotes to `stackGet` of the looked-up arguments, and `congr` down
  to each operand discharges via `mapVal_lookup` (since `transTy` is the identity).
* `store` (array result `buf w n`): the result is a *function* `Fin n → BitVec w`,
  so the agreement is taken pointwise via `funext`, in the lattice-template style,
  with `stackSet` on both sides reduced to the looked-up arguments.

All goals closed.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Memref

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. `mapVal_lookup` in `transTy` form

`Memref.mapVal_lookup` (proved in `MemrefToJasmin.lean`) already states
`(mapVar v).lookup (mapVal V) = transTy (v.lookup V)`, so this is a direct alias
threading the dialect-fan-out naming convention. -/

/-- Variable lookup commutes with the valuation transport, in `transTy` form. -/
theorem mapVal_lookup_transTy {Γ : Ctxt memrefDialect} {s : MemrefTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) :=
  mapVal_lookup v V

/-! ## 2. `mapVal` commutes with valuation extension -/

/-- `mapVal` commutes with valuation extension via `transTy` on the new value.
    By `rfl` (`mapVal` is the matching `.cons`, `Valuation.extend` is `.cons`). -/
theorem mapVal_extend {Γ : Ctxt memrefDialect} {t : MemrefTy}
    (V : Ctxt.Valuation Γ) (x : TyDenote.denote t) :
    mapVal (V.extend x) = (mapVal V).extend (transTy (t := t) x) :=
  rfl

/-! ## 3. Leaf agreement (the crux)

For one `memref` expression `e`, the jasmin lowering `lowerExpr e` denotes (under
the transported valuation) to `transTy` of `e`'s denotation. Proved by casing on
`e.op` and destructuring its argument `HVector`. `load` closes via the scalar
tactic (`congr` + `mapVal_lookup_transTy`); `store` closes pointwise via
`funext` (the result is a buffer `Fin n → BitVec w`). -/

/-- **Leaf agreement.** The lowered jasmin expression's denotation agrees with
    `transTy` of the original memref expression's denotation, for every op. -/
theorem lowerExpr_denote {Γ : Ctxt memrefDialect} {t : MemrefTy}
    (e : Expr memrefDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerExpr e).denote (mapVal V) = transTy (e.denote V) := by
  obtain ⟨op, hop, args⟩ := e
  subst hop
  cases op with
  | load w n =>
      rcases args with _ | ⟨a, _ | ⟨i, _⟩⟩
      simp only [lowerExpr, Expr.denote, DialectDenote.denote,
        MemrefOp.toJasmin, transTy]
      congr 1
      · exact mapVal_lookup_transTy _ _
      · exact congrArg BitVec.toNat (mapVal_lookup_transTy _ _)
  | store w n =>
      rcases args with _ | ⟨a, _ | ⟨i, _ | ⟨v, _⟩⟩⟩
      simp only [lowerExpr, Expr.denote, DialectDenote.denote,
        MemrefOp.toJasmin, transTy]
      congr 1
      · exact mapVal_lookup_transTy _ _
      · exact congrArg BitVec.toNat (mapVal_lookup_transTy _ _)
      · exact mapVal_lookup_transTy _ _

/-! ## 4. The `Com` induction -/

/-- **Preservation (unconditional).** The memref→jasmin dialect lowering preserves
    `Com.denote`: the lowered jasmin program on the transported valuation denotes
    to `transTy` of the original memref program's denotation. -/
theorem lowerMemrefToJasmin_denote {Γ : Ctxt memrefDialect} {t : MemrefTy} :
    (com : Com memrefDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (lowerMemrefToJasmin com).denote (mapVal V) = transTy (com.denote V)
  | .ret v, V => by
      simpa [lowerMemrefToJasmin, Com.denote] using mapVal_lookup_transTy v V
  | .var e body, V => by
      show (lowerMemrefToJasmin body).denote
            ((mapVal V).extend ((lowerExpr e).denote (mapVal V))) = _
      rw [lowerExpr_denote e V, ← mapVal_extend V (e.denote V)]
      exact lowerMemrefToJasmin_denote body (V.extend (e.denote V))

/-! ## 5. Worked corollary on `smokeProg` -/

/-- **Smoke.** Lowering the `load %a[%i]` `smokeProg` preserves its denotation. -/
theorem smokeProg_denote_preserved
    (V : Ctxt.Valuation (d := memrefDialect) [.buf 32 4, .int 64]) :
    (lowerMemrefToJasmin smokeProg).denote (mapVal V) = transTy (smokeProg.denote V) :=
  lowerMemrefToJasmin_denote smokeProg V

end CatCrypt.Crypto.SecureCompilation.Dialects.Memref
