/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasmin

/-!
# `lowerArithToJasmin` is denotation-preserving — UNCONDITIONALLY

The `LatticeToJasminDenote` / `LatticeToJasminDenoteUncond` mirror for the
neutral `arith` dialect (D0 of the MLIR dialect-alignment restructure). The
structural lowering `lowerArithToJasmin : Com arithDialect Γ t → Com jasminDialect
(Γ.map ArithTy.toJasmin) (ArithTy.toJasmin t)` and the transport lemma
`Arith.mapVal_lookup` are already proved in `ArithToJasmin.lean`; this file closes
the **denotational** half.

## Why the value transport is the identity

`⟦arith .int w⟧ = BitVec w = ⟦jasmin .reg w⟧` definitionally, so the per-value
transport `transTy : ⟦t⟧ → ⟦ArithTy.toJasmin t⟧` is the identity in every branch.
Unlike the lattice case (whose values are functions `Fin n → BitVec 16`, worked
pointwise), the arith case is scalar `BitVec`, so the leaf agreement is a direct
`BitVec`-equation.

## The one structural wrinkle vs. the lattice template

`ArithOp.toJasmin` maps to *concrete* jasmin ops (`regArith`/`mulhi`/…) whose
signature equals `(sig op).map ArithTy.toJasmin` only *propositionally*
(`Arith.toJasmin_sig`, `rfl` per op), so `Arith.lowerExpr` transports its arg
`HVector` across that proof with a `▸` cast. Since `toJasmin_sig op` reduces to
`rfl` once `op` is a concrete constructor (`cases e.op`), the cast vanishes after
case-splitting and the agreement closes structurally — exactly as for the lattice
leaves, but with the scalar `BitVec` op in place of the pointwise stack-array
leaf.

Since `arithDenote` was *defined* equal to `jasminDenote (op.toJasmin)` on every
op, the preservation theorem is exact (no value drift).

0 sorries.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Arith

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The per-value transport `transTy` (the identity)

`⟦arith .int w⟧ = BitVec w = ⟦jasmin .reg w⟧` definitionally, so `transTy` returns
the value unchanged in its single branch. -/

/-- Transport an `arith` value to its `ArithTy.toJasmin`-image type. The source
    `⟦.int w⟧ = BitVec w` and target `⟦(.int w).toJasmin⟧ = ⟦.reg w⟧ = BitVec w`
    are the *same* type, so the value passes through unchanged (the identity). -/
def transTy : {t : ArithTy} → TyDenote.denote t → TyDenote.denote (ArithTy.toJasmin t)
  | .int _, v => v

/-- On a concrete integer type, `transTy` is the identity. -/
theorem transTy_int {w : Nat} (v : BitVec w) :
    transTy (t := .int w) v = v := rfl

/-! ## 2. `mapVal_lookup` in `transTy` form

`Arith.mapVal_lookup` (proved in `ArithToJasmin.lean`) states
`(mapVar v).lookup (mapVal V) = v.lookup V`. Since `transTy = id`, that is exactly
the `transTy` form, definitionally. -/

/-- Variable lookup commutes with the valuation transport, in `transTy` form.
    Definitionally `Arith.mapVal_lookup` since `transTy` is the identity. -/
theorem mapVal_lookup_transTy {Γ : Ctxt arithDialect} {s : ArithTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) :=
  mapVal_lookup v V

/-! ## 3. `mapVal` commutes with valuation extension -/

/-- `mapVal` commutes with valuation extension via `transTy` on the new value.
    By `rfl` (`mapVal` is the matching `.cons`, `Valuation.extend` is `.cons`). -/
theorem mapVal_extend {Γ : Ctxt arithDialect} {t : ArithTy}
    (V : Ctxt.Valuation Γ) (x : TyDenote.denote t) :
    mapVal (V.extend x) = (mapVal V).extend (transTy (t := t) x) :=
  rfl

/-! ## 4. Leaf agreement (the crux)

For one `arith` expression `e`, the jasmin lowering `lowerExpr e` denotes (under
the transported valuation) to `transTy` of `e`'s denotation. Proved by casing on
`e.op` and destructuring its argument `HVector`.

The technique (the keystone the dialect fan-out reuses): `cases op` reduces the
propositional `toJasmin_sig`/`toJasmin_ret` casts in `lowerExpr`/`Expr.denote` to
`rfl` (so the `▸`s vanish), and `simp only [..., DialectDenote.denote, arithDenote,
jasminDenote, JasminBinOp.apply, mulHiW, ...]` unfolds the class-projection denote
on both sides to the *same* concrete `BitVec` operator applied to the looked-up
arguments. The two sides then differ only in `Expr.lookupArgs (mapVarHV _) (mapVal
V)` vs `Expr.lookupArgs _ V` — these are *definitionally* `(mapVar v).lookup (mapVal
V)` vs `v.lookup V` per slot, related by `mapVal_lookup_transTy`. A `congr` down to
each operand (matching the operator's arity/shape) then discharges each via
`mapVal_lookup_transTy`, which closes by defeq even though the `HVector`
projections never fire under `simp` (the VIR `Expr.lookupArgs`/`mapVarHV` recursors
are stuck on the abstract argument list). For the widening-high multiply the
operands sit two `BitVec.toNat`s deep inside `BitVec.ofNat (… * … / 2^w)`, so its
branch peels with `congr 3` + `congrArg BitVec.toNat`. -/

/-- **Leaf agreement.** The lowered jasmin expression's denotation agrees with
    `transTy` of the original arith expression's denotation, for every op. -/
theorem lowerExpr_denote {Γ : Ctxt arithDialect} {t : ArithTy}
    (e : Expr arithDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerExpr e).denote (mapVal V) = transTy (e.denote V) := by
  obtain ⟨op, hop, args⟩ := e
  subst hop
  cases op <;> (rcases args with _ | ⟨a, _ | ⟨b, _⟩⟩) <;>
    simp only [lowerExpr, Expr.denote, DialectDenote.denote,
      JasminBinOp.apply, mulHiW, ArithOp.toJasmin, transTy] <;>
    first
      | rfl
      | (congr 1 <;> exact mapVal_lookup_transTy _ _)
      | (refine congrArg (· >>> _) ?_; exact mapVal_lookup_transTy _ _)
      | (refine congrArg (· <<< _) ?_; exact mapVal_lookup_transTy _ _)
      | (congr 3 <;> exact congrArg BitVec.toNat (mapVal_lookup_transTy _ _))

/-! ## 5. The `Com` induction -/

/-- **Preservation (unconditional).** The arith→jasmin dialect lowering preserves
    `Com.denote`: the lowered jasmin program on the transported valuation denotes
    to `transTy` of the original arith program's denotation. -/
theorem lowerArithToJasmin_denote {Γ : Ctxt arithDialect} {t : ArithTy} :
    (com : Com arithDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (lowerArithToJasmin com).denote (mapVal V) = transTy (com.denote V)
  | .ret v, V => by
      simpa [lowerArithToJasmin, Com.denote] using mapVal_lookup_transTy v V
  | .var e body, V => by
      show (lowerArithToJasmin body).denote
            ((mapVal V).extend ((lowerExpr e).denote (mapVal V))) = _
      rw [lowerExpr_denote e V, ← mapVal_extend V (e.denote V)]
      exact lowerArithToJasmin_denote body (V.extend (e.denote V))

/-! ## 6. Worked corollary on `smokeProg` -/

/-- **Smoke.** Lowering the two-input `smokeProg` (`a + b`) preserves its
    denotation. -/
theorem smokeProg_denote_preserved
    (V : Ctxt.Valuation (d := arithDialect) [.int 32, .int 32]) :
    (lowerArithToJasmin smokeProg).denote (mapVal V) = transTy (smokeProg.denote V) :=
  lowerArithToJasmin_denote smokeProg V

end CatCrypt.Crypto.SecureCompilation.Dialects.Arith
