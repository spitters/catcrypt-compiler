/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.VectorToJasmin

/-!
# `lowerVectorToJasmin` is denotation-preserving — UNCONDITIONALLY

The `arith` denote mirror for the neutral `vector` dialect (D0 of the MLIR
dialect-alignment restructure). The structural lowering `lowerVectorToJasmin :
Com vectorDialect Γ t → Com jasminDialect (Γ.map VectorTy.toJasmin) (VectorTy.toJasmin
t)` and the transport lemma `Vector.mapVal_lookup` are already proved in
`VectorToJasmin.lean`; this file closes the **denotational** half.

## Why the value transport is the identity

`⟦vector .v512⟧ = BitVec 512 = ⟦jasmin .reg 512⟧` definitionally, so the per-value
transport `transTy : ⟦t⟧ → ⟦VectorTy.toJasmin t⟧` is the identity in its single
branch. The leaf agreement is a direct `BitVec 512`-equation.

## The one structural wrinkle vs. the arith template

`VectorOp.toJasmin` maps to the *concrete* jasmin op `vpackZMM bop` whose signature
equals `(sig op).map VectorTy.toJasmin` only *propositionally* (`Vector.toJasmin_sig`,
`rfl` per op), so `Vector.lowerExpr` transports its arg `HVector` across that proof
with a `▸` cast. Since `toJasmin_sig op` reduces to `rfl` once `op` is a concrete
constructor (`cases e.op`), the cast vanishes after case-splitting and the agreement
closes structurally.

Since `vectorDenote` was *defined* equal to `jasminDenote (op.toJasmin)` on `pack`
(both `zmmPackQ bop`, reused from `JasminDialect`), the preservation theorem is exact
(no value drift).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Vector

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The per-value transport `transTy` (the identity)

`transTy` is defined upstream in `VectorToJasmin.lean` (it had to move there: a
second `VectorTy` constructor broke the one-line `mapVal` defeq). It is the
identity on each branch (`⟦v512⟧ = ⟦reg 512⟧`, `⟦v128⟧ = ⟦reg 128⟧`
definitionally). -/

/-- On the ZMM type, `transTy` is the identity. -/
theorem transTy_v512 (v : BitVec 512) :
    transTy (s := .v512) v = v := rfl

/-- On the XMM type, `transTy` is the identity. -/
theorem transTy_v128 (v : BitVec 128) :
    transTy (s := .v128) v = v := rfl

/-! ## 2. `mapVal_lookup` in `transTy` form

`Vector.mapVal_lookup` (proved in `VectorToJasmin.lean`) states
`(mapVar v).lookup (mapVal V) = v.lookup V`. Since `transTy = id`, that is exactly
the `transTy` form, definitionally. -/

/-- Variable lookup commutes with the valuation transport, in `transTy` form.
    Definitionally `Vector.mapVal_lookup` since `transTy` is the identity. -/
theorem mapVal_lookup_transTy {Γ : Ctxt vectorDialect} {s : VectorTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) :=
  mapVal_lookup v V

/-! ## 3. `mapVal` commutes with valuation extension -/

/-- `mapVal` commutes with valuation extension via `transTy` on the new value.
    By `rfl` (`mapVal` is the matching `.cons`, `Valuation.extend` is `.cons`). -/
theorem mapVal_extend {Γ : Ctxt vectorDialect} {t : VectorTy}
    (V : Ctxt.Valuation Γ) (x : TyDenote.denote t) :
    mapVal (V.extend x) = (mapVal V).extend (transTy (s := t) x) :=
  rfl

/-! ## 4. Leaf agreement (the crux)

For one `vector` expression `e`, the jasmin lowering `lowerExpr e` denotes (under the
transported valuation) to `transTy` of `e`'s denotation. Proved by casing on `e.op`
and destructuring its argument `HVector`.

`pack` is a single binary op, so it is the `addi`-shaped case of the keystone arith
tactic: `cases op` reduces the propositional `toJasmin_sig`/`toJasmin_ret` casts to
`rfl` (the `▸`s vanish); `simp only [..., DialectDenote.denote, vectorDenote,
jasminDenote, VectorOp.toJasmin, transTy]` unfolds the class-projection denote on both
sides to the *same* `zmmPackQ bop` applied to the looked-up arguments; the two sides
then differ only per operand slot, related by `mapVal_lookup_transTy`. A `congr 1 <;>
exact mapVal_lookup_transTy _ _` discharges both operands. -/

set_option maxRecDepth 1024 in
/-- **Leaf agreement.** The lowered jasmin expression's denotation agrees with
    `transTy` of the original vector expression's denotation, for every op. -/
theorem lowerExpr_denote {Γ : Ctxt vectorDialect} {t : VectorTy}
    (e : Expr vectorDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerExpr e).denote (mapVal V) = transTy (e.denote V) := by
  obtain ⟨op, hop, args⟩ := e
  subst hop
  -- Split the OUTER op and (for `vsimd`) the inner `SimdOp` FIRST, so the jasmin
  -- denote's inner `match op` reduces to a concrete waist call; then destructure
  -- the binary arg `HVector` and unfold both denote sides.
  match op with
  | .pack _ =>
    rcases args with _ | ⟨a, _ | ⟨b, _⟩⟩
    simp only [lowerExpr, Expr.denote, DialectDenote.denote, VectorOp.toJasmin, transTy]
    refine congr (congrArg _ ?_) ?_ <;> exact mapVal_lookup_transTy _ _
  | .vsimd op' =>
    cases op' <;>
      (rcases args with _ | ⟨a, _ | ⟨b, _⟩⟩
       simp only [lowerExpr, Expr.denote, DialectDenote.denote, VectorOp.toJasmin, transTy]
       refine congr (congrArg _ ?_) ?_ <;> exact mapVal_lookup_transTy _ _)

/-! ## 5. The `Com` induction -/

/-- **Preservation (unconditional).** The vector→jasmin dialect lowering preserves
    `Com.denote`: the lowered jasmin program on the transported valuation denotes to
    `transTy` of the original vector program's denotation. -/
theorem lowerVectorToJasmin_denote {Γ : Ctxt vectorDialect} {t : VectorTy} :
    (com : Com vectorDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (lowerVectorToJasmin com).denote (mapVal V) = transTy (com.denote V)
  | .ret v, V => by
      simpa [lowerVectorToJasmin, Com.denote] using mapVal_lookup_transTy v V
  | .var e body, V => by
      show (lowerVectorToJasmin body).denote
            ((mapVal V).extend ((lowerExpr e).denote (mapVal V))) = _
      rw [lowerExpr_denote e V, ← mapVal_extend V (e.denote V)]
      exact lowerVectorToJasmin_denote body (V.extend (e.denote V))

/-! ## 6. Worked corollary on `smokeProg` -/

/-- **Smoke.** Lowering the one-input-op `smokeProg` (`pack .add a b`) preserves its
    denotation. -/
theorem smokeProg_denote_preserved
    (V : Ctxt.Valuation (d := vectorDialect) [.v512, .v512]) :
    (lowerVectorToJasmin smokeProg).denote (mapVal V) = transTy (smokeProg.denote V) :=
  lowerVectorToJasmin_denote smokeProg V

end CatCrypt.Crypto.SecureCompilation.Dialects.Vector
