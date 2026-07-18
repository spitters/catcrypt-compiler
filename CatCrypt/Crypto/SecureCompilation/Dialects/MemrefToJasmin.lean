/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.Memref

/-!
# `Com memref → Com jasmin` — the D0 verified-lowering recursion

The `ArithToJasmin` mirror for the neutral `memref` dialect (D0 fan-out of the
MLIR dialect-alignment restructure). Structural `Com→Com` recursion along the
`MemrefTy.toJasmin` / `MemrefOp.toJasmin` maps, with the valuation transport
needed for the denotation-preservation proof in `MemrefToJasminDenote.lean`.

As in `ArithToJasmin`, `MemrefOp.toJasmin` maps to *concrete* jasmin ops
(`stackLoad`/`stackStore`), so `sig (op.toJasmin) = (sig op).map toJasmin` is
propositional (`Memref.toJasmin_sig`, `rfl` per op) rather than definitional, so
`lowerExpr` transports the arg `HVector` across that proof.

Since `memrefDenote` was defined to equal the jasmin image's denotation on every
op, the preservation theorem is exact (no value drift). The new wrinkle vs. the
scalar `arith` case is the `store` op, whose result is a *buffer*
(`Fin n → BitVec w`); the agreement there is worked pointwise via `funext`, as in
the lattice template.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Memref

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The de Bruijn variable transport along `MemrefTy.toJasmin` -/

/-- Transport a `memref` de Bruijn variable into the `toJasmin`-mapped jasmin
    context. `(t :: Γ).map toJasmin = toJasmin t :: Γ.map toJasmin` definitionally. -/
def mapVar {Γ : Ctxt memrefDialect} {s : MemrefTy} :
    Ctxt.Var Γ s → Ctxt.Var (d := jasminDialect) (Γ.map MemrefTy.toJasmin) (MemrefTy.toJasmin s)
  | .here => .here
  | .there v => .there (mapVar v)

/-- Lift `mapVar` pointwise over an arg `HVector`, transporting the index list. -/
def mapVarHV {Γ : Ctxt memrefDialect} :
    {tys : List MemrefTy} →
    HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := jasminDialect) (Γ.map MemrefTy.toJasmin) ty)
      (tys.map MemrefTy.toJasmin)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapVarHV rest)

/-! ## 2. Lower one `Expr[memref]` to an `Expr[jasmin]` -/

/-- Lower a `memref` expression to its jasmin image. The op is `e.op.toJasmin`; its
    signature matches `(sig e.op).map toJasmin` via `toJasmin_sig` (so the args are
    cast across that proof), and its result type matches via `toJasmin_ret`. -/
def lowerExpr {Γ : Ctxt memrefDialect} {t : MemrefTy} (e : Expr memrefDialect Γ t) :
    Expr jasminDialect (Γ.map MemrefTy.toJasmin) (MemrefTy.toJasmin t) :=
  { op := e.op.toJasmin
    retTy_eq := (toJasmin_ret e.op).trans (congrArg MemrefTy.toJasmin e.retTy_eq)
    args := (toJasmin_sig e.op).symm ▸ mapVarHV e.args }

/-! ## 3. Lower a `Com[memref]` to a `Com[jasmin]` -/

/-- Lower a `memref` program to a jasmin program over the `toJasmin`-mapped context
    and result type. -/
def lowerMemrefToJasmin {Γ : Ctxt memrefDialect} {t : MemrefTy} :
    Com memrefDialect Γ t → Com jasminDialect (Γ.map MemrefTy.toJasmin) (MemrefTy.toJasmin t)
  | .ret v => .ret (mapVar v)
  | .var e body => .var (lowerExpr e) (lowerMemrefToJasmin body)

/-! ## 4. The per-value transport `transTy` and the valuation transport `mapVal`

The value transport is the IDENTITY: `⟦memref .int w⟧ = BitVec w = ⟦jasmin .reg w⟧`
and `⟦memref .buf w n⟧ = (Fin n → BitVec w) = ⟦jasmin .stackArr w n⟧` definitionally,
so the transport returns each value unchanged. `MemrefTy.toJasmin` is defined by
pattern matching, so the type equality is *stuck* for an abstract `t`; casing on
`t` makes source and target denotation syntactically the same type in each branch.
This *computes* to the identity on concrete constructors. (Unlike the single-
constructor `arith` case, the two-constructor `memref` type needs this explicit
transport in `mapVal`, exactly as the lattice template does.) -/

/-- Transport a `memref` value to its `MemrefTy.toJasmin`-image type. Casing on `t`
    makes the source `⟦t⟧` and target `⟦t.toJasmin⟧` denotations the *same* type in
    each branch, so the value passes through unchanged (the identity). -/
def transTy : {t : MemrefTy} → TyDenote.denote t → TyDenote.denote (MemrefTy.toJasmin t)
  | .int _, v => v
  | .buf _ _, v => v

/-- On a concrete scalar type, `transTy` is the identity. -/
theorem transTy_int {w : Nat} (v : BitVec w) :
    transTy (t := .int w) v = v := rfl

/-- On a concrete buffer type, `transTy` is the identity. -/
theorem transTy_buf {w n : Nat} (v : Fin n → BitVec w) :
    transTy (t := .buf w n) v = v := rfl

/-- Valuation transport along `MemrefTy.toJasmin`, applying `transTy` per binding
    (identity on the underlying values). -/
def mapVal {Γ : Ctxt memrefDialect} :
    Ctxt.Valuation Γ → Ctxt.Valuation (d := jasminDialect) (Γ.map MemrefTy.toJasmin)
  | .nil => .nil
  | .cons (t := t) v rest => .cons (transTy (t := t) v) (mapVal rest)

/-- Looking up a transported variable in a transported valuation yields `transTy`
    of the original lookup. -/
theorem mapVal_lookup {Γ : Ctxt memrefDialect} {s : MemrefTy}
    (v : Ctxt.Var Γ s) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = transTy (v.lookup V) := by
  induction v with
  | here => match V with | .cons _ _ => rfl
  | there v ih => match V with | .cons _ V' => exact ih V'

end CatCrypt.Crypto.SecureCompilation.Dialects.Memref
